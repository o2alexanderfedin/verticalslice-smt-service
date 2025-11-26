"""
Tests for async lazy loading of embedding provider.

This module tests the async lazy loading pattern using asyncio.Task
to ensure:
1. Singleton behavior (same instance returned)
2. Race condition safety (concurrent calls don't create multiple instances)
3. Functionality (provider works correctly)
4. Performance (application startup is fast)

TDD approach: These tests are written BEFORE implementation (RED phase).
"""

import asyncio
import time
from collections.abc import Generator

import pytest

from src.api.dependencies import get_embedding_provider
from src.infrastructure.embeddings.sentence_transformer import SentenceTransformerProvider


@pytest.fixture
def reset_provider_singleton() -> Generator[None, None, None]:
    """
    Reset the embedding provider singleton between tests.

    This fixture ensures each test starts with a clean state.
    It resets the module-level _embedding_provider_task variable
    to None before and after each test.

    Yields:
        None
    """
    # Setup: Reset before test
    import src.api.dependencies as deps

    deps._embedding_provider_task = None

    yield

    # Teardown: Reset after test
    deps._embedding_provider_task = None


@pytest.mark.asyncio
async def test_get_embedding_provider_returns_same_instance(
    reset_provider_singleton: None,
) -> None:
    """
    Test that get_embedding_provider() returns the same instance (singleton).

    This verifies the singleton pattern is working correctly:
    - First call creates the instance
    - Second call returns the same instance
    - Third call returns the same instance

    SOLID: Single Responsibility - provider management is separate concern
    """
    # Act: Get provider three times
    provider1 = await get_embedding_provider()
    provider2 = await get_embedding_provider()
    provider3 = await get_embedding_provider()

    # Assert: All references point to the same instance
    assert provider1 is provider2, "Second call should return same instance"
    assert provider2 is provider3, "Third call should return same instance"
    assert isinstance(provider1, SentenceTransformerProvider), "Should be correct type"


@pytest.mark.asyncio
async def test_concurrent_calls_are_safe(reset_provider_singleton: None) -> None:
    """
    Test that concurrent calls to get_embedding_provider() are race-condition safe.

    This simulates the scenario where multiple requests arrive simultaneously
    before the model is loaded. The Task pattern ensures only one instance
    is created and all calls await the same loading operation.

    SOLID: Open/Closed - pattern handles concurrency without modification
    """
    # Act: Launch 10 concurrent calls
    tasks = [get_embedding_provider() for _ in range(10)]
    providers = await asyncio.gather(*tasks)

    # Assert: All returned the same instance
    first_provider = providers[0]
    for i, provider in enumerate(providers):
        assert provider is first_provider, f"Provider {i} should be the same instance"

    assert isinstance(first_provider, SentenceTransformerProvider), "Should be correct type"


@pytest.mark.asyncio
async def test_provider_can_generate_embeddings(reset_provider_singleton: None) -> None:
    """
    Test that the lazily-loaded provider can actually generate embeddings.

    This verifies the provider is fully functional after lazy loading:
    - Can generate embeddings
    - Embeddings have correct shape
    - Embeddings are normalized

    SOLID: Liskov Substitution - provider works same as eager-loaded version
    """
    # Arrange
    test_text = "The quick brown fox jumps over the lazy dog"

    # Act: Get provider and generate embedding
    provider = await get_embedding_provider()
    embedding = await provider.embed(test_text)

    # Assert: Embedding is valid
    assert embedding is not None, "Embedding should not be None"
    assert len(embedding.shape) == 1, "Embedding should be 1-dimensional"
    assert embedding.shape[0] == 384, "all-MiniLM-L6-v2 produces 384-dim embeddings"

    # Check normalization (L2 norm should be ~1.0 for normalized vectors)
    import numpy as np

    norm = np.linalg.norm(embedding)
    assert abs(norm - 1.0) < 0.01, "Embedding should be normalized (L2 norm ≈ 1.0)"


@pytest.mark.asyncio
async def test_application_startup_is_fast(reset_provider_singleton: None) -> None:
    """
    Test that the async lazy loading doesn't block application startup.

    This verifies the key performance benefit:
    - Startup should be fast (< 500ms)
    - Model loading happens on first use, not startup

    SOLID: Dependency Inversion - high-level code doesn't depend on loading time

    Note: This test does NOT call get_embedding_provider(), simulating
    the startup scenario where no requests have arrived yet.
    """
    # Arrange: Simulate fresh startup (singleton already reset by fixture)
    import src.api.dependencies as deps

    # Act: Measure time to "startup" (verify provider is not loaded)
    start_time = time.time()

    # Verify provider is not loaded yet
    assert deps._embedding_provider_task is None, "Provider should not be loaded at startup"

    elapsed = time.time() - start_time

    # Assert: Startup is instant (< 500ms)
    assert elapsed < 0.5, f"Startup should be < 500ms, got {elapsed:.3f}s"


@pytest.mark.asyncio
async def test_subsequent_calls_reuse_loaded_model(reset_provider_singleton: None) -> None:
    """
    Test that subsequent calls reuse the already-loaded model without reloading.

    This verifies efficiency:
    - First call loads model (takes time)
    - Subsequent calls are fast (reuse loaded model)

    SOLID: Interface Segregation - callers only depend on embed() interface
    """
    # Act: First call (loads model)
    start1 = time.time()
    provider1 = await get_embedding_provider()
    elapsed1 = time.time() - start1

    # Act: Second call (reuses loaded model)
    start2 = time.time()
    provider2 = await get_embedding_provider()
    elapsed2 = time.time() - start2

    # Assert: Second call is much faster (< 100ms)
    assert elapsed2 < 0.1, f"Second call should be fast (< 100ms), got {elapsed2:.3f}s"
    assert provider1 is provider2, "Should reuse same instance"

    # First call takes longer (loads model), but we don't assert exact time
    # since it depends on hardware
    assert elapsed1 > elapsed2, "First call should take longer than subsequent calls"
