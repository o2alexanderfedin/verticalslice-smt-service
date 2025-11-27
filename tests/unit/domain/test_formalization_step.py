"""Unit tests for FormalizationStep.

Tests cover:
- Skip logic for short inputs
- Force skip flag behavior
- Successful formalization on first attempt
- Retry loop with improving similarity scores
- Max retries exhausted
- Source embedding computation failure
- LLM provider exceptions
- Embedding provider exceptions
- Similarity calculation edge cases
- Caching behavior
"""

from unittest.mock import AsyncMock, Mock

import numpy as np
import pytest

from src.domain.exceptions import FormalizationError
from src.domain.steps.formalization import FormalizationStep
from src.infrastructure.cache import AsyncFileCache
from src.shared.result import Err, Ok


class TestFormalizationStep:
    """Tests for FormalizationStep."""

    @pytest.fixture
    def step(
        self, mock_llm_provider, mock_embedding_provider, mock_semantic_verifier
    ) -> FormalizationStep:
        """Create formalization step with mocked dependencies."""
        return FormalizationStep(
            llm_provider=mock_llm_provider,
            embedding_provider=mock_embedding_provider,
            verifier=mock_semantic_verifier,
            threshold=0.91,
            max_retries=3,
            skip_threshold=200,
        )

    @pytest.mark.asyncio
    async def test_short_input_skips_formalization(
        self, step: FormalizationStep, mock_llm_provider, mock_embedding_provider
    ) -> None:
        """Test that inputs shorter than skip_threshold are skipped."""
        short_text = "x > 5"  # Less than 200 chars
        result = await step.execute(short_text)

        # Should return Ok with input text unchanged
        assert isinstance(result, Ok)
        assert result.value.formal_text == short_text
        assert result.value.similarity_score == 1.0
        assert result.value.attempts == 0

        # No LLM or embedding calls should be made
        mock_llm_provider.formalize.assert_not_called()
        mock_embedding_provider.embed.assert_not_called()

    @pytest.mark.asyncio
    async def test_force_skip_bypasses_formalization(
        self, step: FormalizationStep, mock_llm_provider, mock_embedding_provider
    ) -> None:
        """Test that force_skip=True skips formalization regardless of length."""
        long_text = "x" * 500  # Much longer than skip_threshold
        result = await step.execute(long_text, force_skip=True)

        # Should return Ok with input text unchanged
        assert isinstance(result, Ok)
        assert result.value.formal_text == long_text
        assert result.value.similarity_score == 1.0
        assert result.value.attempts == 0

        # No LLM or embedding calls should be made
        mock_llm_provider.formalize.assert_not_called()
        mock_embedding_provider.embed.assert_not_called()

    @pytest.mark.asyncio
    async def test_successful_formalization_first_attempt(
        self,
        step: FormalizationStep,
        mock_llm_provider,
        mock_embedding_provider,
        mock_semantic_verifier,
    ) -> None:
        """Test successful formalization on first attempt with high similarity."""
        informal_text = "x" * 300  # Long enough to trigger formalization
        formal_text = "The variable x must be greater than 5"

        # Setup mocks with AsyncMock for async methods
        mock_llm_provider.formalize = AsyncMock(return_value=formal_text)

        source_embedding = np.random.rand(384).astype(np.float32)
        formal_embedding = np.random.rand(384).astype(np.float32)
        mock_embedding_provider.embed = AsyncMock(side_effect=[source_embedding, formal_embedding])

        mock_semantic_verifier.calculate_similarity = lambda src, fmt: 0.95

        result = await step.execute(informal_text)

        # Should succeed on first attempt
        assert isinstance(result, Ok)
        assert result.value.formal_text == formal_text
        assert result.value.similarity_score == 0.95
        assert result.value.attempts == 1

        # Verify calls
        assert mock_embedding_provider.embed.call_count == 2  # source + formal
        mock_llm_provider.formalize.assert_called_once()

    @pytest.mark.asyncio
    async def test_retry_loop_with_improving_similarity(
        self,
        step: FormalizationStep,
        mock_llm_provider,
        mock_embedding_provider,
        mock_semantic_verifier,
    ) -> None:
        """Test retry loop when initial similarity is below threshold."""
        informal_text = "x" * 300
        formal_attempts = ["Attempt 1", "Attempt 2", "Attempt 3 - good"]

        mock_llm_provider.formalize = AsyncMock(side_effect=formal_attempts)

        source_embedding = np.random.rand(384).astype(np.float32)
        formal_embeddings = [
            np.random.rand(384).astype(np.float32),
            np.random.rand(384).astype(np.float32),
            np.random.rand(384).astype(np.float32),
        ]
        mock_embedding_provider.embed = AsyncMock(
            side_effect=[source_embedding] + formal_embeddings
        )

        # Similarity improves: 0.85, 0.88, 0.92 (meets threshold on 3rd)
        similarity_scores = [0.85, 0.88, 0.92]
        call_count = 0

        def get_similarity(src, fmt):
            nonlocal call_count
            result = similarity_scores[call_count]
            call_count += 1
            return result

        mock_semantic_verifier.calculate_similarity = get_similarity

        result = await step.execute(informal_text)

        # Should succeed on third attempt
        assert isinstance(result, Ok)
        assert result.value.formal_text == "Attempt 3 - good"
        assert result.value.similarity_score == 0.92
        assert result.value.attempts == 3

        # Verify retry behavior
        assert mock_llm_provider.formalize.call_count == 3
        assert mock_embedding_provider.embed.call_count == 4  # 1 source + 3 attempts

    @pytest.mark.asyncio
    async def test_max_retries_exhausted_returns_best(
        self,
        step: FormalizationStep,
        mock_llm_provider,
        mock_embedding_provider,
        mock_semantic_verifier,
    ) -> None:
        """Test that max retries returns best result even if below threshold."""
        informal_text = "x" * 300
        formal_attempts = ["Attempt 1", "Attempt 2", "Attempt 3"]

        mock_llm_provider.formalize = AsyncMock(side_effect=formal_attempts)

        source_embedding = np.random.rand(384).astype(np.float32)
        formal_embeddings = [
            np.random.rand(384).astype(np.float32),
            np.random.rand(384).astype(np.float32),
            np.random.rand(384).astype(np.float32),
        ]
        mock_embedding_provider.embed = AsyncMock(
            side_effect=[source_embedding] + formal_embeddings
        )

        # All below threshold, but improving: 0.80, 0.85, 0.89
        similarity_scores = [0.80, 0.85, 0.89]
        call_count = 0

        def get_similarity(src, fmt):
            nonlocal call_count
            result = similarity_scores[call_count]
            call_count += 1
            return result

        mock_semantic_verifier.calculate_similarity = get_similarity

        result = await step.execute(informal_text)

        # Should return best result (0.89 from attempt 3)
        assert isinstance(result, Ok)
        assert result.value.formal_text == "Attempt 3"
        assert result.value.similarity_score == 0.89
        assert result.value.attempts == 3

        # All retries used
        assert mock_llm_provider.formalize.call_count == 3

    @pytest.mark.asyncio
    async def test_source_embedding_failure(
        self, step: FormalizationStep, mock_embedding_provider
    ) -> None:
        """Test error handling when source embedding computation fails."""
        informal_text = "x" * 300
        mock_embedding_provider.embed = AsyncMock(
            side_effect=RuntimeError("Embedding model failed")
        )

        result = await step.execute(informal_text)

        # Should return Err
        assert isinstance(result, Err)
        assert isinstance(result.error, FormalizationError)
        assert "Failed to compute source embedding" in str(result.error)
        assert result.error.attempts == 0
        assert result.error.best_similarity == 0.0

    @pytest.mark.asyncio
    async def test_llm_provider_exception_during_formalization(
        self,
        step: FormalizationStep,
        mock_llm_provider,
        mock_embedding_provider,
        mock_semantic_verifier,
    ) -> None:
        """Test that LLM exceptions are handled gracefully in retry loop."""
        informal_text = "x" * 300

        # First two attempts throw exceptions, third succeeds
        mock_llm_provider.formalize = AsyncMock(
            side_effect=[
                RuntimeError("LLM timeout"),
                RuntimeError("LLM rate limit"),
                "Final formal text",
            ]
        )

        source_embedding = np.random.rand(384).astype(np.float32)
        formal_embedding = np.random.rand(384).astype(np.float32)
        mock_embedding_provider.embed = AsyncMock(side_effect=[source_embedding, formal_embedding])

        mock_semantic_verifier.calculate_similarity = lambda src, fmt: 0.95

        result = await step.execute(informal_text)

        # Should succeed on third attempt
        assert isinstance(result, Ok)
        assert result.value.formal_text == "Final formal text"
        assert result.value.attempts == 3

        # All retries attempted
        assert mock_llm_provider.formalize.call_count == 3

    @pytest.mark.asyncio
    async def test_all_llm_attempts_fail_with_exceptions(
        self, step: FormalizationStep, mock_llm_provider, mock_embedding_provider
    ) -> None:
        """Test when all LLM attempts fail with exceptions."""
        informal_text = "x" * 300

        # All attempts fail
        mock_llm_provider.formalize = AsyncMock(side_effect=RuntimeError("LLM unavailable"))

        source_embedding = np.random.rand(384).astype(np.float32)
        mock_embedding_provider.embed = AsyncMock(return_value=source_embedding)

        result = await step.execute(informal_text)

        # Should return Err with no successful attempts
        assert isinstance(result, Err)
        assert isinstance(result.error, FormalizationError)
        assert "failed with exceptions" in str(result.error)
        assert result.error.attempts == 3
        assert result.error.best_similarity == 0.0

    @pytest.mark.asyncio
    async def test_embedding_provider_exception_during_formalization(
        self,
        step: FormalizationStep,
        mock_llm_provider,
        mock_embedding_provider,
        mock_semantic_verifier,
    ) -> None:
        """Test embedding exceptions during formal text embedding."""
        informal_text = "x" * 300

        mock_llm_provider.formalize = AsyncMock(return_value="Formal text")

        source_embedding = np.random.rand(384).astype(np.float32)
        # Source succeeds, but formal embedding fails on first attempt, succeeds on second
        mock_embedding_provider.embed = AsyncMock(
            side_effect=[
                source_embedding,
                RuntimeError("Embedding failed"),
                np.random.rand(384).astype(np.float32),
            ]
        )

        mock_semantic_verifier.calculate_similarity = lambda src, fmt: 0.95

        result = await step.execute(informal_text)

        # Should succeed on second attempt
        assert isinstance(result, Ok)
        assert result.value.attempts == 2

    @pytest.mark.asyncio
    async def test_refinement_uses_previous_attempt_context(
        self,
        step: FormalizationStep,
        mock_llm_provider,
        mock_embedding_provider,
        mock_semantic_verifier,
    ) -> None:
        """Test that retry attempts pass previous_attempt and previous_similarity."""
        informal_text = "x" * 300
        mock_llm_provider.formalize = AsyncMock(side_effect=["First attempt", "Second attempt"])

        source_embedding = np.random.rand(384).astype(np.float32)
        formal_embeddings = [
            np.random.rand(384).astype(np.float32),
            np.random.rand(384).astype(np.float32),
        ]
        mock_embedding_provider.embed = AsyncMock(
            side_effect=[source_embedding] + formal_embeddings
        )

        # First below threshold, second meets it
        similarity_scores = [0.85, 0.92]
        call_count = 0

        def get_similarity(src, fmt):
            nonlocal call_count
            result = similarity_scores[call_count]
            call_count += 1
            return result

        mock_semantic_verifier.calculate_similarity = get_similarity

        result = await step.execute(informal_text)

        assert isinstance(result, Ok)

        # Verify first call has no previous context
        first_call = mock_llm_provider.formalize.call_args_list[0]
        assert first_call.kwargs["previous_attempt"] is None
        assert first_call.kwargs["previous_similarity"] is None

        # Verify second call has previous context
        second_call = mock_llm_provider.formalize.call_args_list[1]
        assert second_call.kwargs["previous_attempt"] == "First attempt"
        assert second_call.kwargs["previous_similarity"] == 0.85

    @pytest.mark.asyncio
    async def test_zero_skip_threshold_never_skips(
        self, mock_llm_provider, mock_embedding_provider, mock_semantic_verifier
    ) -> None:
        """Test that skip_threshold=0 disables auto-skip for short inputs."""
        step = FormalizationStep(
            llm_provider=mock_llm_provider,
            embedding_provider=mock_embedding_provider,
            verifier=mock_semantic_verifier,
            threshold=0.91,
            max_retries=3,
            skip_threshold=0,  # Never skip
        )

        short_text = "x"  # Very short
        mock_llm_provider.formalize = AsyncMock(return_value="Formal x")

        source_embedding = np.random.rand(384).astype(np.float32)
        formal_embedding = np.random.rand(384).astype(np.float32)
        mock_embedding_provider.embed = AsyncMock(side_effect=[source_embedding, formal_embedding])
        mock_semantic_verifier.calculate_similarity = lambda src, fmt: 0.95

        result = await step.execute(short_text)

        # Should NOT skip - should formalize
        assert isinstance(result, Ok)
        assert result.value.formal_text == "Formal x"
        assert result.value.attempts == 1
        mock_llm_provider.formalize.assert_called_once()

    @pytest.mark.asyncio
    async def test_boundary_similarity_exactly_at_threshold(
        self,
        step: FormalizationStep,
        mock_llm_provider,
        mock_embedding_provider,
        mock_semantic_verifier,
    ) -> None:
        """Test that similarity exactly at threshold (0.91) passes."""
        informal_text = "x" * 300
        mock_llm_provider.formalize = AsyncMock(return_value="Formal text")

        source_embedding = np.random.rand(384).astype(np.float32)
        formal_embedding = np.random.rand(384).astype(np.float32)
        mock_embedding_provider.embed = AsyncMock(side_effect=[source_embedding, formal_embedding])

        # Exactly at threshold
        mock_semantic_verifier.calculate_similarity = lambda src, fmt: 0.91

        result = await step.execute(informal_text)

        # Should succeed
        assert isinstance(result, Ok)
        assert result.value.similarity_score == 0.91
        assert result.value.attempts == 1

    @pytest.mark.asyncio
    async def test_boundary_similarity_just_below_threshold(
        self,
        step: FormalizationStep,
        mock_llm_provider,
        mock_embedding_provider,
        mock_semantic_verifier,
    ) -> None:
        """Test that similarity just below threshold triggers retry."""
        informal_text = "x" * 300
        mock_llm_provider.formalize = AsyncMock(side_effect=["Attempt 1", "Attempt 2"])

        source_embedding = np.random.rand(384).astype(np.float32)
        formal_embeddings = [
            np.random.rand(384).astype(np.float32),
            np.random.rand(384).astype(np.float32),
        ]
        mock_embedding_provider.embed = AsyncMock(
            side_effect=[source_embedding] + formal_embeddings
        )

        # First just below, second above
        similarity_scores = [0.909, 0.92]
        call_count = 0

        def get_similarity(src, fmt):
            nonlocal call_count
            result = similarity_scores[call_count]
            call_count += 1
            return result

        mock_semantic_verifier.calculate_similarity = get_similarity

        result = await step.execute(informal_text)

        # Should need second attempt
        assert isinstance(result, Ok)
        assert result.value.attempts == 2


class TestFormalizationCaching:
    """Tests for FormalizationStep caching behavior."""

    @pytest.fixture
    def mock_cache(self):
        """Create mock cache."""
        cache = Mock(spec=AsyncFileCache)
        cache.get = AsyncMock(return_value=None)
        cache.set = AsyncMock()
        cache._generate_cache_key = Mock(return_value="test_formalization_cache_key")
        return cache

    @pytest.fixture
    def step_with_cache(
        self, mock_llm_provider, mock_embedding_provider, mock_semantic_verifier, mock_cache
    ) -> FormalizationStep:
        """Create formalization step with mocked cache."""
        return FormalizationStep(
            llm_provider=mock_llm_provider,
            embedding_provider=mock_embedding_provider,
            verifier=mock_semantic_verifier,
            threshold=0.91,
            max_retries=3,
            skip_threshold=200,
            cache=mock_cache,
        )

    @pytest.mark.asyncio
    async def test_successful_formalization_with_caching(
        self,
        step_with_cache: FormalizationStep,
        mock_llm_provider,
        mock_embedding_provider,
        mock_semantic_verifier,
        mock_cache,
    ) -> None:
        """Test successful formalization writes to cache."""
        informal_text = "x" * 300
        formal_text = "The variable x must be greater than 5"

        # Setup mocks
        mock_llm_provider.formalize = AsyncMock(return_value=formal_text)
        source_embedding = np.random.rand(384).astype(np.float32)
        formal_embedding = np.random.rand(384).astype(np.float32)
        mock_embedding_provider.embed = AsyncMock(side_effect=[source_embedding, formal_embedding])
        mock_semantic_verifier.calculate_similarity = lambda src, fmt: 0.95

        result = await step_with_cache.execute(informal_text)

        # Verify success
        assert isinstance(result, Ok)
        assert result.value.formal_text == formal_text
        assert result.value.similarity_score == 0.95
        assert result.value.attempts == 1

        # Verify cache was written
        mock_cache.set.assert_called_once()
        call_args = mock_cache.set.call_args
        assert call_args[0][0] == "test_formalization_cache_key"
        cached_data = call_args[0][1]
        assert cached_data["formal_text"] == formal_text
        assert cached_data["similarity"] == 0.95
        assert cached_data["attempts"] == 1

    @pytest.mark.asyncio
    async def test_formalization_cache_hit(
        self,
        step_with_cache: FormalizationStep,
        mock_llm_provider,
        mock_embedding_provider,
        mock_cache,
    ) -> None:
        """Test that cache hit returns cached result without calling LLM."""
        informal_text = "x" * 300
        cached_data = {
            "formal_text": "Cached formal text",
            "similarity": 0.93,
            "attempts": 2,
        }

        # Mock cache hit
        mock_cache.get = AsyncMock(return_value=cached_data)

        result = await step_with_cache.execute(informal_text)

        # Verify cached result returned
        assert isinstance(result, Ok)
        assert result.value.formal_text == "Cached formal text"
        assert result.value.similarity_score == 0.93
        assert result.value.attempts == 2

        # Verify no LLM or embedding calls
        mock_llm_provider.formalize.assert_not_called()
        mock_embedding_provider.embed.assert_not_called()

        # Cache get was called, but set was not (already cached)
        mock_cache.get.assert_called_once()
        mock_cache.set.assert_not_called()

    @pytest.mark.asyncio
    async def test_llm_exception_prevents_cache_write(
        self,
        step_with_cache: FormalizationStep,
        mock_llm_provider,
        mock_embedding_provider,
        mock_cache,
    ) -> None:
        """Test that LLM exceptions prevent cache write."""
        informal_text = "x" * 300

        # All LLM calls fail
        mock_llm_provider.formalize = AsyncMock(side_effect=RuntimeError("LLM error"))

        source_embedding = np.random.rand(384).astype(np.float32)
        mock_embedding_provider.embed = AsyncMock(return_value=source_embedding)

        result = await step_with_cache.execute(informal_text)

        # Should return Err
        assert isinstance(result, Err)

        # Cache should not be written
        mock_cache.set.assert_not_called()

    @pytest.mark.asyncio
    async def test_cache_read_failure_doesnt_break_execution(
        self,
        step_with_cache: FormalizationStep,
        mock_llm_provider,
        mock_embedding_provider,
        mock_semantic_verifier,
        mock_cache,
    ) -> None:
        """Test that cache read failures don't prevent formalization."""
        informal_text = "x" * 300
        formal_text = "Formal text"

        # Cache read raises exception
        mock_cache.get = AsyncMock(side_effect=RuntimeError("Cache read error"))

        # Normal formalization mocks
        mock_llm_provider.formalize = AsyncMock(return_value=formal_text)
        source_embedding = np.random.rand(384).astype(np.float32)
        formal_embedding = np.random.rand(384).astype(np.float32)
        mock_embedding_provider.embed = AsyncMock(side_effect=[source_embedding, formal_embedding])
        mock_semantic_verifier.calculate_similarity = lambda src, fmt: 0.95

        result = await step_with_cache.execute(informal_text)

        # Should succeed despite cache error
        assert isinstance(result, Ok)
        assert result.value.formal_text == formal_text
        assert result.value.similarity_score == 0.95

        # Cache write should still be attempted
        mock_cache.set.assert_called_once()

    @pytest.mark.asyncio
    async def test_cache_write_failure_doesnt_break_execution(
        self,
        step_with_cache: FormalizationStep,
        mock_llm_provider,
        mock_embedding_provider,
        mock_semantic_verifier,
        mock_cache,
    ) -> None:
        """Test that cache write failures don't prevent success."""
        informal_text = "x" * 300
        formal_text = "Formal text"

        # Cache write raises exception
        mock_cache.set = AsyncMock(side_effect=RuntimeError("Cache write error"))

        # Normal formalization mocks
        mock_llm_provider.formalize = AsyncMock(return_value=formal_text)
        source_embedding = np.random.rand(384).astype(np.float32)
        formal_embedding = np.random.rand(384).astype(np.float32)
        mock_embedding_provider.embed = AsyncMock(side_effect=[source_embedding, formal_embedding])
        mock_semantic_verifier.calculate_similarity = lambda src, fmt: 0.95

        result = await step_with_cache.execute(informal_text)

        # Should succeed despite cache error
        assert isinstance(result, Ok)
        assert result.value.formal_text == formal_text
        assert result.value.similarity_score == 0.95

    @pytest.mark.asyncio
    async def test_best_result_cached_after_retries(
        self,
        step_with_cache: FormalizationStep,
        mock_llm_provider,
        mock_embedding_provider,
        mock_semantic_verifier,
        mock_cache,
    ) -> None:
        """Test that best result is cached even if threshold not met."""
        informal_text = "x" * 300

        # All attempts below threshold
        mock_llm_provider.formalize = AsyncMock(side_effect=["Attempt 1", "Attempt 2", "Attempt 3"])

        source_embedding = np.random.rand(384).astype(np.float32)
        formal_embeddings = [np.random.rand(384).astype(np.float32) for _ in range(3)]
        mock_embedding_provider.embed = AsyncMock(
            side_effect=[source_embedding] + formal_embeddings
        )

        # All attempts below threshold, but improving
        similarity_scores = [0.75, 0.82, 0.89]
        call_count = 0

        def get_similarity(src, fmt):
            nonlocal call_count
            result = similarity_scores[call_count]
            call_count += 1
            return result

        mock_semantic_verifier.calculate_similarity = get_similarity

        result = await step_with_cache.execute(informal_text)

        # Should return best result
        assert isinstance(result, Ok)
        assert result.value.formal_text == "Attempt 3"
        assert result.value.similarity_score == 0.89
        assert result.value.attempts == 3

        # Verify cache was written with best result
        mock_cache.set.assert_called_once()
        call_args = mock_cache.set.call_args
        cached_data = call_args[0][1]
        assert cached_data["formal_text"] == "Attempt 3"
        assert cached_data["similarity"] == 0.89
        assert cached_data["attempts"] == 3
