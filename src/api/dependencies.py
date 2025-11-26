"""Dependency injection for FastAPI.

Provides singleton instances of infrastructure components and per-request services.
"""

import asyncio
from functools import lru_cache

from src.application.pipeline_service import PipelineService
from src.infrastructure.embeddings.sentence_transformer import SentenceTransformerProvider
from src.infrastructure.llm.client import AnthropicClient
from src.infrastructure.smt.cvc5_executor import Cvc5Executor
from src.shared.config import Settings

# Module-level task for async lazy loading of embedding provider
# This ensures only one loading task is created even with concurrent requests
_embedding_provider_task: asyncio.Task[SentenceTransformerProvider] | None = None


@lru_cache
def get_settings() -> Settings:
    """Get application settings (singleton).

    Cached because settings are expensive to load and should be reused.

    Returns:
        Application settings
    """
    return Settings()


async def _load_embedding_provider() -> SentenceTransformerProvider:
    """Load embedding provider asynchronously.

    This helper function loads the SentenceTransformer model in a thread pool
    executor to avoid blocking the event loop. The model loading is CPU-bound
    and synchronous, so we offload it to a thread.

    Returns:
        Loaded SentenceTransformer provider

    Raises:
        RuntimeError: If loading fails
    """
    settings = get_settings()

    # Run synchronous model loading in thread pool to avoid blocking
    loop = asyncio.get_event_loop()
    provider = await loop.run_in_executor(
        None,  # Use default thread pool executor
        lambda: SentenceTransformerProvider(model_name=settings.embedding_model_name),
    )

    return provider


async def get_embedding_provider() -> SentenceTransformerProvider:
    """Get embedding provider (singleton) with async lazy loading.

    This function uses the asyncio.Task pattern for safe lazy initialization:
    - First call: Creates a Task to load the model asynchronously
    - Concurrent calls: Await the same Task (no race conditions)
    - Subsequent calls: Return the already-loaded instance instantly

    The model is loaded on first use rather than at startup, improving
    application startup time while maintaining thread safety.

    Returns:
        Sentence transformer provider (singleton instance)

    Raises:
        RuntimeError: If loading fails

    SOLID Principles Applied:
    - SRP: This function only manages provider lifecycle
    - OCP: Pattern is extensible to other lazy-loaded dependencies
    - DIP: Callers depend on abstract interface, not loading mechanism
    """
    global _embedding_provider_task

    # If task doesn't exist, create it (first call or after reset)
    if _embedding_provider_task is None:
        _embedding_provider_task = asyncio.create_task(_load_embedding_provider())

    # Await the task (either newly created or already running/completed)
    # If task is already complete, this returns immediately with cached result
    # If task is running, this waits for completion
    # Multiple concurrent calls will all await the same task
    provider = await _embedding_provider_task

    return provider


@lru_cache
def get_llm_provider() -> AnthropicClient:
    """Get LLM provider (singleton).

    Cached for connection pooling and client reuse.

    Returns:
        Anthropic Claude client
    """
    return AnthropicClient()


@lru_cache
def get_smt_solver() -> Cvc5Executor:
    """Get SMT solver (singleton).

    Cached because the executor is stateless and can be reused.

    Returns:
        cvc5 executor
    """
    return Cvc5Executor()


async def get_pipeline_service() -> PipelineService:
    """Get pipeline service (per-request).

    NOT cached because PipelineService is lightweight and we want
    clean state per request.

    Note: This is now async because it depends on async get_embedding_provider().

    Returns:
        Pipeline service instance
    """
    # Await the async embedding provider
    embedding_provider = await get_embedding_provider()

    return PipelineService(
        embedding_provider=embedding_provider,
        llm_provider=get_llm_provider(),
        smt_solver=get_smt_solver(),
        settings=get_settings(),
    )
