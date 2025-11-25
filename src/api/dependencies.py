"""Dependency injection for FastAPI.

Provides singleton instances of infrastructure components and per-request services.
"""

from functools import lru_cache

from src.application.pipeline_service import PipelineService
from src.infrastructure.embeddings.sentence_transformer import SentenceTransformerProvider
from src.infrastructure.llm.client import AnthropicClient
from src.infrastructure.smt.cvc5_executor import Cvc5Executor
from src.shared.config import Settings


@lru_cache
def get_settings() -> Settings:
    """Get application settings (singleton).

    Cached because settings are expensive to load and should be reused.

    Returns:
        Application settings
    """
    return Settings()


@lru_cache
def get_embedding_provider() -> SentenceTransformerProvider:
    """Get embedding provider (singleton).

    Cached because loading the model is expensive (~100-200MB).
    The model is reused across all requests.

    Returns:
        Sentence transformer provider
    """
    settings = get_settings()
    return SentenceTransformerProvider(model_name=settings.embedding_model_name)


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


def get_pipeline_service() -> PipelineService:
    """Get pipeline service (per-request).

    NOT cached because PipelineService is lightweight and we want
    clean state per request.

    Returns:
        Pipeline service instance
    """
    return PipelineService(
        embedding_provider=get_embedding_provider(),
        llm_provider=get_llm_provider(),
        smt_solver=get_smt_solver(),
        settings=get_settings(),
    )
