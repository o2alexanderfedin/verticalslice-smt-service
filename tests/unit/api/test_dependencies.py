"""Unit tests for API dependency injection.

Tests cover:
- Settings singleton initialization
- Embedding provider singleton with correct model
- LLM provider singleton initialization
- SMT solver singleton initialization
- Pipeline service creation with dependencies
- Cache behavior (lru_cache)
"""

from unittest.mock import Mock

import pytest

from src.api.dependencies import (
    get_embedding_provider,
    get_llm_provider,
    get_pipeline_service,
    get_settings,
    get_smt_solver,
)
from src.application.pipeline_service import PipelineService
from src.infrastructure.embeddings.sentence_transformer import SentenceTransformerProvider
from src.infrastructure.llm.client import AnthropicClient
from src.infrastructure.smt.cvc5_executor import Cvc5Executor
from src.shared.config import Settings


class TestDependencies:
    """Tests for API dependency injection."""

    # ========================================================================
    # Settings Tests
    # ========================================================================

    def test_get_settings_returns_settings_instance(self):
        """Test get_settings returns Settings instance."""
        # Clear cache first
        get_settings.cache_clear()

        settings = get_settings()

        assert isinstance(settings, Settings)
        assert settings.api_title is not None
        assert settings.api_version is not None

    def test_get_settings_is_cached(self):
        """Test get_settings returns same instance (singleton)."""
        get_settings.cache_clear()

        settings1 = get_settings()
        settings2 = get_settings()

        # Should be same object (cached)
        assert settings1 is settings2

    def test_settings_has_required_configuration(self):
        """Test settings has all required configuration values."""
        get_settings.cache_clear()
        settings = get_settings()

        # API config
        assert hasattr(settings, "api_title")
        assert hasattr(settings, "api_version")

        # Thresholds
        assert hasattr(settings, "formalization_similarity_threshold")
        assert hasattr(settings, "extraction_max_degradation")

        # Retry config
        assert hasattr(settings, "formalization_max_retries")
        assert hasattr(settings, "extraction_max_retries")
        assert hasattr(settings, "validation_max_retries")

        # Model config
        assert hasattr(settings, "embedding_model_name")

    def test_settings_thresholds_within_valid_range(self):
        """Test settings thresholds are within valid ranges."""
        get_settings.cache_clear()
        settings = get_settings()

        # Similarity threshold should be 0-1
        assert 0.0 <= settings.formalization_similarity_threshold <= 1.0

        # Degradation should be 0-1
        assert 0.0 <= settings.extraction_max_degradation <= 1.0

    def test_settings_retry_counts_positive(self):
        """Test settings retry counts are positive."""
        get_settings.cache_clear()
        settings = get_settings()

        assert settings.formalization_max_retries >= 1
        assert settings.extraction_max_retries >= 1
        assert settings.validation_max_retries >= 1

    # ========================================================================
    # Embedding Provider Tests
    # ========================================================================

    @pytest.mark.asyncio
    async def test_get_embedding_provider_returns_sentence_transformer(self, mocker):
        """Test get_embedding_provider returns SentenceTransformerProvider."""
        # Reset singleton
        import src.api.dependencies as deps

        deps._embedding_provider_task = None
        get_settings.cache_clear()

        # Mock SentenceTransformer to avoid loading real model
        mock_model = Mock()
        mock_model.get_sentence_embedding_dimension.return_value = 384
        mocker.patch("sentence_transformers.SentenceTransformer", return_value=mock_model)

        provider = await get_embedding_provider()

        assert isinstance(provider, SentenceTransformerProvider)

    @pytest.mark.asyncio
    async def test_get_embedding_provider_is_cached(self, mocker):
        """Test get_embedding_provider returns same instance (singleton)."""
        # Reset singleton
        import src.api.dependencies as deps

        deps._embedding_provider_task = None
        get_settings.cache_clear()

        # Mock to avoid loading model
        mock_model = Mock()
        mock_model.get_sentence_embedding_dimension.return_value = 384
        mocker.patch("sentence_transformers.SentenceTransformer", return_value=mock_model)

        provider1 = await get_embedding_provider()
        provider2 = await get_embedding_provider()

        # Should be same object (cached)
        assert provider1 is provider2

    @pytest.mark.asyncio
    async def test_embedding_provider_uses_settings_model_name(self, mocker):
        """Test embedding provider uses model name from settings."""
        # Reset singleton
        import src.api.dependencies as deps

        deps._embedding_provider_task = None
        get_settings.cache_clear()

        mock_model = Mock()
        mock_model.get_sentence_embedding_dimension.return_value = 384
        # Patch in the provider module where it's imported
        mock_st_class = mocker.patch(
            "src.infrastructure.embeddings.sentence_transformer.SentenceTransformer",
            return_value=mock_model,
        )

        await get_embedding_provider()

        # Should have been called with model name from settings
        settings = get_settings()
        mock_st_class.assert_called_once_with(settings.embedding_model_name)

    # ========================================================================
    # LLM Provider Tests
    # ========================================================================

    def test_get_llm_provider_returns_anthropic_client(self, mocker):
        """Test get_llm_provider returns AnthropicClient."""
        get_llm_provider.cache_clear()

        # Mock Anthropic client initialization
        mocker.patch.dict("os.environ", {"ANTHROPIC_API_KEY": "test-key"})
        mocker.patch("anthropic.AsyncAnthropic")

        provider = get_llm_provider()

        assert isinstance(provider, AnthropicClient)

    def test_get_llm_provider_is_cached(self, mocker):
        """Test get_llm_provider returns same instance (singleton)."""
        get_llm_provider.cache_clear()

        mocker.patch.dict("os.environ", {"ANTHROPIC_API_KEY": "test-key"})
        mocker.patch("anthropic.AsyncAnthropic")

        provider1 = get_llm_provider()
        provider2 = get_llm_provider()

        # Should be same object (cached)
        assert provider1 is provider2

    # ========================================================================
    # SMT Solver Tests
    # ========================================================================

    def test_get_smt_solver_returns_cvc5_executor(self):
        """Test get_smt_solver returns Cvc5Executor."""
        get_smt_solver.cache_clear()

        solver = get_smt_solver()

        assert isinstance(solver, Cvc5Executor)

    def test_get_smt_solver_is_cached(self):
        """Test get_smt_solver returns same instance (singleton)."""
        get_smt_solver.cache_clear()

        solver1 = get_smt_solver()
        solver2 = get_smt_solver()

        # Should be same object (cached)
        assert solver1 is solver2

    # ========================================================================
    # Pipeline Service Tests
    # ========================================================================

    @pytest.mark.asyncio
    async def test_get_pipeline_service_returns_pipeline_service(self, mocker):
        """Test get_pipeline_service returns PipelineService."""
        get_settings.cache_clear()
        # Reset singleton
        import src.api.dependencies as deps

        deps._embedding_provider_task = None
        get_llm_provider.cache_clear()
        get_smt_solver.cache_clear()

        # Mock all dependencies
        mock_model = Mock()
        mock_model.get_sentence_embedding_dimension.return_value = 384
        mocker.patch("sentence_transformers.SentenceTransformer", return_value=mock_model)
        mocker.patch.dict("os.environ", {"ANTHROPIC_API_KEY": "test-key"})
        mocker.patch("anthropic.AsyncAnthropic")

        service = await get_pipeline_service()

        assert isinstance(service, PipelineService)

    @pytest.mark.asyncio
    async def test_get_pipeline_service_not_cached(self, mocker):
        """Test get_pipeline_service returns new instance each time (not cached)."""
        get_settings.cache_clear()
        # Reset singleton
        import src.api.dependencies as deps

        deps._embedding_provider_task = None
        get_llm_provider.cache_clear()
        get_smt_solver.cache_clear()

        # Mock dependencies
        mock_model = Mock()
        mock_model.get_sentence_embedding_dimension.return_value = 384
        mocker.patch("sentence_transformers.SentenceTransformer", return_value=mock_model)
        mocker.patch.dict("os.environ", {"ANTHROPIC_API_KEY": "test-key"})
        mocker.patch("anthropic.AsyncAnthropic")

        service1 = await get_pipeline_service()
        service2 = await get_pipeline_service()

        # Should be different objects (not cached)
        assert service1 is not service2

    @pytest.mark.asyncio
    async def test_pipeline_service_has_all_dependencies(self, mocker):
        """Test pipeline service is initialized with all dependencies."""
        get_settings.cache_clear()
        # Reset singleton
        import src.api.dependencies as deps

        deps._embedding_provider_task = None
        get_llm_provider.cache_clear()
        get_smt_solver.cache_clear()

        # Mock dependencies
        mock_model = Mock()
        mock_model.get_sentence_embedding_dimension.return_value = 384
        mocker.patch("sentence_transformers.SentenceTransformer", return_value=mock_model)
        mocker.patch.dict("os.environ", {"ANTHROPIC_API_KEY": "test-key"})
        mocker.patch("anthropic.AsyncAnthropic")

        service = await get_pipeline_service()

        # Verify service has dependencies
        assert service.embedding_provider is not None
        assert service.llm_provider is not None
        assert service.smt_solver is not None
        assert service.settings is not None

    @pytest.mark.asyncio
    async def test_pipeline_service_uses_singleton_dependencies(self, mocker):
        """Test pipeline service uses singleton instances of dependencies."""
        get_settings.cache_clear()
        # Reset singleton
        import src.api.dependencies as deps

        deps._embedding_provider_task = None
        get_llm_provider.cache_clear()
        get_smt_solver.cache_clear()

        # Mock dependencies
        mock_model = Mock()
        mock_model.get_sentence_embedding_dimension.return_value = 384
        mocker.patch("sentence_transformers.SentenceTransformer", return_value=mock_model)
        mocker.patch.dict("os.environ", {"ANTHROPIC_API_KEY": "test-key"})
        mocker.patch("anthropic.AsyncAnthropic")

        # Get singletons
        settings = get_settings()
        embedding_provider = await get_embedding_provider()
        llm_provider = get_llm_provider()
        smt_solver = get_smt_solver()

        # Create service
        service = await get_pipeline_service()

        # Service should use same singleton instances
        assert service.settings is settings
        assert service.embedding_provider is embedding_provider
        assert service.llm_provider is llm_provider
        assert service.smt_solver is smt_solver
