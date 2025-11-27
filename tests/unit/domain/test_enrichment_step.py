"""Unit tests for EnrichmentStep with focus on cache safety.

Tests cover:
- Successful enrichment with caching
- APIError prevents cache write
- APITimeoutError prevents cache write
- Cache read failures don't break execution
- Cache write failures don't break execution
"""

from unittest.mock import AsyncMock, Mock

import anthropic
import pytest

from src.domain.exceptions import EnrichmentError
from src.domain.steps.enrichment import EnrichmentStep
from src.infrastructure.cache import AsyncFileCache
from src.shared.result import Err, Ok


class TestEnrichmentStep:
    """Tests for EnrichmentStep with cache safety verification."""

    @pytest.fixture
    def mock_llm_provider(self):
        """Create mock LLM provider."""
        provider = Mock()
        provider.enrich_with_web_search = AsyncMock()
        return provider

    @pytest.fixture
    def mock_cache(self):
        """Create mock cache."""
        cache = Mock(spec=AsyncFileCache)
        cache.get = AsyncMock(return_value=None)
        cache.set = AsyncMock()
        cache._generate_cache_key = Mock(return_value="test_cache_key")
        return cache

    @pytest.fixture
    def step_with_cache(self, mock_llm_provider, mock_cache) -> EnrichmentStep:
        """Create enrichment step with mocked cache."""
        return EnrichmentStep(
            llm_provider=mock_llm_provider,
            max_searches=5,
            timeout=60.0,
            cache=mock_cache,
        )

    @pytest.fixture
    def step_without_cache(self, mock_llm_provider) -> EnrichmentStep:
        """Create enrichment step without cache."""
        return EnrichmentStep(
            llm_provider=mock_llm_provider,
            max_searches=5,
            timeout=60.0,
            cache=None,
        )

    @pytest.mark.asyncio
    async def test_successful_enrichment_with_caching(
        self,
        step_with_cache: EnrichmentStep,
        mock_llm_provider,
        mock_cache,
    ) -> None:
        """Test successful enrichment writes to cache."""
        input_text = "stainless steel thermal expansion"
        enriched_text = "Stainless steel has a coefficient of thermal expansion..."
        sources = ["https://example.com/steel", "https://example.com/thermal"]

        # Mock successful API call
        mock_llm_provider.enrich_with_web_search.return_value = (
            enriched_text,
            2,  # search_count
            sources,
        )

        result = await step_with_cache.execute(input_text)

        # Verify success
        assert isinstance(result, Ok)
        assert result.value.enriched_text == enriched_text
        assert result.value.search_count == 2
        assert result.value.sources_used == sources

        # Verify cache was written
        mock_cache.set.assert_called_once()
        call_args = mock_cache.set.call_args
        assert call_args[0][0] == "test_cache_key"  # cache key
        cached_data = call_args[0][1]
        assert cached_data["enriched_text"] == enriched_text
        assert cached_data["search_count"] == 2
        assert cached_data["sources_used"] == sources

    @pytest.mark.asyncio
    async def test_api_error_prevents_cache_write(
        self,
        step_with_cache: EnrichmentStep,
        mock_llm_provider,
        mock_cache,
    ) -> None:
        """Test that anthropic.APIError prevents cache write.

        This verifies the critical safety property: if the Anthropic API
        returns an error (500, 429, etc.), we must NOT cache anything.
        """
        input_text = "test input"

        # Mock API error (e.g., HTTP 500 Internal Server Error)
        mock_llm_provider.enrich_with_web_search.side_effect = anthropic.InternalServerError(
            message="Internal server error",
            response=Mock(status_code=500),
            body=None,
        )

        result = await step_with_cache.execute(input_text)

        # Verify failure
        assert isinstance(result, Err)
        assert isinstance(result.error, EnrichmentError)
        assert "Internal server error" in str(result.error)

        # CRITICAL: Verify cache was NOT written
        mock_cache.set.assert_not_called()

    @pytest.mark.asyncio
    async def test_api_timeout_prevents_cache_write(
        self,
        step_with_cache: EnrichmentStep,
        mock_llm_provider,
        mock_cache,
    ) -> None:
        """Test that anthropic.APITimeoutError prevents cache write.

        This covers the HTTP 504 Gateway Timeout scenario that was observed
        in production. Timeouts must NOT be cached.
        """
        input_text = "test input"

        # Mock API timeout (e.g., HTTP 504 Gateway Timeout)
        mock_llm_provider.enrich_with_web_search.side_effect = anthropic.APITimeoutError(
            request=Mock(),
        )

        result = await step_with_cache.execute(input_text)

        # Verify failure
        assert isinstance(result, Err)
        assert isinstance(result.error, EnrichmentError)

        # CRITICAL: Verify cache was NOT written
        mock_cache.set.assert_not_called()

    @pytest.mark.asyncio
    async def test_rate_limit_error_prevents_cache_write(
        self,
        step_with_cache: EnrichmentStep,
        mock_llm_provider,
        mock_cache,
    ) -> None:
        """Test that anthropic.RateLimitError prevents cache write.

        Rate limit errors (HTTP 429) should not be cached.
        """
        input_text = "test input"

        # Mock rate limit error (HTTP 429)
        mock_llm_provider.enrich_with_web_search.side_effect = anthropic.RateLimitError(
            message="Rate limit exceeded",
            response=Mock(status_code=429),
            body=None,
        )

        result = await step_with_cache.execute(input_text)

        # Verify failure
        assert isinstance(result, Err)
        assert isinstance(result.error, EnrichmentError)

        # CRITICAL: Verify cache was NOT written
        mock_cache.set.assert_not_called()

    @pytest.mark.asyncio
    async def test_connection_error_prevents_cache_write(
        self,
        step_with_cache: EnrichmentStep,
        mock_llm_provider,
        mock_cache,
    ) -> None:
        """Test that anthropic.APIConnectionError prevents cache write.

        Network/connection errors should not be cached.
        """
        input_text = "test input"

        # Mock connection error
        mock_llm_provider.enrich_with_web_search.side_effect = anthropic.APIConnectionError(
            message="Connection failed",
            request=Mock(),
        )

        result = await step_with_cache.execute(input_text)

        # Verify failure
        assert isinstance(result, Err)
        assert isinstance(result.error, EnrichmentError)

        # CRITICAL: Verify cache was NOT written
        mock_cache.set.assert_not_called()

    @pytest.mark.asyncio
    async def test_cache_read_failure_continues_execution(
        self,
        step_with_cache: EnrichmentStep,
        mock_llm_provider,
        mock_cache,
    ) -> None:
        """Test that cache read failures don't break execution."""
        input_text = "test input"
        enriched_text = "enriched result"

        # Mock cache read failure
        mock_cache.get.side_effect = Exception("Cache read failed")

        # Mock successful API call
        mock_llm_provider.enrich_with_web_search.return_value = (
            enriched_text,
            1,
            ["https://example.com"],
        )

        result = await step_with_cache.execute(input_text)

        # Verify success despite cache read failure
        assert isinstance(result, Ok)
        assert result.value.enriched_text == enriched_text

        # Verify cache write was still attempted
        mock_cache.set.assert_called_once()

    @pytest.mark.asyncio
    async def test_cache_write_failure_doesnt_break_execution(
        self,
        step_with_cache: EnrichmentStep,
        mock_llm_provider,
        mock_cache,
    ) -> None:
        """Test that cache write failures don't break execution."""
        input_text = "test input"
        enriched_text = "enriched result"

        # Mock successful API call
        mock_llm_provider.enrich_with_web_search.return_value = (
            enriched_text,
            1,
            ["https://example.com"],
        )

        # Mock cache write failure
        mock_cache.set.side_effect = Exception("Cache write failed")

        result = await step_with_cache.execute(input_text)

        # Verify success despite cache write failure
        assert isinstance(result, Ok)
        assert result.value.enriched_text == enriched_text

    @pytest.mark.asyncio
    async def test_successful_enrichment_without_cache(
        self,
        step_without_cache: EnrichmentStep,
        mock_llm_provider,
    ) -> None:
        """Test successful enrichment works without cache."""
        input_text = "test input"
        enriched_text = "enriched result"

        # Mock successful API call
        mock_llm_provider.enrich_with_web_search.return_value = (
            enriched_text,
            1,
            ["https://example.com"],
        )

        result = await step_without_cache.execute(input_text)

        # Verify success
        assert isinstance(result, Ok)
        assert result.value.enriched_text == enriched_text

    @pytest.mark.asyncio
    async def test_cache_hit_returns_cached_data(
        self,
        step_with_cache: EnrichmentStep,
        mock_llm_provider,
        mock_cache,
    ) -> None:
        """Test that cache hit returns cached data without API call."""
        input_text = "test input"
        cached_data = {
            "enriched_text": "cached enriched text",
            "search_count": 3,
            "sources_used": ["https://cached.com"],
        }

        # Mock cache hit
        mock_cache.get.return_value = cached_data

        result = await step_with_cache.execute(input_text)

        # Verify cached data returned
        assert isinstance(result, Ok)
        assert result.value.enriched_text == cached_data["enriched_text"]
        assert result.value.search_count == cached_data["search_count"]
        assert result.value.sources_used == cached_data["sources_used"]

        # Verify API was NOT called
        mock_llm_provider.enrich_with_web_search.assert_not_called()

        # Verify cache was NOT written (already cached)
        mock_cache.set.assert_not_called()
