"""Tests for the web search enrichment step."""

from unittest.mock import AsyncMock, MagicMock

import pytest

from src.domain.exceptions import EnrichmentError
from src.domain.models import EnrichmentResult
from src.domain.steps.enrichment import EnrichmentStep
from src.shared.result import Err, Ok


@pytest.fixture
def mock_llm_provider() -> MagicMock:
    """Create a mock LLM provider."""
    provider = MagicMock()
    provider.enrich_with_web_search = AsyncMock()
    return provider


class TestEnrichmentStep:
    """Tests for EnrichmentStep."""

    @pytest.mark.asyncio
    async def test_successful_enrichment(self, mock_llm_provider: MagicMock) -> None:
        """Test successful enrichment with web search results."""
        # Arrange
        input_text = "The Riemann hypothesis states that all non-trivial zeros have real part 1/2"
        enriched_text = """Context: The Riemann hypothesis is one of the most important unsolved problems in mathematics.

The Riemann hypothesis states that all non-trivial zeros of the Riemann zeta function have real part equal to 1/2.

Key terms:
- Riemann zeta function: A complex function defined for complex numbers
- Non-trivial zeros: The zeros that are not negative even integers
- Real part: The component of a complex number on the real axis"""

        mock_llm_provider.enrich_with_web_search.return_value = (
            enriched_text,
            2,  # search_count
            [
                "https://en.wikipedia.org/wiki/Riemann_hypothesis",
                "https://mathworld.wolfram.com/RiemannHypothesis.html",
            ],
        )

        step = EnrichmentStep(
            llm_provider=mock_llm_provider,
            max_searches=5,
            timeout=60.0,
        )

        # Act
        result = await step.execute(input_text)

        # Assert
        assert isinstance(result, Ok)
        enrichment_result = result.value
        assert isinstance(enrichment_result, EnrichmentResult)
        assert enrichment_result.enriched_text == enriched_text
        assert enrichment_result.original_text == input_text
        assert enrichment_result.search_count == 2
        assert len(enrichment_result.sources_used) == 2
        assert enrichment_result.enrichment_time_seconds >= 0

        mock_llm_provider.enrich_with_web_search.assert_called_once_with(
            text=input_text,
            max_searches=5,
        )

    @pytest.mark.asyncio
    async def test_enrichment_with_no_searches(self, mock_llm_provider: MagicMock) -> None:
        """Test enrichment when no web searches are needed."""
        # Arrange
        input_text = "x must be greater than 5"
        enriched_text = "The variable x must satisfy the constraint: x > 5"

        mock_llm_provider.enrich_with_web_search.return_value = (
            enriched_text,
            0,  # No searches needed
            [],
        )

        step = EnrichmentStep(
            llm_provider=mock_llm_provider,
            max_searches=5,
            timeout=60.0,
        )

        # Act
        result = await step.execute(input_text)

        # Assert
        assert isinstance(result, Ok)
        enrichment_result = result.value
        assert enrichment_result.search_count == 0
        assert enrichment_result.sources_used == []

    @pytest.mark.asyncio
    async def test_enrichment_failure(self, mock_llm_provider: MagicMock) -> None:
        """Test enrichment failure handling."""
        # Arrange
        input_text = "Some text to enrich"
        mock_llm_provider.enrich_with_web_search.side_effect = Exception("API error")

        step = EnrichmentStep(
            llm_provider=mock_llm_provider,
            max_searches=5,
            timeout=60.0,
        )

        # Act
        result = await step.execute(input_text)

        # Assert
        assert isinstance(result, Err)
        error = result.error
        assert isinstance(error, EnrichmentError)
        assert "API error" in str(error)
        assert error.search_count == 0

    @pytest.mark.asyncio
    async def test_enrichment_with_custom_max_searches(self, mock_llm_provider: MagicMock) -> None:
        """Test enrichment with custom max_searches parameter."""
        # Arrange
        input_text = "Test text"
        mock_llm_provider.enrich_with_web_search.return_value = ("Enriched", 3, [])

        step = EnrichmentStep(
            llm_provider=mock_llm_provider,
            max_searches=10,
            timeout=120.0,
        )

        # Act
        await step.execute(input_text)

        # Assert
        mock_llm_provider.enrich_with_web_search.assert_called_once_with(
            text=input_text,
            max_searches=10,
        )


class TestEnrichmentResult:
    """Tests for EnrichmentResult model."""

    def test_enrichment_result_creation(self) -> None:
        """Test creating EnrichmentResult with valid data."""
        result = EnrichmentResult(
            enriched_text="Enriched version",
            original_text="Original text",
            search_count=3,
            sources_used=["https://example.com/1", "https://example.com/2"],
            enrichment_time_seconds=1.5,
        )

        assert result.enriched_text == "Enriched version"
        assert result.original_text == "Original text"
        assert result.search_count == 3
        assert len(result.sources_used) == 2
        assert result.enrichment_time_seconds == 1.5

    def test_enrichment_result_is_immutable(self) -> None:
        """Test that EnrichmentResult is immutable."""
        from pydantic import ValidationError as PydanticValidationError

        result = EnrichmentResult(
            enriched_text="Text",
            original_text="Original",
            search_count=1,
            sources_used=[],
            enrichment_time_seconds=0.5,
        )

        with pytest.raises(PydanticValidationError):
            result.search_count = 5  # type: ignore


class TestEnrichmentError:
    """Tests for EnrichmentError exception."""

    def test_enrichment_error_creation(self) -> None:
        """Test creating EnrichmentError with attributes."""
        error = EnrichmentError("Test error message", search_count=2)

        assert str(error) == "Test error message"
        assert error.search_count == 2

    def test_enrichment_error_default_search_count(self) -> None:
        """Test EnrichmentError with default search_count."""
        error = EnrichmentError("Error")

        assert error.search_count == 0
