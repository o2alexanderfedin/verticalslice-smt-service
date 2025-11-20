"""Step 0: Optional web search enrichment.

Enriches input text with domain knowledge using web search.
This is an optional preprocessing step that runs before formalization.
"""

import logging
import time
from typing import TYPE_CHECKING

from src.domain.exceptions import EnrichmentError
from src.domain.models import EnrichmentResult
from src.shared.result import Err, Ok, Result

if TYPE_CHECKING:
    from src.domain.protocols import LLMProvider

logger = logging.getLogger(__name__)


class EnrichmentStep:
    """Step 0: Optional web search enrichment."""

    def __init__(
        self,
        llm_provider: "LLMProvider",
        max_searches: int = 5,
        timeout: float = 60.0,
    ):
        """Initialize enrichment step.

        Args:
            llm_provider: Provider for LLM calls with web search
            max_searches: Maximum number of web searches to perform
            timeout: Timeout for enrichment in seconds
        """
        self.llm_provider = llm_provider
        self.max_searches = max_searches
        self.timeout = timeout

    async def execute(self, input_text: str) -> Result[EnrichmentResult, EnrichmentError]:
        """Execute enrichment with web search.

        Analyzes input text for terms needing clarification and enriches
        with domain knowledge from web searches.

        Args:
            input_text: Text to enrich with domain context

        Returns:
            Ok(EnrichmentResult) if successful
            Err(EnrichmentError) if enrichment fails
        """
        logger.info(f"Starting enrichment (input_text_length={len(input_text)})")
        start_time = time.time()

        try:
            # Call LLM with web search to enrich text
            enriched_text, search_count, sources_used = (
                await self.llm_provider.enrich_with_web_search(
                    text=input_text,
                    max_searches=self.max_searches,
                )
            )

            enrichment_time = time.time() - start_time

            logger.info(
                f"Enrichment succeeded: "
                f"search_count={search_count}, "
                f"sources_used={len(sources_used)}, "
                f"enriched_length={len(enriched_text)}, "
                f"time={enrichment_time:.2f}s"
            )

            return Ok(
                EnrichmentResult(
                    enriched_text=enriched_text,
                    original_text=input_text,
                    search_count=search_count,
                    sources_used=sources_used,
                    enrichment_time_seconds=enrichment_time,
                )
            )

        except Exception as e:
            enrichment_time = time.time() - start_time
            logger.error(f"Enrichment failed after {enrichment_time:.2f}s: {e}")
            return Err(
                EnrichmentError(
                    message=f"Web search enrichment failed: {str(e)}",
                    search_count=0,
                )
            )
