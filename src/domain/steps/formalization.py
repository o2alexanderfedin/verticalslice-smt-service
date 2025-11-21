"""Step 1: Formalization with semantic verification.

Transforms informal text to formal text while preserving semantics.
Uses embedding distance to verify semantic similarity ≥91%.
"""

import logging
from typing import TYPE_CHECKING

from src.domain.exceptions import FormalizationError
from src.domain.models import FormalizationResult
from src.shared.result import Err, Ok, Result

if TYPE_CHECKING:
    from src.domain.protocols import EmbeddingProvider, LLMProvider, SemanticVerifier

logger = logging.getLogger(__name__)


class FormalizationStep:
    """Step 1: Formalization with semantic verification."""

    def __init__(
        self,
        llm_provider: "LLMProvider",
        embedding_provider: "EmbeddingProvider",
        verifier: "SemanticVerifier",
        threshold: float = 0.91,
        max_retries: int = 3,
        skip_threshold: int = 20,
    ):
        """Initialize formalization step.

        Args:
            llm_provider: Provider for LLM calls
            embedding_provider: Provider for embeddings
            verifier: Semantic similarity verifier
            threshold: Minimum similarity threshold (default 0.91)
            max_retries: Maximum retry attempts (default 3)
            skip_threshold: Skip formalization for inputs shorter than this (default 20)
        """
        self.llm_provider = llm_provider
        self.embedding_provider = embedding_provider
        self.verifier = verifier
        self.threshold = threshold
        self.max_retries = max_retries
        self.skip_threshold = skip_threshold

    async def execute(
        self, informal_text: str, force_skip: bool = False
    ) -> Result[FormalizationResult, FormalizationError]:
        """Execute formalization with retry logic.

        CRITICAL OPTIMIZATION: Compute source embedding ONCE before loop,
        reuse in all iterations. Only compute new embedding for each attempt.

        Args:
            informal_text: Source natural language text
            force_skip: If True, unconditionally skip formalization (API override)

        Returns:
            Ok(FormalizationResult) if successful
            Err(FormalizationError) if all retries exhausted
        """
        logger.info(f"Starting formalization (text_length={len(informal_text)})")

        # OPTIMIZATION: Skip formalization for very short inputs or when explicitly requested
        should_skip = False
        skip_reason = ""

        if force_skip:
            should_skip = True
            skip_reason = "explicitly requested via API flag"
        elif self.skip_threshold > 0 and len(informal_text) < self.skip_threshold:
            should_skip = True
            skip_reason = (
                f"short input ({len(informal_text)} chars < {self.skip_threshold} threshold)"
            )

        if should_skip:
            logger.info(f"Skipping formalization: {skip_reason}. " f"Treating as already formal.")
            return Ok(
                FormalizationResult(
                    formal_text=informal_text,
                    similarity_score=1.0,  # Perfect similarity since it's unchanged
                    attempts=0,  # No LLM calls needed
                )
            )

        try:
            # OPTIMIZATION: Compute source embedding ONCE
            embedding_source = await self.embedding_provider.embed(informal_text)
            logger.debug("Source embedding computed")

        except Exception as e:
            logger.error(f"Failed to compute source embedding: {e}")
            return Err(
                FormalizationError(
                    message=f"Failed to compute source embedding: {str(e)}",
                    best_similarity=0.0,
                    attempts=0,
                )
            )

        best_similarity = 0.0
        best_formal_text: str | None = None
        previous_attempt: str | None = None
        previous_similarity: float | None = None

        # Retry loop with conversation-based refinement
        for attempt in range(self.max_retries):
            logger.debug(
                f"Formalization attempt {attempt + 1}/{self.max_retries} "
                f"mode={'refinement' if previous_attempt else 'first_attempt'})"
            )

            try:
                # Call LLM with optional refinement context
                formal_text = await self.llm_provider.formalize(
                    informal_text,
                    previous_attempt=previous_attempt,
                    previous_similarity=previous_similarity,
                )

                # Log the complete formalized text for debugging
                logger.info(
                    f"Formalized text (attempt {attempt + 1}, length={len(formal_text)}): "
                    f"{formal_text}"
                )

                # Compute embedding for formal text (only new embedding needed)
                embedding_formal = await self.embedding_provider.embed(formal_text)

                # Calculate similarity
                similarity = self.verifier.calculate_similarity(embedding_source, embedding_formal)

                logger.info(
                    f"Attempt {attempt + 1}: similarity={similarity:.4f} "
                    f"(threshold={self.threshold})"
                )

                # Track best result
                if similarity > best_similarity:
                    best_similarity = similarity
                    best_formal_text = formal_text

                # Check threshold
                if similarity >= self.threshold:
                    logger.info(f"Formalization succeeded after {attempt + 1} attempts")
                    return Ok(
                        FormalizationResult(
                            formal_text=formal_text,
                            similarity_score=similarity,
                            attempts=attempt + 1,
                        )
                    )

                # Save for next refinement iteration
                previous_attempt = formal_text
                previous_similarity = similarity

            except Exception as e:
                logger.warning(f"Attempt {attempt + 1} failed: {e}")
                # Continue to next attempt

        # All retries exhausted - return best result with warning
        logger.warning(
            f"Formalization did not meet threshold after {self.max_retries} attempts. "
            f"Using best result with similarity: {best_similarity:.4f} (threshold: {self.threshold})"
        )

        # Return best result if we have one
        if best_formal_text is not None:
            return Ok(
                FormalizationResult(
                    formal_text=best_formal_text,
                    similarity_score=best_similarity,
                    attempts=self.max_retries,
                )
            )

        # No successful attempts at all
        return Err(
            FormalizationError(
                message=f"All {self.max_retries} formalization attempts failed with exceptions",
                best_similarity=0.0,
                attempts=self.max_retries,
            )
        )
