"""Step 2: SMT-LIB extraction with degradation verification.

Extracts SMT-LIB code from formalized text with annotations.
Uses embedding distance to verify degradation ≤5%.
"""

import logging
from typing import TYPE_CHECKING

from src.shared.result import Result, Ok, Err
from src.domain.models import ExtractionResult
from src.domain.exceptions import ExtractionError

if TYPE_CHECKING:
    from src.domain.protocols import LLMProvider, EmbeddingProvider, SemanticVerifier

logger = logging.getLogger(__name__)


class ExtractionStep:
    """Step 2: SMT-LIB extraction with degradation verification."""

    def __init__(
        self,
        llm_provider: 'LLMProvider',
        embedding_provider: 'EmbeddingProvider',
        verifier: 'SemanticVerifier',
        max_degradation: float = 0.05,
        max_retries: int = 5,
        detail_start: float = 0.5,
        detail_step: float = 0.1
    ):
        """Initialize extraction step.

        Args:
            llm_provider: Provider for LLM calls
            embedding_provider: Provider for embeddings
            verifier: Semantic similarity verifier
            max_degradation: Maximum allowed degradation (default 0.05)
            max_retries: Maximum retry attempts (default 5)
            detail_start: Starting detail level (default 0.5)
            detail_step: Detail level increase per retry (default 0.1)
        """
        self.llm_provider = llm_provider
        self.embedding_provider = embedding_provider
        self.verifier = verifier
        self.max_degradation = max_degradation
        self.max_retries = max_retries
        self.detail_start = detail_start
        self.detail_step = detail_step

    async def execute(
        self,
        formal_text: str
    ) -> Result[ExtractionResult, ExtractionError]:
        """Execute extraction with retry logic.

        CRITICAL OPTIMIZATION: Compute formal text embedding ONCE before loop,
        reuse in all iterations. Only compute SMT embedding for each attempt.

        Args:
            formal_text: Formalized text from Step 1

        Returns:
            Ok(ExtractionResult) if successful
            Err(ExtractionError) if all retries exhausted
        """
        logger.info(f"Starting extraction (formal_text_length={len(formal_text)})")

        try:
            # OPTIMIZATION: Compute formal text embedding ONCE
            embedding_formal = await self.embedding_provider.embed(formal_text)
            logger.debug("Formal text embedding computed")

        except Exception as e:
            logger.error(f"Failed to compute formal text embedding: {e}")
            return Err(ExtractionError(
                message=f"Failed to compute formal text embedding: {str(e)}",
                best_degradation=1.0,
                attempts=0
            ))

        best_degradation = 1.0
        best_smt_code = ""
        previous_attempt: str | None = None
        previous_degradation: float | None = None

        # Retry loop with conversation-based refinement
        # NOTE: Temperature is NOT varied here - it stays at 0.0 for all attempts
        # (hardcoded in LLM client for deterministic code generation)
        for attempt in range(self.max_retries):
            # Increase detail level on each attempt (for logging purposes)
            detail_level = min(1.0, self.detail_start + attempt * self.detail_step)

            logger.debug(
                f"Extraction attempt {attempt + 1}/{self.max_retries} "
                f"(detail_level={detail_level:.2f}, "
                f"mode={'refinement' if previous_attempt else 'first_attempt'})"
            )

            try:
                # Call LLM to extract SMT-LIB with optional refinement context
                smt_code = await self.llm_provider.extract_to_smtlib(
                    formal_text,
                    detail_level=detail_level,
                    previous_attempt=previous_attempt,
                    previous_degradation=previous_degradation
                )

                # Compute embedding for SMT code (only new embedding needed)
                embedding_smt = await self.embedding_provider.embed(smt_code)

                # Calculate degradation
                degradation = self.verifier.calculate_degradation(
                    embedding_formal,
                    embedding_smt
                )

                logger.info(
                    f"Attempt {attempt + 1}: degradation={degradation:.4f} "
                    f"(max={self.max_degradation})"
                )

                # Track best result
                if degradation < best_degradation:
                    best_degradation = degradation
                    best_smt_code = smt_code

                # Check threshold
                if degradation <= self.max_degradation:
                    logger.info(f"Extraction succeeded after {attempt + 1} attempts")
                    return Ok(ExtractionResult(
                        smt_lib_code=smt_code,
                        degradation=degradation,
                        attempts=attempt + 1
                    ))

                # Save for next refinement iteration
                previous_attempt = smt_code
                previous_degradation = degradation

            except Exception as e:
                logger.warning(f"Attempt {attempt + 1} failed: {e}")
                # Continue to next attempt

        # All retries exhausted
        logger.warning(
            f"Extraction failed after {self.max_retries} attempts. "
            f"Best degradation: {best_degradation:.4f} (max: {self.max_degradation})"
        )
        return Err(ExtractionError(
            message=(
                f"Failed to meet degradation threshold after {self.max_retries} attempts. "
                f"Best degradation: {best_degradation:.4f}, Max allowed: {self.max_degradation}"
            ),
            best_degradation=best_degradation,
            attempts=self.max_retries
        ))
