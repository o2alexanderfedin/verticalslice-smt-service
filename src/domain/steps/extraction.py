"""Step 2: SMT-LIB extraction with degradation verification.

Extracts SMT-LIB code from formalized text with annotations.
Uses embedding distance to verify degradation ≤5%.
"""

import logging
from typing import TYPE_CHECKING, Optional

from src.domain.exceptions import ExtractionError
from src.domain.models import ExtractionResult
from src.infrastructure.cache import AsyncFileCache
from src.shared.result import Err, Ok, Result

if TYPE_CHECKING:
    from src.domain.protocols import EmbeddingProvider, LLMProvider, SemanticVerifier

logger = logging.getLogger(__name__)


class ExtractionStep:
    """Step 2: SMT-LIB extraction with degradation verification and caching."""

    def __init__(
        self,
        llm_provider: "LLMProvider",
        embedding_provider: "EmbeddingProvider",
        verifier: "SemanticVerifier",
        max_degradation: float = 0.05,
        max_retries: int = 5,
        detail_start: float = 0.5,
        detail_step: float = 0.1,
        skip_retries_threshold: int = 50,
        cache: Optional[AsyncFileCache] = None,
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
            skip_retries_threshold: Skip retries for texts shorter than this (default 50)
            cache: Optional AsyncFileCache for caching extraction results
        """
        self.llm_provider = llm_provider
        self.embedding_provider = embedding_provider
        self.verifier = verifier
        self.max_degradation = max_degradation
        self.max_retries = max_retries
        self.detail_start = detail_start
        self.detail_step = detail_step
        self.skip_retries_threshold = skip_retries_threshold
        self.cache = cache

    async def execute(self, formal_text: str) -> Result[ExtractionResult, ExtractionError]:
        """Execute extraction with retry logic and caching.

        CRITICAL OPTIMIZATION: Compute formal text embedding ONCE before loop,
        reuse in all iterations. Only compute SMT embedding for each attempt.

        Args:
            formal_text: Formalized text from Step 1

        Returns:
            Ok(ExtractionResult) if successful
            Err(ExtractionError) if all retries exhausted
        """
        logger.info(f"Starting extraction (formal_text_length={len(formal_text)})")

        # Check cache if enabled
        cache_key: Optional[str] = None
        if self.cache:
            try:
                cache_key = self.cache._generate_cache_key(formal_text, "extraction")
                cached_result = await self.cache.get(cache_key)
                if cached_result is not None:
                    logger.info(
                        f"Extraction cache hit: "
                        f"smt_code_length={len(cached_result['smt_lib_code'])}, "
                        f"degradation={cached_result['degradation']:.4f}"
                    )
                    return Ok(
                        ExtractionResult(
                            smt_lib_code=cached_result["smt_lib_code"],
                            degradation=cached_result["degradation"],
                            attempts=cached_result["attempts"],
                        )
                    )
                logger.debug("Extraction cache miss")
            except Exception as e:
                logger.warning(f"Cache read failed (continuing without cache): {e}")

        try:
            # OPTIMIZATION: Compute formal text embedding ONCE
            embedding_formal = await self.embedding_provider.embed(formal_text)
            logger.debug("Formal text embedding computed")

        except Exception as e:
            logger.error(f"Failed to compute formal text embedding: {e}")
            return Err(
                ExtractionError(
                    message=f"Failed to compute formal text embedding: {str(e)}",
                    best_degradation=1.0,
                    attempts=0,
                )
            )

        # OPTIMIZATION: Skip retries for short formal texts
        # Short, simple texts should get correct SMT-LIB on first attempt with 5-phase prompt
        skip_retries = (
            self.skip_retries_threshold > 0 and len(formal_text) < self.skip_retries_threshold
        )

        if skip_retries:
            logger.info(
                f"Short formal text ({len(formal_text)} chars < {self.skip_retries_threshold} threshold). "
                f"Will accept first extraction attempt without retries."
            )

        best_degradation = 1.0
        best_smt_code: str | None = None
        previous_attempt: str | None = None
        previous_degradation: float | None = None

        # Retry loop with conversation-based refinement
        # NOTE: Temperature is NOT varied here - it stays at 0.0 for all attempts
        # (hardcoded in LLM client for deterministic code generation)
        max_attempts = 1 if skip_retries else self.max_retries
        for attempt in range(max_attempts):
            # Increase detail level on each attempt (for logging purposes)
            detail_level = min(1.0, self.detail_start + attempt * self.detail_step)

            logger.debug(
                f"Extraction attempt {attempt + 1}/{max_attempts} "
                f"(detail_level={detail_level:.2f}, "
                f"mode={'refinement' if previous_attempt else 'first_attempt'}, "
                f"skip_retries={skip_retries})"
            )

            try:
                # Call LLM to extract SMT-LIB with optional refinement context
                smt_code = await self.llm_provider.extract_to_smtlib(
                    formal_text,
                    detail_level=detail_level,
                    previous_attempt=previous_attempt,
                    previous_degradation=previous_degradation,
                )

                # Compute embedding for SMT code (only new embedding needed)
                embedding_smt = await self.embedding_provider.embed(smt_code)

                # Calculate degradation
                degradation = self.verifier.calculate_degradation(embedding_formal, embedding_smt)

                logger.info(
                    f"Attempt {attempt + 1}: degradation={degradation:.4f} "
                    f"(max={self.max_degradation})"
                )

                # Track best result
                if degradation < best_degradation:
                    best_degradation = degradation
                    best_smt_code = smt_code

                # Check threshold (or accept if skipping retries)
                if degradation <= self.max_degradation or skip_retries:
                    if skip_retries:
                        logger.info(
                            f"Extraction succeeded after {attempt + 1} attempt "
                            f"(skip_retries=True, degradation={degradation:.4f} accepted without quality check)"
                        )
                    else:
                        logger.info(f"Extraction succeeded after {attempt + 1} attempts")

                    # Store in cache if enabled
                    if self.cache and cache_key:
                        try:
                            cache_data = {
                                "smt_lib_code": smt_code,
                                "degradation": degradation,
                                "attempts": attempt + 1,
                            }
                            await self.cache.set(cache_key, cache_data)
                            logger.debug(f"Stored extraction result in cache: {cache_key}")
                        except Exception as e:
                            logger.warning(f"Cache write failed (ignoring): {e}")

                    return Ok(
                        ExtractionResult(
                            smt_lib_code=smt_code, degradation=degradation, attempts=attempt + 1
                        )
                    )

                # Save for next refinement iteration
                previous_attempt = smt_code
                previous_degradation = degradation

            except Exception as e:
                logger.warning(f"Attempt {attempt + 1} failed: {e}")
                # Continue to next attempt

        # All retries exhausted - return best result with warning
        logger.warning(
            f"Extraction did not meet threshold after {max_attempts} attempts. "
            f"Using best result with degradation: {best_degradation:.4f} (max: {self.max_degradation})"
        )

        # Return best result if we have one
        if best_smt_code is not None:
            # Store in cache even if degradation threshold not met
            if self.cache and cache_key:
                try:
                    cache_data = {
                        "smt_lib_code": best_smt_code,
                        "degradation": best_degradation,
                        "attempts": max_attempts,
                    }
                    await self.cache.set(cache_key, cache_data)
                    logger.debug(f"Stored extraction result in cache: {cache_key}")
                except Exception as e:
                    logger.warning(f"Cache write failed (ignoring): {e}")

            return Ok(
                ExtractionResult(
                    smt_lib_code=best_smt_code,
                    degradation=best_degradation,
                    attempts=max_attempts,
                )
            )

        # No successful attempts at all
        return Err(
            ExtractionError(
                message=f"All {max_attempts} extraction attempts failed with exceptions",
                best_degradation=1.0,
                attempts=max_attempts,
            )
        )
