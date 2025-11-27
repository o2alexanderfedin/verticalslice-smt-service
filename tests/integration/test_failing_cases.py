"""Integration tests for known failing cases with diagnostic tracing.

These tests verify and debug specific input cases that have failed in production.
Each test captures comprehensive diagnostic information including:
- All pipeline step inputs and outputs
- LLM prompts and responses
- SMT solver errors and fixes attempted
- Full attempt history for retry loops

Run with: pytest tests/integration/test_failing_cases.py -v -s --log-cli-level=DEBUG
"""

import logging
import os
from typing import Any

import pytest

from src.application.pipeline_service import PipelineService
from src.domain.exceptions import ValidationError
from src.domain.steps.extraction import ExtractionStep
from src.domain.steps.formalization import FormalizationStep
from src.domain.steps.validation import ValidationStep
from src.domain.verification.embedding_verifier import EmbeddingDistanceVerifier
from src.infrastructure.embeddings.sentence_transformer import SentenceTransformerProvider
from src.infrastructure.llm.client import AnthropicClient
from src.infrastructure.smt.cvc5_executor import Cvc5Executor
from src.shared.logging_config import configure_logging

# Configure debug logging for comprehensive tracing
configure_logging("DEBUG")

logger = logging.getLogger(__name__)


# ============================================================================
# Fixtures
# ============================================================================


@pytest.fixture
def llm_provider() -> AnthropicClient:
    """Create LLM provider for integration tests."""
    return AnthropicClient()


@pytest.fixture
def embedding_provider() -> SentenceTransformerProvider:
    """Create embedding provider for integration tests."""
    return SentenceTransformerProvider()


@pytest.fixture
def verifier() -> EmbeddingDistanceVerifier:
    """Create semantic verifier for integration tests."""
    return EmbeddingDistanceVerifier()


@pytest.fixture
def smt_solver() -> Cvc5Executor:
    """Create SMT solver for integration tests."""
    return Cvc5Executor()


@pytest.fixture
def pipeline_service(
    llm_provider: AnthropicClient,
    embedding_provider: SentenceTransformerProvider,
    verifier: EmbeddingDistanceVerifier,
    smt_solver: Cvc5Executor,
) -> PipelineService:
    """Create complete pipeline service for integration tests."""
    return PipelineService(
        llm_provider=llm_provider,
        embedding_provider=embedding_provider,
        verifier=verifier,
        smt_solver=smt_solver,
    )


# ============================================================================
# Diagnostic Helpers
# ============================================================================


def log_step_result(step_name: str, result: Any) -> None:
    """Log detailed information about a pipeline step result.

    Args:
        step_name: Name of the pipeline step
        result: Result object from the step
    """
    logger.info("=" * 80)
    logger.info(f"STEP: {step_name}")
    logger.info("=" * 80)

    if hasattr(result, "is_ok") and result.is_ok():
        value = result.value
        logger.info("Status: SUCCESS")

        # Log step-specific fields
        if hasattr(value, "formal_text"):
            logger.info(f"Formal Text: {value.formal_text}")
        if hasattr(value, "similarity_score"):
            logger.info(f"Similarity Score: {value.similarity_score:.4f}")
        if hasattr(value, "smt_lib_code"):
            logger.info(f"SMT-LIB Code:\n{value.smt_lib_code}")
        if hasattr(value, "degradation"):
            logger.info(f"Degradation: {value.degradation:.4f}")
        if hasattr(value, "check_sat_result"):
            logger.info(f"SAT Result: {value.check_sat_result}")
        if hasattr(value, "model"):
            logger.info(f"Model: {value.model}")
        if hasattr(value, "attempts"):
            logger.info(f"Attempts: {value.attempts}")
    else:
        error = result.error if hasattr(result, "error") else result
        logger.error("Status: FAILED")
        logger.error(f"Error: {error}")

        # Log ValidationError diagnostics if available
        if isinstance(error, ValidationError):
            logger.error(f"Last Error: {error.last_error}")
            logger.error(f"Attempts Made: {error.attempts}")
            if error.smt_code:
                logger.error(f"Failed SMT Code:\n{error.smt_code}")
            if error.informal_text:
                logger.error(f"Informal Text: {error.informal_text}")
            if error.formal_text:
                logger.error(f"Formal Text: {error.formal_text}")
            if error.attempt_history:
                logger.error(f"Attempt History ({len(error.attempt_history)} attempts):")
                for i, attempt in enumerate(error.attempt_history, 1):
                    logger.error(f"  Attempt {i}:")
                    logger.error(f"    Error: {attempt.get('solver_error', 'N/A')}")
                    logger.error(f"    Fix Attempted:\n{attempt.get('fix_attempted', 'N/A')}")

    logger.info("=" * 80)


# ============================================================================
# Test Cases
# ============================================================================


@pytest.mark.skipif(
    not os.environ.get("ANTHROPIC_API_KEY") and not os.environ.get("CLAUDE_CODE_OAUTH_TOKEN"),
    reason="ANTHROPIC_API_KEY or CLAUDE_CODE_OAUTH_TOKEN not set",
)
class TestStainlessSteelThermalExpansion:
    """Tests for stainless steel thermal expansion constraint.

    This constraint has been failing validation with parse error:
    "Expected a RPAREN_TOK, got `at` (SYMBOL)"

    Input: "Stainless steel rod with the length of 100' expands less than
            by 15\" at the temperature 500 Celcius"

    Goal: Capture full diagnostic trace to understand:
    1. What formal text is generated
    2. What SMT code is initially extracted
    3. What solver errors occur
    4. What fixes the LLM attempts
    5. Why fixes fail to resolve the parse error
    """

    @pytest.mark.asyncio
    async def test_full_pipeline_with_diagnostics(
        self,
        llm_provider: AnthropicClient,
        embedding_provider: SentenceTransformerProvider,
        verifier: EmbeddingDistanceVerifier,
        smt_solver: Cvc5Executor,
    ) -> None:
        """Test full pipeline for stainless steel thermal expansion with debug tracing."""
        informal_text = (
            "Stainless steel rod with the length of 100' expands less than "
            'by 15" at the temperature 500 Celcius'
        )

        logger.info("=" * 80)
        logger.info("TESTING: Stainless Steel Thermal Expansion Constraint")
        logger.info("=" * 80)
        logger.info(f"Input: {informal_text}")
        logger.info("=" * 80)

        # Step 1: Formalization
        logger.info("Starting Formalization Step...")
        formalization_step = FormalizationStep(
            llm_provider=llm_provider,
            embedding_provider=embedding_provider,
            verifier=verifier,
            threshold=0.70,
            max_retries=3,
        )

        formal_result = await formalization_step.execute(informal_text)
        log_step_result("FORMALIZATION", formal_result)

        assert formal_result.is_ok(), f"Formalization failed: {formal_result.error}"
        formal_text = formal_result.value.formal_text

        # Step 2: Extraction
        logger.info("Starting Extraction Step...")
        extraction_step = ExtractionStep(
            llm_provider=llm_provider,
            embedding_provider=embedding_provider,
            verifier=verifier,
            max_degradation=0.50,
            max_retries=3,
        )

        extraction_result = await extraction_step.execute(formal_text)
        log_step_result("EXTRACTION", extraction_result)

        assert extraction_result.is_ok(), f"Extraction failed: {extraction_result.error}"
        smt_code = extraction_result.value.smt_lib_code

        # Step 3: Validation (EXPECTED TO FAIL - capturing diagnostics)
        logger.info("Starting Validation Step...")
        validation_step = ValidationStep(
            llm_provider=llm_provider,
            smt_solver=smt_solver,
            max_retries=5,
        )

        # Pass informal and formal text for context-rich error fixing
        validation_result = await validation_step.execute(
            smt_code, informal_text=informal_text, formal_text=formal_text
        )
        log_step_result("VALIDATION", validation_result)

        # Close LLM connection
        await llm_provider.close()

        # Analyze the result
        if validation_result.is_ok():
            logger.info("✅ VALIDATION SUCCEEDED - Problem appears to be fixed!")
            logger.info(f"SAT Result: {validation_result.value.check_sat_result}")
            logger.info(f"Total Attempts: {validation_result.value.attempts}")
        else:
            logger.error("❌ VALIDATION FAILED - Analyzing diagnostics...")
            error = validation_result.error
            assert isinstance(error, ValidationError), "Expected ValidationError"

            # Detailed root cause analysis
            logger.error("\n" + "=" * 80)
            logger.error("ROOT CAUSE ANALYSIS")
            logger.error("=" * 80)

            # Check if error is in initial extraction or in fixes
            if error.attempts == 1:
                logger.error(
                    "❌ Initial SMT code failed validation on first attempt - "
                    "problem is in EXTRACTION step"
                )
            else:
                logger.error(
                    f"❌ All {error.attempts} fix attempts failed - "
                    "problem is in VALIDATION retry logic"
                )

            # Analyze error pattern
            if "at" in error.last_error and "SYMBOL" in error.last_error:
                logger.error("❌ Parse error involves the word 'at' being treated as a symbol")
                logger.error(
                    "   This suggests measurement/unit handling issue "
                    "(e.g., '15\" at temperature')"
                )

            # Check if context-rich fixes were used
            if error.attempt_history:
                logger.error(
                    f"✅ Context-rich fixes WERE used ({len(error.attempt_history)} attempts logged)"
                )

                # Analyze fix patterns
                for i, attempt in enumerate(error.attempt_history, 1):
                    logger.error(f"\n--- Attempt {i} Analysis ---")
                    solver_error = attempt.get("solver_error", "")
                    if "line" in solver_error.lower():
                        logger.error(f"✅ Error location was parsed: {solver_error}")
                    else:
                        logger.error(f"❌ No error location found: {solver_error}")
            else:
                logger.error("❌ NO attempt history - context-rich fixes may not have been used")

            logger.error("=" * 80)

            # Make test fail to capture attention
            pytest.fail(
                f"Validation failed after {error.attempts} attempts. "
                f"Last error: {error.last_error}. "
                "Check logs above for detailed diagnostics."
            )

    @pytest.mark.asyncio
    async def test_validation_only_with_manual_smt(
        self,
        llm_provider: AnthropicClient,
        smt_solver: Cvc5Executor,
    ) -> None:
        """Test validation with manually crafted SMT code for thermal expansion.

        This test bypasses formalization/extraction to verify if a correctly
        written SMT-LIB representation of the constraint can validate successfully.
        """
        informal_text = (
            "Stainless steel rod with the length of 100' expands less than "
            'by 15" at the temperature 500 Celcius'
        )

        # Manually craft SMT code for thermal expansion
        # Using linear thermal expansion formula: ΔL = α * L₀ * ΔT
        # where α ≈ 17.3 × 10⁻⁶ /°C for stainless steel
        manual_smt_code = """(set-logic QF_NRA)

; Constants for thermal expansion
(declare-const initial_length Real)  ; feet
(declare-const expansion_coefficient Real)  ; per degree Celsius
(declare-const temperature Real)  ; degrees Celsius
(declare-const expansion Real)  ; inches

; Known values
(assert (= initial_length 100.0))  ; 100 feet
(assert (= expansion_coefficient 0.0000173))  ; stainless steel coefficient
(assert (= temperature 500.0))  ; 500 Celsius

; Calculate expansion in inches
; ΔL = α * L₀ * ΔT
; Convert feet to inches (12 inches per foot)
(assert (= expansion (* expansion_coefficient (* initial_length 12.0) temperature)))

; Constraint: expansion must be less than 15 inches
(assert (< expansion 15.0))

(check-sat)
(get-model)
"""

        logger.info("=" * 80)
        logger.info("TESTING: Manual SMT Code for Thermal Expansion")
        logger.info("=" * 80)
        logger.info(f"Input: {informal_text}")
        logger.info(f"Manual SMT Code:\n{manual_smt_code}")
        logger.info("=" * 80)

        # Test validation
        validation_step = ValidationStep(
            llm_provider=llm_provider,
            smt_solver=smt_solver,
            max_retries=3,
        )

        validation_result = await validation_step.execute(manual_smt_code)
        log_step_result("VALIDATION (Manual SMT)", validation_result)

        await llm_provider.close()

        # This should succeed if SMT code is correct
        if validation_result.is_ok():
            logger.info("✅ Manual SMT code validates successfully!")
            logger.info(
                "   This confirms the constraint CAN be represented in SMT-LIB - "
                "problem is in LLM extraction"
            )
        else:
            logger.error("❌ Even manual SMT code failed - may need different logic")
            pytest.fail(f"Manual SMT validation failed: {validation_result.error}")
