"""Integration tests for domain steps with real infrastructure dependencies.

These tests verify that domain steps correctly interact with their
infrastructure dependencies (LLM providers, embedding providers, SMT solvers).
Uses real API calls with minimal input to reduce cost.
"""

import os

import pytest

from src.domain.steps.extraction import ExtractionStep
from src.domain.steps.formalization import FormalizationStep
from src.domain.steps.validation import ValidationStep
from src.domain.verification.embedding_verifier import EmbeddingDistanceVerifier
from src.infrastructure.embeddings.sentence_transformer import SentenceTransformerProvider
from src.infrastructure.llm.client import AnthropicClient
from src.infrastructure.smt.z3_executor import Z3Executor


@pytest.fixture
def llm_provider() -> AnthropicClient:
    """Create LLM provider."""
    return AnthropicClient()


@pytest.fixture
def embedding_provider() -> SentenceTransformerProvider:
    """Create embedding provider."""
    return SentenceTransformerProvider()


@pytest.fixture
def verifier() -> EmbeddingDistanceVerifier:
    """Create semantic verifier."""
    return EmbeddingDistanceVerifier()


@pytest.fixture
def smt_solver() -> Z3Executor:
    """Create SMT solver."""
    return Z3Executor()


@pytest.mark.skipif(
    not os.environ.get("ANTHROPIC_API_KEY") and not os.environ.get("CLAUDE_CODE_OAUTH_TOKEN"),
    reason="ANTHROPIC_API_KEY or CLAUDE_CODE_OAUTH_TOKEN not set"
)
class TestFormalizationStepIntegration:
    """Integration tests for FormalizationStep → LLMProvider, EmbeddingProvider."""

    @pytest.mark.asyncio
    async def test_formalize_simple_text(
        self,
        llm_provider: AnthropicClient,
        embedding_provider: SentenceTransformerProvider,
        verifier: EmbeddingDistanceVerifier,
    ) -> None:
        """Test formalization of simple text with real providers."""
        step = FormalizationStep(
            llm_provider=llm_provider,
            embedding_provider=embedding_provider,
            verifier=verifier,
            threshold=0.80,  # Lower threshold for testing
            max_retries=2,
            skip_threshold=0,  # Don't skip for test
        )

        result = await step.execute("x > 5")
        await llm_provider.close()

        assert result.is_ok()
        formal_result = result.value
        assert formal_result.formal_text
        assert formal_result.similarity_score > 0
        assert formal_result.attempts >= 1

    @pytest.mark.asyncio
    async def test_formalize_skips_short_text(
        self,
        llm_provider: AnthropicClient,
        embedding_provider: SentenceTransformerProvider,
        verifier: EmbeddingDistanceVerifier,
    ) -> None:
        """Test formalization skips short text below threshold."""
        step = FormalizationStep(
            llm_provider=llm_provider,
            embedding_provider=embedding_provider,
            verifier=verifier,
            skip_threshold=100,  # Skip texts under 100 chars
        )

        result = await step.execute("x > 5")
        await llm_provider.close()

        assert result.is_ok()
        formal_result = result.value
        # Should skip and return original text
        assert formal_result.formal_text == "x > 5"
        assert formal_result.similarity_score == 1.0
        assert formal_result.attempts == 0


@pytest.mark.skipif(
    not os.environ.get("ANTHROPIC_API_KEY") and not os.environ.get("CLAUDE_CODE_OAUTH_TOKEN"),
    reason="ANTHROPIC_API_KEY or CLAUDE_CODE_OAUTH_TOKEN not set"
)
class TestExtractionStepIntegration:
    """Integration tests for ExtractionStep → LLMProvider, EmbeddingProvider."""

    @pytest.mark.asyncio
    async def test_extract_simple_constraint(
        self,
        llm_provider: AnthropicClient,
        embedding_provider: SentenceTransformerProvider,
        verifier: EmbeddingDistanceVerifier,
    ) -> None:
        """Test extraction of simple constraint with real providers."""
        step = ExtractionStep(
            llm_provider=llm_provider,
            embedding_provider=embedding_provider,
            verifier=verifier,
            max_degradation=0.50,  # Higher threshold for testing
            max_retries=2,
            skip_retries_threshold=0,  # Don't skip for test
        )

        result = await step.execute("The variable x must be greater than 5.")
        await llm_provider.close()

        assert result.is_ok()
        extraction_result = result.value
        assert extraction_result.smt_lib_code
        assert extraction_result.degradation >= 0
        assert extraction_result.attempts >= 1
        # Should contain SMT-LIB code
        code_lower = extraction_result.smt_lib_code.lower()
        assert any(keyword in code_lower for keyword in ["declare", "assert", "check-sat"])

    @pytest.mark.asyncio
    async def test_extract_skips_short_text(
        self,
        llm_provider: AnthropicClient,
        embedding_provider: SentenceTransformerProvider,
        verifier: EmbeddingDistanceVerifier,
    ) -> None:
        """Test extraction accepts first attempt for short text."""
        step = ExtractionStep(
            llm_provider=llm_provider,
            embedding_provider=embedding_provider,
            verifier=verifier,
            skip_retries_threshold=100,  # Skip retries for texts under 100 chars
        )

        result = await step.execute("x > 5")
        await llm_provider.close()

        assert result.is_ok()
        extraction_result = result.value
        # Should only make 1 attempt due to skip
        assert extraction_result.attempts == 1


class TestValidationStepIntegration:
    """Integration tests for ValidationStep → LLMProvider, SMTSolver."""

    @pytest.mark.asyncio
    async def test_validate_correct_smt_code(
        self,
        llm_provider: AnthropicClient,
        smt_solver: Z3Executor,
    ) -> None:
        """Test validation of correct SMT-LIB code."""
        step = ValidationStep(
            llm_provider=llm_provider,
            smt_solver=smt_solver,
            max_retries=2,
        )

        smt_code = """
(declare-const x Int)
(assert (> x 5))
(check-sat)
(get-model)
"""

        result = await step.execute(smt_code)
        await llm_provider.close()

        assert result.is_ok()
        solver_result = result.value
        assert solver_result.success
        assert solver_result.check_sat_result == "sat"
        assert solver_result.attempts == 1

    @pytest.mark.asyncio
    async def test_validate_unsat_code(
        self,
        llm_provider: AnthropicClient,
        smt_solver: Z3Executor,
    ) -> None:
        """Test validation of unsatisfiable SMT-LIB code."""
        step = ValidationStep(
            llm_provider=llm_provider,
            smt_solver=smt_solver,
        )

        smt_code = """
(declare-const x Int)
(assert (> x 5))
(assert (< x 3))
(check-sat)
"""

        result = await step.execute(smt_code)
        await llm_provider.close()

        assert result.is_ok()
        solver_result = result.value
        assert solver_result.success
        assert solver_result.check_sat_result == "unsat"

    @pytest.mark.asyncio
    async def test_validate_strips_markdown_fences(
        self,
        llm_provider: AnthropicClient,
        smt_solver: Z3Executor,
    ) -> None:
        """Test validation strips markdown code fences."""
        step = ValidationStep(
            llm_provider=llm_provider,
            smt_solver=smt_solver,
        )

        smt_code = """```smt-lib
(declare-const x Int)
(assert (> x 5))
(check-sat)
```"""

        result = await step.execute(smt_code)
        await llm_provider.close()

        assert result.is_ok()
        solver_result = result.value
        assert solver_result.success

    @pytest.mark.asyncio
    async def test_validate_fixes_syntax_error(
        self,
        llm_provider: AnthropicClient,
        smt_solver: Z3Executor,
    ) -> None:
        """Test validation uses LLM to fix syntax errors."""
        step = ValidationStep(
            llm_provider=llm_provider,
            smt_solver=smt_solver,
            max_retries=3,
        )

        # Missing closing paren on first line
        broken_code = """
(declare-const x Int
(assert (> x 5))
(check-sat)
"""

        result = await step.execute(broken_code)
        await llm_provider.close()

        # May or may not succeed depending on LLM fix quality
        # But should not raise exception
        if result.is_ok():
            assert result.value.success
        else:
            # If it fails, should have made all retry attempts
            assert result.error.attempts == 3


@pytest.mark.skipif(
    not os.environ.get("ANTHROPIC_API_KEY") and not os.environ.get("CLAUDE_CODE_OAUTH_TOKEN"),
    reason="ANTHROPIC_API_KEY or CLAUDE_CODE_OAUTH_TOKEN not set"
)
class TestEndToEndIntegration:
    """End-to-end integration test through all steps."""

    @pytest.mark.asyncio
    async def test_full_pipeline_simple_constraint(
        self,
        llm_provider: AnthropicClient,
        embedding_provider: SentenceTransformerProvider,
        verifier: EmbeddingDistanceVerifier,
        smt_solver: Z3Executor,
    ) -> None:
        """Test full pipeline from informal text to SMT validation."""
        # Step 1: Formalization
        formalization_step = FormalizationStep(
            llm_provider=llm_provider,
            embedding_provider=embedding_provider,
            verifier=verifier,
            threshold=0.70,  # Lower for testing
            max_retries=2,
        )

        formal_result = await formalization_step.execute("x must be greater than 5")

        assert formal_result.is_ok()
        formal_text = formal_result.value.formal_text

        # Step 2: Extraction
        extraction_step = ExtractionStep(
            llm_provider=llm_provider,
            embedding_provider=embedding_provider,
            verifier=verifier,
            max_degradation=0.50,  # Higher for testing
            max_retries=2,
        )

        extraction_result = await extraction_step.execute(formal_text)

        assert extraction_result.is_ok()
        smt_code = extraction_result.value.smt_lib_code

        # Step 3: Validation
        validation_step = ValidationStep(
            llm_provider=llm_provider,
            smt_solver=smt_solver,
            max_retries=3,
        )

        validation_result = await validation_step.execute(smt_code)
        await llm_provider.close()

        # The full pipeline should succeed
        assert validation_result.is_ok()
        assert validation_result.value.success
        assert validation_result.value.check_sat_result == "sat"
