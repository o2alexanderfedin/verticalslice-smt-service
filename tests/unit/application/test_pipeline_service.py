"""Unit tests for PipelineService.

Tests cover:
- Complete successful pipeline flow
- Skip formalization flag behavior
- Error propagation from each step
- Metrics collection
- Result building
"""

from unittest.mock import AsyncMock, Mock

import pytest

from src.application.pipeline_service import PipelineService
from src.domain.exceptions import ExtractionError, FormalizationError, ValidationError
from src.domain.models import (
    VerifiedOutput,
)
from src.shared.result import Err, Ok


class TestPipelineService:
    """Tests for PipelineService."""

    @pytest.fixture
    def settings(self) -> Mock:
        """Create mock settings."""
        settings = Mock()
        settings.formalization_similarity_threshold = 0.91
        settings.formalization_max_retries = 3
        settings.formalization_skip_threshold = 200
        settings.extraction_max_degradation = 0.05
        settings.extraction_max_retries = 5
        settings.extraction_detail_start = 0.5
        settings.extraction_detail_step = 0.1
        settings.extraction_skip_retries_threshold = 50
        settings.validation_max_retries = 3
        settings.enrichment_max_searches = 5
        settings.enrichment_timeout = 60.0
        return settings

    @pytest.fixture
    def service(
        self,
        mock_embedding_provider,
        mock_llm_provider,
        mock_smt_solver,
        settings,
    ) -> PipelineService:
        """Create pipeline service with mocked dependencies."""
        return PipelineService(
            embedding_provider=mock_embedding_provider,
            llm_provider=mock_llm_provider,
            smt_solver=mock_smt_solver,
            settings=settings,
        )

    @pytest.mark.asyncio
    async def test_complete_successful_pipeline(
        self,
        service: PipelineService,
        mock_llm_provider,
        mock_embedding_provider,
        mock_smt_solver,
    ) -> None:
        """Test complete successful pipeline execution."""
        import numpy as np

        # Use long text to avoid auto-skip
        informal_text = "x" * 300  # Long enough to trigger formalization
        formal_text = "The variable x must be greater than 5"
        smt_code = "(declare-const x Int)\n(assert (> x 5))\n(check-sat)"

        # Mock formalization
        mock_llm_provider.formalize = AsyncMock(return_value=formal_text)
        embeddings = [np.random.rand(384).astype(np.float32) for _ in range(4)]
        mock_embedding_provider.embed = AsyncMock(side_effect=embeddings)

        # Mock extraction
        mock_llm_provider.extract_to_smtlib = AsyncMock(return_value=smt_code)

        # Mock validation
        mock_smt_solver.execute = AsyncMock(
            return_value={
                "success": True,
                "check_sat_result": "sat",
                "model": "(define-fun x () Int 10)",
                "unsat_core": None,
                "raw_output": "sat\n(define-fun x () Int 10)",
            }
        )

        # Mock semantic verifier (service creates it internally)
        service.semantic_verifier.calculate_similarity = lambda src, fmt: 0.95
        service.semantic_verifier.calculate_degradation = lambda src, fmt: 0.02

        result = await service.process(informal_text)

        assert isinstance(result, Ok)
        output = result.value
        assert isinstance(output, VerifiedOutput)
        assert output.informal_text == informal_text
        assert output.formal_text == formal_text
        assert output.smt_lib_code == smt_code
        assert output.check_sat_result == "sat"
        assert output.model == "(define-fun x () Int 10)"
        assert output.solver_success is True
        assert output.passed_all_checks is True

        # Verify metrics
        assert output.metrics.formalization_attempts == 1
        assert output.metrics.extraction_attempts == 1
        assert output.metrics.validation_attempts == 1
        assert output.metrics.success is True
        assert output.metrics.total_time_seconds > 0

    @pytest.mark.asyncio
    async def test_skip_formalization_flag(
        self,
        service: PipelineService,
        mock_llm_provider,
        mock_embedding_provider,
        mock_smt_solver,
    ) -> None:
        """Test that skip_formalization flag works."""
        import numpy as np

        informal_text = "x > 5"

        # Skip formalization - input is treated as already formal
        mock_embedding_provider.embed = AsyncMock(
            side_effect=[
                np.random.rand(384).astype(np.float32),
                np.random.rand(384).astype(np.float32),
            ]
        )

        mock_llm_provider.extract_to_smtlib = AsyncMock(return_value="(check-sat)")

        mock_smt_solver.execute = AsyncMock(
            return_value={
                "success": True,
                "check_sat_result": "sat",
                "model": None,
                "unsat_core": None,
                "raw_output": "sat",
            }
        )

        service.semantic_verifier.calculate_degradation = lambda src, fmt: 0.02

        result = await service.process(informal_text, skip_formalization=True)

        assert isinstance(result, Ok)
        output = result.value

        # Formalization was skipped
        assert output.formal_text == informal_text
        assert output.formalization_similarity == 1.0
        assert output.metrics.formalization_attempts == 0

        # Extraction and validation still ran
        assert output.metrics.extraction_attempts == 1
        assert output.metrics.validation_attempts == 1

    @pytest.mark.asyncio
    async def test_formalization_error_propagates(
        self,
        service: PipelineService,
        mock_llm_provider,
        mock_embedding_provider,
    ) -> None:
        """Test that formalization errors propagate to caller."""
        import numpy as np

        informal_text = "x" * 300

        # Formalization fails
        mock_embedding_provider.embed = AsyncMock(
            return_value=np.random.rand(384).astype(np.float32)
        )
        mock_llm_provider.formalize = AsyncMock(side_effect=RuntimeError("LLM down"))

        result = await service.process(informal_text)

        assert isinstance(result, Err)
        assert isinstance(result.error, FormalizationError)

    @pytest.mark.asyncio
    async def test_extraction_error_propagates(
        self,
        service: PipelineService,
        mock_llm_provider,
        mock_embedding_provider,
    ) -> None:
        """Test that extraction errors propagate to caller."""
        import numpy as np

        informal_text = "x" * 300
        formal_text = "formal text"

        # Formalization succeeds
        mock_llm_provider.formalize = AsyncMock(return_value=formal_text)
        embeddings = [np.random.rand(384).astype(np.float32) for _ in range(3)]
        mock_embedding_provider.embed = AsyncMock(side_effect=embeddings)
        service.semantic_verifier.calculate_similarity = lambda src, fmt: 0.95

        # Extraction fails
        mock_llm_provider.extract_to_smtlib = AsyncMock(side_effect=RuntimeError("LLM down"))

        result = await service.process(informal_text)

        assert isinstance(result, Err)
        assert isinstance(result.error, ExtractionError)

    @pytest.mark.asyncio
    async def test_validation_error_propagates(
        self,
        service: PipelineService,
        mock_llm_provider,
        mock_embedding_provider,
        mock_smt_solver,
    ) -> None:
        """Test that validation errors propagate to caller."""
        import numpy as np

        informal_text = "x" * 300
        formal_text = "formal text"
        smt_code = "(broken)"

        # Formalization and extraction succeed
        mock_llm_provider.formalize = AsyncMock(return_value=formal_text)
        mock_llm_provider.extract_to_smtlib = AsyncMock(return_value=smt_code)
        embeddings = [np.random.rand(384).astype(np.float32) for _ in range(4)]
        mock_embedding_provider.embed = AsyncMock(side_effect=embeddings)
        service.semantic_verifier.calculate_similarity = lambda src, fmt: 0.95
        service.semantic_verifier.calculate_degradation = lambda src, fmt: 0.02

        # Validation fails
        mock_smt_solver.execute = AsyncMock(
            return_value={
                "success": False,
                "check_sat_result": "error",
                "model": None,
                "unsat_core": None,
                "raw_output": "Syntax error",
            }
        )
        mock_llm_provider.fix_smt_errors = AsyncMock(return_value="(still broken)")

        result = await service.process(informal_text)

        assert isinstance(result, Err)
        assert isinstance(result.error, ValidationError)

    @pytest.mark.asyncio
    async def test_metrics_collection(
        self,
        service: PipelineService,
        mock_llm_provider,
        mock_embedding_provider,
        mock_smt_solver,
    ) -> None:
        """Test that metrics are collected correctly."""
        import numpy as np

        # Use long text to trigger formalization
        informal_text = "x" * 300

        mock_llm_provider.formalize = AsyncMock(side_effect=["Attempt 1", "Attempt 2"])
        embeddings = [np.random.rand(384).astype(np.float32) for _ in range(6)]
        mock_embedding_provider.embed = AsyncMock(side_effect=embeddings)

        similarity_count = 0

        def get_similarity(src, fmt):
            nonlocal similarity_count
            similarity_count += 1
            return 0.85 if similarity_count == 1 else 0.95

        service.semantic_verifier.calculate_similarity = get_similarity

        mock_llm_provider.extract_to_smtlib = AsyncMock(side_effect=["SMT 1", "SMT 2", "SMT 3"])
        service.semantic_verifier.calculate_degradation = lambda src, fmt: (
            0.02 if "SMT 3" in str(src) or "SMT 3" in str(fmt) else 0.10
        )

        mock_smt_solver.execute = AsyncMock(
            side_effect=[
                {
                    "success": False,
                    "check_sat_result": "error",
                    "model": None,
                    "unsat_core": None,
                    "raw_output": "Error",
                },
                {
                    "success": True,
                    "check_sat_result": "sat",
                    "model": None,
                    "unsat_core": None,
                    "raw_output": "sat",
                },
            ]
        )
        mock_llm_provider.fix_smt_errors = AsyncMock(return_value="(fixed)")

        result = await service.process(informal_text)

        assert isinstance(result, Ok)
        metrics = result.value.metrics

        # Check attempts
        assert metrics.formalization_attempts == 2
        assert metrics.extraction_attempts >= 1  # May vary based on degradation
        assert metrics.validation_attempts == 2

        # Check timing
        assert metrics.formalization_time_seconds > 0
        assert metrics.extraction_time_seconds > 0
        assert metrics.solver_execution_time_seconds > 0
        assert metrics.total_time_seconds > 0

        # Check success
        assert metrics.success is True

    @pytest.mark.asyncio
    async def test_proof_summary_sat(
        self,
        service: PipelineService,
        mock_llm_provider,
        mock_embedding_provider,
        mock_smt_solver,
    ) -> None:
        """Test proof summary generation for SAT results."""
        import numpy as np

        mock_llm_provider.formalize = AsyncMock(return_value="formal")
        mock_llm_provider.extract_to_smtlib = AsyncMock(return_value="(check-sat)")
        mock_embedding_provider.embed = AsyncMock(
            return_value=np.random.rand(384).astype(np.float32)
        )
        service.semantic_verifier.calculate_similarity = lambda src, fmt: 0.95
        service.semantic_verifier.calculate_degradation = lambda src, fmt: 0.02

        mock_smt_solver.execute = AsyncMock(
            return_value={
                "success": True,
                "check_sat_result": "sat",
                "model": "(define-fun x () Int 7)",
                "unsat_core": None,
                "raw_output": "sat\n(define-fun x () Int 7)",
            }
        )

        result = await service.process("x > 5")

        assert isinstance(result, Ok)
        assert "satisfying assignment" in result.value.proof_summary.lower()

    @pytest.mark.asyncio
    async def test_proof_summary_unsat(
        self,
        service: PipelineService,
        mock_llm_provider,
        mock_embedding_provider,
        mock_smt_solver,
    ) -> None:
        """Test proof summary generation for UNSAT results."""
        import numpy as np

        mock_llm_provider.formalize = AsyncMock(return_value="formal")
        mock_llm_provider.extract_to_smtlib = AsyncMock(return_value="(check-sat)")
        mock_embedding_provider.embed = AsyncMock(
            return_value=np.random.rand(384).astype(np.float32)
        )
        service.semantic_verifier.calculate_similarity = lambda src, fmt: 0.95
        service.semantic_verifier.calculate_degradation = lambda src, fmt: 0.02

        mock_smt_solver.execute = AsyncMock(
            return_value={
                "success": True,
                "check_sat_result": "unsat",
                "model": None,
                "unsat_core": "(a1 a2)",
                "raw_output": "unsat\n(a1 a2)",
            }
        )

        result = await service.process("x > 5")

        assert isinstance(result, Ok)
        assert "unsatisfiable" in result.value.proof_summary.lower()

    @pytest.mark.asyncio
    async def test_short_input_auto_skip(
        self,
        service: PipelineService,
        mock_llm_provider,
        mock_embedding_provider,
        mock_smt_solver,
    ) -> None:
        """Test that short inputs automatically skip formalization."""
        import numpy as np

        short_text = "x > 5"  # Less than 200 chars

        mock_embedding_provider.embed = AsyncMock(
            side_effect=[
                np.random.rand(384).astype(np.float32),
                np.random.rand(384).astype(np.float32),
            ]
        )

        mock_llm_provider.extract_to_smtlib = AsyncMock(return_value="(check-sat)")
        service.semantic_verifier.calculate_degradation = lambda src, fmt: 0.02

        mock_smt_solver.execute = AsyncMock(
            return_value={
                "success": True,
                "check_sat_result": "sat",
                "model": None,
                "unsat_core": None,
                "raw_output": "sat",
            }
        )

        result = await service.process(short_text)

        assert isinstance(result, Ok)

        # Formalization was auto-skipped
        assert result.value.formal_text == short_text
        assert result.value.metrics.formalization_attempts == 0

        # LLM formalize should never be called
        mock_llm_provider.formalize.assert_not_called()
