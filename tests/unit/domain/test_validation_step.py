"""Unit tests for ValidationStep.

Tests cover:
- Successful validation (sat/unsat/unknown)
- Syntax error handling with retry
- Max retries exhausted
- Solver execution exceptions
- Error fixing via LLM
- Markdown fence stripping
"""

from unittest.mock import AsyncMock

import pytest

from src.domain.exceptions import ValidationError
from src.domain.steps.validation import ValidationStep
from src.shared.result import Err, Ok


class TestValidationStep:
    """Tests for ValidationStep."""

    @pytest.fixture
    def step(self, mock_llm_provider, mock_smt_solver) -> ValidationStep:
        """Create validation step with mocked dependencies."""
        return ValidationStep(
            llm_provider=mock_llm_provider,
            smt_solver=mock_smt_solver,
            max_retries=3,
            solver_timeout=30.0,
        )

    @pytest.mark.asyncio
    async def test_successful_validation_sat_result(
        self, step: ValidationStep, mock_smt_solver
    ) -> None:
        """Test successful validation with SAT result."""
        smt_code = "(declare-const x Int)\n(assert (> x 5))\n(check-sat)"

        mock_smt_solver.execute = AsyncMock(
            return_value={
                "success": True,
                "check_sat_result": "sat",
                "model": "(define-fun x () Int 10)",
                "unsat_core": None,
                "raw_output": "sat\n(define-fun x () Int 10)",
            }
        )

        result = await step.execute(smt_code)

        assert isinstance(result, Ok)
        assert result.value.success is True
        assert result.value.check_sat_result == "sat"
        assert result.value.model == "(define-fun x () Int 10)"
        assert result.value.unsat_core is None
        assert result.value.attempts == 1

    @pytest.mark.asyncio
    async def test_successful_validation_unsat_result(
        self, step: ValidationStep, mock_smt_solver
    ) -> None:
        """Test successful validation with UNSAT result."""
        smt_code = "(assert false)\n(check-sat)"

        mock_smt_solver.execute = AsyncMock(
            return_value={
                "success": True,
                "check_sat_result": "unsat",
                "model": None,
                "unsat_core": "(a1 a2)",
                "raw_output": "unsat\n(a1 a2)",
            }
        )

        result = await step.execute(smt_code)

        assert isinstance(result, Ok)
        assert result.value.success is True
        assert result.value.check_sat_result == "unsat"
        assert result.value.model is None
        assert result.value.unsat_core == "(a1 a2)"
        assert result.value.attempts == 1

    @pytest.mark.asyncio
    async def test_successful_validation_unknown_result(
        self, step: ValidationStep, mock_smt_solver
    ) -> None:
        """Test successful validation with UNKNOWN result."""
        smt_code = "(check-sat)"

        mock_smt_solver.execute = AsyncMock(
            return_value={
                "success": True,
                "check_sat_result": "unknown",
                "model": None,
                "unsat_core": None,
                "raw_output": "unknown",
            }
        )

        result = await step.execute(smt_code)

        assert isinstance(result, Ok)
        assert result.value.success is True
        assert result.value.check_sat_result == "unknown"
        assert result.value.attempts == 1

    @pytest.mark.asyncio
    async def test_syntax_error_with_successful_fix(
        self, step: ValidationStep, mock_llm_provider, mock_smt_solver
    ) -> None:
        """Test syntax error recovery via LLM fix."""
        broken_code = "(assert > x 5)"  # Invalid syntax
        fixed_code = "(assert (> x 5))"

        # First attempt fails, second succeeds
        mock_smt_solver.execute = AsyncMock(
            side_effect=[
                {
                    "success": False,
                    "check_sat_result": "error",
                    "model": None,
                    "unsat_core": None,
                    "raw_output": "Parse error: unexpected token",
                },
                {
                    "success": True,
                    "check_sat_result": "sat",
                    "model": "(define-fun x () Int 10)",
                    "unsat_core": None,
                    "raw_output": "sat\n(define-fun x () Int 10)",
                },
            ]
        )

        mock_llm_provider.fix_smt_errors = AsyncMock(return_value=fixed_code)

        result = await step.execute(broken_code)

        assert isinstance(result, Ok)
        assert result.value.success is True
        assert result.value.attempts == 2

        # Verify LLM was called to fix error
        mock_llm_provider.fix_smt_errors.assert_called_once()
        call_args = mock_llm_provider.fix_smt_errors.call_args
        assert broken_code in call_args.args
        assert "Parse error" in call_args.args[1]

    @pytest.mark.asyncio
    async def test_max_retries_exhausted(
        self, step: ValidationStep, mock_llm_provider, mock_smt_solver
    ) -> None:
        """Test that max retries returns error."""
        smt_code = "(broken code)"

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

        result = await step.execute(smt_code)

        assert isinstance(result, Err)
        assert isinstance(result.error, ValidationError)
        assert "failed after 3 attempts" in str(result.error)
        assert result.error.attempts == 3
        assert "Syntax error" in result.error.last_error

    @pytest.mark.asyncio
    async def test_solver_exception_handling(
        self, step: ValidationStep, mock_llm_provider, mock_smt_solver
    ) -> None:
        """Test handling of solver execution exceptions."""
        smt_code = "(check-sat)"

        # First attempt throws, second succeeds
        mock_smt_solver.execute = AsyncMock(
            side_effect=[
                RuntimeError("Solver crashed"),
                {
                    "success": True,
                    "check_sat_result": "sat",
                    "model": None,
                    "unsat_core": None,
                    "raw_output": "sat",
                },
            ]
        )

        mock_llm_provider.fix_smt_errors = AsyncMock(return_value=smt_code)

        result = await step.execute(smt_code)

        assert isinstance(result, Ok)
        assert result.value.attempts == 2

    @pytest.mark.asyncio
    async def test_all_solver_attempts_fail_with_exceptions(
        self, step: ValidationStep, mock_llm_provider, mock_smt_solver
    ) -> None:
        """Test when all solver attempts fail with exceptions."""
        smt_code = "(check-sat)"

        mock_smt_solver.execute = AsyncMock(side_effect=RuntimeError("Solver down"))
        mock_llm_provider.fix_smt_errors = AsyncMock(return_value=smt_code)

        result = await step.execute(smt_code)

        assert isinstance(result, Err)
        assert isinstance(result.error, ValidationError)
        assert result.error.attempts == 3

    @pytest.mark.asyncio
    async def test_markdown_fence_stripping(self, step: ValidationStep, mock_smt_solver) -> None:
        """Test that markdown code fences are stripped."""
        smt_with_fences = "```smt-lib\n(check-sat)\n```"

        mock_smt_solver.execute = AsyncMock(
            return_value={
                "success": True,
                "check_sat_result": "sat",
                "model": None,
                "unsat_core": None,
                "raw_output": "sat",
            }
        )

        result = await step.execute(smt_with_fences)

        assert isinstance(result, Ok)

        # Verify solver received code without fences
        call_args = mock_smt_solver.execute.call_args
        assert "```" not in call_args.args[0]
        assert "(check-sat)" in call_args.args[0]

    @pytest.mark.asyncio
    async def test_llm_fix_failure_continues_retry(
        self, step: ValidationStep, mock_llm_provider, mock_smt_solver
    ) -> None:
        """Test that LLM fix failure doesn't stop retry loop."""
        smt_code = "(broken)"

        mock_smt_solver.execute = AsyncMock(
            return_value={
                "success": False,
                "check_sat_result": "error",
                "model": None,
                "unsat_core": None,
                "raw_output": "Error",
            }
        )

        # LLM fix fails on first attempt, succeeds on second
        mock_llm_provider.fix_smt_errors = AsyncMock(
            side_effect=[
                RuntimeError("LLM down"),
                "(fixed)",
            ]
        )

        result = await step.execute(smt_code)

        # Should exhaust retries
        assert isinstance(result, Err)
        assert result.error.attempts == 3

    @pytest.mark.asyncio
    async def test_timeout_parameter_passed_to_solver(
        self, step: ValidationStep, mock_smt_solver
    ) -> None:
        """Test that solver timeout parameter is passed correctly."""
        smt_code = "(check-sat)"

        mock_smt_solver.execute = AsyncMock(
            return_value={
                "success": True,
                "check_sat_result": "sat",
                "model": None,
                "unsat_core": None,
                "raw_output": "sat",
            }
        )

        result = await step.execute(smt_code)

        assert isinstance(result, Ok)

        # Verify timeout was passed
        call_args = mock_smt_solver.execute.call_args
        assert call_args.kwargs["timeout"] == 30.0

    @pytest.mark.asyncio
    async def test_multiple_retries_with_progressive_fixes(
        self, step: ValidationStep, mock_llm_provider, mock_smt_solver
    ) -> None:
        """Test multiple retry attempts with progressive fixes."""
        initial_code = "(broken 1)"
        fix_1 = "(broken 2)"
        fix_2 = "(fixed)"

        mock_smt_solver.execute = AsyncMock(
            side_effect=[
                {
                    "success": False,
                    "check_sat_result": "error",
                    "model": None,
                    "unsat_core": None,
                    "raw_output": "Error 1",
                },
                {
                    "success": False,
                    "check_sat_result": "error",
                    "model": None,
                    "unsat_core": None,
                    "raw_output": "Error 2",
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

        mock_llm_provider.fix_smt_errors = AsyncMock(side_effect=[fix_1, fix_2])

        result = await step.execute(initial_code)

        assert isinstance(result, Ok)
        assert result.value.attempts == 3
        assert mock_llm_provider.fix_smt_errors.call_count == 2
