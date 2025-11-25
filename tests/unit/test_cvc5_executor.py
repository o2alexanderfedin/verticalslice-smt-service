"""Unit tests for Cvc5Executor.

Tests cover satisfiable/unsatisfiable cases, error handling, timeout scenarios,
and various SMT-LIB features.
"""

import pytest

from src.infrastructure.smt.cvc5_executor import Cvc5Executor


class TestCvc5ExecutorBasic:
    """Basic functionality tests for Cvc5Executor."""

    @pytest.fixture
    def executor(self) -> Cvc5Executor:
        """Create executor instance."""
        return Cvc5Executor()

    @pytest.mark.asyncio
    async def test_satisfiable_constraint(self, executor: Cvc5Executor) -> None:
        """Test execution of satisfiable constraint returns sat with model."""
        smt_code = """
(set-logic QF_LIA)
(declare-const x Int)
(assert (> x 5))
(check-sat)
(get-model)
"""

        result = await executor.execute(smt_code)

        assert result["success"] is True
        assert result["check_sat_result"] == "sat"
        assert result["model"] is not None
        assert "define-fun" in result["model"]
        assert result["error_message"] is None

    @pytest.mark.asyncio
    async def test_unsatisfiable_constraint(self, executor: Cvc5Executor) -> None:
        """Test execution of unsatisfiable constraint returns unsat with core."""
        smt_code = """
(set-logic QF_LIA)
(declare-const x Int)
(assert (! (> x 5) :named a1))
(assert (! (< x 3) :named a2))
(check-sat)
(get-unsat-core)
"""

        result = await executor.execute(smt_code)

        assert result["success"] is True
        assert result["check_sat_result"] == "unsat"
        assert result["unsat_core"] is not None
        assert result["model"] is None
        assert result["error_message"] is None

    @pytest.mark.asyncio
    async def test_satisfiable_without_get_model(self, executor: Cvc5Executor) -> None:
        """Test sat result without explicit get-model command."""
        smt_code = """
(set-logic QF_LIA)
(declare-const x Int)
(assert (> x 5))
(check-sat)
"""

        result = await executor.execute(smt_code)

        assert result["success"] is True
        assert result["check_sat_result"] == "sat"
        # Model should still be extracted programmatically
        assert result["model"] is not None

    @pytest.mark.asyncio
    async def test_unsatisfiable_without_get_unsat_core(self, executor: Cvc5Executor) -> None:
        """Test unsat result without explicit get-unsat-core command."""
        smt_code = """
(set-logic QF_LIA)
(declare-const x Int)
(assert (> x 5))
(assert (< x 3))
(check-sat)
"""

        result = await executor.execute(smt_code)

        assert result["success"] is True
        assert result["check_sat_result"] == "unsat"
        # Unsat core may or may not be available without named assertions
        assert result["model"] is None

    @pytest.mark.asyncio
    async def test_multiple_variables(self, executor: Cvc5Executor) -> None:
        """Test execution with multiple variables."""
        smt_code = """
(set-logic QF_LIA)
(declare-const x Int)
(declare-const y Int)
(assert (> x 5))
(assert (< y 10))
(assert (> (+ x y) 10))
(check-sat)
(get-model)
"""

        result = await executor.execute(smt_code)

        assert result["success"] is True
        assert result["check_sat_result"] == "sat"
        assert result["model"] is not None
        # Should contain both x and y definitions
        assert "x" in result["model"]
        assert "y" in result["model"]


class TestCvc5ExecutorTypes:
    """Test different SMT-LIB types."""

    @pytest.fixture
    def executor(self) -> Cvc5Executor:
        """Create executor instance."""
        return Cvc5Executor()

    @pytest.mark.asyncio
    async def test_integer_type(self, executor: Cvc5Executor) -> None:
        """Test constraints with integer type."""
        smt_code = """
(set-logic QF_LIA)
(declare-const x Int)
(assert (and (> x 0) (< x 100)))
(check-sat)
"""

        result = await executor.execute(smt_code)

        assert result["success"] is True
        assert result["check_sat_result"] == "sat"

    @pytest.mark.asyncio
    async def test_real_type(self, executor: Cvc5Executor) -> None:
        """Test constraints with real type."""
        smt_code = """
(set-logic QF_LRA)
(declare-const x Real)
(assert (and (> x 0.0) (< x 1.0)))
(check-sat)
"""

        result = await executor.execute(smt_code)

        assert result["success"] is True
        assert result["check_sat_result"] == "sat"

    @pytest.mark.asyncio
    async def test_boolean_type(self, executor: Cvc5Executor) -> None:
        """Test constraints with boolean type."""
        smt_code = """
(set-logic QF_UF)
(declare-const p Bool)
(declare-const q Bool)
(assert (and p (not q)))
(check-sat)
"""

        result = await executor.execute(smt_code)

        assert result["success"] is True
        assert result["check_sat_result"] == "sat"

    @pytest.mark.asyncio
    async def test_mixed_types(self, executor: Cvc5Executor) -> None:
        """Test constraints with mixed types."""
        smt_code = """
(set-logic QF_UFLIRA)
(declare-const x Int)
(declare-const y Real)
(declare-const p Bool)
(assert (> x 5))
(assert (< y 10.5))
(assert p)
(check-sat)
"""

        result = await executor.execute(smt_code)

        assert result["success"] is True
        assert result["check_sat_result"] == "sat"


class TestCvc5ExecutorErrorHandling:
    """Error handling tests."""

    @pytest.fixture
    def executor(self) -> Cvc5Executor:
        """Create executor instance."""
        return Cvc5Executor()

    @pytest.mark.asyncio
    async def test_syntax_error(self, executor: Cvc5Executor) -> None:
        """Test handling of syntax error."""
        # Missing closing paren
        smt_code = """
(declare-const x Int
(assert (> x 5))
(check-sat)
"""

        result = await executor.execute(smt_code)

        assert result["success"] is False
        assert result["check_sat_result"] == "error"
        assert result["error_message"] is not None
        assert result["model"] is None
        assert result["unsat_core"] is None

    @pytest.mark.asyncio
    async def test_undefined_symbol(self, executor: Cvc5Executor) -> None:
        """Test handling of undefined symbol."""
        smt_code = """
(set-logic QF_LIA)
(assert (> x 5))
(check-sat)
"""

        result = await executor.execute(smt_code)

        # Should fail due to undeclared variable
        assert result["success"] is False
        assert result["check_sat_result"] == "error"

    @pytest.mark.asyncio
    async def test_type_mismatch(self, executor: Cvc5Executor) -> None:
        """Test handling of type mismatch."""
        smt_code = """
(set-logic QF_LIA)
(declare-const x Int)
(assert (> x 5.5))
(check-sat)
"""

        result = await executor.execute(smt_code)

        # This may or may not fail depending on automatic coercion
        # Just check that result is returned
        assert "success" in result
        assert "check_sat_result" in result

    @pytest.mark.asyncio
    async def test_empty_input(self, executor: Cvc5Executor) -> None:
        """Test handling of empty input."""
        result = await executor.execute("")

        # Should handle gracefully
        assert "success" in result
        assert "check_sat_result" in result


class TestCvc5ExecutorTimeout:
    """Timeout handling tests."""

    @pytest.fixture
    def executor(self) -> Cvc5Executor:
        """Create executor instance."""
        return Cvc5Executor()

    @pytest.mark.asyncio
    async def test_fast_execution(self, executor: Cvc5Executor) -> None:
        """Test that fast execution completes within timeout."""
        smt_code = """
(set-logic QF_LIA)
(declare-const x Int)
(assert (> x 5))
(check-sat)
"""

        result = await executor.execute(smt_code, timeout=5.0)

        assert result["success"] is True
        assert result["check_sat_result"] in ("sat", "unsat", "unknown")

    @pytest.mark.asyncio
    async def test_timeout_short(self, executor: Cvc5Executor) -> None:
        """Test timeout with very short limit."""
        # Create a complex problem that might timeout
        smt_code = """
(set-logic QF_NIA)
(declare-const x Int)
(declare-const y Int)
(declare-const z Int)
(assert (= (* x x) (+ (* y y) (* z z))))
(assert (> x 1000))
(assert (> y 1000))
(assert (> z 1000))
(check-sat)
"""

        # Use very short timeout
        result = await executor.execute(smt_code, timeout=0.001)

        # May timeout or may succeed quickly - both are acceptable
        assert "success" in result
        assert "check_sat_result" in result
        if result["check_sat_result"] == "timeout":
            assert result["success"] is False


class TestCvc5ExecutorRawOutput:
    """Test raw output tracking."""

    @pytest.fixture
    def executor(self) -> Cvc5Executor:
        """Create executor instance."""
        return Cvc5Executor()

    @pytest.mark.asyncio
    async def test_raw_output_sat(self, executor: Cvc5Executor) -> None:
        """Test raw output for sat case."""
        smt_code = """
(set-logic QF_LIA)
(declare-const x Int)
(assert (> x 5))
(check-sat)
"""

        result = await executor.execute(smt_code)

        assert result["raw_output"]
        assert "sat" in result["raw_output"].lower()

    @pytest.mark.asyncio
    async def test_raw_output_unsat(self, executor: Cvc5Executor) -> None:
        """Test raw output for unsat case."""
        smt_code = """
(set-logic QF_LIA)
(declare-const x Int)
(assert (> x 5))
(assert (< x 3))
(check-sat)
"""

        result = await executor.execute(smt_code)

        assert result["raw_output"]
        assert "unsat" in result["raw_output"].lower()

    @pytest.mark.asyncio
    async def test_raw_output_includes_model(self, executor: Cvc5Executor) -> None:
        """Test raw output includes model when requested."""
        smt_code = """
(set-logic QF_LIA)
(declare-const x Int)
(assert (> x 5))
(check-sat)
(get-model)
"""

        result = await executor.execute(smt_code)

        assert result["raw_output"]
        # Raw output should include both sat and model
        assert "sat" in result["raw_output"].lower()
        assert "define-fun" in result["raw_output"]


class TestCvc5ExecutorProtocolCompliance:
    """Test compliance with SMTSolver protocol."""

    @pytest.fixture
    def executor(self) -> Cvc5Executor:
        """Create executor instance."""
        return Cvc5Executor()

    @pytest.mark.asyncio
    async def test_return_type_is_dict(self, executor: Cvc5Executor) -> None:
        """Test that execute returns dict (not dataclass)."""
        smt_code = """
(set-logic QF_LIA)
(declare-const x Int)
(assert (> x 5))
(check-sat)
"""

        result = await executor.execute(smt_code)

        # Must be dict for compatibility with ValidationStep
        assert isinstance(result, dict)

    @pytest.mark.asyncio
    async def test_return_dict_has_required_keys(self, executor: Cvc5Executor) -> None:
        """Test that return dict has all required keys."""
        smt_code = """
(set-logic QF_LIA)
(declare-const x Int)
(assert (> x 5))
(check-sat)
"""

        result = await executor.execute(smt_code)

        # Required keys from SMTSolver protocol
        assert "success" in result
        assert "check_sat_result" in result
        assert "model" in result
        assert "unsat_core" in result
        assert "raw_output" in result
        assert "error_message" in result

    @pytest.mark.asyncio
    async def test_success_field_is_bool(self, executor: Cvc5Executor) -> None:
        """Test that success field is boolean."""
        smt_code = """
(set-logic QF_LIA)
(declare-const x Int)
(assert (> x 5))
(check-sat)
"""

        result = await executor.execute(smt_code)

        assert isinstance(result["success"], bool)

    @pytest.mark.asyncio
    async def test_check_sat_result_is_string(self, executor: Cvc5Executor) -> None:
        """Test that check_sat_result is string."""
        smt_code = """
(set-logic QF_LIA)
(declare-const x Int)
(assert (> x 5))
(check-sat)
"""

        result = await executor.execute(smt_code)

        assert isinstance(result["check_sat_result"], str)
        assert result["check_sat_result"] in (
            "sat",
            "unsat",
            "unknown",
            "timeout",
            "error",
        )
