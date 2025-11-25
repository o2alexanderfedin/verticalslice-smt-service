"""Unit tests for Result type."""

import pytest

from src.shared.result import Err, Ok


class TestOk:
    """Tests for Ok result type."""

    def test_ok_creation(self) -> None:
        """Test creating Ok result."""
        result = Ok(42)
        assert result.value == 42

    def test_ok_is_ok(self) -> None:
        """Test is_ok returns True for Ok."""
        result = Ok("success")
        assert result.is_ok() is True
        assert result.is_err() is False

    def test_ok_unwrap(self) -> None:
        """Test unwrap returns value for Ok."""
        result = Ok(42)
        assert result.unwrap() == 42

    def test_ok_unwrap_or(self) -> None:
        """Test unwrap_or returns value (not default) for Ok."""
        result = Ok(42)
        assert result.unwrap_or(100) == 42

    def test_ok_map(self) -> None:
        """Test map transforms value for Ok."""
        result = Ok(5)
        mapped = result.map(lambda x: x * 2)
        assert mapped.is_ok()
        assert mapped.unwrap() == 10

    def test_ok_map_chain(self) -> None:
        """Test chaining map operations."""
        result = Ok(5)
        mapped = result.map(lambda x: x * 2).map(lambda x: x + 3)
        assert mapped.unwrap() == 13

    def test_ok_repr(self) -> None:
        """Test string representation of Ok."""
        result = Ok(42)
        assert repr(result) == "Ok(42)"

    def test_ok_with_string(self) -> None:
        """Test Ok with string value."""
        result = Ok("test")
        assert result.unwrap() == "test"

    def test_ok_with_none(self) -> None:
        """Test Ok with None value."""
        result = Ok(None)
        assert result.unwrap() is None

    def test_ok_frozen(self) -> None:
        """Test Ok is immutable (frozen dataclass)."""
        result = Ok(42)
        with pytest.raises((AttributeError, TypeError)):  # FrozenInstanceError
            result.value = 100  # type: ignore


class TestErr:
    """Tests for Err result type."""

    def test_err_creation(self) -> None:
        """Test creating Err result."""
        error = ValueError("test error")
        result = Err(error)
        assert result.error is error

    def test_err_is_err(self) -> None:
        """Test is_err returns True for Err."""
        result = Err(ValueError("test"))
        assert result.is_err() is True
        assert result.is_ok() is False

    def test_err_unwrap_raises(self) -> None:
        """Test unwrap raises the error for Err."""
        result = Err(ValueError("test error"))
        with pytest.raises(ValueError, match="test error"):
            result.unwrap()

    def test_err_unwrap_or(self) -> None:
        """Test unwrap_or returns default for Err."""
        result: Err[ValueError] = Err(ValueError("test"))
        assert result.unwrap_or(42) == 42

    def test_err_map(self) -> None:
        """Test map does nothing for Err."""
        result = Err(ValueError("test"))
        mapped = result.map(lambda x: x * 2)  # type: ignore
        assert mapped.is_err()
        assert mapped.error.args[0] == "test"

    def test_err_repr(self) -> None:
        """Test string representation of Err."""
        error = ValueError("test")
        result = Err(error)
        assert "Err" in repr(result)
        assert "ValueError" in repr(result)

    def test_err_with_custom_exception(self) -> None:
        """Test Err with custom exception."""

        class CustomError(Exception):
            pass

        result = Err(CustomError("custom"))
        with pytest.raises(CustomError, match="custom"):
            result.unwrap()

    def test_err_frozen(self) -> None:
        """Test Err is immutable (frozen dataclass)."""
        result = Err(ValueError("test"))
        with pytest.raises((AttributeError, TypeError)):  # FrozenInstanceError
            result.error = RuntimeError("new")  # type: ignore


class TestResultPatternMatching:
    """Tests for pattern matching with Result types."""

    def test_pattern_match_ok(self) -> None:
        """Test pattern matching on Ok result."""
        result = Ok(42)

        value = result.unwrap() if result.is_ok() else 0

        assert value == 42

    def test_pattern_match_err(self) -> None:
        """Test pattern matching on Err result."""
        result = Err(ValueError("test"))

        value = result.unwrap_or(100) if result.is_err() else result.unwrap()

        assert value == 100

    def test_function_returning_result_ok(self) -> None:
        """Test function returning Ok result."""

        def divide(a: int, b: int) -> Ok[float] | Err[ZeroDivisionError]:
            if b == 0:
                return Err(ZeroDivisionError("Cannot divide by zero"))
            return Ok(a / b)

        result = divide(10, 2)
        assert result.is_ok()
        assert result.unwrap() == 5.0

    def test_function_returning_result_err(self) -> None:
        """Test function returning Err result."""

        def divide(a: int, b: int) -> Ok[float] | Err[ZeroDivisionError]:
            if b == 0:
                return Err(ZeroDivisionError("Cannot divide by zero"))
            return Ok(a / b)

        result = divide(10, 0)
        assert result.is_err()
        with pytest.raises(ZeroDivisionError):
            result.unwrap()


class TestResultComposability:
    """Tests for composing Result types."""

    def test_ok_chain_multiple_operations(self) -> None:
        """Test chaining multiple operations on Ok."""
        result = Ok(5).map(lambda x: x * 2).map(lambda x: str(x)).map(lambda x: f"Result: {x}")

        assert result.unwrap() == "Result: 10"

    def test_err_chain_stops_at_error(self) -> None:
        """Test error propagation in chain."""
        result: Ok[int] | Err[ValueError] = Err(ValueError("error"))
        mapped = result.map(lambda x: x * 2).map(lambda x: x + 1)  # type: ignore

        assert mapped.is_err()
        with pytest.raises(ValueError, match="error"):
            mapped.unwrap()

    def test_unwrap_or_with_computation(self) -> None:
        """Test unwrap_or can provide computed default."""
        err_result: Err[ValueError] = Err(ValueError("test"))
        default_value = 100
        assert err_result.unwrap_or(default_value) == 100

        ok_result = Ok(42)
        assert ok_result.unwrap_or(default_value) == 42
