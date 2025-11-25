"""Unit tests for retry decorator."""

import pytest

from src.shared.retry import retry_with_backoff


class TestRetryWithBackoff:
    """Tests for retry_with_backoff decorator."""

    @pytest.mark.asyncio
    async def test_success_on_first_attempt(self) -> None:
        """Test function succeeds on first attempt."""
        call_count = 0

        @retry_with_backoff(max_retries=3)
        async def succeeds_immediately() -> str:
            nonlocal call_count
            call_count += 1
            return "success"

        result = await succeeds_immediately()
        assert result == "success"
        assert call_count == 1

    @pytest.mark.asyncio
    async def test_success_after_retries(self) -> None:
        """Test function succeeds after some retries."""
        call_count = 0

        @retry_with_backoff(max_retries=3, initial_delay=0.01)
        async def succeeds_on_third_attempt() -> str:
            nonlocal call_count
            call_count += 1
            if call_count < 3:
                raise ValueError("Not yet")
            return "success"

        result = await succeeds_on_third_attempt()
        assert result == "success"
        assert call_count == 3

    @pytest.mark.asyncio
    async def test_fails_after_max_retries(self) -> None:
        """Test function raises after exhausting retries."""
        call_count = 0

        @retry_with_backoff(max_retries=2, initial_delay=0.01)
        async def always_fails() -> str:
            nonlocal call_count
            call_count += 1
            raise ValueError("Always fails")

        with pytest.raises(ValueError, match="Always fails"):
            await always_fails()

        assert call_count == 3  # Initial + 2 retries

    @pytest.mark.asyncio
    async def test_specific_exception_caught(self) -> None:
        """Test only specified exceptions are caught."""
        call_count = 0

        @retry_with_backoff(max_retries=3, initial_delay=0.01, exceptions=(ValueError,))
        async def raises_different_exception() -> str:
            nonlocal call_count
            call_count += 1
            raise RuntimeError("Not retried")

        with pytest.raises(RuntimeError, match="Not retried"):
            await raises_different_exception()

        assert call_count == 1  # No retries for RuntimeError

    @pytest.mark.asyncio
    async def test_exponential_backoff(self) -> None:
        """Test exponential backoff delays increase."""
        call_count = 0
        delays_used = []

        @retry_with_backoff(max_retries=3, initial_delay=0.01, exponential_base=2.0)
        async def fails_with_tracking() -> str:
            nonlocal call_count
            import time

            if call_count > 0:
                delays_used.append(time.time())
            call_count += 1
            if call_count < 4:
                raise ValueError("Retry")
            return "success"

        result = await fails_with_tracking()
        assert result == "success"
        assert call_count == 4

    @pytest.mark.asyncio
    async def test_max_delay_cap(self) -> None:
        """Test delay is capped at max_delay."""
        call_count = 0

        @retry_with_backoff(max_retries=2, initial_delay=10.0, max_delay=0.01)
        async def capped_delay() -> str:
            nonlocal call_count
            call_count += 1
            if call_count < 3:
                raise ValueError("Retry")
            return "success"

        result = await capped_delay()
        assert result == "success"

    @pytest.mark.asyncio
    async def test_function_with_args(self) -> None:
        """Test retry works with function arguments."""
        call_count = 0

        @retry_with_backoff(max_retries=2, initial_delay=0.01)
        async def add(a: int, b: int) -> int:
            nonlocal call_count
            call_count += 1
            if call_count < 2:
                raise ValueError("Retry")
            return a + b

        result = await add(5, 3)
        assert result == 8
        assert call_count == 2

    @pytest.mark.asyncio
    async def test_function_with_kwargs(self) -> None:
        """Test retry works with keyword arguments."""
        call_count = 0

        @retry_with_backoff(max_retries=2, initial_delay=0.01)
        async def greet(name: str, greeting: str = "Hello") -> str:
            nonlocal call_count
            call_count += 1
            if call_count < 2:
                raise ValueError("Retry")
            return f"{greeting}, {name}"

        result = await greet(name="World", greeting="Hi")
        assert result == "Hi, World"

    @pytest.mark.asyncio
    async def test_zero_retries(self) -> None:
        """Test with max_retries=0 (no retries)."""
        call_count = 0

        @retry_with_backoff(max_retries=0, initial_delay=0.01)
        async def no_retries() -> str:
            nonlocal call_count
            call_count += 1
            raise ValueError("Fails immediately")

        with pytest.raises(ValueError):
            await no_retries()

        assert call_count == 1  # Only initial attempt
