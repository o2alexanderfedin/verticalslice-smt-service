"""
Retry utility with exponential backoff.

This module provides a decorator for retrying async functions with exponential
backoff on transient failures. Used for API calls and external service integrations.
"""

import asyncio
import logging
from functools import wraps
from typing import Callable, TypeVar, ParamSpec, Any

logger = logging.getLogger(__name__)

P = ParamSpec("P")
T = TypeVar("T")


def retry_with_backoff(
    max_retries: int = 3,
    initial_delay: float = 1.0,
    exponential_base: float = 2.0,
    max_delay: float = 60.0,
    exceptions: tuple[type[Exception], ...] = (Exception,),
) -> Callable[[Callable[P, T]], Callable[P, T]]:
    """
    Decorator for retrying async functions with exponential backoff.

    This decorator automatically retries failed async function calls with
    increasing delay between attempts. Useful for handling transient failures
    in API calls, network requests, and external service integrations.

    Args:
        max_retries: Maximum number of retry attempts (default: 3)
        initial_delay: Initial delay in seconds before first retry (default: 1.0)
        exponential_base: Base for exponential backoff calculation (default: 2.0)
        max_delay: Maximum delay in seconds between retries (default: 60.0)
        exceptions: Tuple of exception types to catch and retry (default: all exceptions)

    Returns:
        Decorated async function with retry logic

    Example:
        >>> @retry_with_backoff(max_retries=3, initial_delay=1.0)
        ... async def call_api(url: str) -> dict:
        ...     async with httpx.AsyncClient() as client:
        ...         response = await client.get(url)
        ...         return response.json()
    """

    def decorator(func: Callable[P, T]) -> Callable[P, T]:
        @wraps(func)
        async def wrapper(*args: P.args, **kwargs: P.kwargs) -> T:
            last_exception: Exception | None = None

            for attempt in range(max_retries + 1):
                try:
                    return await func(*args, **kwargs)
                except exceptions as e:
                    last_exception = e

                    if attempt == max_retries:
                        logger.error(
                            f"{func.__name__} failed after {max_retries} retries: {e}"
                        )
                        raise

                    # Calculate exponential backoff delay
                    delay = min(
                        initial_delay * (exponential_base ** attempt),
                        max_delay
                    )

                    logger.warning(
                        f"{func.__name__} attempt {attempt + 1}/{max_retries + 1} failed: {e}. "
                        f"Retrying in {delay:.2f}s..."
                    )

                    await asyncio.sleep(delay)

            # This should never be reached due to raise in the loop
            if last_exception:
                raise last_exception
            raise RuntimeError(f"{func.__name__} exhausted retries without exception")

        return wrapper

    return decorator
