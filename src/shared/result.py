"""Result type for functional error handling.

This module implements a Rust-style Result type that makes error handling
explicit in type signatures without relying on exceptions for control flow.
"""

from collections.abc import Callable
from dataclasses import dataclass
from typing import Generic, TypeVar, Union

T = TypeVar("T")  # Success type
E = TypeVar("E", bound=Exception)  # Error type
U = TypeVar("U")  # Map target type


@dataclass(frozen=True)
class Ok(Generic[T]):
    """Successful result containing a value."""

    value: T

    def is_ok(self) -> bool:
        """Check if this is a success result."""
        return True

    def is_err(self) -> bool:
        """Check if this is an error result."""
        return False

    def unwrap(self) -> T:
        """Get the value (safe because this is Ok)."""
        return self.value

    def unwrap_or(self, default: T) -> T:
        """Get the value or default (returns value because this is Ok)."""
        return self.value

    def map(self, func: Callable[[T], U]) -> "Result[U, E]":
        """Transform the success value."""
        return Ok(func(self.value))

    def __repr__(self) -> str:
        return f"Ok({self.value!r})"


@dataclass(frozen=True)
class Err(Generic[E]):
    """Error result containing an exception."""

    error: E

    def is_ok(self) -> bool:
        """Check if this is a success result."""
        return False

    def is_err(self) -> bool:
        """Check if this is an error result."""
        return True

    def unwrap(self) -> T:
        """Get the value (raises because this is Err)."""
        raise self.error

    def unwrap_or(self, default: T) -> T:
        """Get the value or default (returns default because this is Err)."""
        return default

    def map(self, func: Callable[[T], U]) -> "Result[U, E]":
        """Transform the success value (does nothing for Err)."""
        return self  # type: ignore

    def __repr__(self) -> str:
        return f"Err({self.error!r})"


# Type alias for clearer function signatures
Result = Union[Ok[T], Err[E]]
