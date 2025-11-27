"""
Application exception hierarchy.

This module defines all domain and application exceptions for the SMT Pipeline.
Exceptions are organized hierarchically with a base PipelineError class and
specific exceptions for each pipeline step failure.

These exceptions are used in Result[T, E] types to represent expected failures
that are part of normal operation (e.g., similarity threshold not met).
"""


class PipelineError(Exception):
    """
    Base exception for all pipeline errors.

    All domain-specific exceptions inherit from this base class,
    making it easy to catch all pipeline-related errors.
    """

    pass


class FormalizationError(PipelineError):
    """
    Exception raised when Step 1 (Formalization) fails.

    This error indicates that the pipeline could not produce formalized text
    with sufficient semantic similarity (≥91%) to the original informal text
    within the allowed number of retry attempts.

    Attributes:
        message: Human-readable error message
        attempts: Number of attempts made before failure
        final_similarity: Best similarity score achieved across all attempts
        informal_text: The original informal text that failed to formalize
    """

    def __init__(
        self,
        message: str,
        attempts: int,
        final_similarity: float,
        informal_text: str,
    ) -> None:
        """
        Initialize FormalizationError.

        Args:
            message: Human-readable error message
            attempts: Number of attempts made (1-3)
            final_similarity: Best similarity score achieved (0.0-1.0)
            informal_text: The original informal text
        """
        super().__init__(message)
        self.attempts = attempts
        self.final_similarity = final_similarity
        self.informal_text = informal_text

    def __str__(self) -> str:
        """Return detailed error string."""
        return (
            f"{super().__str__()} "
            f"(attempts={self.attempts}, "
            f"final_similarity={self.final_similarity:.4f})"
        )


class ExtractionError(PipelineError):
    """
    Exception raised when Step 2 (Extraction) fails.

    This error indicates that the pipeline could not extract SMT-LIB code
    with acceptable information degradation (≤5%) from the formal text
    within the allowed number of retry attempts.

    Attributes:
        message: Human-readable error message
        attempts: Number of attempts made before failure
        final_degradation: Lowest degradation score achieved across all attempts
        formal_text: The formal text that failed to extract
    """

    def __init__(
        self,
        message: str,
        attempts: int,
        final_degradation: float,
        formal_text: str,
    ) -> None:
        """
        Initialize ExtractionError.

        Args:
            message: Human-readable error message
            attempts: Number of attempts made (1-5)
            final_degradation: Lowest degradation achieved (0.0-1.0)
            formal_text: The formal text that failed
        """
        super().__init__(message)
        self.attempts = attempts
        self.final_degradation = final_degradation
        self.formal_text = formal_text

    def __str__(self) -> str:
        """Return detailed error string."""
        return (
            f"{super().__str__()} "
            f"(attempts={self.attempts}, "
            f"final_degradation={self.final_degradation:.4f})"
        )


class ValidationError(PipelineError):
    """
    Exception raised when Step 3 (Validation) fails.

    This error indicates that the pipeline could not produce valid,
    executable SMT-LIB code within the allowed number of retry attempts.
    The solver continued to return syntax errors even after LLM-based fixes.

    Attributes:
        message: Human-readable error message
        attempts: Number of attempts made before failure
        last_error: Last error message from the solver (alias for final_error)
        final_error: Last error message from the solver
        smt_code: The SMT-LIB code that failed validation
        informal_text: Original informal constraint (for diagnostics)
        formal_text: Formalized constraint (for diagnostics)
        attempt_history: History of all attempts (for diagnostics)
    """

    def __init__(
        self,
        message: str,
        attempts: int,
        last_error: str = "",
        final_error: str | None = None,
        smt_code: str = "",
        informal_text: str = "",
        formal_text: str = "",
        attempt_history: list[dict[str, str]] | None = None,
    ) -> None:
        """
        Initialize ValidationError.

        Args:
            message: Human-readable error message
            attempts: Number of attempts made (1-3)
            last_error: Last solver error message
            final_error: Alias for last_error (backward compatibility)
            smt_code: The SMT-LIB code that failed
            informal_text: Original informal constraint
            formal_text: Formalized constraint
            attempt_history: List of attempt details
        """
        super().__init__(message)
        self.attempts = attempts
        # Support both last_error and final_error parameter names
        self.last_error = last_error or final_error or ""
        self.final_error = self.last_error  # Alias for backward compatibility
        self.smt_code = smt_code
        self.informal_text = informal_text
        self.formal_text = formal_text
        self.attempt_history = attempt_history or []

    def __str__(self) -> str:
        """Return detailed error string without truncation."""
        return (
            f"{super().__str__()} " f"(attempts={self.attempts}, " f"last_error={self.last_error})"
        )
