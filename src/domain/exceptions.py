"""Domain-level exceptions for the pipeline.

These exceptions represent business logic failures, not infrastructure errors.
"""


class PipelineError(Exception):
    """Base exception for all pipeline errors."""
    pass


class FormalizationError(PipelineError):
    """Raised when formalization step fails to meet similarity threshold."""

    def __init__(self, message: str, best_similarity: float, attempts: int):
        super().__init__(message)
        self.best_similarity = best_similarity
        self.attempts = attempts


class ExtractionError(PipelineError):
    """Raised when extraction step fails to meet degradation threshold."""

    def __init__(self, message: str, best_degradation: float, attempts: int):
        super().__init__(message)
        self.best_degradation = best_degradation
        self.attempts = attempts


class ValidationError(PipelineError):
    """Raised when validation step fails to execute successfully."""

    def __init__(self, message: str, last_error: str, attempts: int):
        super().__init__(message)
        self.last_error = last_error
        self.attempts = attempts


class LLMError(PipelineError):
    """Raised when LLM provider encounters an error."""
    pass


class EmbeddingError(PipelineError):
    """Raised when embedding provider encounters an error."""
    pass


class SolverExecutionError(PipelineError):
    """Raised when SMT solver execution fails."""
    pass
