"""Protocol definitions for dependency inversion.

These protocols define interfaces that infrastructure implementations must satisfy.
Following the Dependency Inversion Principle: domain depends on abstractions, not concretions.
"""

from typing import Any, Protocol
import numpy as np
import numpy.typing as npt


class EmbeddingProvider(Protocol):
    """Protocol for generating text embeddings."""

    async def embed(self, text: str) -> npt.NDArray[np.float32]:
        """Generate embedding vector for text.

        Args:
            text: Input text to embed

        Returns:
            Embedding vector as numpy array

        Raises:
            EmbeddingError: If embedding generation fails
        """
        ...


class LLMProvider(Protocol):
    """Protocol for LLM interactions."""

    async def formalize(
        self,
        informal_text: str,
        temperature: float,
        previous_attempt: str | None = None,
        previous_similarity: float | None = None
    ) -> str:
        """Convert informal text to formal text while preserving semantics.

        Args:
            informal_text: Natural language input
            temperature: Sampling temperature (0.0 = deterministic)
            previous_attempt: Previous formalization attempt (for refinement)
            previous_similarity: Similarity score of previous attempt

        Returns:
            Formalized text (or refined version if previous_attempt provided)

        Raises:
            LLMError: If LLM call fails
        """
        ...

    async def extract_to_smtlib(
        self,
        formal_text: str,
        detail_level: float
    ) -> str:
        """Extract SMT-LIB code from formalized text with annotations.

        Args:
            formal_text: Formalized text from Step 1
            detail_level: Level of detail in annotations (0.0-1.0)

        Returns:
            Complete SMT-LIB code with annotations

        Raises:
            LLMError: If LLM call fails
        """
        ...

    async def fix_smt_errors(self, smt_code: str, error_message: str) -> str:
        """Fix SMT-LIB syntax or semantic errors.

        Args:
            smt_code: SMT-LIB code that failed to execute
            error_message: Error message from solver

        Returns:
            Fixed SMT-LIB code

        Raises:
            LLMError: If LLM call fails
        """
        ...


class SMTSolver(Protocol):
    """Protocol for SMT solver execution."""

    async def execute(
        self,
        smt_code: str,
        timeout: float = 30.0
    ) -> dict[str, Any]:
        """Execute SMT-LIB code and return results.

        Args:
            smt_code: Complete SMT-LIB code to execute
            timeout: Execution timeout in seconds

        Returns:
            Dictionary with keys:
                - success: bool (whether execution succeeded)
                - check_sat_result: str (sat/unsat/unknown or error)
                - model: Optional[str] (variable assignments if sat)
                - unsat_core: Optional[str] (conflicting constraints if unsat)
                - raw_output: str (complete solver output)
                - error_message: Optional[str] (error details if failed)

        Raises:
            SolverExecutionError: If solver fails critically
        """
        ...


class SemanticVerifier(Protocol):
    """Protocol for semantic verification using embeddings."""

    def calculate_similarity(
        self,
        embedding1: npt.NDArray[np.float32],
        embedding2: npt.NDArray[np.float32]
    ) -> float:
        """Calculate cosine similarity between two embeddings.

        Args:
            embedding1: First embedding vector
            embedding2: Second embedding vector

        Returns:
            Cosine similarity score (0.0 to 1.0)
        """
        ...

    def calculate_degradation(
        self,
        embedding_source: npt.NDArray[np.float32],
        embedding_target: npt.NDArray[np.float32]
    ) -> float:
        """Calculate information degradation between source and target.

        Degradation is defined as: 1 - similarity

        Args:
            embedding_source: Source text embedding
            embedding_target: Target text embedding

        Returns:
            Degradation score (0.0 to 1.0, lower is better)
        """
        ...
