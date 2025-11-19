"""
Domain interfaces (protocols) for dependency inversion.

This module defines all external dependencies as runtime-checkable protocols.
This ensures the domain layer has no concrete dependencies on infrastructure,
enabling easy testing and allowing implementations to be swapped at runtime.

All protocols use typing.Protocol with @runtime_checkable decorator for
structural subtyping and runtime type checking.
"""

from typing import Protocol, runtime_checkable

import numpy as np
import numpy.typing as npt

from src.domain.models import SolverResult


# ============================================================================
# Embedding Provider Protocol
# ============================================================================


@runtime_checkable
class EmbeddingProvider(Protocol):
    """
    Protocol for generating text embeddings.

    Implementations:
    - SentenceTransformerProvider (local model: all-MiniLM-L6-v2)
    - OpenAIEmbeddingProvider (API-based, future extension)

    The embedding provider generates dense vector representations of text
    for semantic similarity calculations.
    """

    async def embed(self, text: str) -> npt.NDArray[np.float32]:
        """
        Generate embedding vector for text.

        Args:
            text: Input text to embed

        Returns:
            Numpy array of shape (embedding_dim,) with dtype float32
            Typical dimension: 384 for all-MiniLM-L6-v2

        Raises:
            EmbeddingError: If embedding generation fails
        """
        ...


# ============================================================================
# LLM Provider Protocol
# ============================================================================


@runtime_checkable
class LLMProvider(Protocol):
    """
    Protocol for LLM interactions.

    Implementations:
    - AnthropicClient (Claude Sonnet 4.5)
    - OpenAIClient (GPT-4, future extension)

    The LLM provider handles all three transformation steps:
    1. Formalization: informal text → formal text
    2. Extraction: formal text → SMT-LIB code
    3. Error correction: broken SMT-LIB → fixed SMT-LIB
    """

    async def formalize(
        self,
        informal_text: str,
        temperature: float = 0.3,
        previous_attempt: str | None = None,
        previous_similarity: float | None = None
    ) -> str:
        """
        Transform informal text to formal text.

        Args:
            informal_text: Source natural language text
            temperature: Sampling temperature (0.0-1.0)
                        Lower = more deterministic
                        Higher = more creative variations
            previous_attempt: Previous formalization attempt (for refinement)
            previous_similarity: Similarity score of previous attempt

        Returns:
            Formalized text with explicit facts and rules (or refined version)

        Raises:
            LLMError: If API call fails
        """
        ...

    async def extract_to_smtlib(
        self, formal_text: str, detail_level: float = 0.6
    ) -> str:
        """
        Extract formal text to SMT-LIB code.

        Args:
            formal_text: Formalized text with explicit semantics
            detail_level: Annotation detail level (0.0-1.0)
                         Lower = minimal annotations
                         Higher = verbose annotations preserving more context

        Returns:
            Complete annotated SMT-LIB code (executable)

        Raises:
            LLMError: If API call fails
        """
        ...

    async def fix_smt_errors(
        self, smt_code: str, error_message: str
    ) -> str:
        """
        Fix SMT-LIB syntax errors while preserving annotations.

        Args:
            smt_code: Broken SMT-LIB code with syntax errors
            error_message: Error message from solver execution

        Returns:
            Fixed SMT-LIB code (should execute without errors)

        Raises:
            LLMError: If API call fails
        """
        ...


# ============================================================================
# SMT Solver Protocol
# ============================================================================


@runtime_checkable
class SMTSolver(Protocol):
    """
    Protocol for SMT solver execution.

    Implementations:
    - PysmtExecutor (solver-agnostic via pySMT library)

    The solver executes SMT-LIB code and returns the check-sat result
    along with model (if sat) or unsat-core (if unsat).
    """

    async def execute(
        self,
        smt_lib_code: str,
        timeout_seconds: int = 30,
        get_model: bool = True,
        get_unsat_core: bool = False,
    ) -> SolverResult:
        """
        Execute SMT-LIB code with solver.

        Args:
            smt_lib_code: Complete SMT-LIB file to execute
            timeout_seconds: Maximum execution time
            get_model: Whether to retrieve model if sat
            get_unsat_core: Whether to retrieve unsat-core if unsat

        Returns:
            SolverResult with check-sat result, model/unsat-core, and raw output

        Raises:
            SolverError: If solver execution fails or times out
        """
        ...


# ============================================================================
# Semantic Verifier Protocol
# ============================================================================


@runtime_checkable
class SemanticVerifier(Protocol):
    """
    Protocol for semantic verification using embedding distances.

    Implementations:
    - EmbeddingDistanceVerifier (cosine similarity and degradation)

    The verifier calculates similarity and degradation metrics between
    text embeddings to ensure semantic preservation through pipeline steps.
    """

    def calculate_similarity(
        self,
        embedding_a: npt.NDArray[np.float32],
        embedding_b: npt.NDArray[np.float32],
    ) -> float:
        """
        Calculate cosine similarity between two embeddings.

        Cosine similarity measures the angle between vectors, ranging from
        -1 (opposite) to 1 (identical). Values ≥0.91 indicate high semantic similarity.

        Args:
            embedding_a: First embedding vector
            embedding_b: Second embedding vector

        Returns:
            Cosine similarity score in range [-1.0, 1.0]
            Typically in range [0.0, 1.0] for semantic text

        Raises:
            ValueError: If embeddings have different dimensions
        """
        ...

    def calculate_degradation(
        self,
        embedding_source: npt.NDArray[np.float32],
        embedding_target: npt.NDArray[np.float32],
    ) -> float:
        """
        Calculate information degradation from source to target.

        Degradation is computed as (1 - cosine_similarity), representing
        the proportion of semantic information lost. Values ≤0.05 indicate
        minimal degradation (≥95% information preserved).

        Args:
            embedding_source: Source text embedding (more detailed)
            embedding_target: Target text embedding (potentially less detailed)

        Returns:
            Degradation score in range [0.0, 1.0]
            0.0 = no degradation (identical)
            1.0 = complete degradation (unrelated)

        Raises:
            ValueError: If embeddings have different dimensions
        """
        ...
