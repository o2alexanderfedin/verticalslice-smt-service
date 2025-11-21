"""Domain models for the SMT-LIB pipeline.

All models use Pydantic for validation, serialization, and type safety.
"""

from enum import Enum

from pydantic import BaseModel, ConfigDict, Field

# ============================================================================
# Step 0: Enrichment Models (Optional)
# ============================================================================


class EnrichmentResult(BaseModel):
    """Result from optional Step 0: Web Search Enrichment."""

    enriched_text: str = Field(description="Text enriched with domain context from web searches")
    original_text: str = Field(description="Original input text before enrichment")
    search_count: int = Field(ge=0, le=20, description="Number of web searches performed")
    sources_used: list[str] = Field(
        default_factory=list, description="URLs of sources used for enrichment"
    )
    enrichment_time_seconds: float = Field(
        ge=0.0, description="Time spent on enrichment in seconds"
    )

    model_config = ConfigDict(frozen=True)


# ============================================================================
# Step 1: Formalization Models
# ============================================================================


class FormalizationResult(BaseModel):
    """Result from Step 1: Formalization."""

    formal_text: str = Field(description="Formalized version of informal text")
    similarity_score: float = Field(
        ge=0.0, le=1.0, description="Cosine similarity between informal and formal embeddings"
    )
    attempts: int = Field(
        ge=0, le=10, description="Number of attempts required to achieve threshold (0 if skipped)"
    )

    model_config = ConfigDict(frozen=True)  # Immutable


# ============================================================================
# Step 2: Extraction Models
# ============================================================================


class ExtractionResult(BaseModel):
    """Result from Step 2: SMT-LIB Extraction."""

    smt_lib_code: str = Field(description="Complete annotated SMT-LIB file (code + comments)")
    degradation: float = Field(
        ge=0.0, le=1.0, description="Information degradation from formal text to SMT-LIB"
    )
    attempts: int = Field(
        ge=1, le=10, description="Number of attempts required to achieve threshold"
    )

    model_config = ConfigDict(frozen=True)


# ============================================================================
# Step 3: Validation Models
# ============================================================================


class CheckSatResult(str, Enum):
    """Possible check-sat results from SMT solver."""

    SAT = "sat"
    UNSAT = "unsat"
    UNKNOWN = "unknown"


class SolverResult(BaseModel):
    """Result from Step 3: SMT Solver Validation."""

    success: bool = Field(description="Whether solver executed without errors")
    check_sat_result: str = Field(
        description="Result from (check-sat): sat, unsat, unknown, or error message"
    )
    model: str | None = Field(
        default=None, description="Variable assignments from (get-model) if sat"
    )
    unsat_core: str | None = Field(
        default=None, description="Minimal unsatisfiable subset from (get-unsat-core) if unsat"
    )
    raw_output: str = Field(description="Complete raw output from solver")
    attempts: int = Field(
        ge=1, le=10, description="Number of attempts required (including error fixes)"
    )

    model_config = ConfigDict(frozen=True)


# ============================================================================
# Pipeline Metrics
# ============================================================================


class PipelineMetrics(BaseModel):
    """Performance and quality metrics for the entire pipeline."""

    # Step 1: Formalization metrics
    formalization_attempts: int = Field(
        ge=0,
        le=10,
        description="Number of attempts required to achieve formalization similarity threshold (0=skipped, 1-10=actual attempts)",
    )
    final_formalization_similarity: float = Field(
        ge=0.0,
        le=1.0,
        description="Final embedding similarity score between informal and formal text (0.0-1.0, threshold: 0.91)",
    )
    formalization_time_seconds: float = Field(
        ge=0.0, description="Total time spent on formalization step in seconds"
    )

    # Step 2: Extraction metrics
    extraction_attempts: int = Field(
        ge=1,
        le=10,
        description="Number of attempts required to achieve extraction degradation threshold (1-10)",
    )
    final_extraction_degradation: float = Field(
        ge=0.0,
        le=1.0,
        description="Final information degradation score from formal text to SMT-LIB (0.0-1.0, threshold: 0.05)",
    )
    extraction_time_seconds: float = Field(
        ge=0.0, description="Total time spent on SMT-LIB extraction step in seconds"
    )

    # Step 3: Validation metrics
    validation_attempts: int = Field(
        ge=1,
        le=10,
        description="Number of attempts required to achieve successful solver execution (1-10, includes error fixes)",
    )
    solver_execution_time_seconds: float = Field(
        ge=0.0, description="Total time spent executing SMT solver in seconds"
    )

    # Overall metrics
    total_time_seconds: float = Field(
        ge=0.0, description="Total end-to-end pipeline execution time in seconds"
    )
    success: bool = Field(
        description="Whether the entire pipeline completed successfully (all steps passed)"
    )

    model_config = ConfigDict(frozen=True)


# ============================================================================
# Final Output
# ============================================================================


class VerifiedOutput(BaseModel):
    """Complete verified output from the pipeline."""

    # Original input
    informal_text: str = Field(description="Original informal natural language text")

    # Optional enrichment output (Step 0)
    enrichment_performed: bool = Field(
        default=False, description="Whether web search enrichment was performed"
    )
    enrichment_search_count: int | None = Field(
        default=None, description="Number of web searches performed during enrichment"
    )
    enrichment_sources: list[str] | None = Field(
        default=None, description="URLs of sources used for enrichment"
    )
    enrichment_time_seconds: float | None = Field(
        default=None, description="Time spent on enrichment in seconds"
    )

    # Step 1 output
    formal_text: str = Field(description="Formalized version with preserved semantics")
    formalization_similarity: float = Field(
        ge=0.0, le=1.0, description="Embedding similarity score (≥0.91 required)"
    )

    # Step 2 output
    smt_lib_code: str = Field(description="Complete annotated SMT-LIB code (executable)")
    extraction_degradation: float = Field(
        ge=0.0, le=1.0, description="Information degradation score (≤0.05 required)"
    )

    # Step 3 output
    check_sat_result: str = Field(description="Result from SMT solver: sat, unsat, or unknown")
    model: str | None = Field(default=None, description="Model (variable assignments) if sat")
    unsat_core: str | None = Field(
        default=None, description="Unsat core (conflicting constraints) if unsat"
    )
    solver_success: bool = Field(description="Whether solver executed successfully")

    # Metrics
    metrics: PipelineMetrics = Field(description="Performance and quality metrics")

    # Quality gates
    passed_all_checks: bool = Field(description="Whether all quality thresholds were met")

    model_config = ConfigDict(frozen=False)  # Mutable for building up
