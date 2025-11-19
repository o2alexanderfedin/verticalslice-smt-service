"""Domain models for the SMT-LIB pipeline.

All models use Pydantic for validation, serialization, and type safety.
"""

from pydantic import BaseModel, Field, ConfigDict
from typing import Optional
from enum import Enum


# ============================================================================
# Step 1: Formalization Models
# ============================================================================

class FormalizationResult(BaseModel):
    """Result from Step 1: Formalization."""

    formal_text: str = Field(
        description="Formalized version of informal text"
    )
    similarity_score: float = Field(
        ge=0.0,
        le=1.0,
        description="Cosine similarity between informal and formal embeddings"
    )
    attempts: int = Field(
        ge=0,
        le=10,
        description="Number of attempts required to achieve threshold (0 if skipped)"
    )

    model_config = ConfigDict(frozen=True)  # Immutable


# ============================================================================
# Step 2: Extraction Models
# ============================================================================

class ExtractionResult(BaseModel):
    """Result from Step 2: SMT-LIB Extraction."""

    smt_lib_code: str = Field(
        description="Complete annotated SMT-LIB file (code + comments)"
    )
    degradation: float = Field(
        ge=0.0,
        le=1.0,
        description="Information degradation from formal text to SMT-LIB"
    )
    attempts: int = Field(
        ge=1,
        le=10,
        description="Number of attempts required to achieve threshold"
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

    success: bool = Field(
        description="Whether solver executed without errors"
    )
    check_sat_result: str = Field(
        description="Result from (check-sat): sat, unsat, unknown, or error message"
    )
    model: Optional[str] = Field(
        default=None,
        description="Variable assignments from (get-model) if sat"
    )
    unsat_core: Optional[str] = Field(
        default=None,
        description="Minimal unsatisfiable subset from (get-unsat-core) if unsat"
    )
    raw_output: str = Field(
        description="Complete raw output from solver"
    )
    attempts: int = Field(
        ge=1,
        le=10,
        description="Number of attempts required (including error fixes)"
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
        description="Number of attempts required to achieve formalization similarity threshold (0=skipped, 1-10=actual attempts)"
    )
    final_formalization_similarity: float = Field(
        ge=0.0,
        le=1.0,
        description="Final embedding similarity score between informal and formal text (0.0-1.0, threshold: 0.91)"
    )
    formalization_time_seconds: float = Field(
        ge=0.0,
        description="Total time spent on formalization step in seconds"
    )

    # Step 2: Extraction metrics
    extraction_attempts: int = Field(
        ge=1,
        le=10,
        description="Number of attempts required to achieve extraction degradation threshold (1-10)"
    )
    final_extraction_degradation: float = Field(
        ge=0.0,
        le=1.0,
        description="Final information degradation score from formal text to SMT-LIB (0.0-1.0, threshold: 0.05)"
    )
    extraction_time_seconds: float = Field(
        ge=0.0,
        description="Total time spent on SMT-LIB extraction step in seconds"
    )

    # Step 3: Validation metrics
    validation_attempts: int = Field(
        ge=1,
        le=10,
        description="Number of attempts required to achieve successful solver execution (1-10, includes error fixes)"
    )
    solver_execution_time_seconds: float = Field(
        ge=0.0,
        description="Total time spent executing SMT solver in seconds"
    )

    # Overall metrics
    total_time_seconds: float = Field(
        ge=0.0,
        description="Total end-to-end pipeline execution time in seconds"
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
    informal_text: str = Field(
        description="Original informal natural language text"
    )

    # Step 1 output
    formal_text: str = Field(
        description="Formalized version with preserved semantics"
    )
    formalization_similarity: float = Field(
        ge=0.0,
        le=1.0,
        description="Embedding similarity score (≥0.91 required)"
    )

    # Step 2 output
    smt_lib_code: str = Field(
        description="Complete annotated SMT-LIB code (executable)"
    )
    extraction_degradation: float = Field(
        ge=0.0,
        le=1.0,
        description="Information degradation score (≤0.05 required)"
    )

    # Step 3 output
    check_sat_result: str = Field(
        description="Result from SMT solver: sat, unsat, or unknown"
    )
    model: Optional[str] = Field(
        default=None,
        description="Model (variable assignments) if sat"
    )
    unsat_core: Optional[str] = Field(
        default=None,
        description="Unsat core (conflicting constraints) if unsat"
    )
    solver_success: bool = Field(
        description="Whether solver executed successfully"
    )

    # Metrics
    metrics: PipelineMetrics = Field(
        description="Performance and quality metrics"
    )

    # Quality gates
    passed_all_checks: bool = Field(
        description="Whether all quality thresholds were met"
    )
    requires_manual_review: bool = Field(
        description="Whether manual review is recommended"
    )

    model_config = ConfigDict(frozen=False)  # Mutable for building up
