"""API request/response models.

Separate from domain models to allow different validation rules.
"""

from pydantic import BaseModel, Field

from src.domain.models import PipelineMetrics, VerifiedOutput


class ProcessRequest(BaseModel):
    """Request model for processing informal text through the semantic-preserving pipeline.

    The informal text will be transformed through three rigorous steps:
    1. **Formalization**: Converts informal text to formal representation (≥91% semantic similarity required)
    2. **SMT-LIB Extraction**: Generates annotated SMT-LIB code (≤5% information loss allowed)
    3. **Solver Validation**: Executes with Z3 solver to verify correctness (must produce valid output)

    Each step includes automatic retry mechanisms with increasing temperature/detail
    to ensure quality thresholds are met.
    """

    informal_text: str = Field(
        min_length=1,
        max_length=10000,
        description=(
            "Informal natural language text containing logical constraints or rules to process. "
            "Should describe conditions, relationships, or requirements that can be formalized. "
            "Examples: 'x must be greater than 5', 'the sum of a and b equals 10', "
            "'all employees must have a valid ID number'"
        ),
        examples=[
            "x must be greater than 5 and less than 10",
            "the sum of a and b must equal 10",
            "if x is even then y must be odd",
        ],
    )

    skip_formalization: bool = Field(
        default=False,
        description=(
            "Skip formalization step and treat input as already formal. "
            "Useful for simple expressions like 'x > 5' that don't need LLM processing. "
            "The service automatically skips formalization for very short inputs, "
            "but this flag allows explicit control."
        ),
    )

    model_config = {
        "json_schema_extra": {
            "examples": [
                {"informal_text": "x must be greater than 5 and less than 10"},
                {"informal_text": "the sum of a and b must equal 10"},
                {"informal_text": "if x is positive then y must be negative"},
                {"informal_text": "x > 5", "skip_formalization": True},
            ]
        }
    }


class ProcessResponse(BaseModel):
    """Response model containing complete verified output from the semantic-preserving pipeline.

    This response includes outputs from all three pipeline steps, performance metrics,
    and quality indicators. All outputs have been verified to meet semantic similarity
    and information preservation thresholds.
    """

    # Original input
    informal_text: str = Field(
        description="The original informal natural language text that was processed"
    )

    # Step 1 output: Formalization
    formal_text: str = Field(
        description=(
            "Formalized version of the informal text with preserved semantics. "
            "This text maintains the same meaning but uses more precise, structured language "
            "suitable for further processing."
        ),
        examples=["The integer variable x must satisfy the constraint: x > 5 AND x < 10"],
    )
    formalization_similarity: float = Field(
        ge=0.0,
        le=1.0,
        description=(
            "Cosine similarity score between informal and formal text embeddings. "
            "Measures semantic preservation. "
            "Threshold: ≥0.91 required for acceptance. "
            "Range: 0.0 (completely different) to 1.0 (semantically identical)."
        ),
        examples=[0.95],
    )

    # Step 2 output: SMT-LIB Extraction
    smt_lib_code: str = Field(
        description=(
            "Complete annotated SMT-LIB code that can be executed by Z3 solver. "
            "Includes variable declarations, assertions, and solver commands. "
            "Contains inline comments explaining the formalization."
        ),
        examples=[
            "(declare-const x Int)\n(assert (> x 5))\n(assert (< x 10))\n(check-sat)\n(get-model)"
        ],
    )
    extraction_degradation: float = Field(
        ge=0.0,
        le=1.0,
        description=(
            "Information degradation score from formal text to SMT-LIB code. "
            "Measures information loss during extraction. "
            "Threshold: ≤0.05 required for acceptance. "
            "Range: 0.0 (no information lost) to 1.0 (complete information loss)."
        ),
        examples=[0.03],
    )

    # Step 3 output: Solver Validation
    check_sat_result: str = Field(
        description=(
            "Result from SMT solver's (check-sat) command. "
            "Possible values: 'sat' (satisfiable - solution exists), "
            "'unsat' (unsatisfiable - no solution possible), "
            "'unknown' (solver could not determine), "
            "or an error message if execution failed."
        ),
        examples=["sat"],
    )
    model: str | None = Field(
        default=None,
        description=(
            "Model (variable assignments) from solver if check-sat returned 'sat'. "
            "Shows concrete values that satisfy all constraints. "
            "Example: '((x 7))' means x=7 satisfies the constraints. "
            "None if result was 'unsat' or 'unknown'."
        ),
        examples=["((x 7))"],
    )
    unsat_core: str | None = Field(
        default=None,
        description=(
            "Minimal unsatisfiable core from solver if check-sat returned 'unsat'. "
            "Identifies the conflicting subset of constraints. "
            "Useful for debugging why no solution exists. "
            "None if result was 'sat' or 'unknown'."
        ),
        examples=None,
    )
    solver_success: bool = Field(
        description=(
            "Whether the SMT solver executed successfully without errors. "
            "True means the solver ran and produced a valid result (sat/unsat/unknown). "
            "False means there were execution errors (syntax errors, timeouts, etc.)."
        ),
        examples=[True],
    )

    # Metrics
    metrics: PipelineMetrics = Field(
        description=(
            "Detailed performance and quality metrics for all three pipeline steps. "
            "Includes attempt counts, execution times, and quality scores. "
            "Useful for monitoring pipeline performance and identifying bottlenecks."
        )
    )

    # Quality gates
    passed_all_checks: bool = Field(
        description=(
            "Whether all quality thresholds were met across all three steps. "
            "True means: formalization_similarity ≥ 0.91, extraction_degradation ≤ 0.05, "
            "and solver executed successfully. "
            "False means at least one threshold was not met (though processing may have continued)."
        ),
        examples=[True],
    )
    requires_manual_review: bool = Field(
        description=(
            "Whether this output should be manually reviewed by a human. "
            "Triggered when: quality scores are close to thresholds, "
            "multiple retry attempts were needed, or other risk indicators are present. "
            "True does not mean the output is incorrect, just that extra caution is advised."
        ),
        examples=[False],
    )

    model_config = {
        "json_schema_extra": {
            "examples": [
                {
                    "informal_text": "x must be greater than 5 and less than 10",
                    "formal_text": "The integer variable x must satisfy the following constraints: x is greater than 5 AND x is less than 10",
                    "formalization_similarity": 0.95,
                    "smt_lib_code": "; Formalization: The integer variable x must satisfy: x > 5 AND x < 10\n(declare-const x Int)\n(assert (> x 5))\n(assert (< x 10))\n(check-sat)\n(get-model)",
                    "extraction_degradation": 0.03,
                    "check_sat_result": "sat",
                    "model": "((x 7))",
                    "unsat_core": None,
                    "solver_success": True,
                    "metrics": {
                        "formalization_attempts": 1,
                        "final_formalization_similarity": 0.95,
                        "formalization_time_seconds": 1.2,
                        "extraction_attempts": 1,
                        "final_extraction_degradation": 0.03,
                        "extraction_time_seconds": 1.5,
                        "validation_attempts": 1,
                        "solver_execution_time_seconds": 0.3,
                        "total_time_seconds": 3.0,
                        "success": True,
                    },
                    "passed_all_checks": True,
                    "requires_manual_review": False,
                }
            ]
        }
    }

    @classmethod
    def from_domain(cls, output: VerifiedOutput) -> "ProcessResponse":
        """Convert domain model to API response.

        Args:
            output: Domain VerifiedOutput model

        Returns:
            API ProcessResponse model
        """
        return cls(
            informal_text=output.informal_text,
            formal_text=output.formal_text,
            formalization_similarity=output.formalization_similarity,
            smt_lib_code=output.smt_lib_code,
            extraction_degradation=output.extraction_degradation,
            check_sat_result=output.check_sat_result,
            model=output.model,
            unsat_core=output.unsat_core,
            solver_success=output.solver_success,
            metrics=output.metrics,
            passed_all_checks=output.passed_all_checks,
            requires_manual_review=output.requires_manual_review,
        )


class ErrorResponse(BaseModel):
    """Error response model returned when pipeline processing fails.

    Provides detailed information about what went wrong and at which stage,
    helping developers debug issues with their input or understand processing limitations.
    """

    error: str = Field(
        description=(
            "Human-readable error message describing what went wrong. "
            "Includes the pipeline step that failed (formalization/extraction/validation) "
            "and the specific reason for failure."
        ),
        examples=[
            "Formalization failed: Could not achieve required similarity threshold (0.89 < 0.91)",
            "Extraction failed: Information degradation too high (0.08 > 0.05)",
            "Validation failed: SMT solver execution error - syntax error on line 3",
        ],
    )
    details: dict | None = Field(
        default=None,
        description=(
            "Additional structured error details for debugging. "
            "May include: attempt counts, quality scores, solver output, or other diagnostic information. "
            "Not always present - only included when relevant context is available."
        ),
        examples=[
            {"step": "formalization", "attempts": 3, "final_similarity": 0.89, "threshold": 0.91}
        ],
    )

    model_config = {
        "json_schema_extra": {
            "examples": [
                {
                    "error": "Formalization failed: Could not achieve required similarity threshold after 3 attempts",
                    "details": {
                        "step": "formalization",
                        "attempts": 3,
                        "final_similarity": 0.89,
                        "threshold": 0.91,
                    },
                },
                {
                    "error": "Validation failed: SMT solver syntax error",
                    "details": {
                        "step": "validation",
                        "solver_output": "Parse error at line 3: unexpected token ','",
                    },
                },
            ]
        }
    }
