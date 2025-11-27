"""API request/response models.

Separate from domain models to allow different validation rules.
"""

from pydantic import BaseModel, Field

from src.domain.models import PipelineMetrics, VerifiedOutput


class ProcessRequest(BaseModel):
    """Request model for processing informal text through the formal verification pipeline.

    The informal text will be transformed through three rigorous steps:
    1. **Formalization**: Converts informal text to formal representation with semantic preservation
    2. **Symbolic Logic Generation**: Generates verified symbolic representations with accuracy validation
    3. **Formal Verification**: Validates logic with verification engine to ensure correctness

    Each step includes automatic quality verification and intelligent retry mechanisms.
    """

    informal_text: str = Field(
        min_length=1,
        max_length=100000,
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
            "Useful for simple expressions like 'x > 5' that don't need AI processing. "
            "The service automatically skips formalization for very short inputs, "
            "but this flag allows explicit control."
        ),
    )

    enrich: bool = Field(
        default=False,
        description=(
            "Enable web search enrichment before processing. "
            "When enabled, the service will use web search to gather domain-specific "
            "definitions, context, and clarifications before running the main pipeline. "
            "Useful for inputs containing domain-specific terminology or ambiguous references."
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
    """Response model containing complete verified output from the formal verification pipeline.

    This response includes outputs from all three pipeline steps, performance metrics,
    and quality indicators. All outputs have been verified to meet semantic similarity
    and information preservation thresholds.
    """

    # Original input
    informal_text: str = Field(
        description="The original informal natural language text that was processed"
    )

    # Optional enrichment metadata (Step 0)
    enrichment_performed: bool = Field(
        default=False,
        description="Whether web search enrichment was performed on the input",
    )
    enriched_text: str = Field(
        description=(
            "Text after enrichment step. If enrichment was performed (enrich=true), "
            "this contains the input text enhanced with domain knowledge from web searches. "
            "If enrichment was not performed (enrich=false or default), "
            "this equals the original informal_text."
        ),
        examples=[
            "The variable x must be greater than 5 and less than 10. "
            "Background: In mathematics, a variable is a symbol that represents a value in equations."
        ],
    )
    enrichment_search_count: int | None = Field(
        default=None,
        description="Number of web searches performed during enrichment (if enabled)",
    )
    enrichment_sources: list[str] | None = Field(
        default=None,
        description="URLs of sources used for enrichment (if enabled)",
    )
    enrichment_time_seconds: float | None = Field(
        default=None,
        description="Time spent on enrichment in seconds (if enabled)",
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
            "Semantic similarity score between informal and formal text. "
            "Measures how well the original meaning was preserved. "
            "Range: 0.0 (low similarity) to 1.0 (high similarity). "
            "Higher values indicate better semantic preservation."
        ),
        examples=[0.95],
    )

    # Step 2 output: Symbolic Logic Generation
    smt_lib_code: str = Field(
        description=(
            "Complete symbolic logic representation that can be verified by formal verification engine. "
            "Includes variable declarations, assertions, and verification commands. "
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
            "Information preservation score during symbolic logic generation. "
            "Measures how accurately information was transformed. "
            "Range: 0.0 (perfect preservation) to 1.0 (significant loss). "
            "Lower values indicate better information retention."
        ),
        examples=[0.03],
    )

    # Step 3 output: Formal Verification
    check_sat_result: str = Field(
        description=(
            "Result from formal verification engine. "
            "Possible values: 'sat' (satisfiable - solution exists), "
            "'unsat' (unsatisfiable - no solution possible), "
            "'unknown' (engine could not determine), "
            "or an error message if verification failed."
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
            "Whether the formal verification engine executed successfully without errors. "
            "True means verification ran and produced a valid result (sat/unsat/unknown). "
            "False means there were execution errors (syntax errors, timeouts, etc.)."
        ),
        examples=[True],
    )

    # Proof data
    proof: dict | None = Field(
        default=None,
        description=(
            "Verification proof from the formal verification engine. "
            "Contains both raw solver output and human-readable summary. "
            "Enables external verification and auditing of results."
        ),
        examples=[
            {
                "raw_output": "(sat)\n((x 7))",
                "summary": "Verification successful: Found satisfying assignment where x=7",
            }
        ],
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
            "True means all automated quality checks passed successfully. "
            "False means at least one quality threshold was not met."
        ),
        examples=[True],
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
                    "proof": {
                        "raw_output": "(sat)\n((x 7))",
                        "summary": "Verification successful: Found satisfying assignment where x=7",
                    },
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
        # Construct proof dict if raw output is available
        proof: dict | None = None
        if output.proof_raw_output is not None:
            proof = {
                "raw_output": output.proof_raw_output,
                "summary": output.proof_summary or "Verification completed",
            }

        return cls(
            informal_text=output.informal_text,
            enrichment_performed=output.enrichment_performed,
            enriched_text=output.enriched_text,
            enrichment_search_count=output.enrichment_search_count,
            enrichment_sources=output.enrichment_sources,
            enrichment_time_seconds=output.enrichment_time_seconds,
            formal_text=output.formal_text,
            formalization_similarity=output.formalization_similarity,
            smt_lib_code=output.smt_lib_code,
            extraction_degradation=output.extraction_degradation,
            check_sat_result=output.check_sat_result,
            model=output.model,
            unsat_core=output.unsat_core,
            solver_success=output.solver_success,
            proof=proof,
            metrics=output.metrics,
            passed_all_checks=output.passed_all_checks,
        )


class ErrorLocationModel(BaseModel):
    """Location of an error in SMT-LIB code."""

    line_number: int | None = Field(
        default=None,
        description="Line where error occurred (1-indexed)",
    )
    column_number: int | None = Field(
        default=None,
        description="Column where error occurred (1-indexed)",
    )
    error_line: str | None = Field(
        default=None,
        description="The actual line of code with the error",
    )
    context_before: list[str] = Field(
        default_factory=list,
        description="Up to 3 lines of code before the error",
    )
    context_after: list[str] = Field(
        default_factory=list,
        description="Up to 3 lines of code after the error",
    )


class ValidationAttemptModel(BaseModel):
    """Details of a single validation attempt."""

    attempt_number: int = Field(
        description="Attempt number (1-indexed)",
    )
    smt_code: str = Field(
        description="SMT-LIB code that was attempted",
    )
    solver_error: str = Field(
        description="Error message from the solver",
    )
    fix_attempted: str = Field(
        default="",
        description="Fix that was attempted (empty if this was the last attempt)",
    )


class ValidationDiagnostics(BaseModel):
    """Rich diagnostic information for validation errors."""

    informal_text: str = Field(
        description="Original informal constraint from user",
    )
    formal_text: str = Field(
        description="Formalized version of the constraint",
    )
    final_smt_code: str = Field(
        description="Final SMT-LIB code that failed validation",
    )
    final_error: str = Field(
        description="Final error message from solver",
    )
    error_location: ErrorLocationModel | None = Field(
        default=None,
        description="Parsed error location with context (if parseable)",
    )
    attempts: int = Field(
        description="Number of attempts made",
    )
    attempt_history: list[ValidationAttemptModel] = Field(
        default_factory=list,
        description="History of all validation attempts",
    )


class ErrorResponse(BaseModel):
    """Error response model returned when pipeline processing fails.

    Provides detailed information about what went wrong and at which stage,
    helping developers debug issues with their input or understand processing limitations.
    """

    error: str = Field(
        description=(
            "Human-readable error message describing what went wrong. "
            "Includes the pipeline step that failed and the reason for failure."
        ),
        examples=[
            "Formalization failed: Could not achieve required semantic similarity threshold",
            "Symbolic logic generation failed: Information preservation below acceptable threshold",
            "Formal verification failed: Syntax error detected in generated logic",
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
    diagnostics: ValidationDiagnostics | None = Field(
        default=None,
        description=(
            "Rich diagnostic information for validation errors. "
            "Includes original intent, error location, code context, and attempt history. "
            "Only present for validation (Step 3) errors."
        ),
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
                    "error": "Formal verification failed: Syntax error detected in logic",
                    "details": {
                        "step": "validation",
                        "solver_output": "Parse error at line 3: unexpected token ','",
                    },
                    "diagnostics": {
                        "informal_text": "x must be greater than 5",
                        "formal_text": "The variable x must satisfy: x > 5",
                        "final_smt_code": "(declare-const x Int)\n(assert (> x 5))\n(check-sat)",
                        "final_error": "Expected RPAREN_TOK, got `at` (SYMBOL)",
                        "error_location": {
                            "line_number": 2,
                            "column_number": 15,
                            "error_line": "(assert (> x 5))",
                            "context_before": ["(declare-const x Int)"],
                            "context_after": ["(check-sat)"],
                        },
                        "attempts": 3,
                        "attempt_history": [],
                    },
                },
            ]
        }
    }
