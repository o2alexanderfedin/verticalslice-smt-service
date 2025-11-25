"""Pipeline API routes.

Endpoints for processing informal text through formal symbolic verification.
"""

import logging

from fastapi import APIRouter, Depends, HTTPException

from src.api.dependencies import get_pipeline_service
from src.api.models import ErrorResponse, ProcessRequest, ProcessResponse
from src.application.pipeline_service import PipelineService
from src.shared.result import Err, Ok

logger = logging.getLogger(__name__)

router = APIRouter(prefix="/pipeline", tags=["pipeline"])


@router.post(
    "/process",
    response_model=ProcessResponse,
    status_code=200,
    summary="Process informal text to verified formal logic",
    description="""
    Transform informal natural language into verified formal logic through an intelligent quality assurance pipeline.

    ## How It Works

    ```
    ┌─────────────────────────────────────┐
    │     Natural Language Input          │
    │  (Requirements, constraints, rules) │
    └──────────────┬──────────────────────┘
                   │
                   ▼
    ┌──────────────────────────────────────────────────┐
    │                                                   │
    │     AI-Powered Quality Assurance Pipeline        │
    │                                                   │
    │  • Intelligent semantic analysis                 │
    │  • Automated accuracy verification               │
    │  • Multi-stage quality gates                     │
    │                                                   │
    └──────────────┬───────────────────────────────────┘
                   │
                   ▼
    ┌─────────────────────────────────────┐
    │      Verified Formal Logic          │
    │   (Proof + satisfiability result)   │
    └─────────────────────────────────────┘
    ```

    ## Quality Assurance

    - Multiple quality gates throughout the pipeline
    - Accuracy preservation verified at each phase
    - Automated quality checks and validation
    - Comprehensive quality metrics in response

    ## Performance

    - Typical processing time: 3-10 seconds
    - Depends on text complexity and retry attempts
    - Detailed metrics returned in response

    ## Example Request

    ```json
    {
      "informal_text": "x must be greater than 5 and less than 10"
    }
    ```

    ## Example Success Response (200)

    ```json
    {
      "informal_text": "x must be greater than 5 and less than 10",
      "formal_text": "The integer variable x must satisfy: x > 5 AND x < 10",
      "formalization_similarity": 0.95,
      "smt_lib_code": "(declare-const x Int)\\n(assert (> x 5))\\n(assert (< x 10))\\n(check-sat)\\n(get-model)",
      "extraction_degradation": 0.03,
      "check_sat_result": "sat",
      "model": "((x 7))",
      "unsat_core": null,
      "solver_success": true,
      "proof": {
        "raw_output": "(sat)\\n((x 7))",
        "summary": "Verification successful: Found satisfying assignment where x=7"
      },
      "metrics": { ... },
      "passed_all_checks": true
    }
    ```

    ## Error Scenarios

    - **422 Unprocessable Entity**: Pipeline processing failed at one of the three phases
    - **500 Internal Server Error**: Unexpected system error (API failures, etc.)
    """,
    responses={
        200: {
            "description": "Successfully processed text through all three pipeline phases",
            "content": {
                "application/json": {
                    "example": {
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
                    }
                }
            },
        },
        422: {
            "model": ErrorResponse,
            "description": "Pipeline processing failed at formalization, extraction, or validation phase",
            "content": {
                "application/json": {
                    "examples": {
                        "formalization_failure": {
                            "summary": "Formalization failed to meet quality threshold",
                            "value": {
                                "error": "Formalization failed: Could not achieve required semantic similarity threshold",
                                "details": {
                                    "step": "formalization",
                                    "message": "Quality threshold not met after multiple attempts",
                                },
                            },
                        },
                        "extraction_failure": {
                            "summary": "Logic generation failed quality check",
                            "value": {
                                "error": "Logic generation failed: Accuracy preservation below acceptable threshold",
                                "details": {
                                    "step": "extraction",
                                    "message": "Quality threshold not met after refinement attempts",
                                },
                            },
                        },
                        "validation_failure": {
                            "summary": "Formal verification failed",
                            "value": {
                                "error": "Formal verification failed: Syntax error detected in generated logic",
                                "details": {
                                    "step": "validation",
                                    "message": "Verification engine detected syntax error",
                                },
                            },
                        },
                    }
                }
            },
        },
        500: {
            "model": ErrorResponse,
            "description": "Internal server error (API failure, system error, etc.)",
            "content": {
                "application/json": {
                    "example": {
                        "error": "Internal server error during pipeline processing",
                        "details": None,
                    }
                }
            },
        },
    },
    tags=["Pipeline Processing"],
)
async def process_informal_text(
    request: ProcessRequest, pipeline_service: PipelineService = Depends(get_pipeline_service)
) -> ProcessResponse:
    """Process informal text through the complete quality-assured pipeline.

    Executes all three phases (formalization, logic generation, formal verification)
    with quality verification at each stage. Returns verified formal logic that has been
    validated by the formal verification engine.

    Args:
        request: ProcessRequest containing informal natural language text
        pipeline_service: Injected PipelineService instance for processing

    Returns:
        ProcessResponse with verified formal logic, quality metrics, and verification results

    Raises:
        HTTPException: 422 if pipeline processing fails at any phase
        HTTPException: 500 for unexpected system errors
    """
    logger.info(f"Processing request (text_length={len(request.informal_text)})")

    try:
        # Execute pipeline
        result = await pipeline_service.process(
            request.informal_text,
            skip_formalization=request.skip_formalization,
            enrich=request.enrich,
        )

        # Match on Result type
        match result:
            case Ok(output):
                logger.info("Pipeline processing succeeded")
                return ProcessResponse.from_domain(output)

            case Err(error):
                logger.warning(f"Pipeline processing failed: {error}")
                raise HTTPException(status_code=422, detail=str(error))

    except HTTPException:
        # Re-raise HTTP exceptions
        raise

    except Exception as e:
        # Catch unexpected errors
        logger.error(f"Unexpected error during pipeline processing: {e}", exc_info=True)
        raise HTTPException(
            status_code=500, detail="Internal server error during pipeline processing"
        ) from e
