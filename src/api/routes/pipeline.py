"""Pipeline API routes.

Endpoints for processing informal text through the SMT-LIB pipeline.
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
    summary="Process informal text to verified SMT-LIB output",
    description="""
    Transform informal natural language into verified, executable SMT-LIB code through a semantic-preserving pipeline.

    ## Pipeline Overview

    This endpoint executes a rigorous three-step process with quality gates at each stage:

    ### Step 1: Formalization
    - Converts informal text to formal, structured representation
    - Uses Claude AI with semantic embeddings for verification
    - **Quality Gate**: ≥91% embedding similarity required
    - Automatic retry with increasing temperature if threshold not met
    - Maximum 3 attempts before failure

    ### Step 2: SMT-LIB Extraction
    - Generates annotated SMT-LIB code from formal text
    - Includes variable declarations, assertions, and solver commands
    - **Quality Gate**: ≤5% information degradation allowed
    - Automatic retry with increasing detail level if threshold exceeded
    - Maximum 5 attempts before failure

    ### Step 3: Solver Validation
    - Executes generated code with Z3 SMT solver
    - Validates syntax and logical correctness
    - Captures solver results (sat/unsat/unknown)
    - **Quality Gate**: Must execute without errors
    - Automatic retry with Claude-powered error fixing if needed
    - Maximum 3 attempts before failure

    ## Quality Assurance

    - All outputs meet strict quality thresholds
    - Semantic similarity verified with embeddings
    - Information preservation measured at each step
    - Solver execution confirms syntactic and logical correctness
    - Manual review flagged for edge cases

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
      "metrics": { ... },
      "passed_all_checks": true
    }
    ```

    ## Error Scenarios

    - **422 Unprocessable Entity**: Pipeline processing failed at one of the three steps
    - **500 Internal Server Error**: Unexpected system error (API failures, etc.)
    """,
    responses={
        200: {
            "description": "Successfully processed text through all three pipeline steps",
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
            "description": "Pipeline processing failed at formalization, extraction, or validation step",
            "content": {
                "application/json": {
                    "examples": {
                        "formalization_failure": {
                            "summary": "Formalization failed to meet similarity threshold",
                            "value": {
                                "error": "Formalization failed: Could not achieve required similarity threshold after 3 attempts",
                                "details": {
                                    "step": "formalization",
                                    "attempts": 3,
                                    "final_similarity": 0.89,
                                    "threshold": 0.91,
                                },
                            },
                        },
                        "extraction_failure": {
                            "summary": "Extraction exceeded degradation threshold",
                            "value": {
                                "error": "Extraction failed: Information degradation too high after 5 attempts",
                                "details": {
                                    "step": "extraction",
                                    "attempts": 5,
                                    "final_degradation": 0.08,
                                    "threshold": 0.05,
                                },
                            },
                        },
                        "validation_failure": {
                            "summary": "Solver validation failed with syntax error",
                            "value": {
                                "error": "Validation failed: SMT solver execution error after 3 attempts",
                                "details": {
                                    "step": "validation",
                                    "solver_output": "Parse error at line 3: unexpected token",
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
    """Process informal text through the complete semantic-preserving pipeline.

    Executes all three steps (formalization, extraction, validation) with quality
    verification at each stage. Returns verified SMT-LIB code that has been
    validated by the Z3 solver.

    Args:
        request: ProcessRequest containing informal natural language text
        pipeline_service: Injected PipelineService instance for processing

    Returns:
        ProcessResponse with verified SMT-LIB output, quality metrics, and solver results

    Raises:
        HTTPException: 422 if pipeline processing fails at any step
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


@router.get(
    "/examples",
    response_model=list[dict],
    status_code=200,
    summary="Get example informal texts for testing the pipeline",
    description="""
    Retrieve a curated list of example informal text inputs for testing the pipeline.

    These examples cover various complexity levels and constraint types:
    - Simple numeric constraints
    - Multiple variable relationships
    - Conditional logic
    - Edge cases and boundary conditions

    Each example includes:
    - `text`: The informal text suitable for the /process endpoint
    - `description`: What the example demonstrates
    - `expected_result`: Expected check-sat outcome (sat/unsat)

    Use these examples to:
    - Test the pipeline functionality
    - Understand what inputs work well
    - Learn SMT-LIB constraint patterns
    - Validate API integration

    ## Example Response

    ```json
    [
      {
        "text": "x must be greater than 5 and less than 10",
        "description": "Simple range constraint",
        "expected_result": "sat"
      },
      {
        "text": "x must be greater than 10 and less than 5",
        "description": "Unsatisfiable constraint",
        "expected_result": "unsat"
      }
    ]
    ```
    """,
    responses={
        200: {
            "description": "List of example texts with descriptions and expected outcomes",
            "content": {
                "application/json": {
                    "example": [
                        {
                            "text": "x must be greater than 5 and less than 10",
                            "description": "Simple satisfiable range constraint on integer variable",
                            "expected_result": "sat",
                        },
                        {
                            "text": "x must be greater than 10 and less than 5",
                            "description": "Unsatisfiable constraint (impossible range)",
                            "expected_result": "unsat",
                        },
                        {
                            "text": "the sum of a and b must equal 10",
                            "description": "Arithmetic relationship between two variables",
                            "expected_result": "sat",
                        },
                    ]
                }
            },
        }
    },
    tags=["Pipeline Processing"],
)
async def get_examples() -> list[dict]:
    """Get curated example informal texts for testing the pipeline.

    Provides a collection of test cases covering different constraint types,
    complexity levels, and expected outcomes. Useful for API testing and
    understanding input format requirements.

    Returns:
        List of dictionaries containing example texts, descriptions, and expected results
    """
    from examples.sample_texts import SAMPLE_TEXTS

    return SAMPLE_TEXTS
