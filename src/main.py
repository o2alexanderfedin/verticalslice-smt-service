"""Main FastAPI application.

Entry point for the SMT-LIB pipeline service.
"""

import logging

from fastapi import FastAPI
from fastapi.middleware.cors import CORSMiddleware
from fastapi.responses import RedirectResponse

from src.api.dependencies import get_settings
from src.api.routes import pipeline
from src.shared.logging_config import configure_logging

# Configure logging
settings = get_settings()
configure_logging(settings.log_level)

logger = logging.getLogger(__name__)

# Create FastAPI application with enhanced metadata
app = FastAPI(
    title=settings.api_title,
    version=settings.api_version,
    description="""
# Semantic-Preserving SMT-LIB Pipeline Service

Transform informal natural language into verified, executable SMT-LIB code through a rigorous semantic-preserving pipeline.

## Overview

This service provides a production-grade API for converting informal logical constraints into formal SMT-LIB code that can be executed by SMT solvers. It ensures semantic preservation through multiple quality gates and automatic error correction.

## Pipeline Architecture

The service implements a three-step pipeline with quality verification at each stage:

### 1. Formalization (≥91% Semantic Similarity)
- Converts informal text to formal representation using Claude AI
- Verifies semantic preservation with embedding similarity
- Automatic retry with increasing temperature
- Maximum 3 attempts

### 2. SMT-LIB Extraction (≤5% Information Loss)
- Generates annotated SMT-LIB code from formal text
- Measures information degradation with embedding comparison
- Automatic retry with increasing detail level
- Maximum 5 attempts

### 3. Solver Validation (Error-Free Execution)
- Executes code with Z3 SMT solver
- Validates syntax and logical correctness
- Claude-powered automatic error fixing
- Maximum 3 attempts

## Key Features

- **Semantic Verification**: Embedding-based similarity measurement at each step
- **Quality Gates**: Strict thresholds ensure output quality
- **Automatic Retry**: Intelligent retry mechanisms with adaptive parameters
- **Error Recovery**: AI-powered error fixing for solver failures
- **Comprehensive Metrics**: Detailed performance and quality metrics
- **Manual Review Flags**: Identifies outputs requiring human validation

## Quality Guarantees

- **Formalization Similarity**: ≥91% embedding similarity
- **Information Preservation**: ≤5% degradation allowed
- **Solver Validation**: Must execute without errors
- **End-to-End Testing**: All outputs verified with Z3 solver

## Technology Stack

- **API Framework**: FastAPI (async, high performance)
- **AI Model**: Claude Sonnet 4.5 (Anthropic)
- **Embeddings**: Sentence Transformers (all-MiniLM-L6-v2)
- **SMT Solver**: Z3 (Microsoft Research)
- **Language**: Python 3.12+ with type hints

## Use Cases

- Formal verification of requirements
- Automated constraint generation
- Natural language to logic transformation
- SMT solver integration
- Formal methods tooling

## Documentation

- **Swagger UI**: Interactive API documentation and testing
- **ReDoc**: Alternative documentation view
- **Examples**: Curated test cases at `/pipeline/examples`
- **Health Check**: Service status at `/health`

## Support

For issues, questions, or feature requests, please refer to the project repository.
    """,
    docs_url="/docs",
    redoc_url="/redoc",
    contact={
        "name": "SMT Pipeline Team",
        "email": "support@example.com",
    },
    license_info={
        "name": "MIT License",
        "url": "https://opensource.org/licenses/MIT",
    },
    openapi_tags=[
        {
            "name": "Pipeline Processing",
            "description": "Core pipeline endpoints for processing informal text to SMT-LIB code",
        },
        {"name": "Health & Status", "description": "Service health check and status endpoints"},
    ],
)

# Configure CORS
# Note: allow_credentials=False is required when using allow_origins=["*"]
# This enables maximum compatibility for cross-domain requests
app.add_middleware(
    CORSMiddleware,
    allow_origins=settings.cors_allowed_origins,
    allow_credentials=False,
    allow_methods=["*"],
    allow_headers=["*"],
)

# Include routers
app.include_router(pipeline.router)


@app.get("/", include_in_schema=False)
async def root():
    """Redirect root to API documentation."""
    return RedirectResponse(url="/docs")


@app.get(
    "/health",
    status_code=200,
    summary="Service health check",
    description="""
    Check the health and status of the SMT Pipeline service.

    Returns basic service information including:
    - **status**: Current service health (healthy/degraded/unhealthy)
    - **service**: Service name
    - **version**: Current API version
    - **model**: AI model being used (Claude version)
    - **embedding_model**: Embedding model for semantic comparison

    Use this endpoint for:
    - Service monitoring and alerting
    - Load balancer health checks
    - Deployment verification
    - Status page integration

    ## Example Response

    ```json
    {
      "status": "healthy",
      "service": "Semantic-Preserving SMT-LIB Pipeline",
      "version": "0.1.0",
      "model": "claude-sonnet-4-5-20250929",
      "embedding_model": "sentence-transformers/all-MiniLM-L6-v2"
    }
    ```
    """,
    responses={
        200: {
            "description": "Service is healthy and operational",
            "content": {
                "application/json": {
                    "example": {
                        "status": "healthy",
                        "service": "Semantic-Preserving SMT-LIB Pipeline",
                        "version": "0.1.0",
                        "model": "claude-sonnet-4-5-20250929",
                        "embedding_model": "sentence-transformers/all-MiniLM-L6-v2",
                    }
                }
            },
        }
    },
    tags=["Health & Status"],
)
async def health_check():
    """Service health check endpoint.

    Provides current service status and configuration information.
    Used for monitoring, health checks, and deployment verification.

    Returns:
        Dictionary containing service health status and metadata
    """
    return {
        "status": "healthy",
        "service": settings.api_title,
        "version": settings.api_version,
        "model": settings.anthropic_model,
        "embedding_model": settings.embedding_model_name,
    }


@app.on_event("startup")
async def startup_event():
    """Application startup event handler.

    Validates critical configuration and fails fast if issues are detected.
    """
    logger.info(f"Starting {settings.api_title} v{settings.api_version}")

    # CRITICAL: Validate required configuration
    errors: list[str] = []

    # Check Anthropic API key
    if not settings.anthropic_api_key or settings.anthropic_api_key.strip() == "":
        errors.append("ANTHROPIC_API_KEY is not set or empty")
    elif not settings.anthropic_api_key.startswith("sk-"):
        errors.append(
            f"ANTHROPIC_API_KEY appears invalid (should start with 'sk-', got '{settings.anthropic_api_key[:10]}...')"
        )

    # Check model configuration
    if not settings.anthropic_model:
        errors.append("ANTHROPIC_MODEL is not set")

    # Check embedding model
    if not settings.embedding_model_name:
        errors.append("EMBEDDING_MODEL_NAME is not set")

    if errors:
        error_msg = "CRITICAL CONFIGURATION ERRORS:\n" + "\n".join(f"  - {e}" for e in errors)
        logger.critical(error_msg)
        raise RuntimeError(error_msg)

    logger.info(f"Using Anthropic model: {settings.anthropic_model}")
    logger.info(f"Using embedding model: {settings.embedding_model_name}")
    logger.info("Configuration validation passed - all critical settings are present")


@app.on_event("shutdown")
async def shutdown_event():
    """Application shutdown event handler."""
    logger.info(f"Shutting down {settings.api_title}")


if __name__ == "__main__":
    import uvicorn

    uvicorn.run(
        "src.main:app", host="0.0.0.0", port=8000, reload=True, log_level=settings.log_level.lower()
    )
