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
# Intelligent Formal Verification Service

Transform natural language requirements into verified formal logic through an AI-powered quality assurance pipeline.

## Overview

This service provides a production-grade API for converting informal logical constraints and business rules into formally verified representations. It ensures accuracy through multiple quality gates and automatic error correction.

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

## Key Features

- **Accuracy Preservation**: Advanced AI ensures meaning is maintained throughout transformation
- **Quality Assurance**: Multiple quality gates verify output accuracy
- **Intelligent Automation**: Automatic retry and error correction mechanisms
- **High Reliability**: Production-tested pipeline with comprehensive validation
- **Detailed Metrics**: Complete visibility into processing quality and performance

## Use Cases

- Formal verification of business requirements
- Automated constraint validation
- Requirements analysis and verification
- Business rule transformation
- Compliance and regulatory verification

## Documentation

- **Swagger UI**: Interactive API documentation and testing
- **ReDoc**: Alternative documentation view
- **Health Check**: Service status at `/health`

## Support

For issues, questions, or feature requests, please refer to the project repository.
    """,
    docs_url="/docs",
    redoc_url="/redoc",
    contact={
        "name": "Formal Verification Team",
        "email": "support@example.com",
    },
    license_info={
        "name": "CC BY-NC-ND 4.0",
        "url": "https://creativecommons.org/licenses/by-nc-nd/4.0/",
    },
    openapi_tags=[
        {
            "name": "Pipeline Processing",
            "description": "Core pipeline endpoints for processing informal text to verified symbolic logic",
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
    Check the health and status of the Formal Verification service.

    Returns basic service information including:
    - **status**: Current service health (healthy/degraded/unhealthy)
    - **service**: Service name
    - **version**: Current API version

    Use this endpoint for:
    - Service monitoring and alerting
    - Load balancer health checks
    - Deployment verification
    - Status page integration

    ## Example Response

    ```json
    {
      "status": "healthy",
      "service": "Formal Symbolic Verification",
      "version": "0.1.0"
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
                        "service": "Intelligent Formal Verification",
                        "version": "0.1.0",
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

    # Check embedding model
    if not settings.embedding_model_name:
        errors.append("EMBEDDING_MODEL_NAME is not set")

    if errors:
        error_msg = "CRITICAL CONFIGURATION ERRORS:\n" + "\n".join(f"  - {e}" for e in errors)
        logger.critical(error_msg)
        raise RuntimeError(error_msg)

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
