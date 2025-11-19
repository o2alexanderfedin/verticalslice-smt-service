<objective>
Implement the Application Service Layer and API Layer to complete the vertical slice.

The Application layer orchestrates the three-step pipeline by coordinating domain steps. The API layer exposes a FastAPI REST endpoint for external clients. Together they complete the vertical slice from HTTP request to verified SMT-LIB output.

This implementation ties together domain logic and infrastructure to create a working service.
</objective>

<context>
**Architecture Reference:** @docs/architecture/ARCHITECTURE.md

**Project Context:**
- FastAPI for REST API
- Application service orchestrates pipeline steps
- Dependency injection for clean architecture
- Full async/await for non-blocking I/O
- Result types propagate from domain through API

**What These Layers Contain:**
- `PipelineService` - Orchestrates three steps sequentially
- FastAPI application setup with CORS, error handling
- API routes (`POST /pipeline/process`)
- Request/response Pydantic models
- Dependency injection providers
- Error mapping (domain exceptions → HTTP status codes)

**Why This Matters:**
These layers expose the domain logic to the outside world. The service layer coordinates workflow, while the API layer provides the HTTP interface. Both must handle errors gracefully and maintain type safety.
</context>

<requirements>
**Mandatory Implementation Requirements:**

1. **Implement Pipeline Service in `src/application/pipeline_service.py`:**
   - Class: `PipelineService`
   - Constructor accepts:
     - `embedding_provider: EmbeddingProvider`
     - `llm_provider: LLMProvider`
     - `smt_solver: SMTSolver`
     - `config: PipelineConfig`
   - Method: `async def process(informal_text: str) -> Result[VerifiedOutput, PipelineError]`
   - Orchestration logic:
     1. Create FormalizationStep and execute
     2. If Ok, create ExtractionStep and execute
     3. If Ok, create ValidationStep and execute
     4. If Ok, build VerifiedOutput with all metrics
     5. If any Err, propagate the error
   - Must create PipelineMetrics tracking attempts and times
   - Must set `requires_manual_review` flag based on triggers
   - All steps must be awaited (async execution)

2. **Create API models in `src/api/models.py`:**
   - `ProcessRequest(BaseModel)`:
     - `informal_text: str` with validation (min_length=1, max_length=10000)
   - `ProcessResponse(BaseModel)`:
     - All fields from VerifiedOutput
     - Class method: `from_domain(output: VerifiedOutput) -> ProcessResponse`
     - Proper serialization of numpy arrays (if any)
   - `ErrorResponse(BaseModel)`:
     - `error: str`
     - `details: Optional[dict]`

3. **Implement dependencies in `src/api/dependencies.py`:**
   - Function: `get_settings() -> Settings` with `@lru_cache()`
   - Function: `get_embedding_provider() -> SentenceTransformerProvider` with `@lru_cache()`
     - WHY lru_cache: Model is expensive to load, reuse singleton
   - Function: `get_llm_provider() -> AnthropicClient` with `@lru_cache()`
     - WHY lru_cache: Connection pooling, reuse client
   - Function: `get_smt_solver() -> Z3Executor` with `@lru_cache()`
     - WHY lru_cache: Stateless, reuse instance
   - Function: `get_pipeline_service(...) -> PipelineService` (NOT cached)
     - WHY not cached: Lightweight orchestrator, create per-request for clean state
     - Use `Depends()` to inject cached providers

4. **Create pipeline route in `src/api/routes/pipeline.py`:**
   - Router: `APIRouter(prefix="/pipeline", tags=["pipeline"])`
   - Endpoint: `POST /process`
     - Accepts: ProcessRequest
     - Returns: ProcessResponse
     - Status: 200 on success
     - Errors: 422 for pipeline failures, 500 for unexpected errors
   - Implementation:
     1. Extract informal_text from request
     2. Call `await pipeline_service.process(informal_text)`
     3. Match Result:
        - `Ok(output)` → return ProcessResponse.from_domain(output)
        - `Err(error)` → raise HTTPException(422, detail=str(error))
   - Include request validation and error handling

5. **Create main application in `src/main.py`:**
   - FastAPI app creation with metadata (title, version, description)
   - Include CORS middleware (allow origins, methods, headers)
   - Include pipeline router
   - Add health check endpoint: `GET /health` → `{"status": "healthy"}`
   - Add root endpoint: `GET /` → redirect to `/docs`
   - Configure logging
   - Error handlers for common exceptions

6. **Create example/demo in `examples/sample_texts.py`:**
   - At least 3 sample informal texts for testing:
     - Simple constraint (e.g., "x must be greater than 5")
     - Medium complexity (multiple constraints)
     - Complex (nested conditions)
   - Expected behavior for each (sat/unsat prediction)

7. **Create demo endpoint in `src/api/routes/pipeline.py`:**
   - Endpoint: `GET /pipeline/examples`
   - Returns: List of example texts with descriptions
   - Allows users to test service easily

**Type Safety Requirements:**
- All request/response models use Pydantic
- Dependency functions have return type annotations
- Service methods fully typed
- No `Any` types

**Error Handling Requirements:**
- Domain errors (FormalizationError, etc.) → HTTP 422 Unprocessable Entity
- Validation errors → HTTP 422 with details
- Unexpected errors → HTTP 500 with generic message (don't leak internals)
- All errors logged with context
</requirements>

<implementation>
**Step-by-Step Implementation:**

1. **Implement application service:**
   - Create `src/application/pipeline_service.py`
   - Implement PipelineService with sequential orchestration
   - Create EmbeddingDistanceVerifier instance for steps
   - Build PipelineMetrics tracking all attempts and times
   - Check manual review triggers (high retries, close thresholds)

2. **Create API models:**
   - Create `src/api/__init__.py`
   - Create `src/api/models.py`
   - Define ProcessRequest with validation
   - Define ProcessResponse with from_domain converter
   - Define ErrorResponse for structured errors

3. **Set up dependency injection:**
   - Create `src/api/dependencies.py`
   - Implement all provider functions with proper caching
   - Use Settings to configure providers
   - PipelineService should NOT be cached (per-request)

4. **Create routes:**
   - Create `src/api/routes/__init__.py`
   - Create `src/api/routes/pipeline.py`
   - Implement POST /process with full error handling
   - Implement GET /examples for demo
   - Use dependency injection for clean code

5. **Create main application:**
   - Create `src/main.py`
   - Set up FastAPI with metadata
   - Add CORS middleware
   - Include pipeline router
   - Add health and root endpoints
   - Configure exception handlers

6. **Create examples:**
   - Create `examples/__init__.py`
   - Create `examples/sample_texts.py`
   - Add diverse test cases

**Key Implementation Patterns:**

```python
# Pipeline Service Orchestration
async def process(self, informal_text: str) -> Result[VerifiedOutput, PipelineError]:
    start_time = time.time()

    # Step 1: Formalization
    formalization_step = FormalizationStep(
        self.llm_provider,
        self.semantic_verifier,
        self.config
    )
    result = await formalization_step.execute(informal_text)

    match result:
        case Err(error):
            return Err(error)
        case Ok(formalization_result):
            formal_text = formalization_result.formal_text

    # Step 2: Extraction (similar pattern)
    # Step 3: Validation (similar pattern)

    # Build VerifiedOutput with all metrics
    return Ok(VerifiedOutput(...))

# API Endpoint with Result Matching
@router.post("/process", response_model=ProcessResponse)
async def process_informal_text(
    request: ProcessRequest,
    service: PipelineService = Depends(get_pipeline_service)
) -> ProcessResponse:
    result = await service.process(request.informal_text)

    match result:
        case Ok(output):
            return ProcessResponse.from_domain(output)
        case Err(error):
            raise HTTPException(status_code=422, detail=str(error))
```

**What to Avoid and WHY:**
- ❌ NO caching PipelineService - keep it per-request for clean state
- ❌ NO exposing internal errors to API users - wrap in generic messages
- ❌ NO blocking I/O - all service calls must be async
- ❌ NO business logic in API layer - keep it in domain/service
- ❌ NO tight coupling - use dependency injection
</implementation>

<output>
Create the following files:

**Application layer:**
- `./src/application/pipeline_service.py` - PipelineService orchestrator

**API layer:**
- `./src/api/__init__.py`
- `./src/api/models.py` - Request/response models
- `./src/api/dependencies.py` - Dependency injection providers
- `./src/api/routes/__init__.py`
- `./src/api/routes/pipeline.py` - Pipeline endpoints

**Main application:**
- `./src/main.py` - FastAPI application setup

**Examples:**
- `./examples/__init__.py`
- `./examples/sample_texts.py` - Sample informal texts for testing

All files must have docstrings, type annotations, and error handling.
</output>

<verification>
Before declaring complete, verify:

1. **Service orchestration:**
   - PipelineService calls all three steps sequentially
   - Result types properly matched and propagated
   - PipelineMetrics calculated correctly
   - Manual review triggers implemented

2. **API correctness:**
   - POST /process endpoint works
   - Request validation catches invalid input
   - Successful responses return ProcessResponse
   - Errors return proper HTTP status codes (422, 500)
   - GET /examples returns sample data

3. **Dependency injection:**
   - Cached providers reuse instances (@lru_cache)
   - PipelineService not cached (per-request)
   - All dependencies properly typed
   - Settings loaded from environment

4. **Type safety:**
   - Mypy strict mode passes
   - All models use Pydantic
   - No Any types

5. **Error handling:**
   - Domain errors mapped to HTTP 422
   - Unexpected errors mapped to HTTP 500
   - Error details logged but not leaked to users
   - All exceptions caught

Test the service:
```bash
# Start the service
uvicorn src.main:app --reload

# Test health check
curl http://localhost:8000/health

# Test examples endpoint
curl http://localhost:8000/pipeline/examples

# Test process endpoint
curl -X POST http://localhost:8000/pipeline/process \
  -H "Content-Type: application/json" \
  -d '{"informal_text": "x must be greater than 5"}'
```
</verification>

<success_criteria>
The application and API layers are complete when:

1. ✅ PipelineService orchestrates all three steps correctly
2. ✅ API endpoints respond to requests
3. ✅ Dependency injection works (cached and per-request)
4. ✅ Request/response models validate correctly
5. ✅ Error handling maps domain errors to HTTP status codes
6. ✅ Health check and examples endpoints work
7. ✅ FastAPI docs accessible at /docs
8. ✅ Service can be started with uvicorn
9. ✅ Sample texts provided for testing
10. ✅ Mypy strict mode passes

Report back: "Application and API layers complete, service running on port 8000, X sample texts available for testing."
</success_criteria>
