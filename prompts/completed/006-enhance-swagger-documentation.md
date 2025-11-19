<objective>
Enhance the Swagger/OpenAPI documentation for the SMT Pipeline service with rich descriptions, comprehensive schemas, and examples.

The service already has Swagger UI configured at /docs, but needs enhanced documentation to make it production-ready with clear endpoint descriptions, request/response examples, and proper validation documentation.

This will make the API self-documenting and easier for developers to use and test.
</objective>

<context>
**Current State:**
- FastAPI service at `src/main.py` with Swagger UI at `/docs`
- API routes in `src/api/routes/pipeline.py`
- Request/response models in `src/api/models.py`
- Pydantic models with validation already defined

**Technology Stack:**
- FastAPI with built-in Swagger UI
- Pydantic models for request/response validation
- OpenAPI 3.0+ specification

**What Needs Enhancement:**
- Endpoint descriptions and examples
- Request/response schema examples
- Parameter descriptions
- Error response documentation
- Operation summaries and tags

**Why This Matters:**
Good API documentation reduces integration time, provides self-service testing through Swagger UI, and serves as living documentation that stays in sync with code.
</context>

<requirements>
**Mandatory Enhancements:**

1. **Enhance API Models in `src/api/models.py`:**
   - Add `Field(description="...")` to all model fields
   - Add `Config.json_schema_extra` with example values
   - Document validation constraints
   - Add clear docstrings to all models

2. **Enhance Route Descriptions in `src/api/routes/pipeline.py`:**
   - Add detailed docstrings to all endpoint functions
   - Include parameter descriptions
   - Document all possible responses (200, 422, 500)
   - Add examples for request bodies
   - Use `tags` for endpoint grouping
   - Add `summary` and `description` to route decorators

3. **Enhance Main App Metadata in `src/main.py`:**
   - Add comprehensive `description` with markdown formatting
   - Add `contact` information
   - Add `license` info
   - Configure custom Swagger UI settings (if needed)

4. **Add Response Models:**
   - Document success responses (200)
   - Document error responses (422, 500)
   - Add examples for each response type

5. **Verify Swagger UI:**
   - Ensure `/docs` endpoint is accessible
   - Verify all endpoints appear in Swagger UI
   - Test example requests through Swagger UI
   - Check that request/response examples are visible

**Documentation Standards:**

For Pydantic Models:
```python
class ProcessRequest(BaseModel):
    """Request model for processing informal text through the pipeline.

    The informal text will be transformed through three steps:
    1. Formalization (≥91% semantic similarity)
    2. SMT-LIB extraction (≤5% information loss)
    3. Solver validation (executable SMT-LIB output)
    """

    informal_text: str = Field(
        ...,
        min_length=1,
        max_length=10000,
        description="Informal natural language text to process. "
                    "Should contain logical constraints or rules. "
                    "Example: 'x must be greater than 5 and less than 10'",
        examples=["x must be greater than 5"]
    )

    class Config:
        json_schema_extra = {
            "examples": [
                {
                    "informal_text": "x must be greater than 5 and y must be even"
                }
            ]
        }
```

For Route Endpoints:
```python
@router.post(
    "/process",
    response_model=ProcessResponse,
    status_code=200,
    summary="Process informal text to SMT-LIB",
    description="""
    Transforms informal natural language into verified SMT-LIB code.

    **Pipeline Steps:**
    1. **Formalization**: Converts informal text to formal representation
    2. **Extraction**: Generates annotated SMT-LIB code
    3. **Validation**: Executes with Z3 solver for verification

    **Quality Gates:**
    - Formalization: ≥91% embedding similarity
    - Extraction: ≤5% information degradation
    - Validation: Must execute without errors

    **Example Request:**
    ```json
    {
      "informal_text": "x must be greater than 5 and less than 10"
    }
    ```
    """,
    responses={
        200: {
            "description": "Successfully processed text",
            "content": {
                "application/json": {
                    "example": {
                        "informal_text": "x > 5",
                        "formal_text": "The variable x must satisfy: x > 5",
                        "smt_lib_code": "(declare-const x Int)\n(assert (> x 5))",
                        "check_sat_result": "sat",
                        "solver_success": True
                    }
                }
            }
        },
        422: {
            "description": "Pipeline processing failed",
            "content": {
                "application/json": {
                    "example": {
                        "detail": "Formalization failed: Could not preserve semantics (similarity: 0.87 < 0.91)"
                    }
                }
            }
        }
    }
)
async def process_informal_text(
    request: ProcessRequest,
    service: PipelineService = Depends(get_pipeline_service)
) -> ProcessResponse:
    """Process informal text through the 3-step semantic-preserving pipeline.

    Args:
        request: Request containing informal natural language text
        service: Injected pipeline service instance

    Returns:
        Verified SMT-LIB output with solver result

    Raises:
        HTTPException: 422 if pipeline processing fails
        HTTPException: 500 if unexpected error occurs
    """
```

**Required Fields to Document:**
- All ProcessRequest fields
- All ProcessResponse fields (informal_text, formal_text, smt_lib_code, etc.)
- All PipelineMetrics fields
- Error response structure
</requirements>

<implementation>
**Step-by-Step Enhancement:**

1. **Review current models:**
   - Read `src/api/models.py`
   - Identify all fields needing descriptions
   - Note existing validation rules

2. **Enhance Pydantic models:**
   - Add Field(description=...) to every field
   - Add examples to Field() where appropriate
   - Add Config.json_schema_extra with full examples
   - Add comprehensive docstrings

3. **Review current routes:**
   - Read `src/api/routes/pipeline.py`
   - Identify all endpoints
   - Note current documentation level

4. **Enhance route endpoints:**
   - Add detailed docstrings
   - Add summary and description to decorators
   - Document all response codes (200, 422, 500)
   - Add request/response examples
   - Add tags for grouping

5. **Enhance main app:**
   - Read `src/main.py`
   - Update FastAPI() constructor with rich description
   - Add contact and license info (optional)
   - Verify docs_url and redoc_url

6. **Test Swagger UI:**
   - Start the service
   - Navigate to http://localhost:8000/docs
   - Verify all endpoints visible
   - Check that descriptions appear
   - Test example requests

**Key Enhancements to Make:**

For ProcessRequest:
- Describe informal_text field with examples
- Document min_length and max_length constraints
- Add 2-3 example requests

For ProcessResponse:
- Describe all fields (informal_text, formal_text, smt_lib_code, etc.)
- Explain what each metric means
- Add example successful response
- Document requires_manual_review flag

For Error Responses:
- Document FormalizationError scenarios
- Document ExtractionError scenarios
- Document ValidationError scenarios
- Provide example error responses

For Endpoints:
- POST /process: Full pipeline processing
- GET /examples: Available test cases
- GET /health: Service health check

**What to Avoid and WHY:**
- ❌ NO overly technical jargon - keep it accessible
- ❌ NO missing examples - examples help developers understand usage
- ❌ NO vague descriptions - be specific about what each field means
- ❌ NO undocumented validation - explain all constraints
</implementation>

<output>
Modify the following files:

**API Models:**
- `./src/api/models.py` - Add Field descriptions, examples, and Config.json_schema_extra

**API Routes:**
- `./src/api/routes/pipeline.py` - Add endpoint descriptions, response documentation, examples

**Main Application:**
- `./src/main.py` - Enhance FastAPI metadata (description, contact, license)

**Optional Documentation:**
- `./docs/API_DOCUMENTATION.md` - Summary of API endpoints and usage (optional)

All enhancements should maintain backward compatibility - only adding documentation, not changing functionality.
</output>

<verification>
Before declaring complete, verify:

1. **Swagger UI accessible:**
   - Start service: `uvicorn src.main:app --reload`
   - Navigate to: http://localhost:8000/docs
   - Verify Swagger UI loads without errors

2. **All endpoints documented:**
   - POST /pipeline/process appears with full description
   - GET /pipeline/examples appears with description
   - GET /health appears with description
   - All endpoints show request/response schemas

3. **Request schemas enhanced:**
   - ProcessRequest shows field descriptions
   - Example values visible in schema
   - Validation constraints documented (min_length, max_length)

4. **Response schemas enhanced:**
   - ProcessResponse shows all fields with descriptions
   - Success response (200) has example
   - Error responses (422, 500) have examples

5. **Examples work:**
   - "Try it out" button functional
   - Example requests can be executed
   - Responses return expected format

6. **Documentation quality:**
   - All descriptions are clear and helpful
   - Technical terms explained
   - Examples are realistic and useful

Test checklist:
```bash
# Start service
uvicorn src.main:app --reload

# Open browser
open http://localhost:8000/docs

# Verify:
# - Swagger UI loads
# - All 3 endpoints visible
# - Descriptions appear for all fields
# - Examples are present
# - "Try it out" works
```
</verification>

<success_criteria>
The Swagger documentation is complete when:

1. ✅ All Pydantic models have Field descriptions
2. ✅ All models have json_schema_extra examples
3. ✅ All endpoints have detailed docstrings
4. ✅ All endpoints have summary and description in decorators
5. ✅ All response codes documented (200, 422, 500)
6. ✅ Request/response examples visible in Swagger UI
7. ✅ Swagger UI accessible at /docs
8. ✅ All endpoints functional through "Try it out"
9. ✅ Documentation is clear, helpful, and accurate
10. ✅ No breaking changes to API functionality

Report back: "Swagger documentation enhanced. X fields documented, Y endpoints enhanced, Z examples added. Accessible at http://localhost:8000/docs"
</success_criteria>
