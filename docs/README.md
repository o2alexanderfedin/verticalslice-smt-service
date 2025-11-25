# API Documentation

## OpenAPI Specification

This service uses **FastAPI**, which automatically generates the OpenAPI specification from the code at runtime.

### Accessing the Spec

- **Interactive Swagger UI**: `https://your-domain.com/docs`
- **ReDoc**: `https://your-domain.com/redoc`
- **Raw JSON spec**: `https://your-domain.com/openapi.json`

### Why No Committed openapi.json?

We **do not commit** `openapi.json` to the repository because:

1. **Single Source of Truth**: The code is the source of truth
2. **No Drift**: Spec is always in sync with code
3. **Auto-Generated**: FastAPI generates it from type hints and docstrings
4. **Always Current**: Every deploy has the latest spec

### Exporting the Spec

If you need to export the spec (for external documentation or API client generation):

```bash
# Export from local dev server
./scripts/export-openapi.sh

# Export from production
./scripts/export-openapi.sh https://your-domain.com/openapi.json

# Custom output path
./scripts/export-openapi.sh http://localhost:8000/openapi.json custom-path.json
```

### Updating API Documentation

To update the API documentation:

1. Update the code (route handlers, models, docstrings)
2. FastAPI automatically updates the spec
3. No manual spec file updates needed

**Example:**

```python
@router.post(
    "/endpoint",
    summary="Short description",  # Shows in UI
    description="Detailed markdown docs",  # Shows in expanded view
    response_model=MyResponse,  # Auto-generates schema
)
async def my_endpoint(request: MyRequest):
    """This docstring also appears in docs."""
    ...
```

### Best Practices

- ✅ Use type hints on all endpoints
- ✅ Define Pydantic models for request/response
- ✅ Write clear docstrings and descriptions
- ✅ Use `summary` and `description` parameters
- ✅ Include examples in Pydantic models
- ❌ Never commit `openapi.json` to git
- ❌ Never manually edit OpenAPI spec
