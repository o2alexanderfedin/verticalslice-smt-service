# SMT Pipeline API - Quick Reference

## Base URL
```
http://localhost:8000
```

## Endpoints

### 1. Process Informal Text
Transform informal text to verified SMT-LIB code.

**Endpoint:** `POST /pipeline/process`

**Request:**
```json
{
  "informal_text": "x must be greater than 5 and less than 10"
}
```

**Success Response (200):**
```json
{
  "informal_text": "x must be greater than 5 and less than 10",
  "formal_text": "The integer variable x must satisfy: x > 5 AND x < 10",
  "formalization_similarity": 0.95,
  "smt_lib_code": "(declare-const x Int)\n(assert (> x 5))\n(assert (< x 10))\n(check-sat)\n(get-model)",
  "extraction_degradation": 0.03,
  "check_sat_result": "sat",
  "model": "((x 7))",
  "unsat_core": null,
  "solver_success": true,
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
    "success": true
  },
  "passed_all_checks": true,
  "requires_manual_review": false
}
```

**Error Response (422):**
```json
{
  "error": "Formalization failed: Could not achieve required similarity threshold after 3 attempts",
  "details": {
    "step": "formalization",
    "attempts": 3,
    "final_similarity": 0.89,
    "threshold": 0.91
  }
}
```

**cURL Example:**
```bash
curl -X POST "http://localhost:8000/pipeline/process" \
  -H "Content-Type: application/json" \
  -d '{"informal_text": "x must be greater than 5 and less than 10"}'
```

---

### 2. Get Examples
Retrieve curated test examples.

**Endpoint:** `GET /pipeline/examples`

**Response (200):**
```json
[
  {
    "text": "x must be greater than 5 and less than 10",
    "description": "Simple satisfiable range constraint",
    "expected_result": "sat"
  },
  {
    "text": "x must be greater than 10 and less than 5",
    "description": "Unsatisfiable constraint (impossible range)",
    "expected_result": "unsat"
  }
]
```

**cURL Example:**
```bash
curl "http://localhost:8000/pipeline/examples"
```

---

### 3. Health Check
Check service status and configuration.

**Endpoint:** `GET /health`

**Response (200):**
```json
{
  "status": "healthy",
  "service": "Semantic-Preserving SMT-LIB Pipeline",
  "version": "0.1.0",
  "model": "claude-sonnet-4-5-20250929",
  "embedding_model": "sentence-transformers/all-MiniLM-L6-v2"
}
```

**cURL Example:**
```bash
curl "http://localhost:8000/health"
```

---

## Quality Thresholds

| Metric | Threshold | Meaning |
|--------|-----------|---------|
| Formalization Similarity | ≥ 0.91 | Embedding similarity between informal and formal text |
| Extraction Degradation | ≤ 0.05 | Information loss from formal text to SMT-LIB |
| Solver Execution | Must succeed | Z3 solver must execute without errors |

## Response Fields Explained

### ProcessResponse Fields

| Field | Type | Description |
|-------|------|-------------|
| `informal_text` | string | Original input text |
| `formal_text` | string | Formalized version with preserved semantics |
| `formalization_similarity` | float | Similarity score (0.0-1.0) |
| `smt_lib_code` | string | Executable SMT-LIB code |
| `extraction_degradation` | float | Information loss (0.0-1.0) |
| `check_sat_result` | string | sat/unsat/unknown |
| `model` | string\|null | Variable assignments if sat |
| `unsat_core` | string\|null | Conflicting constraints if unsat |
| `solver_success` | boolean | Solver executed successfully |
| `metrics` | object | Performance metrics |
| `passed_all_checks` | boolean | All quality gates passed |
| `requires_manual_review` | boolean | Human review recommended |

### PipelineMetrics Fields

| Field | Type | Description |
|-------|------|-------------|
| `formalization_attempts` | int | Attempts for formalization (1-10) |
| `final_formalization_similarity` | float | Final similarity score |
| `formalization_time_seconds` | float | Time spent on formalization |
| `extraction_attempts` | int | Attempts for extraction (1-10) |
| `final_extraction_degradation` | float | Final degradation score |
| `extraction_time_seconds` | float | Time spent on extraction |
| `validation_attempts` | int | Attempts for validation (1-10) |
| `solver_execution_time_seconds` | float | Time spent on solver |
| `total_time_seconds` | float | Total pipeline time |
| `success` | boolean | Pipeline completed successfully |

## Error Codes

| Code | Meaning | Common Causes |
|------|---------|---------------|
| 200 | Success | All steps completed successfully |
| 422 | Unprocessable Entity | Failed quality threshold, solver error |
| 500 | Internal Server Error | API failure, system error |

## Error Scenarios

### Formalization Failure
```json
{
  "error": "Formalization failed: Could not achieve required similarity threshold after 3 attempts",
  "details": {
    "step": "formalization",
    "attempts": 3,
    "final_similarity": 0.89,
    "threshold": 0.91
  }
}
```

### Extraction Failure
```json
{
  "error": "Extraction failed: Information degradation too high after 5 attempts",
  "details": {
    "step": "extraction",
    "attempts": 5,
    "final_degradation": 0.08,
    "threshold": 0.05
  }
}
```

### Validation Failure
```json
{
  "error": "Validation failed: SMT solver execution error after 3 attempts",
  "details": {
    "step": "validation",
    "solver_output": "Parse error at line 3: unexpected token"
  }
}
```

## Performance Expectations

| Metric | Typical Value |
|--------|---------------|
| Total Processing Time | 3-10 seconds |
| Formalization Time | 1-3 seconds |
| Extraction Time | 1-4 seconds |
| Validation Time | 0.1-1 second |
| Success Rate | 85-95% (depends on input complexity) |

## Input Guidelines

### Good Input Examples
✅ "x must be greater than 5"
✅ "the sum of a and b equals 10"
✅ "if x is positive then y must be negative"
✅ "all elements in the array must be unique"

### Input to Avoid
❌ Ambiguous constraints: "x should be big"
❌ Non-logical statements: "the sky is blue"
❌ Incomplete constraints: "x must be"
❌ Very long text (>10,000 characters)

## Documentation

- **Swagger UI**: http://localhost:8000/docs
- **ReDoc**: http://localhost:8000/redoc
- **OpenAPI Schema**: `openapi.json`

## Python Client Example

```python
import httpx

async def process_text(informal_text: str):
    async with httpx.AsyncClient() as client:
        response = await client.post(
            "http://localhost:8000/pipeline/process",
            json={"informal_text": informal_text}
        )
        response.raise_for_status()
        return response.json()

# Usage
result = await process_text("x must be greater than 5 and less than 10")
print(f"SMT-LIB Code:\n{result['smt_lib_code']}")
print(f"Solver Result: {result['check_sat_result']}")
print(f"Model: {result['model']}")
```

## JavaScript/TypeScript Client Example

```typescript
async function processText(informalText: string) {
  const response = await fetch('http://localhost:8000/pipeline/process', {
    method: 'POST',
    headers: {
      'Content-Type': 'application/json',
    },
    body: JSON.stringify({ informal_text: informalText }),
  });

  if (!response.ok) {
    const error = await response.json();
    throw new Error(error.error);
  }

  return await response.json();
}

// Usage
const result = await processText('x must be greater than 5 and less than 10');
console.log('SMT-LIB Code:', result.smt_lib_code);
console.log('Solver Result:', result.check_sat_result);
console.log('Model:', result.model);
```

## Support

For detailed documentation, visit the interactive Swagger UI at `/docs`.
