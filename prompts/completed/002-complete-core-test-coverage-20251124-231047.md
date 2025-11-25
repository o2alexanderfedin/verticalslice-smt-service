<objective>
Complete test coverage for core business logic modules (Domain, Application, Infrastructure, API layers) to reach 85%+ overall coverage. Build on the existing test infrastructure already in place from the previous work that achieved 9% coverage with shared utilities fully tested.
</objective>

<context>
**Current State:**
- Coverage: 9% (976/1077 statements uncovered)
- Target: 85%+ coverage
- Gap: 76 percentage points
- Existing: 70 passing tests, excellent test infrastructure in place
- Test execution: <3 seconds (excellent)

**What's Already Done (100% coverage):**
- ✅ Shared utilities (result, config, retry)
- ✅ Embedding verifier
- ✅ Test infrastructure and fixtures in conftest.py
- ✅ Comprehensive mocking patterns established

**Project Structure:**
- FastAPI-based SMT-LIB verification pipeline
- Uses pytest with pytest-asyncio, pytest-cov
- All tests in tests/unit/ with mirror structure to src/

Review @CLAUDE.md for project conventions.
</context>

<requirements>
1. **Prioritize by impact**: Focus on modules with highest statement counts first
2. **Use existing infrastructure**: Leverage mock fixtures already created in tests/unit/conftest.py
3. **Follow established patterns**: Match the style and structure of existing test files
4. **Fast execution**: Maintain <5 second total test execution time
5. **Comprehensive coverage**: Test happy paths, error cases, edge cases, boundary conditions
6. **Mock all external dependencies**: No API calls, no real models, no external services
7. **Type safety**: Full type hints in all test code
8. **SOLID compliance**: Refactor production code if needed for testability (minimal changes only)
</requirements>

<implementation>
Create tests in this priority order (highest impact first):

**Priority 1: Domain Steps (~17% coverage gain)**

**tests/unit/domain/test_formalization_step.py** (61 statements)
Critical formalization logic with LLM and semantic verification.

Test scenarios:
- Skip logic for short inputs (< 200 chars should skip, return input as-is with similarity=1.0, attempts=0)
- Force skip flag (skip_formalization=True should skip regardless of length)
- Successful formalization on first attempt (similarity ≥ 0.91)
- Retry loop with improving similarity scores
- Max retries exhausted (return best result)
- Source embedding computation failure
- LLM provider exceptions during formalization
- Embedding provider exceptions during verification
- Similarity calculation with various threshold values
- Temperature progression (if applicable)
- Previous attempt refinement logic

Mock dependencies:
- LLMProvider.formalize() → return formal text
- EmbeddingProvider.embed() → return numpy array
- SemanticVerifier.calculate_similarity() → return float

**tests/unit/domain/test_extraction_step.py** (58 statements)
SMT-LIB code extraction with degradation checks.

Test scenarios:
- Successful extraction on first attempt
- Retry loop with degradation checks
- Max degradation threshold validation
- Max retries exhausted
- LLM provider exceptions
- Embedding provider exceptions
- Detail level progression across retries
- Skip retries for very short formal texts
- Invalid SMT-LIB syntax handling (caught in validation, not here)
- Empty or malformed LLM responses

Mock dependencies:
- LLMProvider.extract() → return SMT-LIB code string
- EmbeddingProvider.embed() → return numpy array
- SemanticVerifier.calculate_degradation() → return float

**tests/unit/domain/test_validation_step.py** (57 statements)
SMT solver validation with retry logic.

Test scenarios:
- Successful validation (sat result with model)
- Successful validation (unsat result with core)
- Unknown result handling
- Timeout result handling
- Syntax error in SMT code (solver returns error)
- Retry loop for fixable errors
- Max retries exhausted
- Solver execution exceptions
- Empty SMT code input
- Missing check-sat command
- Raw output capture and formatting

Mock dependencies:
- SMTSolver.execute() → return dict with success, check_sat_result, model, etc.

**Priority 2: Application Layer (~9% coverage gain)**

**tests/unit/application/test_pipeline_service.py** (94 statements)
End-to-end pipeline orchestration.

Test scenarios:
- Complete successful pipeline flow (formalization → extraction → validation)
- Skip formalization flag behavior
- Enrich flag behavior (if implemented)
- Error in formalization step (propagates to caller)
- Error in extraction step (propagates to caller)
- Error in validation step (propagates to caller)
- Metrics collection (timing, attempts, scores)
- Result type handling (Ok/Err propagation)
- Configuration injection (thresholds, retries)

Mock dependencies:
- FormalizationStep.execute() → return Ok(FormalizationResult)
- ExtractionStep.execute() → return Ok(ExtractionResult)
- ValidationStep.execute() → return Ok(ValidationResult)
- EnrichmentStep (if used)

**Priority 3: Infrastructure Layer (~22% coverage gain)**

**tests/unit/infrastructure/test_llm_client.py** (98 statements)
Anthropic API client with comprehensive error handling.

Test scenarios:
- Successful formalization call
- Successful extraction call
- HTTP 429 rate limit (should retry)
- HTTP 500 server error (should retry)
- HTTP 401 authentication error (should fail immediately)
- Network timeout (should retry)
- Invalid JSON response
- Empty response from API
- Retry exhaustion (all retries failed)
- Message streaming (if used)
- Token counting and limits

Mock dependencies:
- httpx.AsyncClient.post() → return mocked Response object
- Response.json() → return dict with content
- Response.raise_for_status() → raise or pass

**tests/unit/infrastructure/test_sentence_transformer.py** (27 statements)
Embedding generation with model caching.

Test scenarios:
- First embedding generation (model load)
- Cached model reuse (subsequent calls)
- Embedding dimension validation
- Empty string input
- Very long text input
- Model loading failure
- Inference failure
- Normalization of embeddings

Mock dependencies:
- transformers.AutoModel.from_pretrained() → return mock model
- transformers.AutoTokenizer.from_pretrained() → return mock tokenizer
- model() → return mock output with last_hidden_state
- torch.mean() → return mock tensor

**tests/unit/infrastructure/test_cvc5_executor.py** (expand existing - currently 21 tests)
Additional scenarios beyond existing tests:
- Edge cases in model extraction
- Edge cases in unsat core extraction
- More complex timeout scenarios (without hanging test)
- Multiple solver interactions
- Memory limits
- Large constraint sets

**Priority 4: API Layer (~4% coverage gain)**

**tests/unit/api/test_pipeline_routes.py** (25 statements)
FastAPI endpoint testing.

Test scenarios:
- Successful POST /pipeline/process request
- Request validation (ProcessRequest model)
- Response formatting (ProcessResponse model)
- 422 error when pipeline processing fails
- 500 error for unexpected exceptions
- Request body validation (missing fields, wrong types)
- Large input text handling

Mock dependencies:
- PipelineService.process() → return Ok(PipelineOutput) or Err(error)
- Use FastAPI TestClient for endpoint testing

**tests/unit/api/test_dependencies.py** (21 statements)
Dependency injection testing.

Test scenarios:
- get_pipeline_service returns properly configured service
- Service has correct dependencies injected
- Settings loaded correctly
- LLM client initialized
- Embedding provider initialized
- Steps initialized with correct configuration

Mock dependencies:
- Settings (can use real Settings with test values)
</implementation>

<mocking_patterns>
**Domain Steps Mocking:**
```python
@pytest.fixture
def mock_formalization_step(mocker):
    step = mocker.AsyncMock(spec=FormalizationStep)
    step.execute.return_value = Ok(FormalizationResult(
        formal_text="Formal version",
        similarity_score=0.95,
        attempts=1
    ))
    return step
```

**LLM Client Mocking:**
```python
@pytest.fixture
def mock_httpx_response(mocker):
    response = mocker.Mock()
    response.json.return_value = {
        "content": [{"text": "LLM response"}],
        "usage": {"input_tokens": 100, "output_tokens": 50}
    }
    response.status_code = 200
    return response

@pytest.fixture
def mock_httpx_client(mocker, mock_httpx_response):
    client = mocker.AsyncMock()
    client.post.return_value = mock_httpx_response
    return client
```

**FastAPI Testing:**
```python
from fastapi.testclient import TestClient

def test_process_endpoint_success(mock_pipeline_service):
    # Mock the dependency
    app.dependency_overrides[get_pipeline_service] = lambda: mock_pipeline_service

    client = TestClient(app)
    response = client.post("/pipeline/process", json={"informal_text": "test"})

    assert response.status_code == 200
```
</mocking_patterns>

<verification>
After each module's tests are created, run:

```bash
# Run new tests only
pytest tests/unit/domain/test_formalization_step.py -v
pytest tests/unit/domain/test_extraction_step.py -v
pytest tests/unit/domain/test_validation_step.py -v
pytest tests/unit/application/test_pipeline_service.py -v
pytest tests/unit/infrastructure/test_llm_client.py -v
pytest tests/unit/infrastructure/test_sentence_transformer.py -v
pytest tests/unit/api/test_pipeline_routes.py -v
pytest tests/unit/api/test_dependencies.py -v

# Check overall coverage
pytest tests/unit/ --cov=src --cov-report=term-missing --cov-report=html

# Verify performance
pytest tests/unit/ -v  # Should complete in <5 seconds
```

**Success Criteria:**
- Coverage ≥85% overall
- All tests pass
- Execution time <5 seconds
- No external API calls
- No code duplication
</verification>

<success_criteria>
✅ Overall coverage reaches 85%+
✅ All new tests pass consistently
✅ Total test suite completes in <5 seconds
✅ Zero external API calls during tests
✅ Domain steps have >90% coverage each
✅ Application layer has >90% coverage
✅ Infrastructure layer has >80% coverage
✅ API layer has >90% coverage
✅ HTML coverage report generated in htmlcov/
✅ All tests properly isolated and can run independently
✅ Type hints maintained throughout
✅ Following existing test patterns and conventions
✅ No regression in existing test coverage
</success_criteria>

<constraints>
**NEVER:**
- Make real API calls to Anthropic
- Load actual HuggingFace models
- Break existing functionality
- Create integration tests (unit tests only)
- Skip critical error paths
- Over-engineer solutions

**ALWAYS:**
- Use AsyncMock for async dependencies
- Use existing fixtures from conftest.py
- Follow existing test patterns
- Test both Ok and Err result paths
- Include clear docstrings
- Maintain type safety
- Keep tests fast (<5 seconds total)
</constraints>

<output>
Create these test files:
1. tests/unit/domain/test_formalization_step.py
2. tests/unit/domain/test_extraction_step.py
3. tests/unit/domain/test_validation_step.py
4. tests/unit/application/test_pipeline_service.py
5. tests/unit/infrastructure/test_llm_client.py
6. tests/unit/infrastructure/test_sentence_transformer.py
7. tests/unit/api/test_pipeline_routes.py
8. tests/unit/api/test_dependencies.py

Each file should:
- Have comprehensive docstrings
- Use pytest fixtures for setup
- Group tests in classes
- Follow test_[function]_[scenario]_[expected_result] naming
- Test all code paths (happy, error, edge cases)
</output>
