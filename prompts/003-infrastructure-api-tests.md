<objective>
Complete test coverage for Infrastructure and API layers to push overall coverage from 42% to 73%+. Focus on LLM client, embedding provider, and FastAPI endpoints with comprehensive mocking of external dependencies.
</objective>

<context>
**Current State:**
- Coverage: 42% (449/1077 statements)
- Target for this prompt: 73%+ (gain of ~31 percentage points)
- Existing: 113 passing tests, <3 seconds execution

**What's Already Complete:**
- ✅ Domain steps: 98% coverage (formalization, extraction, validation)
- ✅ Application pipeline: 82% coverage
- ✅ Shared utilities: 90-100% coverage
- ✅ Test infrastructure fully established

**What Needs Testing:**
- ❌ Infrastructure: LLM Client (98 statements), Sentence Transformer (27 statements)
- ❌ API: Routes (25 statements), Dependencies (21 statements)
- Total: ~171 statements = ~16% coverage gain + additional coverage from existing modules

Review @CLAUDE.md for conventions.
</context>

<requirements>
1. **Mock all external services**: Anthropic API, HuggingFace models, torch operations
2. **Use existing fixtures**: Leverage tests/unit/conftest.py patterns
3. **Fast execution**: Maintain <5 second total test time
4. **Comprehensive scenarios**: HTTP errors, retries, timeouts, edge cases
5. **Type safety**: Full type hints throughout
6. **Follow patterns**: Match existing test structure and style
</requirements>

<implementation>
Create tests in this order:

**Priority 1: Infrastructure - LLM Client (98 statements, ~9% gain)**

**tests/unit/infrastructure/test_llm_client.py**

The AnthropicLLMClient is critical infrastructure. Test all scenarios:

**Formalization Tests:**
- Successful formalization with valid response
- Response with multiple content blocks (take first text)
- Empty content array (error handling)
- Missing 'text' field in content (error handling)
- Previous attempt refinement (include previous_attempt in prompt)
- Previous similarity score in refinement context

**Extraction Tests:**
- Successful extraction with valid SMT-LIB code
- Code with markdown fences (should be preserved, validation strips them)
- Empty or whitespace-only response
- Missing content in response
- Previous attempt with degradation context

**HTTP Error Handling:**
- 429 Rate Limit → should retry with exponential backoff
- 500 Server Error → should retry
- 503 Service Unavailable → should retry
- 401 Authentication → should fail immediately (don't retry)
- 400 Bad Request → should fail immediately
- Network timeout (httpx.TimeoutException) → should retry
- Connection error (httpx.ConnectError) → should retry

**Retry Logic:**
- Successful retry after transient failure
- Max retries exhausted (all attempts fail)
- Exponential backoff timing (verify delays)

**Request Formatting:**
- API key in Authorization header
- Model selection (haiku-3.5)
- Max tokens configuration
- Temperature settings
- System prompt construction
- Message structure

Mock patterns:
```python
@pytest.fixture
def mock_httpx_client(mocker):
    client = mocker.AsyncMock(spec=httpx.AsyncClient)
    response = mocker.Mock()
    response.json.return_value = {
        "content": [{"type": "text", "text": "LLM response"}],
        "usage": {"input_tokens": 100, "output_tokens": 50}
    }
    response.status_code = 200
    client.post.return_value = response
    return client
```

**Priority 2: Infrastructure - Sentence Transformer (27 statements, ~2.5% gain)**

**tests/unit/infrastructure/test_sentence_transformer.py**

Embedding generation with model caching and torch operations.

Test scenarios:
- First call loads model and tokenizer
- Subsequent calls reuse cached model (verify model not loaded again)
- Mean pooling of token embeddings
- Normalization of embeddings (L2 norm)
- Empty string input (should handle gracefully)
- Very long text (>512 tokens, should truncate)
- Embedding dimension verification (384 for MiniLM-L6-v2)
- Model loading failure (transformers.AutoModel.from_pretrained fails)
- Tokenization failure
- Inference failure (model() raises exception)

Mock patterns:
```python
@pytest.fixture
def mock_transformers(mocker):
    # Mock model
    mock_model = mocker.Mock()
    mock_output = mocker.Mock()
    mock_output.last_hidden_state = torch.randn(1, 10, 384)  # batch, seq, dim
    mock_model.return_value = mock_output

    # Mock tokenizer
    mock_tokenizer = mocker.Mock()
    mock_tokenizer.return_value = {
        "input_ids": torch.tensor([[1, 2, 3]]),
        "attention_mask": torch.tensor([[1, 1, 1]])
    }

    # Patch AutoModel and AutoTokenizer
    mocker.patch("transformers.AutoModel.from_pretrained", return_value=mock_model)
    mocker.patch("transformers.AutoTokenizer.from_pretrained", return_value=mock_tokenizer)

    return mock_model, mock_tokenizer
```

**Priority 3: API Layer - Routes (25 statements, ~2.3% gain)**

**tests/unit/api/test_pipeline_routes.py**

FastAPI endpoint testing with TestClient.

Test scenarios:
- Successful POST /pipeline/process with complete response
- Request validation (ProcessRequest model validation)
- Missing informal_text field (422 validation error)
- Empty informal_text (should be allowed)
- Very long informal_text (100K chars from recent increase)
- skip_formalization flag = true
- skip_formalization flag = false
- enrich flag = true
- enrich flag = false
- Pipeline returns Ok(output) → 200 response
- Pipeline returns Err(error) → 422 response with error details
- Unexpected exception in pipeline → 500 response
- Response model validation (ProcessResponse fields)
- Metrics in response
- Proof field in response

Mock patterns:
```python
from fastapi.testclient import TestClient
from src.main import app

@pytest.fixture
def mock_pipeline_service(mocker):
    service = mocker.AsyncMock()
    service.process.return_value = Ok(PipelineOutput(...))
    return service

def test_process_endpoint_success(mock_pipeline_service, mocker):
    # Override dependency
    mocker.patch("src.api.dependencies.get_pipeline_service", return_value=mock_pipeline_service)

    client = TestClient(app)
    response = client.post("/pipeline/process", json={"informal_text": "test input"})

    assert response.status_code == 200
    assert "formal_text" in response.json()
```

**Priority 4: API Layer - Dependencies (21 statements, ~2% gain)**

**tests/unit/api/test_dependencies.py**

Dependency injection initialization testing.

Test scenarios:
- get_pipeline_service returns PipelineService instance
- Service has all required dependencies (steps, providers)
- FormalizationStep initialized with correct config
- ExtractionStep initialized with correct config
- ValidationStep initialized with correct config
- LLM client initialized with API key from settings
- Embedding provider initialized with correct model
- Settings loaded from environment
- Threshold values applied from settings
- Retry counts applied from settings

**Priority 5: Expand CVC5 Executor Tests**

**Enhance tests/unit/test_cvc5_executor.py** (currently 21 tests, expand to ~30)

Additional scenarios:
- Very large constraints (test performance)
- Multiple check-sat calls
- Incremental solver usage
- Model value extraction for different types (Int, Real, Bool)
- Unsat core extraction edge cases
- Empty model (sat but no variables to extract)
- Partial models (some values undefined)
</implementation>

<verification>
After creating each test file, verify:

```bash
# Test each module individually
pytest tests/unit/infrastructure/test_llm_client.py -v
pytest tests/unit/infrastructure/test_sentence_transformer.py -v
pytest tests/unit/api/test_pipeline_routes.py -v
pytest tests/unit/api/test_dependencies.py -v

# Check overall coverage
pytest tests/unit/ --cov=src --cov-report=term-missing --cov-report=html

# Verify all tests pass and performance
pytest tests/unit/ -v  # Should complete in <5 seconds
```

Expected results:
- LLM Client: 90%+ coverage
- Sentence Transformer: 90%+ coverage
- API Routes: 95%+ coverage
- API Dependencies: 90%+ coverage
- Overall: 73%+ coverage
</verification>

<success_criteria>
✅ Overall coverage reaches 73%+
✅ Infrastructure layer: >85% coverage
✅ API layer: >90% coverage
✅ All tests pass consistently
✅ Test suite completes in <5 seconds
✅ Zero external API calls
✅ No regression in existing coverage
✅ HTML coverage report generated
✅ All mocks properly configured
✅ Type safety maintained
</success_criteria>

<constraints>
**NEVER:**
- Make real Anthropic API calls
- Load actual HuggingFace models
- Make real torch operations (mock torch)
- Break existing tests
- Skip error scenarios

**ALWAYS:**
- Mock httpx.AsyncClient for API calls
- Mock transformers for model loading
- Mock torch for tensor operations
- Test both success and failure paths
- Include comprehensive error scenarios
- Use AsyncMock for async methods
- Follow existing test patterns
</constraints>

<output>
Create/enhance these test files:
1. tests/unit/infrastructure/test_llm_client.py (~30 tests)
2. tests/unit/infrastructure/test_sentence_transformer.py (~12 tests)
3. tests/unit/api/test_pipeline_routes.py (~15 tests)
4. tests/unit/api/test_dependencies.py (~8 tests)
5. Expand tests/unit/test_cvc5_executor.py (+9 tests)

Total new tests: ~74
Expected final test count: ~187 tests
Expected coverage: 73-75%
</output>
