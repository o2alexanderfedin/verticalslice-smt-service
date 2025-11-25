<objective>
Fix 17 failing unit tests in the infrastructure and API test layers created by prompt 003. All failures are due to test implementation bugs (incorrect mocking, wrong API usage), not production code issues. Current coverage: 72% (201 passing, 17 failing tests).
</objective>

<context>
Prompt 003 successfully created comprehensive infrastructure and API tests, achieving 72% coverage (up from 42%). However, 17 tests have implementation bugs that need fixing:

**Test Failure Categories:**
1. **test_dependencies.py** (2 failures): Accessing private attributes `._embedding_provider` instead of public `.embedding_provider`
2. **test_llm_client.py** (6 failures): Incorrect Anthropic exception initialization - missing required `response` and `body` parameters for APIStatusError/APIError
3. **test_sentence_transformer.py** (11 failures): Mocking not working correctly - real SentenceTransformer model being loaded instead of using mocks

**Note**: One test in `test_cvc5_executor.py::test_timeout_short` hangs indefinitely and should be skipped with xfail marker (already documented in that file).

Review @CLAUDE.md for testing conventions.
</context>

<requirements>
1. **Fix test_dependencies.py failures** (2 tests):
   - Change `._embedding_provider` to `.embedding_provider` (and similar for other private attributes)
   - PipelineService uses public properties, not private attributes

2. **Fix test_llm_client.py failures** (6 tests):
   - Correct Anthropic exception initialization
   - `APIStatusError` requires `message`, `response`, and `body` keyword arguments
   - `APIError` requires `message` and `request` positional arguments
   - Create mock response and request objects as needed
   - Example pattern:
     ```python
     mock_response = Mock(status_code=429)
     raise APIStatusError(message="Rate limited", response=mock_response, body={})
     ```

3. **Fix test_sentence_transformer.py failures** (11 tests):
   - Mocks are not being applied correctly - real model is loading
   - Fix mock patching to intercept SentenceTransformer initialization
   - Ensure mocks are patched in the correct module path
   - Mock should be: `"src.infrastructure.embeddings.sentence_transformer.SentenceTransformer"`
   - Verify mock.encode is being called, not real model
   - Fix embedding dimension assertion (mocked value vs real value mismatch)

4. **Preserve working tests**:
   - DO NOT modify any passing tests (201 tests currently passing)
   - Only fix the 17 failing tests
   - Maintain existing test structure and patterns

5. **Verification**:
   - All 218 tests should pass (excluding xfailed test_timeout_short)
   - Coverage should remain at 72%+
   - Test execution time should stay under 60 seconds
</requirements>

<implementation>
Fix tests in this order:

**Step 1: Fix test_dependencies.py**
File: `tests/unit/api/test_dependencies.py`

Find and fix these 2 tests:
- `test_pipeline_service_has_all_dependencies`
- `test_pipeline_service_uses_singleton_dependencies`

Change all assertions from private attributes (._attribute) to public properties (.attribute):
- `._embedding_provider` → `.embedding_provider`
- `._llm_provider` → `.llm_provider`
- `._smt_solver` → `.smt_solver`
- `._settings` → `.settings`

**Step 2: Fix test_llm_client.py**
File: `tests/unit/infrastructure/test_llm_client.py`

Find and fix these 6 tests by correcting exception initialization:
- `test_formalize_retries_on_rate_limit_429`
- `test_formalize_retries_on_500_server_error`
- `test_formalize_fails_immediately_on_auth_error`
- `test_formalize_fails_on_max_retries_exhausted`
- `test_extract_retries_on_api_error`
- `test_enrich_retries_on_api_error`

For APIStatusError, use this pattern:
```python
from anthropic import APIStatusError
mock_response = Mock()
mock_response.status_code = 429  # or appropriate status
raise APIStatusError(
    message="Error message here",
    response=mock_response,
    body={}
)
```

For APIError, use this pattern:
```python
from anthropic import APIError
import httpx
mock_request = httpx.Request("POST", "https://api.anthropic.com/v1/messages")
raise APIError(message="Error message", request=mock_request)
```

**Step 3: Fix test_sentence_transformer.py**
File: `tests/unit/infrastructure/test_sentence_transformer.py`

Find and fix these 11 tests by correcting mock patching:
- `test_initialization_loads_model`
- `test_initialization_with_custom_model_name`
- `test_model_loaded_once_during_init`
- `test_embed_generates_embedding`
- `test_embed_normalizes_embeddings`
- `test_embed_with_empty_string`
- `test_initialization_handles_model_loading_failure`
- `test_embedding_dimension_matches_model`
- `test_multiple_embeds_reuse_model`

Issues to fix:
1. **Mock path must be exact**: `"src.infrastructure.embeddings.sentence_transformer.SentenceTransformer"`
2. **Mock must be applied before import/instantiation**
3. **For tests checking model loading**: Mock the class, not the instance
4. **For tests checking encode calls**: Ensure mock.encode is set up correctly
5. **For dimension tests**: Mock `get_sentence_embedding_dimension()` to return expected value (e.g., 768) and verify against that same value

Pattern for fixtures:
```python
@pytest.fixture
def mock_sentence_transformer(mocker):
    """Mock SentenceTransformer class."""
    mock_class = mocker.Mock()
    mock_instance = mocker.Mock()
    mock_instance.encode.return_value = np.random.rand(384).astype(np.float32)
    mock_instance.get_sentence_embedding_dimension.return_value = 384
    mock_class.return_value = mock_instance

    mocker.patch(
        "src.infrastructure.embeddings.sentence_transformer.SentenceTransformer",
        return_value=mock_instance
    )
    return mock_instance
```

**Step 4: Verify all fixes**
Run tests to confirm:
```bash
pytest tests/unit/ --deselect=tests/unit/test_cvc5_executor.py::TestCvc5ExecutorTimeout::test_timeout_short -v
```

Expected: 218 passed, 1 deselected, coverage 72%+
</implementation>

<output>
Modify these existing files:
- `./tests/unit/api/test_dependencies.py` - Fix 2 tests (private → public attributes)
- `./tests/unit/infrastructure/test_llm_client.py` - Fix 6 tests (exception initialization)
- `./tests/unit/infrastructure/test_sentence_transformer.py` - Fix 11 tests (mock patching)

DO NOT create new files.
DO NOT modify passing tests.
</output>

<verification>
Before declaring complete, verify:

1. Run full test suite (excluding hanging test):
   ```bash
   pytest tests/unit/ --deselect=tests/unit/test_cvc5_executor.py::TestCvc5ExecutorTimeout::test_timeout_short -v --tb=short
   ```

2. Confirm results:
   - ✓ 218 tests pass
   - ✓ 1 test deselected (xfailed timeout test)
   - ✓ 0 failures
   - ✓ Coverage 72%+
   - ✓ Execution time < 60 seconds

3. Verify coverage report:
   ```bash
   pytest tests/unit/ --cov=src --cov-report=term-missing --deselect=tests/unit/test_cvc5_executor.py::TestCvc5ExecutorTimeout::test_timeout_short
   ```

4. Check that no passing tests were broken:
   - API routes: 22 tests passing
   - Application pipeline: 9 tests passing
   - Domain steps: 34 tests passing
   - Shared utilities: 70 tests passing
   - CVC5 executor: 29 tests passing (excluding xfailed)
</verification>

<success_criteria>
✅ All 17 failing tests now pass
✅ Total: 218 passing tests, 1 deselected
✅ Coverage remains at 72%+
✅ Test execution time < 60 seconds
✅ No regression in previously passing tests
✅ All tests use proper mocking (no real API calls or model loading)
</success_criteria>

<constraints>
**NEVER:**
- Modify production code (only fix test files)
- Change test logic or assertions (only fix mocking/API usage bugs)
- Remove or skip failing tests (fix them properly)
- Break passing tests
- Load real models or make real API calls in tests

**ALWAYS:**
- Use exact mock paths for patching
- Include all required parameters for exceptions
- Verify mocks are working before asserting
- Test changes incrementally (run tests after each fix)
- Preserve existing test structure and patterns
</constraints>
