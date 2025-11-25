<objective>
Improve test coverage from the current 8% (981/1070 uncovered statements) to 85%+ by creating comprehensive unit tests across the entire codebase. Refactor production code as needed to make it more testable while adhering to SOLID, KISS, DRY, YAGNI, and TRIZ principles. This ensures code quality, catches regressions early, and maintains confidence during refactoring and feature development. High test coverage is critical for this SMT verification pipeline where correctness is paramount.
</objective>

<context>
This is a FastAPI-based SMT-LIB verification pipeline service with the following architecture:
- **API Layer**: FastAPI routes handling HTTP requests (src/api/)
- **Application Layer**: PipelineService orchestrating the workflow (src/application/)
- **Domain Layer**: Business logic for formalization, extraction, enrichment, validation (src/domain/)
- **Infrastructure Layer**: External integrations (LLM, embeddings, SMT solvers) (src/infrastructure/)
- **Shared**: Configuration, logging, result types, utilities (src/shared/)

Current state:
- **Current coverage**: 8% overall (21 tests, only cvc5_executor.py at 86%)
- **Test framework**: pytest with pytest-asyncio, pytest-cov
- **Test location**: tests/unit/ directory
- **Bug discovered**: test_timeout_short in tests/unit/test_cvc5_executor.py:284 hangs indefinitely with 0.001s timeout

Review the project structure by examining @CLAUDE.md for conventions and @pyproject.toml for dependencies.
</context>

<requirements>
1. **Fix the hanging test first**: Debug and repair test_timeout_short (line 284 in test_cvc5_executor.py) that hangs when testing 0.001s timeout
2. **Achieve 85%+ coverage** across the entire codebase through systematic unit testing
3. **Unit tests only**: All tests must use mocked dependencies, no external API calls (Anthropic), no real database, no real SMT solvers where possible
4. **Test all layers**:
   - API routes (src/api/routes/)
   - Application services (src/application/)
   - Domain steps and verification (src/domain/)
   - Infrastructure providers (src/infrastructure/)
   - Shared utilities (src/shared/)
5. **Follow existing test patterns**: Match the structure and style of current tests in test_cvc5_executor.py
6. **Fast execution**: All unit tests should complete in under 5 seconds total
7. **Clear test names**: Use descriptive names following pattern: test_[function]_[scenario]_[expected_result]
8. **Comprehensive scenarios**: Test happy paths, error cases, edge cases, and boundary conditions
9. **Type safety**: Maintain full type hints in all test code
10. **Async handling**: Properly test async functions using @pytest.mark.asyncio
11. **Refactor for testability**: If production code is difficult to test (tight coupling, hidden dependencies, complex methods), refactor it to be more testable
12. **Design principles**: Ensure all code (both production and test) adheres to:
    - **SOLID**: Single Responsibility, Open/Closed, Liskov Substitution, Interface Segregation, Dependency Inversion
    - **KISS**: Keep It Simple, Stupid - prefer simple solutions
    - **DRY**: Don't Repeat Yourself - extract common functionality
    - **YAGNI**: You Aren't Gonna Need It - don't build features until needed
    - **TRIZ**: Theory of Inventive Problem Solving - seek ideal solutions where problems eliminate themselves

Before starting, thoroughly analyze the codebase to identify:
- Which modules have 0% coverage and need tests first
- Which functions are most critical to the pipeline flow
- What mocking strategies will be needed (LLM, embeddings, solvers)
- How to structure test files to mirror the src/ directory
- Which code needs refactoring for testability (tight coupling, God objects, hidden dependencies)
</requirements>

<implementation>
Follow this systematic approach:

**Phase 1: Fix the hanging test (CRITICAL)**
1. Debug test_timeout_short to understand why it hangs with 0.001s timeout
2. The issue is likely in how Cvc5Executor handles extremely short timeouts in its async execution
3. Fix the timeout handling mechanism to properly respect timeout limits
4. Verify the fix by running the specific test: `pytest tests/unit/test_cvc5_executor.py::TestCvc5ExecutorTimeout::test_timeout_short -v`
5. DO NOT proceed to Phase 2 until this test passes or is properly marked as xfail with explanation

**Phase 2: Create test infrastructure**
1. Set up pytest fixtures for common mocks in `tests/unit/conftest.py`:
   - Mock LLMProvider
   - Mock EmbeddingProvider
   - Mock SemanticVerifier
   - Mock SMTSolver
   - Mock settings/config
2. Create helper utilities for generating test data (sample SMT code, embeddings, etc.)

**Phase 2.5: Refactor production code for testability (as needed)**
When encountering code that is difficult to test, refactor it following these patterns:

1. **Dependency Injection**: If a class creates its own dependencies, refactor to inject them via constructor
   - Example: Instead of `self.client = httpx.AsyncClient()` inside a method, inject the client via __init__
   - Why: Enables mocking dependencies for unit tests

2. **Extract complex methods**: If a method does too much (violates Single Responsibility), break it into smaller methods
   - Example: A 100-line method doing validation, API calls, and result formatting → extract into separate methods
   - Why: Each piece can be tested independently

3. **Remove hidden dependencies**: If code accesses global state, environment variables, or singletons directly
   - Example: Reading `os.environ` directly → inject via Settings/config object
   - Why: Tests can't control global state reliably

4. **Interface Segregation**: If protocols/interfaces are too broad, split them into focused interfaces
   - Example: A Protocol with 10 methods → split into 2-3 focused protocols
   - Why: Easier to mock and test specific behaviors

5. **Simplify conditionals**: Complex nested if/else → extract into guard clauses or strategy pattern
   - Why: Reduces cyclomatic complexity and makes test cases clearer

**IMPORTANT refactoring rules:**
- Only refactor when necessary for testing (don't over-engineer)
- Maintain backward compatibility (don't break existing API contracts)
- Run existing tests after each refactor to ensure no regressions
- Keep changes minimal and focused (KISS principle)
- Don't add features while refactoring (YAGNI principle)
- Document why the refactoring was needed in commit messages

**Phase 3: Systematic coverage by layer (prioritize by business criticality)**

**3.1 Domain Layer** (highest priority - core business logic)
- tests/unit/domain/test_formalization_step.py
  - Test FormalizationStep.execute() with various inputs
  - Test skip_threshold logic (< 200 chars should skip)
  - Test retry logic and temperature progression
  - Test similarity threshold validation
  - Mock LLM and embedding providers

- tests/unit/domain/test_extraction_step.py
  - Test ExtractionStep.execute() logic
  - Test degradation threshold checks
  - Test retry mechanism
  - Mock dependencies

- tests/unit/domain/test_validation_step.py
  - Test ValidationStep.execute()
  - Test SMT solver integration
  - Test error handling for invalid SMT code
  - Mock SMT solver responses

- tests/unit/domain/test_enrichment_step.py (if used)
  - Test enrichment logic
  - Mock web search/external calls

- tests/unit/domain/test_embedding_verifier.py
  - Test cosine similarity calculation
  - Test threshold comparisons

**3.2 Application Layer** (orchestration logic)
- tests/unit/application/test_pipeline_service.py
  - Test PipelineService.process() end-to-end with mocked steps
  - Test error propagation from each step
  - Test skip_formalization flag
  - Test enrich flag
  - Mock all domain step dependencies

**3.3 API Layer** (request/response handling)
- tests/unit/api/test_pipeline_routes.py
  - Test process_informal_text endpoint
  - Test request validation (ProcessRequest model)
  - Test response formatting (ProcessResponse model)
  - Test error responses (422, 500)
  - Use FastAPI TestClient with mocked PipelineService

- tests/unit/api/test_dependencies.py
  - Test get_pipeline_service dependency injection
  - Test proper initialization of services

**3.4 Infrastructure Layer** (external integrations - mock heavily)
- tests/unit/infrastructure/test_llm_client.py
  - Test AnthropicLLMClient.formalize() with mocked httpx
  - Test AnthropicLLMClient.extract() with mocked httpx
  - Test error handling for API failures
  - Test retry logic
  - Mock Anthropic API responses

- tests/unit/infrastructure/test_sentence_transformer.py
  - Test embedding generation with mocked model
  - Test caching behavior
  - Mock torch/transformers dependencies

- tests/unit/infrastructure/test_pysmt_executor.py (if used)
  - Test PysmtExecutor.execute()
  - Mock pysmt solver calls

- tests/unit/infrastructure/test_z3_executor.py (if used)
  - Test Z3Executor.execute()
  - Mock z3 solver calls

**3.5 Shared Layer** (utilities)
- tests/unit/shared/test_result.py
  - Test Ok and Err result types
  - Test pattern matching
  - Test type safety

- tests/unit/shared/test_config.py
  - Test Settings loading from environment
  - Test validation of threshold values
  - Test defaults

- tests/unit/shared/test_retry.py (if retry utility exists)
  - Test retry decorator behavior
  - Test exponential backoff

**Phase 4: Verification**
1. Run full test suite: `pytest tests/unit/ -v --cov=src --cov-report=term-missing`
2. Verify coverage is ≥85% overall
3. Check that all tests complete in < 5 seconds
4. Ensure NO external API calls are made (no Anthropic tokens used)
5. Verify all tests are properly isolated (can run in any order)
</implementation>

<mocking_strategy>
Critical mocking guidelines to ensure fast, isolated unit tests:

**DO use mocks for:**
- Anthropic API calls (httpx.AsyncClient)
- HuggingFace model loading (transformers.AutoModel, AutoTokenizer)
- Torch operations (embedding model inference)
- External SMT solvers (cvc5, z3, pysmt) where appropriate
- File I/O operations
- Network requests
- Environment variables (use monkeypatch)

**Mocking patterns:**
```python
# Example LLM mock
@pytest.fixture
def mock_llm_provider(mocker):
    mock = mocker.AsyncMock(spec=LLMProvider)
    mock.formalize.return_value = "Formal text output"
    mock.extract.return_value = "(declare-const x Int)\n(assert (> x 5))"
    return mock

# Example embedding mock
@pytest.fixture
def mock_embedding_provider(mocker):
    mock = mocker.AsyncMock(spec=EmbeddingProvider)
    mock.embed.return_value = np.array([0.1] * 384)  # 384-dim vector
    return mock
```

**Why mocking matters:**
- Unit tests must be fast (< 5 seconds total) - external calls would take minutes
- Unit tests must be free (no API token costs)
- Unit tests must be deterministic (no flaky network issues)
- Unit tests must be isolated (test one component at a time)
</mocking_strategy>

<output>
Create the following test files in tests/unit/:
- Fix: tests/unit/test_cvc5_executor.py (repair hanging test)
- New: tests/unit/conftest.py (shared fixtures)
- New: tests/unit/domain/test_formalization_step.py
- New: tests/unit/domain/test_extraction_step.py
- New: tests/unit/domain/test_validation_step.py
- New: tests/unit/domain/test_enrichment_step.py (if needed)
- New: tests/unit/domain/test_embedding_verifier.py
- New: tests/unit/application/test_pipeline_service.py
- New: tests/unit/api/test_pipeline_routes.py
- New: tests/unit/api/test_dependencies.py
- New: tests/unit/infrastructure/test_llm_client.py
- New: tests/unit/infrastructure/test_sentence_transformer.py
- New: tests/unit/shared/test_result.py
- New: tests/unit/shared/test_config.py

Refactor production code in src/ as needed:
- Apply dependency injection where classes create their own dependencies
- Extract complex methods into smaller, focused functions
- Remove hidden dependencies on global state
- Split overly broad interfaces into focused protocols
- Simplify complex conditionals

Each test file should:
- Have clear docstrings explaining what's being tested
- Use pytest fixtures for setup
- Group related tests in classes (like TestClassName pattern)
- Use descriptive test method names
- Include assertions with meaningful error messages
</output>

<verification>
Before declaring complete, verify your work by running:

1. **Fix verification**:
   ```bash
   pytest tests/unit/test_cvc5_executor.py::TestCvc5ExecutorTimeout::test_timeout_short -v
   ```
   Must pass or be properly marked as xfail.

2. **Full test suite**:
   ```bash
   pytest tests/unit/ -v --cov=src --cov-report=term-missing --cov-report=html
   ```

3. **Coverage check**:
   - Overall coverage must be ≥85%
   - No module should have <50% coverage (indicates missing critical tests)

4. **Performance check**:
   - Total execution time must be <5 seconds
   - If any test takes >0.5s, investigate and optimize

5. **Quality checks**:
   - All tests pass
   - No pytest warnings (except deprecation warnings from dependencies)
   - No external API calls made (check logs)
   - Tests can run in random order: `pytest tests/unit/ --random-order`

6. **Type safety**:
   ```bash
   mypy tests/unit/
   ```
   All test code should pass type checking.

7. **Design principles review**:
   - Review refactored code for SOLID compliance (check for tight coupling, God objects, mixed responsibilities)
   - Verify no code duplication exists (DRY check)
   - Confirm solutions remain simple and readable (KISS check)
   - Ensure no unnecessary features were added (YAGNI check)
</verification>

<success_criteria>
✅ test_timeout_short no longer hangs and either passes or is properly marked as xfail
✅ Coverage report shows ≥85% overall coverage
✅ All unit tests pass consistently
✅ Full test suite completes in <5 seconds
✅ Zero external API calls or token usage during tests
✅ All new test files follow existing patterns and conventions
✅ No reduction in coverage for already-tested modules (cvc5_executor stays ≥86%)
✅ Coverage HTML report generated in htmlcov/ for easy review
✅ All tests properly isolated (can run independently)
✅ Type hints maintained throughout test code
✅ Refactored code adheres to SOLID principles (dependency injection, single responsibility, etc.)
✅ No code duplication in tests or production code (DRY)
✅ Code remains simple and readable (KISS)
✅ No speculative features added during refactoring (YAGNI)
</success_criteria>

<constraints>
**NEVER:**
- Make real API calls to Anthropic (always mock httpx.AsyncClient)
- Load actual HuggingFace models (mock transformers library)
- Use real credentials or secrets in tests
- Create integration tests (those belong in tests/integration/)
- Skip critical error paths just to boost coverage numbers
- Violate SOLID principles (e.g., create God classes, tight coupling)
- Repeat code unnecessarily (violates DRY)
- Add speculative features not needed for testing (violates YAGNI)
- Over-engineer simple solutions (violates KISS)
- Break existing functionality when refactoring

**ALWAYS:**
- Use AsyncMock for async dependencies
- Properly configure pytest-asyncio markers
- Include docstrings in test functions
- Test both Ok and Err result paths
- Verify type safety with proper type hints
- Follow the existing test patterns in test_cvc5_executor.py
- Apply dependency injection for better testability
- Keep classes and functions focused on single responsibilities (SRP)
- Extract common test fixtures to avoid duplication (DRY)
- Prefer composition over inheritance (favor protocols/interfaces)
- Seek simplest solution that works (KISS + TRIZ ideal final result)
- Run existing tests after refactoring to prevent regressions
</constraints>
