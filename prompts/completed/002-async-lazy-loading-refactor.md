<objective>
Refactor the embedding provider initialization from eager loading to async lazy loading using Python's asyncio.Task pattern.

This refactoring will:
- Eliminate blocking during application startup (faster startup time)
- Maintain race condition safety through Task-based synchronization
- Improve architecture by aligning with async programming patterns
- Apply TDD, SOLID, KISS, DRY, YAGNI, and TRIZ principles throughout

The result will be a more elegant, performant solution that pays the initialization cost on first use while safely handling concurrent requests.
</objective>

<context>
**Current Implementation (v1.15.0):**
- Embedding model is eagerly loaded in FastAPI lifespan event
- `get_embedding_provider()` uses `@lru_cache` decorator (synchronous singleton)
- `SentenceTransformer()` initialization blocks for ~1.4 seconds
- Application startup is delayed by model loading time
- Race condition is prevented but at the cost of slower startup

**Problem:**
The current eager loading approach works but has architectural drawbacks:
1. Blocks application startup (~1.4 seconds)
2. Uses synchronous caching (`@lru_cache`) in an async application
3. Prevents app from being "ready" (health checks pass) before first real request could be served
4. Not idiomatic for async Python applications

**Better Approach:**
Use async lazy loading with `asyncio.Task` pattern:
1. First call to `get_embedding_provider()` creates a Task for loading
2. Subsequent concurrent calls await the same Task
3. Model loads asynchronously without blocking startup
4. Thread-safe through Task deduplication
5. Idiomatic async Python pattern

**Key Files:**
- `src/main.py` - Contains lifespan event with eager loading (to be simplified)
- `src/api/dependencies.py` - Contains `@lru_cache` decorated `get_embedding_provider()` (to be refactored)
- `src/infrastructure/embeddings/sentence_transformer.py` - Contains synchronous `__init__` (reference only)
- `src/application/pipeline_service.py` - Uses embedding provider (consumer, no changes needed)
</context>

<principles>
## SOLID Principles Application

### Single Responsibility Principle (SRP)
- **Dependency module** (`dependencies.py`): Only responsible for dependency injection, not initialization logic
- **Provider class** (`sentence_transformer.py`): Only responsible for embedding operations, not caching strategy
- **Lifespan handler** (`main.py`): Only responsible for critical startup/shutdown, not feature-specific initialization

### Open/Closed Principle (OCP)
- Design the async lazy loading pattern to be extensible to other providers (LLM, SMT solver)
- Use protocol/interface so implementation can be swapped without changing consumers

### Liskov Substitution Principle (LSP)
- The new async `get_embedding_provider()` must be a drop-in replacement
- All existing consumers should work without modification (tests verify this)

### Interface Segregation Principle (ISP)
- Consumers only depend on `EmbeddingProvider` protocol, not concrete implementation
- Don't expose internal initialization details to consumers

### Dependency Inversion Principle (DIP)
- High-level modules (pipeline service) depend on abstractions (`EmbeddingProvider` protocol)
- Low-level modules (concrete providers) implement the abstraction
- Dependency injection container (`dependencies.py`) manages instantiation

## Additional Principles

### KISS (Keep It Simple, Stupid)
- Use standard library `asyncio.Task` - no external libraries needed
- Minimal code changes - only modify what's necessary
- Clear, readable implementation over clever optimizations

### DRY (Don't Repeat Yourself)
- Extract common async lazy loading pattern if multiple providers need it
- Reuse existing `loop.run_in_executor()` pattern
- Single source of truth for provider instance

### YAGNI (You Aren't Gonna Need It)
- Don't add configuration for eager vs lazy loading - lazy is always better here
- Don't add metrics/monitoring yet - wait for actual need
- Don't create abstract base class for lazy loading - one provider is enough for now

### TRIZ (Theory of Inventive Problem Solving)
**Contradiction Resolution:**
- Want: Fast startup (app ready immediately)
- Want: Model loaded before first request completes
- Solution: Async lazy loading - startup is instant, first request pays initialization cost naturally

**Ideal Final Result (IFR):**
- The "problem" (when to load) eliminates itself - loading happens exactly when first needed
- No explicit orchestration required - Task pattern handles synchronization automatically
</principles>

<tdd_approach>
## Test-Driven Development Workflow

**Critical Rule**: Write tests BEFORE implementation. Tests define the contract.

### Phase 1: Write Failing Tests

**Test 1: Basic Async Singleton Behavior**
```python
# tests/unit/api/test_dependencies_async_lazy.py

import pytest
from src.api.dependencies import get_embedding_provider

@pytest.mark.asyncio
async def test_get_embedding_provider_returns_same_instance():
    """Multiple calls return the same provider instance."""
    provider1 = await get_embedding_provider()
    provider2 = await get_embedding_provider()

    assert provider1 is provider2
```

**Test 2: Concurrent Access Safety**
```python
@pytest.mark.asyncio
async def test_concurrent_calls_are_safe():
    """Concurrent calls don't cause race condition or duplicate initialization."""
    import asyncio

    # Simulate 10 concurrent requests arriving during startup
    tasks = [get_embedding_provider() for _ in range(10)]
    providers = await asyncio.gather(*tasks)

    # All should be the same instance
    assert all(p is providers[0] for p in providers)
```

**Test 3: Provider Actually Works**
```python
@pytest.mark.asyncio
async def test_provider_can_generate_embeddings():
    """Loaded provider can actually generate embeddings."""
    provider = await get_embedding_provider()

    embedding = await provider.embed("test text")

    assert embedding is not None
    assert len(embedding) > 0
    assert isinstance(embedding[0], float)
```

**Test 4: Fast Startup (Integration Test)**
```python
@pytest.mark.asyncio
async def test_application_startup_is_fast():
    """Application startup doesn't block on model loading."""
    from src.main import app
    from fastapi.testclient import TestClient
    import time

    # Measure startup time
    start = time.time()
    client = TestClient(app)
    startup_time = time.time() - start

    # Startup should be under 500ms (not the 1.4s model load time)
    assert startup_time < 0.5
```

**Test 5: Cleanup (Reset for Testing)**
```python
@pytest.fixture(autouse=True)
def reset_provider_singleton():
    """Reset singleton state between tests."""
    from src.api import dependencies
    dependencies._embedding_provider_task = None
    yield
    dependencies._embedding_provider_task = None
```

### Phase 2: Run Tests (Should Fail)
```bash
pytest tests/unit/api/test_dependencies_async_lazy.py -v
```

Expected: All tests fail because `get_embedding_provider()` is still synchronous with `@lru_cache`.

### Phase 3: Implement Minimal Code to Pass

**Implementation Steps:**
1. Remove `@lru_cache` from `get_embedding_provider()`
2. Add module-level `_embedding_provider_task` variable
3. Implement async lazy loading with Task pattern
4. Use `run_in_executor()` to load synchronous model asynchronously

### Phase 4: Refactor

**After tests pass:**
1. Add type hints
2. Add docstrings
3. Extract helper function if needed
4. Add logging for observability
5. **Re-run tests to ensure they still pass**
</tdd_approach>

<implementation_plan>
## Step-by-Step Implementation

### Step 1: Write All Tests First (TDD)

Create `tests/unit/api/test_dependencies_async_lazy.py` with all 5 tests from TDD section above.

**Run tests to verify they fail:**
```bash
pytest tests/unit/api/test_dependencies_async_lazy.py -v
```

Expected output: All tests should fail with errors about `get_embedding_provider()` not being awaitable.

### Step 2: Refactor `src/api/dependencies.py`

**Current implementation (lines 27-38):**
```python
@lru_cache
def get_embedding_provider() -> SentenceTransformerProvider:
    """Get embedding provider (singleton).

    Cached because loading the model is expensive (~100-200MB).
    The model is reused across all requests.

    Returns:
        Sentence transformer provider
    """
    settings = get_settings()
    return SentenceTransformerProvider(model_name=settings.embedding_model_name)
```

**New implementation:**
```python
import asyncio
from typing import Optional

# Module-level Task to ensure singleton behavior
_embedding_provider_task: Optional[asyncio.Task[SentenceTransformerProvider]] = None

async def get_embedding_provider() -> SentenceTransformerProvider:
    """Get embedding provider (async lazy-loaded singleton).

    Uses asyncio.Task pattern to ensure:
    - Model is loaded only once (singleton)
    - Multiple concurrent calls await the same Task
    - No race conditions during initialization
    - Non-blocking startup (lazy loading)

    The first call creates a Task that loads the model asynchronously.
    Subsequent calls (even concurrent ones) await the same Task.

    Returns:
        Sentence transformer provider (loaded and ready)
    """
    global _embedding_provider_task

    # If no Task exists, create one to load the provider
    if _embedding_provider_task is None:
        _embedding_provider_task = asyncio.create_task(_load_embedding_provider())

    # Await the Task (either newly created or existing)
    return await _embedding_provider_task


async def _load_embedding_provider() -> SentenceTransformerProvider:
    """Load embedding provider asynchronously.

    Runs the synchronous SentenceTransformer initialization in a thread pool
    to avoid blocking the event loop.

    Returns:
        Fully initialized sentence transformer provider
    """
    import logging

    logger = logging.getLogger(__name__)
    settings = get_settings()

    logger.info(f"Loading embedding model asynchronously: {settings.embedding_model_name}")

    # Run synchronous initialization in thread pool executor
    loop = asyncio.get_event_loop()
    provider = await loop.run_in_executor(
        None,  # Use default ThreadPoolExecutor
        lambda: SentenceTransformerProvider(model_name=settings.embedding_model_name)
    )

    logger.info("Embedding model loaded and ready")

    return provider
```

**Key improvements:**
1. **Async function signature** - `async def get_embedding_provider()`
2. **Task-based singleton** - `_embedding_provider_task` ensures single initialization
3. **Thread pool execution** - `loop.run_in_executor()` prevents event loop blocking
4. **Concurrent safety** - Multiple coroutines can await the same Task
5. **Lazy loading** - Only loads when first called

### Step 3: Simplify `src/main.py` Lifespan Event

**Current implementation (lines 25-69):**
```python
@asynccontextmanager
async def lifespan(app: FastAPI) -> AsyncGenerator[None, None]:
    """Application lifespan manager.

    Handles startup and shutdown events using the modern lifespan pattern.
    Validates critical configuration and eagerly loads the embedding model.
    """
    # Startup logic
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

    # CRITICAL: Eagerly initialize embedding model to prevent race conditions
    # This prevents the smoke test race condition where requests arrive before
    # the SentenceTransformer model finishes lazy initialization
    logger.info("Eagerly loading embedding model...")
    from src.api.dependencies import get_embedding_provider

    embedding_provider = get_embedding_provider()

    # Warmup: Run a test embedding to ensure model is fully initialized
    # This triggers any lazy PyTorch initialization that happens on first encode()
    logger.info("Running embedding warmup...")
    await embedding_provider.embed("warmup")
    logger.info("Embedding model fully initialized and ready")

    # Application is now ready to handle requests
    yield

    # Shutdown logic
    logger.info(f"Shutting down {settings.api_title}")
```

**New implementation (simplified):**
```python
@asynccontextmanager
async def lifespan(app: FastAPI) -> AsyncGenerator[None, None]:
    """Application lifespan manager.

    Handles startup and shutdown events using the modern lifespan pattern.
    Validates critical configuration before startup.

    Note: Embedding model is now lazy-loaded on first use via async Task pattern,
    eliminating the need for eager initialization during startup.
    """
    # Startup logic
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
    logger.info("Application ready - embedding model will be loaded on first use")

    # Application is now ready to handle requests
    yield

    # Shutdown logic
    logger.info(f"Shutting down {settings.api_title}")
```

**Key changes:**
1. **Removed eager loading** - No longer calls `get_embedding_provider()` during startup
2. **Removed warmup call** - No longer needed
3. **Simplified comments** - Explain lazy loading strategy
4. **Faster startup** - Application starts immediately

### Step 4: Update Health Endpoint (Optional Enhancement)

Consider adding `embedding_model_loaded` status to health check:

```python
@app.get("/health")
async def health_check():
    """Service health check endpoint."""
    from src.api.dependencies import _embedding_provider_task

    return {
        "status": "healthy",
        "service": settings.api_title,
        "version": settings.api_version,
        "embedding_model": settings.embedding_model_name,
        "embedding_model_loaded": _embedding_provider_task is not None and _embedding_provider_task.done(),
    }
```

**Note**: This is optional (YAGNI) - only add if monitoring requires it.

### Step 5: Run Tests Again (Should Pass)

```bash
pytest tests/unit/api/test_dependencies_async_lazy.py -v
```

Expected: All 5 tests should pass.

### Step 6: Run Full Test Suite

```bash
pytest tests/ -v
```

Expected: All existing tests should still pass (Liskov Substitution Principle - drop-in replacement).

### Step 7: Manual Verification

**Test 1: Application Starts Fast**
```bash
time uvicorn src.main:app --host 0.0.0.0 --port 8000
```

Expected: Application should start in < 1 second (not ~2.5 seconds).

**Test 2: Health Check Works Immediately**
```bash
curl http://localhost:8000/health
```

Expected: Returns 200 immediately after startup.

**Test 3: First Pipeline Request Loads Model**
```bash
curl -X POST http://localhost:8000/pipeline/process \
  -H 'Content-Type: application/json' \
  -d '{"informal_text": "x > 5"}'
```

Expected:
- Takes ~5-6 seconds (includes ~1.4s model loading)
- Subsequent requests are fast (~4s without model loading)

**Test 4: Concurrent Requests Don't Cause Issues**
```bash
# Send 5 concurrent requests
for i in {1..5}; do
  curl -X POST http://localhost:8000/pipeline/process \
    -H 'Content-Type: application/json' \
    -d '{"informal_text": "test '$i'"}' &
done
wait
```

Expected: All requests succeed, no race condition errors.
</implementation_plan>

<verification>
## Checklist Before Completion

### Code Quality
- [ ] All new code has type hints (mypy passes)
- [ ] All functions have docstrings
- [ ] Logging statements added for observability
- [ ] No `print()` statements (use `logger` instead)
- [ ] Code follows project conventions (black, ruff pass)

### Testing
- [ ] All 5 new tests written and pass
- [ ] Existing test suite still passes (no regressions)
- [ ] Integration tests verify startup time improvement
- [ ] Concurrent access test verifies no race conditions

### SOLID Principles Applied
- [ ] Single Responsibility: Each function has one clear purpose
- [ ] Open/Closed: Pattern is extensible to other providers
- [ ] Liskov Substitution: Drop-in replacement for existing code
- [ ] Interface Segregation: Consumers only depend on protocol
- [ ] Dependency Inversion: High-level code depends on abstraction

### Other Principles
- [ ] KISS: Implementation is simple and clear
- [ ] DRY: No code duplication
- [ ] YAGNI: Only implemented what's needed (no premature optimization)
- [ ] TRIZ: Contradiction resolved (fast startup + safe lazy loading)

### Documentation
- [ ] Docstrings explain the async Task pattern
- [ ] Comments explain WHY, not WHAT
- [ ] README updated if needed (startup behavior changed)

### Performance
- [ ] Application startup time < 1 second (measured)
- [ ] First request completes successfully (with model loading)
- [ ] Subsequent requests are fast (no repeated loading)
- [ ] Concurrent requests work correctly

### Production Safety
- [ ] No new environment variables required
- [ ] Backward compatible (existing code works unchanged)
- [ ] Error handling preserves existing behavior
- [ ] Logging provides visibility into initialization
</verification>

<success_criteria>
1. **Tests Pass**: All 5 new tests pass + full test suite passes
2. **Startup Improved**: Application starts in < 1 second (measured with `time`)
3. **Race Condition Prevented**: Concurrent requests handled safely (10 concurrent test passes)
4. **Drop-in Replacement**: No changes needed to existing consumers (`pipeline_service.py`, route handlers)
5. **Code Quality**: Mypy, black, ruff all pass
6. **SOLID Compliance**: All 5 principles demonstrably applied
7. **TDD Followed**: Tests written before implementation
8. **Production Ready**: Manual verification confirms expected behavior
</success_criteria>

<pair_programming_notes>
## Pair Programming Approach

**Driver (You)**: Types the code
**Navigator (Claude/This Prompt)**: Reviews and guides

### During Implementation

**Navigator checks:**
1. "Did we write the test first?" (TDD)
2. "Is this the simplest approach?" (KISS)
3. "Are we duplicating code?" (DRY)
4. "Do we actually need this?" (YAGNI)
5. "Which SOLID principle does this serve?"

**Driver confirms:**
1. Tests fail before implementation
2. Tests pass after implementation
3. Refactoring doesn't break tests
4. Final code is clean and documented

### After Each Function

**Review together:**
- Type hints complete?
- Docstring clear?
- Single responsibility?
- Testable in isolation?

### After Full Implementation

**Review together:**
- All tests pass?
- No regressions?
- Performance improved?
- Ready for commit?
</pair_programming_notes>

<git_workflow>
## Commit Strategy

### Commit 1: Add Tests (Red)
```bash
git add tests/unit/api/test_dependencies_async_lazy.py
git commit -m "test: add async lazy loading tests for embedding provider (TDD red phase)"
```

### Commit 2: Implement Async Lazy Loading (Green)
```bash
git add src/api/dependencies.py
git commit -m "refactor: implement async lazy loading for embedding provider

- Replace @lru_cache with asyncio.Task pattern
- Use run_in_executor for non-blocking initialization
- Ensure thread-safe singleton behavior
- All tests now pass (TDD green phase)"
```

### Commit 3: Simplify Lifespan Event (Refactor)
```bash
git add src/main.py
git commit -m "refactor: remove eager loading from lifespan event

- Embedding model now lazy-loaded on first use
- Faster application startup (< 1 second)
- Simplified startup logic (configuration validation only)
- All tests still pass (TDD refactor phase)"
```

### Commit 4: Documentation
```bash
git add README.md  # If updated
git commit -m "docs: update startup behavior documentation"
```

### Create Release
```bash
git flow release start v1.16.0
git flow release finish -m "v1.16.0: Async lazy loading for embedding provider" v1.16.0
git push origin develop main --tags
```
</git_workflow>

<expected_outcome>
After completing this refactoring:

1. **Faster Startup**: Application starts in < 1 second (vs ~2.5 seconds before)
2. **Safe Concurrency**: Multiple concurrent requests handled correctly
3. **Cleaner Architecture**: Async lazy loading aligns with FastAPI's async design
4. **Better Testing**: Comprehensive test coverage for initialization edge cases
5. **SOLID Compliance**: Code demonstrates all 5 SOLID principles
6. **Production Ready**: No breaking changes, backward compatible

**Metrics Improvement:**
- Startup time: 2.5s → < 1s (60% faster)
- First request: ~5-6s (includes model loading, expected)
- Subsequent requests: ~4s (no model loading, same as before)
- Code complexity: Reduced (simpler startup logic)
- Test coverage: Increased (5 new tests for edge cases)
</expected_outcome>
