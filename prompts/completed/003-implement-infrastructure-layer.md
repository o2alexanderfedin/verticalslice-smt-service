<objective>
Implement the Infrastructure Layer of the SMT Pipeline service - the concrete implementations of all protocols defined in the domain layer.

This layer provides the actual integrations with external services: Anthropic Claude API, sentence-transformers embedding model, and Z3 SMT solver. All implementations must satisfy the domain protocols and use async/await patterns.

The implementations must handle real-world concerns: retries, timeouts, error handling, and resource management.
</objective>

<context>
**Architecture Reference:** @docs/architecture/ARCHITECTURE.md

**Project Context:**
- Python 3.11+ with strict typing
- Anthropic Claude Sonnet API for LLM operations
- sentence-transformers/all-MiniLM-L6-v2 for embeddings (local model)
- Z3 solver via async subprocess execution
- All implementations must be async
- Must implement protocols from domain layer

**Dependencies to Install:**
- anthropic (Claude API client)
- httpx (async HTTP for API calls)
- sentence-transformers (embedding model)
- torch (required by sentence-transformers)
- numpy (vector operations)

**What This Layer Contains:**
- AnthropicClient - implements LLMProvider protocol
- SentenceTransformerProvider - implements EmbeddingProvider protocol
- Z3Executor - implements SMTSolver protocol
- LLM prompt templates for formalization, extraction, and error fixing

**Why This Matters:**
This layer bridges the pure domain logic with real external services. It must handle all the messy details (network errors, timeouts, resource cleanup) while maintaining clean protocol contracts.
</context>

<requirements>
**Mandatory Implementation Requirements:**

1. **Implement Anthropic LLM Client in `src/infrastructure/llm/client.py`:**
   - Class: `AnthropicClient` implementing `LLMProvider` protocol
   - Use `anthropic` Python SDK
   - Use `httpx.AsyncClient` for connection pooling
   - Methods must implement:
     - `async def formalize(informal_text: str, temperature: float) -> str`
     - `async def extract_to_smtlib(formal_text: str, detail_level: float) -> str`
     - `async def fix_smt_errors(smt_code: str, error_message: str) -> str`
   - All methods must:
     - Use async with proper connection pooling
     - Have 30-second timeout
     - Include error handling with retries
     - Use structured prompts from prompts.py
     - Use claude-sonnet-4-5-20250929 model

2. **Create LLM prompts in `src/infrastructure/llm/prompts.py`:**
   - `FORMALIZATION_PROMPT` - Template for Step 1
     - Must instruct minimal formalization to preserve semantics
     - Must emphasize keeping similarity high (≥91%)
     - Use {informal_text} placeholder
   - `EXTRACTION_PROMPT` - Template for Step 2
     - Must instruct heavy annotation of SMT-LIB code
     - Must emphasize completeness (≤5% information loss)
     - Use {formal_text} and {detail_level} placeholders
   - `ERROR_FIX_PROMPT` - Template for Step 3 fixes
     - Must instruct to preserve ALL annotations
     - Must fix only the specific error
     - Use {smt_code} and {error_message} placeholders
   - All prompts must be XML-structured for Claude

3. **Implement Embedding Provider in `src/infrastructure/embeddings/sentence_transformer.py`:**
   - Class: `SentenceTransformerProvider` implementing `EmbeddingProvider` protocol
   - Load model: `sentence-transformers/all-MiniLM-L6-v2`
   - Method: `async def embed(text: str) -> np.ndarray`
   - CRITICAL: Run embedding computation in thread pool (CPU-bound)
     - Use `loop.run_in_executor(None, self._compute_embedding, text)`
     - This prevents blocking the async event loop
   - Model should be loaded once in __init__ (singleton pattern)
   - Return normalized embeddings (important for cosine similarity)

4. **Implement Z3 Solver in `src/infrastructure/smt/z3_executor.py`:**
   - Class: `Z3Executor` implementing `SMTSolver` protocol
   - Method: `async def execute(smt_lib_code: str, timeout_seconds: int, get_model: bool, get_unsat_core: bool) -> SolverResult`
   - Use `asyncio.create_subprocess_exec` for async execution
   - Execute z3 with `-in` flag (interactive mode)
   - Pass SMT-LIB code via stdin
   - Capture stdout and stderr
   - Parse output:
     - First line should be sat/unsat/unknown
     - If get_model and sat, parse model from remaining lines
     - If get_unsat_core and unsat, parse core from remaining lines
   - Handle errors:
     - Parse errors (invalid syntax)
     - Runtime errors (type mismatches)
     - Timeouts (asyncio.TimeoutError)
   - Return `SolverResult` model with success flag and parsed data

5. **Create configuration in `src/infrastructure/config.py`:**
   - Use `pydantic-settings` for type-safe config
   - Class: `Settings(BaseSettings)`
   - Nested: `PipelineConfig` for thresholds and retry limits
   - Load from `.env` file
   - Required fields:
     - `anthropic_api_key: str`
     - `anthropic_model: str = "claude-sonnet-4-5-20250929"`
     - `embedding_model: str = "sentence-transformers/all-MiniLM-L6-v2"`
     - `formalization_similarity_threshold: float = 0.91`
     - `extraction_degradation_threshold: float = 0.05`
     - `max_formalization_retries: int = 3`
     - `max_extraction_retries: int = 5`
     - `max_validation_retries: int = 3`
     - `smt_solver_timeout: int = 30`

**Type Safety Requirements:**
- All methods must have full type annotations
- Use domain models for return types (SolverResult, etc.)
- Import protocols from domain layer for type hints
- No `Any` types

**Async/Await Requirements:**
- ALL I/O must be async:
  - HTTP calls to Anthropic API - use httpx.AsyncClient
  - Embedding generation - use run_in_executor for CPU-bound work
  - Z3 execution - use asyncio.create_subprocess_exec
- No blocking I/O (no requests library, no subprocess.run, no sync file I/O)
- Proper resource cleanup (async context managers)
</requirements>

<implementation>
**Step-by-Step Implementation:**

1. **Create configuration first:**
   - Create `src/infrastructure/__init__.py`
   - Create `src/infrastructure/config.py`
   - Define Settings and PipelineConfig classes
   - Create `.env.example` with all required variables

2. **Implement LLM client:**
   - Create `src/infrastructure/llm/__init__.py`
   - Create `src/infrastructure/llm/prompts.py` with all three prompt templates
   - Create `src/infrastructure/llm/client.py`
   - Implement AnthropicClient with connection pooling
   - Add retry logic with exponential backoff for API calls
   - Use async context managers for httpx.AsyncClient

3. **Implement embedding provider:**
   - Create `src/infrastructure/embeddings/__init__.py`
   - Create `src/infrastructure/embeddings/sentence_transformer.py`
   - Load model in __init__ (expensive operation, do once)
   - Implement async embed method using thread pool executor
   - Normalize embeddings before returning

4. **Implement Z3 solver:**
   - Create `src/infrastructure/smt/__init__.py`
   - Create `src/infrastructure/smt/z3_executor.py`
   - Implement async subprocess execution
   - Parse solver output correctly
   - Handle all error cases with proper SolverResult responses

5. **Create retry utility:**
   - Create `src/shared/retry.py`
   - Implement async retry decorator with exponential backoff
   - Use for API calls and solver execution

**Key Implementation Patterns:**

```python
# Async HTTP with connection pooling (AnthropicClient)
class AnthropicClient:
    def __init__(self, api_key: str, model: str):
        self._client = httpx.AsyncClient(timeout=30.0)
        self._api_key = api_key
        self._model = model

    async def formalize(self, informal_text: str, temperature: float) -> str:
        async with httpx.AsyncClient(timeout=30.0) as client:
            response = await client.post(
                "https://api.anthropic.com/v1/messages",
                headers={"x-api-key": self._api_key},
                json={...}
            )
            return response.json()["content"][0]["text"]

# CPU-bound task in thread pool (SentenceTransformerProvider)
async def embed(self, text: str) -> np.ndarray:
    loop = asyncio.get_event_loop()
    embedding = await loop.run_in_executor(
        None,
        self._compute_embedding,
        text
    )
    return embedding

def _compute_embedding(self, text: str) -> np.ndarray:
    # This runs in thread pool, not async
    embedding = self.model.encode(text, normalize_embeddings=True)
    return embedding

# Async subprocess (Z3Executor)
async def execute(self, smt_lib_code: str, ...) -> SolverResult:
    process = await asyncio.create_subprocess_exec(
        "z3", "-in",
        stdin=asyncio.subprocess.PIPE,
        stdout=asyncio.subprocess.PIPE,
        stderr=asyncio.subprocess.PIPE
    )
    stdout, stderr = await asyncio.wait_for(
        process.communicate(smt_lib_code.encode()),
        timeout=timeout_seconds
    )
    return self._parse_output(stdout.decode())
```

**What to Avoid and WHY:**
- ❌ NO sync HTTP (requests library) - blocks event loop
- ❌ NO sync subprocess (subprocess.run) - blocks event loop
- ❌ NO blocking embedding computation in async context - blocks event loop
- ❌ NO loading models on every call - expensive, load once
- ❌ NO exposing implementation details to domain layer - maintain protocol abstraction
</implementation>

<output>
Create the following files:

**Configuration:**
- `./src/infrastructure/__init__.py`
- `./src/infrastructure/config.py` - Settings and PipelineConfig
- `./.env.example` - Example environment variables

**LLM integration:**
- `./src/infrastructure/llm/__init__.py`
- `./src/infrastructure/llm/prompts.py` - Prompt templates
- `./src/infrastructure/llm/client.py` - AnthropicClient

**Embeddings integration:**
- `./src/infrastructure/embeddings/__init__.py`
- `./src/infrastructure/embeddings/sentence_transformer.py` - SentenceTransformerProvider

**SMT solver integration:**
- `./src/infrastructure/smt/__init__.py`
- `./src/infrastructure/smt/z3_executor.py` - Z3Executor

**Utilities:**
- `./src/shared/retry.py` - Retry decorator with exponential backoff

**Dependencies:**
- Update `./pyproject.toml` or `./requirements.txt` with:
  - anthropic
  - httpx
  - sentence-transformers
  - torch
  - numpy
  - pydantic-settings
  - python-dotenv

All files must have proper docstrings and type annotations.
</output>

<verification>
Before declaring complete, verify:

1. **Protocol compliance:**
   - AnthropicClient satisfies LLMProvider protocol
   - SentenceTransformerProvider satisfies EmbeddingProvider protocol
   - Z3Executor satisfies SMTSolver protocol
   - Use `isinstance(client, LLMProvider)` checks (runtime_checkable)

2. **Async correctness:**
   - All I/O operations use async/await
   - No blocking calls in async context
   - Embedding computation uses thread pool executor
   - HTTP client uses async context managers
   - Subprocess execution uses asyncio.create_subprocess_exec

3. **Type safety:**
   - Mypy strict mode passes
   - All methods have return type annotations
   - Domain models used for return types

4. **Configuration:**
   - Settings loads from .env file
   - All required fields present
   - Nested PipelineConfig works with env_nested_delimiter

5. **Error handling:**
   - API errors caught and wrapped
   - Solver errors parsed correctly
   - Timeouts handled gracefully
   - Retry logic works for transient failures

6. **Resource management:**
   - Models loaded once (singleton pattern)
   - HTTP clients properly closed (async context managers)
   - No resource leaks

Test each implementation:
```bash
# Can run basic checks
python -c "from src.infrastructure.llm.client import AnthropicClient; print('LLM OK')"
python -c "from src.infrastructure.embeddings.sentence_transformer import SentenceTransformerProvider; print('Embeddings OK')"
python -c "from src.infrastructure.smt.z3_executor import Z3Executor; print('Z3 OK')"
```
</verification>

<success_criteria>
The infrastructure layer is complete when:

1. ✅ All 12+ files created
2. ✅ All three protocol implementations working (LLM, Embeddings, Solver)
3. ✅ Configuration system loads from .env
4. ✅ All implementations use async/await correctly
5. ✅ Mypy strict mode passes
6. ✅ No blocking I/O in async context
7. ✅ Proper error handling and retries
8. ✅ Resource management (models loaded once, connections cleaned up)
9. ✅ LLM prompts structured for optimal results
10. ✅ Dependencies documented in requirements/pyproject.toml

Report back: "Infrastructure layer complete with X files created, all protocols implemented, async patterns verified."
</success_criteria>
