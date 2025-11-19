<objective>
Design a comprehensive technical architecture for a Semantic-Preserving Text Formalization and SMT-LIB Extraction Pipeline following the vertical slice paradigm.

This architecture will transform informal natural language text into valid, executable SMT-LIB symbolic representations while maintaining semantic completeness through a three-step pipeline with embedding distance verification.

The design must be production-ready, following SOLID, DRY, KISS, YAGNI, and TRIZ principles, with strong typing, comprehensive error handling, and full async/await patterns.
</objective>

<context>
**Source Specification:** @docs/specs/PIPELINE-DESIGN.md

**Technology Stack:**
- Language: Python 3.11+ with full type annotations
- Framework: FastAPI for REST API layer
- Async Pattern: asyncio with async/await throughout
- LLM: Anthropic Claude Sonnet for formalization and extraction steps
- Embeddings: sentence-transformers/all-MiniLM-L6-v2 (local model)
- SMT Solver: Z3 (via subprocess execution)
- No persistence layer: All processing in-memory
- No caching: Fresh processing for each request

**Project Context:**
This is a vertical slice implementation - we need ONE complete working use case from API endpoint through all three pipeline steps to verified SMT-LIB output. The architecture should be minimalistic yet extensible, focusing on the core pipeline flow with proper separation of concerns.

**Key Requirements from Specification:**
1. **Step 1: Formalization** - Transform informal text to formal text (≥91% embedding similarity)
2. **Step 2: SMT-LIB Extraction** - Extract to heavily annotated SMT-LIB (≤5% degradation)
3. **Step 3: Solver Validation** - Execute with Z3 and handle errors via LLM fixes
4. **Optimization:** Store source embeddings in variables (compute once per retry loop)
5. **Retry Strategy:** Max 3 attempts for Step 1, 5 for Step 2, 3 for Step 3
6. **Complete Output:** Return check-sat result (sat/unsat/unknown), optional model/unsat-core, and annotated SMT-LIB code
</context>

<architectural_principles>
**Vertical Slice Architecture:**
- Each slice cuts through all layers (API → Service → Domain → Infrastructure)
- One complete feature end-to-end rather than horizontal layers
- Focus on ONE working use case: "Process informal text to verified SMT-LIB"
- Avoid building infrastructure not needed for this slice

**SOLID Principles:**
- Single Responsibility: Each class/module has one reason to change
- Open/Closed: Extend behavior without modifying existing code
- Liskov Substitution: Interfaces over implementations
- Interface Segregation: Small, focused interfaces
- Dependency Inversion: Depend on abstractions, not concretions

**Minimalism (KISS + YAGNI):**
- Build only what's needed for the vertical slice
- No premature abstraction
- No speculative features
- Simple solutions over clever ones

**Type Safety (Mandatory):**
- Full type annotations on all functions, methods, and variables
- Use Pydantic models for all data structures
- Never use `Any` type - use `Unknown` with type guards if needed
- Enable strict mypy checking
- Result types for error handling (not exceptions for flow control)

**Async/Await (Mandatory):**
- All I/O operations must be async (LLM calls, embedding generation, SMT solver execution)
- Use httpx for async HTTP (Anthropic API)
- Use asyncio.subprocess for async SMT solver execution
- No blocking I/O in async context
</architectural_principles>

<design_requirements>
**1. Module Structure (Vertical Slice)**

Create a clean module structure following vertical slice paradigm:

```
src/
├── api/                          # API Layer (FastAPI)
│   ├── __init__.py
│   ├── dependencies.py           # FastAPI dependency injection
│   ├── models.py                 # Request/Response Pydantic models
│   └── routes/
│       ├── __init__.py
│       └── pipeline.py           # POST /pipeline/process endpoint
│
├── application/                  # Application/Service Layer
│   ├── __init__.py
│   ├── pipeline_service.py       # Orchestrates 3-step pipeline
│   └── exceptions.py             # Application-level exceptions
│
├── domain/                       # Domain/Business Logic Layer
│   ├── __init__.py
│   ├── models.py                 # Domain models (VerifiedOutput, PipelineMetrics, etc.)
│   ├── interfaces.py             # Protocols/ABCs for dependencies
│   ├── steps/
│   │   ├── __init__.py
│   │   ├── formalization.py      # Step 1: Formalization logic
│   │   ├── extraction.py         # Step 2: SMT-LIB extraction logic
│   │   └── validation.py         # Step 3: Solver validation logic
│   └── verification/
│       ├── __init__.py
│       └── embedding_verifier.py # Embedding distance calculations
│
├── infrastructure/               # Infrastructure/External Dependencies
│   ├── __init__.py
│   ├── llm/
│   │   ├── __init__.py
│   │   ├── client.py             # Anthropic Claude client wrapper
│   │   └── prompts.py            # LLM prompt templates
│   ├── embeddings/
│   │   ├── __init__.py
│   │   └── sentence_transformer.py  # Embedding model wrapper
│   └── smt/
│       ├── __init__.py
│       └── z3_executor.py        # Z3 solver execution wrapper
│
├── shared/                       # Shared utilities
│   ├── __init__.py
│   ├── result.py                 # Result<T, E> type for error handling
│   ├── retry.py                  # Retry decorator/utility
│   └── logging.py                # Logging configuration
│
└── main.py                       # FastAPI application entry point
```

**2. Type System Design**

Define all domain models using Pydantic with strict typing:

```python
# Example structure - adapt as needed
from pydantic import BaseModel, Field
from typing import Optional, Literal
from enum import Enum

class FormalizationResult(BaseModel):
    formal_text: str
    similarity_score: float = Field(ge=0.0, le=1.0)
    attempts: int = Field(ge=1)

class ExtractionResult(BaseModel):
    smt_lib_code: str  # Entire annotated SMT-LIB file
    degradation: float = Field(ge=0.0, le=1.0)
    attempts: int = Field(ge=1)

class SolverResult(BaseModel):
    success: bool
    check_sat_result: Literal["sat", "unsat", "unknown"] | str  # str for error messages
    model: Optional[str] = None
    unsat_core: Optional[str] = None
    raw_output: str
    attempts: int = Field(ge=1)

class VerifiedOutput(BaseModel):
    # ... as per specification
    informal_text: str
    formal_text: str
    formalization_similarity: float
    smt_lib_code: str
    extraction_degradation: float
    check_sat_result: str
    model: Optional[str]
    unsat_core: Optional[str]
    solver_success: bool
    solver_attempts: int
    metrics: "PipelineMetrics"
    passed_all_checks: bool
    requires_manual_review: bool
```

**3. Interface Design (Dependency Inversion)**

Define clear protocols for all external dependencies:

```python
from typing import Protocol
import numpy as np

class EmbeddingProvider(Protocol):
    """Protocol for embedding generation."""
    async def embed(self, text: str) -> np.ndarray: ...

class LLMProvider(Protocol):
    """Protocol for LLM interactions."""
    async def formalize(self, informal_text: str, temperature: float) -> str: ...
    async def extract_to_smtlib(self, formal_text: str, detail_level: float) -> str: ...
    async def fix_smt_errors(self, smt_code: str, error_message: str) -> str: ...

class SMTSolver(Protocol):
    """Protocol for SMT solver execution."""
    async def execute(
        self,
        smt_lib_code: str,
        timeout_seconds: int,
        get_model: bool,
        get_unsat_core: bool
    ) -> SolverResult: ...
```

**4. Error Handling Strategy**

Implement comprehensive error handling using Result types:

```python
from typing import Generic, TypeVar, Union
from dataclasses import dataclass

T = TypeVar('T')
E = TypeVar('E', bound=Exception)

@dataclass
class Ok(Generic[T]):
    value: T

@dataclass
class Err(Generic[E]):
    error: E

Result = Union[Ok[T], Err[E]]

# Define domain-specific exceptions
class PipelineError(Exception):
    """Base exception for pipeline errors."""
    pass

class FormalizationError(PipelineError):
    """Step 1 failed to preserve semantics."""
    attempts: int
    final_similarity: float

class ExtractionError(PipelineError):
    """Step 2 failed to extract complete information."""
    attempts: int
    final_degradation: float

class ValidationError(PipelineError):
    """Step 3 failed to produce valid SMT-LIB."""
    attempts: int
    final_error: str
```

**5. Async/Await Architecture**

ALL I/O operations must be async. Key patterns:

```python
# LLM calls
async def formalize(self, text: str) -> str:
    async with httpx.AsyncClient() as client:
        response = await client.post(...)

# Embedding generation
async def embed(self, text: str) -> np.ndarray:
    # Even if model is CPU-bound, run in thread pool
    loop = asyncio.get_event_loop()
    return await loop.run_in_executor(None, self._compute_embedding, text)

# SMT solver execution
async def execute_solver(self, code: str) -> SolverResult:
    process = await asyncio.create_subprocess_exec(
        "z3", "-in",
        stdin=asyncio.subprocess.PIPE,
        stdout=asyncio.subprocess.PIPE,
        stderr=asyncio.subprocess.PIPE
    )
    stdout, stderr = await process.communicate(code.encode())
```

**6. Retry Logic with Stored Embeddings**

CRITICAL optimization from specification:

```python
# Step 1: Store source embedding ONCE
embedding_source = await embedding_provider.embed(informal_text)

for attempt in range(max_retries):
    formal_text = await llm.formalize(informal_text, temperature=0.3 + attempt*0.1)
    embedding_formal = await embedding_provider.embed(formal_text)  # Only new embedding
    similarity = cosine_similarity(embedding_source, embedding_formal)
    if similarity >= 0.91:
        break

# Step 2: Store formal text embedding ONCE
embedding_formal = await embedding_provider.embed(formal_text)

for attempt in range(max_retries):
    smt_code = await llm.extract_to_smtlib(formal_text, detail_level=...)
    embedding_smt = await embedding_provider.embed(smt_code)  # Only new embedding
    degradation = 1.0 - cosine_similarity(embedding_formal, embedding_smt)
    if degradation <= 0.05:
        break
```

**7. API Endpoint Design**

Single vertical slice endpoint:

```python
from fastapi import APIRouter, Depends, HTTPException
from src.api.models import ProcessRequest, ProcessResponse

router = APIRouter(prefix="/pipeline", tags=["pipeline"])

@router.post("/process", response_model=ProcessResponse)
async def process_informal_text(
    request: ProcessRequest,
    pipeline_service: PipelineService = Depends(get_pipeline_service)
) -> ProcessResponse:
    """
    Process informal natural language text through the 3-step pipeline.

    Returns verified SMT-LIB code with check-sat result and optional model/unsat-core.
    """
    result = await pipeline_service.process(request.informal_text)

    # Convert Result type to HTTP response
    match result:
        case Ok(output):
            return ProcessResponse.from_domain(output)
        case Err(error):
            # Map domain errors to HTTP status codes
            raise HTTPException(status_code=422, detail=str(error))
```

**8. Dependency Injection**

Use FastAPI's dependency injection for clean architecture:

```python
# src/api/dependencies.py
from functools import lru_cache
from src.application.pipeline_service import PipelineService
from src.infrastructure.llm.client import AnthropicClient
from src.infrastructure.embeddings.sentence_transformer import SentenceTransformerProvider
from src.infrastructure.smt.z3_executor import Z3Executor

@lru_cache()
def get_embedding_provider() -> SentenceTransformerProvider:
    return SentenceTransformerProvider(model_name="sentence-transformers/all-MiniLM-L6-v2")

@lru_cache()
def get_llm_provider() -> AnthropicClient:
    return AnthropicClient(api_key=os.getenv("ANTHROPIC_API_KEY"))

@lru_cache()
def get_smt_solver() -> Z3Executor:
    return Z3Executor()

def get_pipeline_service(
    embedding_provider: SentenceTransformerProvider = Depends(get_embedding_provider),
    llm_provider: AnthropicClient = Depends(get_llm_provider),
    smt_solver: Z3Executor = Depends(get_smt_solver)
) -> PipelineService:
    return PipelineService(
        embedding_provider=embedding_provider,
        llm_provider=llm_provider,
        smt_solver=smt_solver
    )
```

**9. Testing Architecture**

Comprehensive test coverage with three levels:

```
tests/
├── unit/                         # Unit tests (isolated components)
│   ├── test_formalization.py    # Test Step 1 logic
│   ├── test_extraction.py       # Test Step 2 logic
│   ├── test_validation.py       # Test Step 3 logic
│   └── test_embedding_verifier.py
│
├── integration/                  # Integration tests (components working together)
│   ├── test_pipeline_service.py # Test full service orchestration
│   └── test_llm_client.py       # Test real LLM integration (with mocking)
│
├── e2e/                         # End-to-end tests (full API flow)
│   └── test_api_pipeline.py    # Test POST /pipeline/process
│
└── fixtures/
    ├── sample_texts.py          # Test data
    └── mocks.py                 # Mock implementations of protocols
```

Use pytest with async support:
```python
import pytest
from httpx import AsyncClient

@pytest.mark.asyncio
async def test_pipeline_process_endpoint():
    async with AsyncClient(app=app, base_url="http://test") as client:
        response = await client.post("/pipeline/process", json={
            "informal_text": "If x is greater than 5, then y must be less than 10."
        })
        assert response.status_code == 200
        data = response.json()
        assert data["solver_success"] is True
        assert data["check_sat_result"] in ["sat", "unsat", "unknown"]
```

**10. Configuration Management**

Use Pydantic Settings for type-safe configuration:

```python
from pydantic_settings import BaseSettings

class Settings(BaseSettings):
    # API
    api_host: str = "0.0.0.0"
    api_port: int = 8000

    # LLM
    anthropic_api_key: str
    anthropic_model: str = "claude-sonnet-4-5-20250929"

    # Embeddings
    embedding_model: str = "sentence-transformers/all-MiniLM-L6-v2"

    # Pipeline thresholds
    formalization_similarity_threshold: float = 0.91
    extraction_degradation_threshold: float = 0.05

    # Retry limits
    max_formalization_retries: int = 3
    max_extraction_retries: int = 5
    max_validation_retries: int = 3

    # SMT Solver
    smt_solver_timeout: int = 30

    class Config:
        env_file = ".env"
```
</design_requirements>

<deliverables>
Create the following architecture design document:

**File:** `./docs/architecture/ARCHITECTURE.md`

**Structure:**
1. **Executive Summary** - High-level overview of the architecture
2. **System Context** - What problem this solves and how it fits in the bigger picture
3. **Architectural Principles** - SOLID, DRY, KISS, YAGNI, TRIZ applied to this design
4. **Module Design** - Detailed breakdown of each module with responsibilities
5. **Data Flow** - Step-by-step flow through the pipeline with sequence diagrams (Mermaid)
6. **Type System** - All domain models, Result types, and protocols
7. **Error Handling Strategy** - Exception hierarchy, Result types, retry logic
8. **Interface Definitions** - All protocols/ABCs for dependency inversion
9. **Async/Await Patterns** - How concurrency is handled throughout
10. **API Design** - Endpoint specification, request/response models
11. **Dependency Injection** - How components are wired together
12. **Testing Strategy** - Unit, integration, and E2E test approach
13. **Configuration** - Environment variables and settings management
14. **Performance Considerations** - Optimization strategies (stored embeddings, async I/O)
15. **Quality Assurance** - Validation gates, manual review triggers
16. **Future Extensibility** - How to add new steps, solvers, or LLM providers

**Format Requirements:**
- Use Mermaid diagrams for all architectural views (context, module, sequence, etc.)
- Include code examples for key patterns (must be valid Python with full type hints)
- Reference the source specification (@docs/specs/PIPELINE-DESIGN.md) for metrics and thresholds
- Keep it concise but complete - focus on architectural decisions, not implementation details
- Every design decision should include the WHY (TRIZ principle: explain reasoning)

**Quality Checklist:**
Before completing, verify the architecture has:
- [ ] Clear separation of concerns (API → Application → Domain → Infrastructure)
- [ ] Full type safety (no `Any` types, all Pydantic models defined)
- [ ] Comprehensive async/await (all I/O is non-blocking)
- [ ] Proper error handling (Result types, exception hierarchy)
- [ ] Dependency inversion (protocols for all external dependencies)
- [ ] Testability (clear interfaces, dependency injection)
- [ ] Minimalism (only what's needed for the vertical slice)
- [ ] Optimization (stored embeddings as per specification)
- [ ] Mermaid diagrams for all architectural views
- [ ] Code examples with full type annotations
</deliverables>

<success_criteria>
The architecture design is complete when:

1. **Vertical Slice Complete**: One end-to-end flow from API endpoint to verified SMT-LIB output is fully designed
2. **SOLID Compliance**: Each module has single responsibility, depends on abstractions, follows all SOLID principles
3. **Type Safety**: All data structures defined with Pydantic, all functions have type hints, mypy would pass strict mode
4. **Async Throughout**: All I/O operations (LLM, embeddings, solver) use async/await patterns
5. **Testable Design**: Clear interfaces allow easy mocking for unit tests, integration tests, and E2E tests
6. **Error Handling**: Comprehensive exception hierarchy and Result types for all failure modes
7. **Performance Optimized**: Embeddings stored in variables per specification (compute once per retry loop)
8. **Documentation Quality**: Architecture document is clear, concise, includes Mermaid diagrams and code examples
9. **Minimalist**: No over-engineering, no premature abstractions, only what's needed for the slice
10. **Extensible**: Clear extension points for adding new LLM providers, solvers, or pipeline steps

The design should be production-ready and immediately implementable by a development team.
</success_criteria>

<verification>
Before declaring the architecture design complete:

1. **Review against specification**: Cross-check all requirements from @docs/specs/PIPELINE-DESIGN.md are addressed
2. **SOLID check**: Verify each module follows Single Responsibility and depends on abstractions
3. **Type safety check**: Ensure no `Any` types, all models are Pydantic, all functions typed
4. **Async check**: Confirm all I/O operations use async/await (LLM calls, embeddings, solver execution)
5. **Diagram completeness**: Verify Mermaid diagrams for system context, module structure, and sequence flow
6. **Code example validation**: Ensure all code snippets are valid Python 3.11+ with full type hints
7. **Minimalism check**: Remove any speculative features or over-engineering not needed for vertical slice
8. **Extension points**: Verify architecture allows adding new providers without modifying existing code

If any item fails verification, revise the architecture before completing.
</verification>

<constraints>
**Must Have:**
- Python 3.11+ with full type annotations (strict mypy compliance)
- FastAPI for REST API layer
- Async/await for ALL I/O operations (no blocking calls)
- Anthropic Claude Sonnet for LLM steps
- sentence-transformers for embeddings (local model, no API)
- Z3 solver via asyncio subprocess
- Result types for error handling (not exceptions for flow control)
- Pydantic models for all data structures
- Comprehensive error handling (custom exceptions + retry logic)
- Three testing levels (unit, integration, E2E)

**Must NOT Have:**
- Persistence layer (all in-memory processing)
- Caching layer (fresh processing per request)
- Multiple LLM providers (only Anthropic for this vertical slice)
- Complex orchestration frameworks (keep it simple)
- Over-engineered abstractions (YAGNI principle)

**Performance Requirements:**
- Store source embeddings in variables (compute once per retry loop)
- Use async I/O for all external calls
- Timeouts for LLM calls (30s) and solver execution (30s)
- Retry limits: 3 for Step 1, 5 for Step 2, 3 for Step 3

**Quality Requirements:**
- Full type coverage (mypy strict mode)
- 80%+ test coverage
- All async code tested with pytest-asyncio
- Logging at appropriate levels (INFO, WARNING, ERROR)
- Structured error messages with context
</constraints>

<meta_instructions>
This is a complex architectural design task requiring deep thinking about:
- Clean architecture and vertical slice paradigm
- Type-driven design with Pydantic and protocols
- Async/await patterns throughout the stack
- Error handling strategies (Result types vs exceptions)
- Dependency injection and inversion of control
- Testing strategies for async code

Take time to thoroughly analyze the specification and create a well-thought-out, production-ready architecture.

Consider multiple approaches for each design decision and choose the simplest one that satisfies requirements (KISS + YAGNI).

Explain the WHY behind each architectural choice (TRIZ principle: understanding constraints leads to better solutions).

The architecture should feel minimalistic yet complete - nothing unnecessary, nothing missing.
</meta_instructions>
