<objective>
Implement the Domain Layer of the SMT Pipeline service following the architecture specification exactly.

This layer contains the core business logic for the three-step pipeline: formalization, extraction, and solver validation. It must be pure domain logic with no external dependencies except interfaces (protocols).

The implementation must follow SOLID principles, use full type annotations, and implement the stored embeddings optimization for performance.
</objective>

<context>
**Architecture Reference:** @docs/architecture/ARCHITECTURE.md

**Project Context:**
- Python 3.11+ with strict typing (mypy compatible)
- Pydantic models for all data structures
- Protocol-based interfaces for dependency inversion
- Result types for error handling
- No external dependencies in domain layer (only protocols)

**What This Layer Contains:**
- Domain models (VerifiedOutput, PipelineMetrics, FormalizationResult, etc.)
- Interface definitions (Protocols for EmbeddingProvider, LLMProvider, SMTSolver)
- Pipeline step implementations (formalization, extraction, validation)
- Embedding verification logic
- Result types for functional error handling

**Why This Matters:**
The domain layer is the heart of the application. It must be independent of infrastructure concerns, fully testable, and contain all business rules for the three-step semantic-preserving pipeline.
</context>

<requirements>
**Mandatory Implementation Requirements:**

1. **Create all domain models in `src/domain/models.py`:**
   - `FormalizationResult` - Result from Step 1
   - `ExtractionResult` - Result from Step 2
   - `SolverResult` - Result from Step 3
   - `PipelineMetrics` - Performance tracking
   - `VerifiedOutput` - Final pipeline output
   - All models must use Pydantic BaseModel with strict validation
   - All fields must have explicit types (no `Any`)
   - Use `Field()` for constraints (ge, le for numeric ranges)

2. **Create all protocols in `src/domain/interfaces.py`:**
   - `EmbeddingProvider` - Protocol for embedding generation
   - `LLMProvider` - Protocol for LLM interactions
   - `SMTSolver` - Protocol for solver execution
   - `SemanticVerifier` - Protocol for embedding distance calculations
   - All protocols must be `@runtime_checkable`
   - All methods must have full type annotations including numpy arrays

3. **Implement Step 1: Formalization in `src/domain/steps/formalization.py`:**
   - Class: `FormalizationStep`
   - Constructor accepts `LLMProvider`, `SemanticVerifier`, and config
   - Method: `async def execute(informal_text: str) -> Result[FormalizationResult, FormalizationError]`
   - CRITICAL: Store source embedding ONCE before retry loop
   - Retry up to 3 times with temperature adjustment (0.3 + attempt*0.1)
   - Target: ≥91% cosine similarity
   - Return `Ok(FormalizationResult)` on success, `Err(FormalizationError)` on failure

4. **Implement Step 2: Extraction in `src/domain/steps/extraction.py`:**
   - Class: `ExtractionStep`
   - Constructor accepts `LLMProvider`, `SemanticVerifier`, and config
   - Method: `async def execute(formal_text: str) -> Result[ExtractionResult, ExtractionError]`
   - CRITICAL: Store formal text embedding ONCE before retry loop
   - Retry up to 5 times with detail level adjustment (0.6 + attempt*0.1)
   - Target: ≤5% degradation
   - Return `Ok(ExtractionResult)` on success, `Err(ExtractionError)` on failure

5. **Implement Step 3: Validation in `src/domain/steps/validation.py`:**
   - Class: `ValidationStep`
   - Constructor accepts `SMTSolver`, `LLMProvider`, and config
   - Method: `async def execute(smt_code: str) -> Result[SolverResult, ValidationError]`
   - Retry up to 3 times on solver errors
   - Use LLM to fix errors while preserving annotations
   - Return `Ok(SolverResult)` with sat/unsat/unknown on success

6. **Implement embedding verification in `src/domain/verification/embedding_verifier.py`:**
   - Class: `EmbeddingDistanceVerifier` implementing `SemanticVerifier`
   - Method: `calculate_similarity(embedding1, embedding2) -> float`
   - Method: `calculate_degradation(embedding1, embedding2) -> float`
   - Use numpy cosine_similarity formula
   - Must be pure functions (no side effects)

7. **Create Result types in `src/shared/result.py`:**
   - Generic `Ok[T]` and `Err[E]` dataclasses
   - Type alias: `Result[T, E] = Union[Ok[T], Err[E]]`
   - Follow the pattern from architecture document exactly

8. **Create exception hierarchy in `src/application/exceptions.py`:**
   - `PipelineError` - Base exception
   - `FormalizationError` - Step 1 failure with attempts and final_similarity
   - `ExtractionError` - Step 2 failure with attempts and final_degradation
   - `ValidationError` - Step 3 failure with attempts and final_error
   - All must inherit from `PipelineError`

**Type Safety Requirements:**
- NO `Any` types anywhere
- Full type annotations on all functions, methods, parameters, and return types
- Use `numpy.ndarray` for embeddings (not `Any`)
- Use `Literal["sat", "unsat", "unknown"]` for solver results
- Enable forward references for self-referencing Pydantic models

**Performance Requirements:**
- MUST implement stored embeddings optimization (compute source embedding once per retry loop)
- All step implementations must be async
- No blocking I/O in domain layer (all I/O through protocols)
</requirements>

<implementation>
**Step-by-Step Implementation:**

1. **Start with shared utilities:**
   - Create `src/shared/__init__.py`
   - Create `src/shared/result.py` with Ok/Err types
   - Create `src/shared/logging.py` with structured logging setup

2. **Create domain models:**
   - Create `src/domain/__init__.py`
   - Create `src/domain/models.py` with all Pydantic models
   - Reference architecture document for exact field definitions
   - Add validation constraints using Field(ge=, le=)

3. **Define protocols:**
   - Create `src/domain/interfaces.py`
   - Implement all four protocols exactly as specified
   - Use `@runtime_checkable` decorator
   - Import from `typing import Protocol, runtime_checkable`

4. **Implement verification:**
   - Create `src/domain/verification/__init__.py`
   - Create `src/domain/verification/embedding_verifier.py`
   - Implement cosine similarity and degradation calculations
   - Use numpy for vector operations

5. **Implement pipeline steps:**
   - Create `src/domain/steps/__init__.py`
   - Create `src/domain/steps/formalization.py` - implement FormalizationStep
   - Create `src/domain/steps/extraction.py` - implement ExtractionStep
   - Create `src/domain/steps/validation.py` - implement ValidationStep
   - Each step must follow the retry pattern from architecture
   - CRITICAL: Store source embeddings before loops

6. **Create exceptions:**
   - Create `src/application/__init__.py`
   - Create `src/application/exceptions.py`
   - Define exception hierarchy with proper attributes

**What to Avoid and WHY:**
- ❌ NO concrete implementations of external services (that's infrastructure layer)
- ❌ NO direct imports from httpx, anthropic, sentence-transformers (use protocols)
- ❌ NO database code (we have no persistence)
- ❌ NO API code (that's API layer)
- ❌ Use Result types for expected failures, NOT raising exceptions for flow control
- ❌ DO NOT compute embeddings multiple times per retry loop (performance critical)

**Key Patterns from Architecture:**

```python
# Stored embeddings pattern (CRITICAL for performance)
embedding_source = await self.semantic_verifier.embed(informal_text)

for attempt in range(self.config.max_retries):
    formal_text = await self.llm_provider.formalize(
        informal_text,
        temperature=0.3 + attempt * 0.1
    )
    embedding_formal = await self.semantic_verifier.embed(formal_text)
    similarity = self.semantic_verifier.calculate_similarity(
        embedding_source,
        embedding_formal
    )
    if similarity >= self.config.threshold:
        return Ok(FormalizationResult(...))

return Err(FormalizationError(...))
```
</implementation>

<output>
Create the following files:

**Shared utilities:**
- `./src/shared/__init__.py`
- `./src/shared/result.py` - Ok/Err generic types
- `./src/shared/logging.py` - Logging configuration

**Domain models and interfaces:**
- `./src/domain/__init__.py`
- `./src/domain/models.py` - All Pydantic models
- `./src/domain/interfaces.py` - All protocols

**Verification:**
- `./src/domain/verification/__init__.py`
- `./src/domain/verification/embedding_verifier.py` - EmbeddingDistanceVerifier

**Pipeline steps:**
- `./src/domain/steps/__init__.py`
- `./src/domain/steps/formalization.py` - FormalizationStep
- `./src/domain/steps/extraction.py` - ExtractionStep
- `./src/domain/steps/validation.py` - ValidationStep

**Exceptions:**
- `./src/application/__init__.py`
- `./src/application/exceptions.py` - Exception hierarchy

All files must have proper module docstrings and inline comments explaining business logic.
</output>

<verification>
Before declaring complete, verify:

1. **Type safety:**
   - Run `mypy src/domain src/shared src/application --strict` (should pass)
   - No `Any` types anywhere
   - All functions have return type annotations

2. **Protocol compliance:**
   - All protocols are `@runtime_checkable`
   - All protocol methods have async def and full type hints
   - EmbeddingDistanceVerifier implements SemanticVerifier protocol

3. **Model validation:**
   - All Pydantic models have Field constraints where needed
   - FormalizationResult.similarity_score has Field(ge=0.0, le=1.0)
   - All attempts fields have Field(ge=1)

4. **Stored embeddings optimization:**
   - FormalizationStep computes source embedding BEFORE retry loop
   - ExtractionStep computes formal text embedding BEFORE retry loop
   - Each loop iteration only computes NEW embedding

5. **Result type usage:**
   - All step execute methods return Result[SuccessType, ErrorType]
   - Errors are Err(exception), not raised exceptions

6. **Architecture compliance:**
   - Cross-reference every model/class against architecture document
   - Verify all fields match specification exactly
   - Confirm retry counts match (3, 5, 3 for steps 1, 2, 3)

If mypy fails or any verification fails, fix before completing.
</verification>

<success_criteria>
The domain layer is complete when:

1. ✅ All 15+ files created with proper structure
2. ✅ Mypy strict mode passes with no errors
3. ✅ All Pydantic models have complete field definitions matching architecture
4. ✅ All four protocols defined with @runtime_checkable
5. ✅ All three pipeline steps implemented with stored embeddings optimization
6. ✅ Result types properly defined and used
7. ✅ Exception hierarchy complete
8. ✅ No external dependencies except protocols (pure domain logic)
9. ✅ Full type annotations everywhere (no Any types)
10. ✅ Code follows SOLID principles (single responsibility, dependency inversion)

Report back: "Domain layer implementation complete with X files created, mypy strict mode passing, stored embeddings optimization verified."
</success_criteria>
