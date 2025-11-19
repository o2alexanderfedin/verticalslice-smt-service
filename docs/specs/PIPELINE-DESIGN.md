# Semantic-Preserving Text Formalization and SMT-LIB Extraction Pipeline

## Overview

This document describes a three-step pipeline for transforming informal natural language text into valid, executable SMT-LIB symbolic representations while maintaining semantic completeness. The pipeline uses embedding distance metrics for semantic verification and SMT solver execution for syntactic validation.

## Architecture

```mermaid
flowchart TD
    A[Informal Text A] --> B[Step 1: Formalization]
    B --> C{Embedding Distance<br/>A ↔ B}
    C -->|< 91% similarity| D[❌ Reject:<br/>Meaning Changed]
    C -->|≥ 91% similarity| E[✓ Formal Text B]
    D --> B

    E --> F[Step 2: SMT-LIB Extraction]
    F --> G[SMT-LIB Code +<br/>Annotations C]
    G --> H{Embedding Distance<br/>B ↔ C}
    H -->|> 5% degradation| I[❌ Reject:<br/>Information Lost]
    H -->|≤ 5% degradation| J[✓ Complete SMT-LIB]
    I --> F

    J --> L[Step 3: SMT Solver Execution]
    L --> M{Solver Execution}
    M -->|Parse/Runtime Error| N[❌ LLM Fix Code]
    M -->|Success| O[✓ Valid SMT-LIB]
    N --> L

    O --> P[Verified Output:<br/>Executable SMT-LIB]
```

## Pipeline Steps

### Step 1: Iterative Formalization

**Objective:** Transform informal text to formal text while preserving semantic meaning.

**Process:**
```mermaid
sequenceDiagram
    participant A as Informal Text (A)
    participant LLM as Language Model
    participant V as Verifier
    participant B as Formal Text (B)

    Note over V: embedding_A = embed(A)<br/>Compute ONCE, reuse in loop

    loop Retry Loop (max 3 attempts)
        A->>LLM: Request formalization
        LLM->>B: Generate formal version
        B->>V: Calculate embedding_B = embed(B)
        V->>V: cosine_similarity(embedding_A, embedding_B)

        alt similarity ≥ 0.91
            V->>B: ✓ Accept
            B->>A: Return formal text
        else similarity < 0.91
            V->>LLM: ❌ Retry with adjustments
        end
    end
```

**Verification Metric:**
- **Target:** `cosine_similarity(embedding(A), embedding(B)) ≥ 0.91`
- **Baseline:** 91.5% mean from empirical testing
- **Tolerance:** ±1.9% std deviation

**Success Criteria:**
- Formal text emerges naturally
- Facts and rules become explicit
- Semantic meaning preserved
- High embedding similarity maintained

### Step 2: SMT-LIB Extraction with Annotations

**Objective:** Extract facts and constraints into SMT-LIB symbolic representations with completeness verification.

**Process:**
```mermaid
sequenceDiagram
    participant B as Formal Text (B)
    participant LLM as Language Model
    participant V as Verifier
    participant C as SMT-LIB + Annotations

    Note over V: embedding_B = embed(B)<br/>Compute ONCE, reuse in loop

    loop Retry Loop (max 5 attempts)
        B->>LLM: Request SMT-LIB extraction
        Note over LLM: Extract with heavy annotations<br/>to force precision
        LLM->>C: Generate annotated SMT-LIB
        C->>V: Use entire SMT-LIB file as text
        V->>V: embedding_C = embed(smt_lib_file)
        V->>V: Compute degradation vs embedding_B

        alt degradation ≤ 5%
            V->>C: ✓ Accept (Complete)
            C->>B: Return SMT-LIB
        else degradation > 5%
            V->>LLM: ❌ Retry: Missing information
        end
    end
```

**Verification Metric:**
- **Baseline:** 5% expected degradation from sentence removal
- **Target:** `degradation(B, C_smtlib) ≤ 0.05`
- **Calculation:** `1.0 - cosine_similarity(embedding(B), embedding(C_smtlib)) ≤ 0.05`
- **Note:** C_smtlib is the entire SMT-LIB file (code + annotations), not just comments

**Annotation Requirements:**
1. **Mandatory:** Heavily annotate SMT-LIB code with natural language comments
2. **Purpose:**
   - Forces LLM precision during extraction
   - Makes SMT-LIB file readable and self-documenting
   - Entire file (code + comments) used for embedding comparison
3. **Format:**
   ```smt2
   ;; ========================================
   ;; SECTION 1: GROUND TRUTH (from data)
   ;; ========================================
   ;; These are FACTS extracted from problem statement

   ;; Given dimensions (converted to consistent units - inches)
   (declare-const initial_length Real)
   (assert (= initial_length 1200.0))  ; 100 feet = 1200 inches
   ```

**Critical:** The entire SMT-LIB file (including all comments and code) is used for `embedding_C`, not just extracted comments. This works because:
- Annotated SMT-LIB is highly readable
- Comments provide natural language context
- Symbolic assertions are self-documenting
- Together they represent the complete extraction

### Step 3: SMT Solver Validation

**Objective:** Verify that generated SMT-LIB code is syntactically valid and executable.

**Process:**
```mermaid
sequenceDiagram
    participant C as SMT-LIB Code
    participant S as SMT Solver (z3/cvc5)
    participant LLM as Language Model
    participant V as Valid Output

    loop Retry Loop (max 3 attempts)
        C->>S: Execute SMT-LIB code
        S->>S: Parse and check syntax

        alt Success (sat/unsat/unknown)
            S->>V: ✓ Valid executable code
            V->>C: Return verified SMT-LIB
        else Parse Error
            S->>LLM: ❌ Send error message
            Note over LLM: Fix syntax errors<br/>preserving semantics
            LLM->>C: Generate corrected code
        else Runtime Error
            S->>LLM: ❌ Send error message
            Note over LLM: Fix logic errors<br/>preserving semantics
            LLM->>C: Generate corrected code
        end
    end
```

**Verification Metric:**
- **Success:** Solver executes without errors and returns valid response
- **Failure:** Parse errors, runtime errors, or invalid SMT-LIB syntax

**Possible Solver Responses:**

1. **sat** - Formula is satisfiable
   - Can call `get-model` to retrieve variable assignments
   - Model format: `(define-fun x () Int 8)`
   - Requires `(set-option :produce-models true)` in SMT-LIB code

2. **unsat** - Formula is unsatisfiable
   - Can call `get-unsat-core` for unsatisfiable core (minimal subset)
   - Requires `(set-option :produce-unsat-cores true)` in SMT-LIB code

3. **unknown** - Solver cannot determine satisfiability
   - May be due to incomplete decision procedures
   - May be due to timeout or resource limits
   - Can attempt `get-value` but results are unreliable

**Error Types:**
1. **Parse Errors:** Invalid syntax, unknown commands, malformed expressions
2. **Runtime Errors:** Type mismatches, undefined symbols, logic violations
3. **Timeout:** Solver takes too long (configurable threshold)
4. **Invalid Output:** Solver returns unexpected response

**LLM Fix Strategy:**
When solver execution fails:
1. Extract error message from solver output
2. Provide error context to LLM with original code (including all annotations)
3. Request fix while **preserving all annotations and semantic meaning**
4. Verify fixed code still has heavy annotations
5. Re-verify embedding distance after fix (should still be ≤5%)
6. Re-execute with solver

**Critical Requirements for Fixes:**
- **Preserve all natural language annotations/comments**
- **Maintain heavy annotation density**
- Fix only the specific syntax/logic errors identified by solver
- Do not remove or simplify annotations
- Entire fixed file must still be suitable for embedding comparison

**Success Criteria:**
- Solver executes without errors
- Returns valid result (`sat`, `unsat`, or `unknown`)
- All annotations preserved in fixed code
- Code remains semantically equivalent to source (re-check embedding if fixed)

**Output on Success:**
When solver execution succeeds, return:
1. **Check-sat Result:** `sat`, `unsat`, or `unknown`
2. **Model (if sat):** Variable assignments from `get-model` (optional)
3. **Unsat Core (if unsat):** Minimal unsatisfiable subset from `get-unsat-core` (optional)
4. **Annotated SMT-LIB Code:** The complete annotated SMT-LIB file that was successfully executed

This allows downstream consumers to:
- Use the sat/unsat/unknown result for decision-making
- Inspect the model to understand satisfying assignments
- Analyze unsat core to identify conflicting constraints
- Reference the annotated code for understanding and documentation
- Re-execute the code with different solvers or parameters
- Trace back from result to original natural language source

## Complete Flow Diagram

```mermaid
flowchart LR
    subgraph Input
        A[Informal Natural<br/>Language Text]
    end

    subgraph "Step 1: Formalization Loop"
        B[Formalize Text]
        C{Check Similarity<br/>≥ 91%?}
        B --> C
        C -->|No| B
    end

    subgraph "Step 2: Extraction Loop"
        D[Extract to SMT-LIB<br/>with Annotations]
        E{Check Degradation<br/>≤ 5%?}
        D --> E
        E -->|No| D
    end

    subgraph "Step 3: Validation Loop"
        G[Execute with<br/>SMT Solver]
        H{Solver Success?}
        I[LLM Fix Errors]
        G --> H
        H -->|Error| I
        I --> G
    end

    subgraph Output
        F[Valid Executable<br/>SMT-LIB]
    end

    A --> B
    C -->|Yes| D
    E -->|Yes| G
    H -->|Yes| F
```

## Metrics and Thresholds

### Empirical Baselines (from hypothesis verification)

| Metric | Mean | Std Dev | Min | Max | Threshold |
|--------|------|---------|-----|-----|-----------|
| Slight Formalization (A→B) | 91.5% | 1.9% | 88.4% | 94.6% | ≥ 91% |
| High Formalization (A→B2) | 79.1% | 2.0% | 76.2% | 83.3% | ❌ Too aggressive |
| Information Loss (1-2 sentences) | ~5.0% | 2.2% | - | - | ≤ 5% baseline |
| Iterative Drift (A→B→C) | 2.7% | 2.4% | - | - | Monitor |

### Decision Matrix

```mermaid
---
config:
    layout: elk
---
flowchart LR
    A[Calculate Similarity] --> B{Step Type?}

    B -->|Step 1:<br/>Formalization| C{Similarity ≥ 91%?}
    C -->|Yes| D[✓ Accept: Meaning preserved]
    C -->|No| E[❌ Reject: Semantic drift]

    B -->|Step 2:<br/>Extraction| F{Degradation ≤ 5%?}
    F -->|Yes| G[✓ Accept: Complete extraction]
    F -->|No| H[❌ Reject: Information missing]
```

## Implementation Considerations

### 1. Performance Optimizations

**Critical: Store Source Embeddings in Variable**

Since source text doesn't change during retry loops, compute embedding once and store in variable:

```python
# Step 1: Store NL embedding in variable
embedding_nl = embed(nl_text)  # Compute ONCE before loop

for attempt in retries:
    fl_text = formalize(nl_text)
    embedding_fl = embed(fl_text)  # Only compute new embedding
    similarity = cosine_similarity(embedding_nl, embedding_fl)

# Step 2: Store FL embedding in variable
embedding_fl = embed(fl_text)  # Compute ONCE before loop

for attempt in retries:
    smt_lib_code = extract_to_smtlib(fl_text)  # Heavily annotated
    embedding_smt = embed(smt_lib_code)  # Embed entire file
    degradation = 1.0 - cosine_similarity(embedding_fl, embedding_smt)
```

**Performance Impact:**
- **Step 1** with 3 retries: Compute 4 embeddings instead of 6 (33% reduction)
- **Step 2** with 5 retries: Compute 6 embeddings instead of 10 (40% reduction)
- Each embedding computation is ~100-200ms, so significant time savings

**Additional Optimizations:**
1. **Batch Processing:** Process multiple texts in parallel
2. **Persistent Cache:** Cache embeddings across pipeline runs for identical texts (requires actual cache structure)
3. **Early Exit:** Stop retries as soon as threshold is met
4. **GPU Acceleration:** Use CUDA for embedding model if available

### 2. Embedding Model

**Recommendation:** `sentence-transformers/all-MiniLM-L6-v2`
- **Pros:** Fast, local, no API needed, consistent results
- **Cons:** Fixed model version required for reproducible thresholds

### 3. SMT Solver Configuration

**Recommended Solvers:**
- **Z3:** Microsoft's SMT solver (most commonly used, excellent documentation)
- **CVC5:** Alternative solver with good performance
- **Support for SMT-LIB v2.6+**

**Solver Execution:**
```python
import subprocess
from dataclasses import dataclass
from typing import Optional

@dataclass
class SolverResult:
    """Result from SMT solver execution."""
    success: bool
    check_sat_result: str  # "sat", "unsat", "unknown", or error message
    model: Optional[str] = None  # Model output from get-model (if sat)
    unsat_core: Optional[str] = None  # Unsat core (if unsat and requested)
    raw_output: str = ""  # Complete solver output

def execute_smt_solver(
    smt_lib_code: str,
    solver="z3",
    timeout_seconds=30,
    get_model=True,
    get_unsat_core=False
) -> SolverResult:
    """
    Execute SMT-LIB code with solver and optionally retrieve model/unsat-core.

    Args:
        smt_lib_code: Complete SMT-LIB file content
        solver: Solver to use ("z3" or "cvc5")
        timeout_seconds: Max execution time
        get_model: Whether to call (get-model) if sat
        get_unsat_core: Whether to call (get-unsat-core) if unsat

    Returns:
        SolverResult with check-sat result and optional model/core
    """
    try:
        # Ensure options are set for model/core generation
        code_with_options = smt_lib_code
        if get_model and "(set-option :produce-models true)" not in smt_lib_code:
            code_with_options = "(set-option :produce-models true)\n" + code_with_options
        if get_unsat_core and "(set-option :produce-unsat-cores true)" not in smt_lib_code:
            code_with_options = "(set-option :produce-unsat-cores true)\n" + code_with_options

        result = subprocess.run(
            [solver, "-in"],
            input=code_with_options,
            text=True,
            capture_output=True,
            timeout=timeout_seconds,
            check=False
        )

        # Check for errors in stderr
        if result.returncode != 0 or ("error" in result.stderr.lower() and result.stderr.strip()):
            return SolverResult(
                success=False,
                check_sat_result=result.stderr or result.stdout,
                raw_output=result.stdout
            )

        output = result.stdout.strip()
        lines = output.split('\n')

        # First line should be sat/unsat/unknown
        if not lines or lines[0] not in ["sat", "unsat", "unknown"]:
            return SolverResult(
                success=False,
                check_sat_result=f"Unexpected solver output: {output}",
                raw_output=output
            )

        check_sat_result = lines[0]
        model = None
        unsat_core = None

        # Parse model if sat and get-model was called
        if check_sat_result == "sat" and get_model and "(get-model)" in smt_lib_code:
            # Model starts after "sat" line
            model = '\n'.join(lines[1:]) if len(lines) > 1 else None

        # Parse unsat-core if unsat and get-unsat-core was called
        if check_sat_result == "unsat" and get_unsat_core and "(get-unsat-core)" in smt_lib_code:
            # Unsat core starts after "unsat" line
            unsat_core = '\n'.join(lines[1:]) if len(lines) > 1 else None

        return SolverResult(
            success=True,
            check_sat_result=check_sat_result,
            model=model,
            unsat_core=unsat_core,
            raw_output=output
        )

    except subprocess.TimeoutExpired:
        return SolverResult(
            success=False,
            check_sat_result=f"Solver timeout after {timeout_seconds} seconds",
            raw_output=""
        )
    except Exception as e:
        return SolverResult(
            success=False,
            check_sat_result=f"Solver execution error: {str(e)}",
            raw_output=""
        )
```

### 4. Retry Strategy

**Step 1 (Formalization):**
```python
# Store source embedding in variable (compute once, reuse in loop)
embedding_source = embed(informal_text)

max_retries = 3
for attempt in range(max_retries):
    formal_text = llm.formalize(informal_text, temperature=0.3 + attempt*0.1)
    embedding_formal = embed(formal_text)
    similarity = cosine_similarity(embedding_source, embedding_formal)
    if similarity >= 0.91:
        return formal_text
raise FormalizationFailure("Could not preserve semantics")
```

**Step 2 (Extraction):**
```python
# Store formal text embedding in variable (compute once, reuse in loop)
embedding_formal = embed(formal_text)

max_retries = 5
for attempt in range(max_retries):
    smt_lib_code = llm.extract_to_smtlib(
        formal_text,
        annotation_density="heavy",  # Force detailed annotations
        detail_level=min(1.0, 0.6 + attempt*0.1)
    )
    # Use entire SMT-LIB file (code + annotations) for embedding
    embedding_smt = embed(smt_lib_code)
    degradation = 1.0 - cosine_similarity(embedding_formal, embedding_smt)
    if degradation <= 0.05:
        return smt_lib_code
raise ExtractionIncomplete("Missing information in extraction")
```

**Step 3 (Solver Validation):**
```python
max_retries = 3
for attempt in range(max_retries):
    result = execute_smt_solver(
        smt_lib_code,
        solver="z3",
        timeout_seconds=30,
        get_model=True,
        get_unsat_core=False  # Optional: enable if needed
    )

    if result.success:
        # Return solver result with model/core and validated SMT-LIB code
        return {
            "check_sat_result": result.check_sat_result,  # "sat", "unsat", "unknown"
            "model": result.model,  # Variable assignments (if sat)
            "unsat_core": result.unsat_core,  # Conflicting constraints (if unsat)
            "smt_lib_code": smt_lib_code,  # Complete annotated code
            "attempts": attempt + 1
        }

    # Solver failed - use LLM to fix errors
    fixed_code = llm.fix_smt_errors(
        smt_lib_code=smt_lib_code,
        error_message=result.check_sat_result,  # Error message from solver
        instruction="Fix the syntax/logic errors while preserving ALL annotations and semantic meaning"
    )

    # Verify annotations still present and embedding distance maintained
    if not has_heavy_annotations(fixed_code):
        raise ValidationError("LLM removed annotations during fix")

    # Optional: Re-verify embedding distance if significant changes made
    embedding_fixed = embed(fixed_code)
    if 1.0 - cosine_similarity(embedding_formal, embedding_fixed) > 0.05:
        raise ValidationError("Fix changed semantic meaning beyond threshold")

    smt_lib_code = fixed_code  # Use fixed code for next iteration

raise SolverValidationFailure("Could not produce valid SMT-LIB after retries")
```

### 4. SMT-LIB Embedding Preparation

No special processing needed - use the entire SMT-LIB file as-is for embedding:
```python
def prepare_smtlib_for_embedding(smt_lib_code: str) -> str:
    """
    Prepare SMT-LIB code for embedding comparison.

    Since SMT-LIB is heavily annotated with natural language comments,
    we can use the entire file directly for embedding.

    Args:
        smt_lib_code: Complete SMT-LIB file with annotations

    Returns:
        The same SMT-LIB code (no processing needed)
    """
    return smt_lib_code  # Use entire file: comments + code
```

**Why this works:**
- Annotated SMT-LIB is human-readable text
- Comments provide natural language context
- Symbolic assertions (e.g., `(>= num_guards 1)`) are self-documenting
- Embedding models handle mixed format well

### 5. Monitoring and Logging

```python
@dataclass
class PipelineMetrics:
    # Step 1
    formalization_attempts: int
    final_formalization_similarity: float

    # Step 2
    extraction_attempts: int
    final_extraction_degradation: float

    # Step 3
    solver_validation_attempts: int
    solver_execution_time_seconds: float
    solver_result: str  # "sat", "unsat", "unknown"

    # Overall
    total_time_seconds: float
    success: bool
```

## Failure Modes and Handling

### Failure Mode 1: Formalization Changes Meaning

**Detection:** `similarity(A, B) < 0.91`

**Causes:**
- LLM over-formalizes and changes semantics
- Important context stripped during formalization
- Ambiguity resolved incorrectly

**Mitigation:**
1. Adjust temperature (increase randomness)
2. Provide more context in prompt
3. Request "minimal formalization"
4. Manual review if retries exhausted

### Failure Mode 2: Incomplete Extraction

**Detection:** `degradation(B, C_smtlib) > 0.05`

**Causes:**
- Facts/constraints missed during extraction
- Annotations too brief or vague
- Complex relationships not captured in symbolic form
- SMT-LIB code lacks sufficient natural language context

**Mitigation:**
1. Increase detail level in extraction prompt
2. Request heavier annotation density
3. Cross-reference source text sections
4. Manual review of missing information

### Failure Mode 3: False Positives (Low Degradation, Actually Incomplete)

**Detection:** Requires additional validation beyond embedding distance

**Causes:**
- Annotations paraphrase without capturing actual assertions
- SMT-LIB assertions don't match their comments
- Generic annotations that sound complete but are vague
- Missing symbolic assertions compensated by verbose comments

**Mitigation:**
1. Validate SMT-LIB can execute/parse correctly (Step 3 catches this)
2. Cross-check assertion count vs source text complexity
3. Verify each assertion has corresponding annotation
4. Human spot-check on sample extractions

### Failure Mode 4: SMT Solver Execution Errors

**Detection:** `execute_smt_solver()` returns `success=False`

**Causes:**
- **Syntax Errors:** Invalid SMT-LIB syntax, malformed expressions, typos
- **Type Errors:** Incorrect types in assertions (e.g., comparing Real to Bool)
- **Undefined Symbols:** Variables used but not declared
- **Logic Violations:** Constraints that violate the specified logic
- **Timeout:** Solver cannot complete within timeout period

**Mitigation:**
1. LLM fixes errors while preserving annotations
2. Verify annotations not removed during fix
3. Re-check embedding distance after fix (≤5%)
4. Limit retry attempts (max 3)
5. Manual review if all retries fail

**Special Consideration:**
When LLM fixes errors, it may be tempted to simplify code by removing "unnecessary" annotations. Explicitly instruct LLM to preserve ALL annotations and re-verify their presence after fix.

## Quality Assurance

### Automated Validation

```mermaid
flowchart TD
    A[Annotated SMT-LIB] --> B{Embedding Check<br/>≤ 5% degradation?}
    B -->|No| C[❌ Fail: Incomplete]
    B -->|Yes| D{SMT Solver<br/>Executes?}
    D -->|No| E[❌ Fail: Solver Error]
    D -->|Yes| F{Heavy Annotations<br/>Present?}
    F -->|No| G[❌ Fail: Missing Comments]
    F -->|Yes| H{Solver Returns<br/>sat/unsat/unknown?}
    H -->|No| I[❌ Fail: Invalid Result]
    H -->|Yes| J[✓ Pass All Checks]
```

### Manual Review Triggers

Require human review when:
1. Formalization required > 3 attempts
2. Extraction required > 5 attempts
3. Solver validation required > 2 attempts
4. Final degradation > 4% (close to threshold)
5. Source text > 2000 words
6. SMT-LIB > 100 assertions
7. Solver timeout occurred
8. Solver returned unexpected output (not sat/unsat/unknown)

## Integration Points

### Input Interface

```python
from typing import Tuple

def process_informal_text(
    informal_text: str,
    embedding_model: SentenceTransformer
) -> Tuple[str, PipelineMetrics]:
    """
    Process informal text through formalization and SMT-LIB extraction.

    Args:
        informal_text: Source natural language text
        embedding_model: Pre-loaded sentence transformer model

    Returns:
        (smt_lib_code, metrics)
        Where smt_lib_code is the complete annotated SMT-LIB file

    Raises:
        FormalizationFailure: If Step 1 fails after retries
        ExtractionIncomplete: If Step 2 fails after retries
    """
    pass
```

### Output Format

```python
@dataclass
class VerifiedOutput:
    """Output from the complete pipeline."""

    # Original
    informal_text: str

    # Step 1 output
    formal_text: str
    formalization_similarity: float

    # Step 2 output
    smt_lib_code: str  # Entire SMT-LIB file with heavy annotations
    extraction_degradation: float

    # Step 3 output
    check_sat_result: str  # "sat", "unsat", or "unknown"
    model: Optional[str]  # Variable assignments (if sat and requested)
    unsat_core: Optional[str]  # Conflicting constraints (if unsat and requested)
    solver_success: bool  # Whether solver executed without errors
    solver_attempts: int  # Number of fix attempts needed

    # Metrics
    metrics: PipelineMetrics

    # Validation
    passed_all_checks: bool
    requires_manual_review: bool
```

## Directory Structure

```
hypotheses/
├── embedding-distance/
│   ├── README.md                    # Hypothesis documentation
│   ├── PIPELINE-DESIGN.md          # This document
│   ├── verify_embedding_distance.py # Hypothesis verification script
│   ├── requirements.txt
│   └── .env
│
└── (future: formalization-pipeline/)
    ├── README.md
    ├── pipeline.py                  # Main pipeline implementation
    ├── formalization.py             # Step 1: Formalization
    ├── extraction.py                # Step 2: SMT-LIB extraction
    ├── verification.py              # Embedding distance checks
    ├── types.py                     # Type definitions
    └── tests/
        ├── test_formalization.py
        ├── test_extraction.py
        └── test_integration.py
```

## References

1. **Hypothesis Verification:** `hypotheses/embedding-distance/README.md`
2. **Empirical Test Results:** Run `python3 verify_embedding_distance.py --runs 20`
3. **Embedding Model:** [sentence-transformers/all-MiniLM-L6-v2](https://huggingface.co/sentence-transformers/all-MiniLM-L6-v2)

## Future Enhancements

1. **Adaptive Thresholds:** Learn thresholds per text domain
2. **Multi-Model Ensemble:** Use multiple embedding models for robustness
3. **Partial Extraction:** Allow incremental extraction with cumulative degradation tracking
4. **Semantic Clustering:** Group related facts for better SMT-LIB organization
5. **Interactive Mode:** Allow human intervention during loops for complex cases
