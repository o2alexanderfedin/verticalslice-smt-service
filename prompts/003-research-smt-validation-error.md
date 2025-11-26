# Research Prompt: SMT Validation Error with Enrichment Enabled

## Context

Production API endpoint is failing SMT solver validation when `enrich: true` is used. The error message indicates the LLM is generating invalid SMT-LIB code containing explanatory text instead of pure syntax.

**Error from Production:**
```
"SMT solver validation failed after 5 attempts. Last error: Expected EOF_TOK or LPAREN_TOK, got `Here` (SYMBOL)."
```

**Test Input:**
```
Stainless steel rod with the length of 100' expands less than by 15" at the temperature 500 Celcius
```

**Request Parameters:**
```json
{
  "informal_text": "...",
  "enrich": true,
  "max_degradation": 0.05,
  "max_retries": 5
}
```

## Problem Statement

The SMT solver validation is rejecting the LLM's output because it contains text like "Here is the SMT-LIB code:" before the actual code. This violates the parser's expectations for pure SMT-LIB syntax.

The extraction prompt in `src/infrastructure/llm/prompts.py` (line 151) explicitly states:
```
Provide ONLY the complete SMT-LIB code (including all phase comments as shown above).
Structure: Phase comments + set-info + set-logic + declarations + assertions + check-sat + get-model/get-value.
NO explanatory text before/after the code block.
```

Despite this instruction, the LLM is adding explanatory preambles.

## Research Objectives

1. **Reproduce the error locally** with the exact production input
2. **Identify root cause**:
   - Is enrichment changing the LLM's behavior?
   - Is the refinement loop causing the issue?
   - Are the prompts insufficiently clear?
3. **Analyze extraction prompt effectiveness**:
   - Does the prompt need stronger constraints?
   - Should we add XML tags like `<smtlib>...</smtlib>` for clearer boundaries?
   - Should we include negative examples of what NOT to do?
4. **Examine output parsing**:
   - Do we need post-processing to strip explanatory text?
   - Should we add validation before sending to solver?
   - Can we use regex to extract SMT-LIB from mixed output?
5. **Test hypothesis**: Enrichment may be adding context that confuses the LLM

## Investigation Steps

### Step 1: Reproduce Production Error Locally

Start local server and test with exact production input:

```bash
# Ensure environment is configured
set -a && source .env && set +a

# Start server in background
python3 -m uvicorn src.main:app --host 0.0.0.0 --port 8000 2>&1 &

# Wait for startup
sleep 3

# Test with exact production input
curl -X POST http://localhost:8000/pipeline/process \
  -H "Content-Type: application/json" \
  -d '{
    "informal_text": "Stainless steel rod with the length of 100'"'"' expands less than by 15\" at the temperature 500 Celcius",
    "enrich": true,
    "max_degradation": 0.05,
    "max_retries": 5
  }' | jq '.'
```

**Expected Outcome:** Should reproduce the validation error locally.

### Step 2: Test Without Enrichment

```bash
# Same test but with enrich: false
curl -X POST http://localhost:8000/pipeline/process \
  -H "Content-Type: application/json" \
  -d '{
    "informal_text": "Stainless steel rod with the length of 100'"'"' expands less than by 15\" at the temperature 500 Celcius",
    "enrich": false,
    "max_degradation": 0.05,
    "max_retries": 5
  }' | jq '.'
```

**Expected Outcome:** If this succeeds, enrichment is likely the root cause.

### Step 3: Analyze Logs for LLM Output

Examine application logs to see:
- What the enrichment step produced
- What the extraction step received
- What SMT-LIB code was generated (including any preambles)
- Which attempt failed (first attempt vs. refinement)

```bash
# Check logs (server should be logging to stdout/stderr)
# Look for lines containing:
# - "Web search enrichment complete"
# - "Extraction complete"
# - "SMT solver validation"
```

### Step 4: Unit Test for Output Parsing

Create a test that:
1. Simulates LLM returning SMT-LIB with preamble
2. Verifies current parser fails
3. Tests potential fixes (regex extraction, XML tag parsing, etc.)

Example malformed output to test:
```
Here is the SMT-LIB code for this problem:

; === PHASE 1: PROBLEM COMPREHENSION ===
(set-logic QF_LRA)
...
```

### Step 5: Examine Extraction Step Retry Logic

Check `src/domain/steps/extraction.py:119` where `extract_to_smtlib()` is called during retries:
- Does refinement mode change LLM behavior?
- Are previous_attempt and previous_degradation causing issues?
- Should first attempt have different parsing than refinements?

### Step 6: Prompt Engineering Experiments

Test improved prompt variations:
1. Add XML tags: `Respond with <smtlib>CODE_HERE</smtlib>`
2. Add negative examples: "DO NOT start with 'Here is...'"
3. Add explicit instruction: "Start IMMEDIATELY with semicolon comments"
4. Test system message vs user message placement

### Step 7: Validation Before Solver

Add pre-validation before sending to cvc5:
```python
def is_valid_smtlib_syntax(code: str) -> bool:
    """Check if code starts with valid SMT-LIB tokens."""
    stripped = code.strip()
    # Valid start: comment (;) or open paren
    return stripped.startswith(';') or stripped.startswith('(')
```

## Deliverables

1. **Root Cause Analysis Report**:
   - Confirmed reproduction steps
   - Identification of where explanatory text is introduced
   - Hypothesis on why enrichment triggers it

2. **Proposed Solutions** (ranked by impact):
   - Option 1: Prompt engineering improvements
   - Option 2: Post-processing to extract SMT-LIB from mixed output
   - Option 3: Pre-validation before solver
   - Option 4: Different LLM parameters for enrichment vs extraction

3. **Test Cases**:
   - Unit tests for parsing malformed output
   - Integration test with production input
   - Regression tests to ensure fix doesn't break existing functionality

4. **Implementation Plan**:
   - If prompt fix: Updated prompt template with justification
   - If parser fix: Regex or XML parsing logic
   - If validation fix: Pre-validation function
   - All with TDD approach (tests first)

## Success Criteria

1. Production input reproduces locally ✓
2. Root cause identified ✓
3. Fix implemented and tested ✓
4. All 232+ existing tests still pass ✓
5. New tests cover edge cases ✓
6. Production deployment succeeds ✓

## Technical Constraints

- **DO NOT** change SMT-LIB validation logic (it's correct)
- **DO NOT** modify cvc5 executor (solver integration is working)
- **DO** preserve semantic verification (degradation checks)
- **DO** maintain backward compatibility (enrich: false must still work)
- **DO** follow TDD: tests before implementation
- **DO** run linters: black, ruff, mypy before commit

## Related Files

- `src/infrastructure/llm/prompts.py` - EXTRACTION_PROMPT (line 18-151)
- `src/infrastructure/llm/client.py` - extract_to_smtlib() method (line 166-264)
- `src/domain/steps/extraction.py` - ExtractionStep.execute() (line 55-188)
- `src/domain/steps/validation.py` - ValidationStep (uses cvc5)
- `src/infrastructure/smt/cvc5_executor.py` - Cvc5Executor (parser)

## SOLID Principles Application

- **SRP**: Each component has single responsibility
  - Prompts → templates only
  - Client → LLM communication only
  - Extraction → orchestration only
  - Parsing → should be separate concern
- **OCP**: Solution should be extensible (e.g., support for other output formats)
- **DIP**: High-level extraction logic shouldn't depend on output format quirks

## Git Workflow

Following TDD cycle:
1. **Commit 1**: "test: add tests for malformed SMT-LIB parsing" (RED)
2. **Commit 2**: "feat: add pre-validation and output cleaning" (GREEN)
3. **Commit 3**: "refactor: improve extraction prompt clarity" (REFACTOR)

Release: `v1.17.0 - Fix SMT validation with enrichment`

---

**Instructions for Execution:**

1. Read this prompt completely
2. Execute Steps 1-7 systematically
3. Document findings at each step
4. Propose solution based on evidence (not assumptions)
5. Implement using TDD
6. Verify with all existing tests
7. Report back with summary and next steps
