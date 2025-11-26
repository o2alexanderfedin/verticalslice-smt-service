# SMT Validation Error Root Cause Analysis

**Date:** 2025-11-25
**Investigator:** Claude Code
**Incident:** Production API returning "Expected EOF_TOK or LPAREN_TOK, got `Here` (SYMBOL)"

## Summary

The SMT validation error is caused by the **ERROR_FIXING_PROMPT** adding explanatory preambles (like "Here is the fixed SMT-LIB code:") when the LLM is asked to fix syntax errors. The cvc5 parser expects pure SMT-LIB syntax and rejects any text before the actual code.

## Investigation Timeline

### Step 1: Reproduction (✓ SUCCESSFUL)
- Started local server with proper environment
- Tested with exact production input: "Stainless steel rod with the length of 100' expands less than by 15\" at the temperature 500 Celcius"
- **Result:** Successfully reproduced error in ~92 seconds with `enrich=true`

### Step 2: Isolation Test (✓ KEY FINDING)
- Tested same input with `enrich=false`
- **Result:** ERROR STILL OCCURS with `enrich=false`
- **Conclusion:** Enrichment is NOT the root cause - problem is in extraction or validation step

### Step 3: Log Analysis (✓ ROOT CAUSE IDENTIFIED)
Analyzed `/tmp/uvicorn.log` and found the error pattern:

```
2025-11-25 22:20:08 - src.domain.steps.extraction - WARNING - Extraction did not meet threshold after 5 attempts. Using best result with degradation: 0.2665 (max: 0.05)
2025-11-25 22:20:08 - src.application.pipeline_service - INFO - === Step 3: Validation ===
2025-11-25 22:20:08 - src.infrastructure.smt.cvc5_executor - ERROR - cvc5 execution error: Error finding token
2025-11-25 22:20:08 - src.domain.steps.validation - WARNING - Attempt 1 failed with error: Error finding token
2025-11-25 22:20:15 - src.infrastructure.llm.client - INFO - Error fix complete: input_length=3228, output_length=3290
2025-11-25 22:20:15 - src.infrastructure.smt.cvc5_executor - ERROR - cvc5 execution error: Expected EOF_TOK or LPAREN_TOK, got `Here` (SYMBOL).
2025-11-25 22:20:15 - src.domain.steps.validation - WARNING - Attempt 2 failed with error: Expected EOF_TOK or LPAREN_TOK, got `Here` (SYMBOL).
```

**Key Observations:**
1. Initial extraction completes successfully (no "Here" error)
2. Validation step finds syntax error: "Error finding token"
3. Error fixing is called via `fix_smt_errors()`
4. **CRITICAL:** After error fixing, cvc5 fails with "got `Here`"
5. This indicates the LLM is adding preamble text like "Here is the fixed SMT-LIB code:"

## Root Cause

**File:** `src/infrastructure/llm/prompts.py:154-170`
**Prompt:** `ERROR_FIXING_PROMPT`

### Current Prompt (Line 154-170)
```python
ERROR_FIXING_PROMPT = """You are an expert in SMT-LIB syntax and semantics. Your task is to fix errors in SMT-LIB code while preserving all annotations and comments.

**Task**: Fix the following SMT-LIB code that produced an error.

**Requirements**:
1. Fix the syntax or semantic error
2. Preserve ALL comments and annotations
3. Do NOT change the logic or constraints (only fix errors)
4. Ensure the output is valid SMT-LIB 2.6 syntax

**Original SMT-LIB Code**:
{smt_code}

**Error Message**:
{error_message}

**Your Fixed SMT-LIB Code** (respond with ONLY the corrected code, preserving all comments):"""
```

### Problem
Despite the instruction `"respond with ONLY the corrected code"`, the LLM is adding explanatory preambles:
- "Here is the fixed SMT-LIB code:"
- "I've corrected the SMT-LIB code:"
- Similar variations

The cvc5 parser expects the code to start with either:
- `;` (comment)
- `(` (S-expression)

Any other text causes `Expected EOF_TOK or LPAREN_TOK` error.

## Why This Happens

LLMs are trained to be helpful and conversational. Even with explicit instructions like "respond with ONLY", they often add:
- Preambles ("Here is...")
- Explanations ("I've fixed...")
- Markdown formatting ("```smtlib")
- Postambles ("Let me know if...")

This is a known LLM behavior pattern that requires:
1. **Stronger prompt engineering** (XML tags, explicit delimiters)
2. **Post-processing** (extraction of code from mixed output)
3. **Both** for robustness

## Evidence Chain

1. **Timeline Analysis:**
   - Extraction attempts 1-5: All complete successfully
   - Validation attempt 1: First syntax error detected
   - Error fixing called: LLM generates "fixed" code
   - Validation attempt 2: "got `Here`" error appears

2. **Log Pattern:**
   - EVERY occurrence of "got `Here`" follows an "Error fix complete" log
   - NEVER occurs on initial extraction attempts
   - Happens consistently regardless of `enrich` setting

3. **Error Message:**
   - `Expected EOF_TOK or LPAREN_TOK, got 'Here' (SYMBOL).`
   - The word "Here" is NEVER part of valid SMT-LIB syntax
   - This is clearly from explanatory text like "Here is..."

## Impact Assessment

**Severity:** HIGH
**Frequency:** Every request that requires error fixing
**User Impact:** Complete pipeline failure when extraction produces syntactically invalid SMT-LIB

**Affected Scenarios:**
- Complex inputs that produce initial syntax errors
- Inputs requiring multiple validation attempts
- Both enriched and non-enriched requests

**Unaffected Scenarios:**
- Simple inputs where extraction produces valid SMT-LIB on first attempt
- Inputs where validation succeeds without error fixing

## Solution Design

### Option 1: Improved Prompt Engineering (RECOMMENDED)
**Approach:** Use XML tags to clearly delimit code output

**New Prompt Structure:**
```python
ERROR_FIXING_PROMPT = """Fix the SMT-LIB code and respond ONLY with the fixed code inside XML tags.

CRITICAL INSTRUCTIONS:
- Do NOT add any explanatory text before or after the code
- Do NOT use markdown code blocks
- Start your response IMMEDIATELY with <smtlib>
- End your response with </smtlib>
- Everything between tags must be valid SMT-LIB syntax only

Original Code:
{smt_code}

Error:
{error_message}

Respond now with <smtlib>YOUR_FIXED_CODE_HERE</smtlib>:"""
```

**Pros:**
- Addresses root cause directly
- No code changes needed beyond prompt
- LLMs respond better to XML structure

**Cons:**
- Still relies on LLM following instructions
- May need fallback parsing

### Option 2: Post-Processing Extraction (DEFENSIVE)
**Approach:** Parse LLM output to extract pure SMT-LIB code

**Implementation:**
```python
def extract_smtlib_code(llm_output: str) -> str:
    """Extract pure SMT-LIB code from potentially mixed output.

    Handles:
    - Preambles: "Here is...", "I've fixed...", etc.
    - XML tags: <smtlib>...</smtlib>
    - Markdown: ```smtlib ... ```
    - Plain code starting with ; or (
    """
    # Try XML tags first
    if "<smtlib>" in llm_output and "</smtlib>" in llm_output:
        start = llm_output.index("<smtlib>") + len("<smtlib>")
        end = llm_output.index("</smtlib>")
        return llm_output[start:end].strip()

    # Try markdown blocks
    if "```" in llm_output:
        lines = llm_output.split("\n")
        code_lines = []
        in_code = False
        for line in lines:
            if line.strip().startswith("```"):
                in_code = not in_code
                continue
            if in_code:
                code_lines.append(line)
        if code_lines:
            return "\n".join(code_lines)

    # Find first valid SMT-LIB line
    lines = llm_output.split("\n")
    code_start_idx = None
    for i, line in enumerate(lines):
        stripped = line.strip()
        if stripped.startswith(";") or stripped.startswith("("):
            code_start_idx = i
            break

    if code_start_idx is not None:
        return "\n".join(lines[code_start_idx:])

    # Fallback: return as-is and let cvc5 error
    return llm_output
```

**Pros:**
- Defensive against LLM inconsistency
- Handles multiple output formats
- Backwards compatible

**Cons:**
- More complex code
- Could hide underlying prompt issues
- Needs comprehensive testing

### Option 3: Both Approaches (BEST)
**Approach:** Combine improved prompt + post-processing

**Why:**
- Defense in depth
- Prompt guides LLM to correct format
- Post-processing catches when LLM doesn't follow instructions
- Robust against future changes

## Recommended Implementation Plan

### Phase 1: TDD Test Creation (RED)
```python
# tests/unit/infrastructure/test_smtlib_extraction.py

def test_extract_pure_code():
    """Pure SMT-LIB code passes through unchanged."""
    code = "; comment\n(set-logic QF_LIA)"
    assert extract_smtlib_code(code) == code

def test_extract_with_preamble():
    """Extract code when LLM adds preamble."""
    output = "Here is the fixed code:\n; comment\n(set-logic QF_LIA)"
    expected = "; comment\n(set-logic QF_LIA)"
    assert extract_smtlib_code(output) == expected

def test_extract_with_xml_tags():
    """Extract from XML tags."""
    output = "<smtlib>; comment\n(set-logic QF_LIA)</smtlib>"
    expected = "; comment\n(set-logic QF_LIA)"
    assert extract_smtlib_code(output) == expected

def test_extract_from_markdown():
    """Extract from markdown code blocks."""
    output = "```smtlib\n; comment\n(set-logic QF_LIA)\n```"
    expected = "; comment\n(set-logic QF_LIA)"
    assert extract_smtlib_code(output) == expected
```

### Phase 2: Implementation (GREEN)
1. Create `src/shared/smtlib_utils.py` with `extract_smtlib_code()`
2. Update `ERROR_FIXING_PROMPT` to use XML tags
3. Modify `src/infrastructure/llm/client.py:fix_smt_errors()` to call extraction
4. Run tests → GREEN

### Phase 3: Integration (REFACTOR)
1. Test with production input locally
2. Verify all 232+ existing tests pass
3. Run linters (black, ruff, mypy)
4. Commit with TDD workflow

## Success Criteria

- [ ] Production input succeeds locally
- [ ] All existing tests pass
- [ ] New tests cover edge cases
- [ ] Linters pass (black, ruff, mypy)
- [ ] Manual testing with various inputs
- [ ] Production deployment succeeds

## Next Steps

1. Implement extraction utility with tests (TDD RED → GREEN)
2. Update ERROR_FIXING_PROMPT with XML tags (TDD REFACTOR)
3. Run full test suite
4. Deploy to production
5. Monitor for 24h to confirm fix

## Files to Modify

1. `src/infrastructure/llm/prompts.py` - Update ERROR_FIXING_PROMPT
2. `src/shared/smtlib_utils.py` - NEW: Extraction utility
3. `src/infrastructure/llm/client.py` - Use extraction in fix_smt_errors()
4. `tests/unit/shared/test_smtlib_utils.py` - NEW: Test suite
5. `tests/integration/test_error_fixing.py` - NEW: Integration tests

## Risk Assessment

**Implementation Risk:** LOW
- Changes are isolated to error fixing flow
- Post-processing is defensive (won't break working code)
- Comprehensive test coverage

**Deployment Risk:** LOW
- Fix doesn't change API contracts
- Backwards compatible with existing behavior
- Can be quickly reverted if issues arise

**Testing Strategy:**
- Unit tests for extraction logic
- Integration tests with actual LLM calls
- Manual testing with production input
- Canary deployment monitoring
