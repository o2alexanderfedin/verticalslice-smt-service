# Implementation Prompt: Fix SMT Validation Error

## Context

Root cause has been identified and documented in `investigations/smt-validation-error-root-cause.md`.

**Problem:** LLM adds explanatory preambles (like "Here is the fixed SMT-LIB code:") in the error fixing step, causing cvc5 parser to fail with `Expected EOF_TOK or LPAREN_TOK, got 'Here'`.

**Solution:** Implement defense-in-depth approach:
1. Update `ERROR_FIXING_PROMPT` to use XML tags
2. Add post-processing to extract pure SMT-LIB code
3. Use TDD throughout (RED → GREEN → REFACTOR)

## Objective

Implement the fix using Test-Driven Development to ensure SMT error fixing produces valid, parseable code.

## TDD Implementation Steps

### Phase 1: RED (Write Failing Tests)

Create `tests/unit/shared/test_smtlib_utils.py`:

```python
"""Tests for SMT-LIB code extraction utilities."""
import pytest


class TestExtractSmtlibCode:
    """Test cases for extracting pure SMT-LIB code from mixed output."""

    def test_pure_code_unchanged(self):
        """Pure SMT-LIB code passes through unchanged."""
        code = "; comment\n(set-logic QF_LIA)\n(check-sat)"
        from src.shared.smtlib_utils import extract_smtlib_code
        assert extract_smtlib_code(code) == code

    def test_extract_with_preamble(self):
        """Extract code when LLM adds preamble."""
        output = "Here is the fixed code:\n\n; comment\n(set-logic QF_LIA)\n(check-sat)"
        expected = "; comment\n(set-logic QF_LIA)\n(check-sat)"
        from src.shared.smtlib_utils import extract_smtlib_code
        assert extract_smtlib_code(output) == expected

    def test_extract_with_xml_tags(self):
        """Extract from XML tags."""
        output = "<smtlib>\n; comment\n(set-logic QF_LIA)\n(check-sat)\n</smtlib>"
        expected = "; comment\n(set-logic QF_LIA)\n(check-sat)"
        from src.shared.smtlib_utils import extract_smtlib_code
        assert extract_smtlib_code(output) == expected

    def test_extract_from_markdown(self):
        """Extract from markdown code blocks."""
        output = "```smtlib\n; comment\n(set-logic QF_LIA)\n(check-sat)\n```"
        expected = "; comment\n(set-logic QF_LIA)\n(check-sat)"
        from src.shared.smtlib_utils import extract_smtlib_code
        assert extract_smtlib_code(output) == expected

    def test_extract_with_preamble_and_postamble(self):
        """Extract code between preamble and postamble."""
        output = """Here is the corrected SMT-LIB code:

; comment
(set-logic QF_LIA)
(check-sat)

Let me know if you need any other changes!"""
        expected = "; comment\n(set-logic QF_LIA)\n(check-sat)"
        from src.shared.smtlib_utils import extract_smtlib_code
        result = extract_smtlib_code(output)
        # Normalize whitespace for comparison
        assert result.strip() == expected.strip()

    def test_extract_mixed_xml_and_preamble(self):
        """Extract from XML tags even with preamble."""
        output = "Sure! <smtlib>; comment\n(set-logic QF_LIA)</smtlib>"
        expected = "; comment\n(set-logic QF_LIA)"
        from src.shared.smtlib_utils import extract_smtlib_code
        assert extract_smtlib_code(output) == expected

    def test_code_starting_with_paren(self):
        """Extract code starting with open paren (no comment)."""
        output = "Here you go:\n\n(set-logic QF_LIA)\n(check-sat)"
        expected = "(set-logic QF_LIA)\n(check-sat)"
        from src.shared.smtlib_utils import extract_smtlib_code
        assert extract_smtlib_code(output) == expected

    def test_fallback_for_unrecognized_format(self):
        """Return original if no valid SMT-LIB detected."""
        output = "This is just text with no SMT-LIB code"
        from src.shared.smtlib_utils import extract_smtlib_code
        # Should return as-is (will fail at cvc5 parser, but that's expected)
        assert extract_smtlib_code(output) == output
```

**Run tests (should FAIL):**
```bash
python3 -m pytest tests/unit/shared/test_smtlib_utils.py -v
```

### Phase 2: GREEN (Implement to Pass Tests)

Create `src/shared/smtlib_utils.py`:

```python
"""Utilities for working with SMT-LIB code."""
import re


def extract_smtlib_code(llm_output: str) -> str:
    """Extract pure SMT-LIB code from potentially mixed LLM output.

    Handles multiple output formats:
    - XML tags: <smtlib>CODE</smtlib>
    - Markdown: ```smtlib CODE ```
    - Preambles: "Here is..." + CODE
    - Pure code: CODE (passes through unchanged)

    Args:
        llm_output: Raw output from LLM that may contain explanatory text

    Returns:
        Pure SMT-LIB code suitable for parsing by cvc5

    Examples:
        >>> extract_smtlib_code("; comment\\n(set-logic QF_LIA)")
        '; comment\\n(set-logic QF_LIA)'

        >>> extract_smtlib_code("<smtlib>; code</smtlib>")
        '; code'

        >>> extract_smtlib_code("Here is the code:\\n\\n; comment\\n(check-sat)")
        '; comment\\n(check-sat)'
    """
    # Strategy 1: Try XML tags first (most explicit)
    if "<smtlib>" in llm_output and "</smtlib>" in llm_output:
        start_idx = llm_output.index("<smtlib>") + len("<smtlib>")
        end_idx = llm_output.index("</smtlib>")
        return llm_output[start_idx:end_idx].strip()

    # Strategy 2: Try markdown code blocks
    if "```" in llm_output:
        # Match ```smtlib or ``` followed by code
        code_block_pattern = r"```(?:smtlib)?\s*\n(.*?)\n```"
        match = re.search(code_block_pattern, llm_output, re.DOTALL)
        if match:
            return match.group(1).strip()

    # Strategy 3: Find first valid SMT-LIB line (starts with ; or ()
    lines = llm_output.split("\n")
    code_start_idx = None

    for i, line in enumerate(lines):
        stripped = line.strip()
        # Valid SMT-LIB starts with comment or S-expression
        if stripped and (stripped.startswith(";") or stripped.startswith("(")):
            code_start_idx = i
            break

    if code_start_idx is not None:
        # Take from first valid line to end
        code_lines = lines[code_start_idx:]

        # Trim trailing empty lines or common postambles
        while code_lines:
            last_line = code_lines[-1].strip().lower()
            # Remove common postambles
            if (
                not last_line
                or last_line.startswith("let me know")
                or last_line.startswith("hope this helps")
                or last_line.startswith("is there anything")
            ):
                code_lines.pop()
            else:
                break

        return "\n".join(code_lines)

    # Fallback: return as-is (will likely fail at parser, but that's expected)
    return llm_output
```

**Run tests (should PASS):**
```bash
python3 -m pytest tests/unit/shared/test_smtlib_utils.py -v
```

### Phase 3: REFACTOR (Update ERROR_FIXING_PROMPT)

Modify `src/infrastructure/llm/prompts.py`:

**Before (lines 154-170):**
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

**After:**
```python
ERROR_FIXING_PROMPT = """You are an expert in SMT-LIB syntax. Fix the code and respond with ONLY the fixed code inside <smtlib></smtlib> tags.

CRITICAL RESPONSE FORMAT:
- Start your response IMMEDIATELY with <smtlib>
- Put the fixed SMT-LIB code inside the tags
- End with </smtlib>
- Do NOT add any text before or after the tags
- Do NOT use markdown code blocks
- Do NOT add explanations

FIXING REQUIREMENTS:
1. Fix the syntax or semantic error shown below
2. Preserve ALL comments and annotations exactly as they are
3. Do NOT change the logic or constraints (only fix the error)
4. Ensure output is valid SMT-LIB 2.6 syntax

ORIGINAL CODE:
{smt_code}

ERROR:
{error_message}

RESPOND NOW WITH <smtlib>YOUR_FIXED_CODE_HERE</smtlib>:"""
```

### Phase 4: Integration (Update fix_smt_errors)

Modify `src/infrastructure/llm/client.py` in the `fix_smt_errors` method (around line 271-318):

**Find the return statement (line 306-313):**
```python
            fixed_code = message.content[0].text

            logger.info(
                f"Error fix complete: "
                f"input_length={len(smt_code)}, "
                f"output_length={len(fixed_code)}"
            )

            return fixed_code
```

**Replace with:**
```python
            raw_output = message.content[0].text

            # CRITICAL: Extract pure SMT-LIB code from potentially mixed output
            # LLMs may add preambles like "Here is..." despite instructions
            from src.shared.smtlib_utils import extract_smtlib_code

            fixed_code = extract_smtlib_code(raw_output)

            logger.info(
                f"Error fix complete: "
                f"raw_output_length={len(raw_output)}, "
                f"extracted_code_length={len(fixed_code)}"
            )

            return fixed_code
```

### Phase 5: Verification

**Test 1: Unit tests pass**
```bash
python3 -m pytest tests/unit/shared/test_smtlib_utils.py -v
```

**Test 2: All existing tests pass**
```bash
python3 -m pytest tests/unit/ -v
```

**Test 3: Linters pass**
```bash
python3 -m black src/ tests/ --check
python3 -m ruff check src/ tests/
python3 -m mypy src/
```

**Test 4: Production input succeeds**
```bash
curl -X POST http://localhost:8000/pipeline/process \
  -H "Content-Type: application/json" \
  --data @/tmp/test_enrich_true.json | jq '.'
```

Should return SUCCESS instead of validation error.

## Git Workflow (TDD Cycle)

**Commit 1: RED (Tests)**
```bash
git add tests/unit/shared/test_smtlib_utils.py
git commit -m "test: add tests for SMT-LIB code extraction from mixed output

- Test pure code passes through unchanged
- Test extraction with preambles (\"Here is...\")
- Test extraction from XML tags
- Test extraction from markdown blocks
- Test handling of mixed formats and postambles

Part of TDD cycle to fix SMT validation error (RED phase).

Related: investigations/smt-validation-error-root-cause.md"
```

**Commit 2: GREEN (Implementation)**
```bash
git add src/shared/smtlib_utils.py
git add src/infrastructure/llm/client.py
git commit -m "feat: extract pure SMT-LIB code from LLM output to fix validation errors

Implements defensive extraction to handle LLM adding explanatory text:
- Tries XML tags first (<smtlib>CODE</smtlib>)
- Falls back to markdown blocks
- Falls back to finding first valid SMT-LIB line
- Trims common preambles and postambles

Fixes production error: \"Expected EOF_TOK or LPAREN_TOK, got 'Here'\"
Root cause: ERROR_FIXING_PROMPT output contained preambles

Part of TDD cycle (GREEN phase).

Fixes: #SMT-VALIDATION-ERROR"
```

**Commit 3: REFACTOR (Prompt Improvement)**
```bash
git add src/infrastructure/llm/prompts.py
git commit -m "refactor: improve ERROR_FIXING_PROMPT with XML tags for clearer output

Updated prompt to explicitly request <smtlib></smtlib> tags:
- More explicit instructions about response format
- Stronger emphasis on NO preambles or postambles
- Clearer separation of requirements and format

Part of TDD cycle (REFACTOR phase). Works in tandem with
extraction utility for defense-in-depth.

Related: commit feat: extract pure SMT-LIB code"
```

## Success Criteria

- [ ] All new tests pass (test_smtlib_utils.py)
- [ ] All existing 232+ tests pass
- [ ] Black formatting passes
- [ ] Ruff linting passes
- [ ] Mypy type checking passes
- [ ] Production input test succeeds locally
- [ ] 3 commits following TDD cycle (RED → GREEN → REFACTOR)

## Technical Constraints

- **MUST** use TDD approach (tests first)
- **MUST** maintain backwards compatibility
- **MUST** pass all existing tests
- **MUST** follow SOLID principles (especially SRP for extraction utility)
- **DO NOT** modify cvc5 executor or validation logic
- **DO NOT** change API contracts

## Files to Create/Modify

**Create:**
1. `src/shared/smtlib_utils.py` - Extraction utility
2. `tests/unit/shared/test_smtlib_utils.py` - Test suite

**Modify:**
3. `src/infrastructure/llm/prompts.py` - Update ERROR_FIXING_PROMPT (line 154-170)
4. `src/infrastructure/llm/client.py` - Use extraction in fix_smt_errors() (line 306-313)

## Expected Outcome

After implementation:
1. Production input that previously failed now succeeds
2. Error fixing step produces clean SMT-LIB code
3. cvc5 parser accepts the output without "got `Here`" errors
4. All tests pass (existing + new)
5. Code is well-typed, linted, and formatted

## Notes

- Root cause analysis in `investigations/smt-validation-error-root-cause.md`
- Test files ready at `/tmp/test_enrich_true.json` and `/tmp/test_enrich_false.json`
- Local server should be running on port 8000 for manual testing
- Focus on clean, simple implementation following SOLID principles
