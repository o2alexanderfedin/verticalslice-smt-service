# Root Cause Analysis: Stainless Steel Thermal Expansion Validation Failure

**Date**: 2025-11-27
**Test Case**: Stainless steel rod thermal expansion constraint
**Status**: ❌ CRITICAL ISSUE IDENTIFIED

## Executive Summary

The validation failure for the stainless steel thermal expansion constraint is **NOT** due to a parse error with the word "at" as initially suspected. The actual root cause is:

### ❌ ROOT CAUSE: Logic Theory Mismatch

**Problem**: The LLM is generating SMT-LIB code that uses **uninterpreted functions** (`declare-fun thermal_expansion`) but declares the logic as **QF_LRA** (Quantifier-Free Linear Real Arithmetic), which **does not support functions of non-zero arity**.

**Error Message**:
```
Functions (of non-zero arity) cannot be declared in logic QF_LRA.
Try including UF or adding the prefix HO_.
```

## Diagnostic Test Results

### Test Execution Summary

```
Input: "Stainless steel rod with the length of 100' expands less than by 15\" at the temperature 500 Celcius"

✅ FORMALIZATION: PASSED
- Skipped (short input < 200 chars threshold)
- Output: Same as input
- Similarity: 1.0000
- Attempts: 0

✅ EXTRACTION: PASSED
- Degradation: 0.4543 (within 0.50 threshold)
- Output: 3732 characters of SMT-LIB code
- Attempts: 1

❌ VALIDATION: FAILED (cvc5 execution error)
- Error: "Functions (of non-zero arity) cannot be declared in logic QF_LRA"
- Caused segmentation fault in Python runtime
```

## Problematic SMT-LIB Code Generated

The LLM extraction step generated the following code:

```smt
(set-logic QF_LRA)

; ... declarations ...
(declare-const initial_length_inches Real)
(declare-const temperature_celsius Real)
(declare-const expansion_inches Real)

; ❌ PROBLEM: Declaring function in QF_LRA logic
(declare-fun thermal_expansion (Real Real) Real)

; Using the function
(assert (= expansion_inches (thermal_expansion initial_length_inches temperature_celsius)))

; Additional constraint with implication
(assert (=> (and (= initial_length_inches 1200.0) (= temperature_celsius 500.0))
            (and (>= (thermal_expansion initial_length_inches temperature_celsius) 0.0)
                 (< (thermal_expansion initial_length_inches temperature_celsius) 15.0))))
```

### Why This Fails

1. **QF_LRA logic** supports:
   - Quantifier-free formulas
   - Linear Real Arithmetic
   - Constants (declare-const)
   - **NOT uninterpreted functions**

2. **The code uses `declare-fun thermal_expansion`**:
   - This is an uninterpreted function with arity 2 (takes 2 Real arguments)
   - Requires **QF_UFRA** (with Uninterpreted Functions) or similar logic
   - cvc5 correctly rejects this as invalid for QF_LRA

## Why the LLM Generated This Code

### Analysis of Extraction Output

The LLM's reasoning (from comments in generated code):

```
; === PHASE 3: LOGIC SELECTION ===
; Theory Choice: QF_LRA (Quantifier-Free Linear Real Arithmetic)
; Justification:
; - Dealing with physical measurements (expansion in inches)
; - Real-valued quantities (expansion can be fractional)
; - Linear constraints (less than comparison)
; - No quantifiers needed
```

**Problem**: The LLM correctly identified that the problem uses linear real arithmetic, but then **incorrectly chose to use an uninterpreted function** to model the thermal expansion relationship.

**The LLM tried to be clever** by:
1. Using `thermal_expansion` as an uninterpreted function to link initial conditions to expansion
2. Adding implications to constrain the function's behavior
3. This is actually a more sophisticated modeling approach...
4. **But it's incompatible with the chosen logic QF_LRA**

## Correct Approaches

### Option 1: Remove Uninterpreted Function (Simplest)

The constraint doesn't actually require the thermal expansion formula - it just needs to verify if expansion < 15" is satisfiable:

```smt
(set-logic QF_LRA)

(declare-const expansion_inches Real)

; Constraint: expansion must be less than 15 inches
(assert (< expansion_inches 15.0))

; Physical constraint: expansion must be non-negative
(assert (>= expansion_inches 0.0))

(check-sat)
(get-model)
```

This trivially satisfiable (SAT with expansion_inches = 0.0 or any value < 15.0).

### Option 2: Change Logic to QF_UFRA

Keep the uninterpreted function but use a logic that supports it:

```smt
(set-logic QF_UFRA)  ; ← Changed from QF_LRA

(declare-const initial_length_inches Real)
(declare-const temperature_celsius Real)
(declare-const expansion_inches Real)

(assert (= initial_length_inches 1200.0))
(assert (= temperature_celsius 500.0))

; Now this is valid with QF_UFRA
(declare-fun thermal_expansion (Real Real) Real)
(assert (= expansion_inches (thermal_expansion initial_length_inches temperature_celsius)))

(assert (< expansion_inches 15.0))
(assert (>= expansion_inches 0.0))

(check-sat)
(get-model)
```

### Option 3: Use Actual Thermal Expansion Formula (Most Accurate)

Model the physics directly without uninterpreted functions:

```smt
(set-logic QF_NRA)  ; Non-linear due to multiplication

(declare-const initial_length Real)      ; feet
(declare-const coefficient Real)          ; thermal expansion coefficient
(declare-const temperature Real)          ; Celsius
(declare-const expansion Real)            ; inches

; Known values
(assert (= initial_length 100.0))
(assert (= coefficient 0.0000173))         ; stainless steel @ room temp
(assert (= temperature 500.0))

; Thermal expansion formula: ΔL = α * L₀ * ΔT
; Convert feet to inches (*12), assume starting from 20°C
(assert (= expansion (* coefficient (* initial_length 12.0) (- temperature 20.0))))

; Constraint: expansion < 15 inches
(assert (< expansion 15.0))

(check-sat)
(get-model)
```

## Why Initial Error Message Was Misleading

The original HTTP 422 error reported:

```
"detail": "SMT solver validation failed after 5 attempts.
Last error: Expected a RPAREN_TOK, got `at` (SYMBOL)."
```

This made it seem like a **parse error** with the word "at" from "at the temperature 500 Celcius".

**However**, this was actually the **LLM's attempted fix** generating invalid syntax. The initial error was the logic mismatch, and the LLM's fixes created new parse errors.

## Impact on Context-Rich Error Fixing

The context-rich diagnostic system we implemented would help **if the error were fixable**. However:

1. ✅ Error parsing would work: "Functions cannot be declared in logic QF_LRA"
2. ✅ Context extraction would work: Show the problematic declare-fun line
3. ✅ XML context would be provided to LLM
4. ❌ **But the fix requires changing the logic declaration, which requires understanding the entire constraint**
5. ❌ The LLM would need to either:
   - Remove the uninterpreted function entirely (major refactoring)
   - Change `(set-logic QF_LRA)` to `(set-logic QF_UFRA)` (simple but requires understanding relationship)

## Recommended Fixes

### 1. Update Extraction Prompt (PRIMARY FIX)

**File**: `src/infrastructure/llm/prompts.py`

Add explicit guidance in the `SMT_EXTRACTION_PROMPT`:

```xml
<logic_selection_rules>
  <rule priority="critical">
    NEVER use uninterpreted functions (declare-fun with arity > 0) with QF_LRA logic.
    If you need uninterpreted functions, use QF_UFRA, QF_UFLIA, or QF_UFNRA.
  </rule>

  <rule priority="high">
    For constraints that don't require computing actual values (e.g., "expansion < 15 inches"),
    prefer simple variable constraints over complex formulas or uninterpreted functions.
  </rule>

  <rule priority="high">
    Common logic choices:
    - QF_LRA: Linear real arithmetic, NO functions
    - QF_UFRA: Linear real arithmetic WITH uninterpreted functions
    - QF_NRA: Non-linear real arithmetic (for multiplication, division)
    - QF_UFNRA: Non-linear real WITH uninterpreted functions
  </rule>
</logic_selection_rules>
```

### 2. Add Logic Validation (SECONDARY FIX)

**File**: `src/domain/steps/validation.py` (or new `src/shared/smt_validators.py`)

Before attempting solver execution, validate that logic and declarations are compatible:

```python
def validate_logic_consistency(smt_code: str) -> tuple[bool, str | None]:
    """Validate that SMT-LIB code logic matches declarations.

    Returns:
        (is_valid, error_message)
    """
    # Extract logic declaration
    logic_match = re.search(r'\(set-logic\s+(\S+)\)', smt_code)
    if not logic_match:
        return True, None  # No logic set, let solver handle

    logic = logic_match.group(1)

    # Check for uninterpreted functions with non-UF logics
    has_functions = re.search(r'\(declare-fun\s+\w+\s+\([^\)]+\)', smt_code)

    if has_functions and 'UF' not in logic and 'HO' not in logic:
        return False, (
            f"Logic {logic} does not support uninterpreted functions. "
            f"Consider using QF_UFRA, QF_UFLIA, or QF_UFNRA instead."
        )

    return True, None
```

### 3. Enhance Error Fixing Prompt (TERTIARY FIX)

**File**: `src/infrastructure/llm/prompts.py`

Update `ERROR_FIXING_WITH_CONTEXT_PROMPT` to include logic mismatch detection:

```xml
<common_errors>
  <error type="logic_mismatch">
    <symptom>Error mentions "Functions cannot be declared in logic QF_*" or "Try including UF"</symptom>
    <cause>Using declare-fun with a logic that doesn't support uninterpreted functions</cause>
    <fix>
      Option 1 (RECOMMENDED): Remove the uninterpreted function and use direct constraints
      Option 2: Change logic from QF_LRA to QF_UFRA (or QF_LIA to QF_UFLIA, etc.)
    </fix>
  </error>
</common_errors>
```

## Testing Plan

1. ✅ Created integration test that captures this failure
2. ⏳ Implement primary fix (update extraction prompt)
3. ⏳ Re-run integration test to verify
4. ⏳ Add logic consistency validator
5. ⏳ Add unit tests for validator
6. ⏳ Update error fixing prompt with logic mismatch handling
7. ⏳ Run full test suite to ensure no regressions

## Conclusion

The stainless steel validation failure is a **logic theory selection error**, not a parse error. The LLM is generating syntactically valid SMT-LIB that uses advanced features (uninterpreted functions) but selecting an incompatible logic theory (QF_LRA).

**Fix Priority**: Update extraction prompt to prevent logic/feature mismatches.

**Difficulty**: Medium (requires understanding SMT-LIB logic theories)

**Risk**: Low (prompt update is safe, worst case LLM chooses different logic)

**Expected Outcome**: After fix, the LLM will either:
- Use simpler constraints without uninterpreted functions (for QF_LRA)
- Choose QF_UFRA when using uninterpreted functions
- Both approaches should result in valid, solver-executable code
