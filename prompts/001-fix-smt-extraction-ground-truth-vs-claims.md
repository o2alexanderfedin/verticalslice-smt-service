<objective>
Fix the SMT-LIB extraction prompt to correctly distinguish between ground truth facts and claims/constraints to verify, preventing the solver from incorrectly accepting contradictory statements as satisfiable.

This fix addresses a critical bug where statements like "Apples count is 5. This count must be strictly greater than 5 and less than 10" incorrectly produce 'sat' instead of 'unsat', because the prompt doesn't emphasize that modal language ("must", "should", "ought to") signals **claims to verify** rather than **ground truth facts**.
</objective>

<problem_analysis>
**Root Cause**: The current EXTRACTION_PROMPT in src/infrastructure/llm/prompts.py has Phase 2 guidance that doesn't adequately emphasize the critical, **theory-independent** distinction between:

1. **Ground Truth (Facts Given)**: Concrete values, measurements, existing state
   - Example: "Apples count is 5"
   - Should be encoded as: `(assert (= apples 5))`

2. **Claims to Verify (Constraints)**: Requirements, conditions, modal statements using "must", "should", "ought to"
   - Example: "This count must be strictly greater than 5"
   - Should be encoded as: `(assert (> apples 5))`

**Failure Mode**: When both are asserted together as facts, the solver finds them contradictory (unsat is correct). However, the LLM sometimes treats modal language as descriptive facts rather than constraints to test, leading to vacuous models.

**Expected Behavior** (theory-independent pattern):
- Input: "Apples count is 5. This count must be strictly greater than 5 and less than 10"
- Correct interpretation:
  - Ground truth: apples = 5
  - Constraint to verify: apples > 5 AND apples < 10
  - Result: unsat (contradiction - 5 is NOT > 5)

This pattern works identically for:
- Bitvectors: "Register is #b0101. Register must be #b1010" → unsat
- Strings: "Name is 'Alice'. Name must be 'Bob'" → unsat
- Reals: "Temp is 98.6. Temp must be >= 100.0" → unsat
- Any theory where ground truth contradicts claims

**Current Bug**:
- The LLM sometimes interprets "must be" as hypothetical or creates separate variables, allowing sat
</problem_analysis>

<context>
File to modify: src/infrastructure/llm/prompts.py
Specifically: EXTRACTION_PROMPT constant (lines 18-98)
Focus area: Phase 2 (lines 36-48)

The extraction prompt uses a 5-phase process:
1. Problem Comprehension & Data Inventory
2. **Domain Modeling & Ground Truth Separation** ← THIS NEEDS ENHANCEMENT
3. Logic Selection Decision Tree
4. SMT-LIB Encoding
5. Self-Verification Checklist
</context>

<requirements>
Enhance Phase 2 of the EXTRACTION_PROMPT to include:

1. **Explicit Modal Language Detection**: Add guidance on identifying modal verbs (must, should, ought to, has to, needs to) as signals of **constraints to verify**, not descriptive facts

2. **Ground Truth vs Claims Matrix**: Provide clear examples showing:
   - "X is 5" → Ground truth fact → (assert (= x 5))
   - "X must be > 5" → Claim to verify → (assert (> x 5))
   - "X is 5. X must be > 5" → Contradiction → unsat expected

3. **Verb Tense Guidance**:
   - Present indicative ("is", "equals", "has") → Ground truth
   - Modal auxiliary + verb ("must be", "should be") → Constraint
   - Imperative ("ensure that", "verify that") → Constraint

4. **Contradiction Detection Hint**: Remind LLM to check if ground truth and claims contradict, and if so, expect unsat result

5. **Keep existing YES/NO verification guidance** (lines 44-48) intact - it's working correctly
</requirements>

<implementation>
**Step 1**: Read src/infrastructure/llm/prompts.py to understand current structure

**Step 2**: Enhance Phase 2 comments in EXTRACTION_PROMPT (lines 36-48) with new guidance:

Add after line 36 (after "## Phase 2: Domain Modeling & Ground Truth Separation"):

```python
REQUIRED OUTPUT (in SMT-LIB comments):
; === PHASE 2: DOMAIN MODELING ===
;
; CRITICAL: Distinguish FACTS (ground truth) from CLAIMS (constraints to verify)
;
; MODAL LANGUAGE DETECTOR:
; - Modal verbs (must, should, ought to, has to, needs to) signal CLAIMS, not facts
; - Present indicative (is, equals, has, contains) signals GROUND TRUTH
; - Imperative (ensure, verify, check) signals CLAIMS
;
; Ground Truth (concrete facts given in the problem):
; - [list all concrete values, measurements, existing state]
; - Pattern: "X is V" → (assert (= x V))
; - Pattern: "Y contains V" → (assert (= y V))
;
; Claims to Verify (requirements, constraints using modal language):
; - [list all modal statements, requirements, conditions]
; - Pattern: "X must be OP V" → (assert (OP x V))
; - Pattern: "Y should satisfy C" → (assert C)
;
; Contradiction Check:
; - [If ground truth contradicts claims, note: "EXPECT UNSAT - ground truth violates claims"]
; - When ground truth assigns a value AND claims require a different value → expect unsat
;
; SPECIAL CASE - YES/NO Verification Queries:
; If problem asks "Can X happen?" or "Is Y possible?", use ASSERT-AND-TEST pattern:
; 1. Assert all given constraints
; 2. Assert the scenario being tested (e.g., "X happens")
; 3. check-sat (sat=YES possible, unsat=NO impossible)
```

**CRITICAL**: Use generic patterns (X, Y, V, OP, C) not specific examples. The guidance must work for ANY SMT-LIB theory:
- Arithmetic (integers, reals, non-linear)
- Bitvectors (fixed-width binary operations)
- Strings and sequences
- Arrays (with any index/element types)
- Datatypes (enumerated, recursive, parametric)
- Sets and bags (finite/infinite)
- Uninterpreted functions
- Combinations of the above

The modal language pattern "is" vs "must be" is **theory-independent** and applies universally.

**Step 3**: Add a generic pattern with concrete example to Phase 4:

After line 69 (after the uninterpreted function pattern), add:

```python
CRITICAL PATTERN: GROUND TRUTH + CLAIMS ENCODING

Generic Pattern:
  Input: "Variable V is A. V must be OP B."
  (declare-const V Type)
  (assert (= V A))                   ; Ground truth: V IS A
  (assert (OP V B))                  ; Claim: must satisfy (OP V B)
  ; Result: unsat if A does not satisfy (OP A B), sat otherwise

Example (illustrative only - apply pattern to any domain):
  Input: "Count is 5. Count must be strictly greater than 5 and less than 10."
  (declare-const count Int)
  (assert (= count 5))               ; Ground truth: count IS 5
  (assert (> count 5))               ; Claim: must be > 5
  (assert (< count 10))              ; Claim: must be < 10
  ; Result: unsat (contradiction - 5 is not > 5)

INCORRECT encoding (DO NOT DO THIS):
  (declare-const count Int)
  (declare-const target Int)         ; WRONG: creates separate variable
  (assert (= count 5))
  (assert (> target 5))
  ; Result: sat (vacuous - no connection between count and target)

This pattern applies to ANY SMT-LIB theory supported by cvc5:
- Arithmetic: QF_LIA, QF_LRA, QF_NIA, QF_NRA
- Bitvectors: QF_BV, QF_ABV
- Arrays: QF_AX, QF_AUFLIA
- Strings: QF_S, QF_SLIA
- Datatypes: user-defined types
- Sets, Bags, Sequences
- Uninterpreted functions: QF_UF, QF_UFLIA
- Combinations: QF_AUFBV, QF_UFBV, etc.
```

**Step 4**: Update Phase 5 checklist to include ground truth verification:

In the checklist at lines 82-90, add:

```python
; [ ] Ground truth facts separated from claims to verify?
; [ ] Modal language ("must", "should") encoded as constraints, not facts?
; [ ] If ground truth contradicts claims, expecting unsat?
```

**Step 5**: Run tests to verify the fix works:
- Test with: "Apples count is 5. This count must be strictly greater than 5 and less than 10"
- Expected: unsat
- Test with: "Apples count is 5. This count is strictly greater than 5 and less than 10"
- Expected: unsat (even without modal language, "is" contradicts the ground truth)
</implementation>

<output>
Modify file: src/infrastructure/llm/prompts.py
Specifically: EXTRACTION_PROMPT string constant

Changes:
1. Enhanced Phase 2 with Modal Language Detector and Ground Truth vs Claims guidance
2. Added concrete example in Phase 4 showing correct vs incorrect encoding
3. Updated Phase 5 checklist with ground truth verification items

Preserve:
- All existing 5-phase structure
- YES/NO verification guidance (working correctly)
- Uninterpreted function linking pattern
- All other phases unchanged
</output>

<verification>
After implementing changes:

1. **Syntax Check**: Ensure Python string is valid (no unclosed quotes, proper escaping)

2. **Manual Test**: Verify the prompt is generic and contains no domain-specific examples in the instructions themselves (examples should be clearly marked as illustrative)

3. **Theory-Agnostic Test**: Test with multiple SMT-LIB theories to ensure generality:
   - **QF_LIA** (Linear Integer Arithmetic): "Count is 5. Count must be > 5"
   - **QF_LRA** (Linear Real Arithmetic): "Temperature is 98.6. Temperature must be >= 100.0"
   - **QF_BV** (Bitvectors): "Register value is #b0101. Value must equal #b1010"
   - **QF_S** (Strings): "Name is 'Alice'. Name must be 'Bob'"
   - **Arrays**: "Array at index 0 is 5. Array at index 0 must be > 5"
   - **Datatypes**: "Status is PENDING. Status must be APPROVED"
   - Verify all produce unsat as expected (ground truth contradicts claims)

4. **Regression Test**: Ensure existing test cases still pass (tests/unit/domain/test_extraction_step.py)
</verification>

<success_criteria>
- [ ] EXTRACTION_PROMPT Phase 2 uses GENERIC patterns (X, Y, V, OP) not domain-specific examples
- [ ] Phase 2 clearly distinguishes ground truth (is/equals) from claims (must/should)
- [ ] Phase 4 includes generic pattern with ONE illustrative example clearly marked as such
- [ ] Phase 5 checklist includes ground truth verification items
- [ ] Prompt is completely theory-agnostic and works for ALL SMT-LIB theories supported by cvc5
- [ ] Test with multiple theories (QF_LIA, QF_LRA, QF_BV, QF_S, arrays, datatypes) all work correctly
- [ ] Pattern works for bitvectors, strings, sequences, sets, bags, datatypes, temporal logics, etc.
- [ ] All existing unit tests pass
- [ ] No syntax errors in prompts.py
</success_criteria>
