"""LLM prompt templates for the pipeline.

Centralized prompt management for consistency and maintainability.
"""

FORMALIZATION_PROMPT = """Transform the following free-form natural language text into a bit more formal version.
Keep the same meaning and core information, but make it only moderately more formal - don't overdo it.
Keep the casual tone but clean it up a bit.

Text to formalize:
<INFORMAL-TEXT>
{informal_text}
</INFORMAL-TEXT>

Provide only the formalized version, without any preamble or explanation."""


EXTRACTION_PROMPT = """You are a formal verification expert converting problems to SMT-LIB v2.7 format.

CRITICAL: You MUST produce complete, executable SMT-LIB code with ALL required commands.

# MANDATORY 5-PHASE PROCESS

## Phase 1: Problem Comprehension & Data Inventory
REQUIRED OUTPUT (in SMT-LIB comments):
; === PHASE 1: PROBLEM COMPREHENSION ===
; Original Problem: [one-line summary]
;
; Data Inventory:
; - Facts Given: [list all ground truth data from problem]
; - Unknowns to Find: [list all variables/unknowns to solve for]
; - Constraints: [list all relationships/conditions mentioned]
; - Query Type: [SATISFIABILITY/OPTIMIZATION/VERIFICATION/YES-NO]

## Phase 2: Domain Modeling & Ground Truth Separation
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

## Phase 3: Logic Selection Decision Tree
REQUIRED OUTPUT (in SMT-LIB comments):
; === PHASE 3: LOGIC SELECTION ===
; Theory Choice: [QF_LIA/QF_LRA/QF_NIA/QF_NRA/QF_UFLIA/etc.]
; Justification: [explain why this theory fits the problem]
;
; Quantifiers Needed: [YES/NO]
; Non-linearity: [YES/NO]
; Uninterpreted Functions: [list any needed, or NONE]

## Phase 4: SMT-LIB Encoding with Uninterpreted Function Linking
CRITICAL REQUIREMENTS:
1. Declare ALL constants/variables explicitly with correct sorts
2. Use uninterpreted functions to LINK constraint dependencies
3. NEVER create vacuously true models - constraints must interact
4. Add (set-info :source "...") with problem description
5. Use (set-logic ...) with chosen theory from Phase 3
6. For YES/NO queries: assert scenario, then check-sat (do NOT use get-value on boolean)
7. ALWAYS include (check-sat) as the LAST command before any get-model/get-value

UNINTERPRETED FUNCTION LINKING PATTERN (when constraints are independent):
Instead of:
  (assert (> x 5))
  (assert (< y 10))  ; solver can satisfy these independently!

Use linking via uninterpreted function:
  (declare-fun link (Int Int) Bool)  ; connects x and y
  (assert (link x y))  ; forces solver to consider them together
  (assert (=> (link x y) (> x 5)))
  (assert (=> (link x y) (< y 10)))

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

## Phase 5: Self-Verification Checklist
REQUIRED OUTPUT (in SMT-LIB comments at end):
; === PHASE 5: SELF-VERIFICATION ===
; [ ] All variables declared?
; [ ] Constraints match problem description?
; [ ] Logic theory appropriate?
; [ ] Ground truth facts separated from claims to verify?
; [ ] Modal language ("must", "should") encoded as constraints, not facts?
; [ ] If ground truth contradicts claims, expecting unsat?
; [ ] Uninterpreted functions link related constraints?
; [ ] (check-sat) included as LAST command before get-model?
; [ ] For YES/NO: using assert-and-test (not get-value on boolean)?
; [ ] No vacuous truths (constraints actually interact)?

# INPUT TEXT TO CONVERT
{formal_text}

# YOUR RESPONSE
Provide ONLY the complete SMT-LIB code (including all phase comments as shown above).
Structure: Phase comments + set-info + set-logic + declarations + assertions + check-sat + get-model/get-value.
NO explanatory text before/after the code block."""


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


def get_formalization_prompt(informal_text: str) -> str:
    """Get the formalization prompt with text substituted.

    Args:
        informal_text: Informal natural language text

    Returns:
        Complete prompt for formalization
    """
    return FORMALIZATION_PROMPT.format(informal_text=informal_text)


def get_extraction_prompt(formal_text: str, detail_level: float) -> str:
    """Get the extraction prompt with text substituted.

    Args:
        formal_text: Formalized text from Step 1
        detail_level: Level of detail in annotations (0.0-1.0) - DEPRECATED, kept for API compatibility

    Returns:
        Complete prompt for SMT-LIB extraction
    """
    # Note: detail_level parameter is kept for backward compatibility but not used
    # The 5-phase prompt has fixed detail requirements
    return EXTRACTION_PROMPT.format(formal_text=formal_text)


def get_error_fixing_prompt(smt_code: str, error_message: str) -> str:
    """Get the error fixing prompt with code and error substituted.

    Args:
        smt_code: SMT-LIB code that failed
        error_message: Error message from solver

    Returns:
        Complete prompt for error fixing
    """
    return ERROR_FIXING_PROMPT.format(smt_code=smt_code, error_message=error_message)
