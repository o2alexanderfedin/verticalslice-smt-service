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


EXTRACTION_PROMPT = """You are an expert in SMT-LIB (Satisfiability Modulo Theories Library) syntax. Your task is to convert formalized technical text into executable SMT-LIB code with detailed annotations.

**Task**: Convert the following formalized text into complete, executable SMT-LIB code.

**Requirements**:
1. Generate complete, valid SMT-LIB 2.6 syntax
2. Include (check-sat) command
3. Include appropriate (get-model) or (get-unsat-core) commands
4. Add detailed comments explaining each constraint
5. Use appropriate SMT-LIB theories (e.g., Ints, Reals, Arrays)
6. Declare all variables explicitly
7. Detail level: {detail_level:.2f} (0.0=minimal comments, 1.0=extensive comments)

**Formalized Text**:
{formal_text}

**Your SMT-LIB Code** (respond with ONLY the SMT-LIB code, including comments):"""


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
    """Get the extraction prompt with text and detail level substituted.

    Args:
        formal_text: Formalized text from Step 1
        detail_level: Level of detail in annotations (0.0-1.0)

    Returns:
        Complete prompt for SMT-LIB extraction
    """
    return EXTRACTION_PROMPT.format(
        formal_text=formal_text,
        detail_level=detail_level
    )


def get_error_fixing_prompt(smt_code: str, error_message: str) -> str:
    """Get the error fixing prompt with code and error substituted.

    Args:
        smt_code: SMT-LIB code that failed
        error_message: Error message from solver

    Returns:
        Complete prompt for error fixing
    """
    return ERROR_FIXING_PROMPT.format(
        smt_code=smt_code,
        error_message=error_message
    )
