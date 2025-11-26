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
