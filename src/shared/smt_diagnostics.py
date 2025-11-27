"""SMT diagnostic utilities for error parsing and context extraction.

This module provides utilities for parsing SMT solver errors and extracting
contextual information to improve error messages and enable better LLM-based fixes.
"""

import re
from dataclasses import dataclass
from typing import Any


@dataclass
class ErrorLocation:
    """Location of an error in SMT-LIB code.

    Attributes:
        line_number: Line where error occurred (1-indexed), None if not parseable
        column_number: Column where error occurred (1-indexed), None if not parseable
        error_line: The actual line of code with the error, None if not available
        context_before: Up to 3 lines of code before the error
        context_after: Up to 3 lines of code after the error
    """

    line_number: int | None = None
    column_number: int | None = None
    error_line: str | None = None
    context_before: list[str] = None
    context_after: list[str] = None

    def __post_init__(self):
        """Initialize default values for list fields."""
        if self.context_before is None:
            self.context_before = []
        if self.context_after is None:
            self.context_after = []


@dataclass
class SMTErrorContext:
    """Complete context for SMT error fixing.

    This structure provides all information needed for an LLM to make
    an informed fix, including error location, semantic context, and
    history of previous attempts.

    Attributes:
        smt_code: Current SMT-LIB code with error
        error_message: Full error message from solver
        error_location: Parsed location information (if available)
        informal_text: Original informal constraint from user
        formal_text: Formalized version of the constraint
        previous_attempts: History of previous fix attempts
        attempt_number: Current attempt number (1-indexed)
    """

    smt_code: str
    error_message: str
    error_location: ErrorLocation | None
    informal_text: str
    formal_text: str
    previous_attempts: list[dict[str, Any]]
    attempt_number: int

    def get_error_summary_xml(self) -> str:
        """Generate XML-formatted error summary for LLM prompts.

        Returns:
            XML string with error details including location and context
        """
        if not self.error_location or not self.error_location.line_number:
            return f"<error_summary>\n{self.error_message}\n</error_summary>"

        loc = self.error_location
        xml = "<error_summary>\n"
        xml += f"  <message>{self.error_message}</message>\n"
        xml += "  <location>\n"
        xml += f"    <line>{loc.line_number}</line>\n"

        if loc.column_number:
            xml += f"    <column>{loc.column_number}</column>\n"

        xml += "  </location>\n"

        if loc.error_line:
            xml += f"  <error_line>\n{loc.error_line}\n  </error_line>\n"

        if loc.context_before:
            xml += "  <context_before>\n"
            for line in loc.context_before:
                xml += f"{line}\n"
            xml += "  </context_before>\n"

        if loc.context_after:
            xml += "  <context_after>\n"
            for line in loc.context_after:
                xml += f"{line}\n"
            xml += "  </context_after>\n"

        xml += "</error_summary>"
        return xml

    def get_previous_fixes_summary_xml(self) -> str:
        """Generate XML-formatted summary of previous fix attempts.

        Returns:
            XML string with history of failed attempts
        """
        if not self.previous_attempts:
            return "<previous_attempts>None - this is the first fix attempt</previous_attempts>"

        xml = "<previous_attempts>\n"
        xml += f"  <count>{len(self.previous_attempts)}</count>\n"

        for attempt in self.previous_attempts:
            xml += f"  <attempt number=\"{attempt['attempt_number']}\">\n"
            xml += f"    <error>{attempt['solver_error'][:200]}</error>\n"
            xml += f"    <fix_attempted>{attempt['fix_attempted']}</fix_attempted>\n"
            xml += "  </attempt>\n"

        xml += "</previous_attempts>"
        return xml


def parse_cvc5_error(error_message: str) -> tuple[int | None, int | None]:
    """Extract line and column numbers from cvc5 error message.

    cvc5 error messages typically follow these patterns:
    - "(error "line 5 column 12: Expected RPAREN_TOK...")"
    - "(error "Parse Error: file.smt2:10.5: Expected...")"
    - "(error "Expected a RPAREN_TOK...")" (no location)

    Args:
        error_message: Error message from cvc5 solver

    Returns:
        Tuple of (line_number, column_number), both 1-indexed.
        Returns (None, None) if location cannot be parsed.
    """
    # Pattern 1: "line X column Y:"
    match = re.search(r"line\s+(\d+)\s+column\s+(\d+)", error_message, re.IGNORECASE)
    if match:
        return int(match.group(1)), int(match.group(2))

    # Pattern 2: "file.smt2:X.Y:" or ":X.Y:"
    match = re.search(r":(\d+)\.(\d+):", error_message)
    if match:
        return int(match.group(1)), int(match.group(2))

    # Pattern 3: "line X:" (no column)
    match = re.search(r"line\s+(\d+)", error_message, re.IGNORECASE)
    if match:
        return int(match.group(1)), None

    return None, None


def extract_error_context(
    smt_code: str,
    line_number: int | None,
    context_lines: int = 3,
) -> tuple[list[str], str | None, list[str]]:
    """Extract code context around error location.

    Args:
        smt_code: The complete SMT-LIB code
        line_number: Line where error occurred (1-indexed), None if unknown
        context_lines: Number of lines to include before and after error

    Returns:
        Tuple of (lines_before, error_line, lines_after).
        Returns ([], None, []) if line_number is None or out of range.
    """
    if line_number is None:
        return [], None, []

    lines = smt_code.split("\n")
    idx = line_number - 1  # Convert to 0-indexed

    if idx < 0 or idx >= len(lines):
        return [], None, []

    start = max(0, idx - context_lines)
    end = min(len(lines), idx + context_lines + 1)

    before = lines[start:idx]
    error_line = lines[idx]
    after = lines[idx + 1 : end]

    return before, error_line, after


def build_error_location(
    smt_code: str,
    error_message: str,
) -> ErrorLocation | None:
    """Parse error message and build complete ErrorLocation.

    Args:
        smt_code: The SMT-LIB code that failed
        error_message: Error message from solver

    Returns:
        ErrorLocation with parsed information, or None if parsing failed
    """
    line_num, col_num = parse_cvc5_error(error_message)

    if line_num is None:
        return None

    before, error_line, after = extract_error_context(smt_code, line_num)

    return ErrorLocation(
        line_number=line_num,
        column_number=col_num,
        error_line=error_line,
        context_before=before,
        context_after=after,
    )
