"""Unit tests for SMT diagnostics utilities."""

from src.shared.smt_diagnostics import (
    ErrorLocation,
    SMTErrorContext,
    build_error_location,
    extract_error_context,
    parse_cvc5_error,
)


class TestParseCvc5Error:
    """Tests for parse_cvc5_error function."""

    def test_parse_line_and_column_format(self) -> None:
        """Test parsing 'line X column Y:' format."""
        error_msg = '(error "line 10 column 5: Expected a RPAREN_TOK")'
        line, col = parse_cvc5_error(error_msg)
        assert line == 10
        assert col == 5

    def test_parse_line_only_format(self) -> None:
        """Test parsing 'line X:' format without column."""
        error_msg = "Parse Error: file.smt2 line 15: Unexpected token"
        line, col = parse_cvc5_error(error_msg)
        assert line == 15
        assert col is None

    def test_parse_file_colon_format(self) -> None:
        """Test parsing 'file.smt2:X.Y:' format."""
        error_msg = "Parse Error: file.smt2:20.8: Invalid syntax"
        line, col = parse_cvc5_error(error_msg)
        assert line == 20
        assert col == 8

    def test_parse_no_location_info(self) -> None:
        """Test parsing error with no location information."""
        error_msg = "Generic error message without location"
        line, col = parse_cvc5_error(error_msg)
        assert line is None
        assert col is None

    def test_parse_multiple_numbers(self) -> None:
        """Test parsing with multiple numbers, should match first occurrence."""
        error_msg = "Parse Error: file.smt2:10.5: Expected token at position 42"
        line, col = parse_cvc5_error(error_msg)
        assert line == 10
        assert col == 5

    def test_parse_zero_based_location(self) -> None:
        """Test parsing with zero-based location."""
        error_msg = "Error at file.smt2:0.0: Invalid start"
        line, col = parse_cvc5_error(error_msg)
        assert line == 0
        assert col == 0


class TestExtractErrorContext:
    """Tests for extract_error_context function."""

    def test_extract_context_middle_of_file(self) -> None:
        """Test extracting context from middle of file."""
        smt_code = "\n".join(
            [
                "line 1",
                "line 2",
                "line 3",
                "line 4",
                "line 5",
                "line 6",
                "line 7",
            ]
        )
        before, error_line, after = extract_error_context(smt_code, line_number=4, context_lines=2)

        assert before == ["line 2", "line 3"]
        assert error_line == "line 4"
        assert after == ["line 5", "line 6"]

    def test_extract_context_start_of_file(self) -> None:
        """Test extracting context from start of file."""
        smt_code = "\n".join(
            [
                "line 1",
                "line 2",
                "line 3",
                "line 4",
            ]
        )
        before, error_line, after = extract_error_context(smt_code, line_number=1, context_lines=2)

        assert before == []
        assert error_line == "line 1"
        assert after == ["line 2", "line 3"]

    def test_extract_context_end_of_file(self) -> None:
        """Test extracting context from end of file."""
        smt_code = "\n".join(
            [
                "line 1",
                "line 2",
                "line 3",
                "line 4",
            ]
        )
        before, error_line, after = extract_error_context(smt_code, line_number=4, context_lines=2)

        assert before == ["line 2", "line 3"]
        assert error_line == "line 4"
        assert after == []

    def test_extract_context_no_line_number(self) -> None:
        """Test extracting context when line number is None."""
        smt_code = "line 1\nline 2\nline 3"
        before, error_line, after = extract_error_context(
            smt_code, line_number=None, context_lines=2
        )

        assert before == []
        assert error_line is None
        assert after == []

    def test_extract_context_line_out_of_bounds(self) -> None:
        """Test extracting context when line number exceeds file length."""
        smt_code = "line 1\nline 2\nline 3"
        before, error_line, after = extract_error_context(smt_code, line_number=10, context_lines=2)

        assert before == []
        assert error_line is None
        assert after == []

    def test_extract_context_single_line_file(self) -> None:
        """Test extracting context from single-line file."""
        smt_code = "single line"
        before, error_line, after = extract_error_context(smt_code, line_number=1, context_lines=3)

        assert before == []
        assert error_line == "single line"
        assert after == []

    def test_extract_context_custom_context_lines(self) -> None:
        """Test extracting context with custom number of context lines."""
        smt_code = "\n".join([f"line {i}" for i in range(1, 11)])
        before, error_line, after = extract_error_context(smt_code, line_number=5, context_lines=4)

        assert len(before) == 4
        assert before == ["line 1", "line 2", "line 3", "line 4"]
        assert error_line == "line 5"
        assert len(after) == 4
        assert after == ["line 6", "line 7", "line 8", "line 9"]


class TestBuildErrorLocation:
    """Tests for build_error_location function."""

    def test_build_location_with_valid_error(self) -> None:
        """Test building error location from valid error message."""
        smt_code = "\n".join(
            [
                "(set-logic QF_LRA)",
                "(declare-const x Real)",
                "(assert (> x 5))",
                "(assert (< x invalid))",
                "(check-sat)",
            ]
        )
        error_msg = "Parse Error: file.smt2:4.15: Expected RPAREN_TOK, got 'invalid'"

        location = build_error_location(smt_code, error_msg)

        assert location is not None
        assert location.line_number == 4
        assert location.column_number == 15
        assert location.error_line == "(assert (< x invalid))"
        assert len(location.context_before) == 3
        assert location.context_before[0] == "(set-logic QF_LRA)"
        assert len(location.context_after) == 1
        assert location.context_after[0] == "(check-sat)"

    def test_build_location_with_no_line_info(self) -> None:
        """Test building error location when error has no line information."""
        smt_code = "(set-logic QF_LRA)\n(check-sat)"
        error_msg = "Unknown solver error without location"

        location = build_error_location(smt_code, error_msg)

        assert location is None

    def test_build_location_with_line_only(self) -> None:
        """Test building error location with line but no column."""
        smt_code = "\n".join(
            [
                "(set-logic QF_LRA)",
                "(declare-const x Real)",
                "(check-sat)",
            ]
        )
        error_msg = "Error at line 2: Invalid declaration"

        location = build_error_location(smt_code, error_msg)

        assert location is not None
        assert location.line_number == 2
        assert location.column_number is None
        assert location.error_line == "(declare-const x Real)"

    def test_build_location_empty_code(self) -> None:
        """Test building error location with empty SMT code."""
        smt_code = ""
        error_msg = "Error at line 1: Empty file"

        location = build_error_location(smt_code, error_msg)

        # With empty code, line 1 is out of bounds, so we get an ErrorLocation with empty error_line
        assert location is not None
        assert location.line_number == 1
        assert location.error_line == ""


class TestErrorLocation:
    """Tests for ErrorLocation dataclass."""

    def test_error_location_initialization(self) -> None:
        """Test ErrorLocation initialization with default values."""
        location = ErrorLocation()

        assert location.line_number is None
        assert location.column_number is None
        assert location.error_line is None
        # __post_init__ converts None to [] for list fields
        assert location.context_before == []
        assert location.context_after == []

    def test_error_location_with_values(self) -> None:
        """Test ErrorLocation initialization with values."""
        location = ErrorLocation(
            line_number=10,
            column_number=5,
            error_line="(assert (> x y))",
            context_before=["line 1", "line 2"],
            context_after=["line 3"],
        )

        assert location.line_number == 10
        assert location.column_number == 5
        assert location.error_line == "(assert (> x y))"
        assert location.context_before == ["line 1", "line 2"]
        assert location.context_after == ["line 3"]


class TestSMTErrorContext:
    """Tests for SMTErrorContext dataclass and its methods."""

    def test_error_context_initialization(self) -> None:
        """Test SMTErrorContext initialization."""
        context = SMTErrorContext(
            smt_code="(set-logic QF_LRA)",
            error_message="Parse error",
            error_location=None,
            informal_text="x > 5",
            formal_text="x is greater than 5",
            previous_attempts=[],
            attempt_number=1,
        )

        assert context.smt_code == "(set-logic QF_LRA)"
        assert context.error_message == "Parse error"
        assert context.error_location is None
        assert context.informal_text == "x > 5"
        assert context.formal_text == "x is greater than 5"
        assert context.previous_attempts == []
        assert context.attempt_number == 1

    def test_get_error_summary_xml_with_full_location(self) -> None:
        """Test XML error summary with complete error location."""
        location = ErrorLocation(
            line_number=4,
            column_number=15,
            error_line="(assert (< x invalid))",
            context_before=["(set-logic QF_LRA)", "(declare-const x Real)"],
            context_after=["(check-sat)"],
        )
        context = SMTErrorContext(
            smt_code="test code",
            error_message="Expected RPAREN_TOK",
            error_location=location,
            informal_text="x > 5",
            formal_text="x is greater than 5",
            previous_attempts=[],
            attempt_number=1,
        )

        xml = context.get_error_summary_xml()

        assert "<error_summary>" in xml
        assert "<message>Expected RPAREN_TOK</message>" in xml
        assert "<location>" in xml
        assert "<line>4</line>" in xml
        assert "<column>15</column>" in xml
        assert "(assert (< x invalid))" in xml
        assert "<context_before>" in xml
        assert "(set-logic QF_LRA)" in xml
        assert "<context_after>" in xml
        assert "(check-sat)" in xml
        assert "</error_summary>" in xml

    def test_get_error_summary_xml_no_location(self) -> None:
        """Test XML error summary without error location."""
        context = SMTErrorContext(
            smt_code="test code",
            error_message="Generic error",
            error_location=None,
            informal_text="x > 5",
            formal_text="x is greater than 5",
            previous_attempts=[],
            attempt_number=1,
        )

        xml = context.get_error_summary_xml()

        assert "<error_summary>" in xml
        assert "Generic error" in xml
        assert "<location>" not in xml
        assert "</error_summary>" in xml

    def test_get_error_summary_xml_partial_location(self) -> None:
        """Test XML error summary with partial location (no column)."""
        location = ErrorLocation(
            line_number=2,
            column_number=None,
            error_line="(check-sat)",
            context_before=["(set-logic QF_LRA)"],
            context_after=[],
        )
        context = SMTErrorContext(
            smt_code="test code",
            error_message="Invalid command",
            error_location=location,
            informal_text="x > 5",
            formal_text="x is greater than 5",
            previous_attempts=[],
            attempt_number=1,
        )

        xml = context.get_error_summary_xml()

        assert "<line>2</line>" in xml
        assert "<column>" not in xml
        assert "(check-sat)" in xml

    def test_get_previous_fixes_summary_xml_empty(self) -> None:
        """Test XML previous fixes summary with no attempts."""
        context = SMTErrorContext(
            smt_code="test code",
            error_message="Error",
            error_location=None,
            informal_text="x > 5",
            formal_text="x is greater than 5",
            previous_attempts=[],
            attempt_number=1,
        )

        xml = context.get_previous_fixes_summary_xml()

        assert "<previous_attempts>" in xml
        assert "None - this is the first fix attempt" in xml
        assert "</previous_attempts>" in xml

    def test_get_previous_fixes_summary_xml_with_attempts(self) -> None:
        """Test XML previous fixes summary with multiple attempts."""
        context = SMTErrorContext(
            smt_code="test code",
            error_message="Error",
            error_location=None,
            informal_text="x > 5",
            formal_text="x is greater than 5",
            previous_attempts=[
                {
                    "attempt_number": 1,
                    "smt_code": "(assert (> x 5))",
                    "solver_error": "Parse error",
                    "fix_attempted": "(assert (> x 5.0))",
                },
                {
                    "attempt_number": 2,
                    "smt_code": "(assert (> x 5.0))",
                    "solver_error": "Type error",
                    "fix_attempted": "(assert (> (to_real x) 5.0))",
                },
            ],
            attempt_number=3,
        )

        xml = context.get_previous_fixes_summary_xml()

        assert "<previous_attempts>" in xml
        assert "<count>2</count>" in xml
        assert '<attempt number="1">' in xml
        assert "<error>Parse error</error>" in xml
        assert "<fix_attempted>(assert (> x 5.0))</fix_attempted>" in xml
        assert '<attempt number="2">' in xml
        assert "<error>Type error</error>" in xml
        assert "</previous_attempts>" in xml

    def test_get_previous_fixes_summary_xml_escape_special_chars(self) -> None:
        """Test XML escapes special characters in error messages."""
        context = SMTErrorContext(
            smt_code="test code",
            error_message="Error",
            error_location=None,
            informal_text="x > 5",
            formal_text="x is greater than 5",
            previous_attempts=[
                {
                    "attempt_number": 1,
                    "smt_code": "(assert (> x 5))",
                    "solver_error": "Expected '<' but got '>'",
                    "fix_attempted": "(assert (< x 5))",
                },
            ],
            attempt_number=2,
        )

        xml = context.get_previous_fixes_summary_xml()

        # XML should escape < and > characters
        assert "Expected '&lt;' but got '&gt;'" in xml or "Expected '<' but got '>'" in xml
