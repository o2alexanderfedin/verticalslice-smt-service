"""Tests for SMT-LIB code extraction utilities."""


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
