"""Integration tests for AnthropicClient → AsyncAnthropic SDK.

These tests verify that the AnthropicClient correctly calls the Anthropic API
and handles responses properly. Uses real API calls with minimal input to reduce cost.
"""

import os

import pytest

from src.infrastructure.llm.client import AnthropicClient

# Skip all tests in this module if no API key is available
pytestmark = pytest.mark.skipif(
    not os.environ.get("ANTHROPIC_API_KEY") and not os.environ.get("CLAUDE_CODE_OAUTH_TOKEN"),
    reason="ANTHROPIC_API_KEY or CLAUDE_CODE_OAUTH_TOKEN not set"
)


@pytest.fixture
async def client() -> AnthropicClient:
    """Create an AnthropicClient instance."""
    return AnthropicClient()


@pytest.fixture
async def cleanup_client(client: AnthropicClient):
    """Ensure client is closed after test."""
    yield client
    await client.close()


class TestAnthropicClientFormalize:
    """Tests for formalize method."""

    @pytest.mark.asyncio
    async def test_formalize_simple_text(self, cleanup_client: AnthropicClient) -> None:
        """Test formalization of simple informal text."""
        informal_text = "x > 5"

        result = await cleanup_client.formalize(informal_text)

        assert isinstance(result, str)
        assert len(result) > 0
        # Should preserve the core meaning
        assert "5" in result or "five" in result.lower()

    @pytest.mark.asyncio
    async def test_formalize_with_refinement(self, cleanup_client: AnthropicClient) -> None:
        """Test formalization refinement with previous attempt."""
        informal_text = "x > 5"
        previous_attempt = "The variable x must be greater than five."
        previous_similarity = 0.85

        result = await cleanup_client.formalize(
            informal_text,
            previous_attempt=previous_attempt,
            previous_similarity=previous_similarity,
        )

        assert isinstance(result, str)
        assert len(result) > 0


class TestAnthropicClientExtraction:
    """Tests for extract_to_smtlib method."""

    @pytest.mark.asyncio
    async def test_extract_simple_constraint(self, cleanup_client: AnthropicClient) -> None:
        """Test extraction of simple constraint to SMT-LIB."""
        formal_text = "The variable x must be greater than 5."

        result = await cleanup_client.extract_to_smtlib(formal_text, detail_level=0.5)

        assert isinstance(result, str)
        assert len(result) > 0
        # Should contain SMT-LIB markers
        assert (
            "declare" in result.lower()
            or "assert" in result.lower()
            or "check-sat" in result.lower()
        )

    @pytest.mark.asyncio
    async def test_extract_with_refinement(self, cleanup_client: AnthropicClient) -> None:
        """Test extraction refinement with previous attempt."""
        formal_text = "The variable x must be greater than 5."
        previous_attempt = "(declare-const x Int)\n(assert (> x 5))\n(check-sat)"
        previous_degradation = 0.15

        result = await cleanup_client.extract_to_smtlib(
            formal_text,
            detail_level=0.7,
            previous_attempt=previous_attempt,
            previous_degradation=previous_degradation,
        )

        assert isinstance(result, str)
        assert len(result) > 0


class TestAnthropicClientErrorFixing:
    """Tests for fix_smt_errors method."""

    @pytest.mark.asyncio
    async def test_fix_syntax_error(self, cleanup_client: AnthropicClient) -> None:
        """Test fixing SMT-LIB syntax errors."""
        broken_code = "(declare-const x Int\n(assert (> x 5))\n(check-sat)"  # Missing paren
        error_message = "error: unexpected token at line 1, column 21"

        result = await cleanup_client.fix_smt_errors(broken_code, error_message)

        assert isinstance(result, str)
        assert len(result) > 0
        # Should have balanced parentheses
        assert result.count("(") == result.count(")")


class TestAnthropicClientClose:
    """Tests for client lifecycle."""

    @pytest.mark.asyncio
    async def test_close_without_calls(self) -> None:
        """Test closing client that hasn't made any calls."""
        client = AnthropicClient()
        await client.close()
        # Should not raise any exceptions
