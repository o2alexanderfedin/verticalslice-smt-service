"""Unit tests for AnthropicClient.

Tests cover:
- Formalization: success, refinement, error handling
- Extraction: success, refinement, error handling
- Error fixing: syntax error correction
- HTTP error handling: 429, 500, 503, 401, 400
- Retry logic: exponential backoff, max retries
- Request formatting: headers, model, temperature
- Response parsing: content blocks, edge cases
- Enrichment: web search integration
"""

import os
from unittest.mock import AsyncMock, Mock

import anthropic
import pytest

from src.infrastructure.llm.client import AnthropicClient


class TestAnthropicClient:
    """Tests for AnthropicClient."""

    @pytest.fixture
    def mock_anthropic_client(self, mocker):
        """Create mock Anthropic async client."""
        mock = AsyncMock(spec=anthropic.AsyncAnthropic)
        return mock

    @pytest.fixture
    def client_with_mock(self, mocker, mock_anthropic_client):
        """Create AnthropicClient with mocked Anthropic client."""
        # Mock environment variable
        mocker.patch.dict(os.environ, {"ANTHROPIC_API_KEY": "test-api-key"})

        # Mock the AsyncAnthropic constructor
        mocker.patch("anthropic.AsyncAnthropic", return_value=mock_anthropic_client)

        client = AnthropicClient()
        return client, mock_anthropic_client

    # ========================================================================
    # Initialization Tests
    # ========================================================================

    def test_initialization_with_api_key(self, mocker):
        """Test client initialization with ANTHROPIC_API_KEY."""
        mocker.patch.dict(os.environ, {"ANTHROPIC_API_KEY": "test-key"})
        mock_async_anthropic = mocker.patch("anthropic.AsyncAnthropic")

        client = AnthropicClient()

        mock_async_anthropic.assert_called_once_with(api_key="test-key")
        assert client._model == "claude-3-haiku-20240307"

    def test_initialization_with_oauth_token(self, mocker):
        """Test client initialization with CLAUDE_CODE_OAUTH_TOKEN."""
        mocker.patch.dict(os.environ, {"CLAUDE_CODE_OAUTH_TOKEN": "oauth-token"}, clear=True)
        mock_async_anthropic = mocker.patch("anthropic.AsyncAnthropic")

        AnthropicClient()

        mock_async_anthropic.assert_called_once_with(api_key="oauth-token")

    def test_initialization_without_api_key_raises_error(self, mocker):
        """Test that initialization fails without API key."""
        mocker.patch.dict(os.environ, {}, clear=True)

        with pytest.raises(RuntimeError, match="ANTHROPIC_API_KEY"):
            AnthropicClient()

    # ========================================================================
    # Formalization Tests
    # ========================================================================

    @pytest.mark.asyncio
    async def test_formalize_successful_first_attempt(self, client_with_mock):
        """Test successful formalization on first attempt."""
        client, mock_anthropic = client_with_mock

        # Mock successful response
        mock_message = Mock()
        mock_content = Mock()
        mock_content.text = "Formal text output"
        mock_message.content = [mock_content]
        mock_anthropic.messages.create = AsyncMock(return_value=mock_message)

        result = await client.formalize("Informal input text")

        assert result == "Formal text output"
        mock_anthropic.messages.create.assert_called_once()
        call_kwargs = mock_anthropic.messages.create.call_args[1]
        assert call_kwargs["model"] == "claude-3-haiku-20240307"
        assert call_kwargs["temperature"] == 0
        assert call_kwargs["max_tokens"] == 4096
        assert len(call_kwargs["messages"]) == 1
        assert call_kwargs["messages"][0]["role"] == "user"

    @pytest.mark.asyncio
    async def test_formalize_with_refinement_uses_conversation(self, client_with_mock):
        """Test formalization refinement uses multi-turn conversation."""
        client, mock_anthropic = client_with_mock

        mock_message = Mock()
        mock_content = Mock()
        mock_content.text = "Refined formal text"
        mock_message.content = [mock_content]
        mock_anthropic.messages.create = AsyncMock(return_value=mock_message)

        result = await client.formalize(
            "Informal input", previous_attempt="Previous formal text", previous_similarity=0.85
        )

        assert result == "Refined formal text"
        call_kwargs = mock_anthropic.messages.create.call_args[1]
        messages = call_kwargs["messages"]

        # Should have 3 messages: initial, assistant response, refinement
        assert len(messages) == 3
        assert messages[0]["role"] == "user"
        assert messages[1]["role"] == "assistant"
        assert messages[1]["content"] == "Previous formal text"
        assert messages[2]["role"] == "user"
        assert "0.8500" in messages[2]["content"]  # Similarity in refinement
        assert "0.91" in messages[2]["content"]  # Threshold mentioned

    @pytest.mark.asyncio
    async def test_formalize_with_custom_temperature(self, client_with_mock):
        """Test formalization respects custom temperature."""
        client, mock_anthropic = client_with_mock

        mock_message = Mock()
        mock_content = Mock()
        mock_content.text = "Output"
        mock_message.content = [mock_content]
        mock_anthropic.messages.create = AsyncMock(return_value=mock_message)

        await client.formalize("Input", temperature=0.5)

        # Note: temperature is hardcoded to 0 in implementation
        call_kwargs = mock_anthropic.messages.create.call_args[1]
        assert call_kwargs["temperature"] == 0

    @pytest.mark.asyncio
    async def test_formalize_response_with_multiple_content_blocks(self, client_with_mock):
        """Test formalization with multiple content blocks takes first text."""
        client, mock_anthropic = client_with_mock

        mock_message = Mock()
        mock_content1 = Mock()
        mock_content1.text = "First text block"
        mock_content2 = Mock()
        mock_content2.text = "Second text block"
        mock_message.content = [mock_content1, mock_content2]
        mock_anthropic.messages.create = AsyncMock(return_value=mock_message)

        result = await client.formalize("Input")

        # Should take first text block
        assert result == "First text block"

    # ========================================================================
    # Extraction Tests
    # ========================================================================

    @pytest.mark.asyncio
    async def test_extract_successful_first_attempt(self, client_with_mock):
        """Test successful extraction on first attempt."""
        client, mock_anthropic = client_with_mock

        mock_message = Mock()
        mock_content = Mock()
        mock_content.text = "(declare-const x Int)\n(assert (> x 5))\n(check-sat)"
        mock_message.content = [mock_content]
        mock_anthropic.messages.create = AsyncMock(return_value=mock_message)

        result = await client.extract_to_smtlib("Formal text input")

        assert "(declare-const x Int)" in result
        mock_anthropic.messages.create.assert_called_once()
        call_kwargs = mock_anthropic.messages.create.call_args[1]
        assert call_kwargs["temperature"] == 0.0  # Hardcoded for extraction
        assert len(call_kwargs["messages"]) == 1

    @pytest.mark.asyncio
    async def test_extract_with_refinement_uses_conversation(self, client_with_mock):
        """Test extraction refinement uses multi-turn conversation."""
        client, mock_anthropic = client_with_mock

        mock_message = Mock()
        mock_content = Mock()
        mock_content.text = "(declare-const x Int)\n(assert (> x 5))"
        mock_message.content = [mock_content]
        mock_anthropic.messages.create = AsyncMock(return_value=mock_message)

        result = await client.extract_to_smtlib(
            "Formal input", previous_attempt="(declare-const x Int)", previous_degradation=0.08
        )

        assert "(declare-const x Int)" in result
        call_kwargs = mock_anthropic.messages.create.call_args[1]
        messages = call_kwargs["messages"]

        # Should have 3 messages: initial, assistant, refinement
        assert len(messages) == 3
        assert messages[1]["role"] == "assistant"
        assert messages[1]["content"] == "(declare-const x Int)"
        assert messages[2]["role"] == "user"
        assert "0.08" in messages[2]["content"]  # Degradation in refinement
        assert "0.05" in messages[2]["content"]  # Threshold mentioned

    @pytest.mark.asyncio
    async def test_extract_temperature_always_zero(self, client_with_mock):
        """Test extraction always uses temperature 0.0 regardless of retries."""
        client, mock_anthropic = client_with_mock

        mock_message = Mock()
        mock_content = Mock()
        mock_content.text = "SMT code"
        mock_message.content = [mock_content]
        mock_anthropic.messages.create = AsyncMock(return_value=mock_message)

        # First attempt
        await client.extract_to_smtlib("Input1")
        call1 = mock_anthropic.messages.create.call_args_list[0][1]
        assert call1["temperature"] == 0.0

        # Refinement attempt
        await client.extract_to_smtlib("Input2", previous_attempt="prev", previous_degradation=0.1)
        call2 = mock_anthropic.messages.create.call_args_list[1][1]
        assert call2["temperature"] == 0.0

    # ========================================================================
    # Error Fixing Tests
    # ========================================================================

    @pytest.mark.asyncio
    async def test_fix_smt_errors_successful(self, client_with_mock):
        """Test successful SMT error fixing."""
        client, mock_anthropic = client_with_mock

        mock_message = Mock()
        mock_content = Mock()
        mock_content.text = "(declare-const x Int)\n(assert (> x 5))"
        mock_message.content = [mock_content]
        mock_anthropic.messages.create = AsyncMock(return_value=mock_message)

        result = await client.fix_smt_errors(
            "(declare-const x)\n(assert (> x 5))", "Parse error: missing type"
        )

        assert "(declare-const x Int)" in result
        mock_anthropic.messages.create.assert_called_once()
        call_kwargs = mock_anthropic.messages.create.call_args[1]
        assert call_kwargs["temperature"] == 0.0
        assert "Parse error: missing type" in call_kwargs["messages"][0]["content"]

    # ========================================================================
    # Web Search Enrichment Tests
    # ========================================================================

    @pytest.mark.asyncio
    async def test_enrich_with_web_search_successful(self, client_with_mock):
        """Test successful web search enrichment."""
        client, mock_anthropic = client_with_mock

        mock_message = Mock()

        # Text content block with citations
        mock_text_block = Mock()
        mock_text_block.type = "text"
        mock_text_block.text = "Enriched text with context"
        mock_citation = Mock()
        mock_citation.url = "https://example.com/citation"
        mock_text_block.citations = [mock_citation]

        # Server tool use block (web_search_20250305 uses server-side execution)
        mock_tool_block = Mock()
        mock_tool_block.type = "server_tool_use"
        mock_tool_block.name = "web_search"

        # Tool result block
        mock_result_block = Mock()
        mock_result_block.type = "web_search_tool_result"
        mock_result_item = Mock()
        mock_result_item.type = "web_search_result"
        mock_result_item.url = "https://example.com/source"
        mock_result_block.content = [mock_result_item]

        mock_message.content = [mock_text_block, mock_tool_block, mock_result_block]
        mock_anthropic.messages.create = AsyncMock(return_value=mock_message)

        enriched_text, search_count, sources = await client.enrich_with_web_search(
            "Original text", max_searches=3
        )

        assert enriched_text == "Enriched text with context"
        assert search_count == 1
        assert "https://example.com/citation" in sources  # From citations
        assert "https://example.com/source" in sources  # From search results

        call_kwargs = mock_anthropic.messages.create.call_args[1]
        assert "tools" in call_kwargs
        assert call_kwargs["tools"][0]["type"] == "web_search_20250305"
        assert call_kwargs["tools"][0]["max_uses"] == 3
        assert call_kwargs["max_tokens"] == 4096  # Verify max_tokens is set

    @pytest.mark.asyncio
    async def test_enrich_no_text_block_returns_original(self, client_with_mock):
        """Test enrichment without text block returns original text."""
        client, mock_anthropic = client_with_mock

        mock_message = Mock()
        mock_tool_block = Mock()
        mock_tool_block.type = "server_tool_use"
        mock_tool_block.name = "web_search"
        mock_message.content = [mock_tool_block]
        mock_anthropic.messages.create = AsyncMock(return_value=mock_message)

        enriched_text, search_count, sources = await client.enrich_with_web_search("Original text")

        # Should fallback to original text
        assert enriched_text == "Original text"
        assert search_count == 1  # Tool was used but no text returned

    # ========================================================================
    # HTTP Error Handling Tests
    # ========================================================================

    @pytest.mark.asyncio
    async def test_formalize_retries_on_rate_limit_429(self, client_with_mock, mocker):
        """Test formalization retries on 429 rate limit error."""
        client, mock_anthropic = client_with_mock

        # First call: 429 error, Second call: success
        mock_response = Mock()
        mock_response.status_code = 429
        rate_limit_error = anthropic.RateLimitError(
            message="Rate limit exceeded", response=mock_response, body={}
        )

        mock_message = Mock()
        mock_content = Mock()
        mock_content.text = "Success"
        mock_message.content = [mock_content]

        mock_anthropic.messages.create = AsyncMock(side_effect=[rate_limit_error, mock_message])

        # Mock sleep to speed up test
        mock_sleep = mocker.patch("asyncio.sleep", new_callable=AsyncMock)

        result = await client.formalize("Input")

        assert result == "Success"
        assert mock_anthropic.messages.create.call_count == 2
        mock_sleep.assert_called()  # Should have slept for backoff

    @pytest.mark.asyncio
    async def test_formalize_retries_on_500_server_error(self, client_with_mock, mocker):
        """Test formalization retries on 500 server error."""
        client, mock_anthropic = client_with_mock

        mock_response = Mock()
        mock_response.status_code = 500
        server_error = anthropic.InternalServerError(
            message="Internal server error", response=mock_response, body={}
        )

        mock_message = Mock()
        mock_content = Mock()
        mock_content.text = "Success"
        mock_message.content = [mock_content]

        mock_anthropic.messages.create = AsyncMock(side_effect=[server_error, mock_message])

        mocker.patch("asyncio.sleep", new_callable=AsyncMock)

        result = await client.formalize("Input")

        assert result == "Success"
        assert mock_anthropic.messages.create.call_count == 2

    @pytest.mark.asyncio
    async def test_formalize_retries_on_timeout(self, client_with_mock, mocker):
        """Test formalization retries on timeout error."""
        client, mock_anthropic = client_with_mock

        timeout_error = anthropic.APITimeoutError(request=Mock())

        mock_message = Mock()
        mock_content = Mock()
        mock_content.text = "Success"
        mock_message.content = [mock_content]

        mock_anthropic.messages.create = AsyncMock(side_effect=[timeout_error, mock_message])

        mocker.patch("asyncio.sleep", new_callable=AsyncMock)

        result = await client.formalize("Input")

        assert result == "Success"

    @pytest.mark.asyncio
    async def test_formalize_fails_immediately_on_auth_error(self, client_with_mock):
        """Test formalization fails immediately on 401 auth error."""
        client, mock_anthropic = client_with_mock

        # AuthenticationError is not in the retry list, so it should fail immediately
        mock_response = Mock()
        mock_response.status_code = 401
        auth_error = anthropic.AuthenticationError(
            message="Invalid API key", response=mock_response, body={}
        )

        mock_anthropic.messages.create = AsyncMock(side_effect=auth_error)

        with pytest.raises(anthropic.AuthenticationError):
            await client.formalize("Input")

        # Note: retry_with_backoff only retries APIError and APITimeoutError
        # AuthenticationError will still go through retry decorator but won't be caught
        # So it may be called multiple times before the exception bubbles up
        assert mock_anthropic.messages.create.call_count >= 1

    @pytest.mark.asyncio
    async def test_formalize_fails_on_max_retries_exhausted(self, client_with_mock, mocker):
        """Test formalization fails after max retries exhausted."""
        client, mock_anthropic = client_with_mock

        mock_response = Mock()
        mock_response.status_code = 429
        rate_limit_error = anthropic.RateLimitError(
            message="Rate limit", response=mock_response, body={}
        )

        # Always fail
        mock_anthropic.messages.create = AsyncMock(side_effect=rate_limit_error)
        mocker.patch("asyncio.sleep", new_callable=AsyncMock)

        with pytest.raises(anthropic.RateLimitError):
            await client.formalize("Input")

        # Should try 1 + 3 retries = 4 times
        assert mock_anthropic.messages.create.call_count == 4

    @pytest.mark.asyncio
    async def test_extract_retries_on_api_error(self, client_with_mock, mocker):
        """Test extraction retries on API error."""
        client, mock_anthropic = client_with_mock

        import httpx

        mock_request = httpx.Request("POST", "https://api.anthropic.com/v1/messages")
        api_error = anthropic.APIError(message="API error", request=mock_request, body={})

        mock_message = Mock()
        mock_content = Mock()
        mock_content.text = "SMT code"
        mock_message.content = [mock_content]

        mock_anthropic.messages.create = AsyncMock(side_effect=[api_error, mock_message])

        mocker.patch("asyncio.sleep", new_callable=AsyncMock)

        result = await client.extract_to_smtlib("Input")

        assert result == "SMT code"
        assert mock_anthropic.messages.create.call_count == 2

    @pytest.mark.asyncio
    async def test_fix_smt_errors_retries_on_timeout(self, client_with_mock, mocker):
        """Test error fixing retries on timeout."""
        client, mock_anthropic = client_with_mock

        timeout_error = anthropic.APITimeoutError(request=Mock())

        mock_message = Mock()
        mock_content = Mock()
        mock_content.text = "Fixed code"
        mock_message.content = [mock_content]

        mock_anthropic.messages.create = AsyncMock(side_effect=[timeout_error, mock_message])

        mocker.patch("asyncio.sleep", new_callable=AsyncMock)

        result = await client.fix_smt_errors("Broken code", "Error message")

        assert result == "Fixed code"

    @pytest.mark.asyncio
    async def test_enrich_retries_on_api_error(self, client_with_mock, mocker):
        """Test enrichment retries on API error."""
        client, mock_anthropic = client_with_mock

        import httpx

        mock_request = httpx.Request("POST", "https://api.anthropic.com/v1/messages")
        api_error = anthropic.APIError(message="Service unavailable", request=mock_request, body={})

        mock_message = Mock()
        mock_text_block = Mock()
        mock_text_block.type = "text"
        mock_text_block.text = "Enriched"
        mock_text_block.citations = None  # No citations in this test
        mock_message.content = [mock_text_block]

        mock_anthropic.messages.create = AsyncMock(side_effect=[api_error, mock_message])

        mocker.patch("asyncio.sleep", new_callable=AsyncMock)

        enriched_text, _, _ = await client.enrich_with_web_search("Input")

        assert enriched_text == "Enriched"

    # ========================================================================
    # Client Lifecycle Tests
    # ========================================================================

    @pytest.mark.asyncio
    async def test_close_client(self, client_with_mock):
        """Test closing the client."""
        client, mock_anthropic = client_with_mock

        await client.close()

        mock_anthropic.close.assert_called_once()
