"""
Anthropic Claude API client implementation.

This module provides the concrete implementation of the LLMProvider protocol
using Anthropic's Claude Sonnet 4.5 model via the official Python SDK.

All methods use async/await for non-blocking I/O and include retry logic
for handling transient API failures.
"""

import logging
import os

import anthropic

from src.infrastructure.llm.prompts import (
    ERROR_FIXING_PROMPT,
    EXTRACTION_PROMPT,
    FORMALIZATION_PROMPT,
)
from src.shared.retry import retry_with_backoff

logger = logging.getLogger(__name__)


class AnthropicClient:
    """
    Anthropic Claude API client implementing LLMProvider protocol.

    This client handles all three LLM operations required by the pipeline:
    1. Formalization: informal text → formal text
    2. Extraction: formal text → SMT-LIB code
    3. Error fixing: broken SMT-LIB → fixed SMT-LIB

    The client uses async HTTP client with connection pooling and includes
    retry logic with exponential backoff for handling transient failures.

    Attributes:
        _client: Anthropic async client instance
        _model: Claude model identifier for main pipeline (formalization, extraction, validation)
        _enrichment_model: Claude model identifier for enrichment (web search)
    """

    def __init__(self):
        """
        Initialize Anthropic client with dual model support.

        Uses ANTHROPIC_MODEL for main pipeline operations and
        ANTHROPIC_ENRICHMENT_MODEL for web search enrichment.
        """
        api_key = os.environ.get("ANTHROPIC_API_KEY") or os.environ.get("CLAUDE_CODE_OAUTH_TOKEN")
        if not api_key:
            raise RuntimeError(
                "ANTHROPIC_API_KEY or CLAUDE_CODE_OAUTH_TOKEN environment variable is required"
            )
        self._client = anthropic.AsyncAnthropic(api_key=api_key)

        # Main model for formalization, extraction, validation
        self._model = os.environ.get("ANTHROPIC_MODEL", "claude-3-haiku-20240307")

        # Enrichment model for web search (must support web_search tool)
        self._enrichment_model = os.environ.get(
            "ANTHROPIC_ENRICHMENT_MODEL", "claude-sonnet-4-5-20250929"
        )

        logger.info(
            f"Initialized AnthropicClient - Main: {self._model}, Enrichment: {self._enrichment_model}"
        )

    @retry_with_backoff(
        max_retries=3,
        initial_delay=1.0,
        exceptions=(anthropic.APIError, anthropic.APITimeoutError),
    )
    async def formalize(
        self,
        informal_text: str,
        temperature: float = 0,
        previous_attempt: str | None = None,
        previous_similarity: float | None = None,
    ) -> str:
        """
        Transform informal text to formal text using Claude.

        This method uses minimal temperature for more deterministic outputs.
        On retries, it refines the previous attempt based on similarity feedback
        rather than regenerating from scratch.

        Args:
            informal_text: Source natural language text
            temperature: Sampling temperature (0.0-1.0, default: 0)
            previous_attempt: Previous formalization attempt (for refinement)
            previous_similarity: Similarity score of previous attempt

        Returns:
            Formalized text with explicit facts and rules

        Raises:
            anthropic.APIError: If API call fails after retries
        """
        # Build conversation messages
        from anthropic.types import MessageParam

        messages: list[MessageParam] = []

        if previous_attempt is None:
            # First attempt: single message
            prompt = FORMALIZATION_PROMPT.format(informal_text=informal_text)
            messages.append({"role": "user", "content": prompt})

            logger.debug(
                f"Calling formalize (first attempt) with temperature={temperature}, "
                f"text_length={len(informal_text)}"
            )
        else:
            # Refinement: continue conversation with feedback
            initial_prompt = FORMALIZATION_PROMPT.format(informal_text=informal_text)
            messages.append({"role": "user", "content": initial_prompt})
            messages.append({"role": "assistant", "content": previous_attempt})

            # Add refinement feedback
            refinement_prompt = f"""The semantic similarity between your formalization and the original text was {previous_similarity:.4f}, but we need at least 0.91 to ensure meaning is preserved.

Please revise your formalization to stay MUCH closer to the original informal text. Keep the casual tone and don't change the meaning - just clean it up slightly.

Remember the original text:
<INFORMAL-TEXT>
{informal_text}
</INFORMAL-TEXT>

Provide the revised formalization now (just the text, no explanation)."""

            messages.append({"role": "user", "content": refinement_prompt})

            logger.debug(
                f"Calling formalize (refinement) with temperature={temperature}, "
                f"previous_similarity={previous_similarity:.4f}"
            )

        try:
            message = await self._client.messages.create(
                model=self._model, max_tokens=4096, temperature=0, messages=messages
            )

            # Extract text from response
            formal_text = message.content[0].text

            logger.info(
                f"Formalization complete: "
                f"input_length={len(informal_text)}, "
                f"output_length={len(formal_text)}, "
                f"mode={'refinement' if previous_attempt else 'first_attempt'}"
            )

            return formal_text

        except anthropic.APIError as e:
            logger.error(f"Anthropic API error in formalize: {e}")
            raise

    @retry_with_backoff(
        max_retries=3,
        initial_delay=1.0,
        exceptions=(anthropic.APIError, anthropic.APITimeoutError),
    )
    async def extract_to_smtlib(
        self,
        formal_text: str,
        detail_level: float = 0.6,
        previous_attempt: str | None = None,
        previous_degradation: float | None = None,
    ) -> str:
        """
        Extract formal text to SMT-LIB code using Claude.

        This method generates heavily annotated SMT-LIB code with inline comments
        preserving the semantic information from the formal text. The detail_level
        parameter controls annotation verbosity.

        On retries, uses conversation-based refinement: provides the previous SMT-LIB
        code and degradation score, asking Claude to refine it to reduce information loss.

        CRITICAL: Temperature is hardcoded to 0.0 for deterministic code generation.
        This is non-configurable by design - extraction MUST produce consistent,
        reproducible SMT-LIB output. Temperature does NOT vary across retry attempts.

        Args:
            formal_text: Formalized text with explicit semantics
            detail_level: Annotation detail level (0.0-1.0, default: 0.6)
            previous_attempt: Previous SMT-LIB code attempt (for refinement)
            previous_degradation: Degradation score of previous attempt

        Returns:
            Complete annotated SMT-LIB code (executable, or refined version)

        Raises:
            anthropic.APIError: If API call fails after retries
        """
        prompt = EXTRACTION_PROMPT.format(formal_text=formal_text)

        logger.debug(
            f"Calling extract_to_smtlib with detail_level={detail_level}, "
            f"text_length={len(formal_text)}, "
            f"mode={'refinement' if previous_attempt else 'first_attempt'}"
        )

        try:
            # Build conversation based on whether this is a retry
            from anthropic.types import MessageParam

            messages: list[MessageParam] = []

            if previous_attempt is None:
                # First attempt: single message with extraction prompt
                messages.append({"role": "user", "content": prompt})
            else:
                # Refinement: multi-turn conversation with feedback
                # Turn 1: Initial extraction request
                messages.append({"role": "user", "content": prompt})

                # Turn 2: Assistant's previous attempt
                messages.append({"role": "assistant", "content": previous_attempt})

                # Turn 3: Refinement request with degradation feedback
                refinement_prompt = f"""The information degradation was {previous_degradation:.4f}, but we need ≤0.05.

This means too much semantic information was lost when converting to SMT-LIB.

Please revise the SMT-LIB code to better match the formal text. You should:
1. Review if the logic correctly captures ALL constraints from the formal text
2. Check if any constraints are missing or incomplete
3. Verify all variable declarations match the problem domain
4. Fix any logical errors or incomplete assertions
5. Add detailed comments explaining the constraints
6. Include context about variable meanings and relationships

You may need to change the SMT-LIB logic itself, add missing constraints, or enhance annotations -
whatever is needed to reduce information loss and correctly represent the formal text."""
                messages.append({"role": "user", "content": refinement_prompt})

            message = await self._client.messages.create(
                model=self._model,
                max_tokens=4096,
                # CRITICAL: Temperature MUST be 0.0 for deterministic code generation
                # DO NOT make this configurable or allow it to vary across retries
                # Extraction requires consistent, reproducible SMT-LIB output
                temperature=0.0,
                messages=messages,
            )

            smt_code = message.content[0].text

            logger.info(
                f"Extraction complete: "
                f"input_length={len(formal_text)}, "
                f"output_length={len(smt_code)}, "
                f"mode={'refinement' if previous_attempt else 'first_attempt'}"
            )

            return smt_code

        except anthropic.APIError as e:
            logger.error(f"Anthropic API error in extract_to_smtlib: {e}")
            raise

    @retry_with_backoff(
        max_retries=3,
        initial_delay=1.0,
        exceptions=(anthropic.APIError, anthropic.APITimeoutError),
    )
    async def fix_smt_errors(self, smt_code: str, error_message: str) -> str:
        """
        Fix SMT-LIB syntax errors while preserving annotations.

        This method uses Claude to fix syntax errors in SMT-LIB code while
        explicitly instructing it to preserve all comments and annotations.

        Args:
            smt_code: Broken SMT-LIB code with syntax errors
            error_message: Error message from solver execution

        Returns:
            Fixed SMT-LIB code (should execute without errors)

        Raises:
            anthropic.APIError: If API call fails after retries
        """
        prompt = ERROR_FIXING_PROMPT.format(
            smt_code=smt_code,
            error_message=error_message,
        )

        logger.debug(
            f"Calling fix_smt_errors with code_length={len(smt_code)}, "
            f"error={error_message[:100]}"
        )

        try:
            message = await self._client.messages.create(
                model=self._model,
                max_tokens=4096,
                temperature=0.0,  # Deterministic for code fixing
                messages=[{"role": "user", "content": prompt}],
            )

            fixed_code = message.content[0].text

            logger.info(
                f"Error fix complete: "
                f"input_length={len(smt_code)}, "
                f"output_length={len(fixed_code)}"
            )

            return fixed_code

        except anthropic.APIError as e:
            logger.error(f"Anthropic API error in fix_smt_errors: {e}")
            raise

    @retry_with_backoff(
        max_retries=3,
        initial_delay=1.0,
        exceptions=(anthropic.APIError, anthropic.APITimeoutError),
    )
    async def enrich_with_web_search(
        self,
        text: str,
        max_searches: int = 5,
    ) -> tuple[str, int, list[str]]:
        """
        Enrich text with domain knowledge using web search.

        Uses Anthropic's web_search_20250305 tool via the standard Messages API
        to gather relevant context, definitions, and background information for
        domain-specific terminology. Claude autonomously decides when to search
        based on the prompt, and the API executes searches server-side.

        The response includes citations that link enriched text back to sources,
        ensuring traceability of web-sourced information.

        Args:
            text: Input text to enrich
            max_searches: Maximum number of web searches to perform (default: 5)

        Returns:
            Tuple of (enriched_text, search_count, sources_used) where:
            - enriched_text: Text with added context and definitions
            - search_count: Number of web searches performed
            - sources_used: List of source URLs cited

        Raises:
            anthropic.APIError: If API call fails after retries
        """
        logger.debug(
            f"Starting web search enrichment with text_length={len(text)}, "
            f"max_searches={max_searches}"
        )

        # System prompt for enrichment
        system_prompt = """You are an expert at enriching technical and domain-specific text with relevant context.

Your task is to:
1. Identify terms, concepts, or references in the text that may need clarification
2. Use web search to find authoritative definitions and context
3. Return an enriched version of the text that adds helpful context inline or as a preamble

Guidelines:
- Only add context that helps clarify the meaning for SMT-LIB conversion
- Keep the original meaning intact
- Add definitions for domain-specific terms
- Clarify ambiguous references
- Be concise - add context without excessive verbosity
- Format the enriched text clearly

Return the enriched text only, no explanations."""

        user_message = f"""Please enrich the following text with relevant domain knowledge and context:

<text>
{text}
</text>

Search for definitions and background information as needed, then provide the enriched text."""

        try:
            # Call API with web_search tool using enrichment model
            # Note: max_tokens is REQUIRED when using tools
            # Note: Using self._enrichment_model which supports web_search tool
            message = await self._client.messages.create(
                model=self._enrichment_model,  # Use enrichment model (Sonnet) for web search
                max_tokens=4096,  # Required parameter for tool use
                temperature=0,
                system=system_prompt,
                tools=[
                    {
                        "type": "web_search_20250305",
                        "name": "web_search",
                        "max_uses": max_searches,
                    }
                ],
                messages=[{"role": "user", "content": user_message}],
            )

            # Parse response to extract enriched text and sources
            enriched_text = ""
            sources_used: list[str] = []
            search_count = 0
            text_blocks: list[str] = []

            logger.debug(f"Response has {len(message.content)} content blocks")
            for i, block in enumerate(message.content):
                logger.debug(f"Block {i}: type={block.type}")
                if block.type == "text" and hasattr(block, "text"):
                    block_text = block.text  # type: ignore[attr-defined]
                    logger.debug(f"Block {i} text length: {len(block_text)}")
                    text_blocks.append(block_text)
                    # Extract citations from text blocks if available
                    if hasattr(block, "citations") and block.citations:
                        for citation in block.citations:  # type: ignore[attr-defined]
                            if (
                                hasattr(citation, "url")
                                and citation.url
                                and citation.url not in sources_used
                            ):
                                sources_used.append(citation.url)
                elif block.type == "server_tool_use" and hasattr(block, "name") and block.name == "web_search":  # type: ignore[attr-defined]
                    # Count server-side tool uses (web searches)
                    search_count += 1
                elif block.type == "web_search_tool_result":
                    # Extract URLs from search results
                    if hasattr(block, "content") and block.content:
                        for result in block.content:  # type: ignore[attr-defined]
                            if (
                                hasattr(result, "type")
                                and result.type == "web_search_result"  # type: ignore[union-attr]
                                and hasattr(result, "url")
                                and result.url  # type: ignore[union-attr]
                                and result.url not in sources_used  # type: ignore[union-attr]
                            ):
                                sources_used.append(result.url)  # type: ignore[union-attr]

            # Combine all text blocks (usually contains thinking + final enriched text)
            if text_blocks:
                # Take the longest text block as the enriched text (final response is usually longest)
                enriched_text = max(text_blocks, key=len)
                logger.debug(
                    f"Selected longest text block: {len(enriched_text)} chars from {len(text_blocks)} blocks"
                )
            else:
                logger.warning("No text blocks in response, using original")
                enriched_text = text

            logger.info(
                f"Web search enrichment complete: "
                f"search_count={search_count}, "
                f"sources_used={len(sources_used)}, "
                f"output_length={len(enriched_text)}"
            )

            return enriched_text, search_count, sources_used

        except anthropic.APIError as e:
            logger.error(f"Anthropic API error in enrich_with_web_search: {e}")
            raise

    async def close(self) -> None:
        """
        Close the Anthropic client and cleanup resources.

        This method should be called when the client is no longer needed,
        typically at application shutdown.
        """
        await self._client.close()
        logger.info("AnthropicClient closed")
