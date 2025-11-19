"""
Anthropic Claude API client implementation.

This module provides the concrete implementation of the LLMProvider protocol
using Anthropic's Claude Sonnet 4.5 model via the official Python SDK.

All methods use async/await for non-blocking I/O and include retry logic
for handling transient API failures.
"""

import logging

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
        _model: Claude model identifier (e.g., claude-sonnet-4-5-20250929)
        _max_tokens: Maximum tokens for model responses
    """

    def __init__(
        self,
        api_key: str,
        model: str = "claude-sonnet-4-5-20250929",
        max_tokens: int = 4096,
    ):
        """
        Initialize Anthropic client.

        Args:
            api_key: Anthropic API key
            model: Claude model identifier
            max_tokens: Maximum tokens for responses (default: 4096)
        """
        self._client = anthropic.AsyncAnthropic(api_key=api_key)
        self._model = model
        self._max_tokens = max_tokens

        logger.info(f"Initialized AnthropicClient with model: {model}")

    @retry_with_backoff(
        max_retries=3,
        initial_delay=1.0,
        exceptions=(anthropic.APIError, anthropic.APITimeoutError),
    )
    async def formalize(
        self,
        informal_text: str,
        temperature: float = 0.3,
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
            temperature: Sampling temperature (0.0-1.0, default: 0.3)
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
                model=self._model,
                max_tokens=self._max_tokens,
                temperature=temperature,
                messages=messages,
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
                max_tokens=self._max_tokens,
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
                max_tokens=self._max_tokens,
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

    async def close(self) -> None:
        """
        Close the Anthropic client and cleanup resources.

        This method should be called when the client is no longer needed,
        typically at application shutdown.
        """
        await self._client.close()
        logger.info("AnthropicClient closed")
