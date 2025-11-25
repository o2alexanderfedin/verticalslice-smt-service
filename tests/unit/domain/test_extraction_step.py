"""Unit tests for ExtractionStep.

Tests cover:
- Successful extraction on first attempt
- Retry loop with degradation checks
- Max degradation threshold validation
- Max retries exhausted
- LLM provider exceptions
- Embedding provider exceptions
- Detail level progression
- Skip retries for short formal texts
"""

from unittest.mock import AsyncMock

import numpy as np
import pytest

from src.domain.exceptions import ExtractionError
from src.domain.steps.extraction import ExtractionStep
from src.shared.result import Err, Ok


class TestExtractionStep:
    """Tests for ExtractionStep."""

    @pytest.fixture
    def step(
        self, mock_llm_provider, mock_embedding_provider, mock_semantic_verifier
    ) -> ExtractionStep:
        """Create extraction step with mocked dependencies."""
        return ExtractionStep(
            llm_provider=mock_llm_provider,
            embedding_provider=mock_embedding_provider,
            verifier=mock_semantic_verifier,
            max_degradation=0.05,
            max_retries=5,
            detail_start=0.5,
            detail_step=0.1,
            skip_retries_threshold=50,
        )

    @pytest.mark.asyncio
    async def test_successful_extraction_first_attempt(
        self,
        step: ExtractionStep,
        mock_llm_provider,
        mock_embedding_provider,
        mock_semantic_verifier,
    ) -> None:
        """Test successful extraction on first attempt with low degradation."""
        formal_text = "x" * 100
        smt_code = "(declare-const x Int)\n(assert (> x 5))\n(check-sat)"

        mock_llm_provider.extract_to_smtlib = AsyncMock(return_value=smt_code)

        formal_embedding = np.random.rand(384).astype(np.float32)
        smt_embedding = np.random.rand(384).astype(np.float32)
        mock_embedding_provider.embed = AsyncMock(side_effect=[formal_embedding, smt_embedding])

        mock_semantic_verifier.calculate_degradation = lambda src, fmt: 0.02

        result = await step.execute(formal_text)

        assert isinstance(result, Ok)
        assert result.value.smt_lib_code == smt_code
        assert result.value.degradation == 0.02
        assert result.value.attempts == 1

        assert mock_embedding_provider.embed.call_count == 2
        mock_llm_provider.extract_to_smtlib.assert_called_once()

    @pytest.mark.asyncio
    async def test_retry_loop_with_improving_degradation(
        self,
        step: ExtractionStep,
        mock_llm_provider,
        mock_embedding_provider,
        mock_semantic_verifier,
    ) -> None:
        """Test retry loop when initial degradation is above threshold."""
        formal_text = "x" * 100
        smt_attempts = ["Attempt 1", "Attempt 2", "Attempt 3 - good"]

        mock_llm_provider.extract_to_smtlib = AsyncMock(side_effect=smt_attempts)

        formal_embedding = np.random.rand(384).astype(np.float32)
        smt_embeddings = [
            np.random.rand(384).astype(np.float32),
            np.random.rand(384).astype(np.float32),
            np.random.rand(384).astype(np.float32),
        ]
        mock_embedding_provider.embed = AsyncMock(side_effect=[formal_embedding] + smt_embeddings)

        # Degradation improves: 0.10, 0.07, 0.03 (meets threshold on 3rd)
        degradation_scores = [0.10, 0.07, 0.03]
        call_count = 0

        def get_degradation(src, fmt):
            nonlocal call_count
            result = degradation_scores[call_count]
            call_count += 1
            return result

        mock_semantic_verifier.calculate_degradation = get_degradation

        result = await step.execute(formal_text)

        assert isinstance(result, Ok)
        assert result.value.smt_lib_code == "Attempt 3 - good"
        assert result.value.degradation == 0.03
        assert result.value.attempts == 3

        assert mock_llm_provider.extract_to_smtlib.call_count == 3
        assert mock_embedding_provider.embed.call_count == 4

    @pytest.mark.asyncio
    async def test_max_retries_exhausted_returns_best(
        self,
        step: ExtractionStep,
        mock_llm_provider,
        mock_embedding_provider,
        mock_semantic_verifier,
    ) -> None:
        """Test that max retries returns best result even if above threshold."""
        formal_text = "x" * 100
        smt_attempts = ["Attempt 1", "Attempt 2", "Attempt 3", "Attempt 4", "Attempt 5"]

        mock_llm_provider.extract_to_smtlib = AsyncMock(side_effect=smt_attempts)

        formal_embedding = np.random.rand(384).astype(np.float32)
        smt_embeddings = [np.random.rand(384).astype(np.float32) for _ in range(5)]
        mock_embedding_provider.embed = AsyncMock(side_effect=[formal_embedding] + smt_embeddings)

        # All above threshold, but improving: 0.15, 0.12, 0.10, 0.08, 0.06
        degradation_scores = [0.15, 0.12, 0.10, 0.08, 0.06]
        call_count = 0

        def get_degradation(src, fmt):
            nonlocal call_count
            result = degradation_scores[call_count]
            call_count += 1
            return result

        mock_semantic_verifier.calculate_degradation = get_degradation

        result = await step.execute(formal_text)

        # Returns best (0.06 from attempt 5)
        assert isinstance(result, Ok)
        assert result.value.smt_lib_code == "Attempt 5"
        assert result.value.degradation == 0.06
        assert result.value.attempts == 5

    @pytest.mark.asyncio
    async def test_short_formal_text_skips_retries(
        self,
        step: ExtractionStep,
        mock_llm_provider,
        mock_embedding_provider,
        mock_semantic_verifier,
    ) -> None:
        """Test that short formal texts skip retries and accept first result."""
        formal_text = "x > 5"  # Less than 50 chars
        smt_code = "(assert (> x 5))"

        mock_llm_provider.extract_to_smtlib = AsyncMock(return_value=smt_code)

        formal_embedding = np.random.rand(384).astype(np.float32)
        smt_embedding = np.random.rand(384).astype(np.float32)
        mock_embedding_provider.embed = AsyncMock(side_effect=[formal_embedding, smt_embedding])

        # High degradation, but should be accepted anyway
        mock_semantic_verifier.calculate_degradation = lambda src, fmt: 0.15

        result = await step.execute(formal_text)

        # Should accept first attempt despite high degradation
        assert isinstance(result, Ok)
        assert result.value.attempts == 1
        assert mock_llm_provider.extract_to_smtlib.call_count == 1

    @pytest.mark.asyncio
    async def test_formal_embedding_failure(
        self, step: ExtractionStep, mock_embedding_provider
    ) -> None:
        """Test error handling when formal text embedding computation fails."""
        formal_text = "x" * 100
        mock_embedding_provider.embed = AsyncMock(side_effect=RuntimeError("Embedding failed"))

        result = await step.execute(formal_text)

        assert isinstance(result, Err)
        assert isinstance(result.error, ExtractionError)
        assert "Failed to compute formal text embedding" in str(result.error)
        assert result.error.attempts == 0
        assert result.error.best_degradation == 1.0

    @pytest.mark.asyncio
    async def test_llm_provider_exception_during_extraction(
        self,
        step: ExtractionStep,
        mock_llm_provider,
        mock_embedding_provider,
        mock_semantic_verifier,
    ) -> None:
        """Test that LLM exceptions are handled gracefully."""
        formal_text = "x" * 100

        mock_llm_provider.extract_to_smtlib = AsyncMock(
            side_effect=[
                RuntimeError("LLM timeout"),
                RuntimeError("LLM error"),
                "(check-sat)",
            ]
        )

        formal_embedding = np.random.rand(384).astype(np.float32)
        smt_embedding = np.random.rand(384).astype(np.float32)
        mock_embedding_provider.embed = AsyncMock(side_effect=[formal_embedding, smt_embedding])

        mock_semantic_verifier.calculate_degradation = lambda src, fmt: 0.02

        result = await step.execute(formal_text)

        assert isinstance(result, Ok)
        assert result.value.attempts == 3
        assert mock_llm_provider.extract_to_smtlib.call_count == 3

    @pytest.mark.asyncio
    async def test_all_llm_attempts_fail(
        self, step: ExtractionStep, mock_llm_provider, mock_embedding_provider
    ) -> None:
        """Test when all LLM attempts fail with exceptions."""
        formal_text = "x" * 100

        mock_llm_provider.extract_to_smtlib = AsyncMock(side_effect=RuntimeError("LLM down"))

        formal_embedding = np.random.rand(384).astype(np.float32)
        mock_embedding_provider.embed = AsyncMock(return_value=formal_embedding)

        result = await step.execute(formal_text)

        assert isinstance(result, Err)
        assert isinstance(result.error, ExtractionError)
        assert "failed with exceptions" in str(result.error)
        assert result.error.attempts == 5
        assert result.error.best_degradation == 1.0

    @pytest.mark.asyncio
    async def test_refinement_uses_previous_attempt_context(
        self,
        step: ExtractionStep,
        mock_llm_provider,
        mock_embedding_provider,
        mock_semantic_verifier,
    ) -> None:
        """Test that retry attempts pass previous context."""
        formal_text = "x" * 100
        mock_llm_provider.extract_to_smtlib = AsyncMock(side_effect=["First", "Second"])

        formal_embedding = np.random.rand(384).astype(np.float32)
        smt_embeddings = [np.random.rand(384).astype(np.float32) for _ in range(2)]
        mock_embedding_provider.embed = AsyncMock(side_effect=[formal_embedding] + smt_embeddings)

        degradation_scores = [0.10, 0.03]
        call_count = 0

        def get_degradation(src, fmt):
            nonlocal call_count
            result = degradation_scores[call_count]
            call_count += 1
            return result

        mock_semantic_verifier.calculate_degradation = get_degradation

        result = await step.execute(formal_text)

        assert isinstance(result, Ok)

        first_call = mock_llm_provider.extract_to_smtlib.call_args_list[0]
        assert first_call.kwargs["previous_attempt"] is None
        assert first_call.kwargs["previous_degradation"] is None

        second_call = mock_llm_provider.extract_to_smtlib.call_args_list[1]
        assert second_call.kwargs["previous_attempt"] == "First"
        assert second_call.kwargs["previous_degradation"] == 0.10

    @pytest.mark.asyncio
    async def test_detail_level_progression(
        self,
        step: ExtractionStep,
        mock_llm_provider,
        mock_embedding_provider,
        mock_semantic_verifier,
    ) -> None:
        """Test that detail level increases with each retry."""
        formal_text = "x" * 100
        mock_llm_provider.extract_to_smtlib = AsyncMock(side_effect=["First", "Second", "Third"])

        formal_embedding = np.random.rand(384).astype(np.float32)
        smt_embeddings = [np.random.rand(384).astype(np.float32) for _ in range(3)]
        mock_embedding_provider.embed = AsyncMock(side_effect=[formal_embedding] + smt_embeddings)

        degradation_scores = [0.10, 0.08, 0.03]
        call_count = 0

        def get_degradation(src, fmt):
            nonlocal call_count
            result = degradation_scores[call_count]
            call_count += 1
            return result

        mock_semantic_verifier.calculate_degradation = get_degradation

        await step.execute(formal_text)

        # Verify detail levels: 0.5, 0.6, 0.7
        calls = mock_llm_provider.extract_to_smtlib.call_args_list
        assert calls[0].kwargs["detail_level"] == 0.5
        assert calls[1].kwargs["detail_level"] == 0.6
        assert calls[2].kwargs["detail_level"] == 0.7

    @pytest.mark.asyncio
    async def test_boundary_degradation_exactly_at_threshold(
        self,
        step: ExtractionStep,
        mock_llm_provider,
        mock_embedding_provider,
        mock_semantic_verifier,
    ) -> None:
        """Test that degradation exactly at threshold (0.05) passes."""
        formal_text = "x" * 100
        mock_llm_provider.extract_to_smtlib = AsyncMock(return_value="SMT code")

        formal_embedding = np.random.rand(384).astype(np.float32)
        smt_embedding = np.random.rand(384).astype(np.float32)
        mock_embedding_provider.embed = AsyncMock(side_effect=[formal_embedding, smt_embedding])

        mock_semantic_verifier.calculate_degradation = lambda src, fmt: 0.05

        result = await step.execute(formal_text)

        assert isinstance(result, Ok)
        assert result.value.degradation == 0.05
        assert result.value.attempts == 1
