"""Unit tests for SentenceTransformerProvider.

Tests cover:
- Model loading and caching
- Embedding generation
- Normalization and dimensionality
- Thread pool execution
- Error handling
- Edge cases (empty text, long text)
"""

from unittest.mock import AsyncMock, Mock

import numpy as np
import pytest

from src.infrastructure.embeddings.sentence_transformer import SentenceTransformerProvider


class TestSentenceTransformerProvider:
    """Tests for SentenceTransformerProvider."""

    @pytest.fixture
    def mock_sentence_transformer(self, mocker):
        """Create mock SentenceTransformer model."""
        mock_model = Mock()
        mock_model.get_sentence_embedding_dimension.return_value = 384
        mock_model.encode.return_value = np.random.rand(384).astype(np.float32)

        mocker.patch(
            "src.infrastructure.embeddings.sentence_transformer.SentenceTransformer",
            return_value=mock_model,
        )

        return mock_model

    # ========================================================================
    # Initialization Tests
    # ========================================================================

    def test_initialization_loads_model(self, mock_sentence_transformer):
        """Test that initialization loads the model."""
        provider = SentenceTransformerProvider()

        assert provider._model == mock_sentence_transformer
        assert provider._embedding_dim == 384
        assert provider._model_name == "sentence-transformers/all-MiniLM-L6-v2"

    def test_initialization_with_custom_model_name(self, mocker):
        """Test initialization with custom model name."""
        mock_model = Mock()
        mock_model.get_sentence_embedding_dimension.return_value = 768

        mock_st = mocker.patch(
            "src.infrastructure.embeddings.sentence_transformer.SentenceTransformer",
            return_value=mock_model,
        )

        provider = SentenceTransformerProvider(model_name="sentence-transformers/all-mpnet-base-v2")

        mock_st.assert_called_once_with("sentence-transformers/all-mpnet-base-v2")
        assert provider._embedding_dim == 768

    def test_model_loaded_once_during_init(self, mocker):
        """Test model is loaded only once during initialization."""
        mock_st_class = mocker.patch(
            "src.infrastructure.embeddings.sentence_transformer.SentenceTransformer"
        )
        mock_model = Mock()
        mock_model.get_sentence_embedding_dimension.return_value = 384
        mock_st_class.return_value = mock_model

        provider = SentenceTransformerProvider()

        # Model should be loaded exactly once
        assert mock_st_class.call_count == 1

        # Subsequent calls should not reload
        _ = provider._model
        _ = provider._embedding_dim
        assert mock_st_class.call_count == 1

    # ========================================================================
    # Embedding Generation Tests
    # ========================================================================

    @pytest.mark.asyncio
    async def test_embed_generates_embedding(self, mock_sentence_transformer):
        """Test embedding generation returns correct shape and type."""
        provider = SentenceTransformerProvider()

        # Setup mock to return normalized embedding
        expected_embedding = np.random.rand(384).astype(np.float32)
        mock_sentence_transformer.encode.return_value = expected_embedding

        result = await provider.embed("Test text")

        assert isinstance(result, np.ndarray)
        assert result.shape == (384,)
        assert result.dtype == np.float32
        mock_sentence_transformer.encode.assert_called_once()

    @pytest.mark.asyncio
    async def test_embed_normalizes_embeddings(self, mock_sentence_transformer):
        """Test embeddings are normalized."""
        provider = SentenceTransformerProvider()

        embedding = np.random.rand(384).astype(np.float32)
        mock_sentence_transformer.encode.return_value = embedding

        await provider.embed("Test text")

        # Check normalize_embeddings=True was passed
        call_kwargs = mock_sentence_transformer.encode.call_args[1]
        assert call_kwargs["normalize_embeddings"] is True
        assert call_kwargs["convert_to_numpy"] is True
        assert call_kwargs["show_progress_bar"] is False

    @pytest.mark.asyncio
    async def test_embed_runs_in_thread_pool(self, mock_sentence_transformer, mocker):
        """Test embedding computation runs in thread pool executor."""
        provider = SentenceTransformerProvider()

        # Mock run_in_executor
        mock_loop = AsyncMock()
        mock_loop.run_in_executor = AsyncMock(return_value=np.random.rand(384).astype(np.float32))
        mocker.patch("asyncio.get_event_loop", return_value=mock_loop)

        await provider.embed("Test text")

        # Should have used thread pool executor
        mock_loop.run_in_executor.assert_called_once()
        call_args = mock_loop.run_in_executor.call_args[0]
        assert call_args[0] is None  # Default executor
        assert callable(call_args[1])  # _compute_embedding method

    @pytest.mark.asyncio
    async def test_embed_with_empty_string(self, mock_sentence_transformer):
        """Test embedding generation with empty string."""
        provider = SentenceTransformerProvider()

        mock_sentence_transformer.encode.return_value = np.random.rand(384).astype(np.float32)

        result = await provider.embed("")

        assert isinstance(result, np.ndarray)
        assert result.shape == (384,)
        mock_sentence_transformer.encode.assert_called_once_with(
            "", normalize_embeddings=True, show_progress_bar=False, convert_to_numpy=True
        )

    @pytest.mark.asyncio
    async def test_embed_with_long_text(self, mock_sentence_transformer):
        """Test embedding generation with very long text."""
        provider = SentenceTransformerProvider()

        # Text longer than typical token limit (512 tokens)
        long_text = "word " * 1000  # ~1000 tokens

        mock_sentence_transformer.encode.return_value = np.random.rand(384).astype(np.float32)

        result = await provider.embed(long_text)

        assert isinstance(result, np.ndarray)
        assert result.shape == (384,)

    @pytest.mark.asyncio
    async def test_compute_embedding_synchronous(self, mock_sentence_transformer):
        """Test _compute_embedding is synchronous method."""
        provider = SentenceTransformerProvider()

        embedding = np.random.rand(384).astype(np.float64)  # Wrong dtype
        mock_sentence_transformer.encode.return_value = embedding

        # Call synchronous method directly
        result = provider._compute_embedding("Test text")

        assert result.dtype == np.float32  # Should be converted
        assert result.shape == (384,)

    # ========================================================================
    # Error Handling Tests
    # ========================================================================

    @pytest.mark.asyncio
    async def test_embed_handles_model_failure(self, mock_sentence_transformer, mocker):
        """Test embed handles model inference failure."""
        provider = SentenceTransformerProvider()

        # Mock run_in_executor to raise exception
        mock_loop = AsyncMock()
        mock_loop.run_in_executor = AsyncMock(side_effect=RuntimeError("Model inference failed"))
        mocker.patch("asyncio.get_event_loop", return_value=mock_loop)

        with pytest.raises(RuntimeError, match="Failed to generate embedding"):
            await provider.embed("Test text")

    @pytest.mark.asyncio
    async def test_embed_handles_unexpected_exception(self, mock_sentence_transformer, mocker):
        """Test embed handles unexpected exceptions."""
        provider = SentenceTransformerProvider()

        # Mock run_in_executor to raise unexpected exception
        mock_loop = AsyncMock()
        mock_loop.run_in_executor = AsyncMock(side_effect=ValueError("Unexpected error"))
        mocker.patch("asyncio.get_event_loop", return_value=mock_loop)

        with pytest.raises(RuntimeError, match="Failed to generate embedding"):
            await provider.embed("Test text")

    def test_initialization_handles_model_loading_failure(self, mocker):
        """Test initialization handles model loading failure."""
        mocker.patch(
            "src.infrastructure.embeddings.sentence_transformer.SentenceTransformer",
            side_effect=OSError("Model not found"),
        )

        with pytest.raises(OSError, match="Model not found"):
            SentenceTransformerProvider()

    # ========================================================================
    # Embedding Properties Tests
    # ========================================================================

    @pytest.mark.asyncio
    async def test_embedding_dimension_matches_model(self, mocker):
        """Test embedding dimension matches model configuration."""
        mock_model = Mock()
        mock_model.get_sentence_embedding_dimension.return_value = 768

        mocker.patch(
            "src.infrastructure.embeddings.sentence_transformer.SentenceTransformer",
            return_value=mock_model,
        )

        provider = SentenceTransformerProvider()

        assert provider._embedding_dim == 768

    @pytest.mark.asyncio
    async def test_multiple_embeds_reuse_model(self, mock_sentence_transformer):
        """Test multiple embedding calls reuse the same model."""
        provider = SentenceTransformerProvider()

        mock_sentence_transformer.encode.return_value = np.random.rand(384).astype(np.float32)

        # Generate multiple embeddings
        await provider.embed("Text 1")
        await provider.embed("Text 2")
        await provider.embed("Text 3")

        # Model should be called 3 times but not reloaded
        assert mock_sentence_transformer.encode.call_count == 3

        # Model loading should have happened only once (during init)
        # We can verify this by checking the model instance hasn't changed
        assert provider._model == mock_sentence_transformer

    @pytest.mark.asyncio
    async def test_embed_preserves_embedding_dtype(self, mock_sentence_transformer):
        """Test embedding dtype is preserved as float32."""
        provider = SentenceTransformerProvider()

        # Return different dtype
        embedding_float64 = np.random.rand(384).astype(np.float64)
        mock_sentence_transformer.encode.return_value = embedding_float64

        result = await provider.embed("Test")

        # Should be converted to float32
        assert result.dtype == np.float32
