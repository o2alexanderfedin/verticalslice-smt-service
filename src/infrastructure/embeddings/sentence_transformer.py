"""
SentenceTransformer embedding provider implementation.

This module provides the concrete implementation of the EmbeddingProvider protocol
using the sentence-transformers library with the all-MiniLM-L6-v2 model.

The model runs locally (no API calls) and is loaded once at initialization for
performance. All embedding computations are offloaded to a thread pool executor
to prevent blocking the async event loop.
"""

import asyncio
import logging

import numpy as np
import numpy.typing as npt
from sentence_transformers import SentenceTransformer

logger = logging.getLogger(__name__)


class SentenceTransformerProvider:
    """
    SentenceTransformer embedding provider implementing EmbeddingProvider protocol.

    This provider generates dense vector embeddings for text using the
    all-MiniLM-L6-v2 model from sentence-transformers. The model is optimized
    for semantic similarity tasks and produces 384-dimensional embeddings.

    The model is loaded once during initialization and reused for all embedding
    operations. Computation is offloaded to a thread pool to avoid blocking
    the async event loop (embedding generation is CPU-bound, not I/O-bound).

    Attributes:
        _model: Loaded SentenceTransformer model
        _model_name: Model identifier for loading
        _embedding_dim: Dimensionality of output embeddings (384 for all-MiniLM-L6-v2)
    """

    def __init__(
        self,
        model_name: str = "sentence-transformers/all-MiniLM-L6-v2",
    ):
        """
        Initialize SentenceTransformer provider.

        Loads the specified model into memory. This is an expensive operation
        (downloads model if not cached, loads into RAM) so it's done once
        at initialization rather than per-embedding.

        Args:
            model_name: Hugging Face model identifier (default: all-MiniLM-L6-v2)
        """
        self._model_name = model_name

        logger.info(f"Loading SentenceTransformer model: {model_name}")
        self._model = SentenceTransformer(model_name)
        self._embedding_dim = self._model.get_sentence_embedding_dimension()

        logger.info(
            f"SentenceTransformer model loaded: "
            f"dim={self._embedding_dim}, "
            f"model={model_name}"
        )

    async def embed(self, text: str) -> npt.NDArray[np.float32]:
        """
        Generate embedding vector for text.

        This method offloads the CPU-bound embedding computation to a thread pool
        executor to prevent blocking the async event loop. The embedding is
        normalized for cosine similarity calculations.

        Args:
            text: Input text to embed

        Returns:
            Numpy array of shape (embedding_dim,) with dtype float32
            For all-MiniLM-L6-v2: shape (384,)

        Raises:
            RuntimeError: If embedding generation fails
        """
        logger.debug(f"Generating embedding for text (length={len(text)})")

        try:
            # Run CPU-bound embedding in thread pool to avoid blocking event loop
            loop = asyncio.get_event_loop()
            embedding = await loop.run_in_executor(
                None,  # Use default thread pool executor
                self._compute_embedding,
                text,
            )

            logger.debug(
                f"Embedding generated: " f"shape={embedding.shape}, " f"dtype={embedding.dtype}"
            )

            return embedding

        except Exception as e:
            logger.error(f"Embedding generation failed: {e}")
            raise RuntimeError(f"Failed to generate embedding: {e}") from e

    def _compute_embedding(self, text: str) -> npt.NDArray[np.float32]:
        """
        Compute embedding in thread pool (synchronous, CPU-bound).

        This is a synchronous method that runs in a thread pool executor.
        It performs the actual embedding computation using the loaded model.

        IMPORTANT: This method runs in a separate thread, not in the async
        event loop. Do not use async/await here.

        Args:
            text: Input text to embed

        Returns:
            Normalized numpy array of shape (embedding_dim,) with dtype float32
        """
        # Generate embedding with normalization
        # normalize_embeddings=True ensures cosine similarity can be computed
        # as simple dot product (optimization)
        embedding = self._model.encode(
            text,
            normalize_embeddings=True,
            show_progress_bar=False,
            convert_to_numpy=True,
        )

        # Ensure correct dtype
        embedding = embedding.astype(np.float32)

        return embedding
