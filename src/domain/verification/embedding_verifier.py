"""Embedding-based semantic verification.

Centralizes cosine similarity and degradation calculations.
"""

import numpy as np
import numpy.typing as npt
from sklearn.metrics.pairwise import cosine_similarity


class EmbeddingDistanceVerifier:
    """Verifies semantic preservation using embedding distances."""

    def calculate_similarity(
        self, embedding1: npt.NDArray[np.float32], embedding2: npt.NDArray[np.float32]
    ) -> float:
        """Calculate cosine similarity between two embeddings.

        Args:
            embedding1: First embedding vector
            embedding2: Second embedding vector

        Returns:
            Cosine similarity score (0.0 to 1.0, higher is better)
        """
        # Reshape to 2D arrays for sklearn
        emb1 = embedding1.reshape(1, -1)
        emb2 = embedding2.reshape(1, -1)

        # Calculate cosine similarity
        similarity = cosine_similarity(emb1, emb2)[0][0]

        # Ensure it's in valid range
        return float(np.clip(similarity, 0.0, 1.0))

    def calculate_degradation(
        self, embedding_source: npt.NDArray[np.float32], embedding_target: npt.NDArray[np.float32]
    ) -> float:
        """Calculate information degradation between source and target.

        Degradation is defined as: 1 - similarity
        Lower degradation means less information loss.

        Args:
            embedding_source: Source text embedding
            embedding_target: Target text embedding

        Returns:
            Degradation score (0.0 to 1.0, lower is better)
        """
        similarity = self.calculate_similarity(embedding_source, embedding_target)
        return 1.0 - similarity
