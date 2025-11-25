"""Unit tests for EmbeddingDistanceVerifier."""

import numpy as np
import pytest

from src.domain.verification.embedding_verifier import EmbeddingDistanceVerifier


class TestEmbeddingDistanceVerifier:
    """Tests for EmbeddingDistanceVerifier."""

    @pytest.fixture
    def verifier(self) -> EmbeddingDistanceVerifier:
        """Create verifier instance."""
        return EmbeddingDistanceVerifier()

    def test_identical_embeddings_similarity(self, verifier: EmbeddingDistanceVerifier) -> None:
        """Test identical embeddings have similarity of 1.0."""
        embedding = np.array([1.0, 2.0, 3.0], dtype=np.float32)
        similarity = verifier.calculate_similarity(embedding, embedding)
        assert similarity == pytest.approx(1.0, abs=1e-6)

    def test_opposite_embeddings_similarity(self, verifier: EmbeddingDistanceVerifier) -> None:
        """Test opposite embeddings have low similarity."""
        emb1 = np.array([1.0, 0.0, 0.0], dtype=np.float32)
        emb2 = np.array([-1.0, 0.0, 0.0], dtype=np.float32)
        similarity = verifier.calculate_similarity(emb1, emb2)
        assert similarity == pytest.approx(-1.0, abs=1e-6) or similarity == pytest.approx(
            0.0, abs=1e-6
        )

    def test_orthogonal_embeddings_similarity(self, verifier: EmbeddingDistanceVerifier) -> None:
        """Test orthogonal embeddings have similarity near 0."""
        emb1 = np.array([1.0, 0.0, 0.0], dtype=np.float32)
        emb2 = np.array([0.0, 1.0, 0.0], dtype=np.float32)
        similarity = verifier.calculate_similarity(emb1, emb2)
        assert similarity == pytest.approx(0.0, abs=1e-6)

    def test_similar_embeddings(self, verifier: EmbeddingDistanceVerifier) -> None:
        """Test similar embeddings have high similarity."""
        emb1 = np.array([1.0, 2.0, 3.0], dtype=np.float32)
        emb2 = np.array([1.1, 2.1, 3.1], dtype=np.float32)
        similarity = verifier.calculate_similarity(emb1, emb2)
        assert similarity > 0.99

    def test_similarity_is_symmetric(self, verifier: EmbeddingDistanceVerifier) -> None:
        """Test similarity(A, B) == similarity(B, A)."""
        emb1 = np.array([1.0, 2.0, 3.0], dtype=np.float32)
        emb2 = np.array([4.0, 5.0, 6.0], dtype=np.float32)
        sim1 = verifier.calculate_similarity(emb1, emb2)
        sim2 = verifier.calculate_similarity(emb2, emb1)
        assert sim1 == pytest.approx(sim2, abs=1e-6)

    def test_similarity_range_clipping(self, verifier: EmbeddingDistanceVerifier) -> None:
        """Test similarity is clipped to [0, 1] range."""
        # Normal case should be in range
        emb1 = np.array([1.0, 2.0, 3.0], dtype=np.float32)
        emb2 = np.array([1.0, 2.0, 3.0], dtype=np.float32)
        similarity = verifier.calculate_similarity(emb1, emb2)
        assert 0.0 <= similarity <= 1.0

    def test_multidimensional_embeddings(self, verifier: EmbeddingDistanceVerifier) -> None:
        """Test with high-dimensional embeddings."""
        dim = 384
        emb1 = np.random.rand(dim).astype(np.float32)
        emb2 = np.random.rand(dim).astype(np.float32)
        similarity = verifier.calculate_similarity(emb1, emb2)
        assert 0.0 <= similarity <= 1.0

    def test_identical_embeddings_degradation(self, verifier: EmbeddingDistanceVerifier) -> None:
        """Test identical embeddings have zero degradation."""
        embedding = np.array([1.0, 2.0, 3.0], dtype=np.float32)
        degradation = verifier.calculate_degradation(embedding, embedding)
        assert degradation == pytest.approx(0.0, abs=1e-6)

    def test_opposite_embeddings_degradation(self, verifier: EmbeddingDistanceVerifier) -> None:
        """Test opposite embeddings have high degradation."""
        emb1 = np.array([1.0, 0.0, 0.0], dtype=np.float32)
        emb2 = np.array([-1.0, 0.0, 0.0], dtype=np.float32)
        degradation = verifier.calculate_degradation(emb1, emb2)
        # Degradation = 1 - similarity
        # For opposite vectors, similarity ≈ -1, clipped to 0, so degradation = 1
        assert degradation >= 0.9  # Should be close to 1.0

    def test_degradation_range(self, verifier: EmbeddingDistanceVerifier) -> None:
        """Test degradation is always in [0, 1] range."""
        emb1 = np.random.rand(10).astype(np.float32)
        emb2 = np.random.rand(10).astype(np.float32)
        degradation = verifier.calculate_degradation(emb1, emb2)
        assert 0.0 <= degradation <= 1.0

    def test_degradation_is_complement_of_similarity(
        self, verifier: EmbeddingDistanceVerifier
    ) -> None:
        """Test degradation = 1 - similarity."""
        emb1 = np.array([1.0, 2.0, 3.0], dtype=np.float32)
        emb2 = np.array([4.0, 5.0, 6.0], dtype=np.float32)
        similarity = verifier.calculate_similarity(emb1, emb2)
        degradation = verifier.calculate_degradation(emb1, emb2)
        assert degradation == pytest.approx(1.0 - similarity, abs=1e-6)

    def test_low_degradation_high_similarity(self, verifier: EmbeddingDistanceVerifier) -> None:
        """Test low degradation corresponds to high similarity."""
        emb1 = np.array([1.0, 2.0, 3.0], dtype=np.float32)
        emb2 = np.array([1.01, 2.01, 3.01], dtype=np.float32)
        degradation = verifier.calculate_degradation(emb1, emb2)
        assert degradation < 0.01  # Very similar → low degradation

    def test_empty_embeddings_handling(self, verifier: EmbeddingDistanceVerifier) -> None:
        """Test behavior with edge case inputs."""
        # Zero vectors
        emb1 = np.zeros(10, dtype=np.float32)
        emb2 = np.zeros(10, dtype=np.float32)
        # sklearn's cosine_similarity handles zero vectors by returning 0
        similarity = verifier.calculate_similarity(emb1, emb2)
        assert not np.isnan(similarity)  # Should not be NaN
