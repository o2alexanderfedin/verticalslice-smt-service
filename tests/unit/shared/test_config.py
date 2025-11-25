"""Unit tests for Settings configuration."""

import pytest
from pydantic import ValidationError

from src.shared.config import Settings


class TestSettingsDefaults:
    """Test default values for Settings."""

    def test_default_api_config(self) -> None:
        """Test default API configuration values."""
        settings = Settings()
        assert settings.api_title == "Semantic-Preserving SMT-LIB Pipeline"
        assert settings.api_version == "0.1.0"
        assert "informal text" in settings.api_description.lower()

    def test_default_anthropic_config(self) -> None:
        """Test default Anthropic configuration."""
        settings = Settings()
        assert settings.anthropic_timeout == 120.0

    def test_default_embedding_config(self) -> None:
        """Test default embedding configuration."""
        settings = Settings()
        assert "sentence-transformers" in settings.embedding_model_name
        assert "MiniLM" in settings.embedding_model_name

    def test_default_formalization_config(self) -> None:
        """Test default formalization configuration."""
        settings = Settings()
        assert settings.formalization_similarity_threshold == 0.90
        assert settings.formalization_skip_threshold == 200
        assert settings.formalization_max_retries == 5
        assert settings.formalization_temp_start == 0.0
        assert settings.formalization_temp_step == 0.0

    def test_default_extraction_config(self) -> None:
        """Test default extraction configuration."""
        settings = Settings()
        assert settings.extraction_max_degradation == 0.05
        assert settings.extraction_max_retries == 5
        assert settings.extraction_detail_start == 0.5
        assert settings.extraction_detail_step == 0.1
        assert settings.extraction_skip_retries_threshold == 50

    def test_default_validation_config(self) -> None:
        """Test default validation configuration."""
        settings = Settings()
        assert settings.validation_max_retries == 5

    def test_default_enrichment_config(self) -> None:
        """Test default enrichment configuration."""
        settings = Settings()
        assert settings.enrichment_max_searches == 5
        assert settings.enrichment_timeout == 60.0

    def test_default_cors_config(self) -> None:
        """Test default CORS configuration."""
        settings = Settings()
        assert settings.cors_allowed_origins == ["*"]

    def test_default_logging_config(self) -> None:
        """Test default logging configuration."""
        settings = Settings()
        assert settings.log_level == "INFO"


class TestSettingsValidation:
    """Test validation rules for Settings."""

    def test_similarity_threshold_range(self, monkeypatch: pytest.MonkeyPatch) -> None:
        """Test similarity threshold must be between 0.0 and 1.0."""
        # Valid: 0.0
        monkeypatch.setenv("FORMALIZATION_SIMILARITY_THRESHOLD", "0.0")
        settings = Settings()
        assert settings.formalization_similarity_threshold == 0.0

        # Valid: 1.0
        monkeypatch.setenv("FORMALIZATION_SIMILARITY_THRESHOLD", "1.0")
        settings = Settings()
        assert settings.formalization_similarity_threshold == 1.0

        # Invalid: negative
        monkeypatch.setenv("FORMALIZATION_SIMILARITY_THRESHOLD", "-0.1")
        with pytest.raises(ValidationError):
            Settings()

        # Invalid: > 1.0
        monkeypatch.setenv("FORMALIZATION_SIMILARITY_THRESHOLD", "1.1")
        with pytest.raises(ValidationError):
            Settings()

    def test_degradation_range(self, monkeypatch: pytest.MonkeyPatch) -> None:
        """Test degradation must be between 0.0 and 1.0."""
        monkeypatch.setenv("EXTRACTION_MAX_DEGRADATION", "0.5")
        settings = Settings()
        assert settings.extraction_max_degradation == 0.5

        monkeypatch.setenv("EXTRACTION_MAX_DEGRADATION", "1.5")
        with pytest.raises(ValidationError):
            Settings()

    def test_retries_range(self, monkeypatch: pytest.MonkeyPatch) -> None:
        """Test retries must be between 1 and 10."""
        # Valid: 1
        monkeypatch.setenv("FORMALIZATION_MAX_RETRIES", "1")
        settings = Settings()
        assert settings.formalization_max_retries == 1

        # Valid: 10
        monkeypatch.setenv("FORMALIZATION_MAX_RETRIES", "10")
        settings = Settings()
        assert settings.formalization_max_retries == 10

        # Invalid: 0
        monkeypatch.setenv("FORMALIZATION_MAX_RETRIES", "0")
        with pytest.raises(ValidationError):
            Settings()

        # Invalid: 11
        monkeypatch.setenv("FORMALIZATION_MAX_RETRIES", "11")
        with pytest.raises(ValidationError):
            Settings()

    def test_skip_threshold_range(self, monkeypatch: pytest.MonkeyPatch) -> None:
        """Test skip threshold must be between 0 and 1000."""
        monkeypatch.setenv("FORMALIZATION_SKIP_THRESHOLD", "500")
        settings = Settings()
        assert settings.formalization_skip_threshold == 500

        monkeypatch.setenv("FORMALIZATION_SKIP_THRESHOLD", "1001")
        with pytest.raises(ValidationError):
            Settings()

    def test_temperature_range(self, monkeypatch: pytest.MonkeyPatch) -> None:
        """Test temperature must be between 0.0 and 2.0."""
        monkeypatch.setenv("FORMALIZATION_TEMP_START", "1.0")
        settings = Settings()
        assert settings.formalization_temp_start == 1.0

        monkeypatch.setenv("FORMALIZATION_TEMP_START", "2.1")
        with pytest.raises(ValidationError):
            Settings()

    def test_detail_level_range(self, monkeypatch: pytest.MonkeyPatch) -> None:
        """Test detail level must be between 0.0 and 1.0."""
        monkeypatch.setenv("EXTRACTION_DETAIL_START", "0.7")
        settings = Settings()
        assert settings.extraction_detail_start == 0.7

        monkeypatch.setenv("EXTRACTION_DETAIL_START", "1.1")
        with pytest.raises(ValidationError):
            Settings()

    def test_enrichment_max_searches_range(self, monkeypatch: pytest.MonkeyPatch) -> None:
        """Test max searches must be between 1 and 20."""
        monkeypatch.setenv("ENRICHMENT_MAX_SEARCHES", "10")
        settings = Settings()
        assert settings.enrichment_max_searches == 10

        monkeypatch.setenv("ENRICHMENT_MAX_SEARCHES", "21")
        with pytest.raises(ValidationError):
            Settings()

    def test_enrichment_timeout_range(self, monkeypatch: pytest.MonkeyPatch) -> None:
        """Test enrichment timeout must be between 10.0 and 300.0."""
        monkeypatch.setenv("ENRICHMENT_TIMEOUT", "30.0")
        settings = Settings()
        assert settings.enrichment_timeout == 30.0

        monkeypatch.setenv("ENRICHMENT_TIMEOUT", "5.0")
        with pytest.raises(ValidationError):
            Settings()


class TestSettingsEnvironmentLoading:
    """Test loading settings from environment."""

    def test_override_api_title(self, monkeypatch: pytest.MonkeyPatch) -> None:
        """Test overriding API title from environment."""
        monkeypatch.setenv("API_TITLE", "Custom API")
        settings = Settings()
        assert settings.api_title == "Custom API"

    def test_override_multiple_values(self, monkeypatch: pytest.MonkeyPatch) -> None:
        """Test overriding multiple values."""
        monkeypatch.setenv("ANTHROPIC_TIMEOUT", "60.0")
        monkeypatch.setenv("FORMALIZATION_MAX_RETRIES", "3")
        monkeypatch.setenv("LOG_LEVEL", "DEBUG")

        settings = Settings()
        assert settings.anthropic_timeout == 60.0
        assert settings.formalization_max_retries == 3
        assert settings.log_level == "DEBUG"

    def test_case_insensitive_env_vars(self, monkeypatch: pytest.MonkeyPatch) -> None:
        """Test environment variables are case insensitive."""
        monkeypatch.setenv("log_level", "WARNING")
        settings = Settings()
        assert settings.log_level == "WARNING"

    def test_extra_env_vars_ignored(self, monkeypatch: pytest.MonkeyPatch) -> None:
        """Test extra environment variables are ignored."""
        monkeypatch.setenv("UNKNOWN_SETTING", "value")
        Settings()  # Should not raise


class TestSettingsCORSConfig:
    """Test CORS configuration."""

    def test_default_cors_wildcard(self) -> None:
        """Test default CORS allows all origins."""
        settings = Settings()
        assert settings.cors_allowed_origins == ["*"]

    def test_override_cors_origins(self, monkeypatch: pytest.MonkeyPatch) -> None:
        """Test overriding CORS allowed origins."""
        # Note: Pydantic parses JSON lists from env vars
        import json

        origins = ["http://localhost:3000", "https://example.com"]
        monkeypatch.setenv("CORS_ALLOWED_ORIGINS", json.dumps(origins))
        settings = Settings()
        assert settings.cors_allowed_origins == origins
