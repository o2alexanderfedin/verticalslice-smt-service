"""
Configuration management for the SMT Pipeline service.

This module uses pydantic-settings for type-safe configuration loading from
environment variables. All configuration is loaded from .env file at startup.

The configuration is organized hierarchically:
- Settings: Root configuration with all subsections
- PipelineConfig: Pipeline-specific thresholds and retry limits
"""

from pydantic import BaseModel, ConfigDict, Field
from pydantic_settings import BaseSettings, SettingsConfigDict


class PipelineConfig(BaseModel):
    """
    Configuration for pipeline execution parameters.

    This nested configuration contains all thresholds and retry limits
    for the three-step pipeline (formalization, extraction, validation).

    Attributes:
        formalization_similarity_threshold: Minimum cosine similarity for Step 1 (0.0-1.0)
        extraction_degradation_threshold: Maximum information loss for Step 2 (0.0-1.0)
        max_formalization_retries: Maximum retry attempts for Step 1
        max_extraction_retries: Maximum retry attempts for Step 2
        max_validation_retries: Maximum retry attempts for Step 3
        smt_solver_timeout: Timeout in seconds for solver execution
    """

    formalization_similarity_threshold: float = Field(
        default=0.91,
        ge=0.0,
        le=1.0,
        description="Minimum cosine similarity between informal and formal text",
    )
    extraction_degradation_threshold: float = Field(
        default=0.05,
        ge=0.0,
        le=1.0,
        description="Maximum information degradation from formal to SMT-LIB",
    )
    max_formalization_retries: int = Field(
        default=3, ge=1, le=10, description="Maximum retry attempts for formalization"
    )
    max_extraction_retries: int = Field(
        default=5, ge=1, le=10, description="Maximum retry attempts for extraction"
    )
    max_validation_retries: int = Field(
        default=3, ge=1, le=10, description="Maximum retry attempts for validation"
    )
    smt_solver_timeout: int = Field(
        default=30, ge=1, le=300, description="Solver execution timeout in seconds"
    )

    model_config = ConfigDict(frozen=True)


class Settings(BaseSettings):
    """
    Root configuration for the SMT Pipeline service.

    Loads configuration from environment variables with support for .env files.
    All fields are validated at startup, ensuring type safety and correct values.

    Environment Variables:
        ANTHROPIC_API_KEY: API key for Anthropic Claude (required)
        ANTHROPIC_MODEL: Model name for Claude (default: claude-3-haiku-20240307)
        ANTHROPIC_ENRICHMENT_MODEL: Model for web search enrichment (default: claude-3-5-sonnet-20241022)
        EMBEDDING_MODEL: Model name for embeddings (default: sentence-transformers/all-MiniLM-L6-v2)
        PIPELINE_*: Pipeline configuration (see PipelineConfig for details)

    Attributes:
        anthropic_api_key: Anthropic API key for LLM calls
        anthropic_model: Claude model identifier for main pipeline
        anthropic_enrichment_model: Claude model identifier for enrichment (web search)
        embedding_model: Sentence-transformers model identifier
        pipeline: Nested pipeline configuration
    """

    # Anthropic LLM configuration
    anthropic_api_key: str = Field(description="Anthropic API key for Claude LLM calls")
    anthropic_model: str = Field(
        default="claude-3-haiku-20240307",
        description="Claude model identifier for main pipeline (formalization, extraction, validation)",
    )
    anthropic_enrichment_model: str = Field(
        default="claude-sonnet-4-5-20250929",
        description="Claude model identifier for enrichment (web search) - must support web_search tool",
    )

    # Embedding model configuration
    embedding_model: str = Field(
        default="sentence-transformers/all-MiniLM-L6-v2",
        description="Sentence-transformers model identifier",
    )

    # Pipeline configuration (nested with env_nested_delimiter)
    pipeline_formalization_similarity_threshold: float = Field(default=0.91, ge=0.0, le=1.0)
    pipeline_extraction_degradation_threshold: float = Field(default=0.05, ge=0.0, le=1.0)
    pipeline_max_formalization_retries: int = Field(default=3, ge=1, le=10)
    pipeline_max_extraction_retries: int = Field(default=5, ge=1, le=10)
    pipeline_max_validation_retries: int = Field(default=3, ge=1, le=10)
    pipeline_smt_solver_timeout: int = Field(default=30, ge=1, le=300)

    model_config = SettingsConfigDict(
        env_file=".env",
        env_file_encoding="utf-8",
        case_sensitive=False,
        extra="ignore",
    )

    @property
    def pipeline(self) -> PipelineConfig:
        """Build PipelineConfig from flattened environment variables."""
        return PipelineConfig(
            formalization_similarity_threshold=self.pipeline_formalization_similarity_threshold,
            extraction_degradation_threshold=self.pipeline_extraction_degradation_threshold,
            max_formalization_retries=self.pipeline_max_formalization_retries,
            max_extraction_retries=self.pipeline_max_extraction_retries,
            max_validation_retries=self.pipeline_max_validation_retries,
            smt_solver_timeout=self.pipeline_smt_solver_timeout,
        )


# Singleton instance for application-wide configuration
_settings: Settings | None = None


def get_settings() -> Settings:
    """
    Get the singleton Settings instance.

    This function ensures only one Settings object is created during the
    application lifecycle, avoiding redundant .env file reads.

    Returns:
        Settings: The singleton configuration instance

    Example:
        >>> settings = get_settings()
        >>> print(settings.anthropic_model)
        claude-3-haiku-20240307
    """
    global _settings
    if _settings is None:
        _settings = Settings()
    return _settings
