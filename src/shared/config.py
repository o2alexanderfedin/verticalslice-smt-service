"""Configuration management using Pydantic Settings.

Loads configuration from environment variables with validation.
"""

from pydantic import Field
from pydantic_settings import BaseSettings, SettingsConfigDict


class Settings(BaseSettings):
    """Application settings loaded from environment variables."""

    # API Configuration
    api_title: str = Field(default="Semantic-Preserving SMT-LIB Pipeline", description="API title")
    api_version: str = Field(default="0.1.0", description="API version")
    api_description: str = Field(
        default="Transform informal text to verified SMT-LIB output with semantic verification",
        description="API description",
    )

    # Anthropic Claude Configuration
    # Uses CLAUDE_CODE_OAUTH_TOKEN environment variable for authentication
    anthropic_api_key: str = Field(
        ...,
        description="Claude API authentication token",
        validation_alias="CLAUDE_CODE_OAUTH_TOKEN",
    )  # Required
    anthropic_model: str = Field(
        default="claude-sonnet-4-5-20250929", description="Claude model identifier"
    )
    anthropic_max_tokens: int = Field(
        default=4096, description="Maximum tokens for Claude responses"
    )
    anthropic_timeout: float = Field(
        default=120.0, description="Timeout for Anthropic API calls in seconds"
    )

    # Embedding Model Configuration
    embedding_model_name: str = Field(
        default="sentence-transformers/all-MiniLM-L6-v2",
        description="HuggingFace model name for embeddings",
    )

    # Pipeline Thresholds
    formalization_similarity_threshold: float = Field(
        default=0.91, ge=0.0, le=1.0, description="Minimum cosine similarity for formalization step"
    )
    formalization_skip_threshold: int = Field(
        default=20,
        ge=0,
        le=100,
        description="Skip formalization for inputs shorter than this (in characters, 0=never skip)",
    )
    extraction_max_degradation: float = Field(
        default=0.05,
        ge=0.0,
        le=1.0,
        description="Maximum allowed information degradation in extraction",
    )

    # Retry Configuration
    formalization_max_retries: int = Field(
        default=3, ge=1, le=10, description="Maximum retries for formalization step"
    )
    extraction_max_retries: int = Field(
        default=5, ge=1, le=10, description="Maximum retries for extraction step"
    )
    validation_max_retries: int = Field(
        default=3, ge=1, le=10, description="Maximum retries for validation step"
    )

    # Temperature Configuration
    formalization_temp_start: float = Field(
        default=0.0, ge=0.0, le=2.0, description="Starting temperature for formalization"
    )
    formalization_temp_step: float = Field(
        default=0.0,
        ge=0.0,
        le=1.0,
        description="Temperature increase per retry for formalization (0.0 = no increase, deterministic)",
    )
    extraction_detail_start: float = Field(
        default=0.5, ge=0.0, le=1.0, description="Starting detail level for extraction"
    )
    extraction_detail_step: float = Field(
        default=0.1, ge=0.0, le=0.5, description="Detail level increase per retry for extraction"
    )
    extraction_skip_retries_threshold: int = Field(
        default=50,
        ge=0,
        le=200,
        description="Skip extraction retries for formal texts shorter than this (in characters, 0=never skip)",
    )

    # Manual Review Triggers
    manual_review_high_retry_threshold: int = Field(
        default=2,
        description="Trigger manual review if any step required more than this many attempts",
    )
    manual_review_similarity_close_threshold: float = Field(
        default=0.02,
        description="Trigger manual review if similarity is within this distance of threshold",
    )

    # Enrichment Configuration
    enrichment_max_searches: int = Field(
        default=5,
        ge=1,
        le=20,
        description="Maximum number of web searches per enrichment request",
    )
    enrichment_timeout: float = Field(
        default=60.0,
        ge=10.0,
        le=300.0,
        description="Timeout for enrichment step in seconds",
    )

    # CORS Configuration
    cors_allowed_origins: list[str] = Field(default=["*"], description="Allowed CORS origins")

    # Logging
    log_level: str = Field(
        default="INFO", description="Logging level (DEBUG, INFO, WARNING, ERROR, CRITICAL)"
    )

    model_config = SettingsConfigDict(
        env_file=".env", env_file_encoding="utf-8", case_sensitive=False, extra="ignore"
    )
