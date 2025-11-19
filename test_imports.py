"""Test basic imports to verify module structure."""

def test_shared_imports():
    """Test shared module imports."""
    print("Testing shared module imports...")
    from src.shared.result import Ok, Err, Result
    from src.shared.config import Settings
    from src.shared.logging_config import configure_logging
    print("✓ Shared imports OK")


def test_domain_imports():
    """Test domain module imports."""
    print("Testing domain module imports...")
    from src.domain.models import (
        FormalizationResult,
        ExtractionResult,
        SolverResult,
        PipelineMetrics,
        VerifiedOutput
    )
    from src.domain.exceptions import (
        PipelineError,
        FormalizationError,
        ExtractionError,
        ValidationError
    )
    from src.domain.protocols import (
        LLMProvider,
        EmbeddingProvider,
        SMTSolver,
        SemanticVerifier
    )
    from src.domain.verification.embedding_verifier import EmbeddingDistanceVerifier
    print("✓ Domain imports OK")


def test_infrastructure_imports():
    """Test infrastructure module imports."""
    print("Testing infrastructure module imports...")
    from src.infrastructure.llm.client import AnthropicClient
    from src.infrastructure.llm.prompts import (
        get_formalization_prompt,
        get_extraction_prompt,
        get_error_fixing_prompt
    )
    from src.infrastructure.embeddings.sentence_transformer import SentenceTransformerProvider
    from src.infrastructure.smt.pysmt_executor import PysmtExecutor
    print("✓ Infrastructure imports OK")


def test_application_imports():
    """Test application module imports."""
    print("Testing application module imports...")
    from src.application.pipeline_service import PipelineService
    print("✓ Application imports OK")


def test_api_imports():
    """Test API module imports."""
    print("Testing API module imports...")
    from src.api.models import ProcessRequest, ProcessResponse, ErrorResponse
    from src.api.dependencies import (
        get_settings,
        get_embedding_provider,
        get_llm_provider,
        get_smt_solver,
        get_pipeline_service
    )
    from src.api.routes.pipeline import router
    print("✓ API imports OK")


def test_main_import():
    """Test main application import."""
    print("Testing main application import...")
    from src.main import app
    print("✓ Main application import OK")


def test_examples_import():
    """Test examples module import."""
    print("Testing examples module import...")
    from examples.sample_texts import SAMPLE_TEXTS
    print(f"✓ Examples imports OK ({len(SAMPLE_TEXTS)} samples available)")


if __name__ == "__main__":
    print("=" * 60)
    print("TESTING MODULE IMPORTS")
    print("=" * 60)

    try:
        test_shared_imports()
        test_domain_imports()
        test_infrastructure_imports()
        test_application_imports()
        test_api_imports()
        test_main_import()
        test_examples_import()

        print("=" * 60)
        print("✓ ALL IMPORTS SUCCESSFUL")
        print("=" * 60)
        print("\nThe service structure is complete and all modules are accessible.")
        print("\nNext steps:")
        print("1. Install dependencies: poetry install")
        print("2. Configure .env file with your ANTHROPIC_API_KEY")
        print("3. Run the service: poetry run python -m src.main")
        print("4. Open browser to: http://localhost:8000/docs")

    except Exception as e:
        print("=" * 60)
        print(f"✗ IMPORT ERROR: {e}")
        print("=" * 60)
        import traceback
        traceback.print_exc()
