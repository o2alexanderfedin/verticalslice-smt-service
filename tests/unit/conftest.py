"""Test configuration and fixtures.

Provides:
- Python path setup for imports
- Common fixtures for mocked dependencies
- Test data generators
"""

import sys
from collections.abc import AsyncIterator
from pathlib import Path
from unittest.mock import AsyncMock

import numpy as np
import pytest

# Add project root to Python path for imports
project_root = Path(__file__).parent.parent.parent
if str(project_root) not in sys.path:
    sys.path.insert(0, str(project_root))


# ============================================================================
# Mock Providers
# ============================================================================


@pytest.fixture
def mock_llm_provider() -> AsyncMock:
    """Create mock LLM provider."""
    mock = AsyncMock()
    mock.formalize = AsyncMock(return_value="Formal text output")
    mock.extract = AsyncMock(return_value="(declare-const x Int)\n(assert (> x 5))\n(check-sat)")
    mock.fix_smt_errors = AsyncMock(return_value="(fixed code)")
    mock.fix_smt_errors_with_context = AsyncMock(return_value="(fixed code)")
    return mock


@pytest.fixture
def mock_embedding_provider() -> AsyncMock:
    """Create mock embedding provider."""
    mock = AsyncMock()
    # Return consistent 384-dim embeddings
    mock.embed = AsyncMock(return_value=np.random.rand(384).astype(np.float32))
    return mock


@pytest.fixture
def mock_smt_solver() -> AsyncMock:
    """Create mock SMT solver."""
    mock = AsyncMock()
    mock.execute = AsyncMock(
        return_value={
            "success": True,
            "check_sat_result": "sat",
            "model": "(define-fun x () Int 6)",
            "unsat_core": None,
            "raw_output": "sat\n(define-fun x () Int 6)",
            "error_message": None,
        }
    )
    return mock


@pytest.fixture
def mock_semantic_verifier() -> AsyncMock:
    """Create mock semantic verifier."""
    mock = AsyncMock()
    mock.calculate_similarity = AsyncMock(return_value=0.95)
    mock.calculate_degradation = AsyncMock(return_value=0.02)
    return mock


# ============================================================================
# Sample Data Generators
# ============================================================================


@pytest.fixture
def sample_informal_text() -> str:
    """Sample informal text for testing."""
    return "x must be greater than 5"


@pytest.fixture
def sample_formal_text() -> str:
    """Sample formal text for testing."""
    return "The variable x must satisfy the constraint that it is strictly greater than 5."


@pytest.fixture
def sample_smt_code() -> str:
    """Sample SMT-LIB code for testing."""
    return """(set-logic QF_LIA)
(declare-const x Int)
(assert (> x 5))
(check-sat)
(get-model)"""


@pytest.fixture
def sample_embedding() -> np.ndarray:
    """Sample embedding vector for testing."""
    return np.random.rand(384).astype(np.float32)


@pytest.fixture
def sample_solver_result_sat() -> dict:
    """Sample SAT solver result."""
    return {
        "success": True,
        "check_sat_result": "sat",
        "model": "(define-fun x () Int 10)",
        "unsat_core": None,
        "raw_output": "sat\n(define-fun x () Int 10)",
        "error_message": None,
    }


@pytest.fixture
def sample_solver_result_unsat() -> dict:
    """Sample UNSAT solver result."""
    return {
        "success": True,
        "check_sat_result": "unsat",
        "model": None,
        "unsat_core": "(a1 a2)",
        "raw_output": "unsat\n(a1 a2)",
        "error_message": None,
    }


@pytest.fixture
def sample_solver_result_error() -> dict:
    """Sample error solver result."""
    return {
        "success": False,
        "check_sat_result": "error",
        "model": None,
        "unsat_core": None,
        "raw_output": "Parse error: unexpected token",
        "error_message": "Parse error: unexpected token",
    }


# ============================================================================
# Async Fixtures
# ============================================================================


@pytest.fixture
async def async_mock_llm() -> AsyncIterator[AsyncMock]:
    """Async mock LLM provider."""
    mock = AsyncMock()
    mock.formalize.return_value = "Formal output"
    mock.extract.return_value = "(declare-const x Int)\n(check-sat)"
    yield mock


@pytest.fixture
async def async_mock_embedding() -> AsyncIterator[AsyncMock]:
    """Async mock embedding provider."""
    mock = AsyncMock()
    mock.embed.return_value = np.ones(384, dtype=np.float32)
    yield mock
