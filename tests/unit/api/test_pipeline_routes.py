"""Unit tests for Pipeline API routes.

Tests cover:
- Request validation (ProcessRequest)
- Successful processing response
- Pipeline error handling (422)
- Unexpected errors (500)
- Response model validation
- Dependency injection
- Edge cases (empty text, long text, flags)
"""

from unittest.mock import AsyncMock

import pytest
from fastapi import HTTPException
from fastapi.testclient import TestClient

from src.api.models import ProcessResponse
from src.domain.models import PipelineMetrics, VerifiedOutput
from src.shared.result import Err, Ok


class TestPipelineRoutes:
    """Tests for pipeline API routes."""

    @pytest.fixture
    def mock_pipeline_service(self, mocker):
        """Create mock PipelineService."""
        service = AsyncMock()

        # Default successful response
        metrics = PipelineMetrics(
            formalization_attempts=1,
            final_formalization_similarity=0.95,
            formalization_time_seconds=1.2,
            extraction_attempts=1,
            final_extraction_degradation=0.03,
            extraction_time_seconds=1.5,
            validation_attempts=1,
            solver_execution_time_seconds=0.3,
            total_time_seconds=3.0,
            success=True,
        )

        output = VerifiedOutput(
            informal_text="x must be greater than 5",
            enrichment_performed=False,
            enrichment_search_count=None,
            enrichment_sources=None,
            enrichment_time_seconds=None,
            formal_text="The variable x must be greater than 5",
            formalization_similarity=0.95,
            smt_lib_code="(declare-const x Int)\n(assert (> x 5))\n(check-sat)",
            extraction_degradation=0.03,
            check_sat_result="sat",
            model="((x 7))",
            unsat_core=None,
            solver_success=True,
            proof_raw_output="sat\n((x 7))",
            proof_summary="Verification successful",
            metrics=metrics,
            passed_all_checks=True,
        )

        service.process.return_value = Ok(output)
        return service

    @pytest.fixture
    def client_with_mock_service(self, mock_pipeline_service):
        """Create TestClient with mocked pipeline service."""
        # Import after fixtures to avoid circular imports
        from src.api.dependencies import get_pipeline_service
        from src.main import app

        # Override the FastAPI dependency
        app.dependency_overrides[get_pipeline_service] = lambda: mock_pipeline_service

        client = TestClient(app)
        yield client, mock_pipeline_service

        # Clean up
        app.dependency_overrides.clear()

    # ========================================================================
    # Request Validation Tests
    # ========================================================================

    def test_process_request_valid(self, client_with_mock_service):
        """Test valid process request."""
        client, _ = client_with_mock_service

        response = client.post(
            "/pipeline/process", json={"informal_text": "x must be greater than 5"}
        )

        assert response.status_code == 200
        data = response.json()
        assert "informal_text" in data
        assert "formal_text" in data
        assert "smt_lib_code" in data

    def test_process_request_missing_informal_text(self, client_with_mock_service):
        """Test request with missing informal_text returns 422."""
        client, _ = client_with_mock_service

        response = client.post("/pipeline/process", json={})

        assert response.status_code == 422
        data = response.json()
        assert "detail" in data

    def test_process_request_empty_informal_text(self, client_with_mock_service):
        """Test request with empty informal_text returns 422."""
        client, _ = client_with_mock_service

        response = client.post("/pipeline/process", json={"informal_text": ""})

        assert response.status_code == 422

    def test_process_request_very_long_text(self, client_with_mock_service):
        """Test request with maximum length text (100K chars)."""
        client, mock_service = client_with_mock_service

        # Just under the 100K limit
        long_text = "x" * 99999

        response = client.post("/pipeline/process", json={"informal_text": long_text})

        assert response.status_code == 200
        # Verify service was called with long text
        mock_service.process.assert_called_once()
        call_args = mock_service.process.call_args[0]
        assert len(call_args[0]) == 99999

    def test_process_request_exceeds_max_length(self, client_with_mock_service):
        """Test request exceeding 100K character limit returns 422."""
        client, _ = client_with_mock_service

        # Over the 100K limit
        too_long_text = "x" * 100001

        response = client.post("/pipeline/process", json={"informal_text": too_long_text})

        assert response.status_code == 422

    def test_process_request_with_skip_formalization_true(self, client_with_mock_service):
        """Test request with skip_formalization=true."""
        client, mock_service = client_with_mock_service

        response = client.post(
            "/pipeline/process", json={"informal_text": "x > 5", "skip_formalization": True}
        )

        assert response.status_code == 200
        # Verify skip_formalization was passed to service
        mock_service.process.assert_called_once()
        call_kwargs = mock_service.process.call_args[1]
        assert call_kwargs["skip_formalization"] is True

    def test_process_request_with_skip_formalization_false(self, client_with_mock_service):
        """Test request with explicit skip_formalization=false."""
        client, mock_service = client_with_mock_service

        response = client.post(
            "/pipeline/process", json={"informal_text": "x > 5", "skip_formalization": False}
        )

        assert response.status_code == 200
        call_kwargs = mock_service.process.call_args[1]
        assert call_kwargs["skip_formalization"] is False

    def test_process_request_with_enrich_true(self, client_with_mock_service):
        """Test request with enrich=true."""
        client, mock_service = client_with_mock_service

        response = client.post("/pipeline/process", json={"informal_text": "x > 5", "enrich": True})

        assert response.status_code == 200
        call_kwargs = mock_service.process.call_args[1]
        assert call_kwargs["enrich"] is True

    def test_process_request_with_enrich_false(self, client_with_mock_service):
        """Test request with explicit enrich=false."""
        client, mock_service = client_with_mock_service

        response = client.post(
            "/pipeline/process", json={"informal_text": "x > 5", "enrich": False}
        )

        assert response.status_code == 200
        call_kwargs = mock_service.process.call_args[1]
        assert call_kwargs["enrich"] is False

    # ========================================================================
    # Successful Response Tests
    # ========================================================================

    def test_successful_process_returns_complete_response(self, client_with_mock_service):
        """Test successful processing returns all fields."""
        client, _ = client_with_mock_service

        response = client.post(
            "/pipeline/process", json={"informal_text": "x must be greater than 5"}
        )

        assert response.status_code == 200
        data = response.json()

        # Verify all required fields
        assert data["informal_text"] == "x must be greater than 5"
        assert data["formal_text"] == "The variable x must be greater than 5"
        assert data["formalization_similarity"] == 0.95
        assert "(declare-const x Int)" in data["smt_lib_code"]
        assert data["extraction_degradation"] == 0.03
        assert data["check_sat_result"] == "sat"
        assert data["model"] == "((x 7))"
        assert data["unsat_core"] is None
        assert data["solver_success"] is True
        assert data["passed_all_checks"] is True

    def test_successful_response_includes_proof(self, client_with_mock_service):
        """Test successful response includes proof data."""
        client, _ = client_with_mock_service

        response = client.post("/pipeline/process", json={"informal_text": "test"})

        data = response.json()
        assert "proof" in data
        assert data["proof"]["raw_output"] == "sat\n((x 7))"
        assert data["proof"]["summary"] == "Verification successful"

    def test_successful_response_includes_metrics(self, client_with_mock_service):
        """Test successful response includes detailed metrics."""
        client, _ = client_with_mock_service

        response = client.post("/pipeline/process", json={"informal_text": "test"})

        data = response.json()
        assert "metrics" in data
        metrics = data["metrics"]
        assert metrics["formalization_attempts"] == 1
        assert metrics["final_formalization_similarity"] == 0.95
        assert metrics["formalization_time_seconds"] == 1.2
        assert metrics["extraction_attempts"] == 1
        assert metrics["final_extraction_degradation"] == 0.03
        assert metrics["total_time_seconds"] == 3.0
        assert metrics["success"] is True

    def test_successful_response_with_enrichment(self, client_with_mock_service, mocker):
        """Test response includes enrichment metadata when enrichment performed."""
        client, mock_service = client_with_mock_service

        # Configure mock to return enrichment data
        output_with_enrichment = VerifiedOutput(
            informal_text="test",
            enrichment_performed=True,
            enrichment_search_count=3,
            enrichment_sources=["https://example.com"],
            enrichment_time_seconds=2.5,
            formal_text="formal",
            formalization_similarity=0.95,
            smt_lib_code="code",
            extraction_degradation=0.03,
            check_sat_result="sat",
            model="model",
            unsat_core=None,
            solver_success=True,
            proof_raw_output="output",
            proof_summary="summary",
            metrics=PipelineMetrics(
                formalization_attempts=1,
                final_formalization_similarity=0.95,
                formalization_time_seconds=1.0,
                extraction_attempts=1,
                final_extraction_degradation=0.03,
                extraction_time_seconds=1.0,
                validation_attempts=1,
                solver_execution_time_seconds=0.5,
                total_time_seconds=3.0,
                success=True,
            ),
            passed_all_checks=True,
        )
        mock_service.process.return_value = Ok(output_with_enrichment)

        response = client.post("/pipeline/process", json={"informal_text": "test", "enrich": True})

        data = response.json()
        assert data["enrichment_performed"] is True
        assert data["enrichment_search_count"] == 3
        assert data["enrichment_sources"] == ["https://example.com"]
        assert data["enrichment_time_seconds"] == 2.5

    # ========================================================================
    # Error Response Tests
    # ========================================================================

    def test_pipeline_error_returns_422(self, client_with_mock_service, mocker):
        """Test pipeline processing error returns 422."""
        client, mock_service = client_with_mock_service

        # Configure mock to return error
        mock_service.process.return_value = Err("Formalization failed: quality threshold not met")

        response = client.post("/pipeline/process", json={"informal_text": "test"})

        assert response.status_code == 422
        data = response.json()
        assert "detail" in data
        assert "Formalization failed" in data["detail"]

    def test_formalization_error_in_detail(self, client_with_mock_service):
        """Test formalization error appears in detail."""
        client, mock_service = client_with_mock_service

        mock_service.process.return_value = Err(
            "Formalization failed: Could not achieve required semantic similarity threshold"
        )

        response = client.post("/pipeline/process", json={"informal_text": "test"})

        assert response.status_code == 422
        assert "Formalization" in response.json()["detail"]

    def test_extraction_error_in_detail(self, client_with_mock_service):
        """Test extraction error appears in detail."""
        client, mock_service = client_with_mock_service

        mock_service.process.return_value = Err(
            "Extraction failed: Information degradation too high"
        )

        response = client.post("/pipeline/process", json={"informal_text": "test"})

        assert response.status_code == 422
        assert "Extraction" in response.json()["detail"]

    def test_validation_error_in_detail(self, client_with_mock_service):
        """Test validation error appears in detail."""
        client, mock_service = client_with_mock_service

        mock_service.process.return_value = Err("Validation failed: Syntax error in SMT code")

        response = client.post("/pipeline/process", json={"informal_text": "test"})

        assert response.status_code == 422
        assert "Validation" in response.json()["detail"]

    def test_unexpected_exception_returns_500(self, client_with_mock_service):
        """Test unexpected exception returns 500."""
        client, mock_service = client_with_mock_service

        # Configure mock to raise unexpected exception
        mock_service.process.side_effect = RuntimeError("Unexpected system error")

        response = client.post("/pipeline/process", json={"informal_text": "test"})

        assert response.status_code == 500
        data = response.json()
        assert "detail" in data
        assert "Internal server error" in data["detail"]

    def test_http_exception_reraised(self, client_with_mock_service):
        """Test HTTPException is re-raised correctly."""
        client, mock_service = client_with_mock_service

        # Configure mock to raise HTTPException
        mock_service.process.side_effect = HTTPException(
            status_code=503, detail="Service temporarily unavailable"
        )

        response = client.post("/pipeline/process", json={"informal_text": "test"})

        # HTTPException should be re-raised as-is
        assert response.status_code == 503
        assert "Service temporarily unavailable" in response.json()["detail"]

    # ========================================================================
    # Response Model Validation Tests
    # ========================================================================

    def test_response_model_validation(self, client_with_mock_service):
        """Test response conforms to ProcessResponse model."""
        client, _ = client_with_mock_service

        response = client.post("/pipeline/process", json={"informal_text": "test"})

        # Should not raise validation error
        ProcessResponse(**response.json())

    def test_response_similarity_within_bounds(self, client_with_mock_service):
        """Test formalization_similarity is between 0 and 1."""
        client, _ = client_with_mock_service

        response = client.post("/pipeline/process", json={"informal_text": "test"})

        data = response.json()
        assert 0.0 <= data["formalization_similarity"] <= 1.0

    def test_response_degradation_within_bounds(self, client_with_mock_service):
        """Test extraction_degradation is between 0 and 1."""
        client, _ = client_with_mock_service

        response = client.post("/pipeline/process", json={"informal_text": "test"})

        data = response.json()
        assert 0.0 <= data["extraction_degradation"] <= 1.0
