#!/bin/bash
set -e

# Integration Tests Script
# Runs integration tests against the deployed environment

DEPLOY_URL="${DEPLOY_URL:-http://localhost:8000}"

echo "========================================="
echo "Running Integration Tests"
echo "========================================="
echo "Target URL: $DEPLOY_URL"
echo ""

# Create a Python integration test script
cat > /tmp/integration_test.py << 'EOF'
import os
import sys
import asyncio
import httpx
from typing import Dict, Any

DEPLOY_URL = os.environ.get("DEPLOY_URL", "http://localhost:8000")

async def test_full_pipeline():
    """Test complete pipeline with a valid input."""
    print("Running: Full Pipeline Test")

    async with httpx.AsyncClient(timeout=60.0) as client:
        response = await client.post(
            f"{DEPLOY_URL}/pipeline/process",
            json={
                "informal_text": "x must be greater than 5 and less than 10"
            }
        )

        assert response.status_code == 200, f"Expected 200, got {response.status_code}"

        data = response.json()

        # Check required fields
        required_fields = [
            "informal_text",
            "formal_text",
            "formalization_similarity",
            "smt_lib_code",
            "extraction_degradation",
            "check_sat_result",
            "solver_success",
            "metrics",
            "passed_all_checks",
            "requires_manual_review"
        ]

        for field in required_fields:
            assert field in data, f"Missing required field: {field}"

        # Check quality thresholds
        assert data["formalization_similarity"] >= 0.91, \
            f"Formalization similarity too low: {data['formalization_similarity']}"

        assert data["extraction_degradation"] <= 0.05, \
            f"Extraction degradation too high: {data['extraction_degradation']}"

        assert data["solver_success"] is True, "Solver validation failed"

        assert data["check_sat_result"] == "sat", \
            f"Expected sat result, got {data['check_sat_result']}"

        print(f"  ✓ Formalization similarity: {data['formalization_similarity']:.4f}")
        print(f"  ✓ Extraction degradation: {data['extraction_degradation']:.4f}")
        print(f"  ✓ Solver result: {data['check_sat_result']}")
        print(f"  ✓ All quality checks passed: {data['passed_all_checks']}")

    print("  Status: PASSED\n")
    return True

async def test_unsatisfiable_constraint():
    """Test pipeline with unsatisfiable constraint."""
    print("Running: Unsatisfiable Constraint Test")

    async with httpx.AsyncClient(timeout=60.0) as client:
        response = await client.post(
            f"{DEPLOY_URL}/pipeline/process",
            json={
                "informal_text": "x must be greater than 10 and less than 5"
            }
        )

        assert response.status_code == 200, f"Expected 200, got {response.status_code}"

        data = response.json()

        # Should complete successfully but return unsat
        assert data["solver_success"] is True, "Solver validation failed"
        assert data["check_sat_result"] == "unsat", \
            f"Expected unsat result, got {data['check_sat_result']}"

        print(f"  ✓ Solver result: {data['check_sat_result']}")
        print(f"  ✓ Correctly identified unsatisfiable constraint")

    print("  Status: PASSED\n")
    return True

async def test_multiple_variables():
    """Test pipeline with multiple variables."""
    print("Running: Multiple Variables Test")

    async with httpx.AsyncClient(timeout=60.0) as client:
        response = await client.post(
            f"{DEPLOY_URL}/pipeline/process",
            json={
                "informal_text": "the sum of a and b must equal 10"
            }
        )

        assert response.status_code == 200, f"Expected 200, got {response.status_code}"

        data = response.json()

        assert data["solver_success"] is True, "Solver validation failed"
        assert data["check_sat_result"] == "sat", \
            f"Expected sat result, got {data['check_sat_result']}"

        # Check that SMT-LIB code contains both variables
        smt_code = data["smt_lib_code"].lower()
        assert "a" in smt_code and "b" in smt_code, \
            "SMT-LIB code should contain both variables a and b"

        print(f"  ✓ Multiple variables handled correctly")
        print(f"  ✓ Solver result: {data['check_sat_result']}")

    print("  Status: PASSED\n")
    return True

async def test_examples_endpoint():
    """Test examples endpoint returns valid data."""
    print("Running: Examples Endpoint Test")

    async with httpx.AsyncClient(timeout=10.0) as client:
        response = await client.get(f"{DEPLOY_URL}/pipeline/examples")

        assert response.status_code == 200, f"Expected 200, got {response.status_code}"

        data = response.json()

        assert isinstance(data, list), "Examples should be a list"
        assert len(data) > 0, "Examples should not be empty"

        # Check first example has required structure
        if data:
            example = data[0]
            assert "text" in example, "Example missing 'text' field"
            assert "description" in example, "Example missing 'description' field"
            assert "expected_result" in example, "Example missing 'expected_result' field"

        print(f"  ✓ Found {len(data)} examples")
        print(f"  ✓ Examples have correct structure")

    print("  Status: PASSED\n")
    return True

async def test_error_handling():
    """Test error handling with invalid input."""
    print("Running: Error Handling Test")

    async with httpx.AsyncClient(timeout=30.0) as client:
        response = await client.post(
            f"{DEPLOY_URL}/pipeline/process",
            json={
                "informal_text": ""
            }
        )

        # Should return 422 for invalid input
        assert response.status_code == 422, \
            f"Expected 422 for empty input, got {response.status_code}"

        print(f"  ✓ Empty input correctly rejected with HTTP 422")

    print("  Status: PASSED\n")
    return True

async def main():
    """Run all integration tests."""
    print(f"Target: {DEPLOY_URL}\n")

    tests = [
        test_full_pipeline,
        test_unsatisfiable_constraint,
        test_multiple_variables,
        test_examples_endpoint,
        test_error_handling,
    ]

    passed = 0
    failed = 0

    for test in tests:
        try:
            await test()
            passed += 1
        except AssertionError as e:
            print(f"  Status: FAILED - {e}\n")
            failed += 1
        except Exception as e:
            print(f"  Status: ERROR - {e}\n")
            failed += 1

    print("=" * 45)
    print("Integration Tests Summary")
    print("=" * 45)
    print(f"Total Tests: {passed + failed}")
    print(f"Passed: {passed}")
    print(f"Failed: {failed}")
    print("=" * 45)

    if failed > 0:
        print("Integration Tests: FAILED")
        print("=" * 45)
        sys.exit(1)
    else:
        print("Integration Tests: PASSED")
        print("=" * 45)
        sys.exit(0)

if __name__ == "__main__":
    asyncio.run(main())
EOF

# Run the Python integration test script
python3 /tmp/integration_test.py
