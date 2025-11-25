"""Manual test for ground truth vs claims fix.

This test verifies that the SMT extraction prompt correctly distinguishes
between ground truth facts and claims to verify.
"""

import asyncio
import sys
from pathlib import Path

# Add project root to path
project_root = Path(__file__).parent.parent.parent
sys.path.insert(0, str(project_root))

from src.infrastructure.llm.client import AnthropicClient  # noqa: E402
from src.infrastructure.smt.cvc5_executor import Cvc5Executor  # noqa: E402


async def test_ground_truth_vs_claims():
    """Test the original problematic case."""

    # Initialize components
    llm_client = AnthropicClient()
    smt_solver = Cvc5Executor()

    # Original problematic input
    problematic_text = (
        "Apples count is 5. This count must be strictly greater than 5 and less than 10"
    )

    print(f"Testing with: {problematic_text}")
    print("=" * 80)

    # Extract SMT-LIB code
    print("\n1. Extracting SMT-LIB code...")
    extraction_result = await llm_client.extract_smt_logic(problematic_text)

    if extraction_result.is_err():
        print(f"❌ Extraction failed: {extraction_result.error}")
        return False

    smt_code = extraction_result.unwrap()
    print(f"\n2. Generated SMT-LIB code:\n{smt_code}")
    print("=" * 80)

    # Execute with solver
    print("\n3. Executing with cvc5 solver...")
    solver_result = await smt_solver.execute(smt_code)

    if solver_result.is_err():
        print(f"❌ Solver execution failed: {solver_result.error}")
        return False

    output = solver_result.unwrap()
    print(f"\n4. Solver result: {output.check_sat_result}")
    print(f"   Success: {output.success}")

    if output.model:
        print(f"   Model: {output.model}")
    if output.unsat_core:
        print(f"   Unsat core: {output.unsat_core}")

    print("\n" + "=" * 80)

    # Verify expected result
    if output.check_sat_result == "unsat":
        print("✅ SUCCESS: Correctly detected contradiction (unsat)")
        print("   The fix is working! Ground truth (count = 5) contradicts claim (count > 5)")
        return True
    else:
        print(f"❌ FAILURE: Expected 'unsat' but got '{output.check_sat_result}'")
        print("   The fix is NOT working correctly")
        return False


async def test_additional_theories():
    """Test with other SMT-LIB theories."""

    llm_client = AnthropicClient()
    smt_solver = Cvc5Executor()

    test_cases = [
        {
            "name": "Bitvectors",
            "text": "Register value is #b0101. This value must equal #b1010",
            "expected": "unsat",
        },
        {"name": "Strings", "text": "Name is 'Alice'. Name must be 'Bob'", "expected": "unsat"},
        {
            "name": "Real Arithmetic",
            "text": "Temperature is 98.6. Temperature must be at least 100.0",
            "expected": "unsat",
        },
        {
            "name": "Satisfiable Case",
            "text": "Count is 5. Count must be less than 10",
            "expected": "sat",
        },
    ]

    print("\n\nTesting additional theories:")
    print("=" * 80)

    results = []

    for test_case in test_cases:
        print(f"\nTest: {test_case['name']}")
        print(f"Input: {test_case['text']}")
        print(f"Expected: {test_case['expected']}")

        # Extract
        extraction_result = await llm_client.extract_smt_logic(test_case["text"])

        if extraction_result.is_err():
            print(f"❌ Extraction failed: {extraction_result.error}")
            results.append(False)
            continue

        smt_code = extraction_result.unwrap()

        # Execute
        solver_result = await smt_solver.execute(smt_code)

        if solver_result.is_err():
            print(f"❌ Solver failed: {solver_result.error}")
            results.append(False)
            continue

        output = solver_result.unwrap()
        actual = output.check_sat_result

        if actual == test_case["expected"]:
            print(f"✅ PASS: Got expected '{actual}'")
            results.append(True)
        else:
            print(f"❌ FAIL: Expected '{test_case['expected']}' but got '{actual}'")
            results.append(False)

    print("\n" + "=" * 80)
    print(f"Theory tests: {sum(results)}/{len(results)} passed")

    return all(results)


async def main():
    """Run all tests."""

    print("SMT Ground Truth vs Claims Fix - Manual Test")
    print("=" * 80)

    # Test main case
    main_test_passed = await test_ground_truth_vs_claims()

    # Test additional theories (optional, may take longer)
    run_theory_tests = input("\nRun additional theory tests? (y/n): ").lower() == "y"

    if run_theory_tests:
        theory_tests_passed = await test_additional_theories()
    else:
        theory_tests_passed = True
        print("Skipping theory tests")

    # Summary
    print("\n" + "=" * 80)
    print("SUMMARY:")
    print(f"  Main test (apples contradiction): {'✅ PASS' if main_test_passed else '❌ FAIL'}")
    if run_theory_tests:
        print(f"  Theory tests: {'✅ PASS' if theory_tests_passed else '❌ FAIL'}")

    if main_test_passed and theory_tests_passed:
        print("\n🎉 All tests passed! The fix is working correctly.")
        return 0
    else:
        print("\n⚠️ Some tests failed. The fix needs adjustment.")
        return 1


if __name__ == "__main__":
    exit_code = asyncio.run(main())
    sys.exit(exit_code)
