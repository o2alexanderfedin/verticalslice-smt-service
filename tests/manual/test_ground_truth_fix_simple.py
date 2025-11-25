"""Simple manual test for ground truth vs claims fix using the API."""

import asyncio

import httpx


async def test_via_api():
    """Test via the running API service."""

    # Problematic input
    test_text = "Apples count is 5. This count must be strictly greater than 5 and less than 10"

    print("Testing SMT Ground Truth vs Claims Fix")
    print("=" * 80)
    print(f"Input: {test_text}")
    print("Expected result: unsat (contradiction)")
    print("=" * 80)

    async with httpx.AsyncClient(timeout=60.0) as client:
        response = await client.post(
            "http://localhost:8000/pipeline/process",
            json={"informal_text": test_text, "skip_formalization": True},
        )

        if response.status_code != 200:
            print(f"\n❌ API call failed: {response.status_code}")
            print(response.text)
            return False

        result = response.json()

        print(f"\n1. Formal text: {result.get('formal_text', 'N/A')}")
        print(f"\n2. SMT-LIB code:\n{result['smt_lib_code']}")
        print(f"\n3. Solver result: {result['check_sat_result']}")
        print(f"4. Solver success: {result['solver_success']}")

        if result.get("model"):
            print(f"5. Model: {result['model']}")
        if result.get("unsat_core"):
            print(f"5. Unsat core: {result['unsat_core']}")

        print("\n" + "=" * 80)

        if result["check_sat_result"] == "unsat":
            print("✅ SUCCESS: Fix is working!")
            print("   The solver correctly detected the contradiction:")
            print("   - Ground truth: count = 5")
            print("   - Claim: count > 5")
            print("   - Result: unsat (5 is not > 5)")
            return True
        else:
            print(f"❌ FAILURE: Expected 'unsat' but got '{result['check_sat_result']}'")
            print("   The fix is NOT working correctly.")
            return False


async def main():
    """Run the test."""
    try:
        success = await test_via_api()
        return 0 if success else 1
    except Exception as e:
        print(f"\n❌ Test failed with error: {e}")
        import traceback

        traceback.print_exc()
        return 1


if __name__ == "__main__":
    exit_code = asyncio.run(main())
    exit(exit_code)
