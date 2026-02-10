#!/usr/bin/env python3
"""Test formalization caching with simple constraint."""

import json
import time

import requests

ENDPOINT = "https://verticalslice-smt-service-gvav8.ondigitalocean.app/pipeline/process"
PAYLOAD = {"informal_text": "x must be greater than 5 and less than 10"}


def test_cache():
    print("=" * 80)
    print("Testing Formalization Caching - v1.16.9")
    print("=" * 80)
    print(f"\nPayload: {json.dumps(PAYLOAD, indent=2)}")
    print(f"Endpoint: {ENDPOINT}\n")

    # First request - cache miss
    print("🔄 Request 1 (Cache Miss - should execute full formalization)")
    print("-" * 80)
    start1 = time.time()
    response1 = requests.post(ENDPOINT, json=PAYLOAD, timeout=120)
    duration1 = time.time() - start1

    print(f"Status Code: {response1.status_code}")
    print(f"Duration: {duration1:.2f}s")

    if response1.status_code == 200:
        data1 = response1.json()
        print("\n✓ Success Response:")
        print(f"  - Check SAT Result: {data1.get('check_sat_result')}")
        print(f"  - Solver Success: {data1.get('solver_success')}")
        print(f"  - Formalization Similarity: {data1.get('formalization_similarity'):.4f}")
        print(f"  - Formalization Attempts: {data1['metrics']['formalization_attempts']}")
        print(f"  - Formalization Time: {data1['metrics']['formalization_time_seconds']:.2f}s")
        print(f"  - Total Time: {data1['metrics']['total_time_seconds']:.2f}s")
    else:
        print("\n❌ Error Response:")
        print(response1.text[:500])
        return

    # Wait a moment
    print("\n⏳ Waiting 2 seconds before second request...")
    time.sleep(2)

    # Second request - cache hit
    print("\n🔄 Request 2 (Cache Hit - should use cached formalization)")
    print("-" * 80)
    start2 = time.time()
    response2 = requests.post(ENDPOINT, json=PAYLOAD, timeout=120)
    duration2 = time.time() - start2

    print(f"Status Code: {response2.status_code}")
    print(f"Duration: {duration2:.2f}s")

    if response2.status_code == 200:
        data2 = response2.json()
        print("\n✓ Success Response:")
        print(f"  - Check SAT Result: {data2.get('check_sat_result')}")
        print(f"  - Solver Success: {data2.get('solver_success')}")
        print(f"  - Formalization Similarity: {data2.get('formalization_similarity'):.4f}")
        print(f"  - Formalization Attempts: {data2['metrics']['formalization_attempts']}")
        print(f"  - Formalization Time: {data2['metrics']['formalization_time_seconds']:.2f}s")
        print(f"  - Total Time: {data2['metrics']['total_time_seconds']:.2f}s")
    else:
        print("\n❌ Error Response:")
        print(response2.text[:500])
        return

    # Analysis
    print("\n" + "=" * 80)
    print("📊 ANALYSIS")
    print("=" * 80)

    time_saved = duration1 - duration2
    formalization_time_saved = (
        data1["metrics"]["formalization_time_seconds"]
        - data2["metrics"]["formalization_time_seconds"]
    )

    print("\nTotal Request Duration:")
    print(f"  Request 1 (miss):  {duration1:.2f}s")
    print(f"  Request 2 (hit):   {duration2:.2f}s")
    print(f"  Time Saved:        {time_saved:.2f}s ({time_saved/duration1*100:.1f}% faster)")

    print("\nFormalization Step Duration:")
    print(f"  Request 1 (miss):  {data1['metrics']['formalization_time_seconds']:.2f}s")
    print(f"  Request 2 (hit):   {data2['metrics']['formalization_time_seconds']:.2f}s")
    print(f"  Time Saved:        {formalization_time_saved:.2f}s")

    print("\nCache Effectiveness:")
    if formalization_time_saved > 5:
        print("  ✅ PASS - Formalization caching working correctly!")
        print(f"     Saved {formalization_time_saved:.2f}s on formalization step")
    elif formalization_time_saved > 0:
        print("  ⚠️  PARTIAL - Some improvement but less than expected")
        print(f"     Expected ~8-9s, got {formalization_time_saved:.2f}s")
    else:
        print("  ❌ FAIL - No cache benefit observed")
        print(
            f"     Formalization times identical: {data1['metrics']['formalization_time_seconds']:.2f}s"
        )

    print("\nResults Match:")
    results_match = (
        data1.get("check_sat_result") == data2.get("check_sat_result")
        and data1.get("solver_success") == data2.get("solver_success")
        and abs(data1.get("formalization_similarity") - data2.get("formalization_similarity"))
        < 0.0001
    )
    if results_match:
        print("  ✅ Both requests returned identical results")
    else:
        print("  ❌ Results differ between requests")


if __name__ == "__main__":
    try:
        test_cache()
    except Exception as e:
        print(f"\n❌ Test failed with exception: {e}")
        import traceback

        traceback.print_exc()
