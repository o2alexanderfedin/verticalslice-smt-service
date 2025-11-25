#!/bin/bash
# Performance test script

echo "Testing API performance..."
echo "Start time: $(date '+%H:%M:%S')"
START=$(date +%s.%N)

RESPONSE=$(curl -s -X POST http://localhost:8000/pipeline/process \
  -H "Content-Type: application/json" \
  -d '{"informal_text": "x must be greater than 5 and less than 10"}')

END=$(date +%s.%N)
ELAPSED=$(echo "$END - $START" | bc)

echo "End time: $(date '+%H:%M:%S')"
echo ""
echo "Wall Clock Time: ${ELAPSED}s"
echo ""
echo "Response Metrics:"
echo "$RESPONSE" | jq '{
  total_time: .metrics.total_time_seconds,
  formalization_time: .metrics.formalization_time_seconds,
  extraction_time: .metrics.extraction_time_seconds,
  validation_time: .metrics.solver_execution_time_seconds,
  formalization_attempts: .metrics.formalization_attempts,
  extraction_attempts: .metrics.extraction_attempts,
  passed_checks: .passed_all_checks,
  result: .check_sat_result
}'
