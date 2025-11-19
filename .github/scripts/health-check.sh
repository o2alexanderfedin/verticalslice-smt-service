#!/bin/bash
set -e

# Health Check Script
# Polls the /health endpoint with exponential backoff retry logic

DEPLOY_URL="${DEPLOY_URL:-http://localhost:8000}"
MAX_RETRIES=5
RETRY_COUNT=0
WAIT_TIME=5

echo "========================================="
echo "Running Health Check"
echo "========================================="
echo "Target URL: $DEPLOY_URL/health"
echo "Max retries: $MAX_RETRIES"
echo ""

while [ $RETRY_COUNT -lt $MAX_RETRIES ]; do
    RETRY_COUNT=$((RETRY_COUNT + 1))
    echo "Attempt $RETRY_COUNT of $MAX_RETRIES..."

    # Try to hit the health endpoint
    if HTTP_CODE=$(curl -s -o /tmp/health_response.json -w "%{http_code}" "$DEPLOY_URL/health"); then
        if [ "$HTTP_CODE" -eq 200 ]; then
            echo "Health check passed! (HTTP $HTTP_CODE)"
            echo ""
            echo "Response:"
            cat /tmp/health_response.json | python3 -m json.tool
            echo ""
            echo "========================================="
            echo "Health Check: PASSED"
            echo "========================================="
            exit 0
        else
            echo "Health check failed with HTTP code: $HTTP_CODE"
            cat /tmp/health_response.json 2>/dev/null || echo "No response body"
        fi
    else
        echo "Failed to connect to health endpoint"
    fi

    if [ $RETRY_COUNT -lt $MAX_RETRIES ]; then
        echo "Waiting ${WAIT_TIME}s before retry..."
        sleep $WAIT_TIME
        # Exponential backoff
        WAIT_TIME=$((WAIT_TIME * 2))
    fi
done

echo ""
echo "========================================="
echo "Health Check: FAILED"
echo "========================================="
echo "Service did not become healthy after $MAX_RETRIES attempts"
exit 1
