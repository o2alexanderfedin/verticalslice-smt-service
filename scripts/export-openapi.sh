#!/bin/bash
# Export OpenAPI spec from running FastAPI app
# Usage: ./scripts/export-openapi.sh [URL] [OUTPUT_FILE]
#
# FastAPI automatically generates the OpenAPI spec from code at runtime.
# This script fetches the current spec from a running instance.

set -e

# Configuration
DEFAULT_URL="http://localhost:8000/openapi.json"
DEFAULT_OUTPUT="openapi.json"

URL="${1:-$DEFAULT_URL}"
OUTPUT="${2:-$DEFAULT_OUTPUT}"

echo "Fetching OpenAPI spec from: $URL"

# Fetch spec
if curl -f -s "$URL" -o "$OUTPUT"; then
    echo "✅ OpenAPI spec exported to: $OUTPUT"

    # Pretty print info
    if command -v jq &> /dev/null; then
        VERSION=$(jq -r '.info.version' "$OUTPUT")
        TITLE=$(jq -r '.info.title' "$OUTPUT")
        echo "📋 API: $TITLE v$VERSION"
    fi
else
    echo "❌ Failed to fetch OpenAPI spec from $URL"
    echo "Make sure the app is running (python -m uvicorn src.main:app)"
    exit 1
fi
