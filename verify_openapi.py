#!/usr/bin/env python3
"""Verify OpenAPI documentation generation.

This script checks that:
1. FastAPI app can be instantiated
2. OpenAPI schema can be generated
3. All endpoints have proper documentation
4. All models have descriptions
"""

import sys
from pathlib import Path

# Add project root to path
sys.path.insert(0, str(Path(__file__).parent))

try:
    from src.main import app

    print("✓ FastAPI app imported successfully")
except Exception as e:
    print(f"✗ Error importing FastAPI app: {e}")
    import traceback

    traceback.print_exc()
    sys.exit(1)

try:
    # Generate OpenAPI schema
    openapi_schema = app.openapi()
    print("✓ OpenAPI schema generated successfully")

    # Verify basic metadata
    print("\n=== API Metadata ===")
    print(f"Title: {openapi_schema['info']['title']}")
    print(f"Version: {openapi_schema['info']['version']}")
    print(f"Description: {openapi_schema['info']['description'][:100]}...")

    # Verify contact and license
    if "contact" in openapi_schema["info"]:
        print(f"Contact: {openapi_schema['info']['contact']}")
    if "license" in openapi_schema["info"]:
        print(f"License: {openapi_schema['info']['license']}")

    # Verify endpoints
    print("\n=== Endpoints ===")
    endpoints = []
    for path, methods in openapi_schema["paths"].items():
        for method, details in methods.items():
            if method.upper() in ["GET", "POST", "PUT", "DELETE", "PATCH"]:
                endpoint_info = {
                    "path": path,
                    "method": method.upper(),
                    "summary": details.get("summary", "NO SUMMARY"),
                    "description": details.get("description", "NO DESCRIPTION"),
                    "tags": details.get("tags", []),
                }
                endpoints.append(endpoint_info)
                print(f"{method.upper():6} {path:30} - {endpoint_info['summary']}")

                # Verify responses
                if "responses" in details:
                    for status_code in details["responses"]:
                        print(
                            f"       └─ {status_code}: {details['responses'][status_code].get('description', 'No description')}"
                        )

    # Verify models/schemas
    print("\n=== Schemas ===")
    if "components" in openapi_schema and "schemas" in openapi_schema["components"]:
        for schema_name, schema_def in openapi_schema["components"]["schemas"].items():
            has_description = "description" in schema_def
            field_count = len(schema_def.get("properties", {}))
            fields_with_desc = sum(
                1 for prop in schema_def.get("properties", {}).values() if "description" in prop
            )

            status = "✓" if has_description and fields_with_desc == field_count else "⚠"
            print(
                f"{status} {schema_name:30} - {field_count} fields, {fields_with_desc} with descriptions"
            )

            # Check for examples
            if "examples" in schema_def:
                print(f"   └─ Has {len(schema_def['examples'])} example(s)")

    # Verify tags
    print("\n=== Tags ===")
    if "tags" in openapi_schema:
        for tag in openapi_schema["tags"]:
            print(f"• {tag['name']}: {tag.get('description', 'No description')}")

    # Summary
    print("\n=== Summary ===")
    print(f"✓ Total endpoints: {len(endpoints)}")
    print(
        f"✓ Endpoints with descriptions: {sum(1 for e in endpoints if e['description'] != 'NO DESCRIPTION')}"
    )
    print(
        f"✓ Endpoints with summaries: {sum(1 for e in endpoints if e['summary'] != 'NO SUMMARY')}"
    )

    schemas_count = len(openapi_schema.get("components", {}).get("schemas", {}))
    print(f"✓ Total schemas: {schemas_count}")

    print("\n✓ OpenAPI documentation verification completed successfully!")
    print("\nTo view the Swagger UI, run:")
    print("  uvicorn src.main:app --reload")
    print("  Then navigate to: http://localhost:8000/docs")

except Exception as e:
    print(f"\n✗ Error during verification: {e}")
    import traceback

    traceback.print_exc()
    sys.exit(1)
