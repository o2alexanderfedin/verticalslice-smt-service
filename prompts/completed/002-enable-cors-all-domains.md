<objective>
Enable CORS (Cross-Origin Resource Sharing) for all domains in the FastAPI service.

The service currently blocks cross-domain requests, preventing web applications from other domains from calling the API.
</objective>

<context>
This is a FastAPI service deployed to Digital Ocean App Platform.
The CORS configuration is in the main application file.

@src/main.py - FastAPI application with CORS middleware
@src/shared/config.py - Configuration settings including CORS_ALLOWED_ORIGINS
@app.yaml - Digital Ocean App Platform configuration with CORS env var
</context>

<requirements>
1. Configure CORS middleware to allow requests from any origin ("*")
2. Ensure all standard CORS headers are allowed:
   - Allow all HTTP methods (GET, POST, PUT, DELETE, OPTIONS, etc.)
   - Allow credentials if needed
   - Allow all headers
3. Update configuration to use "*" for allowed origins
4. Verify the CORS_ALLOWED_ORIGINS setting in app.yaml is correctly set to allow all
</requirements>

<implementation>
Find the CORSMiddleware configuration in src/main.py and update:
- allow_origins=["*"] - Allow any domain
- allow_methods=["*"] - Allow all HTTP methods
- allow_headers=["*"] - Allow all headers
- allow_credentials=True or False based on security needs

Note: If allow_credentials=True, you cannot use "*" for origins - you'd need to reflect the origin.
For maximum compatibility, use allow_credentials=False with allow_origins=["*"].
</implementation>

<output>
Modify:
- `./src/main.py` - Update CORSMiddleware configuration
- `./src/shared/config.py` - Update default CORS config if needed
- `./app.yaml` - Verify CORS_ALLOWED_ORIGINS env var
</output>

<verification>
After changes:
1. Run the service locally and test with curl:
   ```bash
   curl -X OPTIONS http://localhost:8000/pipeline/process \
     -H "Origin: http://example.com" \
     -H "Access-Control-Request-Method: POST" \
     -v
   ```
2. Verify response includes:
   - Access-Control-Allow-Origin: * (or the requesting origin)
   - Access-Control-Allow-Methods includes POST
3. Run linters to ensure code quality
</verification>

<success_criteria>
- CORS middleware allows requests from any origin
- All HTTP methods are allowed
- OPTIONS preflight requests return proper CORS headers
- Service can be called from any web domain
</success_criteria>
