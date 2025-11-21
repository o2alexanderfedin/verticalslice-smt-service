<objective>
Diagnose and fix the Digital Ocean deployment failure by establishing a bulletproof local-to-production deployment pipeline. The application has been failing to deploy to DO App Platform with container crashes, and the root cause is unknown. This prompt will systematically identify, fix, and verify the issue.

**End Goal**: A fully working deployment to Digital Ocean that passes all health checks and can process requests.

**Why This Matters**: Multiple deployment attempts have failed. We need comprehensive debugging with enhanced logging to identify the exact failure point and ensure it never happens again.
</objective>

<context>
@Dockerfile
@app.yaml
@src/main.py
@src/shared/config.py
@src/infrastructure/llm/client.py
@.github/workflows/deploy.yml
@requirements.txt

**Known Issues**:
- Previous deployments failed with `DeployContainerExitNonZero`
- Container starts but immediately crashes in DO
- Cannot easily get runtime logs from DO to see Python traceback
- Never fully tested in local Docker environment

**Available Debug Tools**:
- `doctl` CLI with full access
- DO web console
- GitHub Actions logs
- Local Docker environment
</context>

<phase_1_local_docker_testing>
## Phase 1: Establish Local Docker Baseline

First, we need to prove the application works perfectly in Docker locally before attempting any cloud deployment.

### Step 1.1: Examine Current Docker Configuration
1. Read and analyze `Dockerfile` for potential issues:
   - Base image compatibility
   - Dependency installation order
   - Environment variable handling
   - Port exposure
   - Entry point configuration

2. Read `app.yaml` to understand DO App Platform expectations:
   - Environment variables required
   - Health check configuration
   - Resource requirements

### Step 1.2: Build and Run Locally
```bash
# Clean any previous builds
docker system prune -f

# Build with verbose output
docker build -t smt-service:local . 2>&1 | tee docker-build.log

# Check if build succeeded
docker images | grep smt-service
```

### Step 1.3: Run Container with Debugging
```bash
# Run with all environment variables and verbose logging
docker run -d \
  --name smt-local \
  -p 8000:8000 \
  -e LOG_LEVEL=DEBUG \
  -e CLAUDE_CODE_OAUTH_TOKEN="your-token-here" \
  -e ANTHROPIC_MODEL="claude-sonnet-4-5-20250929" \
  smt-service:local

# Check if container is running
docker ps -a | grep smt-local

# Get container logs immediately
docker logs smt-local

# If container exited, get exit code
docker inspect smt-local --format='{{.State.ExitCode}}'
```

### Step 1.4: Verify Health Check
```bash
# Wait for startup
sleep 10

# Test health endpoint
curl -v http://localhost:8000/health

# Test docs endpoint
curl -v http://localhost:8000/docs
```

### Step 1.5: Document Any Failures
If the container fails locally, capture:
- Exit code
- Full container logs
- Any Python tracebacks
- Environment variable issues

**CRITICAL**: Do not proceed to Phase 2 until local Docker works perfectly.
</phase_1_local_docker_testing>

<phase_2_enhanced_logging>
## Phase 2: Add Comprehensive Startup Logging

If Phase 1 passes, enhance the application with extensive startup logging to capture any DO-specific issues.

### Step 2.1: Add Startup Diagnostics to main.py

Modify `src/main.py` startup event to include:

```python
@app.on_event("startup")
async def startup_event():
    """Application startup with comprehensive diagnostics."""
    import os
    import sys

    logger.info("=" * 60)
    logger.info("STARTUP DIAGNOSTICS BEGIN")
    logger.info("=" * 60)

    # Python environment
    logger.info(f"Python version: {sys.version}")
    logger.info(f"Python executable: {sys.executable}")
    logger.info(f"Working directory: {os.getcwd()}")

    # Environment variables (redacted)
    logger.info("Environment variables:")
    for key in sorted(os.environ.keys()):
        value = os.environ[key]
        if 'KEY' in key or 'TOKEN' in key or 'SECRET' in key:
            value = f"{value[:8]}..." if len(value) > 8 else "***"
        logger.info(f"  {key}={value}")

    # Configuration validation
    logger.info(f"Settings loaded:")
    logger.info(f"  anthropic_api_key: {'SET' if settings.anthropic_api_key else 'NOT SET'}")
    logger.info(f"  anthropic_api_key length: {len(settings.anthropic_api_key) if settings.anthropic_api_key else 0}")
    logger.info(f"  anthropic_api_key prefix: {settings.anthropic_api_key[:10] if settings.anthropic_api_key else 'N/A'}...")
    logger.info(f"  anthropic_model: {settings.anthropic_model}")
    logger.info(f"  embedding_model_name: {settings.embedding_model_name}")

    # Validate critical config
    errors: list[str] = []
    if not settings.anthropic_api_key or settings.anthropic_api_key.strip() == "":
        errors.append("ANTHROPIC_API_KEY/CLAUDE_CODE_OAUTH_TOKEN is not set")
    if not settings.anthropic_model:
        errors.append("ANTHROPIC_MODEL is not set")

    if errors:
        logger.critical("CONFIGURATION ERRORS:")
        for e in errors:
            logger.critical(f"  - {e}")
        logger.info("=" * 60)
        raise RuntimeError("\\n".join(errors))

    # Test imports
    try:
        logger.info("Testing critical imports...")
        import anthropic
        logger.info(f"  anthropic version: {anthropic.__version__}")
        import sentence_transformers
        logger.info(f"  sentence_transformers: OK")
        import torch
        logger.info(f"  torch version: {torch.__version__}")
        logger.info(f"  torch CUDA available: {torch.cuda.is_available()}")
    except ImportError as e:
        logger.error(f"Import error: {e}")
        raise

    logger.info("=" * 60)
    logger.info("STARTUP DIAGNOSTICS COMPLETE - ALL OK")
    logger.info("=" * 60)
```

### Step 2.2: Add Request Logging Middleware

Add to `src/main.py`:

```python
from fastapi import Request
import time

@app.middleware("http")
async def log_requests(request: Request, call_next):
    start_time = time.time()
    logger.info(f"REQUEST: {request.method} {request.url.path}")

    response = await call_next(request)

    duration = time.time() - start_time
    logger.info(f"RESPONSE: {request.method} {request.url.path} - {response.status_code} - {duration:.3f}s")

    return response
```

### Step 2.3: Rebuild and Test Locally Again

After adding logging:
```bash
docker stop smt-local && docker rm smt-local
docker build -t smt-service:local .
docker run -d --name smt-local -p 8000:8000 \
  -e LOG_LEVEL=DEBUG \
  -e CLAUDE_CODE_OAUTH_TOKEN="your-token" \
  smt-service:local
docker logs -f smt-local
```

Verify you see the full startup diagnostics in logs.
</phase_2_enhanced_logging>

<phase_3_do_investigation>
## Phase 3: Investigate Digital Ocean Environment

### Step 3.1: Get DO App Logs

```bash
# Get app ID
APP_ID=$(doctl apps list --format ID --no-header)
echo "App ID: $APP_ID"

# Get recent deployment logs
doctl apps logs $APP_ID --type DEPLOY --tail 100

# Get runtime logs (if container started at all)
doctl apps logs $APP_ID --type RUN --tail 100

# Get build logs
doctl apps logs $APP_ID --type BUILD --tail 100
```

### Step 3.2: Check DO Console for Clues

Use Playwright or manual browser inspection to:
1. Go to DO App Platform console
2. Check the "Runtime Logs" tab
3. Check the "Build Logs" tab
4. Check app configuration for environment variables
5. Verify the container image tag matches latest release

### Step 3.3: Compare Local vs DO Environment

Create a comparison checklist:
- [ ] Environment variables match
- [ ] Port configuration (8000)
- [ ] Health check path (/health)
- [ ] Memory/CPU limits
- [ ] Docker image tag

### Step 3.4: Research Common DO App Platform Issues

Search online for:
- "Digital Ocean App Platform DeployContainerExitNonZero"
- "DO App Platform Python FastAPI container crash"
- "DO App Platform health check timeout"

Document findings and potential solutions.
</phase_3_do_investigation>

<phase_4_fix_and_deploy>
## Phase 4: Fix Issues and Deploy

Based on findings from Phase 3, implement fixes.

### Common Fixes to Try:

1. **Health Check Timeout**: Increase timeout in app.yaml
2. **Memory Issues**: Increase memory allocation
3. **Startup Time**: App takes too long to start, times out
4. **Environment Variables**: Missing or malformed
5. **Port Binding**: Container not binding to correct port

### Step 4.1: Update Configuration

Make necessary changes to:
- `app.yaml` - health check, resources, env vars
- `Dockerfile` - optimize build, ensure proper CMD
- `src/main.py` - faster startup, better error handling

### Step 4.2: Commit and Create Release

```bash
git add -A
git commit -m "fix: enhance startup logging and deployment config

- Add comprehensive startup diagnostics
- Add request logging middleware
- [List specific fixes applied]

🤖 Generated with [Claude Code](https://claude.com/claude-code)

Co-Authored-By: Claude <noreply@anthropic.com>"

git push origin main

# Create new release
VERSION="v1.8.15"
gh release create $VERSION \
  --title "$VERSION - Fix deployment issues" \
  --notes "Enhanced logging and deployment configuration fixes"
```

### Step 4.3: Monitor Deployment

```bash
# Get workflow ID
RUN_ID=$(gh run list --limit 1 --json databaseId --jq '.[0].databaseId')

# Watch until complete
gh run watch $RUN_ID --exit-status
```

### Step 4.4: Verify DO Deployment

```bash
# Get deployment URL
DEPLOY_URL=$(doctl apps list --format DefaultIngress --no-header)

# Test health
curl -v "https://$DEPLOY_URL/health"

# Test API
curl -X POST "https://$DEPLOY_URL/pipeline/process" \
  -H "Content-Type: application/json" \
  -d '{"informal_text": "x > 5"}'
```
</phase_4_fix_and_deploy>

<phase_5_verification>
## Phase 5: Comprehensive Verification

### Step 5.1: Run Full Test Suite

```bash
# Health check
curl -s https://verticalslice-smt-service-d5hf3.ondigitalocean.app/health | jq .

# Simple pipeline test
curl -s -X POST https://verticalslice-smt-service-d5hf3.ondigitalocean.app/pipeline/process \
  -H "Content-Type: application/json" \
  -d '{"informal_text": "2*2=5"}' | jq .

# Check response includes expected fields
```

### Step 5.2: Document Solution

Create `./deployment-fix-notes.md` with:
- Root cause of the issue
- Steps taken to diagnose
- Fix implemented
- Verification results
- Prevention measures for future

### Step 5.3: Clean Up

- Remove any temporary debug code (if not needed in production)
- Update TO-DOS.md to mark deployment issues as resolved
</phase_5_verification>

<success_criteria>
1. Local Docker container starts and responds to health checks
2. Enhanced logging shows full startup diagnostics
3. Root cause of DO failure identified and documented
4. Fix implemented and committed
5. New release deployed to DO successfully
6. DO health check passes: `curl https://[app-url]/health` returns 200
7. Pipeline endpoint works: POST to `/pipeline/process` returns valid response
8. All findings documented in deployment-fix-notes.md
</success_criteria>

<constraints>
- **DO NOT skip local testing** - Phase 1 must pass before proceeding
- **DO NOT remove debug logging prematurely** - keep it for future troubleshooting
- **DO commit frequently** - save progress at each phase
- **DO document everything** - future debugging depends on this
- **DO use git flow** - proper releases with version tags
</constraints>

<tools_available>
- Docker CLI for local testing
- doctl CLI for DO management
- gh CLI for GitHub releases
- curl for API testing
- Playwright (if browser automation needed for DO console)
- Web search for researching DO-specific issues
</tools_available>
