<objective>
Set up a complete CI/CD pipeline for this Python FastAPI project that automatically builds, tests, lints, and deploys to Digital Ocean App Platform on every release.

This workflow ensures code quality through automated testing and linting before deployment, and verifies successful deployment through health checks, integration tests, and smoke tests. This is critical for maintaining production reliability and enabling confident, rapid releases.
</objective>

<context>
This is a Python-based SMT-LIB pipeline service built with FastAPI. The project needs a production-ready CI/CD workflow that:
- Runs on GitHub Actions
- Triggers on release creation (tagged releases)
- Executes comprehensive quality checks
- Deploys to Digital Ocean App Platform
- Verifies deployment success with multiple verification strategies

The user has Digital Ocean authentication already configured, so we'll use Digital Ocean's official GitHub Actions and doctl CLI.

Review the project structure to understand:
@requirements.txt - Python dependencies that need to be installed for testing
@src/ - Application source code structure
@tests/ - Test directory (if it exists)
@pyproject.toml or setup.py - Project configuration (if they exist)
@.env.example - Environment variables needed for deployment

First, determine which testing and linting tools are used by examining:
- requirements.txt or requirements-dev.txt for test dependencies
- pyproject.toml for tool configurations (ruff, black, mypy, pytest, etc.)
- Existing configuration files (.flake8, .pylintrc, mypy.ini, etc.)
</context>

<requirements>
Create a GitHub Actions workflow that performs these steps in sequence:

1. **Setup & Install**
   - Check out code
   - Set up Python 3.12 (or version from project config)
   - Install dependencies from requirements.txt
   - Install any dev/test dependencies

2. **Code Quality Checks** (these can run in parallel)
   - Run linter(s) - auto-detect which linters are configured (ruff, flake8, pylint, etc.)
   - Run type checker if configured (mypy)
   - Run code formatter check if configured (black, ruff format)
   - All quality checks must pass for deployment to proceed

3. **Testing**
   - Run test suite with pytest (or unittest if that's what's used)
   - Generate coverage report
   - Require minimum coverage threshold (configure based on current coverage or default to 70%)
   - Tests must pass for deployment to proceed

4. **Build**
   - Verify application starts successfully
   - Build Docker image if Dockerfile exists
   - Tag image with release version

5. **Deploy to Digital Ocean App Platform**
   - Use Digital Ocean's official GitHub Actions
   - Deploy using App Spec configuration (create app.yaml if doesn't exist)
   - Set environment variables from GitHub secrets
   - Wait for deployment to complete

6. **Post-Deployment Verification** (run all three in parallel)
   - **Health Check**: Hit /health endpoint, retry up to 5 times with exponential backoff
   - **Integration Tests**: Run integration test suite against deployed environment
   - **Smoke Tests**: Execute critical API endpoint tests to verify basic functionality

7. **Notification**
   - Report success/failure status
   - Include deployment URL and verification results
</requirements>

<implementation>
**Workflow Structure:**
- Create `.github/workflows/deploy.yml`
- Trigger: `on: release: types: [published]`
- Use job dependencies to ensure proper sequencing (quality checks → tests → deploy → verify)
- Use matrix strategy for parallel linting/type checking if multiple tools detected

**Tool Detection Logic:**
Examine the codebase to automatically detect which tools are configured:
- Check pyproject.toml [tool.ruff], [tool.black], [tool.mypy], [tool.pytest] sections
- Check for config files: .flake8, .pylintrc, mypy.ini, pytest.ini
- Check requirements.txt or requirements-dev.txt for tool dependencies
- Only include steps for tools that are actually configured

**Digital Ocean Integration:**
- Use `digitalocean/app_action@v1.1.6` for App Platform deployments
- Secrets needed (document in README):
  - `DIGITALOCEAN_ACCESS_TOKEN` - DO API token for authentication
  - `APP_NAME` - Name of the App Platform application
  - Any application environment variables (DATABASE_URL, API_KEYS, etc.)

**App Spec Configuration:**
If `app.yaml` doesn't exist, create a Digital Ocean App Spec that:
- Defines the Python/FastAPI service
- Sets build and run commands
- Configures health check endpoint
- Sets environment variables
- Configures auto-scaling if appropriate

**Verification Scripts:**
Create helper scripts in `.github/scripts/`:
- `health-check.sh` - Polls /health endpoint with retries
- `smoke-tests.sh` - Runs critical API tests against deployment
- `integration-tests.sh` - Executes integration test suite with DEPLOY_URL env var

**Why these constraints matter:**
- Linting and type checking BEFORE tests catches simple errors fast, saving CI minutes
- Tests BEFORE deployment prevents broken code from reaching production
- Multiple verification strategies catch different failure modes (health check = server running, integration tests = business logic works, smoke tests = critical paths work)
- Parallel verification reduces total pipeline time
- Automatic tool detection means the workflow adapts to project changes without manual updates
</implementation>

<output>
Create these files with relative paths:

1. `.github/workflows/deploy.yml` - Main CI/CD workflow file
2. `.github/scripts/health-check.sh` - Health check verification script (executable)
3. `.github/scripts/smoke-tests.sh` - Smoke test execution script (executable)
4. `.github/scripts/integration-tests.sh` - Integration test runner (executable)
5. `app.yaml` - Digital Ocean App Spec (only if it doesn't exist)
6. `DEPLOYMENT.md` - Documentation for the CI/CD setup including:
   - Required GitHub secrets to configure
   - How to trigger deployments
   - How to monitor deployment status
   - Troubleshooting common issues

Mark shell scripts as executable: `chmod +x .github/scripts/*.sh`
</output>

<verification>
Before declaring complete, verify your work:

1. **Workflow Validation:**
   - Validate workflow YAML syntax
   - Ensure all required secrets are documented
   - Verify job dependencies are correct (no circular dependencies)

2. **Tool Detection:**
   - Confirm you've correctly identified which linters/formatters/type checkers are configured
   - List the tools you detected in your response

3. **Script Testing:**
   - Verify shell scripts have proper error handling (set -e)
   - Ensure scripts accept required environment variables
   - Check that scripts have informative output for CI logs

4. **Documentation:**
   - Ensure DEPLOYMENT.md includes all required secrets
   - Document the complete deployment flow
   - Include troubleshooting section for common issues

5. **App Spec:**
   - If you created app.yaml, verify it matches the project's tech stack
   - Ensure environment variables are properly referenced
   - Confirm health check endpoint path is correct
</verification>

<success_criteria>
- GitHub Actions workflow file created with all required jobs
- Workflow automatically detects and runs appropriate linters/type checkers/formatters
- All quality checks and tests must pass before deployment
- Digital Ocean App Platform deployment configured correctly
- Three verification strategies implemented (health check, integration tests, smoke tests)
- All shell scripts are executable and have error handling
- Complete documentation in DEPLOYMENT.md with all required secrets listed
- Workflow syntax is valid and ready to use
- App Spec created (if needed) with correct configuration for FastAPI application
</success_criteria>

<research>
Before implementation, thoroughly examine the codebase to:
1. Identify ALL configured linting/formatting/type-checking tools
2. Understand the test framework and structure
3. Determine if Dockerfile exists or if we need to rely on buildpacks
4. Find the health check endpoint path (likely /health or /healthz)
5. Identify critical API endpoints for smoke tests
6. Understand environment variable requirements from .env.example or config.py
</research>
