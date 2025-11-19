# Deployment Guide - CI/CD Pipeline

This document describes the automated CI/CD pipeline for deploying the Semantic-Preserving SMT-LIB Pipeline Service to Digital Ocean App Platform.

## Overview

The CI/CD pipeline is implemented using GitHub Actions and automatically:
- Runs code quality checks (linting, formatting, type checking)
- Executes the test suite with coverage reporting
- Builds and verifies the application
- Builds and pushes Docker images to Digital Ocean Container Registry
- Deploys to Digital Ocean App Platform
- Verifies deployment with health checks, integration tests, and smoke tests

## Pipeline Workflow

### Trigger

The deployment pipeline is triggered by:
- **Release creation**: When a new release is published on GitHub (tagged releases)
- **Manual trigger**: Can be manually triggered via GitHub Actions UI

### Jobs

The pipeline consists of 6 sequential jobs:

1. **Quality Checks** (parallel matrix)
   - Ruff linter
   - Black formatter check
   - Mypy type checker

2. **Tests**
   - Pytest with coverage (minimum 70% required)
   - Coverage report upload to Codecov

3. **Build**
   - Application startup verification
   - Docker image build and push to DOCR
   - Tagged with release version and 'latest'

4. **Deploy**
   - Updates App Spec with new image tag
   - Deploys to Digital Ocean App Platform
   - Waits for deployment to complete

5. **Verify** (parallel matrix)
   - Health check (5 retries with exponential backoff)
   - Integration tests (5 test scenarios)
   - Smoke tests (7 critical endpoint tests)

6. **Notify**
   - Reports deployment success/failure
   - Includes deployment URL and version

## Required GitHub Secrets

Configure these secrets in your GitHub repository settings (Settings → Secrets and variables → Actions):

### Required Secrets

| Secret Name | Description | Example |
|------------|-------------|---------|
| `DIGITALOCEAN_ACCESS_TOKEN` | Digital Ocean API token with read/write access | `dop_v1_xxxxxxxxxxxxx` |
| `DIGITALOCEAN_REGISTRY_NAME` | Name of your Digital Ocean Container Registry | `my-registry` |
| `DIGITALOCEAN_APP_ID` | App Platform application ID | `12345678-1234-1234-1234-123456789012` |
| `ANTHROPIC_API_KEY` | Anthropic API key for Claude AI | `sk-ant-xxxxxxxxxxxxx` |

### How to Get These Values

#### DIGITALOCEAN_ACCESS_TOKEN
1. Go to [Digital Ocean API Settings](https://cloud.digitalocean.com/account/api/tokens)
2. Click "Generate New Token"
3. Name it "GitHub Actions CI/CD"
4. Select "Read" and "Write" scopes
5. Copy the token immediately (it won't be shown again)

#### DIGITALOCEAN_REGISTRY_NAME
1. Go to [Container Registry](https://cloud.digitalocean.com/registry)
2. Create a new registry if you don't have one
3. Use the registry name (e.g., `my-registry` from `registry.digitalocean.com/my-registry`)

#### DIGITALOCEAN_APP_ID
1. Go to [App Platform](https://cloud.digitalocean.com/apps)
2. Create a new app or select existing app
3. The App ID is in the URL: `https://cloud.digitalocean.com/apps/<APP_ID>`
4. Or use `doctl apps list` to get the ID

#### ANTHROPIC_API_KEY
1. Go to [Anthropic Console](https://console.anthropic.com/)
2. Navigate to API Keys
3. Create a new API key
4. Copy the key starting with `sk-ant-`

## Initial Setup

### 1. Create Digital Ocean Container Registry

```bash
# Install doctl CLI
brew install doctl  # macOS
# or download from https://docs.digitalocean.com/reference/doctl/how-to/install/

# Authenticate
doctl auth init

# Create container registry
doctl registry create <registry-name> --subscription-tier basic
```

### 2. Create Digital Ocean App Platform App

You have two options:

**Option A: Using doctl CLI**
```bash
# Create app from spec file
doctl apps create --spec app.yaml

# Get the app ID
doctl apps list
```

**Option B: Using Digital Ocean Console**
1. Go to [App Platform](https://cloud.digitalocean.com/apps)
2. Click "Create App"
3. Select "DigitalOcean Container Registry"
4. Choose your registry and repository
5. Configure settings (or upload app.yaml)
6. Note the App ID from the URL

### 3. Configure GitHub Secrets

1. Go to your GitHub repository
2. Navigate to Settings → Secrets and variables → Actions
3. Click "New repository secret"
4. Add each of the required secrets listed above

### 4. Configure Environment Variables in Digital Ocean

Some environment variables need to be set in Digital Ocean App Platform dashboard:

1. Go to your app in [App Platform](https://cloud.digitalocean.com/apps)
2. Navigate to Settings → App-Level Environment Variables
3. Add `ANTHROPIC_API_KEY` as a secret (if not already in app.yaml)
4. Save changes

## How to Deploy

### Automatic Deployment (Recommended)

1. **Create a new release on GitHub:**
   ```bash
   # Tag your code
   git tag -a v0.1.0 -m "Release version 0.1.0"
   git push origin v0.1.0

   # Or create release via GitHub UI
   # Go to Releases → Draft a new release
   # Create a new tag (e.g., v0.1.0)
   # Click "Publish release"
   ```

2. **Monitor the deployment:**
   - Go to Actions tab in GitHub
   - Watch the "Deploy to Digital Ocean" workflow
   - Deployment typically takes 5-10 minutes

### Manual Deployment

1. Go to GitHub Actions tab
2. Select "Deploy to Digital Ocean" workflow
3. Click "Run workflow"
4. Select the branch to deploy
5. Click "Run workflow"

## Monitoring Deployment Status

### GitHub Actions

- **In Progress**: Yellow circle icon
- **Success**: Green checkmark
- **Failed**: Red X

Click on a workflow run to see detailed logs for each job.

### Digital Ocean App Platform

1. Go to [App Platform](https://cloud.digitalocean.com/apps)
2. Select your app
3. View deployment history and status
4. Check logs in the "Runtime Logs" tab

### Health Check Endpoint

After deployment, verify the service is running:
```bash
curl https://your-app-url.ondigitalocean.app/health
```

Expected response:
```json
{
  "status": "healthy",
  "service": "Semantic-Preserving SMT-LIB Pipeline",
  "version": "0.1.0",
  "model": "claude-sonnet-4-5-20250929",
  "embedding_model": "sentence-transformers/all-MiniLM-L6-v2"
}
```

## Verification Tests

The pipeline runs three types of verification tests:

### 1. Health Check
- Polls `/health` endpoint
- 5 retries with exponential backoff
- Ensures service is responsive

### 2. Smoke Tests
- Tests critical API endpoints
- 7 test scenarios including:
  - Root redirect
  - Health check
  - OpenAPI schema
  - Pipeline examples
  - Simple processing
  - Error handling
  - Response structure validation

### 3. Integration Tests
- End-to-end API testing
- 5 test scenarios:
  - Full pipeline with valid input
  - Unsatisfiable constraint handling
  - Multiple variables processing
  - Examples endpoint functionality
  - Error handling validation

## Troubleshooting

### Common Issues

#### 1. Quality Checks Fail

**Problem**: Ruff, Black, or Mypy checks fail

**Solution**:
```bash
# Run checks locally before committing
ruff check src/ tests/
black --check src/ tests/
mypy src/

# Auto-fix formatting issues
black src/ tests/

# Fix linting issues
ruff check --fix src/ tests/
```

#### 2. Tests Fail

**Problem**: Pytest fails or coverage is below threshold

**Solution**:
```bash
# Run tests locally
pytest tests/ -v --cov=src --cov-report=term-missing

# Check which lines are not covered
pytest tests/ --cov=src --cov-report=html
open htmlcov/index.html
```

#### 3. Docker Build Fails

**Problem**: Docker image build fails

**Solution**:
- Check Dockerfile syntax
- Verify requirements.txt is complete
- Test build locally:
  ```bash
  docker build -t test-build .
  docker run -p 8000:8000 -e ANTHROPIC_API_KEY=xxx test-build
  ```

#### 4. Deployment Fails

**Problem**: Digital Ocean deployment fails or times out

**Solution**:
- Check Digital Ocean app logs
- Verify app.yaml is valid
- Ensure all required environment variables are set
- Check instance size is sufficient (professional-xs minimum)

#### 5. Health Check Fails

**Problem**: Health check doesn't pass after deployment

**Solution**:
- Check application logs in Digital Ocean
- Verify `/health` endpoint works:
  ```bash
  curl https://your-app-url.ondigitalocean.app/health
  ```
- Ensure ANTHROPIC_API_KEY is set correctly
- Check for errors in startup logs

#### 6. Integration Tests Fail

**Problem**: Integration tests fail but deployment succeeded

**Solution**:
- Check which specific test failed in GitHub Actions logs
- Test the endpoint manually:
  ```bash
  curl -X POST https://your-app-url.ondigitalocean.app/pipeline/process \
    -H "Content-Type: application/json" \
    -d '{"informal_text": "x must be greater than 5"}'
  ```
- Verify Anthropic API key is valid and has credits
- Check application logs for errors

### Getting Help

1. **Check GitHub Actions logs**: Detailed logs for each step
2. **Check Digital Ocean logs**: Runtime logs in App Platform dashboard
3. **Review recent changes**: Compare with last successful deployment
4. **Test locally**: Replicate the issue in local environment

## Pipeline Configuration

### Modify Pipeline Behavior

Edit `.github/workflows/deploy.yml` to customize:

- **Python version**: Change `PYTHON_VERSION` environment variable
- **Coverage threshold**: Modify `--cov-fail-under=70` in test job
- **Retry attempts**: Update retry logic in health-check.sh
- **Test timeout**: Adjust timeout values in integration-tests.sh
- **Instance size**: Update `instance_size_slug` in app.yaml

### Add New Tests

**Smoke Tests**: Edit `.github/scripts/smoke-tests.sh`
**Integration Tests**: Edit `.github/scripts/integration-tests.sh`

## Security Best Practices

1. **Never commit secrets**: Use GitHub Secrets for all sensitive data
2. **Rotate tokens regularly**: Update Digital Ocean and Anthropic tokens
3. **Use scoped tokens**: Grant minimum required permissions
4. **Monitor access logs**: Review Digital Ocean access logs regularly
5. **Enable 2FA**: On both GitHub and Digital Ocean accounts

## Rollback Procedure

If a deployment fails or introduces issues:

### Option 1: Rollback in Digital Ocean Console
1. Go to App Platform → Your App
2. Navigate to "Deployments" tab
3. Find the last known good deployment
4. Click "Rollback to this deployment"

### Option 2: Deploy Previous Version
1. Create a new release with the previous version tag
2. Or manually trigger workflow with previous branch/tag

### Option 3: Manual Rollback with doctl
```bash
# List deployments
doctl apps list-deployments <app-id>

# Get previous deployment ID
doctl apps get-deployment <app-id> <deployment-id>

# Note: Full rollback requires redeployment
```

## Performance Considerations

### Pipeline Optimization

- **Parallel execution**: Quality checks and verifications run in parallel
- **Docker layer caching**: Uses GitHub Actions cache for faster builds
- **Pip caching**: Python dependencies cached between runs
- **Conditional jobs**: Skips unnecessary steps when possible

### Expected Timings

- Quality Checks: 1-2 minutes (parallel)
- Tests: 2-3 minutes
- Build: 3-5 minutes (including Docker build)
- Deploy: 2-4 minutes
- Verify: 2-3 minutes (parallel)
- **Total**: ~10-15 minutes

## Cost Estimates

### Digital Ocean Costs
- **Container Registry**: $5/month (Basic tier)
- **App Platform**: ~$12/month (Professional-XS instance)
- **Total**: ~$17/month

### CI/CD Costs
- **GitHub Actions**: Free for public repos, 2000 minutes/month for private
- **This pipeline**: ~15 minutes per deployment

## Next Steps

1. Set up status badges in README.md
2. Configure Slack/email notifications for deployment status
3. Set up monitoring and alerting (DataDog, Sentry, etc.)
4. Implement staging environment for pre-production testing
5. Add database backups to deployment process (if applicable)
6. Configure custom domain and SSL certificate

## Resources

- [Digital Ocean App Platform Docs](https://docs.digitalocean.com/products/app-platform/)
- [GitHub Actions Documentation](https://docs.github.com/en/actions)
- [doctl CLI Reference](https://docs.digitalocean.com/reference/doctl/)
- [Anthropic API Documentation](https://docs.anthropic.com/)

## Support

For issues with the pipeline:
1. Check this documentation first
2. Review GitHub Actions logs
3. Check Digital Ocean status page
4. Contact DevOps team or create an issue
