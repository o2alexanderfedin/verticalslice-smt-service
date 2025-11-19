# Digital Ocean App Platform Requirements and Best Practices

**Research Date:** 2025-11-19
**Service:** verticalslice-smt-service
**Target Platform:** Digital Ocean App Platform with Container Registry

---

## Table of Contents
- [Critical Architecture Requirements](#critical-architecture-requirements)
- [Container Registry Authentication](#container-registry-authentication)
- [Multi-Platform Docker Builds](#multi-platform-docker-builds)
- [Health Check Configuration](#health-check-configuration)
- [Common Deployment Errors](#common-deployment-errors)
- [Image Naming and Tagging Best Practices](#image-naming-and-tagging-best-practices)
- [Official Documentation Links](#official-documentation-links)

---

## Critical Architecture Requirements

### Platform Support: LINUX/AMD64 ONLY

**CRITICAL:** Digital Ocean App Platform **ONLY** supports Linux-based container images built for the **AMD64 (x86_64) architecture**.

**What this means:**
- ARM64 images (including those built on Apple M1/M2/M3 Macs) will **FAIL** to deploy
- Multi-arch images work, but App Platform will pull the AMD64 variant
- If you push an image with a different OS or architecture, the build fails

**Why this matters for our project:**
- Development is happening on M1 Mac (ARM64 architecture)
- By default, Docker builds produce ARM64 images on ARM Macs
- **We must explicitly build for linux/amd64 architecture**

**Source:** [DigitalOcean App Platform Dockerfile Reference](https://docs.digitalocean.com/products/app-platform/reference/dockerfile/)
**Source:** [Deploy from Container Images](https://docs.digitalocean.com/products/app-platform/how-to/deploy-from-container-images/)

### Solutions for Building AMD64 Images on ARM Macs

#### Option 1: Dockerfile Platform Specification (Simple, Single-Platform)
```dockerfile
FROM --platform=linux/amd64 python:3.11-slim AS builder
```

**Pros:** Simple, works for single-platform builds
**Cons:** Only builds AMD64, slower due to QEMU emulation on ARM Macs

#### Option 2: Docker Buildx Multi-Platform (Recommended for CI/CD)
```bash
docker buildx build --platform linux/amd64 -t myimage:tag .
```

**Pros:** Works in both local dev and CI/CD, can build multiple platforms
**Cons:** Requires Docker Buildx setup (standard in modern Docker Desktop)

#### Option 3: Build Args (Not Recommended)
Passing `--build-arg BUILDPLATFORM=linux/amd64` is less reliable than the above methods.

---

## Container Registry Authentication

### Digital Ocean Container Registry (DOCR) Format
```
registry.digitalocean.com/<your-registry-name>/<repository-name>:<tag>
```

For our project:
```
registry.digitalocean.com/nolock-ocr-services/verticalslice-smt-service:<tag>
```

### Authentication Methods for GitHub Actions

#### Method 1: Using doctl (Simpler, recommended by DO)
```yaml
- name: Install doctl
  uses: digitalocean/action-doctl@v2
  with:
    token: ${{ secrets.DIGITALOCEAN_ACCESS_TOKEN }}

- name: Log in to DOCR
  run: doctl registry login --expiry-seconds 600
```

**Best Practices:**
- Run `doctl registry login` immediately before `docker push`
- Use short expiry times (600-1200 seconds) for security
- Don't mix doctl and docker login in the same job

**Source:** [DigitalOcean doctl Action](https://github.com/digitalocean/action-doctl)

#### Method 2: Using docker/login-action (More Reliable for Complex Workflows)
```yaml
- name: Log in to DOCR
  uses: docker/login-action@v3
  with:
    registry: registry.digitalocean.com
    username: ${{ secrets.DIGITALOCEAN_ACCESS_TOKEN }}
    password: ${{ secrets.DIGITALOCEAN_ACCESS_TOKEN }}
```

**Why it works:**
- DOCR accepts the access token as both username and password
- More reliable for docker/build-push-action workflows
- Better integration with GitHub Actions caching

**Source:** [CI/CD Systems with Container Registry](https://docs.digitalocean.com/products/container-registry/how-to/set-up-ci-cd/)

### Common Authentication Issues

**Issue:** "unauthorized: (Error when pushing container to docr)"
**Solution:** Run `doctl registry login` right before push, not earlier in workflow

**Issue:** Intermittent auth failures in GitHub Actions
**Solution:** Use docker/login-action instead of doctl for more reliability

**Source:** [DigitalOcean Community - DOCR Auth Issues](https://www.digitalocean.com/community/questions/unauthorized-error-when-pushing-container-to-docr)

---

## Multi-Platform Docker Builds

### Why Multi-Platform Builds Matter
- Local development on ARM Macs produces ARM64 images
- Digital Ocean App Platform requires AMD64 images
- Multi-platform builds allow single image to work everywhere

### Basic Multi-Platform Build Setup in GitHub Actions

```yaml
- name: Set up QEMU
  uses: docker/setup-qemu-action@v3

- name: Set up Docker Buildx
  uses: docker/setup-buildx-action@v3

- name: Build and push
  uses: docker/build-push-action@v6
  with:
    context: .
    platforms: linux/amd64,linux/arm64
    push: true
    tags: registry.digitalocean.com/myregistry/myapp:latest
    cache-from: type=gha
    cache-to: type=gha,mode=max
```

**Key Components:**

1. **QEMU Setup** (`docker/setup-qemu-action@v3`)
   - Configures QEMU emulation for ARM builds on Intel runners
   - Required for multi-platform builds in GitHub Actions
   - GitHub runners are Intel/AMD64, so ARM building is emulated

2. **Docker Buildx** (`docker/setup-buildx-action@v3`)
   - Enables buildx builder for multi-platform support
   - Required for docker/build-push-action
   - Supports advanced features like caching

3. **Build and Push** (`docker/build-push-action@v6`)
   - Handles building for multiple platforms simultaneously
   - Integrates with GitHub Actions cache for faster builds
   - Creates multi-arch manifest automatically

**Source:** [Docker Multi-Platform Images in GitHub Actions](https://docs.docker.com/build/ci/github-actions/multi-platform/)

### For Digital Ocean App Platform: AMD64 Only Sufficient

Since Digital Ocean App Platform only supports AMD64, we can simplify:

```yaml
- name: Set up Docker Buildx
  uses: docker/setup-buildx-action@v3

- name: Build and push
  uses: docker/build-push-action@v6
  with:
    context: .
    platforms: linux/amd64  # Only AMD64 needed for DO
    push: true
    tags: registry.digitalocean.com/myregistry/myapp:latest
    cache-from: type=gha
    cache-to: type=gha,mode=max
```

**Note:** Building only linux/amd64 is faster than multi-platform, and sufficient for DO deployment.

### Performance Considerations

**QEMU Emulation Overhead:**
- ARM portion of build uses QEMU emulation on Intel runners
- Can be 10-30x slower than native builds
- For our Python/PyTorch app, expect 5-10 minutes for multi-platform build
- AMD64-only build: 2-4 minutes (much faster)

**Optimization Strategies:**
1. Build only linux/amd64 for production (DO requirement)
2. Use GitHub Actions cache (`cache-from/cache-to: type=gha`)
3. Multi-stage builds to minimize final image size
4. Pre-download large dependencies (sentence-transformers model) in builder stage

**Source:** [Building Multi-Platform Images for ARM64](https://www.blacksmith.sh/blog/building-multi-platform-docker-images-for-arm64-in-github-actions)

---

## Health Check Configuration

### App Platform Health Check Requirements

Health checks are **mandatory** for all publicly-accessible services in App Platform. They determine if your app is ready to receive traffic.

### Recommended Configuration for Our Service

Based on our stack (FastAPI + sentence-transformers + PyTorch):

```yaml
health_check:
  http_path: /health
  initial_delay_seconds: 120  # Model loading takes ~60-90 seconds
  period_seconds: 30          # Check every 30 seconds
  timeout_seconds: 10         # Allow 10 seconds per check
  success_threshold: 1        # One success = healthy
  failure_threshold: 5        # Five failures = unhealthy
```

### Why These Values?

**initial_delay_seconds: 120**
- Our app loads sentence-transformers model (~90MB) at startup
- Model loading takes 60-90 seconds on Professional-S instance (1 vCPU, 4GB RAM)
- 120 seconds provides buffer for slower startups
- **Too low:** App marked unhealthy before it's ready
- **Too high:** Delays traffic routing to healthy instances

**period_seconds: 30**
- Standard interval for FastAPI services
- Balances responsiveness with overhead
- Detects issues within 2-3 minutes (failure_threshold * period_seconds)

**timeout_seconds: 10**
- Our /health endpoint responds in <100ms when healthy
- 10 seconds handles temporary slowdowns (GC, CPU contention)
- Prevents false positives from transient delays

**failure_threshold: 5**
- Requires 5 consecutive failures to mark unhealthy
- 5 failures × 30 seconds = 150 seconds before marking unhealthy
- Prevents restarts from transient issues (brief memory spikes, network hiccups)

**Source:** [How to Set Up and Manage Health Checks](https://docs.digitalocean.com/products/app-platform/how-to/manage-health-checks/)

### Common Health Check Failures

**Symptom:** "My app deployment failed because of a health check"

**Common Causes:**
1. **App not listening on correct port**
   - App Platform health checks use the port defined in `http_port` (default: 8000)
   - Solution: Ensure app binds to 0.0.0.0:8000 (not 127.0.0.1)

2. **Health endpoint doesn't exist**
   - /health endpoint returns 404
   - Solution: Implement /health endpoint in FastAPI

3. **Insufficient startup time**
   - App needs more time to load model
   - Solution: Increase `initial_delay_seconds`

4. **Memory exhaustion**
   - App OOMs before becoming healthy
   - Symptom: Restart count increases, memory never approaches 100%
   - Solution: Upgrade instance size or optimize memory usage

5. **Platform architecture mismatch**
   - ARM64 image on AMD64 platform causes crashes
   - Solution: Build for linux/amd64

**Source:** [Troubleshoot Health Check Failures](https://docs.digitalocean.com/support/my-app-deployment-failed-because-of-a-health-check/)

### Health Endpoint Implementation

Our FastAPI /health endpoint should be simple and fast:

```python
@app.get("/health")
async def health_check():
    """Simple health check endpoint for App Platform."""
    return {"status": "healthy"}
```

**Best Practices:**
- Return 200 OK with simple JSON
- Don't include heavy operations (DB queries, external API calls)
- Don't check model loading here (model loaded at startup, not per-request)
- Keep response time <100ms for reliability

---

## Common Deployment Errors

### Error 1: Container Fails to Deploy Without Logs

**Symptom:** Deployment fails with vague error messages or no logs

**Root Cause:** Platform architecture mismatch (ARM64 image on AMD64 platform)

**Solution:**
```dockerfile
FROM --platform=linux/amd64 python:3.11-slim AS builder
```

Or with buildx:
```bash
docker buildx build --platform linux/amd64 -t myimage:tag .
```

**Source:** [Container Fails Without Logs](https://docs.digitalocean.com/support/my-container-based-app-fails-to-deploy-without-logs-or-error-codes./)

---

### Error 2: Out of Memory During Build

**Symptom:** "App Platform build or deployment failing with an out of memory error"

**Root Cause:** App Platform builds have 8GB memory limit

**Solutions:**

**Option 1: Optimize Dockerfile (Preferred)**
- Use multi-stage builds
- Clean up build artifacts in same RUN command
- Remove unnecessary dependencies

**Option 2: Build Locally, Push to DOCR (Recommended for our use case)**
- Build Docker image on local machine or CI/CD
- Push to Digital Ocean Container Registry
- App Platform deploys directly from image (skips build)
- **This is what we're doing!**

**Source:** [Out of Memory Build Errors](https://docs.digitalocean.com/support/why-is-my-app-platform-build-or-deployment-failing-with-an-out-of-memory-error/)

---

### Error 3: User Does Not Exist

**Symptom:** "user does not exist" error during deployment

**Root Cause:** USER instruction before required context

**Solution:** Ensure USER comes after FROM and WORKDIR:
```dockerfile
FROM python:3.11-slim
WORKDIR /app
RUN useradd -m -u 1000 app
USER app  # Must be after FROM and WORKDIR
```

---

### Error 4: Duplicate/Mutable Tag Issues

**Symptom:** Cached old image version despite new build

**Root Cause:** Using mutable tags like 'latest'

**Solution:** Use unique tags for each build:
```bash
# Bad: Mutable tag
docker tag myapp:latest registry.digitalocean.com/myregistry/myapp:latest

# Good: Immutable tag
docker tag myapp:v1.2.3 registry.digitalocean.com/myregistry/myapp:v1.2.3
```

**Source:** [Image Pull Issues with Duplicate Tags](https://docs.digitalocean.com/products/app-platform/reference/error-codes/)

---

### Error 5: Environment Variables Not Available at Build Time

**Symptom:** ARG values are empty during build

**Root Cause:** Environment variables are runtime-only in App Platform

**Solution:** Use Dockerfile ARG with default values:
```dockerfile
ARG PYTHON_VERSION=3.11
FROM python:${PYTHON_VERSION}-slim
```

And pass build args in workflow:
```yaml
build-args: |
  PYTHON_VERSION=3.11
  BUILD_DATE=${{ github.event.repository.updated_at }}
```

---

## Image Naming and Tagging Best Practices

### Avoid Mutable Tags in Production

**Never use `:latest` in production deployments.**

**Why?**
- Tags are mutable pointers that can change
- `:latest` might point to different images over time
- Introduces unpredictable side effects
- Difficult to rollback to previous version

**Exception:** `:latest` is acceptable for development/testing environments.

### Use Semantic Versioning

**Recommended Format:**
```
registry.digitalocean.com/nolock-ocr-services/verticalslice-smt-service:v1.2.3
```

**Tag Strategy:**
- `v1.2.3` - Specific release (immutable, production)
- `v1.2` - Latest patch for minor version (semi-mutable, testing)
- `v1` - Latest minor for major version (mutable, development)
- `latest` - Latest build (mutable, local dev only)

**Implementation in CI/CD:**
```yaml
- name: Extract version from release
  id: version
  run: |
    VERSION=${GITHUB_REF#refs/tags/}
    echo "version=$VERSION" >> $GITHUB_OUTPUT

- name: Build and push
  uses: docker/build-push-action@v6
  with:
    tags: |
      ${{ env.IMAGE_NAME }}:${{ steps.version.outputs.version }}
      ${{ env.IMAGE_NAME }}:latest
```

**Source:** [Container Image Versioning Best Practices](https://learn.microsoft.com/en-us/azure/container-registry/container-registry-image-tag-version)

### Lock Deployed Images

**Best Practice:** Lock deployed image tags by setting write-enabled to false

**How to lock a tag in DOCR:**
```bash
doctl registry repository tag update <registry>/<repo>:<tag> --write-enabled=false
```

**When to lock:**
- Production deployment tags (v1.2.3)
- After verifying deployment succeeded
- Before announcing release to users

**Why?**
- Prevents accidental overwrites
- Ensures production immutability
- Enables reliable rollbacks

---

## Project-Specific Considerations

### Our Stack and Its Implications

**Components:**
- Python 3.11
- FastAPI + Uvicorn
- sentence-transformers (90MB model)
- PyTorch (large dependency)
- pySMT + Z3 solver
- Anthropic API client

**Image Size Considerations:**
- Base Python 3.11 image: ~125MB
- PyTorch + sentence-transformers: ~1.2GB
- Z3 solver: ~50MB
- Application code: ~5MB
- **Total final image size: ~1.4GB**

**Build Time Estimates:**
- Local build (M1 Mac, linux/amd64): 8-12 minutes (QEMU emulation)
- GitHub Actions (Intel runner, linux/amd64): 4-6 minutes (native)
- With layer caching: 1-2 minutes (unchanged dependencies)

**Runtime Resource Requirements:**
- Minimum instance: Professional-S (1 vCPU, 4GB RAM)
- Model loading: 60-90 seconds
- Memory usage at idle: ~1.2GB
- Memory usage under load: ~2-3GB

**Why Professional-S?**
- Basic instances (512MB-1GB RAM) are insufficient for PyTorch + model
- Professional-S provides 4GB RAM with headroom for processing
- 1 vCPU adequate for I/O-bound LLM API calls

---

## Implementation Checklist for Our Project

### Dockerfile Requirements
- [x] Multi-stage build for size optimization
- [ ] Platform specification: `FROM --platform=linux/amd64 python:3.11-slim`
- [x] Pre-download sentence-transformers model in builder stage
- [x] Install Z3 solver in runtime stage
- [x] Non-root user (security)
- [x] Health check with appropriate timing
- [x] Port 8000 exposed

### GitHub Actions Workflow Requirements
- [ ] Docker Buildx setup
- [ ] DOCR authentication (docker/login-action)
- [ ] Build for linux/amd64 platform
- [ ] Tag with semantic version + latest
- [ ] GitHub Actions cache for layers
- [ ] Push to DOCR only on release or manual trigger
- [ ] Deploy to App Platform after successful build
- [ ] Post-deployment health check verification

### App Platform Configuration (app.yaml) Requirements
- [ ] Correct registry reference (nolock-ocr-services)
- [ ] Image tag updated by CI/CD
- [ ] Instance size: professional-s (4GB RAM)
- [ ] Health check: 120s initial delay, 30s interval
- [ ] Port 8000 configured
- [ ] All environment variables set
- [ ] Region: nyc

### Secrets Configuration
- [ ] DIGITALOCEAN_ACCESS_TOKEN
- [ ] DIGITALOCEAN_APP_ID
- [ ] DIGITALOCEAN_REGISTRY_NAME
- [ ] ANTHROPIC_API_KEY

---

## Official Documentation Links

### Digital Ocean
- [App Platform Dockerfile Reference](https://docs.digitalocean.com/products/app-platform/reference/dockerfile/)
- [Deploy from Container Images](https://docs.digitalocean.com/products/app-platform/how-to/deploy-from-container-images/)
- [Container Registry Documentation](https://docs.digitalocean.com/products/container-registry/)
- [App Platform Health Checks](https://docs.digitalocean.com/products/app-platform/how-to/manage-health-checks/)
- [App Platform Error Codes](https://docs.digitalocean.com/products/app-platform/reference/error-codes/)
- [Troubleshooting Apps](https://docs.digitalocean.com/support/how-to-troubleshoot-apps-in-app-platform/)
- [CI/CD with Container Registry](https://docs.digitalocean.com/products/container-registry/how-to/set-up-ci-cd/)

### Docker
- [Multi-Platform Builds](https://docs.docker.com/build/building/multi-platform/)
- [GitHub Actions Multi-Platform](https://docs.docker.com/build/ci/github-actions/multi-platform/)
- [Docker Buildx Reference](https://docs.docker.com/reference/cli/docker/buildx/build/)
- [Docker Build Push Action](https://github.com/docker/build-push-action)
- [Docker Login Action](https://github.com/docker/login-action)
- [Docker Setup Buildx Action](https://github.com/docker/setup-buildx-action)

### GitHub Actions
- [DigitalOcean doctl Action](https://github.com/digitalocean/action-doctl)
- [GitHub Actions Cache](https://docs.github.com/en/actions/using-workflows/caching-dependencies-to-speed-up-workflows)

### Community Resources
- [Building Multi-Platform Docker Images in GitHub Actions - Depot](https://depot.dev/blog/multi-platform-docker-images-in-github-actions)
- [Multi-Platform Builds for ARM64 - Blacksmith](https://www.blacksmith.sh/blog/building-multi-platform-docker-images-for-arm64-in-github-actions)

---

## Summary of Key Findings

### Critical Requirements
1. **Architecture:** Must build for linux/amd64 (Digital Ocean does not support ARM64)
2. **Authentication:** Use docker/login-action or doctl registry login in CI/CD
3. **Health Checks:** Set initial_delay_seconds to 120+ for model loading time
4. **Instance Size:** Professional-S (4GB RAM) minimum for PyTorch + sentence-transformers
5. **Tagging:** Use semantic versioning, avoid mutable :latest in production

### Recommended Approach
1. Build Docker image in GitHub Actions with buildx (linux/amd64)
2. Push to Digital Ocean Container Registry
3. Deploy to App Platform (pulls pre-built image, skips build)
4. Use health checks with adequate startup time
5. Verify deployment with automated tests

### Common Pitfalls to Avoid
1. Building ARM64 images on M1 Mac without platform specification
2. Using :latest tag in production
3. Insufficient health check initial_delay_seconds
4. Running doctl registry login too early in workflow
5. Under-provisioning instance size (model needs 4GB+ RAM)

---

**Last Updated:** 2025-11-19
**Researched By:** Claude (Sonnet 4.5)
**Purpose:** Production deployment of verticalslice-smt-service to Digital Ocean App Platform
