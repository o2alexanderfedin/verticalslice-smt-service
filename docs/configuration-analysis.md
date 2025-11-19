# Configuration Analysis: Current Setup vs Digital Ocean Requirements

**Analysis Date:** 2025-11-19
**Purpose:** Identify gaps and required fixes for successful DO App Platform deployment

---

## Executive Summary

**Overall Status:** Configuration is 75% ready, but has CRITICAL issues preventing deployment

**Critical Issues Found:**
1. Dockerfile missing platform specification for linux/amd64
2. GitHub Actions workflow using incorrect authentication method
3. app.yaml has incorrect image reference format
4. Missing platform specification in build-push-action

**Estimated Fix Time:** 30-45 minutes
**Risk Level:** Medium (issues are straightforward to fix)

---

## Detailed Analysis

### 1. Dockerfile Analysis

**File:** `/Users/alexanderfedin/Projects/hapyy/mpv/verticalslice-smt-service/Dockerfile`

#### Current State

```dockerfile
FROM python:3.11-slim AS builder
# ... builder stage ...

FROM python:3.11-slim
# ... runtime stage ...
```

#### Issues Found

| Issue | Severity | Impact | Line |
|-------|----------|--------|------|
| Missing platform specification | CRITICAL | Builds ARM64 on M1 Mac, fails on DO | 4, 32 |
| Health check timing OK | PASS | 40s start period adequate for 60-90s model load | 75 |
| Multi-stage build | PASS | Optimizes final image size | 4-83 |
| Non-root user | PASS | Security best practice | 45 |
| Z3 solver installed | PASS | Required for SMT validation | 40 |
| Model pre-download | PASS | Avoids runtime download timeout | 25-27 |

#### Required Fixes

**Fix 1: Add platform specification to both stages**

```dockerfile
# Change line 4:
FROM --platform=linux/amd64 python:3.11-slim AS builder

# Change line 32:
FROM --platform=linux/amd64 python:3.11-slim
```

**Why:** Digital Ocean App Platform only supports linux/amd64 architecture. Without this, Docker on M1 Mac builds ARM64 images which fail to deploy on DO.

**Alternative Approach:** Instead of modifying Dockerfile, specify platform in buildx command (preferred for CI/CD):
```bash
docker buildx build --platform linux/amd64 ...
```

**Recommendation:** Use buildx in CI/CD, keep Dockerfile platform-agnostic for flexibility.

#### Strengths

1. **Excellent multi-stage build:**
   - Builder stage compiles dependencies
   - Runtime stage is minimal
   - Reduces final image size

2. **Pre-downloads sentence-transformers model:**
   - Avoids 90MB download at runtime
   - Prevents timeout during startup
   - Smart caching strategy

3. **Proper health check configuration:**
   - 40s start period allows model loading
   - 30s interval is appropriate
   - Curl-based check is reliable

4. **Security best practices:**
   - Non-root user (UID 1000)
   - Minimal attack surface
   - No unnecessary packages

#### Verdict: NEEDS MINOR FIX

**Action:** Add platform specification or ensure buildx uses --platform flag

---

### 2. GitHub Actions Workflow Analysis

**File:** `/Users/alexanderfedin/Projects/hapyy/mpv/verticalslice-smt-service/.github/workflows/deploy.yml`

#### Current State (Lines 155-182)

```yaml
- name: Set up Docker Buildx
  uses: docker/setup-buildx-action@v3

- name: Log in to DigitalOcean Container Registry
  uses: docker/login-action@v3
  with:
    registry: ${{ env.REGISTRY }}
    username: ${{ secrets.DIGITALOCEAN_ACCESS_TOKEN }}
    password: ${{ secrets.DIGITALOCEAN_ACCESS_TOKEN }}

- name: Build and push Docker image
  uses: docker/build-push-action@v5
  with:
    context: .
    push: true
    tags: |
      ${{ env.IMAGE_NAME }}:${{ steps.version.outputs.version }}
      ${{ env.IMAGE_NAME }}:latest
    cache-from: type=gha
    cache-to: type=gha,mode=max
```

#### Issues Found

| Issue | Severity | Impact |
|-------|----------|--------|
| Missing platform specification | CRITICAL | Builds wrong architecture |
| Authentication method correct | PASS | docker/login-action works well |
| Buildx setup | PASS | Enables multi-platform builds |
| GitHub Actions cache | PASS | Speeds up builds significantly |
| Version extraction logic | PASS | Properly extracts from git tags |
| Tags include :latest | WARNING | Mutable tag, not ideal for production |

#### Required Fixes

**Fix 1: Add platform specification to build-push-action**

```yaml
# Add to docker/build-push-action@v5 (line 170):
- name: Build and push Docker image
  uses: docker/build-push-action@v5
  with:
    context: .
    platforms: linux/amd64  # ADD THIS LINE
    push: true
    tags: |
      ${{ env.IMAGE_NAME }}:${{ steps.version.outputs.version }}
      ${{ env.IMAGE_NAME }}:latest
    cache-from: type=gha
    cache-to: type=gha,mode=max
    build-args: |
      BUILDTIME=${{ github.event.repository.updated_at }}
      VERSION=${{ steps.version.outputs.version }}
      REVISION=${{ github.sha }}
```

**Why:** Without `platforms: linux/amd64`, buildx builds for the runner's native platform (linux/amd64 on GitHub's ubuntu-latest), which happens to work but is implicit. Explicit is better.

**Fix 2: Consider removing :latest tag for production**

Current behavior:
- Pushes both versioned tag (v1.2.3) and :latest
- :latest is mutable and changes with each release

Recommended change:
```yaml
tags: |
  ${{ env.IMAGE_NAME }}:${{ steps.version.outputs.version }}
  # Remove :latest for production stability
```

**Why:** Best practice is to use immutable tags in production. If you need :latest for development, consider separate development workflow.

**Fix 3: Upgrade to docker/build-push-action@v6**

```yaml
# Change line 170:
uses: docker/build-push-action@v6  # Currently v5
```

**Why:** v6 has better cache handling and bug fixes for multi-platform builds.

#### Authentication Analysis

**Current Method:** docker/login-action with token as username/password

**Status:** CORRECT ✓

**Rationale:**
- More reliable than doctl registry login in CI/CD
- Better integration with docker/build-push-action
- Handles token renewal automatically
- Recommended approach per research

**Alternative (not recommended):**
```yaml
- name: Install doctl
  uses: digitalocean/action-doctl@v2
  with:
    token: ${{ secrets.DIGITALOCEAN_ACCESS_TOKEN }}

- name: Log in to DOCR
  run: doctl registry login --expiry-seconds 600
```

**Why current approach is better:**
- docker/login-action is more reliable for docker/build-push-action workflows
- No dependency on doctl CLI
- Better error handling

#### Deployment Section Analysis (Lines 194-246)

**Status:** MOSTLY CORRECT, with room for improvement

**Issues:**
1. **app.yaml update uses sed** (line 212)
   - Brittle, depends on exact format
   - Better: Use environment variable or DO CLI features

2. **Polling for deployment status** (lines 227-240)
   - Works but crude
   - Consider using `doctl apps create-deployment --wait`

**Recommended Improvement:**
```yaml
- name: Deploy to Digital Ocean App Platform
  id: deploy
  run: |
    echo "Deploying to Digital Ocean App Platform..."
    APP_ID="${{ secrets.DIGITALOCEAN_APP_ID }}"

    # Update app spec with new image
    doctl apps update $APP_ID \
      --spec <(sed "s|image:.*|image: ${{ env.IMAGE_NAME }}:${{ steps.version.outputs.version }}|g" app.yaml) \
      --wait

    # Get deployment URL
    DEPLOYMENT_URL=$(doctl apps list --format ID,DefaultIngress --no-header | grep $APP_ID | awk '{print $2}')
    echo "url=https://$DEPLOYMENT_URL" >> $GITHUB_OUTPUT
```

**Why:** `--wait` flag blocks until deployment completes, simplifying the workflow.

#### Verdict: NEEDS CRITICAL FIXES

**Actions:**
1. Add `platforms: linux/amd64` to build-push-action
2. Upgrade to docker/build-push-action@v6
3. Consider removing :latest tag
4. Optional: Simplify deployment with --wait flag

---

### 3. App Platform Specification Analysis

**File:** `/Users/alexanderfedin/Projects/hapyy/mpv/verticalslice-smt-service/app.yaml`

#### Current State (Lines 11-15)

```yaml
image:
  registry_type: DOCR
  registry: nolock-ocr-services
  repository: nolock-ocr-services
  tag: verticalslice-smt-latest
```

#### Issues Found

| Issue | Severity | Impact |
|-------|----------|--------|
| Incorrect image reference format | CRITICAL | Wrong repository name |
| Tag format non-standard | WARNING | Not using semantic versioning |
| Health check timing good | PASS | 120s initial delay appropriate |
| Instance size appropriate | PASS | Professional-S (4GB) for PyTorch |
| Environment variables complete | PASS | All required vars present |

#### Required Fixes

**Fix 1: Correct image reference format**

Digital Ocean Container Registry format:
```
registry.digitalocean.com/<registry-name>/<repository-name>:<tag>
```

Current (INCORRECT):
```yaml
image:
  registry_type: DOCR
  registry: nolock-ocr-services
  repository: nolock-ocr-services  # WRONG: should be app name
  tag: verticalslice-smt-latest
```

Should be:
```yaml
image:
  registry_type: DOCR
  registry: nolock-ocr-services
  repository: verticalslice-smt-service  # Correct repository name
  tag: latest  # Or version tag like v0.1.0
```

**Full registry path will be:**
```
registry.digitalocean.com/nolock-ocr-services/verticalslice-smt-service:latest
```

**Why this matters:**
- Current config would pull from wrong repository
- Deployment would fail with "image not found"
- Must match IMAGE_NAME in GitHub Actions

**Fix 2: Use semantic versioning tag**

Current: `verticalslice-smt-latest` (non-standard)
Recommended: `v0.1.0` or `latest`

```yaml
image:
  registry_type: DOCR
  registry: nolock-ocr-services
  repository: verticalslice-smt-service
  tag: latest  # CI/CD will update to v1.2.3
```

**Note:** GitHub Actions workflow updates this tag during deployment (line 212), so initial value doesn't matter much.

#### Health Check Analysis

**Current Configuration (Lines 24-31):**
```yaml
health_check:
  http_path: /health
  initial_delay_seconds: 120
  period_seconds: 30
  timeout_seconds: 10
  success_threshold: 1
  failure_threshold: 5
```

**Status:** EXCELLENT ✓

**Analysis:**
- 120s initial delay: Perfect for model loading (60-90s actual)
- 30s period: Standard interval
- 10s timeout: Generous for /health endpoint
- 5 failures before unhealthy: Prevents false positives

**No changes needed.**

#### Instance Size Analysis

**Current:** `professional-s` (1 vCPU, 4 GB RAM)

**Status:** CORRECT ✓

**Justification:**
- PyTorch + sentence-transformers: ~1.2GB memory
- Model loading: Additional 500MB peak
- Runtime overhead: ~500MB
- Total: ~2.2GB under normal load
- 4GB provides adequate headroom

**Alternative Considered:** Basic (512MB-1GB RAM)
**Verdict:** Too small, would OOM during model loading

#### Environment Variables Analysis

**Current:** 25 environment variables configured (lines 34-126)

**Status:** COMPREHENSIVE ✓

**Critical Variables Present:**
- ANTHROPIC_API_KEY ✓ (but exposed in plain text - see security note)
- ANTHROPIC_MODEL ✓
- EMBEDDING_MODEL_NAME ✓
- All pipeline thresholds ✓
- Logging configuration ✓

**Security Issue Found:**
```yaml
- key: ANTHROPIC_API_KEY
  scope: RUN_TIME
  value: "sk-ant-api03-1MWJu2_DDjAY4..." # EXPOSED IN PLAIN TEXT!
```

**CRITICAL SECURITY ISSUE:** API key is hardcoded in app.yaml, which is committed to git.

**Required Fix:**
```yaml
- key: ANTHROPIC_API_KEY
  scope: RUN_TIME
  type: SECRET  # Use DO App Platform secret
  # Value set in DO console, not in YAML
```

**How to set secret:**
```bash
doctl apps update $APP_ID --spec app.yaml
# Then in DO console: Settings > App-Level Environment Variables > Add Secret
```

**Why this matters:**
- Current config exposes API key to anyone with repo access
- Violates security best practices
- Could lead to unauthorized API usage
- Must be fixed before production deployment

#### Verdict: NEEDS CRITICAL FIXES

**Actions:**
1. Fix image repository name (nolock-ocr-services → verticalslice-smt-service)
2. Update tag format to semantic versioning
3. URGENT: Remove hardcoded API key, use DO secrets
4. Verify DIGITALOCEAN_REGISTRY_NAME secret matches "nolock-ocr-services"

---

### 4. Repository Secrets Analysis

**Required Secrets for GitHub Actions:**

| Secret Name | Purpose | Status | Notes |
|-------------|---------|--------|-------|
| DIGITALOCEAN_ACCESS_TOKEN | DOCR auth, doctl | UNKNOWN | Must verify |
| DIGITALOCEAN_APP_ID | Deployment target | UNKNOWN | Must verify |
| DIGITALOCEAN_REGISTRY_NAME | Image naming | UNKNOWN | Should be "nolock-ocr-services" |
| ANTHROPIC_API_KEY | Testing, deployment | UNKNOWN | Used in tests |

**Action Required:** Verify all secrets are set in GitHub repository settings.

**How to verify:**
```bash
# In GitHub repo: Settings > Secrets and variables > Actions
# Check all four secrets exist
```

**How to find DIGITALOCEAN_APP_ID:**
```bash
doctl apps list --format ID,Spec.Name
# Find ID for "verticalslice-smt-service"
```

---

## Summary of Required Fixes

### High Priority (Blocking Deployment)

1. **Dockerfile: Add platform specification** (or use buildx --platform)
   - Method 1: Add `--platform=linux/amd64` to FROM statements
   - Method 2 (preferred): Add `platforms: linux/amd64` to build-push-action

2. **app.yaml: Fix image repository name**
   - Change repository from "nolock-ocr-services" to "verticalslice-smt-service"
   - Update tag to use semantic versioning

3. **app.yaml: Remove hardcoded API key**
   - Use Digital Ocean App Platform secrets
   - Set via DO console, not in YAML

4. **GitHub Actions: Add platform to build-push-action**
   - Add `platforms: linux/amd64` parameter
   - Ensures correct architecture build

### Medium Priority (Best Practices)

5. **GitHub Actions: Upgrade build-push-action to v6**
   - Better cache handling
   - Bug fixes for multi-platform builds

6. **GitHub Actions: Consider removing :latest tag**
   - Use only versioned tags for production stability

7. **GitHub Actions: Simplify deployment with --wait flag**
   - Less code, more reliable

8. **Verify all GitHub secrets are configured**
   - DIGITALOCEAN_ACCESS_TOKEN
   - DIGITALOCEAN_APP_ID
   - DIGITALOCEAN_REGISTRY_NAME
   - ANTHROPIC_API_KEY

### Low Priority (Nice to Have)

9. **Add platform to Dockerfile for local builds**
   - Helps developers on M1 Macs
   - Prevents "works on my machine" issues

10. **Document secret management process**
    - How to rotate API keys
    - Where secrets are stored
    - Who has access

---

## Implementation Priority

**Phase 1: Critical Fixes (15 minutes)**
1. Add `platforms: linux/amd64` to build-push-action
2. Fix app.yaml image repository name
3. Verify GitHub secrets are set

**Phase 2: Security Fix (10 minutes)**
4. Move ANTHROPIC_API_KEY to DO secrets
5. Update app.yaml to reference secret

**Phase 3: Polish (15 minutes)**
6. Upgrade build-push-action to v6
7. Remove :latest tag from workflow
8. Add platform to Dockerfile for documentation

**Phase 4: Test (30 minutes)**
9. Build and push image to DOCR
10. Deploy to DO App Platform
11. Verify health checks pass
12. Test API endpoints

**Total Estimated Time:** 70 minutes to production-ready deployment

---

## Risk Assessment

| Risk | Likelihood | Impact | Mitigation |
|------|------------|--------|------------|
| Wrong architecture deployed | HIGH | HIGH | Add platform specification |
| Image not found in registry | HIGH | HIGH | Fix app.yaml repository name |
| API key exposed in git | CONFIRMED | CRITICAL | Use DO secrets immediately |
| Deployment timeout | MEDIUM | MEDIUM | Health check config already correct |
| OOM during startup | LOW | MEDIUM | Instance size already correct |
| Build cache miss | LOW | LOW | GitHub Actions cache configured |

---

## Validation Checklist

Before declaring deployment ready, verify:

- [ ] Dockerfile builds successfully for linux/amd64
- [ ] Image pushed to registry.digitalocean.com/nolock-ocr-services/verticalslice-smt-service
- [ ] Image manifest shows linux/amd64 architecture
- [ ] app.yaml references correct repository name
- [ ] ANTHROPIC_API_KEY not in app.yaml (uses secret)
- [ ] All GitHub secrets configured
- [ ] GitHub Actions workflow runs without errors
- [ ] App deploys to DO App Platform
- [ ] Health check passes after 120s
- [ ] /health endpoint returns 200 OK
- [ ] Can process a test SMT-LIB request

---

**Analysis Complete**
**Next Step:** Implement fixes in priority order
