<objective>
Research Digital Ocean's Docker image requirements and best practices, build a properly configured multi-architecture Docker image, deploy it to Digital Ocean App Platform, troubleshoot and fix all deployment errors, and configure automated CI/CD deployment via GitHub Actions.

This comprehensive task will establish a complete, production-ready deployment pipeline for the verticalslice-smt-service from local development through automated deployment.
</objective>

<context>
Project: verticalslice-smt-service - A semantic-preserving SMT-LIB pipeline service built with Python FastAPI
Current situation:
- Dockerfile exists and works locally on M1 Mac
- GitHub Actions workflow (.github/workflows/deploy.yml) is partially configured
- Digital Ocean App Platform app created (app.yaml exists)
- Docker images currently fail to deploy due to architecture mismatch and other issues
- Need to understand DO-specific requirements before proceeding

Tech stack:
- Python 3.11 with FastAPI
- Dependencies: anthropic, sentence-transformers, pySMT, Z3 solver
- Digital Ocean Container Registry and App Platform
- GitHub Actions for CI/CD

@Dockerfile
@.github/workflows/deploy.yml
@app.yaml
@pyproject.toml
@requirements.txt
</context>

<research_phase>
Before building or deploying anything, thoroughly research and document Digital Ocean's requirements:

1. **Use WebSearch extensively** to find official Digital Ocean documentation on:
   - Docker image architecture requirements (ARM vs x86/AMD64)
   - Digital Ocean Container Registry authentication and push process
   - App Platform deployment specifications and requirements
   - Multi-architecture Docker builds with buildx
   - GitHub Actions integration with Digital Ocean

2. **Document findings** in `./docs/digitalocean-requirements.md` including:
   - Required Docker image architecture(s)
   - Authentication methods for DOCR
   - Best practices for App Platform deployments
   - Common pitfalls and solutions
   - Links to official documentation

3. **Analyze current configuration** against DO requirements:
   - Review Dockerfile for DO compatibility
   - Check if current GitHub Actions workflow follows DO best practices
   - Identify gaps in app.yaml configuration
</research_phase>

<implementation_requirements>
Based on research findings, implement the complete deployment solution:

1. **Fix Dockerfile for Digital Ocean**:
   - Ensure correct base image architecture
   - Optimize for DO App Platform (size, layers, startup time)
   - Include all necessary runtime dependencies
   - Verify health check compatibility

2. **Build multi-architecture Docker image**:
   - Use Docker Buildx for linux/amd64 and linux/arm64
   - Configure proper registry authentication
   - Push to Digital Ocean Container Registry with correct tags
   - Handle the sentence-transformers model download efficiently

3. **Deploy to Digital Ocean App Platform**:
   - Update app.yaml with correct image references
   - Configure environment variables properly
   - Set appropriate resource limits
   - Deploy and verify the application starts successfully

4. **Fix all deployment errors**:
   - Monitor deployment logs
   - Troubleshoot architecture mismatches
   - Fix authentication issues
   - Resolve any runtime errors
   - Verify health endpoints respond correctly

5. **Configure GitHub Actions CI/CD**:
   - Fix Docker registry authentication in workflow
   - Add multi-platform build step
   - Implement proper versioning/tagging strategy
   - Add deployment verification steps
   - Ensure workflow runs on release or manual trigger
</implementation_requirements>

<execution_strategy>
Follow this systematic approach:

**Phase 1: Research (Use WebSearch liberally)**
- Search for "Digital Ocean App Platform Docker requirements"
- Search for "Digital Ocean Container Registry authentication GitHub Actions"
- Search for "Docker buildx multi-platform Digital Ocean"
- Document ALL findings with links to sources

**Phase 2: Analysis**
- Compare research findings with current setup
- Identify specific issues in Dockerfile, app.yaml, and GitHub workflow
- Create an action plan with specific fixes needed

**Phase 3: Implementation**
- Fix Dockerfile based on DO requirements
- Update GitHub Actions workflow for proper DO integration
- Build and push correct architecture image
- Deploy to DO App Platform
- Monitor and fix any errors that arise

**Phase 4: Verification**
- Confirm image exists in DO Container Registry with correct architecture
- Verify app deploys successfully on DO App Platform
- Test health endpoints
- Trigger GitHub Actions workflow to confirm automation works

**Phase 5: Documentation**
- Document the complete process in `./docs/deployment-process.md`
- Include troubleshooting guide for common issues
- Add architecture diagrams if helpful
</execution_strategy>

<constraints_and_warnings>
**Critical requirements** (explain WHY):
- MUST use linux/amd64 architecture for Digital Ocean - DO App Platform runs on x86 servers, not ARM. M1 Mac builds produce ARM images which won't work.
- MUST authenticate to DO Container Registry properly - without proper auth, GitHub Actions cannot push images, breaking automation.
- MUST handle large dependencies (sentence-transformers model) - the 90MB model download needs to be done during build, not runtime, to avoid deployment timeouts.
- DO NOT skip error handling - deployment failures must be caught and fixed systematically, not ignored.

**Use WebSearch whenever**:
- You encounter an error you haven't seen before
- You need to verify DO-specific requirements
- You're unsure about authentication methods
- You need to check latest DO documentation
</constraints_and_warnings>

<output>
Create/update the following files:

**Documentation:**
- `./docs/digitalocean-requirements.md` - Comprehensive research findings
- `./docs/deployment-process.md` - Step-by-step deployment guide
- `./docs/troubleshooting.md` - Common issues and solutions

**Configuration updates:**
- Update `Dockerfile` if needed for DO compatibility
- Update `.github/workflows/deploy.yml` with fixes for DO deployment
- Update `app.yaml` if needed based on research

**Verification artifacts:**
- `./docs/deployment-verification.md` - Results of deployment testing and health checks
</output>

<verification>
Before declaring complete, verify EVERY step:

1. **Research verification:**
   - ✓ DO architecture requirements documented with sources
   - ✓ Authentication methods researched and documented
   - ✓ Best practices identified and recorded

2. **Build verification:**
   - ✓ Multi-architecture image built successfully
   - ✓ Image pushed to DO Container Registry
   - ✓ Image manifest shows correct architectures (linux/amd64)

3. **Deployment verification:**
   - ✓ App deploys to DO App Platform without errors
   - ✓ Health endpoint returns 200 OK
   - ✓ Application logs show no critical errors
   - ✓ Can process a test request successfully

4. **CI/CD verification:**
   - ✓ GitHub Actions workflow runs without failures
   - ✓ Automated build pushes image to registry
   - ✓ Automated deployment triggers successfully
   - ✓ All workflow steps pass quality checks

5. **Documentation verification:**
   - ✓ All findings documented with sources
   - ✓ Deployment process is reproducible from docs
   - ✓ Troubleshooting guide covers actual issues encountered
</verification>

<success_criteria>
This task is complete when:
1. Digital Ocean requirements are fully researched and documented
2. Docker image builds successfully for linux/amd64 architecture
3. Image is pushed to Digital Ocean Container Registry
4. Application deploys successfully to DO App Platform
5. Health checks pass and application is accessible
6. GitHub Actions workflow automates the entire process
7. Complete documentation exists for maintenance and troubleshooting
8. ALL errors encountered have been fixed and documented
</success_criteria>

<additional_guidance>
**For maximum efficiency:**
- Use WebSearch tool liberally - don't guess at DO requirements
- When you encounter errors, search for the specific error message
- Run multiple independent research queries in parallel
- Test each fix incrementally rather than changing everything at once
- Keep detailed notes of what you try and what works/doesn't work

**Quality expectations:**
- Go beyond basic setup - create a robust, production-ready deployment
- Include monitoring and health check best practices
- Document not just WHAT to do, but WHY (for future maintenance)
- Anticipate common failure modes and document solutions
</additional_guidance>
