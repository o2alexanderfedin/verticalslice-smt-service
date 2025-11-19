<objective>
Create Docker deployment configuration for the SMT Pipeline service.

This includes a production-ready Dockerfile with multi-stage build, docker-compose for easy local deployment, and all necessary configuration files. The deployment must work on local Docker service and be ready for production use.

The Docker setup must optimize for size, security, and performance while maintaining all functionality.
</objective>

<context>
**Architecture Reference:** @docs/architecture/ARCHITECTURE.md

**Project Context:**
- FastAPI service running on Python 3.11+
- Dependencies: Anthropic SDK, sentence-transformers, torch, Z3
- Service listens on port 8000
- Requires environment variables for configuration
- Z3 solver must be installed in container
- sentence-transformers models need to be downloaded

**What This Produces:**
- Multi-stage Dockerfile (builder + runtime)
- docker-compose.yml for local deployment
- .dockerignore for efficient builds
- Health check configuration
- Environment variable documentation

**Why This Matters:**
Proper Docker configuration ensures the service can be deployed consistently across environments. Multi-stage builds minimize image size. Health checks ensure reliability. This makes the service production-ready.
</context>

<requirements>
**Mandatory Implementation Requirements:**

1. **Create multi-stage Dockerfile at `./Dockerfile`:**

   **Stage 1: Builder**
   - Base: `python:3.11-slim` as builder
   - Install build dependencies:
     - gcc, g++, build-essential (for compiling Python packages)
     - curl, wget (for downloading resources)
   - Install Z3 solver:
     - Download Z3 release or install via apt
     - Must be version 4.12+ for SMT-LIB v2.6 support
   - Copy requirements and install Python dependencies
   - Download sentence-transformers model:
     - Pre-download `sentence-transformers/all-MiniLM-L6-v2`
     - Store in known location for runtime stage

   **Stage 2: Runtime**
   - Base: `python:3.11-slim` (fresh, minimal)
   - Install runtime dependencies only:
     - libgomp1 (for torch)
     - z3 (from builder stage)
   - Create non-root user `app` for security
   - Copy installed packages from builder
   - Copy application code from ./src
   - Copy downloaded model from builder
   - Set working directory to `/app`
   - Expose port 8000
   - Run as non-root user
   - Health check: `curl -f http://localhost:8000/health || exit 1`
   - CMD: `["uvicorn", "src.main:app", "--host", "0.0.0.0", "--port", "8000"]`

2. **Create .dockerignore at `./.dockerignore`:**
   - Exclude:
     - `__pycache__/`, `*.pyc`, `.pytest_cache/`
     - `.git/`, `.gitignore`
     - `.env` (don't copy secrets)
     - `docs/`, `examples/` (not needed in container)
     - `prompts/`, `.memory_bank/`
     - `*.md` except essential docs
     - `tests/` (run tests before building)
     - `.vscode/`, `.idea/`, `*.swp`
   - Include:
     - `src/` (application code)
     - `requirements.txt` or `pyproject.toml`
     - `.env.example` (template only)

3. **Create docker-compose.yml at `./docker-compose.yml`:**
   ```yaml
   version: '3.8'

   services:
     smt-pipeline:
       build:
         context: .
         dockerfile: Dockerfile
       container_name: smt-pipeline-service
       ports:
         - "8000:8000"
       environment:
         - ANTHROPIC_API_KEY=${ANTHROPIC_API_KEY}
         - ANTHROPIC_MODEL=claude-sonnet-4-5-20250929
         - EMBEDDING_MODEL=sentence-transformers/all-MiniLM-L6-v2
         - FORMALIZATION_SIMILARITY_THRESHOLD=0.91
         - EXTRACTION_DEGRADATION_THRESHOLD=0.05
         - MAX_FORMALIZATION_RETRIES=3
         - MAX_EXTRACTION_RETRIES=5
         - MAX_VALIDATION_RETRIES=3
         - SMT_SOLVER_TIMEOUT=30
       env_file:
         - .env
       healthcheck:
         test: ["CMD", "curl", "-f", "http://localhost:8000/health"]
         interval: 30s
         timeout: 10s
         retries: 3
         start_period: 40s
       restart: unless-stopped
       networks:
         - smt-network

   networks:
     smt-network:
       driver: bridge
   ```

4. **Create requirements.txt at `./requirements.txt`:**
   - Core dependencies:
     - fastapi
     - uvicorn[standard]
     - pydantic>=2.0
     - pydantic-settings
     - python-dotenv
   - LLM integration:
     - anthropic
     - httpx
   - Embeddings:
     - sentence-transformers
     - torch
     - numpy
   - Utilities:
     - python-multipart (for form data if needed)
   - Pin major versions for reproducibility

5. **Update .env.example at `./.env.example`:**
   ```bash
   # Anthropic API Configuration
   ANTHROPIC_API_KEY=your_api_key_here
   ANTHROPIC_MODEL=claude-sonnet-4-5-20250929

   # Embedding Model
   EMBEDDING_MODEL=sentence-transformers/all-MiniLM-L6-v2

   # Pipeline Thresholds
   FORMALIZATION_SIMILARITY_THRESHOLD=0.91
   EXTRACTION_DEGRADATION_THRESHOLD=0.05

   # Retry Limits
   MAX_FORMALIZATION_RETRIES=3
   MAX_EXTRACTION_RETRIES=5
   MAX_VALIDATION_RETRIES=3

   # SMT Solver
   SMT_SOLVER_TIMEOUT=30
   ```

6. **Create deployment documentation at `./docs/DEPLOYMENT.md`:**
   - Prerequisites (Docker, docker-compose)
   - Build instructions
   - Run instructions
   - Environment variable configuration
   - Health check verification
   - Troubleshooting common issues
   - Resource requirements (CPU, memory)
   - Security considerations

**Optimization Requirements:**
- Multi-stage build to minimize final image size
- Layer caching optimization (copy requirements before code)
- Non-root user for security
- Health checks for reliability
- Proper signal handling for graceful shutdown
- Resource limits in docker-compose (optional but recommended)

**Security Requirements:**
- Run as non-root user
- Don't include .env in image (use env_file)
- Minimize attack surface (slim base image)
- Only install required runtime dependencies
- HTTPS for external API calls (handled by httpx)
</requirements>

<implementation>
**Step-by-Step Implementation:**

1. **Create Dockerfile:**
   - Start with builder stage for compilation
   - Install Z3 solver (check official releases)
   - Pre-download sentence-transformers model
   - Create runtime stage with minimal dependencies
   - Copy artifacts from builder
   - Set up non-root user and permissions
   - Configure health check
   - Optimize layer caching

2. **Create .dockerignore:**
   - Exclude development files
   - Exclude test files
   - Exclude documentation
   - Keep only essential runtime files

3. **Create docker-compose.yml:**
   - Define service with build context
   - Map ports (8000:8000)
   - Set environment variables
   - Configure health check
   - Add restart policy
   - Create network for future extensibility

4. **Create requirements.txt:**
   - List all dependencies from architecture
   - Pin versions for reproducibility
   - Group by category (core, LLM, embeddings, etc.)

5. **Update .env.example:**
   - Document all required variables
   - Provide sensible defaults
   - Include comments explaining each variable

6. **Write deployment docs:**
   - Clear step-by-step instructions
   - Common troubleshooting tips
   - Security best practices

**Key Docker Patterns:**

```dockerfile
# Multi-stage build pattern
FROM python:3.11-slim as builder

# Install build dependencies
RUN apt-get update && apt-get install -y \
    gcc g++ build-essential curl \
    && rm -rf /var/lib/apt/lists/*

# Install Z3
RUN apt-get update && apt-get install -y z3 \
    && rm -rf /var/lib/apt/lists/*

# Install Python dependencies
COPY requirements.txt .
RUN pip install --no-cache-dir -r requirements.txt

# Pre-download model
RUN python -c "from sentence_transformers import SentenceTransformer; SentenceTransformer('sentence-transformers/all-MiniLM-L6-v2')"

# Runtime stage
FROM python:3.11-slim

# Install runtime dependencies only
RUN apt-get update && apt-get install -y \
    libgomp1 z3 curl \
    && rm -rf /var/lib/apt/lists/*

# Create non-root user
RUN useradd -m -u 1000 app

# Copy from builder
COPY --from=builder /usr/local/lib/python3.11/site-packages /usr/local/lib/python3.11/site-packages
COPY --from=builder /root/.cache/torch /home/app/.cache/torch

# Copy application
WORKDIR /app
COPY --chown=app:app ./src ./src

# Switch to non-root
USER app

# Health check
HEALTHCHECK --interval=30s --timeout=10s --retries=3 \
    CMD curl -f http://localhost:8000/health || exit 1

EXPOSE 8000

CMD ["uvicorn", "src.main:app", "--host", "0.0.0.0", "--port", "8000"]
```

**What to Avoid and WHY:**
- ❌ NO copying .env into image - secrets should come from env_file
- ❌ NO running as root - security vulnerability
- ❌ NO large base images - increases attack surface and size
- ❌ NO skipping .dockerignore - bloats image with unnecessary files
- ❌ NO missing health checks - can't detect service failures
</implementation>

<output>
Create the following files:

**Docker configuration:**
- `./Dockerfile` - Multi-stage build for production
- `./.dockerignore` - Exclude unnecessary files
- `./docker-compose.yml` - Local deployment configuration
- `./requirements.txt` - Python dependencies (if not using pyproject.toml)

**Documentation:**
- `./docs/DEPLOYMENT.md` - Deployment guide

**Configuration:**
- Update `./.env.example` with all required variables

Optional but recommended:
- `./docker-compose.dev.yml` - Development configuration with volumes for hot reload
- `./Makefile` - Common Docker commands (build, run, stop, logs)
</output>

<verification>
Before declaring complete, verify:

1. **Build succeeds:**
   ```bash
   docker build -t smt-pipeline:latest .
   # Should complete without errors
   # Note image size (should be < 2GB ideally)
   ```

2. **Compose works:**
   ```bash
   # Create .env with real ANTHROPIC_API_KEY
   docker-compose up -d
   # Service should start
   ```

3. **Health check passes:**
   ```bash
   docker-compose ps
   # Status should show "healthy" after start period
   ```

4. **Service responds:**
   ```bash
   curl http://localhost:8000/health
   # Should return {"status": "healthy"}

   curl http://localhost:8000/docs
   # Should return FastAPI Swagger UI
   ```

5. **Non-root user:**
   ```bash
   docker-compose exec smt-pipeline whoami
   # Should return "app", not "root"
   ```

6. **Environment variables:**
   ```bash
   docker-compose exec smt-pipeline env | grep ANTHROPIC
   # Should show ANTHROPIC_API_KEY is set
   ```

7. **Clean shutdown:**
   ```bash
   docker-compose down
   # Should shut down gracefully without errors
   ```

If any verification fails, fix before completing.
</verification>

<success_criteria>
The Docker deployment is complete when:

1. ✅ Multi-stage Dockerfile builds successfully
2. ✅ Image size optimized (< 2GB if possible)
3. ✅ docker-compose.yml configured correctly
4. ✅ Service starts and responds on port 8000
5. ✅ Health check passes consistently
6. ✅ Running as non-root user (app)
7. ✅ Environment variables loaded correctly
8. ✅ .dockerignore excludes development files
9. ✅ Z3 solver available in container
10. ✅ Sentence-transformers model pre-downloaded
11. ✅ Deployment documentation complete
12. ✅ Can process sample request successfully

Report back: "Docker deployment complete. Image size: XMB. Service healthy on http://localhost:8000. Ready for production deployment."
</success_criteria>
