# SMT Pipeline Service - Deployment Guide

## Table of Contents
- [Prerequisites](#prerequisites)
- [Quick Start](#quick-start)
- [Environment Configuration](#environment-configuration)
- [Building the Docker Image](#building-the-docker-image)
- [Running with Docker Compose](#running-with-docker-compose)
- [Verification](#verification)
- [Troubleshooting](#troubleshooting)
- [Production Deployment](#production-deployment)
- [Resource Requirements](#resource-requirements)
- [Security Considerations](#security-considerations)

---

## Prerequisites

### Required Software
- **Docker**: Version 20.10 or later
- **Docker Compose**: Version 2.0 or later (included with Docker Desktop)
- **Git**: For cloning the repository

### System Requirements
- **CPU**: 2+ cores recommended
- **RAM**: 4GB minimum, 8GB recommended
- **Disk**: 5GB free space (for Docker images and models)
- **Network**: Internet access for building images and downloading models

### API Keys
- **Anthropic API Key**: Required for LLM operations
  - Sign up at: https://console.anthropic.com/
  - Get your API key from the dashboard

### Verify Prerequisites
```bash
# Check Docker version
docker --version
# Output: Docker version 20.10.x or later

# Check Docker Compose version
docker compose version
# Output: Docker Compose version 2.x.x or later

# Verify Docker is running
docker ps
# Should list running containers (or empty list if none)
```

---

## Quick Start

### 1. Clone the Repository
```bash
git clone <repository-url>
cd verticalslice-smt-service
```

### 2. Configure Environment
```bash
# Copy example environment file
cp .env.example .env

# Edit .env and add your Anthropic API key
# REQUIRED: Update ANTHROPIC_API_KEY with your actual key
nano .env  # or use your preferred editor
```

### 3. Build and Run
```bash
# Build and start the service
docker compose up -d

# View logs to verify startup
docker compose logs -f smt-pipeline
```

### 4. Verify Health
```bash
# Wait 40 seconds for model loading, then check health
sleep 40
curl http://localhost:8000/health
# Expected output: {"status": "healthy"}

# Access API documentation
curl http://localhost:8000/docs
# Or open in browser: http://localhost:8000/docs
```

**You're ready to use the service!**

---

## Environment Configuration

### Required Variables

| Variable | Description | Default | Notes |
|----------|-------------|---------|-------|
| `ANTHROPIC_API_KEY` | Anthropic API key | **REQUIRED** | Get from https://console.anthropic.com/ |

### Core Configuration

| Variable | Description | Default | Notes |
|----------|-------------|---------|-------|
| `ANTHROPIC_MODEL` | Claude model to use | `claude-sonnet-4-5-20250929` | Latest Sonnet 4.5 recommended |
| `EMBEDDING_MODEL` | Sentence-transformers model | `sentence-transformers/all-MiniLM-L6-v2` | Local model, no API key needed |

### Quality Thresholds

| Variable | Description | Default | Range | Impact |
|----------|-------------|---------|-------|--------|
| `FORMALIZATION_SIMILARITY_THRESHOLD` | Step 1 similarity requirement | `0.91` | 0.85-0.95 | Higher = stricter semantic preservation |
| `EXTRACTION_DEGRADATION_THRESHOLD` | Step 2 max information loss | `0.05` | 0.03-0.10 | Lower = stricter information preservation |

### Retry Configuration

| Variable | Description | Default | Range | Impact |
|----------|-------------|---------|-------|--------|
| `MAX_FORMALIZATION_RETRIES` | Step 1 retry limit | `3` | 1-10 | More retries = higher quality, longer latency |
| `MAX_EXTRACTION_RETRIES` | Step 2 retry limit | `5` | 1-10 | More retries = higher quality, longer latency |
| `MAX_VALIDATION_RETRIES` | Step 3 retry limit | `3` | 1-10 | More retries = better error correction |

### Performance Tuning

| Variable | Description | Default | Range | Impact |
|----------|-------------|---------|-------|--------|
| `SMT_SOLVER_TIMEOUT` | Solver timeout (seconds) | `30` | 10-120 | Higher = can solve complex problems, may hang longer |
| `LOG_LEVEL` | Logging verbosity | `INFO` | DEBUG, INFO, WARNING, ERROR | DEBUG for troubleshooting |

### Example .env File
```bash
# Required
ANTHROPIC_API_KEY=sk-ant-api03-xxx...

# Optional (defaults shown)
ANTHROPIC_MODEL=claude-sonnet-4-5-20250929
EMBEDDING_MODEL=sentence-transformers/all-MiniLM-L6-v2
FORMALIZATION_SIMILARITY_THRESHOLD=0.91
EXTRACTION_DEGRADATION_THRESHOLD=0.05
MAX_FORMALIZATION_RETRIES=3
MAX_EXTRACTION_RETRIES=5
MAX_VALIDATION_RETRIES=3
SMT_SOLVER_TIMEOUT=30
LOG_LEVEL=INFO
```

---

## Building the Docker Image

### Standard Build
```bash
# Build the image
docker build -t smt-pipeline:latest .

# Build with build arguments (if needed)
docker build --build-arg PYTHON_VERSION=3.11 -t smt-pipeline:latest .
```

### Build Process
The Dockerfile uses a multi-stage build for optimization:

1. **Stage 1 (Builder)**:
   - Installs build dependencies (gcc, g++, build-essential)
   - Installs Z3 SMT solver
   - Installs Python packages
   - Pre-downloads sentence-transformers model (~90MB)
   - Total build time: 5-10 minutes (first build)

2. **Stage 2 (Runtime)**:
   - Minimal Python 3.11 slim image
   - Copies only runtime dependencies
   - Runs as non-root user (`app`)
   - Final image size: ~1.5-2GB

### Build Optimization Tips
```bash
# Use BuildKit for faster builds
DOCKER_BUILDKIT=1 docker build -t smt-pipeline:latest .

# Cache Python packages for faster rebuilds
# (BuildKit automatically caches layers)

# Build without cache (if needed)
docker build --no-cache -t smt-pipeline:latest .
```

### Verify Build
```bash
# Check image size
docker images smt-pipeline:latest

# Inspect image layers
docker history smt-pipeline:latest

# Test image runs
docker run --rm smt-pipeline:latest python -c "import torch; import sentence_transformers; print('OK')"
```

---

## Running with Docker Compose

### Start Service
```bash
# Start in background (detached mode)
docker compose up -d

# Start in foreground (see logs)
docker compose up

# Start and rebuild if code changed
docker compose up -d --build
```

### View Logs
```bash
# View all logs
docker compose logs

# Follow logs (real-time)
docker compose logs -f

# View last 100 lines
docker compose logs --tail=100

# View logs for specific service
docker compose logs smt-pipeline
```

### Stop Service
```bash
# Stop containers (preserves containers)
docker compose stop

# Stop and remove containers
docker compose down

# Stop and remove everything (containers, networks, volumes)
docker compose down -v
```

### Restart Service
```bash
# Restart service
docker compose restart

# Restart with rebuild
docker compose down && docker compose up -d --build
```

### Scale Service (Optional)
```bash
# Run multiple instances behind a load balancer
docker compose up -d --scale smt-pipeline=3
```

---

## Verification

### 1. Container Health
```bash
# Check container status
docker compose ps

# Expected output:
# NAME                   STATUS              PORTS
# smt-pipeline-service   Up (healthy)        0.0.0.0:8000->8000/tcp
```

### 2. Health Endpoint
```bash
# Check health endpoint
curl http://localhost:8000/health

# Expected output:
# {"status":"healthy"}

# Or with detailed output
curl -v http://localhost:8000/health
```

### 3. API Documentation
```bash
# Access Swagger UI
open http://localhost:8000/docs

# Or get OpenAPI spec
curl http://localhost:8000/openapi.json
```

### 4. Test Processing Endpoint
```bash
# Simple test request
curl -X POST http://localhost:8000/pipeline/process \
  -H "Content-Type: application/json" \
  -d '{
    "informal_text": "There exists a number x that is greater than 5 and less than 10"
  }'

# Expected: JSON response with formalized text, SMT-LIB code, and solver result
```

### 5. Verify Non-Root User
```bash
# Check the user running the process
docker compose exec smt-pipeline whoami

# Expected output: app (not root)

# Verify process user
docker compose exec smt-pipeline ps aux | grep uvicorn
# Should show user "app"
```

### 6. Verify Environment Variables
```bash
# Check environment variables are loaded
docker compose exec smt-pipeline env | grep ANTHROPIC

# Should show:
# ANTHROPIC_API_KEY=sk-ant-...
# ANTHROPIC_MODEL=claude-sonnet-4-5-20250929
```

---

## Troubleshooting

### Container Fails to Start

**Symptom**: Container exits immediately after starting

**Diagnosis**:
```bash
# Check logs for errors
docker compose logs smt-pipeline

# Check exit code
docker compose ps -a
```

**Common Causes**:
1. **Missing .env file**: Ensure `.env` exists with `ANTHROPIC_API_KEY`
2. **Invalid API key**: Verify your Anthropic API key is correct
3. **Port conflict**: Port 8000 already in use
   ```bash
   # Find process using port 8000
   lsof -i :8000
   # Kill or change port in docker-compose.yml
   ```

### Health Check Failing

**Symptom**: Container status shows "unhealthy"

**Diagnosis**:
```bash
# Check health check logs
docker inspect smt-pipeline-service | jq '.[0].State.Health'

# Check application logs
docker compose logs smt-pipeline | grep -i error
```

**Common Causes**:
1. **Model loading timeout**: Increase `start_period` in docker-compose.yml
2. **Application crashed**: Check logs for Python errors
3. **Health endpoint not responding**: Verify FastAPI app is running

### Model Download Fails

**Symptom**: Errors like "Unable to load model" or "Model not found"

**Diagnosis**:
```bash
# Check build logs
docker build -t smt-pipeline:latest . 2>&1 | grep -i sentence-transformers
```

**Solution**:
1. Ensure internet connection during build
2. Try building with `--no-cache` to force re-download
3. Manually download model during build:
   ```bash
   # Inside Dockerfile builder stage
   RUN python -c "from sentence_transformers import SentenceTransformer; SentenceTransformer('sentence-transformers/all-MiniLM-L6-v2')"
   ```

### API Requests Timeout

**Symptom**: Requests hang or timeout

**Diagnosis**:
```bash
# Check if service is processing
docker compose logs -f smt-pipeline

# Check resource usage
docker stats smt-pipeline-service
```

**Common Causes**:
1. **Anthropic API slow**: Check Anthropic API status
2. **Resource limits**: Increase memory/CPU in docker-compose.yml
3. **Complex SMT problem**: Increase `SMT_SOLVER_TIMEOUT`

### Permission Denied Errors

**Symptom**: "Permission denied" errors in logs

**Diagnosis**:
```bash
# Check file permissions in container
docker compose exec smt-pipeline ls -la /app

# Check user
docker compose exec smt-pipeline id
```

**Solution**:
Ensure files are owned by `app` user in Dockerfile:
```dockerfile
COPY --chown=app:app ./src ./src
```

### Out of Memory (OOM)

**Symptom**: Container killed or exits with status 137

**Diagnosis**:
```bash
# Check Docker daemon logs
docker logs smt-pipeline-service

# Check system resources
docker stats smt-pipeline-service
```

**Solution**:
1. Increase memory limit in docker-compose.yml:
   ```yaml
   deploy:
     resources:
       limits:
         memory: 8G  # Increase from 4G
   ```
2. Use smaller embedding model
3. Reduce concurrent requests

### Z3 Solver Errors

**Symptom**: "z3 not found" or solver execution errors

**Diagnosis**:
```bash
# Verify Z3 is installed
docker compose exec smt-pipeline which z3

# Test Z3 execution
docker compose exec smt-pipeline z3 --version
```

**Solution**:
Ensure Z3 is installed in both builder and runtime stages of Dockerfile.

---

## Production Deployment

### Security Hardening

1. **Environment Variables**:
   ```bash
   # Use secrets management (e.g., Docker secrets, Kubernetes secrets)
   # Never commit .env to version control
   # Rotate API keys regularly
   ```

2. **Network Security**:
   ```yaml
   # In docker-compose.yml, expose only necessary ports
   ports:
     - "127.0.0.1:8000:8000"  # Bind to localhost only

   # Use reverse proxy (nginx, traefik) with HTTPS
   ```

3. **Resource Limits**:
   ```yaml
   # Enforce resource limits to prevent DoS
   deploy:
     resources:
       limits:
         cpus: '4.0'
         memory: 8G
   ```

4. **Read-Only Filesystem** (Optional):
   ```yaml
   # Make container filesystem read-only
   read_only: true
   tmpfs:
     - /tmp
   ```

### High Availability Setup

```yaml
# docker-compose.prod.yml
version: '3.8'

services:
  smt-pipeline:
    # ... existing config ...
    deploy:
      replicas: 3
      update_config:
        parallelism: 1
        delay: 10s
      restart_policy:
        condition: on-failure
        max_attempts: 3
```

### Monitoring & Logging

```yaml
# Add logging driver
services:
  smt-pipeline:
    logging:
      driver: "json-file"
      options:
        max-size: "10m"
        max-file: "3"
```

### CI/CD Integration

```yaml
# Example GitHub Actions workflow
name: Build and Deploy

on:
  push:
    branches: [main]

jobs:
  build:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v3
      - name: Build Docker image
        run: docker build -t smt-pipeline:${{ github.sha }} .
      - name: Push to registry
        run: docker push smt-pipeline:${{ github.sha }}
```

---

## Resource Requirements

### Minimum Requirements
- **CPU**: 1 core
- **RAM**: 2GB
- **Disk**: 3GB
- **Use case**: Testing, development, light workloads

### Recommended Requirements
- **CPU**: 2-4 cores
- **RAM**: 4-8GB
- **Disk**: 5GB
- **Use case**: Production, moderate workloads (1-10 req/min)

### High-Performance Requirements
- **CPU**: 8+ cores
- **RAM**: 16GB+
- **Disk**: 10GB
- **Use case**: Heavy workloads (10+ req/min), multiple instances

### Model Resource Usage
- **sentence-transformers/all-MiniLM-L6-v2**: ~90MB disk, ~500MB RAM
- **Z3 solver**: ~50MB disk, varies by problem complexity
- **PyTorch runtime**: ~500MB RAM

### Estimation Tool
```bash
# Measure actual resource usage
docker stats smt-pipeline-service

# Example output:
# CONTAINER            CPU %     MEM USAGE / LIMIT     MEM %
# smt-pipeline-service 15.00%    2.5GiB / 4GiB        62.5%
```

---

## Security Considerations

### 1. Non-Root User
The container runs as user `app` (UID 1000), not root. This limits potential damage from container breakout.

### 2. Secret Management
- **Never** commit `.env` to version control
- Use environment variables for secrets
- Consider using Docker secrets or external secret managers (AWS Secrets Manager, HashiCorp Vault)

### 3. Network Isolation
- Container runs in isolated network (`smt-network`)
- Only port 8000 is exposed
- Consider using reverse proxy for HTTPS termination

### 4. Dependency Security
```bash
# Scan image for vulnerabilities
docker scan smt-pipeline:latest

# Update base image regularly
docker pull python:3.11-slim
docker build --no-cache -t smt-pipeline:latest .
```

### 5. Input Validation
- All inputs validated by Pydantic models
- LLM prompts sanitized to prevent injection
- SMT-LIB code executed in isolated solver process

### 6. Rate Limiting (Recommended)
```python
# Add to FastAPI app
from slowapi import Limiter, _rate_limit_exceeded_handler
from slowapi.util import get_remote_address

limiter = Limiter(key_func=get_remote_address)
app.state.limiter = limiter
app.add_exception_handler(RateLimitExceeded, _rate_limit_exceeded_handler)

@app.post("/pipeline/process")
@limiter.limit("10/minute")
async def process_pipeline(...):
    ...
```

### 7. HTTPS Only (Production)
```nginx
# Example nginx reverse proxy config
server {
    listen 443 ssl http2;
    server_name api.example.com;

    ssl_certificate /etc/ssl/certs/cert.pem;
    ssl_certificate_key /etc/ssl/private/key.pem;

    location / {
        proxy_pass http://localhost:8000;
        proxy_set_header Host $host;
        proxy_set_header X-Real-IP $remote_addr;
    }
}
```

---

## Additional Resources

### Documentation
- [Architecture Overview](./architecture/ARCHITECTURE.md)
- [API Documentation](http://localhost:8000/docs) (when running)
- [Pipeline Design Spec](./specs/PIPELINE-DESIGN.md)

### External Resources
- [Docker Documentation](https://docs.docker.com/)
- [FastAPI Documentation](https://fastapi.tiangolo.com/)
- [Anthropic API Documentation](https://docs.anthropic.com/)
- [sentence-transformers Documentation](https://www.sbert.net/)
- [Z3 Solver Documentation](https://github.com/Z3Prover/z3)

### Support
- **Issues**: Create an issue on GitHub
- **Questions**: Check documentation or ask in discussions
- **Security**: Report security issues privately to security@example.com

---

## Quick Reference

### Common Commands
```bash
# Build
docker compose build

# Start
docker compose up -d

# Stop
docker compose down

# Logs
docker compose logs -f

# Health
curl http://localhost:8000/health

# Restart
docker compose restart

# Rebuild and restart
docker compose up -d --build

# Clean up
docker compose down -v
docker system prune -a
```

### Port Reference
- **8000**: FastAPI application (HTTP)
- **8000/health**: Health check endpoint
- **8000/docs**: Swagger UI documentation
- **8000/pipeline/process**: Main processing endpoint

### File Locations in Container
- **Application code**: `/app/src/`
- **Python packages**: `/home/app/.local/`
- **Model cache**: `/home/app/.cache/`
- **Z3 binary**: `/usr/bin/z3`

---

**Deployment complete!** For questions or issues, consult the troubleshooting section or open an issue on GitHub.
