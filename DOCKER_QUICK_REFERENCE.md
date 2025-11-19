# Docker Quick Reference Card

## Essential Commands

### Initial Setup
```bash
# 1. Copy environment template
cp .env.example .env

# 2. Edit .env and add your ANTHROPIC_API_KEY
nano .env  # or your preferred editor

# 3. Build and start
docker compose up -d

# 4. Verify health (wait 40 seconds for startup)
curl http://localhost:8000/health
```

### Daily Operations
```bash
# Start service
docker compose up -d

# Stop service
docker compose down

# Restart service
docker compose restart

# View logs (real-time)
docker compose logs -f

# Check status
docker compose ps
```

### Makefile Shortcuts
```bash
# Build
make build

# Start
make up

# Stop
make down

# View logs
make logs

# Check health
make health

# Run all tests
make test

# Development mode (hot reload)
make dev-up
```

## Service Endpoints

- **Health Check**: http://localhost:8000/health
- **API Docs (Swagger)**: http://localhost:8000/docs
- **ReDoc**: http://localhost:8000/redoc
- **Process Endpoint**: POST http://localhost:8000/pipeline/process

## Testing Examples

### Health Check
```bash
curl http://localhost:8000/health
# Expected: {"status":"healthy"}
```

### Process Request (Placeholder)
```bash
curl -X POST http://localhost:8000/pipeline/process \
  -H "Content-Type: application/json" \
  -d '{"informal_text": "There exists a number x that is greater than 5"}'
```

### Check Environment Variables
```bash
docker compose exec smt-pipeline env | grep ANTHROPIC
```

## Troubleshooting

### Container Won't Start
```bash
# Check logs for errors
docker compose logs smt-pipeline

# Check container status
docker compose ps -a

# Rebuild from scratch
docker compose down
docker build --no-cache -t smt-pipeline:latest .
docker compose up -d
```

### Health Check Failing
```bash
# Wait longer (model loading takes time)
sleep 60 && curl http://localhost:8000/health

# Check if port is available
lsof -i :8000

# View detailed logs
docker compose logs -f smt-pipeline
```

### Port Conflict
```bash
# Change port in docker-compose.yml
# ports:
#   - "8001:8000"  # Use 8001 instead
```

### Out of Memory
```bash
# Increase memory limit in docker-compose.yml
# deploy:
#   resources:
#     limits:
#       memory: 8G  # Increase from 4G
```

## File Locations

### Configuration
- **Environment**: `.env` (local, gitignored)
- **Environment Template**: `.env.example` (versioned)
- **Docker Compose**: `docker-compose.yml` (production)
- **Dev Compose**: `docker-compose.dev.yml` (development)
- **Build Instructions**: `Dockerfile`
- **Build Exclusions**: `.dockerignore`

### Documentation
- **Deployment Guide**: `docs/DEPLOYMENT.md`
- **Architecture**: `docs/architecture/ARCHITECTURE.md`
- **This Guide**: `DOCKER_QUICK_REFERENCE.md`
- **Summary**: `DOCKER_DEPLOYMENT_SUMMARY.md`

### Application
- **Source Code**: `src/main.py` (placeholder)
- **Dependencies**: `requirements.txt`

## Resource Requirements

### Minimum
- CPU: 1 core
- RAM: 2GB
- Disk: 3GB

### Recommended
- CPU: 2-4 cores
- RAM: 4-8GB
- Disk: 5GB

### Image Size
- **Total**: 1.33GB
- **Base**: ~140MB (python:3.11-slim)
- **Dependencies**: ~500MB (pip packages)
- **Model**: ~90MB (sentence-transformers)
- **PyTorch**: ~560MB

## Environment Variables Reference

### Required
- `ANTHROPIC_API_KEY`: Your Anthropic API key (get from https://console.anthropic.com/)

### Optional (with defaults)
- `ANTHROPIC_MODEL`: claude-sonnet-4-5-20250929
- `EMBEDDING_MODEL`: sentence-transformers/all-MiniLM-L6-v2
- `FORMALIZATION_SIMILARITY_THRESHOLD`: 0.91
- `EXTRACTION_DEGRADATION_THRESHOLD`: 0.05
- `MAX_FORMALIZATION_RETRIES`: 3
- `MAX_EXTRACTION_RETRIES`: 5
- `MAX_VALIDATION_RETRIES`: 3
- `SMT_SOLVER_TIMEOUT`: 30
- `LOG_LEVEL`: INFO

## Security Checklist

- [ ] Never commit `.env` to version control
- [ ] Rotate API keys regularly
- [ ] Use HTTPS in production (reverse proxy)
- [ ] Keep base image updated
- [ ] Scan for vulnerabilities: `docker scan smt-pipeline:latest`
- [ ] Run as non-root user (already configured)
- [ ] Use resource limits (already configured)
- [ ] Implement rate limiting in production

## Common Issues

| Issue | Solution |
|-------|----------|
| Container exits immediately | Check logs: `docker compose logs` |
| Health check fails | Wait 40s for model loading |
| Port 8000 in use | Change port in docker-compose.yml |
| API key error | Update `ANTHROPIC_API_KEY` in `.env` |
| Out of memory | Increase memory limit to 8G |
| Slow startup | Normal - model loads in 30-40s |
| Permission denied | Check file ownership, use `--chown` |

## Build Optimization

```bash
# Use BuildKit for faster builds
DOCKER_BUILDKIT=1 docker compose build

# Clean build (no cache)
docker compose build --no-cache

# Prune unused resources
docker system prune -a
```

## Development Workflow

```bash
# 1. Start in dev mode (hot reload)
make dev-up

# 2. Make code changes in src/

# 3. View logs to see reload
make dev-logs

# 4. Test changes
curl http://localhost:8000/health

# 5. Stop when done
make dev-down
```

## Production Deployment

```bash
# 1. Review security settings
cat docs/DEPLOYMENT.md

# 2. Configure production .env
cp .env.example .env
# Edit with production values

# 3. Build production image
docker compose build

# 4. Run in production mode
docker compose up -d

# 5. Verify health
curl http://localhost:8000/health

# 6. Monitor logs
docker compose logs -f

# 7. Set up HTTPS reverse proxy (nginx/traefik)
# 8. Configure monitoring and alerting
```

## Links

- **Full Deployment Guide**: `docs/DEPLOYMENT.md`
- **Architecture Docs**: `docs/architecture/ARCHITECTURE.md`
- **Docker Docs**: https://docs.docker.com/
- **FastAPI Docs**: https://fastapi.tiangolo.com/
- **Anthropic Docs**: https://docs.anthropic.com/

---

**Quick Start**: `cp .env.example .env` → Edit ANTHROPIC_API_KEY → `docker compose up -d` → Wait 40s → `curl http://localhost:8000/health`
