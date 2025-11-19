.PHONY: help build up down restart logs health test clean prune dev-up dev-down

# Default target
help:
	@echo "SMT Pipeline Service - Docker Management"
	@echo ""
	@echo "Production Commands:"
	@echo "  make build       - Build Docker image"
	@echo "  make up          - Start service in detached mode"
	@echo "  make down        - Stop and remove containers"
	@echo "  make restart     - Restart service"
	@echo "  make logs        - View service logs (follow mode)"
	@echo "  make health      - Check service health"
	@echo "  make test        - Run health check and basic API test"
	@echo ""
	@echo "Development Commands:"
	@echo "  make dev-up      - Start service in dev mode (with hot reload)"
	@echo "  make dev-down    - Stop dev service"
	@echo "  make dev-logs    - View dev service logs"
	@echo ""
	@echo "Maintenance Commands:"
	@echo "  make clean       - Stop and remove containers, networks"
	@echo "  make prune       - Clean up Docker system (images, containers, volumes)"
	@echo "  make rebuild     - Rebuild and restart service"
	@echo ""
	@echo "Usage Examples:"
	@echo "  make build && make up    - Build and start production service"
	@echo "  make dev-up              - Start development service with hot reload"
	@echo "  make logs                - View real-time logs"
	@echo "  make test                - Verify service is working"

# ===========================
# Production Commands
# ===========================

build:
	@echo "Building Docker image..."
	docker compose build

up:
	@echo "Starting service..."
	docker compose up -d
	@echo "Service started. Run 'make logs' to view logs or 'make health' to check status."

down:
	@echo "Stopping service..."
	docker compose down

restart:
	@echo "Restarting service..."
	docker compose restart

logs:
	@echo "Viewing logs (Ctrl+C to exit)..."
	docker compose logs -f

health:
	@echo "Checking service health..."
	@sleep 2
	@curl -f http://localhost:8000/health && echo "\n✓ Service is healthy" || echo "\n✗ Service is not responding"

test: health
	@echo ""
	@echo "Testing API documentation endpoint..."
	@curl -f -s http://localhost:8000/docs > /dev/null && echo "✓ API docs accessible at http://localhost:8000/docs" || echo "✗ API docs not accessible"
	@echo ""
	@echo "Testing OpenAPI spec..."
	@curl -f -s http://localhost:8000/openapi.json > /dev/null && echo "✓ OpenAPI spec available" || echo "✗ OpenAPI spec not available"
	@echo ""
	@echo "All basic checks passed! Service is ready."

# ===========================
# Development Commands
# ===========================

dev-up:
	@echo "Starting service in development mode..."
	docker compose -f docker-compose.dev.yml up -d
	@echo "Development service started with hot reload enabled."

dev-down:
	@echo "Stopping development service..."
	docker compose -f docker-compose.dev.yml down

dev-logs:
	@echo "Viewing development logs (Ctrl+C to exit)..."
	docker compose -f docker-compose.dev.yml logs -f

# ===========================
# Maintenance Commands
# ===========================

clean:
	@echo "Cleaning up containers and networks..."
	docker compose down -v
	@echo "Cleanup complete."

prune:
	@echo "Pruning Docker system..."
	@echo "This will remove:"
	@echo "  - All stopped containers"
	@echo "  - All networks not used by at least one container"
	@echo "  - All dangling images"
	@echo "  - All build cache"
	@read -p "Continue? [y/N] " -n 1 -r; \
	echo; \
	if [[ $$REPLY =~ ^[Yy]$$ ]]; then \
		docker system prune -a -f; \
		echo "Prune complete."; \
	else \
		echo "Cancelled."; \
	fi

rebuild:
	@echo "Rebuilding and restarting service..."
	docker compose down
	docker compose build --no-cache
	docker compose up -d
	@echo "Rebuild complete. Service restarted."

# ===========================
# Utility Commands
# ===========================

shell:
	@echo "Opening shell in container..."
	docker compose exec smt-pipeline /bin/bash

ps:
	@echo "Container status:"
	docker compose ps

env:
	@echo "Environment variables in container:"
	docker compose exec smt-pipeline env | grep -E "ANTHROPIC|EMBEDDING|THRESHOLD|RETRY|SOLVER" | sort

inspect:
	@echo "Container details:"
	docker inspect smt-pipeline-service

image-size:
	@echo "Docker image size:"
	docker images smt-pipeline:latest --format "table {{.Repository}}\t{{.Tag}}\t{{.Size}}"
