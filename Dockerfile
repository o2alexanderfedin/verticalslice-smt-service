# ===========================
# Stage 1: Builder
# ===========================
# Specify platform for Digital Ocean App Platform compatibility (linux/amd64 only)
# This ensures correct architecture on ARM Macs and in CI/CD
FROM --platform=linux/amd64 python:3.11-slim AS builder

# Install build dependencies and Z3 solver
RUN apt-get update && apt-get install -y --no-install-recommends \
    gcc \
    g++ \
    build-essential \
    curl \
    wget \
    z3 \
    && rm -rf /var/lib/apt/lists/*

# Set working directory for builder
WORKDIR /build

# Copy requirements and install Python dependencies
COPY requirements.txt .

# Install CPU-only PyTorch first to avoid downloading 3GB+ CUDA libraries
# This is critical for GitHub Actions runners with limited disk space
RUN pip install --no-cache-dir --user torch --index-url https://download.pytorch.org/whl/cpu

# Install remaining dependencies (torch already satisfied from CPU-only install)
RUN pip install --no-cache-dir --user -r requirements.txt

# Pre-download sentence-transformers model to avoid runtime download
# This saves time and ensures the model is always available
RUN python -c "from sentence_transformers import SentenceTransformer; \
    model = SentenceTransformer('sentence-transformers/all-MiniLM-L6-v2'); \
    print('Model downloaded successfully')"

# ===========================
# Stage 2: Runtime
# ===========================
# Specify platform for Digital Ocean App Platform compatibility (linux/amd64 only)
FROM --platform=linux/amd64 python:3.11-slim

# Install runtime dependencies only
# libgomp1: Required for PyTorch/sentence-transformers
# z3: SMT solver for validation step
# curl: For health checks
RUN apt-get update && apt-get install -y --no-install-recommends \
    libgomp1 \
    z3 \
    curl \
    && rm -rf /var/lib/apt/lists/*

# Create non-root user for security
RUN useradd -m -u 1000 -s /bin/bash app

# Copy Python packages from builder stage
COPY --from=builder /root/.local /home/app/.local

# Copy downloaded sentence-transformers model from builder stage
# This includes model weights and tokenizer
COPY --from=builder /root/.cache /home/app/.cache

# Set up application directory
WORKDIR /app

# Copy application source code
# Assumes src/ directory contains the FastAPI application
COPY --chown=app:app ./src ./src

# Ensure the app user's local bin is in PATH
ENV PATH=/home/app/.local/bin:$PATH

# Switch to non-root user
USER app

# Expose FastAPI default port
EXPOSE 8000

# Health check configuration
# Checks /health endpoint every 30 seconds
# Allows 10 seconds timeout per check
# Requires 3 consecutive failures to mark as unhealthy
# Waits 40 seconds before starting checks (model loading time)
HEALTHCHECK --interval=30s --timeout=10s --retries=3 --start-period=40s \
    CMD curl -f http://localhost:8000/health || exit 1

# Run FastAPI application with uvicorn
# --host 0.0.0.0: Listen on all network interfaces
# --port 8000: Default FastAPI port
# --no-access-log: Reduce verbosity in production (optional, can be removed for debugging)
CMD ["uvicorn", "src.main:app", "--host", "0.0.0.0", "--port", "8000"]
