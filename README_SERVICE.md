# Semantic-Preserving SMT-LIB Pipeline Service

A production-ready FastAPI service that transforms informal natural language text into verified, executable SMT-LIB code with semantic preservation guarantees.

## Features

- **Three-Step Verification Pipeline**:
  1. **Formalization**: Convert informal text to formal text (≥91% semantic similarity)
  2. **Extraction**: Generate annotated SMT-LIB code (≤5% information degradation)
  3. **Validation**: Execute with SMT solver and fix errors automatically

- **Semantic Verification**: Uses embedding distance metrics to ensure semantic preservation at each step
- **Automatic Error Correction**: LLM-based fixing of SMT-LIB syntax/semantic errors
- **Quality Gates**: Automatic triggers for manual review based on retry counts and threshold proximity
- **Production-Ready**: Full async/await, comprehensive error handling, structured logging

## Quick Start

### 1. Install Dependencies

```bash
# Install Poetry (if not already installed)
curl -sSL https://install.python-poetry.org | python3 -

# Install project dependencies
poetry install
```

### 2. Configure Environment

```bash
# Copy example environment file
cp .env.example .env

# Edit .env and add your Anthropic API key
# ANTHROPIC_API_KEY=your_api_key_here
```

### 3. Run the Service

```bash
# Start the FastAPI server
poetry run python -m src.main

# Or use uvicorn directly
poetry run uvicorn src.main:app --reload --host 0.0.0.0 --port 8000
```

### 4. Test the Service

Open your browser to: http://localhost:8000/docs

Or use curl:

```bash
# Health check
curl http://localhost:8000/health

# Get example texts
curl http://localhost:8000/pipeline/examples

# Process informal text
curl -X POST http://localhost:8000/pipeline/process \
  -H "Content-Type: application/json" \
  -d '{"informal_text": "x must be greater than 5"}'
```

## API Endpoints

### `POST /pipeline/process`

Process informal text through the complete pipeline.

**Request:**
```json
{
  "informal_text": "x must be greater than 5 and y must be less than 10"
}
```

**Response:**
```json
{
  "informal_text": "x must be greater than 5 and y must be less than 10",
  "formal_text": "Let x and y be integers. x > 5. y < 10.",
  "formalization_similarity": 0.94,
  "smt_lib_code": "(declare-const x Int)\n(declare-const y Int)\n...",
  "extraction_degradation": 0.03,
  "check_sat_result": "sat",
  "model": "((x 6) (y 9))",
  "unsat_core": null,
  "solver_success": true,
  "metrics": {
    "formalization_attempts": 1,
    "extraction_attempts": 1,
    "validation_attempts": 1,
    "total_time_seconds": 3.45
  },
  "passed_all_checks": true,
  "requires_manual_review": false
}
```

### `GET /pipeline/examples`

Get example informal texts for testing.

### `GET /health`

Health check endpoint.

## Architecture

The service follows Clean Architecture principles:

```
src/
├── api/              # API layer (FastAPI routes, models, dependencies)
├── application/      # Application layer (PipelineService orchestration)
├── domain/           # Domain layer (business logic, models, protocols)
│   ├── steps/        # Pipeline steps (formalization, extraction, validation)
│   └── verification/ # Semantic verification logic
├── infrastructure/   # Infrastructure layer (LLM, embeddings, SMT solver)
│   ├── llm/          # Anthropic Claude client and prompts
│   ├── embeddings/   # Sentence transformers provider
│   └── smt/          # pySMT executor
└── shared/           # Shared utilities (Result type, config, logging)
```

## Configuration

All configuration is done via environment variables (see `.env.example`):

- **Anthropic API**: API key, model, timeout
- **Embeddings**: Model name (default: all-MiniLM-L6-v2)
- **Thresholds**: Similarity threshold (0.91), degradation limit (0.05)
- **Retries**: Max attempts per step (3/5/3)
- **Manual Review**: Triggers for human review

## Development

### Run Tests

```bash
poetry run pytest
```

### Type Checking

```bash
poetry run mypy src/
```

### Linting

```bash
poetry run ruff check src/
```

### Formatting

```bash
poetry run black src/
```

## Dependencies

- **FastAPI**: Web framework
- **Anthropic**: Claude API client
- **sentence-transformers**: Embedding models
- **pySMT**: Solver-agnostic SMT-LIB execution
- **scikit-learn**: Cosine similarity calculation

## License

Proprietary
