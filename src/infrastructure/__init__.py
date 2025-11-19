"""
Infrastructure layer module.

This module contains concrete implementations of all domain protocols,
integrating with external services: Anthropic Claude API, sentence-transformers
embedding model, and Z3 SMT solver.

Key components:
- llm/: Anthropic Claude client and prompt templates
- embeddings/: SentenceTransformer embedding provider
- smt/: Z3 solver executor
- config.py: Configuration management with Pydantic Settings
"""
