"""
Domain layer module.

This module contains the core business logic for the SMT Pipeline service.
It is independent of infrastructure concerns and depends only on protocols (interfaces).

Key components:
- models.py: Domain models (Pydantic-based data structures)
- interfaces.py: Protocol definitions for external dependencies
- steps/: Pipeline step implementations (formalization, extraction, validation)
- verification/: Semantic verification logic using embeddings
"""
