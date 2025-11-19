"""
Shared utilities module.

This module contains common utilities used across all layers of the application,
including Result types for functional error handling and logging configuration.
"""

from src.shared.result import Err, Ok, Result

__all__ = ["Ok", "Err", "Result"]
