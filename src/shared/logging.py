"""
Structured logging configuration.

This module provides centralized logging configuration for the application
with structured logging support (JSON formatting for production).

Usage:
    from src.shared.logging import get_logger

    logger = get_logger(__name__)
    logger.info("Processing request", extra={"user_id": 123})
"""

import logging
import sys


def get_logger(name: str, level: int | None = None) -> logging.Logger:
    """
    Get a configured logger instance.

    Args:
        name: Logger name (usually __name__ of the calling module)
        level: Optional logging level (defaults to INFO)

    Returns:
        Configured logger instance
    """
    logger = logging.getLogger(name)

    if level is None:
        level = logging.INFO

    logger.setLevel(level)

    # Add console handler if no handlers exist
    if not logger.handlers:
        handler = logging.StreamHandler(sys.stdout)
        handler.setLevel(level)

        # Use structured format for better parsing
        formatter = logging.Formatter(
            fmt="%(asctime)s - %(name)s - %(levelname)s - %(message)s",
            datefmt="%Y-%m-%d %H:%M:%S",
        )
        handler.setFormatter(formatter)
        logger.addHandler(handler)

    return logger
