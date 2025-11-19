"""Sample informal texts for testing the pipeline.

Provides example inputs with varying complexity levels.
"""

SAMPLE_TEXTS = [
    {
        "id": "simple_constraint",
        "description": "Simple numeric constraint",
        "informal_text": "x must be greater than 5",
        "expected_result": "sat",
        "complexity": "simple"
    },
    {
        "id": "two_variables",
        "description": "Two variables with constraints",
        "informal_text": "x must be greater than 5 and y must be less than 10, and x plus y equals 12",
        "expected_result": "sat",
        "complexity": "medium"
    },
    {
        "id": "unsatisfiable",
        "description": "Unsatisfiable constraints",
        "informal_text": "x is greater than 10 and x is less than 5",
        "expected_result": "unsat",
        "complexity": "simple"
    },
    {
        "id": "complex_conditions",
        "description": "Complex nested conditions",
        "informal_text": (
            "If x is positive, then y must be negative. "
            "If y is negative, then z must be greater than 100. "
            "Also, x plus y plus z must equal 50."
        ),
        "expected_result": "sat",
        "complexity": "complex"
    },
    {
        "id": "arithmetic_relations",
        "description": "Multiple arithmetic relations",
        "informal_text": (
            "Let a, b, and c be integers. "
            "The sum of a and b is 10. "
            "The product of b and c is 20. "
            "c is greater than a."
        ),
        "expected_result": "sat",
        "complexity": "medium"
    },
    {
        "id": "boolean_logic",
        "description": "Boolean variables with logic",
        "informal_text": (
            "Let p and q be boolean variables. "
            "Either p is true or q is true, but not both. "
            "If p is true, then variable x must be positive. "
            "If q is true, then variable x must be negative."
        ),
        "expected_result": "sat",
        "complexity": "complex"
    }
]


def get_sample_by_id(sample_id: str) -> dict:
    """Get a sample text by its ID.

    Args:
        sample_id: Sample identifier

    Returns:
        Sample dictionary

    Raises:
        ValueError: If sample ID not found
    """
    for sample in SAMPLE_TEXTS:
        if sample["id"] == sample_id:
            return sample
    raise ValueError(f"Sample with ID '{sample_id}' not found")


def get_samples_by_complexity(complexity: str) -> list[dict]:
    """Get sample texts by complexity level.

    Args:
        complexity: Complexity level (simple, medium, complex)

    Returns:
        List of matching samples
    """
    return [
        sample for sample in SAMPLE_TEXTS
        if sample["complexity"] == complexity
    ]
