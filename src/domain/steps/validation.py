"""Step 3: SMT solver validation with error correction.

Executes SMT-LIB code with solver and fixes errors using LLM.
"""

import logging
from typing import TYPE_CHECKING

from src.shared.result import Result, Ok, Err
from src.domain.models import SolverResult
from src.domain.exceptions import ValidationError

if TYPE_CHECKING:
    from src.domain.protocols import LLMProvider, SMTSolver

logger = logging.getLogger(__name__)


class ValidationStep:
    """Step 3: SMT solver validation with error correction."""

    def __init__(
        self,
        llm_provider: 'LLMProvider',
        smt_solver: 'SMTSolver',
        max_retries: int = 3,
        solver_timeout: float = 30.0
    ):
        """Initialize validation step.

        Args:
            llm_provider: Provider for LLM calls (error fixing)
            smt_solver: SMT solver executor
            max_retries: Maximum retry attempts for error fixing (default 3)
            solver_timeout: Timeout for solver execution in seconds (default 30.0)
        """
        self.llm_provider = llm_provider
        self.smt_solver = smt_solver
        self.max_retries = max_retries
        self.solver_timeout = solver_timeout

    async def execute(
        self,
        smt_code: str
    ) -> Result[SolverResult, ValidationError]:
        """Execute solver validation with error correction.

        Args:
            smt_code: SMT-LIB code from Step 2

        Returns:
            Ok(SolverResult) if solver executes successfully
            Err(ValidationError) if all retries exhausted
        """
        logger.info(f"Starting validation (smt_code_length={len(smt_code)})")

        current_code = smt_code
        last_error = ""

        for attempt in range(self.max_retries):
            logger.debug(
                f"Validation attempt {attempt + 1}/{self.max_retries}"
            )

            try:
                # Execute SMT solver
                result = await self.smt_solver.execute(
                    current_code,
                    timeout=self.solver_timeout
                )

                # Check if execution succeeded
                if result["success"]:
                    logger.info(
                        f"Validation succeeded after {attempt + 1} attempts. "
                        f"Result: {result['check_sat_result']}"
                    )
                    return Ok(SolverResult(
                        success=True,
                        check_sat_result=result["check_sat_result"],
                        model=result.get("model"),
                        unsat_core=result.get("unsat_core"),
                        raw_output=result["raw_output"],
                        attempts=attempt + 1
                    ))

                # Execution failed - try to fix
                last_error = result.get("error_message", "Unknown error")
                logger.warning(
                    f"Attempt {attempt + 1} failed with error: {last_error}"
                )

                if attempt < self.max_retries - 1:
                    # Use LLM to fix the error
                    logger.debug("Requesting LLM to fix SMT errors")
                    current_code = await self.llm_provider.fix_smt_errors(
                        current_code,
                        last_error
                    )
                    logger.debug("Received fixed SMT code from LLM")

            except Exception as e:
                last_error = str(e)
                logger.error(f"Attempt {attempt + 1} raised exception: {e}")

                if attempt < self.max_retries - 1:
                    # Try to fix
                    try:
                        current_code = await self.llm_provider.fix_smt_errors(
                            current_code,
                            last_error
                        )
                    except Exception as fix_error:
                        logger.error(f"Failed to fix error: {fix_error}")
                        # Continue to next iteration with same code

        # All retries exhausted
        logger.error(
            f"Validation failed after {self.max_retries} attempts. "
            f"Last error: {last_error}"
        )
        return Err(ValidationError(
            message=(
                f"SMT solver validation failed after {self.max_retries} attempts. "
                f"Last error: {last_error}"
            ),
            last_error=last_error,
            attempts=self.max_retries
        ))
