"""pySMT-based SMT solver executor.

Uses pySMT library for solver-agnostic SMT-LIB execution.
"""

import logging
import asyncio
import io
from typing import Optional

from src.domain.exceptions import SolverExecutionError

logger = logging.getLogger(__name__)


class PysmtExecutor:
    """SMT solver executor using pySMT library."""

    def __init__(self, solver_name: str = "z3"):
        """Initialize pySMT executor.

        Args:
            solver_name: Solver backend to use (z3, cvc5, msat, etc.)
        """
        self.solver_name = solver_name
        logger.info(f"Initialized pySMT executor with solver: {solver_name}")

    async def execute(
        self,
        smt_code: str,
        timeout: float = 30.0
    ) -> dict:
        """Execute SMT-LIB code and return results.

        Runs in thread pool to avoid blocking event loop.

        Args:
            smt_code: Complete SMT-LIB code to execute
            timeout: Execution timeout in seconds

        Returns:
            Dictionary with keys:
                - success: bool
                - check_sat_result: str (sat/unsat/unknown or error)
                - model: Optional[str]
                - unsat_core: Optional[str]
                - raw_output: str
                - error_message: Optional[str]
        """
        logger.debug(f"Executing SMT code ({len(smt_code)} chars)")

        try:
            # Run in thread pool
            loop = asyncio.get_event_loop()
            result = await asyncio.wait_for(
                loop.run_in_executor(None, self._execute_sync, smt_code),
                timeout=timeout
            )

            logger.debug(f"Execution completed: {result['check_sat_result']}")
            return result

        except asyncio.TimeoutError:
            logger.error(f"SMT execution timeout ({timeout}s)")
            return {
                "success": False,
                "check_sat_result": "timeout",
                "model": None,
                "unsat_core": None,
                "raw_output": f"Execution timed out after {timeout} seconds",
                "error_message": f"Solver execution exceeded timeout of {timeout}s"
            }

        except Exception as e:
            logger.error(f"SMT execution failed: {e}")
            return {
                "success": False,
                "check_sat_result": "error",
                "model": None,
                "unsat_core": None,
                "raw_output": str(e),
                "error_message": str(e)
            }

    def _execute_sync(self, smt_code: str) -> dict:
        """Execute SMT code synchronously (runs in thread pool).

        Args:
            smt_code: SMT-LIB code to execute

        Returns:
            Execution result dictionary
        """
        try:
            from pysmt.smtlib.parser import SmtLibParser
            from pysmt.shortcuts import Solver, get_model, get_unsat_core
            import pysmt.exceptions

            # Parse SMT-LIB code
            parser = SmtLibParser()
            script = parser.get_script(io.StringIO(smt_code))

            # Get assertions
            formula = script.get_last_formula()

            # Execute with solver
            # Note: Don't specify logic - let pySMT auto-detect from the formula
            with Solver(name=self.solver_name) as solver:
                solver.add_assertion(formula)

                # Check satisfiability
                is_sat = solver.solve()

                if is_sat:
                    # Get model
                    model = solver.get_model()
                    model_str = str(model) if model else "Model generation not supported"

                    return {
                        "success": True,
                        "check_sat_result": "sat",
                        "model": model_str,
                        "unsat_core": None,
                        "raw_output": f"sat\n{model_str}",
                        "error_message": None
                    }
                else:
                    # Try to get unsat core (may not be supported by all solvers)
                    try:
                        core = get_unsat_core()
                        core_str = str(core) if core else "Unsat core not available"
                    except:
                        core_str = "Unsat core not supported by solver"

                    return {
                        "success": True,
                        "check_sat_result": "unsat",
                        "model": None,
                        "unsat_core": core_str,
                        "raw_output": f"unsat\n{core_str}",
                        "error_message": None
                    }

        except Exception as e:
            error_msg = str(e)
            logger.error(f"pySMT execution error: {error_msg}")

            return {
                "success": False,
                "check_sat_result": "error",
                "model": None,
                "unsat_core": None,
                "raw_output": error_msg,
                "error_message": error_msg
            }
