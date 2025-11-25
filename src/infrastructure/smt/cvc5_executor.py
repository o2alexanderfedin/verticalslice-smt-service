"""cvc5-based SMT solver executor.

Uses cvc5's native Python API and built-in SMT-LIB parser for solver execution.
"""

import asyncio
import logging
from typing import Any

import cvc5

logger = logging.getLogger(__name__)


class Cvc5Executor:
    """SMT solver executor using cvc5 native Python API.

    This executor uses cvc5's built-in parser (InputParser) to parse SMT-LIB
    code and execute it through the native Python bindings. All operations are
    async using run_in_executor to avoid blocking the event loop.
    """

    def __init__(self) -> None:
        """Initialize cvc5 executor.

        Creates a fresh solver instance for each executor. The solver is
        stateless and can be reused across multiple execute() calls.
        """
        logger.info("Initialized Cvc5Executor with cvc5 native API")

    async def execute(self, smt_code: str, timeout: float = 30.0) -> dict[str, Any]:
        """Execute SMT-LIB code and return results.

        Runs in thread pool to avoid blocking event loop during parsing and solving.

        Args:
            smt_code: Complete SMT-LIB code to execute
            timeout: Execution timeout in seconds

        Returns:
            Dictionary with keys:
                - success: bool (whether execution succeeded)
                - check_sat_result: str (sat/unsat/unknown or error)
                - model: str | None (variable assignments if sat)
                - unsat_core: str | None (conflicting constraints if unsat)
                - raw_output: str (complete solver output)
                - error_message: str | None (error details if failed)
        """
        logger.debug(f"Executing SMT code ({len(smt_code)} chars) with timeout={timeout}s")

        try:
            # Run in thread pool
            # Note: We can't interrupt threads, so cvc5's tlimit option is the real timeout.
            # asyncio.wait_for is a safety net with extra buffer for thread overhead.
            loop = asyncio.get_event_loop()
            async_timeout = max(timeout * 2, timeout + 2.0)  # Give cvc5 time to timeout internally
            result = await asyncio.wait_for(
                loop.run_in_executor(None, self._execute_sync, smt_code, timeout),
                timeout=async_timeout,
            )

            logger.debug(f"Execution completed: {result['check_sat_result']}")
            return result

        except TimeoutError:
            logger.error(f"SMT execution timeout ({timeout}s) - asyncio wait_for expired")
            return {
                "success": False,
                "check_sat_result": "timeout",
                "model": None,
                "unsat_core": None,
                "raw_output": f"Execution timed out after {timeout} seconds",
                "error_message": f"Solver execution exceeded timeout of {timeout}s",
            }

        except Exception as e:
            logger.error(f"SMT execution failed: {e}")
            return {
                "success": False,
                "check_sat_result": "error",
                "model": None,
                "unsat_core": None,
                "raw_output": str(e),
                "error_message": str(e),
            }

    def _execute_sync(self, smt_code: str, timeout: float) -> dict[str, Any]:
        """Execute SMT code synchronously (runs in thread pool).

        Args:
            smt_code: SMT-LIB code to execute
            timeout: Execution timeout in seconds

        Returns:
            Execution result dictionary
        """
        try:
            # Create fresh solver instance
            solver = cvc5.Solver()

            # Set timeout in milliseconds (tlimit option in cvc5)
            solver.setOption("tlimit", str(int(timeout * 1000)))

            # Enable model and unsat core production
            solver.setOption("produce-models", "true")
            solver.setOption("produce-unsat-cores", "true")

            # Create parser
            parser = cvc5.InputParser(solver)
            symbol_manager = parser.getSymbolManager()

            # Set input string
            parser.setStringInput(
                cvc5.InputLanguage.SMT_LIB_2_6,
                smt_code,
                "input",  # Input name for error messages
            )

            # Parse and execute all commands
            check_sat_result: str | None = None
            model: str | None = None
            unsat_core: str | None = None
            output_lines: list[str] = []

            while True:
                cmd = parser.nextCommand()
                if cmd.isNull():
                    break

                # Execute command
                cmd_output = cmd.invoke(solver, symbol_manager)

                # Track output
                output_str = str(cmd_output) if cmd_output is not None else ""
                if output_str:
                    output_lines.append(output_str)

                # Detect check-sat result
                output_lower = output_str.lower().strip()
                if output_lower in ("sat", "unsat", "unknown"):
                    check_sat_result = output_lower

                # Detect model output (from get-model command)
                # Model format: starts with "(" and contains "define-fun"
                elif check_sat_result == "sat" and output_str.strip().startswith("("):
                    if "define-fun" in output_str:
                        model = output_str.strip()
                        logger.debug("Model extracted from (get-model) command")

                # Detect unsat core output (from get-unsat-core command)
                # Core format: starts with "(" and contains named assertions
                elif (
                    check_sat_result == "unsat"
                    and output_str.strip().startswith("(")
                    and "define-fun" not in output_str
                ):
                    unsat_core = output_str.strip()
                    logger.debug("Unsat core extracted from (get-unsat-core) command")

            # If no check-sat was found in commands, execute it explicitly
            if check_sat_result is None:
                logger.debug("No check-sat found in SMT code, executing explicitly")
                try:
                    result = solver.checkSat()
                    check_sat_result = self._parse_result(result)
                    output_lines.append(check_sat_result)
                except Exception as e:
                    # cvc5 may throw if timeout exceeded
                    logger.warning(f"checkSat raised exception (likely timeout): {e}")
                    check_sat_result = "timeout"
                    output_lines.append(f"timeout (exception: {e})")

            # If model wasn't extracted but result is sat, try to get it programmatically
            if check_sat_result == "sat" and model is None:
                try:
                    # Re-parse to add (get-model) command
                    logger.debug("Attempting to extract model programmatically")

                    # Create a new parser with get-model appended
                    smt_with_model = smt_code
                    if "(get-model)" not in smt_code.lower():
                        smt_with_model = smt_code + "\n(get-model)"

                    # Re-execute with model extraction
                    solver2 = cvc5.Solver()
                    solver2.setOption("tlimit", str(int(timeout * 1000)))  # Apply same timeout
                    solver2.setOption("produce-models", "true")
                    parser2 = cvc5.InputParser(solver2)
                    sm2 = parser2.getSymbolManager()
                    parser2.setStringInput(cvc5.InputLanguage.SMT_LIB_2_6, smt_with_model, "input")

                    while True:
                        cmd = parser2.nextCommand()
                        if cmd.isNull():
                            break
                        result = cmd.invoke(solver2, sm2)
                        result_str = str(result) if result is not None else ""
                        if result_str.strip().startswith("(") and "define-fun" in result_str:
                            model = result_str.strip()
                            break

                except Exception as e:
                    logger.warning(f"Failed to extract model programmatically: {e}")
                    model = "Model available (solver returned sat)"

            # If unsat core wasn't extracted but result is unsat, try to get it
            if check_sat_result == "unsat" and unsat_core is None:
                try:
                    logger.debug("Attempting to extract unsat core programmatically")
                    core = solver.getUnsatCore()
                    if core:
                        core_terms = [str(term) for term in core]
                        unsat_core = "(\n" + "\n".join(core_terms) + "\n)"
                        logger.debug(f"UNSAT core extracted: {len(core_terms)} terms")
                except Exception as e:
                    logger.warning(f"Failed to extract unsat core: {e}")
                    unsat_core = "Unsat core not available"

            # Build raw output
            raw_output = "\n".join(output_lines)

            return {
                "success": True,
                "check_sat_result": check_sat_result,
                "model": model,
                "unsat_core": unsat_core,
                "raw_output": raw_output,
                "error_message": None,
            }

        except Exception as e:
            error_msg = str(e)
            logger.error(f"cvc5 execution error: {error_msg}")

            return {
                "success": False,
                "check_sat_result": "error",
                "model": None,
                "unsat_core": None,
                "raw_output": error_msg,
                "error_message": error_msg,
            }

    def _parse_result(self, result: cvc5.Result) -> str:
        """Parse cvc5 Result object to string.

        Args:
            result: cvc5.Result from checkSat()

        Returns:
            String representation: "sat", "unsat", or "unknown"
        """
        result_str = str(result).lower()

        if "sat" in result_str and "unsat" not in result_str:
            return "sat"
        elif "unsat" in result_str:
            return "unsat"
        else:
            return "unknown"
