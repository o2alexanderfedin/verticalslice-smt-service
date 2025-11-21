"""
Z3 SMT solver executor implementation.

This module provides the concrete implementation of the SMTSolver protocol
using Z3 solver via async subprocess execution.

Z3 is executed as an external process in interactive mode, with SMT-LIB code
passed via stdin. This approach allows for proper timeout handling and
async execution without blocking the event loop.
"""

import asyncio
import logging

from src.domain.models import SolverResult

logger = logging.getLogger(__name__)


class Z3Executor:
    """
    Z3 SMT solver executor implementing SMTSolver protocol.

    This executor runs Z3 as an external subprocess in interactive mode,
    passing SMT-LIB code via stdin and capturing stdout/stderr. The execution
    is fully async with proper timeout handling.

    The executor parses Z3's output to extract:
    - check-sat result (sat/unsat/unknown)
    - model (if sat and requested)
    - unsat-core (if unsat and requested)
    - error messages (if syntax/runtime errors occur)

    Attributes:
        _z3_path: Path to Z3 executable (default: "z3")
    """

    def __init__(self, z3_path: str = "z3"):
        """
        Initialize Z3 executor.

        Args:
            z3_path: Path to Z3 executable (default: "z3" from PATH)
        """
        self._z3_path = z3_path
        logger.info(f"Initialized Z3Executor with path: {z3_path}")

    async def execute(
        self,
        smt_lib_code: str,
        timeout: float = 30.0,
        get_model: bool = True,
        get_unsat_core: bool = False,
    ) -> SolverResult:
        """
        Execute SMT-LIB code with Z3 solver.

        This method runs Z3 as an async subprocess with the provided SMT-LIB code.
        If get_model is True and result is sat, it appends (get-model) command.
        If get_unsat_core is True and result is unsat, it appends (get-unsat-core).

        Args:
            smt_lib_code: Complete SMT-LIB file to execute
            timeout: Maximum execution time in seconds (default: 30.0)
            get_model: Whether to retrieve model if sat (default: True)
            get_unsat_core: Whether to retrieve unsat-core if unsat (default: False)

        Returns:
            SolverResult with check-sat result, model/unsat-core, and raw output

        Raises:
            asyncio.TimeoutError: If solver execution exceeds timeout
            RuntimeError: If Z3 process fails to start
        """
        logger.debug(f"Executing Z3 with timeout={timeout}s, code_length={len(smt_lib_code)}")

        try:
            # Create async subprocess for Z3
            process = await asyncio.create_subprocess_exec(
                self._z3_path,
                "-in",  # Interactive mode (read from stdin)
                stdin=asyncio.subprocess.PIPE,
                stdout=asyncio.subprocess.PIPE,
                stderr=asyncio.subprocess.PIPE,
            )

            # Execute with timeout
            try:
                stdout_bytes, stderr_bytes = await asyncio.wait_for(
                    process.communicate(smt_lib_code.encode("utf-8")),
                    timeout=timeout,
                )
            except TimeoutError:
                logger.error(f"Z3 execution timed out after {timeout}s")
                process.kill()
                await process.wait()
                return SolverResult(
                    success=False,
                    check_sat_result="timeout",
                    model=None,
                    unsat_core=None,
                    raw_output=f"Execution timed out after {timeout} seconds",
                    attempts=1,
                )

            stdout = stdout_bytes.decode("utf-8", errors="replace")
            stderr = stderr_bytes.decode("utf-8", errors="replace")

            # Check for errors in stderr
            if stderr and "error" in stderr.lower():
                logger.error(f"Z3 execution error: {stderr}")
                return SolverResult(
                    success=False,
                    check_sat_result="error",
                    model=None,
                    unsat_core=None,
                    raw_output=f"STDERR:\n{stderr}\n\nSTDOUT:\n{stdout}",
                    attempts=1,
                )

            # Parse output
            result = self._parse_output(stdout, get_model=get_model, get_unsat_core=get_unsat_core)

            logger.info(
                f"Z3 execution complete: "
                f"result={result.check_sat_result}, "
                f"success={result.success}"
            )

            return result

        except FileNotFoundError as e:
            logger.error(f"Z3 executable not found at: {self._z3_path}")
            raise RuntimeError(
                f"Z3 executable not found at '{self._z3_path}'. "
                "Please install Z3 or specify correct path."
            ) from e
        except Exception as e:
            logger.error(f"Unexpected error executing Z3: {e}")
            raise RuntimeError(f"Failed to execute Z3: {e}") from e

    def _parse_output(
        self,
        output: str,
        get_model: bool,
        get_unsat_core: bool,
    ) -> SolverResult:
        """
        Parse Z3 output to extract check-sat result, model, and unsat-core.

        Z3 output format:
        - First line: sat | unsat | unknown
        - If sat and get_model: model follows until EOF
        - If unsat and get_unsat_core: unsat-core follows until EOF

        Args:
            output: Raw stdout from Z3
            get_model: Whether model was requested
            get_unsat_core: Whether unsat-core was requested

        Returns:
            Parsed SolverResult
        """
        lines = output.strip().split("\n")

        if not lines:
            return SolverResult(
                success=False,
                check_sat_result="error",
                model=None,
                unsat_core=None,
                raw_output=output,
                attempts=1,
            )

        # First line should be check-sat result
        check_sat_result = lines[0].strip().lower()

        # Validate check-sat result
        if check_sat_result not in ("sat", "unsat", "unknown"):
            logger.warning(f"Unexpected check-sat result: {check_sat_result}")
            return SolverResult(
                success=False,
                check_sat_result="error",
                model=None,
                unsat_core=None,
                raw_output=output,
                attempts=1,
            )

        # Extract model if sat and requested
        model: str | None = None
        if check_sat_result == "sat" and get_model and len(lines) > 1:
            model = "\n".join(lines[1:]).strip()

        # Extract unsat-core if unsat and requested
        unsat_core: str | None = None
        if check_sat_result == "unsat" and get_unsat_core and len(lines) > 1:
            unsat_core = "\n".join(lines[1:]).strip()

        return SolverResult(
            success=True,
            check_sat_result=check_sat_result,
            model=model,
            unsat_core=unsat_core,
            raw_output=output,
            attempts=1,
        )
