<objective>
Replace Z3 SMT solver with cvc5 as the primary solver backend for the verticalslice-smt-service.

The service currently uses both Z3Executor (subprocess-based) and PysmtExecutor (pySMT library wrapper) for SMT-LIB code execution. We need to transition to cvc5, which has its own Python bindings and parser, eliminating the need for external dependencies like pySMT.

This change aims to:
- Simplify the solver architecture by using cvc5's native Python API
- Improve parsing reliability with cvc5's built-in SMT-LIB parser
- Maintain API compatibility (no breaking changes to existing endpoints)
- Keep or improve current performance and accuracy
</objective>

<context>
**Current Architecture:**
- Two solver implementations: `Z3Executor` (subprocess) and `PysmtExecutor` (pySMT wrapper)
- Currently using `PysmtExecutor` with Z3 backend in production (see `src/api/dependencies.py:62`)
- Both return dict results conforming to `SMTSolver` protocol (`src/domain/protocols.py:117-139`)
- Used in Step 3 (Validation) of the pipeline (`src/domain/steps/validation.py`)

**Key Files:**
- `src/infrastructure/smt/pysmt_executor.py` - Current pySMT-based executor
- `src/infrastructure/smt/z3_executor.py` - Subprocess-based Z3 executor
- `src/domain/protocols.py` - SMTSolver protocol definition
- `src/api/dependencies.py` - Dependency injection configuration
- `requirements.txt` - Dependencies (currently has `pysmt` and `z3-solver`)

**Project Standards:**
Read `CLAUDE.md` for:
- Type safety requirements (full type annotations, no `Any`)
- Async/await patterns (all I/O must be async)
- Error handling standards
- Testing requirements (unit + integration tests)
- Pre-commit hooks (Black, ruff)
</context>

<requirements>
1. **Install cvc5**: Add `cvc5` to `requirements.txt` and remove `pysmt` and `z3-solver`
2. **Create Cvc5Executor**: New class in `src/infrastructure/smt/cvc5_executor.py` that:
   - Implements the `SMTSolver` protocol from `src/domain/protocols.py`
   - Uses cvc5's Python bindings (not subprocess)
   - Uses cvc5's built-in parser for SMT-LIB code
   - Returns dict with keys: `success`, `check_sat_result`, `model`, `unsat_core`, `raw_output`, `error_message`
   - Handles async execution (use `asyncio.run_in_executor` for CPU-bound parsing/solving)
   - Implements proper timeout handling (default 30.0 seconds)
   - Includes comprehensive error handling and logging
3. **Update Dependency Injection**: Modify `src/api/dependencies.py` to inject `Cvc5Executor` instead of `PysmtExecutor`
4. **Maintain Compatibility**: Ensure `src/domain/steps/validation.py` works without changes (dict return type)
5. **Clean Up**: Mark old executors as deprecated or remove them (your choice based on whether we should keep them)
6. **Update Tests**: Modify relevant tests to work with cvc5
</requirements>

<implementation>
**Study cvc5 API First:**
Research cvc5's Python bindings to understand:
- How to create a solver instance
- How to parse SMT-LIB code (look for parser classes/methods)
- How to execute check-sat and get results
- How to extract models (sat) and unsat cores
- How to handle timeouts and errors

**Implementation Strategy:**
1. Start by reading existing executors to understand the pattern
2. Check cvc5 documentation or examples for parser usage
3. Implement `Cvc5Executor` with full type hints
4. Use thread pool execution for blocking operations (parsing, solving)
5. Match the dict return structure exactly to maintain compatibility
6. Add extensive logging at DEBUG and INFO levels

**Why These Patterns:**
- Thread pool execution prevents blocking the async event loop during CPU-bound SMT solving
- Dict return type (not dataclass) is required for compatibility with `ValidationStep` which uses `isinstance(result, dict)` checks
- Timeout handling is critical - SMT solvers can hang on complex formulas
- Comprehensive error messages help debug when formalization or extraction produces invalid SMT-LIB code

**What to Avoid:**
- Do NOT change the `SMTSolver` protocol interface
- Do NOT use subprocess execution (use native Python bindings)
- Do NOT block the event loop with synchronous calls
- Do NOT use `Any` type hints
- Do NOT skip error handling for parsing or execution failures
</implementation>

<testing>
**Unit Tests:**
Create `tests/unit/test_cvc5_executor.py` with tests for:
- Satisfiable constraints (should return sat + model)
- Unsatisfiable constraints (should return unsat + core)
- Syntax errors (should return error + message)
- Timeout scenarios (should return timeout)
- Various SMT-LIB features (Int, Real, Bool types, assertions)

**Integration Tests:**
Ensure existing integration tests in `tests/integration/` pass:
- `test_domain_steps.py` - ValidationStep tests
- End-to-end pipeline tests

**Manual Testing:**
After implementation, test with the deployed API using the logs pattern from recent deployment:
- Simple constraint: "x must be greater than 5"
- Complex constraint: "Investment Analysis Verification for Miller 694H" (from recent logs)
- Invalid SMT-LIB (test error handling)
</testing>

<output>
Create/modify these files:
- `./src/infrastructure/smt/cvc5_executor.py` - New cvc5-based executor
- `./src/api/dependencies.py` - Update `get_smt_solver()` to return `Cvc5Executor`
- `./requirements.txt` - Replace `pysmt` and `z3-solver` with `cvc5`
- `./tests/unit/test_cvc5_executor.py` - Comprehensive unit tests
- `./src/infrastructure/smt/__init__.py` - Update exports if needed

Optional (your decision):
- Mark `pysmt_executor.py` and `z3_executor.py` as deprecated, or remove them
</output>

<verification>
Before declaring complete, verify:
1. **Type Safety**: Run `mypy src/infrastructure/smt/cvc5_executor.py` (should pass)
2. **Formatting**: Run `black .` and `ruff check .` (should pass)
3. **Unit Tests**: Run `pytest tests/unit/test_cvc5_executor.py -v` (all pass)
4. **Integration Tests**: Run `pytest tests/integration/ -v` (all pass)
5. **Import Check**: Run `python -c "from src.infrastructure.smt.cvc5_executor import Cvc5Executor; print('OK')"` (should succeed)
6. **Protocol Conformance**: Verify `Cvc5Executor` satisfies `SMTSolver` protocol
7. **Async Execution**: Confirm all solver operations use `run_in_executor` to avoid blocking
</verification>

<success_criteria>
- cvc5 is installed and importable
- `Cvc5Executor` class exists and implements `SMTSolver` protocol
- Returns dict with correct structure (matches `ValidationStep` expectations)
- All operations are async (no event loop blocking)
- Timeout handling works correctly
- Error messages are informative
- Unit tests cover sat/unsat/error/timeout cases
- Integration tests pass without modification
- Pre-commit hooks pass (Black, ruff)
- Type checking passes
- Dependency injection updated to use `Cvc5Executor`
</success_criteria>

<research>
If you need to understand cvc5's API:
- Check if there's a `cvc5` package on PyPI with documentation
- Look for parser classes (e.g., `InputParser`, `SmtLibParser`, or similar)
- Find solver classes and their methods
- Understand how to set timeouts
- Learn how to extract models and unsat cores

Use web search or examine the cvc5 Python package after installation to understand the API.
</research>
