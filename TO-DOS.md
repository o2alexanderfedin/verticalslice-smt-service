# TO-DOS

## ✅ COMPLETED: Install pySMT Dependencies and Fix Integration - 2025-11-18 23:15

- **DONE: Installed pySMT and Z3 solver, fixed executor and validation step** - Complete pySMT integration with multiple bug fixes. **Implementation:** (1) Added `pysmt>=0.9.5` and `z3-solver==4.13.0.0` to requirements.txt and installed both packages. (2) Fixed `PysmtExecutor.execute()` at line 107 - removed invalid `logic="ALL"` parameter causing "error: ALL" failures, now letting pySMT auto-detect logic from formula. (3) Added `_strip_markdown_fences()` helper to `validation.py` that removes ```smt-lib...``` and ```...``` code fences from LLM-generated code. (4) Applied fence stripping to initial SMT code and all LLM-fixed code. (5) Fixed `PipelineMetrics.formalization_attempts` validation from `ge=1` to `ge=0` to allow skip cases. **Verification:** Full pipeline now works end-to-end for "x > 5" input: formalization skipped (0 attempts, 0s), extraction succeeds (1 attempt, 9.8s, degradation=0.74), validation executes (1 attempt, 0.15s, result=sat, model: x := 6). Total time ~10s. All prior optimizations working: skip thresholds, temperature=0.0, conversation refinement, markdown handling.

## ✅ COMPLETED: Fix Extraction Skip Logic - Accept First Attempt - 2025-11-18 22:58

- **DONE: Fixed skip_retries logic to accept first attempt regardless of degradation** - Bug where extraction logged "Will accept first extraction attempt" but still failed when degradation > threshold. **Problem from logs:** For input "x > 5" (5 chars), code set max_attempts=1 but threshold check at line 148 still returned error when degradation=0.7667 > max=0.05. **Root cause:** Threshold check didn't bypass quality verification when skip_retries=True, defeating the optimization's purpose. **Fix:** Changed condition from `if degradation <= self.max_degradation:` to `if degradation <= self.max_degradation or skip_retries:` at line 148. Added conditional logging to distinguish skip acceptance from threshold-based success. Updated error messages to use max_attempts instead of self.max_retries. **Behavior now:** Short texts (< 50 chars) make 1 LLM call, compute degradation for metrics, then accept result WITHOUT quality check regardless of score.

## ✅ COMPLETED: Skip Extraction Refinement for Short Formal Texts - 2025-11-18 22:48

- **DONE: Added fast-path for short formal texts to skip extraction retries** - Short, simple formal texts now skip the retry loop for performance. **Implementation:** Added `extraction_skip_retries_threshold` config (`src/shared/config.py:116-121`, default 50 chars). Updated `ExtractionStep.__init__` to accept skip_retries_threshold parameter. Added skip logic in execute method (`src/domain/steps/extraction.py:86-97`) that checks formal_text length and sets max_attempts=1 if below threshold. Updated retry loop to use max_attempts and log skip_retries status. Pipeline service passes config to ExtractionStep. **Benefits:** Saves API calls for simple inputs (1 attempt vs up to 5), reduces latency, still computes degradation for metrics. **Example:** "x > 5" (5 chars) skips retries, but "The variable x must be greater than 5 and less than 10" (50+ chars) uses full refinement.

## ✅ COMPLETED: Enforce Zero Temperature for Extraction - 2025-11-18 22:19

- **DONE: Verified and documented extraction temperature stays at 0.0** - Confirmed extraction uses deterministic temperature (0.0) for all attempts with no variations. **Verification:** (1) Temperature hardcoded to 0.0 in `src/infrastructure/llm/client.py:238`, (2) No extraction temperature settings exist in `src/shared/config.py`, (3) Retry loop in `src/domain/steps/extraction.py` does not pass temperature parameter - only detail_level varies. **Documentation added:** Added CRITICAL warning in extract_to_smtlib docstring emphasizing temperature is non-configurable by design, expanded inline comment to 3-line warning at temperature=0.0 assignment, added NOTE in retry loop documenting temperature stays constant across all attempts. **Rationale:** Unlike formalization, extraction must be deterministic to ensure consistent, reproducible SMT-LIB output.

## ✅ COMPLETED: Fix Extraction Refinement Prompt - Allow Logic Changes - 2025-11-18 22:33

- **DONE: Removed misleading constraint from extraction refinement prompt** - Removed "Keep the same SMT-LIB logic" from refinement prompt which could prevent fixing incorrect or incomplete logic. **Implementation:** Rewrote refinement prompt in `src/infrastructure/llm/client.py:215-230` to explicitly allow and encourage logic changes. New prompt includes 6-step checklist: (1) review if logic captures ALL constraints, (2) check for missing constraints, (3) verify variable declarations, (4) fix logical errors, (5) add detailed comments, (6) include variable context. Emphasizes that LLM should change logic AND/OR annotations as needed. **Rationale:** Degradation measures embedding similarity - if logic is wrong, comments won't fix it. Previous prompt was counterproductive by restricting changes to annotations only.

## ✅ COMPLETED: Conversation-Based Refinement for Extraction - 2025-11-18 22:25

- **DONE: Implemented refinement logic for extraction retries** - Extraction now uses conversation-based refinement matching formalization pattern. **Implementation:** Added previous_attempt and previous_degradation parameters to LLMProvider.extract_to_smtlib protocol (`src/domain/protocols.py:56-77`). Updated AnthropicClient.extract_to_smtlib (`src/infrastructure/llm/client.py:162-248`) to build 3-message conversation on retry: initial prompt → previous SMT code → refinement feedback with degradation score and guidance. Updated extraction.py retry loop (`src/domain/steps/extraction.py:85-138`) to track and pass previous attempts. Temperature stays 0.0 for deterministic code generation. **Benefits:** Better convergence through iterative refinement vs simple regeneration, maintains context across retries, explicit feedback guides LLM to reduce information loss.

## ✅ COMPLETED: Use Exact 5-Phase SMT Prompt - 2025-11-18 22:12

- **DONE: Replaced EXTRACTION_PROMPT with exact 5-phase prompt** - The exact battle-tested 5-phase prompt from convert_to_smtlib function has been implemented verbatim in `src/infrastructure/llm/prompts.py:18-98`. The prompt enforces: Phase 1 (problem comprehension with data inventory), Phase 2 (domain modeling with ground truth vs unknowns, assert-and-test pattern for YES/NO), Phase 3 (logic selection decision tree), Phase 4 (SMT-LIB encoding with uninterpreted function linking constraints), Phase 5 (self-verification checklist). Only change made: replaced `{enhanced_text}` placeholder with `{formal_text}` to match our variable naming. Function `get_extraction_prompt()` updated to use new prompt (detail_level parameter deprecated but kept for API compatibility).

## Investigate Pipeline Test Failure and Add CI/CD Smoke Test - 2025-11-19 13:09

- **Investigate pipeline failure for "2*2=5" test** - Simple POST request to /pipeline/process fails. **Problem:** Test curl command to production endpoint returns error - need to check logs and identify root cause (could be LLM response parsing, SMT solver execution, or extraction failure). **Files:** `src/api/routes/pipeline.py`, `src/domain/steps/extraction.py`, `src/domain/steps/validation.py`, `src/infrastructure/smt/z3_executor.py`. **Test command:**
  ```bash
  curl -X 'POST' \
    'https://verticalslice-smt-service-d5hf3.ondigitalocean.app/pipeline/process' \
    -H 'accept: application/json' \
    -H 'Content-Type: application/json' \
    -d '{"informal_text": "2*2=5"}'
  ```

- **Add smoke test to CI/CD workflow** - Create basic POST test in GitHub Actions verification step. **Problem:** No production endpoint testing after deployment - only health check exists. **Files:** `.github/workflows/deploy.yml:274-295`, `.github/scripts/smoke-tests.sh` (may need creation/update). **Solution:** Add curl POST test with sample input to smoke-tests.sh, verify response contains expected fields (check_sat_result, solver_success), fail deployment if smoke test fails.

## Fix GitHub Actions Runner Disk Space Exhaustion - 2025-11-19 16:14

- **Free disk space before Docker build in CI/CD** - GitHub Actions runner exhausts disk space during workflow execution. **Problem:** Runner reports "No space left on device" for worker logs at `/home/runner/actions-runner/cached/_diag/Worker_*.log`. The v1.8.3 workflow failed with `System.IO.IOException: No space left on device` even after CPU-only PyTorch fix. Issue affects runner diagnostics, not pip install. **Files:** `.github/workflows/deploy.yml` (Build Application job). **Solution:** Add step to free disk space before Docker build: remove unused toolchains (Android SDK, .NET, Haskell), clear Docker cache, remove large pre-installed packages. Example:
  ```yaml
  - name: Free disk space
    run: |
      sudo rm -rf /usr/share/dotnet
      sudo rm -rf /opt/ghc
      sudo rm -rf /usr/local/share/boost
      sudo rm -rf "$AGENT_TOOLSDIRECTORY"
      docker system prune -af
      df -h
  ```

## Verify NVIDIA GPU Libraries Not Installed - 2025-11-19 17:47

- **Verify CPU-only PyTorch fix prevents NVIDIA downloads** - Confirm the CI/CD workflow no longer downloads nvidia_cublas_cu12, nvidia_cudnn_cu12, etc. **Problem:** Despite adding CPU-only PyTorch index to workflow, NVIDIA CUDA libraries may still be downloaded via sentence-transformers or other dependencies. The fix in commit c78c633 needs verification. **Files:** `.github/workflows/deploy.yml:42-44,91-93,148-150`, `requirements.txt:23-24`. **Solution:** Check v1.8.7 workflow logs for NVIDIA package downloads. If still present, investigate sentence-transformers dependencies or add explicit exclusion. May need to pin torch version or use `--no-deps` for sentence-transformers.

## Verify v1.8.8 CLAUDE_CODE_OAUTH_TOKEN Fix Deployment - 2025-11-20 13:09

- **Set CLAUDE_CODE_OAUTH_TOKEN secret in DO and verify deployment** - v1.8.8 switches from ANTHROPIC_API_KEY to CLAUDE_CODE_OAUTH_TOKEN. **Problem:** All deployments since v1.8.5 failed with DeployContainerExitNonZero because container crashed during startup validation. Investigation revealed: (1) startup validation at `src/main.py:219-221` checked for "sk-" prefix, (2) ANTHROPIC_API_KEY secret in DO may have been empty/corrupted. **Files:** `src/shared/config.py:23-27` (added validation_alias), `src/main.py:219-221` (removed sk- check), `app.yaml:39` (changed to CLAUDE_CODE_OAUTH_TOKEN). **Solution:** In DO App Platform console, set `CLAUDE_CODE_OAUTH_TOKEN` secret with value `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`, then verify v1.8.8 deployment succeeds.

## Setup Git Hook for Formatting - 2025-11-20 15:04

- **Create pre-commit hook for code formatting** - Automatically run black and ruff before commits. **Problem:** Quality checks failing in CI/CD because code is not formatted before commits, wasting CI resources and time. **Files:** `.git/hooks/pre-commit` (new), `.pre-commit-config.yaml` (optional). **Solution:** Create pre-commit hook that runs `black --check` and `ruff check`, or use pre-commit framework with existing black and ruff config.

## Increase Skip Thresholds to 200 Characters - 2025-11-20 14:31

- **Update formalization and extraction skip thresholds to 200 chars** - Increase minimum text length thresholds for skipping formalization and extraction retries. **Problem:** Current thresholds are too low (formalization: 20 chars, extraction: 50 chars), causing the pipeline to skip quality checks for texts that are still too short to benefit from refinement. **Files:** `src/shared/config.py:48-53` (formalization_skip_threshold), `src/shared/config.py:88-93` (extraction_skip_retries_threshold). **Solution:** Change both default values to 200 characters to ensure only truly trivial inputs skip the refinement loops.

## Add Layer-to-Layer Integration Tests - 2025-11-20 19:57

- **Create integration tests for service layer boundaries** - Add tests verifying interactions between adjacent layers without full deployment. **Problem:** Currently debugging requires deploying to Digital Ocean (~15 min per iteration), which is slow and expensive. Local layer-to-layer tests would catch integration issues much faster. **Files:** `tests/integration/` (new directory), `src/domain/steps/formalization.py`, `src/domain/steps/extraction.py`, `src/infrastructure/llm/client.py`, `src/domain/protocols.py`. **Solution:** Create tests for:
  - FormalizationStep → LLMProvider protocol
  - ExtractionStep → LLMProvider protocol
  - AnthropicClient → AsyncAnthropic SDK
  - ValidationStep → SMTExecutor protocol
  - PipelineService → all step dependencies

  Use real API calls for LLM tests (with short inputs to minimize cost), mock SMT solver where appropriate.

## Fix All Failing Integration Tests - 2025-11-20 21:01

- **Fix all failing integration tests** - Multiple integration tests are failing and must be fixed immediately. **Problem:** Tests in `tests/integration/` are failing - tests were just created but have issues that prevent them from running successfully. These tests use real API calls and must work to validate layer-to-layer boundaries locally instead of costly DO deployments. **Files:** `tests/integration/test_anthropic_client.py`, `tests/integration/test_domain_steps.py`. **Solution:** Run tests locally with `python3 -m pytest tests/integration/ -v`, identify each failure, and fix the root causes. Priority is making all 15 tests pass. No excuses.

## Fix Post-Deployment Verification Tests - 2025-11-21 01:31

- **Remove /pipeline/examples endpoint and fix verification test expectations** - Post-deployment verification tests fail due to test/API mismatches. **Problem:** After v1.8.36 deployment (ValidationStep dict fix), core pipeline works but verification tests fail: (1) `/pipeline/examples` returns 500 - endpoint should be removed or fixed, (2) Tests expect `requires_manual_review` field not in API response, (3) Health check expects `model` field not in response, (4) Root `/` returns 307 redirect instead of expected 200. **Files:** `.github/scripts/integration-tests.sh`, `.github/scripts/smoke-tests.sh`, `src/api/routes/pipeline.py` (for examples endpoint). **Solution:** Either remove examples endpoint or fix it, update test scripts to match actual API response fields, fix redirect behavior test expectation.

## ✅ COMPLETED: Monitor v1.9.0 cvc5 Deployment and Fix Template Sync - 2025-11-24 16:36

- **DONE: v1.9.0 cvc5 migration deployed successfully** - v1.9.0 release pushed with cvc5 migration completed successfully. **Implementation:** Replaced pysmt/z3-solver with cvc5>=1.1.2 in requirements.txt, implemented Cvc5Executor in `src/infrastructure/smt/cvc5_executor.py`, updated configuration. **Verification:** DigitalOcean autodeploy succeeded, cvc5 installation completed without issues, API tested with sample SMT constraints working correctly.

## ✅ COMPLETED: Skip Integration Tests in CI/CD to Reduce API Costs - 2025-11-25 03:46

- **DONE: Modified GitHub Actions workflow to skip integration tests** - Integration tests making expensive Anthropic API calls are now skipped in CI/CD to reduce costs. **Problem:** Integration tests were making 10-11 real Anthropic API calls (totaling ~15-25 seconds for slowest test), causing high API costs and 20+ minute test phases. **Investigation:** Identified 15 integration tests: 6 in `test_anthropic_client.py` and 9 in `test_domain_steps.py`. The `test_full_pipeline_simple_constraint` test makes 4-7 sequential LLM calls (slowest). **Solution:** Modified `.github/workflows/deploy.yml:102` to add `--ignore=tests/integration/` flag to pytest command. **Benefits:** (1) Saves money by avoiding 10-11 API calls per CI/CD run, (2) Reduces test phase from 20+ minutes to <5 minutes, (3) Integration tests remain available for local development. **Committed:** f7c53f1 - "chore: skip integration tests in CI/CD to reduce API costs". **Next deployments:** Will use new workflow without integration tests.

## Monitor v1.10.0 License & Proof Enhancement Deployment - 2025-11-25 03:10

- **Monitor v1.10.0 deployment with license change and proof field** - v1.10.0 release deployed with BREAKING license change and new proof field feature. **Status:** CI/CD workflow 19656901416 currently at "Run Tests" phase installing Python dependencies. Code Quality Checks passed (1m 3s). Background monitor active (process f20729). **Files:** `LICENSE` (CC BY-NC-ND 4.0), `src/api/models.py` (proof field), `src/domain/models.py` (proof_raw_output, proof_summary), `src/main.py` (license metadata), README.md (license badge). **Changes:** (1) License: MIT → CC BY-NC-ND 4.0, (2) Proof field: Added to ProcessResponse with raw_output and summary, (3) Documentation: Abstracted technical terminology, added Mermaid diagrams, renamed service to "Intelligent Formal Verification Service". **Next:** Verify deployment completes, check DO deployment at https://cloud.digitalocean.com/apps/d3ad0b2f-300b-4147-81fc-b876820ee3b9, test API includes proof field in responses. **Note:** This deployment still uses old workflow with integration tests - new workflow (skipping integration tests) will apply to future deployments.

## ✅ COMPLETED: Implement File-Based Caching for SMT Pipeline - 2025-11-26 02:24

- **DONE: Archive completed caching research prompt** - Moved research prompt to completed directory with timestamp. **Implementation:** Renamed `prompts/001-research-python-caching-libs.md` to `prompts/completed/001-research-python-caching-libs-20251126.md`.

- **DONE: Implement async file-based cache for pipeline** - Built custom AsyncFileCache with all required features. **Implementation:** Created AsyncFileCache in `src/infrastructure/cache/async_file_cache.py` with aiofiles, fcntl locking, LRU eviction. Integrated with enrichment and extraction steps. Added 18 comprehensive unit tests with 100% pass rate. **Performance:** ~25,000x speedup on cache hits (10ms vs 250s). Released as v1.16.2.

## ✅ COMPLETED: Verify Cache Only Stores Successful API Responses - 2025-11-26 14:19

- **DONE: Verified cache safety against error responses** - Comprehensive investigation confirmed cache is structurally safe from caching HTTP errors. **Investigation:** (1) Verified Anthropic SDK exception hierarchy - all errors (500, 504, 429, timeouts, connection failures) inherit from `anthropic.APIError`, (2) Analyzed exception flow - retry decorator catches exceptions, LLM client re-raises them, domain steps catch and return Err(), (3) Verified cache writes are unreachable when exceptions occur due to control flow, (4) Created 9 comprehensive unit tests (all passing) proving exceptions prevent caching. **Documentation:** Created `docs/cache-safety-verification.md` with full analysis. Added safety comments to cache write locations in `src/domain/steps/enrichment.py:108-111` and `src/domain/steps/extraction.py:180-183,219-221`. **Test Coverage:** `tests/unit/domain/test_enrichment_step.py` tests HTTP 500, 504, 429, connection errors, timeouts - all prevent caching as designed. **Conclusion:** No code changes needed - current implementation has strong structural safety guarantees. HTTP 504 production incident did NOT cache bad data.

## Test Context-Rich Diagnostics Locally - 2025-11-27 00:48

- **Test context-rich SMT validation diagnostics with failing example** - Verify the enhanced error diagnostics work correctly with the stainless steel example that prompted this feature. **Problem:** Need to verify that the implementation provides rich diagnostics (parsed error location, code context, attempt history) when validation fails. Original failing case: `{"informal_text": "Stainless steel rod with the length of 100' expands less than by 15\" at the temperature 500 Celcius", "enrich": false}` returned HTTP 422 with error "Expected a RPAREN_TOK, got `at` (SYMBOL)" without sufficient context. **Files:** `src/shared/smt_diagnostics.py` (error parsing), `src/infrastructure/llm/client.py:333-432` (context-rich fixing), `src/domain/steps/validation.py:67-235` (validation with history tracking), `src/api/routes/pipeline.py:232-302` (diagnostic response building), `src/api/models.py:306-451` (diagnostic models). **Solution:** Run local test with failing stainless steel example, verify API returns ValidationDiagnostics with error_location (line/column), context_before/after, attempt_history, and that context-rich fixes are being used during validation retries.

## Ensure Test Coverage for Diagnostics - 2025-11-27 01:08

- **Create unit tests for SMT diagnostics components** - Add comprehensive test coverage for the new context-rich diagnostics feature using mocks. **Problem:** The diagnostics feature (commit 90ff2d9) has no unit tests yet. Components need testing: error parsing (`parse_cvc5_error`), context extraction (`extract_error_context`), XML formatting (`get_error_summary_xml`, `get_previous_fixes_summary_xml`), ValidationStep with context-rich fixes, API error response building. Local testing showed both examples succeeded validation, so diagnostic code paths weren't exercised. **Files:** `tests/unit/shared/test_smt_diagnostics.py` (new), `tests/unit/domain/test_validation_step.py` (new or extend existing), `tests/unit/api/test_pipeline_routes.py` (new or extend existing). **Solution:** Create unit tests with mocked dependencies: (1) Test `parse_cvc5_error()` with various error message formats, (2) Test `extract_error_context()` with different line numbers and edge cases, (3) Test XML formatting methods produce valid XML, (4) Test ValidationStep tracks attempt history correctly with mocked LLM/solver, (5) Test API route builds diagnostics from ValidationError with mocked pipeline service. Use mocks extensively to avoid API calls and isolate components.
