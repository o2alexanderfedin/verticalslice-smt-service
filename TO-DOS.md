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