<objective>
Thoroughly investigate the CI/CD smoke test timing issue from v1.14.2 deployment and verify production health.

This investigation will help us understand:
- Whether the smoke test failure was a genuine bug or a race condition
- Exact timing of application startup vs. smoke test execution
- Current production deployment status and API health
- Whether the enriched_text field is working correctly in production

The findings will inform decisions about improving smoke test reliability and deployment verification processes.
</objective>

<context>
**Deployment Context:**
- Version: v1.14.2
- Deployment Date: 2025-11-26 02:32 UTC
- Issue: Smoke test "Simple Pipeline Processing" failed with HTTP 500
- Status: Application is currently running in production
- Change: Added enriched_text field to API responses

**Known Information:**
- Smoke test failed at 02:32:03-04 UTC with HTTP 500
- Production logs show successful requests starting at 02:32:08 UTC
- Suspected timing issue: smoke test ran before app fully initialized
- Production URL: https://verticalslice-smt-service-qgkkc.ondigitalocean.app
- Digital Ocean App ID: d3ad0b2f-300b-4147-81fc-b876820ee3b9

**Files to Examine:**
- `.github/workflows/deploy.yml` - Deployment workflow and smoke test timing
- `.github/scripts/smoke-tests.sh` - Smoke test implementation
- Production logs via `doctl apps logs`
- GitHub Actions logs via `gh run view`
</context>

<investigation_requirements>
This is a deep analysis task requiring methodical investigation and evidence gathering. Thoroughly analyze each aspect before drawing conclusions.

**Phase 1: Timing Analysis**

1. **Extract Exact Timestamps:**
   - Get the GitHub Actions workflow run ID for v1.14.2 deployment
   - Extract exact timestamps for:
     - When deployment completed
     - When smoke tests started
     - When first smoke test executed
     - When smoke test failed
   - Get production application logs for the same time window
   - Identify when first successful request was processed

2. **Calculate Critical Intervals:**
   - Time from deployment completion to smoke test execution
   - Time from smoke test to first successful production request
   - Application initialization time (estimate from logs)
   - Gap between smoke test and readiness

3. **Identify Initialization Bottlenecks:**
   - Review application startup logs
   - Identify slow initialization steps (model loading, dependencies, etc.)
   - Measure time to first health check success

**Phase 2: Production Health Verification**

1. **API Health Check:**
   - Test production /health endpoint
   - Verify response structure and status
   - Check uptime and recent error rates

2. **Feature Verification (enriched_text field):**
   - Send test request to /pipeline/process with `enrich=false`
   - Verify `enriched_text` field is present and equals `informal_text`
   - Send test request with `enrich=true` (if time permits)
   - Verify `enriched_text` field contains enriched content
   - Confirm field is properly populated in both scenarios

3. **Error Log Analysis:**
   - Check production logs for any errors since deployment
   - Identify any recurring issues or warnings
   - Verify no 500 errors in recent production traffic

**Phase 3: Root Cause Determination**

Consider multiple explanations and evaluate evidence:
- **Hypothesis A**: Race condition - smoke test ran before initialization completed
- **Hypothesis B**: Transient deployment issue - temporary infrastructure problem
- **Hypothesis C**: Code bug - real application error that resolved itself
- **Hypothesis D**: External dependency - network, database, or API unavailability

For each hypothesis, identify supporting and contradicting evidence from logs.
</investigation_requirements>

<tools_and_commands>
**GitHub Actions Investigation:**
```bash
# Get recent workflow runs
gh run list --workflow=deploy.yml --limit=5

# Get detailed logs for specific run
gh run view <run-id> --log

# Extract smoke test section
gh run view <run-id> --log | grep -A 30 "Smoke Tests"
```

**Production Logs:**
```bash
# Get recent production logs
doctl apps logs d3ad0b2f-300b-4147-81fc-b876820ee3b9 --type run --tail 100

# Get logs around deployment time
doctl apps logs d3ad0b2f-300b-4147-81fc-b876820ee3b9 --type run --tail 500 | grep "2025-11-26 02:32"

# Search for errors
doctl apps logs d3ad0b2f-300b-4147-81fc-b876820ee3b9 --type run --tail 200 | grep -i error
```

**Production API Testing:**
```bash
# Health check
curl -s https://verticalslice-smt-service-qgkkc.ondigitalocean.app/health | jq

# Test enriched_text field (enrich=false)
curl -s -X POST https://verticalslice-smt-service-qgkkc.ondigitalocean.app/pipeline/process \
  -H 'Content-Type: application/json' \
  -d '{"informal_text": "x > 5"}' | jq '.enriched_text'

# Verify field equals informal_text when enrich=false
curl -s -X POST https://verticalslice-smt-service-qgkkc.ondigitalocean.app/pipeline/process \
  -H 'Content-Type: application/json' \
  -d '{"informal_text": "test input"}' | jq '{informal_text, enriched_text, enrichment_performed}'
```

For maximum efficiency, whenever you need to perform multiple independent operations, invoke all relevant tools simultaneously rather than sequentially.
</tools_and_commands>

<output_format>
Create two deliverables:

**1. Markdown Report: `./investigations/v1.14.2-deployment-timing.md`**

Structure:
```markdown
# V1.14.2 Deployment Investigation

## Executive Summary
[One paragraph: What happened, root cause, current status]

## Timeline Analysis
### Deployment Events
| Time (UTC) | Event | Source |
|------------|-------|--------|
| ... | ... | ... |

### Critical Intervals
- Deployment completion → Smoke test execution: X seconds
- Smoke test failure → First successful request: Y seconds
- Estimated initialization time: Z seconds

## Findings

### 1. Timing Analysis
[Detailed breakdown with evidence from logs]

### 2. Production Health Status
[Current API health, enriched_text verification results]

### 3. Root Cause Determination
[Which hypothesis is supported by evidence and why]

## Evidence
### GitHub Actions Logs
```
[Relevant excerpts]
```

### Production Logs
```
[Relevant excerpts]
```

### API Test Results
```json
[Test response examples]
```

## Conclusions
1. [Key finding 1]
2. [Key finding 2]
3. [Key finding 3]

## Recommendations
1. [Specific actionable recommendation]
2. [Specific actionable recommendation]
3. [Specific actionable recommendation]
```

**2. JSON Data File: `./investigations/v1.14.2-deployment-data.json`**

Structure:
```json
{
  "investigation_date": "2025-11-26T...",
  "deployment_version": "v1.14.2",
  "timing": {
    "deployment_completed_utc": "...",
    "smoke_test_started_utc": "...",
    "smoke_test_failed_utc": "...",
    "first_success_utc": "...",
    "intervals": {
      "deployment_to_smoke_test_seconds": 0,
      "smoke_test_to_success_seconds": 0,
      "estimated_initialization_seconds": 0
    }
  },
  "production_health": {
    "health_endpoint_status": 200,
    "recent_errors_count": 0,
    "enriched_text_field_working": true,
    "test_results": {
      "enrich_false": {...},
      "enrich_true": {...}
    }
  },
  "root_cause": {
    "hypothesis": "...",
    "confidence": "high|medium|low",
    "supporting_evidence": [...],
    "contradicting_evidence": [...]
  },
  "recommendations": [...]
}
```
</output_format>

<verification>
Before completing, verify:

**Data Quality:**
- [ ] All timestamps are in UTC and formatted consistently
- [ ] All time intervals are calculated correctly
- [ ] Log excerpts include context (timestamps, log levels, messages)
- [ ] API test results show both success and error cases (if applicable)

**Analysis Completeness:**
- [ ] Both timing analysis AND production health verification completed
- [ ] Root cause hypothesis is supported by specific evidence
- [ ] Contradicting evidence is acknowledged and explained
- [ ] All three recommendations are specific and actionable

**Output Validation:**
- [ ] Markdown report exists at `./investigations/v1.14.2-deployment-timing.md`
- [ ] JSON data file exists at `./investigations/v1.14.2-deployment-data.json`
- [ ] JSON is valid and parseable
- [ ] Report includes all required sections

**Production Safety:**
- [ ] No sensitive data (API keys, tokens) in outputs
- [ ] Test requests are read-only (GET/POST to /process, not destructive)
- [ ] No impact on production users
</verification>

<success_criteria>
1. **Precise Timing Data**: Exact timestamps extracted with second-level precision
2. **Root Cause Identified**: Clear determination of which hypothesis is correct with supporting evidence
3. **Production Verified**: Current v1.14.2 deployment confirmed healthy with enriched_text working
4. **Actionable Recommendations**: At least 3 specific improvements to prevent future timing issues
5. **Complete Documentation**: Both markdown report and JSON data file created with all sections filled
</success_criteria>
