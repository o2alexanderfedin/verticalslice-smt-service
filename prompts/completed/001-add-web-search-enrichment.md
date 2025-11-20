<objective>
Add optional web search enrichment capability to the SMT-LIB pipeline service.

When enabled via an API parameter, the service should use Anthropic's web_search tool to enrich input text with domain knowledge, definitions, and clarifications before processing through the existing pipeline.

This enables better SMT-LIB generation for inputs containing domain-specific terminology, ambiguous references, or incomplete context.
</objective>

<context>
This is a FastAPI service that converts informal text to SMT-LIB format through a multi-step pipeline:
1. Formalization (optional)
2. Extraction (to SMT-LIB)
3. Validation (Z3 solver)

Tech stack:
- Python 3.11, FastAPI, Pydantic
- Anthropic SDK for LLM calls
- Async architecture throughout

Examine these files to understand existing patterns:
- `./src/api/routes/pipeline.py` - Current endpoint and request models
- `./src/domain/steps/extraction.py` - Example pipeline step implementation
- `./src/infrastructure/llm/client.py` - Anthropic client usage
- `./src/shared/config.py` - Configuration patterns

Reference Anthropic web_search tool documentation at: https://docs.anthropic.com/en/docs/build-with-claude/tool-use/web-search-tool
</context>

<requirements>
1. **API Changes**:
   - Add `enrich: bool = False` parameter to the `/pipeline/process` endpoint request model
   - Parameter should be optional, defaulting to false for backward compatibility
   - Update response model to include enrichment metadata if performed

2. **Enrichment Step**:
   - Create new step at `./src/domain/steps/enrichment.py` following existing step patterns
   - Use Anthropic's web_search tool to gather relevant context
   - Step should:
     - Analyze input text for terms needing clarification
     - Search for domain definitions, constraints, and background
     - Return enriched text with added context inline or as preamble
   - Track metrics: search_count, enrichment_time, sources_used

3. **Pipeline Integration**:
   - Insert enrichment as first step BEFORE formalization when enabled
   - Update `./src/domain/services/pipeline.py` to conditionally execute enrichment
   - Pass enrichment flag through pipeline context

4. **LLM Client Updates**:
   - Add method to `AnthropicClient` for web search enrichment
   - Use proper tool definition for web_search
   - Handle tool use response parsing

5. **Configuration**:
   - Add enrichment-related settings to config (max_searches, timeout)
   - Allow environment variable override

6. **Type Safety**:
   - Full type annotations throughout
   - Pydantic models for all data structures
   - No use of `Any` type
</requirements>

<implementation>
Follow these patterns from the existing codebase:

1. **Step Pattern** (see extraction.py):
   ```python
   class EnrichmentStep:
       def __init__(self, llm_provider: LLMProvider, config: Settings):
           ...

       async def execute(self, input_text: str) -> EnrichmentResult:
           ...
   ```

2. **LLM Tool Use** - Use Anthropic's tool calling:
   ```python
   response = await client.messages.create(
       model=model,
       messages=[...],
       tools=[{
           "type": "web_search",
           "name": "web_search",
           ...
       }]
   )
   ```

3. **Protocol Extension** - Add to LLMProvider protocol in `./src/domain/protocols.py`

4. **Avoid**:
   - Modifying existing step behavior (enrichment is additive)
   - Breaking backward compatibility (enrich=false must work exactly as before)
   - Blocking calls (use async throughout)
</implementation>

<output>
Create/modify these files:

- `./src/domain/steps/enrichment.py` - New enrichment step implementation
- `./src/api/routes/pipeline.py` - Add enrich parameter to request
- `./src/api/models/pipeline.py` - Update request/response models (if separate)
- `./src/domain/services/pipeline.py` - Integrate enrichment step
- `./src/infrastructure/llm/client.py` - Add web search method
- `./src/domain/protocols.py` - Extend LLMProvider protocol
- `./src/shared/config.py` - Add enrichment configuration
- `./tests/test_enrichment.py` - Unit tests for enrichment step
</output>

<verification>
Before declaring complete:

1. Run type checker: `mypy src/ --strict`
2. Run linters: `ruff check src/ tests/` and `black --check src/ tests/`
3. Run tests: `pytest tests/ -v`
4. Test endpoint manually:
   ```bash
   # Without enrichment (existing behavior)
   curl -X POST http://localhost:8000/pipeline/process \
     -H "Content-Type: application/json" \
     -d '{"informal_text": "x > 5"}'

   # With enrichment
   curl -X POST http://localhost:8000/pipeline/process \
     -H "Content-Type: application/json" \
     -d '{"informal_text": "The Riemann hypothesis states that all non-trivial zeros have real part 1/2", "enrich": true}'
   ```
5. Verify enrichment adds meaningful context without breaking pipeline
</verification>

<success_criteria>
- Endpoint accepts `enrich` parameter (default false)
- When enrich=false, behavior is identical to current
- When enrich=true, web search enriches text before pipeline
- Enrichment metadata included in response
- All type checks pass
- All linters pass
- Tests pass with >80% coverage on new code
- No breaking changes to existing functionality
</success_criteria>
