<objective>
Refine API documentation to further abstract technical implementation details, update licensing to restrictive CC BY-NC-ND, add a simple Mermaid flow diagram, and include proof verification output in API responses.

This improves professional presentation, protects intellectual property with restrictive licensing, provides visual understanding through diagrams, and enhances verification transparency by exposing proof data.
</objective>

<context>
**Current State:**
- FastAPI service with Swagger UI documentation in `src/main.py` and `src/api/routes/pipeline.py`
- API response models in `src/api/models.py` (ProcessResponse)
- MIT License in `LICENSE` file and referenced in `src/main.py`
- Documentation uses "Semantic-Preserving SMT-LIB Pipeline" which reveals too much implementation detail
- "How It Works" section uses text descriptions instead of visual diagrams
- No proof/verification output included in API responses

**Project Standards:**
Read `CLAUDE.md` for type safety, async patterns, error handling, and testing requirements.

**Why This Matters:**
- Professional API presentation suitable for commercial licensing
- Visual diagrams improve user comprehension
- Proof data enables external verification and auditing
- Restrictive license protects proprietary implementation
</context>

<requirements>
1. **Remove revealing terminology from documentation:**
   - Change "Semantic-Preserving SMT-LIB Pipeline" to generic business-friendly description
   - Avoid technical terms like "SMT", "SMT-LIB", "semantic similarity", "embedding"
   - Keep focus on business value: "formal verification", "automated quality assurance"

2. **Replace "How It Works" text with Mermaid diagram:**
   - Create a VERY SIMPLE 3-box flow: Input → Process → Output
   - Add to both README.md and Swagger UI (src/main.py FastAPI description)
   - Include HTML comment above diagram: `<!-- Mermaid diagram - renders in GitHub and Swagger UI -->`
   - Use generic labels: "Natural Language Input" → "AI-Powered Processing" → "Verified Output"

3. **Change license from MIT to CC BY-NC-ND:**
   - Update `LICENSE` file with full Creative Commons Attribution-NonCommercial-NoDerivatives 4.0 International license text
   - Update license reference in `src/main.py` FastAPI metadata
   - Search entire codebase for any other MIT license references and update them
   - CC BY-NC-ND means: Attribution required, Non-Commercial use only, No Derivatives allowed

4. **Add proof field to API response:**
   - Add `proof` field to `ProcessResponse` model in `src/api/models.py`
   - Field should contain BOTH:
     - `raw_output`: Full solver output from cvc5 (string)
     - `summary`: Human-readable verification summary (string)
   - Update `ProcessResponse.from_domain()` to map proof data
   - Verify `VerifiedOutput` domain model includes proof data (if not, add it)
   - Update response examples in Swagger to show proof field
</requirements>

<implementation>
**Step 1: Abstract Documentation Terminology**
1. Read `src/main.py` to locate "Semantic-Preserving SMT-LIB Pipeline" references
2. Replace with: "Intelligent Formal Verification Service" or similar business-friendly name
3. Remove technical implementation details while maintaining accuracy
4. Update service title, description, and metadata

**Step 2: Create and Integrate Mermaid Diagram**
1. Design very simple Mermaid flow:
   ```mermaid
   graph LR
       A[Natural Language Input] --> B[AI-Powered Processing]
       B --> C[Verified Output]
   ```
2. Add to README.md in "How It Works" section (replace existing text)
3. Add to `src/main.py` FastAPI description (replace existing "How It Works" text section)
4. Include HTML comment for viewer compatibility

**Step 3: Update License to CC BY-NC-ND**
1. Search for MIT license references:
   - `LICENSE` file
   - `src/main.py` license_info
   - README.md (if exists)
   - Any other files mentioning MIT
2. Replace `LICENSE` file content with CC BY-NC-ND 4.0 full text from: https://creativecommons.org/licenses/by-nc-nd/4.0/legalcode.txt
3. Update `src/main.py` license_info:
   ```python
   license_info={
       "name": "CC BY-NC-ND 4.0",
       "url": "https://creativecommons.org/licenses/by-nc-nd/4.0/",
   }
   ```
4. Add license badge to README.md if it exists

**Step 4: Add Proof Field to API Response**
1. Read `src/domain/models.py` to check if VerifiedOutput has proof data
2. If missing, add proof fields to VerifiedOutput:
   ```python
   proof_raw_output: str | None = None
   proof_summary: str | None = None
   ```
3. Update `src/api/models.py` ProcessResponse:
   ```python
   proof: dict | None = Field(
       default=None,
       description=(
           "Verification proof from the formal verification engine. "
           "Contains both raw solver output and human-readable summary."
       ),
       examples=[{
           "raw_output": "(sat)\n((x 7))",
           "summary": "Verification successful: Found satisfying assignment where x=7"
       }]
   )
   ```
4. Update ProcessResponse.from_domain() to construct proof dict
5. Update example responses in Swagger documentation

**Why These Patterns:**
- CC BY-NC-ND prevents commercial use and derivatives, protecting IP while allowing attribution
- Mermaid diagrams render natively in GitHub and Swagger UI without external dependencies
- Proof data enables external auditing while maintaining clean API design
- Business-friendly terminology makes the API marketable while hiding implementation
</implementation>

<constraints>
- **Never break existing functionality**: All API endpoints must continue working
- **Maintain type safety**: Full type annotations, no `Any` types
- **Preserve async patterns**: All I/O operations stay async
- **Keep backward compatibility**: Proof field must be optional (default=None) so existing clients don't break
- **Run formatters**: Execute `black .` and `ruff check .` before committing
</constraints>

<output>
Modify these files:
- `./LICENSE` - Replace with CC BY-NC-ND 4.0 full license text
- `./README.md` - Add Mermaid diagram (if README exists), update license badge
- `./src/main.py` - Update service title, add Mermaid diagram, update license_info
- `./src/api/routes/pipeline.py` - Update endpoint descriptions to remove technical terms
- `./src/api/models.py` - Add proof field to ProcessResponse with examples
- `./src/domain/models.py` - Add proof fields to VerifiedOutput (if missing)
- Any other files with MIT license references

Do NOT modify:
- Core pipeline logic (`src/domain/steps/`)
- SMT executor implementations
- Test files (unless updating expected responses)
</output>

<verification>
Before declaring complete, verify your work:

1. **License verification:**
   ```bash
   grep -r "MIT" . --exclude-dir=.git --exclude-dir=node_modules
   ```
   Should find NO MIT references

2. **Mermaid diagram rendering:**
   - Check README.md contains valid Mermaid syntax
   - Check src/main.py description contains valid Mermaid syntax
   - Verify HTML comment is present for viewer compatibility

3. **Type safety:**
   ```bash
   ruff check .
   ```
   Should pass with no errors

4. **API response structure:**
   - Verify ProcessResponse includes proof field
   - Verify proof is optional (default=None)
   - Verify examples show both raw_output and summary

5. **Formatting:**
   ```bash
   black . && ruff check .
   ```
   Should pass with no changes needed
</verification>

<success_criteria>
- All occurrences of "Semantic-Preserving SMT-LIB Pipeline" replaced with business-friendly alternatives
- All occurrences of "MIT License" replaced with "CC BY-NC-ND 4.0"
- LICENSE file contains full CC BY-NC-ND 4.0 legal text
- README.md and src/main.py both contain simple Mermaid diagram (Input → Process → Output)
- ProcessResponse model includes optional proof field with both raw_output and summary
- All formatters pass (black, ruff)
- Existing API functionality unchanged
- Type hints complete and correct
</success_criteria>
