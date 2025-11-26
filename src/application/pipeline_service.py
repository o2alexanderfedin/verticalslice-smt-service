"""Pipeline service orchestrating the three-step verification process.

This is the application layer that coordinates domain logic.
"""

import logging
import time
from typing import TYPE_CHECKING

from src.domain.exceptions import PipelineError
from src.domain.models import EnrichmentResult, PipelineMetrics, VerifiedOutput
from src.domain.steps.enrichment import EnrichmentStep
from src.domain.steps.extraction import ExtractionStep
from src.domain.steps.formalization import FormalizationStep
from src.domain.steps.validation import ValidationStep
from src.domain.verification.embedding_verifier import EmbeddingDistanceVerifier
from src.shared.result import Err, Ok, Result

if TYPE_CHECKING:
    from src.domain.protocols import EmbeddingProvider, LLMProvider, SMTSolver
    from src.shared.config import Settings

logger = logging.getLogger(__name__)


class PipelineService:
    """Orchestrates the three-step pipeline for SMT-LIB generation."""

    def __init__(
        self,
        embedding_provider: "EmbeddingProvider",
        llm_provider: "LLMProvider",
        smt_solver: "SMTSolver",
        settings: "Settings",
    ):
        """Initialize pipeline service.

        Args:
            embedding_provider: Provider for text embeddings
            llm_provider: Provider for LLM interactions
            smt_solver: SMT solver executor
            settings: Application settings
        """
        self.embedding_provider = embedding_provider
        self.llm_provider = llm_provider
        self.smt_solver = smt_solver
        self.settings = settings

        # Create semantic verifier (shared across steps)
        self.semantic_verifier = EmbeddingDistanceVerifier()

        logger.info("PipelineService initialized")

    async def process(
        self,
        informal_text: str,
        skip_formalization: bool = False,
        enrich: bool = False,
    ) -> Result[VerifiedOutput, PipelineError]:
        """Process informal text through the complete pipeline.

        Orchestrates all steps sequentially:
        0. (Optional) Enrichment with web search
        1. Formalization with semantic verification
        2. Extraction with degradation check
        3. Validation with solver execution

        Args:
            informal_text: Input natural language text
            skip_formalization: If True, skip formalization and treat input as already formal
            enrich: If True, enrich text with web search before processing

        Returns:
            Ok(VerifiedOutput) if pipeline succeeds
            Err(PipelineError) if any step fails
        """
        logger.info(
            f"Starting pipeline processing (text_length={len(informal_text)}, enrich={enrich})"
        )
        pipeline_start = time.time()

        # Optional Step 0: Enrichment
        enrichment_output: EnrichmentResult | None = None
        text_to_process = informal_text

        if enrich:
            logger.info("=== Step 0: Enrichment ===")

            enrichment_step = EnrichmentStep(
                llm_provider=self.llm_provider,
                max_searches=self.settings.enrichment_max_searches,
                timeout=self.settings.enrichment_timeout,
            )

            enrichment_result = await enrichment_step.execute(informal_text)

            match enrichment_result:
                case Err(error):
                    logger.error(f"Step 0 failed: {error}")
                    return Err(error)
                case Ok(enrichment_data):
                    enrichment_output = enrichment_data
                    text_to_process = enrichment_data.enriched_text
                    logger.info(
                        f"Step 0 succeeded: search_count={enrichment_data.search_count}, "
                        f"sources={len(enrichment_data.sources_used)}"
                    )

        # Step 1: Formalization
        logger.info("=== Step 1: Formalization ===")
        formalization_start = time.time()

        formalization_step = FormalizationStep(
            llm_provider=self.llm_provider,
            embedding_provider=self.embedding_provider,
            verifier=self.semantic_verifier,
            threshold=self.settings.formalization_similarity_threshold,
            max_retries=self.settings.formalization_max_retries,
            skip_threshold=self.settings.formalization_skip_threshold,
        )

        formalization_result = await formalization_step.execute(
            text_to_process, force_skip=skip_formalization
        )
        formalization_time = time.time() - formalization_start

        match formalization_result:
            case Err(error):
                logger.error(f"Step 1 failed: {error}")
                return Err(error)
            case Ok(formalization_output):
                logger.info(
                    f"Step 1 succeeded: similarity={formalization_output.similarity_score:.4f}, "
                    f"attempts={formalization_output.attempts}"
                )
                formal_text = formalization_output.formal_text

        # Step 2: Extraction
        logger.info("=== Step 2: Extraction ===")
        extraction_start = time.time()

        extraction_step = ExtractionStep(
            llm_provider=self.llm_provider,
            embedding_provider=self.embedding_provider,
            verifier=self.semantic_verifier,
            max_degradation=self.settings.extraction_max_degradation,
            max_retries=self.settings.extraction_max_retries,
            detail_start=self.settings.extraction_detail_start,
            detail_step=self.settings.extraction_detail_step,
            skip_retries_threshold=self.settings.extraction_skip_retries_threshold,
        )

        extraction_result = await extraction_step.execute(formal_text)
        extraction_time = time.time() - extraction_start

        match extraction_result:
            case Err(error):
                logger.error(f"Step 2 failed: {error}")
                return Err(error)
            case Ok(extraction_output):
                logger.info(
                    f"Step 2 succeeded: degradation={extraction_output.degradation:.4f}, "
                    f"attempts={extraction_output.attempts}"
                )
                smt_code = extraction_output.smt_lib_code

        # Step 3: Validation
        logger.info("=== Step 3: Validation ===")
        validation_start = time.time()

        validation_step = ValidationStep(
            llm_provider=self.llm_provider,
            smt_solver=self.smt_solver,
            max_retries=self.settings.validation_max_retries,
            solver_timeout=30.0,
        )

        validation_result = await validation_step.execute(smt_code)
        validation_time = time.time() - validation_start

        match validation_result:
            case Err(error):
                logger.error(f"Step 3 failed: {error}")
                return Err(error)
            case Ok(solver_output):
                logger.info(
                    f"Step 3 succeeded: result={solver_output.check_sat_result}, "
                    f"attempts={solver_output.attempts}"
                )

        # Build pipeline metrics
        total_time = time.time() - pipeline_start

        metrics = PipelineMetrics(
            formalization_attempts=formalization_output.attempts,
            final_formalization_similarity=formalization_output.similarity_score,
            formalization_time_seconds=formalization_time,
            extraction_attempts=extraction_output.attempts,
            final_extraction_degradation=extraction_output.degradation,
            extraction_time_seconds=extraction_time,
            validation_attempts=solver_output.attempts,
            solver_execution_time_seconds=validation_time,
            total_time_seconds=total_time,
            success=True,
        )

        # Build proof summary
        proof_summary = self._build_proof_summary(solver_output)

        # Build final verified output
        verified_output = VerifiedOutput(
            informal_text=informal_text,
            enrichment_performed=enrichment_output is not None,
            enriched_text=(enrichment_output.enriched_text if enrichment_output else informal_text),
            enrichment_search_count=(enrichment_output.search_count if enrichment_output else None),
            enrichment_sources=enrichment_output.sources_used if enrichment_output else None,
            enrichment_time_seconds=(
                enrichment_output.enrichment_time_seconds if enrichment_output else None
            ),
            formal_text=formal_text,
            formalization_similarity=formalization_output.similarity_score,
            smt_lib_code=smt_code,
            extraction_degradation=extraction_output.degradation,
            check_sat_result=solver_output.check_sat_result,
            model=solver_output.model,
            unsat_core=solver_output.unsat_core,
            solver_success=solver_output.success,
            proof_raw_output=solver_output.raw_output,
            proof_summary=proof_summary,
            metrics=metrics,
            passed_all_checks=True,
        )

        logger.info(f"Pipeline completed successfully in {total_time:.2f}s")

        return Ok(verified_output)

    def _build_proof_summary(self, solver_output) -> str:
        """Build human-readable verification summary from solver output.

        Args:
            solver_output: SolverResult from validation step

        Returns:
            Human-readable summary of verification results
        """
        result = solver_output.check_sat_result

        if result == "sat":
            if solver_output.model:
                return f"Verification successful: Found satisfying assignment {solver_output.model}"
            return "Verification successful: Formula is satisfiable"
        elif result == "unsat":
            if solver_output.unsat_core:
                return f"Verification failed: Formula is unsatisfiable. Core: {solver_output.unsat_core}"
            return "Verification failed: Formula is unsatisfiable (no solution exists)"
        elif result == "unknown":
            return "Verification inconclusive: Solver could not determine satisfiability"
        else:
            return f"Verification result: {result}"
