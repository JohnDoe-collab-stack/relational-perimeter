import RelationalPerimeter

set_option genInjectivity false
namespace Tests.ContinuationSignatureProduction
open ConstitutiveSearch.EndogenousDecomposition ConstitutiveSearch.ContinuationSignatures

theorem same_prefix_different_horizons (cursor : MasterResources.Cursor) (mode : PayloadMode)
    (first second : Nat) :
    (executeSigned (first + 1) cursor mode).readings.head? =
      (executeSigned (second + 1) cursor mode).readings.head? :=
  executeSigned_head_horizon_independent first second cursor mode

theorem actual_executor_preserved (cursor : MasterResources.Cursor) (mode : PayloadMode) (count : Nat) :
    (executeSigned count cursor mode).core = MasterResources.execute count cursor :=
  executeSigned_erases count cursor mode

theorem source_variation_is_visible (cursor : MasterResources.Cursor) (count : Nat) :
    (executeSigned (count + 1) cursor .variedLeft).readings.head? ≠
      (executeSigned (count + 1) cursor .left).readings.head? :=
  executeSigned_varied_head count cursor

theorem produced_readings_not_a_frontier (cursor : MasterResources.Cursor) (mode : PayloadMode) (count : Nat) :
    (executeSigned count cursor mode).readings.length = count :=
  executeSigned_readings_length count cursor mode

theorem positive_coverage_returns_signature (cursor : MasterResources.Cursor)
    (source : AcceptedRoleSource (cursorRole cursor)) :
    recoverSignature (roleReadBasis (cursorRole cursor) (freeVariable (causalStageOfThreadedStage cursor.head.run)))
        (roleReadRealization (cursorRole cursor) (freeVariable (causalStageOfThreadedStage cursor.head.run)))
        (roleReadCoverage (cursorRole cursor))
        ((roleReadRealization (cursorRole cursor)
          (freeVariable (causalStageOfThreadedStage cursor.head.run))).project source) =
      producedSignature (roleReadBasis (cursorRole cursor)
        (freeVariable (causalStageOfThreadedStage cursor.head.run))) source :=
  recoverSignature_exact _ _ _ source

-- Small executable smoke checks, not a performance experiment.
#eval publicSignatureMemory 0 .left
#eval publicSignatureMemory 0 .pairedRight
#eval publicSignatureMemory 0 .variedLeft

theorem runtime_data_matches_rich_execution (input : Nat) (mode : PayloadMode) :
    publicSignatureMemory input mode = (publicSignedExecution input mode).readings :=
  publicSignatureMemory_exact input mode

theorem closed_certificate_keeps_head_exactness (input : Nat) (mode : PayloadMode) :
    (publicSignatureCertificate input mode).execution.readings.head? =
      some (signatureRead (cursorSignature (ProducedContinuation.publicOrigin input) mode)) :=
  (publicSignatureCertificate input mode).headExact

theorem local_image_domain_has_two_occurrences (cursor : MasterResources.Cursor) :
    (roleOpeningFiniteCarrier (cursorRole cursor)).frontier.length = 2 := rfl

end Tests.ContinuationSignatureProduction
/- AXIOM_AUDIT_BEGIN -/
#print axioms Tests.ContinuationSignatureProduction.same_prefix_different_horizons
#print axioms Tests.ContinuationSignatureProduction.actual_executor_preserved
#print axioms Tests.ContinuationSignatureProduction.source_variation_is_visible
#print axioms Tests.ContinuationSignatureProduction.produced_readings_not_a_frontier
#print axioms Tests.ContinuationSignatureProduction.positive_coverage_returns_signature
#print axioms Tests.ContinuationSignatureProduction.runtime_data_matches_rich_execution
#print axioms Tests.ContinuationSignatureProduction.closed_certificate_keeps_head_exactness
#print axioms Tests.ContinuationSignatureProduction.local_image_domain_has_two_occurrences
/- AXIOM_AUDIT_END -/
