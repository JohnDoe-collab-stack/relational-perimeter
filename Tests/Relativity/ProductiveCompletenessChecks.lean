import RelationalPerimeter

/-! Closed public clients: window-based agreement of every resumed family,
the produced neighboring subdivisions, and a genuinely separated pair.
The final evaluation is only a finite executability smoke. -/
set_option genInjectivity false
set_option maxRecDepth 4096
namespace Tests.Relativity.ProductiveCompletenessChecks
open RelationalPerimeter.Relativity
open RelationalPerimeter.Relativity.Production
open RelationalPerimeter.Relativity.Analysis
open ConstitutiveSearch.Resources

def resumptionTransfer {source} (presentation : RelativePathPresentation source) (steps : Nat) :
    ProductiveWindowTransfer presentation (presentation.resume steps) :=
  ⟨fun _ certificate => certificate.toResumed steps⟩

def resumptionFromWindows {source} (presentation : RelativePathPresentation source) (steps : Nat) :
    Agreement presentation.numeric (presentation.resume steps).numeric :=
  (resumptionTransfer presentation steps).toAgreement

theorem resumption_agrees_at_every_later_index {source}
    (presentation : RelativePathPresentation source) (steps : Nat) (precision : Precision)
    (left right : Nat) (enoughLeft : (resumptionFromWindows presentation steps).modulus precision ≤ left)
    (enoughRight : (resumptionFromWindows presentation steps).modulus precision ≤ right) :
    Close (presentation.numeric.approximate left)
      ((presentation.resume steps).numeric.approximate right) precision.value :=
  (resumptionFromWindows presentation steps).close precision left right enoughLeft enoughRight

theorem the_first_prefix_is_actually_produced {source}
    (presentation : RelativePathPresentation source) (steps : Nat) (precision : Precision) :
    ((resumptionTransfer presentation steps).compare precision).firstCertificate.realization =
      presentation.stored.evolve presentation.rule precision.half.denominator :=
  productive_comparison_request_exact ..

theorem resumption_consumes_the_received_request {source}
    (presentation : RelativePathPresentation source) (steps : Nat) (precision : Precision) :
    ((resumptionTransfer presentation steps).compare precision).secondCertificate.realization =
      (presentation.requestWindow precision).certificate.realization.evolve presentation.rule steps := rfl

theorem the_window_modulus_reads_both_returned_depths {source}
    (presentation : RelativePathPresentation source) (steps : Nat) (precision : Precision) :
    (resumptionFromWindows presentation steps).modulus precision =
      ((resumptionTransfer presentation steps).compare precision).firstCertificate.depth +
        ((resumptionTransfer presentation steps).compare precision).secondCertificate.depth := rfl

theorem the_resumption_modulus_has_a_closed_bound {source}
    (presentation : RelativePathPresentation source) (steps : Nat) (precision : Precision) :
    (resumptionFromWindows presentation steps).modulus precision =
      precision.half.denominator + precision.half.denominator := rfl

theorem the_reconstructed_agreement_certifies_every_window {source}
    (presentation : RelativePathPresentation source) (steps : Nat) (window : ReadingWindow) :
    Nonempty (ProductiveWindowCertificate presentation window) ↔
      Nonempty (ProductiveWindowCertificate (presentation.resume steps) window) :=
  productive_window_agreement_iff _ _ (resumptionFromWindows presentation steps) window

theorem identity_comparison_reuses_the_entire_certificate {source}
    (presentation : RelativePathPresentation source) (precision : Precision) :
    ((ProductiveWindowTransfer.identity presentation).compare precision).secondCertificate =
      ((ProductiveWindowTransfer.identity presentation).compare precision).firstCertificate := rfl

def input : Received := ⟨Rational.zero, 7, Calibration.unit⟩

def initial : RelativePathState :=
  let produced := realizeRelativeReading (.received input) .here (.prior .here)
    (.prior (.prior .here)) rfl 0 0
  RelativePathState.fromExecution produced (.prior (.prior .here)) rfl

def family (rule : RelativeRefinementRule) : RelativePathPresentation initial :=
  RelativePathPresentation.fromState initial rule

def leftNeighbor : RelativePathPresentation (refineRelativePaths initial .lower).state :=
  RelativePathPresentation.fromState _ .upper

def rightNeighbor : RelativePathPresentation (refineRelativePaths initial .upper).state :=
  RelativePathPresentation.fromState _ .lower

def neighborTransfer : ProductiveWindowTransfer leftNeighbor rightNeighbor :=
  ProductiveWindowTransfer.ofAgreement rightNeighbor (relative_children_boundary_agreement initial)

def neighborFromWindows : Agreement leftNeighbor.numeric rightNeighbor.numeric :=
  neighborTransfer.toAgreement

theorem the_neighbors_still_have_distinct_initial_readings :
    leftNeighbor.stored.state.reading.value ≠ rightNeighbor.stored.state.reading.value :=
  relative_subdivision_choices_have_different_readings initial

theorem neighboring_windows_reconstruct_a_real_agreement (precision : Precision) (left right : Nat)
    (enoughLeft : neighborFromWindows.modulus precision ≤ left)
    (enoughRight : neighborFromWindows.modulus precision ≤ right) :
    Close (leftNeighbor.numeric.approximate left) (rightNeighbor.numeric.approximate right) precision.value :=
  neighborFromWindows.close precision left right enoughLeft enoughRight

theorem the_returned_second_sources_remain_distinct (precision : Precision) :
    (historyTransport (neighborTransfer.compare precision).secondCertificate.realization.chain.history).references
        (refineRelativePaths initial .upper).state.reading.arrivals.first ≠
      (historyTransport (neighborTransfer.compare precision).secondCertificate.realization.chain.history).references
        (refineRelativePaths initial .upper).state.reading.arrivals.second :=
  relative_refinement_chain_keeps_sources _

theorem the_returned_second_record_is_preserved (precision : Precision) :
    (neighborTransfer.compare precision).secondCertificate.realization.state.cursor.read
      ((historyTransport (neighborTransfer.compare precision).secondCertificate.realization.chain.history).references
        (refineRelativePaths initial .upper).state.reading.arrivals.secondSignal) =
      (refineRelativePaths initial .upper).state.cursor.read
        (refineRelativePaths initial .upper).state.reading.arrivals.secondSignal :=
  history_preserves_reads _ _

theorem separated_constants_have_no_agreement :
    ¬ Nonempty (Agreement (CauchyRepresentation.constant Rational.zero)
      (CauchyRepresentation.constant Rational.one)) := by
  intro ⟨agreement⟩
  have near := agreement.close Precision.unit.half (agreement.modulus Precision.unit.half)
    (agreement.modulus Precision.unit.half) (Nat.le_refl _) (Nat.le_refl _)
  change Close Rational.zero Rational.one Precision.unit.half.value at near
  have bound := near.2
  rw [Rational.sub_zero] at bound
  exact (show ¬ Rational.Le Rational.one Precision.unit.half.value by decide) bound

theorem separated_generated_families_have_no_total_transfer :
    ¬ Nonempty (ProductiveWindowTransfer (family .lower) (family .upper)) := by
  intro ⟨transfer⟩
  let left := relative_lower_limit_agreement (family .lower).stored
  let right := relative_upper_limit_agreement (family .upper).stored
  have constants := Agreement.compose left.reverse (Agreement.compose transfer.toAgreement right)
  have lowerValue : (family .lower).stored.state.reading.value = Rational.zero := by decide
  have upperValue : (family .upper).stored.state.reading.upper = Rational.one := by decide
  rw [lowerValue, upperValue] at constants
  apply separated_constants_have_no_agreement
  exact ⟨constants⟩

def smoke (rule : RelativeRefinementRule) : Nat :=
  ((ProductiveWindowTransfer.identity (family rule)).toAgreement).modulus Precision.unit
#eval smoke .upper

end Tests.Relativity.ProductiveCompletenessChecks
/- AXIOM_AUDIT_BEGIN -/
#print axioms Tests.Relativity.ProductiveCompletenessChecks.resumptionTransfer
#print axioms Tests.Relativity.ProductiveCompletenessChecks.resumptionFromWindows
#print axioms Tests.Relativity.ProductiveCompletenessChecks.resumption_agrees_at_every_later_index
#print axioms Tests.Relativity.ProductiveCompletenessChecks.the_first_prefix_is_actually_produced
#print axioms Tests.Relativity.ProductiveCompletenessChecks.resumption_consumes_the_received_request
#print axioms Tests.Relativity.ProductiveCompletenessChecks.the_window_modulus_reads_both_returned_depths
#print axioms Tests.Relativity.ProductiveCompletenessChecks.the_resumption_modulus_has_a_closed_bound
#print axioms Tests.Relativity.ProductiveCompletenessChecks.the_reconstructed_agreement_certifies_every_window
#print axioms Tests.Relativity.ProductiveCompletenessChecks.identity_comparison_reuses_the_entire_certificate
#print axioms Tests.Relativity.ProductiveCompletenessChecks.input
#print axioms Tests.Relativity.ProductiveCompletenessChecks.initial
#print axioms Tests.Relativity.ProductiveCompletenessChecks.family
#print axioms Tests.Relativity.ProductiveCompletenessChecks.leftNeighbor
#print axioms Tests.Relativity.ProductiveCompletenessChecks.rightNeighbor
#print axioms Tests.Relativity.ProductiveCompletenessChecks.neighborTransfer
#print axioms Tests.Relativity.ProductiveCompletenessChecks.neighborFromWindows
#print axioms Tests.Relativity.ProductiveCompletenessChecks.the_neighbors_still_have_distinct_initial_readings
#print axioms Tests.Relativity.ProductiveCompletenessChecks.neighboring_windows_reconstruct_a_real_agreement
#print axioms Tests.Relativity.ProductiveCompletenessChecks.the_returned_second_sources_remain_distinct
#print axioms Tests.Relativity.ProductiveCompletenessChecks.the_returned_second_record_is_preserved
#print axioms Tests.Relativity.ProductiveCompletenessChecks.separated_constants_have_no_agreement
#print axioms Tests.Relativity.ProductiveCompletenessChecks.separated_generated_families_have_no_total_transfer
#print axioms Tests.Relativity.ProductiveCompletenessChecks.smoke
/- AXIOM_AUDIT_END -/
