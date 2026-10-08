import RelationalPerimeter

/-! Public clients close the agreement interface with received-prefix
resumption and the actually produced neighboring subdivisions. The final
evaluation is an executability smoke, not a cost or physical measurement. -/
set_option genInjectivity false
set_option maxRecDepth 4096
namespace Tests.Relativity.ProductiveAgreementChecks
open RelationalPerimeter.Relativity
open RelationalPerimeter.Relativity.Production
open ConstitutiveSearch.Resources

def input : Received := ⟨Rational.zero, 7, Calibration.unit⟩

def initial : RelativePathState :=
  let produced := realizeRelativeReading (.received input) .here (.prior .here)
    (.prior (.prior .here)) rfl 0 0
  RelativePathState.fromExecution produced (.prior (.prior .here)) rfl

def presentation (rule : RelativeRefinementRule) : RelativePathPresentation initial :=
  RelativePathPresentation.fromState initial rule

def window : ReadingWindow := ⟨Rational.neg (Rational.ofNat 2), Rational.ofNat 5⟩

def certified (rule : RelativeRefinementRule) : ProductiveWindowCertificate (presentation rule) window :=
  ⟨0, (presentation rule).stored, rfl, by
    change window.BracketContains initial.reading
    decide⟩

def afterResume (rule : RelativeRefinementRule) (steps : Nat) :
    ProductiveWindowCertificate ((presentation rule).resume steps) window :=
  (certified rule).certifyAgreed _ ((presentation rule).resumptionAgreement steps)

theorem every_resume_has_a_completely_realized_certificate (rule : RelativeRefinementRule) (steps : Nat) :
    (afterResume rule steps).realization =
      ((presentation rule).resume steps).stored.evolve rule
        (((presentation rule).resumptionAgreement steps).modulus (certified rule).agreementPrecision +
          (certified rule).agreementPrecision.denominator) :=
  productive_agreed_certificate_exact ..

theorem received_agreement_determines_a_sufficient_depth (rule : RelativeRefinementRule) (steps : Nat) :
    (afterResume rule steps).depth = 2 * (certified rule).agreementPrecision.denominator := by
  unfold afterResume
  rw [productive_agreed_certificate_depth]
  dsimp only [RelativePathPresentation.resumptionAgreement]
  exact (Nat.two_mul _).symm

theorem certified_resume_keeps_every_future (rule : RelativeRefinementRule) (resume future : Nat) :
    window.Contains
      (((presentation rule).resume resume).realize ((afterResume rule resume).depth + future)).state.reading.value :=
  productive_window_all_later_readings _ _

theorem certificate_existence_is_invariant_for_every_window (rule : RelativeRefinementRule)
    (steps : Nat) (chosen : ReadingWindow) :
    Nonempty (ProductiveWindowCertificate (presentation rule) chosen) ↔
      Nonempty (ProductiveWindowCertificate ((presentation rule).resume steps) chosen) :=
  productive_window_agreement_iff _ _ ((presentation rule).resumptionAgreement steps) chosen

def leftNeighbor : RelativePathPresentation (refineRelativePaths initial .lower).state :=
  RelativePathPresentation.fromState _ .upper

def rightNeighbor : RelativePathPresentation (refineRelativePaths initial .upper).state :=
  RelativePathPresentation.fromState _ .lower

def neighborAgreement : Analysis.Agreement leftNeighbor.numeric rightNeighbor.numeric :=
  relative_children_boundary_agreement initial

theorem the_neighbors_do_not_have_identical_initial_readings :
    leftNeighbor.stored.state.reading.value ≠ rightNeighbor.stored.state.reading.value :=
  relative_subdivision_choices_have_different_readings initial

theorem neighboring_certificate_existence (chosen : ReadingWindow) :
    Nonempty (ProductiveWindowCertificate leftNeighbor chosen) ↔
      Nonempty (ProductiveWindowCertificate rightNeighbor chosen) :=
  productive_window_agreement_iff _ _ neighborAgreement chosen

def leftCertificate : ProductiveWindowCertificate leftNeighbor window :=
  leftNeighbor.initialWindow.restrict ⟨by decide, by decide⟩

def rightCertificate : ProductiveWindowCertificate rightNeighbor window :=
  leftCertificate.certifyAgreed rightNeighbor neighborAgreement

theorem agreement_preserves_the_second_sources :
    (historyTransport rightCertificate.realization.chain.history).references
        (refineRelativePaths initial .upper).state.reading.arrivals.first ≠
      (historyTransport rightCertificate.realization.chain.history).references
        (refineRelativePaths initial .upper).state.reading.arrivals.second :=
  relative_refinement_chain_keeps_sources _

theorem agreement_preserves_the_second_record :
    rightCertificate.realization.state.cursor.read
      ((historyTransport rightCertificate.realization.chain.history).references
        (refineRelativePaths initial .upper).state.reading.arrivals.secondSignal) =
      (refineRelativePaths initial .upper).state.cursor.read
        (refineRelativePaths initial .upper).state.reading.arrivals.secondSignal :=
  history_preserves_reads _ _

theorem every_agreed_cover_extends_the_received_second_prefix (cover : InstrumentalReadingCover window) :
    ∃ steps, (cover.selectAgreed rightNeighbor neighborAgreement leftCertificate).certificate.realization =
      rightNeighbor.stored.evolve rightNeighbor.rule steps :=
  productive_agreed_cover_extends_the_second_prefix ..

private def certificateReport {source : RelativePathState} {family : RelativePathPresentation source}
    {chosen : ReadingWindow} (produced : ProductiveWindowCertificate family chosen) : Nat × Nat :=
  (produced.depth, produced.realization.state.reading.denominator.relayCount)

def smoke (rule : RelativeRefinementRule) (resume : Nat) : Nat × Nat :=
  @certificateReport initial ((presentation rule).resume resume) window (afterResume rule resume)
#eval smoke .upper 1

end Tests.Relativity.ProductiveAgreementChecks
/- AXIOM_AUDIT_BEGIN -/
#print axioms Tests.Relativity.ProductiveAgreementChecks.input
#print axioms Tests.Relativity.ProductiveAgreementChecks.initial
#print axioms Tests.Relativity.ProductiveAgreementChecks.presentation
#print axioms Tests.Relativity.ProductiveAgreementChecks.window
#print axioms Tests.Relativity.ProductiveAgreementChecks.certified
#print axioms Tests.Relativity.ProductiveAgreementChecks.afterResume
#print axioms Tests.Relativity.ProductiveAgreementChecks.every_resume_has_a_completely_realized_certificate
#print axioms Tests.Relativity.ProductiveAgreementChecks.received_agreement_determines_a_sufficient_depth
#print axioms Tests.Relativity.ProductiveAgreementChecks.certified_resume_keeps_every_future
#print axioms Tests.Relativity.ProductiveAgreementChecks.certificate_existence_is_invariant_for_every_window
#print axioms Tests.Relativity.ProductiveAgreementChecks.leftNeighbor
#print axioms Tests.Relativity.ProductiveAgreementChecks.rightNeighbor
#print axioms Tests.Relativity.ProductiveAgreementChecks.neighborAgreement
#print axioms Tests.Relativity.ProductiveAgreementChecks.the_neighbors_do_not_have_identical_initial_readings
#print axioms Tests.Relativity.ProductiveAgreementChecks.neighboring_certificate_existence
#print axioms Tests.Relativity.ProductiveAgreementChecks.leftCertificate
#print axioms Tests.Relativity.ProductiveAgreementChecks.rightCertificate
#print axioms Tests.Relativity.ProductiveAgreementChecks.agreement_preserves_the_second_sources
#print axioms Tests.Relativity.ProductiveAgreementChecks.agreement_preserves_the_second_record
#print axioms Tests.Relativity.ProductiveAgreementChecks.every_agreed_cover_extends_the_received_second_prefix
#print axioms Tests.Relativity.ProductiveAgreementChecks.smoke
/- AXIOM_AUDIT_END -/
