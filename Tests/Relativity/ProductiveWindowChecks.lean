import RelationalPerimeter

/-! Positive public clients of generated-window certification. The final
compiled smoke is executability evidence, not physical or complexity data. -/
set_option genInjectivity false
namespace Tests.Relativity.ProductiveWindowChecks
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

def coarse : ReadingWindow := ⟨Rational.neg Rational.one, Rational.ofNat 2⟩

def division : OverlappingWindowSplit coarse :=
  ⟨Rational.zero, Rational.one, by decide, by decide, by decide⟩

def cover : InstrumentalReadingCover coarse := .split division (.identity _) (.identity _)

def certified (rule : RelativeRefinementRule) : ProductiveWindowCertificate (presentation rule) coarse :=
  ⟨0, (presentation rule).stored, rfl, by
    change coarse.BracketContains initial.reading
    decide⟩

@[irreducible] def chosen (rule : RelativeRefinementRule) :
    CoveredProductivePresentation (presentation rule) cover := cover.selectProductive (certified rule)

theorem every_rule_has_an_actual_initial_window (rule : RelativeRefinementRule) :
    (presentation rule).initialWindow.realization = (presentation rule).stored := rfl

theorem the_certificate_bounds_the_entire_rational_bracket (rule : RelativeRefinementRule)
    (value : Rational) (lower : Rational.Le initial.reading.value value)
    (upper : Rational.Le value initial.reading.upper) : coarse.Contains value :=
  bracket_contains_every_between_reading (certified rule).inside value lower upper

theorem certificates_bound_every_later_reading (rule : RelativeRefinementRule) (steps : Nat) :
    coarse.Contains ((presentation rule).realize steps).state.reading.value := by
  have inside := productive_window_all_later_readings (certified rule) steps
  change coarse.Contains ((presentation rule).realize (0 + steps)).state.reading.value at inside
  rw [Nat.zero_add] at inside
  exact inside

theorem resumption_preserves_the_complete_certificate (rule : RelativeRefinementRule) (steps : Nat) :
    ((certified rule).toResumed steps).realization =
      (certified rule).realization.evolve rule steps := rfl

theorem certificates_exist_before_and_after_any_resume (rule : RelativeRefinementRule) (steps : Nat) :
    Nonempty (ProductiveWindowCertificate ((presentation rule).resume steps) coarse) :=
  (productive_window_resumption_iff (presentation rule) coarse steps).mp ⟨certified rule⟩

theorem intersection_consumes_the_returned_prefix (rule : RelativeRefinementRule) (first second : Nat) :
    (((certified rule).advance first).common ((certified rule).advance second)).realization =
      ((certified rule).advance first).realization.evolve rule second := by
  rw [productive_common_uses_the_returned_prefix]
  change ((certified rule).advance first).realization.evolve rule (0 + second) = _
  rw [Nat.zero_add]

theorem every_cover_is_selected_from_a_real_prefix (rule : RelativeRefinementRule)
    (chosenCover : InstrumentalReadingCover coarse) :
    ∃ steps, (chosenCover.selectProductive (certified rule)).certificate.realization =
      (certified rule).realization.evolve rule steps := by
  obtain ⟨steps, _, actual⟩ := productive_cover_extends_only_its_received_prefix chosenCover (certified rule)
  exact ⟨steps, actual⟩

theorem cover_restriction_keeps_the_new_production (rule : RelativeRefinementRule) :
    (chosen rule).restrict.realization = (chosen rule).certificate.realization :=
  productive_cover_restriction_keeps_the_produced_prefix _

theorem selected_leaf_contains_every_future_reading (rule : RelativeRefinementRule) (steps : Nat) :
    (cover.selectProductive (certified rule)).window.Contains
      ((presentation rule).realize ((cover.selectProductive (certified rule)).certificate.depth + steps)).state.reading.value :=
  productive_cover_has_no_later_escape _ _ _

theorem selected_prefix_keeps_the_old_sources (rule : RelativeRefinementRule) :
    (historyTransport (cover.selectProductive (certified rule)).certificate.realization.chain.history).references
        initial.reading.arrivals.first ≠
      (historyTransport (cover.selectProductive (certified rule)).certificate.realization.chain.history).references
        initial.reading.arrivals.second := relative_refinement_chain_keeps_sources _

theorem selected_prefix_keeps_the_old_record (rule : RelativeRefinementRule) :
    (cover.selectProductive (certified rule)).certificate.realization.state.cursor.read
      ((historyTransport (cover.selectProductive (certified rule)).certificate.realization.chain.history).references
        initial.reading.arrivals.secondSignal) = initial.cursor.read initial.reading.arrivals.secondSignal :=
  history_preserves_reads _ _

theorem every_finite_search_has_its_actual_budget (rule : RelativeRefinementRule) (fuel : Nat) :
    ProductiveSearchWithinBudget ((presentation rule).searchWindow division.left fuel) :=
  productive_search_never_exceeds_its_budget _ _ _ _ _ _

theorem upper_endpoint_blocks_every_finite_left_certificate (steps : Nat) :
    ¬ division.left.BracketContains ((presentation .upper).realize steps).state.reading := by
  intro inside
  have endpoint := relative_evolution_upper_endpoint (presentation .upper).stored steps
  have initialUpper : initial.reading.upper = Rational.one := rfl
  have same : ((presentation .upper).realize steps).state.reading.upper = division.left.upper :=
    endpoint.trans initialUpper
  exact inside.2.2 same

theorem zero_budget_is_exhausted :
    (match (presentation .lower).searchWindow division.left 0 with
      | .inl _ => true | .inr _ => false) = false := rfl

theorem one_reading_does_not_certify_its_entire_future_bracket :
    division.left.Contains initial.reading.value ∧ ¬ division.left.BracketContains initial.reading :=
  ⟨by decide, upper_endpoint_blocks_every_finite_left_certificate 0⟩

@[irreducible] def resumeAfterZeroBudget : Bool × Nat :=
  match (presentation .lower).searchWindow division.left 0 with
  | .inl found => (true, found.certificate.depth)
  | .inr exhausted =>
    match exhausted.resumeSearch 1 with
    | .inl found => (true, found.certificate.depth)
    | .inr _ => (false, 0)

set_option maxHeartbeats 2000000 in
theorem one_production_changes_the_search_result :
    (match (presentation .lower).searchWindow division.left 1 with
      | .inl found => (true, found.certificate.depth) | .inr _ => (false, 0)) = (true, 1) := rfl

set_option maxHeartbeats 2000000 in
theorem resuming_the_returned_failure_finds_the_next_prefix : resumeAfterZeroBudget = (true, 1) := by
  have outside : ¬ division.left.BracketContains (presentation .lower).stored.state.reading := by
    change ¬ division.left.BracketContains initial.reading
    exact upper_endpoint_blocks_every_finite_left_certificate 0
  unfold resumeAfterZeroBudget RelativePathPresentation.searchWindow
  dsimp only [searchProductiveWindowFrom]
  rw [dif_neg outside]
  dsimp only [ProductiveWindowExhaustion.resumeSearch]
  have one := one_production_changes_the_search_result
  dsimp only [RelativePathPresentation.searchWindow] at one
  exact one

set_option maxHeartbeats 2000000 in
theorem upper_search_returns_the_produced_terminal_prefix :
    (match (presentation .upper).searchWindow division.left 1 with
      | .inl _ => 0 | .inr exhausted => exhausted.realization.state.reading.denominator.relayCount) = 2 := rfl

set_option maxHeartbeats 2000000 in
theorem lower_cover_selects_left : (cover.selectProductive (certified .lower)).leaf.branches = [true] := rfl

set_option maxHeartbeats 2000000 in
theorem upper_cover_selects_right : (cover.selectProductive (certified .upper)).leaf.branches = [false] := rfl

def smoke : (Bool × Nat) × (Bool × Nat) × List Bool × List Bool :=
  let result := (presentation .lower).searchWindow division.left 1
  let searched := match result with
    | .inl found => (true, found.certificate.depth)
    | .inr _ => (false, 0)
  (searched, resumeAfterZeroBudget, (cover.selectProductive (certified .lower)).leaf.branches,
    (cover.selectProductive (certified .upper)).leaf.branches)
#eval smoke

end Tests.Relativity.ProductiveWindowChecks
/- AXIOM_AUDIT_BEGIN -/
#print axioms Tests.Relativity.ProductiveWindowChecks.input
#print axioms Tests.Relativity.ProductiveWindowChecks.initial
#print axioms Tests.Relativity.ProductiveWindowChecks.presentation
#print axioms Tests.Relativity.ProductiveWindowChecks.coarse
#print axioms Tests.Relativity.ProductiveWindowChecks.division
#print axioms Tests.Relativity.ProductiveWindowChecks.cover
#print axioms Tests.Relativity.ProductiveWindowChecks.certified
#print axioms Tests.Relativity.ProductiveWindowChecks.chosen
#print axioms Tests.Relativity.ProductiveWindowChecks.every_rule_has_an_actual_initial_window
#print axioms Tests.Relativity.ProductiveWindowChecks.the_certificate_bounds_the_entire_rational_bracket
#print axioms Tests.Relativity.ProductiveWindowChecks.certificates_bound_every_later_reading
#print axioms Tests.Relativity.ProductiveWindowChecks.resumption_preserves_the_complete_certificate
#print axioms Tests.Relativity.ProductiveWindowChecks.certificates_exist_before_and_after_any_resume
#print axioms Tests.Relativity.ProductiveWindowChecks.intersection_consumes_the_returned_prefix
#print axioms Tests.Relativity.ProductiveWindowChecks.every_cover_is_selected_from_a_real_prefix
#print axioms Tests.Relativity.ProductiveWindowChecks.cover_restriction_keeps_the_new_production
#print axioms Tests.Relativity.ProductiveWindowChecks.selected_leaf_contains_every_future_reading
#print axioms Tests.Relativity.ProductiveWindowChecks.selected_prefix_keeps_the_old_sources
#print axioms Tests.Relativity.ProductiveWindowChecks.selected_prefix_keeps_the_old_record
#print axioms Tests.Relativity.ProductiveWindowChecks.every_finite_search_has_its_actual_budget
#print axioms Tests.Relativity.ProductiveWindowChecks.upper_endpoint_blocks_every_finite_left_certificate
#print axioms Tests.Relativity.ProductiveWindowChecks.zero_budget_is_exhausted
#print axioms Tests.Relativity.ProductiveWindowChecks.one_reading_does_not_certify_its_entire_future_bracket
#print axioms Tests.Relativity.ProductiveWindowChecks.resumeAfterZeroBudget
#print axioms Tests.Relativity.ProductiveWindowChecks.resuming_the_returned_failure_finds_the_next_prefix
#print axioms Tests.Relativity.ProductiveWindowChecks.one_production_changes_the_search_result
#print axioms Tests.Relativity.ProductiveWindowChecks.upper_search_returns_the_produced_terminal_prefix
#print axioms Tests.Relativity.ProductiveWindowChecks.lower_cover_selects_left
#print axioms Tests.Relativity.ProductiveWindowChecks.upper_cover_selects_right
#print axioms Tests.Relativity.ProductiveWindowChecks.smoke
/- AXIOM_AUDIT_END -/
