import RelationalPerimeter.Relativity.Production.RelativePathPrecision

/-!
# Productive families of relative instrumental presentations

Finite local rules drive the existing path producer from its received state.
An ideal numerical readout is then eliminated from these realized prefixes,
with a constructive modulus and positive agreement under resumption. Neither
this readout nor the depth of a requested prefix is a local head parameter.
Independent depth queries may execute their prefixes; only explicit resume
shares an already returned prefix. No physical point or coverage is asserted.
-/
set_option genInjectivity false
namespace RelationalPerimeter.Relativity.Production
open Analysis

/-- Declared instrumental controls, not reconstructed physical laws. The
alternating control reads the actual received numerator count. -/
inductive RelativeRefinementRule where
  | lower | upper | alternating

def RelativeRefinementRule.select (rule : RelativeRefinementRule)
    (state : RelativePathState) : RelativeSubdivision :=
  match rule with
  | .lower => .lower
  | .upper => .upper
  | .alternating => if state.reading.numerator.relayCount % 2 = 0 then .upper else .lower

def RelativeRefinementRun.next {source} (prior : RelativeRefinementRun source)
    (rule : RelativeRefinementRule) : RelativeRefinementRun source :=
  let choice := rule.select prior.state
  prior.resume choice

/-- Forward recursion passes the actual returned head to the next call.
The remaining horizon is never an input to next, select or the producer. -/
def RelativeRefinementRun.evolve {source} (prior : RelativeRefinementRun source)
    (rule : RelativeRefinementRule) : Nat → RelativeRefinementRun source
  | 0 => prior
  | steps + 1 =>
    let head := prior.next rule
    head.evolve rule steps

theorem relative_evolution_next_exact {source} (prior : RelativeRefinementRun source)
    (rule : RelativeRefinementRule) :
    (prior.next rule).state = (refineRelativePaths prior.state (rule.select prior.state)).state := rfl

theorem relative_evolution_compose {source} (prior : RelativeRefinementRun source)
    (rule : RelativeRefinementRule) (first second : Nat) :
    (prior.evolve rule first).evolve rule second = prior.evolve rule (first + second) := by
  induction first generalizing prior with
  | zero => rw [Nat.zero_add]; rfl
  | succ first ih =>
    rw [Nat.succ_add]
    exact ih (prior.next rule)

private theorem appended_request_length (requests : List RelativeSubdivision) (choice : RelativeSubdivision) :
    (requests ++ [choice]).length = requests.length + 1 := by
  induction requests with
  | nil => rfl
  | cons request tail ih => exact congrArg Nat.succ ih

theorem relative_evolution_request_count {source} (prior : RelativeRefinementRun source)
    (rule : RelativeRefinementRule) (steps : Nat) :
    (prior.evolve rule steps).chain.requests.length = prior.chain.requests.length + steps := by
  induction steps generalizing prior with
  | zero => exact (Nat.add_zero _).symm
  | succ steps ih =>
    change ((prior.next rule).evolve rule steps).chain.requests.length = _
    rw [ih]
    change (prior.chain.requests ++ [rule.select prior.state]).length + steps = _
    rw [appended_request_length]
    exact_natural

theorem relative_evolution_brackets {source} (prior : RelativeRefinementRun source)
    (rule : RelativeRefinementRule) (steps : Nat) :
    Rational.Le prior.state.reading.value (prior.evolve rule steps).state.reading.value ∧
      Rational.Le (prior.evolve rule steps).state.reading.upper prior.state.reading.upper := by
  induction steps generalizing prior with
  | zero => exact ⟨Rational.le_refl _, Rational.le_refl _⟩
  | succ steps ih =>
    have tail := ih (prior.next rule)
    have lower : Rational.Le prior.state.reading.value (prior.next rule).state.reading.value := by
      rw [relative_evolution_next_exact]
      exact relative_refinement_lower_monotone _
    have upper : Rational.Le (prior.next rule).state.reading.upper prior.state.reading.upper := by
      rw [relative_evolution_next_exact]
      exact relative_refinement_upper_monotone _
    exact ⟨Rational.le_trans lower tail.1, Rational.le_trans tail.2 upper⟩

private theorem close_in_bracket {source : Cursor} (reading : RelativePathReading source)
    (value : Rational) (lower : Rational.Le reading.value value)
    (upper : Rational.Le value reading.upper) : Close value reading.value reading.resolution := by
  have forward := Rational.add_le_left upper (Rational.neg reading.value)
  change Rational.Le (Rational.sub value reading.value) (Rational.sub reading.upper reading.value) at forward
  rw [relative_bracket_span] at forward
  have backward := Rational.add_le_left lower (Rational.neg value)
  rw [Rational.add_neg] at backward
  exact ⟨forward, Rational.le_trans backward (relative_resolution_nonnegative reading)⟩

theorem relative_evolution_future_close {source} (prior : RelativeRefinementRun source)
    (rule : RelativeRefinementRule) (first second : Nat) (ordered : first ≤ second) :
    Close (prior.evolve rule second).state.reading.value (prior.evolve rule first).state.reading.value
      (prior.evolve rule first).state.reading.resolution := by
  let stored := prior.evolve rule first
  let length := second - first
  have composed : stored.evolve rule length = prior.evolve rule second := by
    exact (relative_evolution_compose prior rule first length).trans
      (congrArg (prior.evolve rule) ((Nat.add_comm first length).trans (Arithmetic.Natural.sub_add_of_le ordered)))
  have brackets := relative_evolution_brackets stored rule length
  have upper := Rational.le_trans (relative_bracket_ordered _) brackets.2
  have close := close_in_bracket stored.state.reading (stored.evolve rule length).state.reading.value
    brackets.1 upper
  rw [composed] at close
  exact close

theorem relative_evolution_precision {source} (prior : RelativeRefinementRun source)
    (rule : RelativeRefinementRule) (precision : Precision) (steps : Nat)
    (enough : precision.denominator ≤ steps) :
    Rational.Le (prior.evolve rule steps).state.reading.resolution precision.value := by
  apply relative_refinement_reaches_requested_precision
  rw [relative_evolution_request_count]
  exact Nat.le_trans enough (Nat.le_add_left ..)

theorem relative_evolution_cauchy {source} (prior : RelativeRefinementRun source)
    (rule : RelativeRefinementRule) (precision : Precision) (first second : Nat)
    (firstEnough : precision.denominator ≤ first) (secondEnough : precision.denominator ≤ second) :
    Close (prior.evolve rule first).state.reading.value (prior.evolve rule second).state.reading.value
      precision.value := by
  cases Nat.le_total first second with
  | inl ordered =>
    have close := close_symm (relative_evolution_future_close prior rule first second ordered)
    have bound := relative_evolution_precision prior rule precision first firstEnough
    exact ⟨Rational.le_trans close.1 bound, Rational.le_trans close.2 bound⟩
  | inr ordered =>
    have close := relative_evolution_future_close prior rule second first ordered
    have bound := relative_evolution_precision prior rule precision second secondEnough
    exact ⟨Rational.le_trans close.1 bound, Rational.le_trans close.2 bound⟩

/-- A rich prefix and a closed local rule generate the entire family. There
is no field for a free numerical sequence, limit, point or future history. -/
structure RelativePathPresentation (source : RelativePathState) where
  stored : RelativeRefinementRun source
  rule : RelativeRefinementRule

def RelativePathPresentation.fromState (source : RelativePathState) (rule : RelativeRefinementRule) :
    RelativePathPresentation source := ⟨⟨source, .root source⟩, rule⟩

def RelativePathPresentation.realize {source} (presentation : RelativePathPresentation source)
    (steps : Nat) : RelativeRefinementRun source := presentation.stored.evolve presentation.rule steps

/-- Store the realized prefix once. Subsequent realization starts from this
received prefix rather than reconstructing its earlier productions. -/
def RelativePathPresentation.resume {source} (presentation : RelativePathPresentation source)
    (steps : Nat) : RelativePathPresentation source :=
  let produced := presentation.realize steps
  ⟨produced, presentation.rule⟩

def RelativePathPresentation.realizePrecision {source} (presentation : RelativePathPresentation source)
    (precision : Precision) : RelativePrecisionRun source precision :=
  let produced := presentation.realize precision.denominator
  ⟨produced, relative_evolution_precision presentation.stored presentation.rule
    precision precision.denominator (Nat.le_refl _)⟩

theorem relative_presentation_resume_exact {source} (presentation : RelativePathPresentation source)
    (first second : Nat) :
    (presentation.resume first).realize second = presentation.realize (first + second) :=
  relative_evolution_compose ..

theorem relative_presentation_origin {source} (presentation : RelativePathPresentation source) (steps : Nat) :
    (presentation.realize steps).state.reading.numerator.origin =
      (historyTransport (presentation.realize steps).chain.history).references source.reading.numerator.origin :=
  relative_refinement_chain_origin _

theorem relative_presentation_sources {source} (presentation : RelativePathPresentation source) (steps : Nat) :
    (historyTransport (presentation.realize steps).chain.history).references source.reading.arrivals.first ≠
      (historyTransport (presentation.realize steps).chain.history).references source.reading.arrivals.second :=
  relative_refinement_chain_keeps_sources _

/-- A downstream numerical interpretation. Requesting an approximation can
execute a finite prefix; no production cost or memoization is erased here. -/
def RelativePathPresentation.numeric {source} (presentation : RelativePathPresentation source) :
    CauchyRepresentation where
  approximate n := (presentation.realize n).state.reading.value
  modulus e := e.denominator
  cauchy e n m hn hm := relative_evolution_cauchy presentation.stored presentation.rule e n m hn hm

theorem relative_presentation_approximation_exact {source} (presentation : RelativePathPresentation source)
    (steps : Nat) : presentation.numeric.approximate steps = (presentation.realize steps).state.reading.value := rfl

theorem relative_first_upper_reading_differs {source} (prior : RelativeRefinementRun source)
    (rule : RelativeRefinementRule) (selected : rule.select prior.state = .upper) :
    (RelativePathPresentation.numeric ⟨prior, rule⟩).approximate 0 ≠
      (RelativePathPresentation.numeric ⟨prior, rule⟩).approximate 1 := by
  change prior.state.reading.value ≠ (prior.next rule).state.reading.value
  rw [relative_evolution_next_exact, selected]
  intro same
  exact relative_subdivision_choices_have_different_readings prior.state
    ((relative_refinement_lower_choice_exact prior.state).trans same)

def RelativePathPresentation.resumptionAgreement {source} (presentation : RelativePathPresentation source)
    (steps : Nat) : Agreement presentation.numeric (presentation.resume steps).numeric where
  modulus e := e.denominator
  close e n m hn hm := by
    change Close (presentation.realize n).state.reading.value
      ((presentation.resume steps).realize m).state.reading.value e.value
    rw [relative_presentation_resume_exact]
    exact relative_evolution_cauchy presentation.stored presentation.rule e n (steps + m) hn
      (Nat.le_trans hm (Nat.le_add_left ..))

theorem relative_evolution_lower_endpoint {source} (prior : RelativeRefinementRun source) (steps : Nat) :
    (prior.evolve .lower steps).state.reading.value = prior.state.reading.value := by
  induction steps generalizing prior with
  | zero => rfl
  | succ steps ih =>
    exact (ih (prior.next .lower)).trans (relative_refinement_lower_choice_exact prior.state)

theorem relative_evolution_upper_endpoint {source} (prior : RelativeRefinementRun source) (steps : Nat) :
    (prior.evolve .upper steps).state.reading.upper = prior.state.reading.upper := by
  induction steps generalizing prior with
  | zero => rfl
  | succ steps ih =>
    exact (ih (prior.next .upper)).trans (relative_refinement_upper_choice_exact prior.state)

def relative_lower_limit_agreement {source} (prior : RelativeRefinementRun source) :
    Agreement (RelativePathPresentation.numeric ⟨prior, .lower⟩)
      (CauchyRepresentation.constant prior.state.reading.value) :=
  CauchyRepresentation.pointwiseAgreement _ _ (fun n => relative_evolution_lower_endpoint prior n)

def relative_upper_limit_agreement {source} (prior : RelativeRefinementRun source) :
    Agreement (RelativePathPresentation.numeric ⟨prior, .upper⟩)
      (CauchyRepresentation.constant prior.state.reading.upper) where
  modulus e := e.denominator
  close e n _ hn _ := by
    let produced := prior.evolve .upper n
    have fixed := relative_evolution_upper_endpoint prior n
    have ordered := relative_bracket_ordered produced.state.reading
    rw [fixed] at ordered
    have forward := Rational.add_le_left ordered (Rational.neg prior.state.reading.upper)
    rw [Rational.add_neg] at forward
    have span := relative_bracket_span produced.state.reading
    rw [fixed] at span
    change Close produced.state.reading.value prior.state.reading.upper e.value
    refine ⟨Rational.le_trans forward e.zero_le_value, ?_⟩
    rw [span]
    exact relative_evolution_precision prior .upper e n hn

/-- The common numerical boundary is obtained from the actual child count
laws and their generated limits. It is not equality of rich receptions. -/
def relative_children_boundary_agreement (source : RelativePathState) :
    Agreement
      ((RelativePathPresentation.fromState (refineRelativePaths source .lower).state .upper).numeric)
      ((RelativePathPresentation.fromState (refineRelativePaths source .upper).state .lower).numeric) :=
  let left := (RelativePathPresentation.fromState (refineRelativePaths source .lower).state .upper).stored
  let right := (RelativePathPresentation.fromState (refineRelativePaths source .upper).state .lower).stored
  let constants : Agreement (CauchyRepresentation.constant left.state.reading.upper)
      (CauchyRepresentation.constant right.state.reading.value) :=
    CauchyRepresentation.pointwiseAgreement
      (CauchyRepresentation.constant left.state.reading.upper)
      (CauchyRepresentation.constant right.state.reading.value)
      (fun _ => relative_refinement_children_meet source)
  Agreement.compose (relative_upper_limit_agreement left)
    (Agreement.compose constants (Agreement.reverse (relative_lower_limit_agreement right)))

end RelationalPerimeter.Relativity.Production
/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Relativity.Production.RelativeRefinementRule
#print axioms RelationalPerimeter.Relativity.Production.RelativeRefinementRule.select
#print axioms RelationalPerimeter.Relativity.Production.RelativeRefinementRun.next
#print axioms RelationalPerimeter.Relativity.Production.RelativeRefinementRun.evolve
#print axioms RelationalPerimeter.Relativity.Production.relative_evolution_next_exact
#print axioms RelationalPerimeter.Relativity.Production.relative_evolution_compose
#print axioms RelationalPerimeter.Relativity.Production.relative_evolution_request_count
#print axioms RelationalPerimeter.Relativity.Production.relative_evolution_brackets
#print axioms RelationalPerimeter.Relativity.Production.relative_evolution_future_close
#print axioms RelationalPerimeter.Relativity.Production.relative_evolution_precision
#print axioms RelationalPerimeter.Relativity.Production.relative_evolution_cauchy
#print axioms RelationalPerimeter.Relativity.Production.RelativePathPresentation
#print axioms RelationalPerimeter.Relativity.Production.RelativePathPresentation.fromState
#print axioms RelationalPerimeter.Relativity.Production.RelativePathPresentation.realize
#print axioms RelationalPerimeter.Relativity.Production.RelativePathPresentation.resume
#print axioms RelationalPerimeter.Relativity.Production.RelativePathPresentation.realizePrecision
#print axioms RelationalPerimeter.Relativity.Production.relative_presentation_resume_exact
#print axioms RelationalPerimeter.Relativity.Production.relative_presentation_origin
#print axioms RelationalPerimeter.Relativity.Production.relative_presentation_sources
#print axioms RelationalPerimeter.Relativity.Production.RelativePathPresentation.numeric
#print axioms RelationalPerimeter.Relativity.Production.relative_presentation_approximation_exact
#print axioms RelationalPerimeter.Relativity.Production.relative_first_upper_reading_differs
#print axioms RelationalPerimeter.Relativity.Production.RelativePathPresentation.resumptionAgreement
#print axioms RelationalPerimeter.Relativity.Production.relative_evolution_lower_endpoint
#print axioms RelationalPerimeter.Relativity.Production.relative_evolution_upper_endpoint
#print axioms RelationalPerimeter.Relativity.Production.relative_lower_limit_agreement
#print axioms RelationalPerimeter.Relativity.Production.relative_upper_limit_agreement
#print axioms RelationalPerimeter.Relativity.Production.relative_children_boundary_agreement
/- AXIOM_AUDIT_END -/
