import RelationalPerimeter.Computation.Machine.CanonicalMemory

/-! Closed positive examples and necessary boundaries of causal reduction.
No electrical calibration is substituted for the scientific source profiles. -/
set_option genInjectivity false
namespace ConstitutiveSearch.ReconfigurableMachine
open EndogenousDecomposition ContinuationSignatures ConnectedFabric

theorem same_outputs_different_bank_shapes_same_futures
    (scope : Scope) (live : LiveContinuation.Memory) (gates : List Gate) (signals : Signals) :
    FutureEquivalent (runtimeContract scope) ⟨live, gates, .separate signals signals⟩
      ⟨live, gates, .shared signals⟩ :=
  (bankReduction scope).equal_memory_same_futures (redundant_bank_shape_removed live gates signals)



theorem calibration_is_not_a_gate_field_observation (memory : Memory) :
    (perform [Channel.singleton 0] { memory with gates := [⟨true⟩] } (.pulse [false] [false])).2 =
      .driven [true] [false] ∧
    (perform [Channel.singleton 0] { memory with gates := [⟨false⟩] } (.pulse [false] [false])).2 =
      .driven [false] [false] := by
  constructor <;> rfl

theorem normalized_storage_one_if_equal (signals : Signals) :
    (normalizeBank (.separate signals signals)).cells = 1 :=
  (route_shared_iff signals signals).mpr rfl

theorem normalized_storage_two_if_unequal (left right : Signals) (different : left ≠ right) :
    normalizeBank (.separate left right) = .separate left right := by
  unfold normalizeBank route
  split
  · rename_i same
    exact False.elim (different same)
  · rfl

/-- The observer cannot reconstruct an unused second copy from its futures. -/
theorem duplicate_vs_shared_remain_different_representations (signals : Signals) :
    Bank.separate signals signals ≠ Bank.shared signals := by
  intro same
  nomatch same

end ConstitutiveSearch.ReconfigurableMachine
/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.ReconfigurableMachine.same_outputs_different_bank_shapes_same_futures
#print axioms ConstitutiveSearch.ReconfigurableMachine.unequal_connections_have_distinguishing_pulse
#print axioms ConstitutiveSearch.ReconfigurableMachine.calibration_is_not_a_gate_field_observation
#print axioms ConstitutiveSearch.ReconfigurableMachine.normalized_storage_one_if_equal
#print axioms ConstitutiveSearch.ReconfigurableMachine.normalized_storage_two_if_unequal
#print axioms ConstitutiveSearch.ReconfigurableMachine.duplicate_vs_shared_remain_different_representations
/- AXIOM_AUDIT_END -/
