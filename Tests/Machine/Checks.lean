import RelationalPerimeter.Computation.Machine.MachineCertificate
import RelationalPerimeter.Computation.Machine.ConnectionSearch

/-! Closed constructive checks, independent from the development IO trace. -/
set_option genInjectivity false
namespace ConstitutiveSearch.ReconfigurableMachine.Checks
open SAT EndogenousDecomposition ConnectedFabric

def closedRoot : GeneratedStructuralBranchContext ([] : Cnf) := .root []
def closedLeft : GeneratedStructuralBranchContext ([] : Cnf) :=
  closedRoot.child 0 false True.intro
def closedRight : GeneratedStructuralBranchContext ([] : Cnf) :=
  closedRoot.child 0 true True.intro

/-- Reusing the left context as its own flipped target genuinely fails. -/
theorem closed_search_failure :
    (generatedStructuralFlipAtSearch [] 0).find closedLeft closedLeft = none := rfl

theorem closed_failure_keeps_two_buffers :
    (attemptBank [Channel.singleton 0] 0 closedLeft closedLeft [false] [false]).cells = 2 := rfl

/-- Positive counterpart: the same structural search finds the distinct sibling. -/
theorem closed_search_success :
    (findConnection [Channel.singleton 0] 0 closedLeft closedRight).isSome = true := rfl

theorem closed_success_groups_convergent_signals :
    (attemptBank [Channel.singleton 0] 0 closedLeft closedRight [false] [true]).cells = 1 := rfl

theorem closed_success_does_not_group_different_signals :
    (attemptBank [Channel.singleton 0] 0 closedLeft closedRight [false] [false]).cells = 2 := rfl

theorem truth_table :
    (Gate.mk false).fire false = false ∧ (Gate.mk false).fire true = true ∧
      (Gate.mk true).fire false = true ∧ (Gate.mk true).fire true = false := by
  constructor
  · rfl
  · constructor
    · rfl
    · constructor <;> rfl

theorem all_two_bit_configurations (a b x y : Bool) :
    fire [⟨a⟩, ⟨b⟩] [x, y] = [(Gate.mk a).fire x, (Gate.mk b).fire y] := rfl

theorem produced_connections_have_real_selected_gate {live : LiveContinuation.Memory}
    (production : LiveContinuation.Production live) :
    compile [Channel.singleton
      (causalStageOfThreadedStage production.built.run).selected] production = [⟨true⟩] := by
  change [configureGate _ _] = _
  unfold configureGate
  rw [if_pos (show (Channel.singleton
    (causalStageOfThreadedStage production.built.run).selected).query =
      (causalStageOfThreadedStage production.built.run).selected from rfl)]

theorem produced_selected_gate_cannot_be_replaced_by_direct {live : LiveContinuation.Memory}
    (production : LiveContinuation.Production live) :
    fire (compile [Channel.singleton
      (causalStageOfThreadedStage production.built.run).selected] production) [false] ≠
      fire [⟨false⟩] [false] := by
  rw [produced_connections_have_real_selected_gate]
  intro same
  have head := congrArg (fun signals : Signals => signals.headD false) same
  exact Bool.noConfusion head

theorem requested_samples_do_not_advance (scope : Scope) (memory : Memory) (inlet : Inlet) :
    (perform scope memory (.sample inlet)).1 = memory := rfl

theorem admitted_bit_pairs_never_force_one_buffer (live : LiveContinuation.Memory) :
    let scope := [Channel.singleton 0]
    let memory : Memory := ⟨live, [⟨true⟩], .shared [true]⟩
    (perform scope memory (.pulse [false] [false])).1.bank.cells = 2 := rfl

theorem malformed_pulse_refused (live : LiveContinuation.Memory) :
    let scope := [Channel.singleton 0]
    let memory : Memory := ⟨live, [⟨true⟩], .shared [true]⟩
    perform scope memory (.pulse [] [true]) = (memory, .refused) := rfl

end ConstitutiveSearch.ReconfigurableMachine.Checks
/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.ReconfigurableMachine.Checks.closed_search_failure
#print axioms ConstitutiveSearch.ReconfigurableMachine.Checks.closed_failure_keeps_two_buffers
#print axioms ConstitutiveSearch.ReconfigurableMachine.Checks.closed_search_success
#print axioms ConstitutiveSearch.ReconfigurableMachine.Checks.closed_success_groups_convergent_signals
#print axioms ConstitutiveSearch.ReconfigurableMachine.Checks.closed_success_does_not_group_different_signals
#print axioms ConstitutiveSearch.ReconfigurableMachine.Checks.truth_table
#print axioms ConstitutiveSearch.ReconfigurableMachine.Checks.all_two_bit_configurations
#print axioms ConstitutiveSearch.ReconfigurableMachine.Checks.produced_connections_have_real_selected_gate
#print axioms ConstitutiveSearch.ReconfigurableMachine.Checks.produced_selected_gate_cannot_be_replaced_by_direct
#print axioms ConstitutiveSearch.ReconfigurableMachine.Checks.requested_samples_do_not_advance
#print axioms ConstitutiveSearch.ReconfigurableMachine.Checks.admitted_bit_pairs_never_force_one_buffer
#print axioms ConstitutiveSearch.ReconfigurableMachine.Checks.malformed_pulse_refused
/- AXIOM_AUDIT_END -/
