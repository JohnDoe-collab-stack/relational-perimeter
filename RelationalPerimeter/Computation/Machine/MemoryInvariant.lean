import RelationalPerimeter.Computation.Machine.MachineCertificate

/-! Runtime memory shape is preserved from the actual installed stage. This
is a safety invariant, not a minimum-byte or total-runtime claim. -/
set_option genInjectivity false
namespace ConstitutiveSearch.ReconfigurableMachine
open SAT EndogenousDecomposition ConnectedFabric

def Coherent (scope : Scope) (memory : Memory) : Prop :=
  memory.gates.length = scope.length ∧
    (memory.bank.read .transformed).length = scope.length ∧
    (memory.bank.read .retained).length = scope.length

theorem sensed_length (scope : Scope) (assignment : Assignment) :
    (sense scope assignment).length = scope.length := by
  induction scope with
  | nil => rfl
  | cons _ _ ih => exact congrArg Nat.succ ih

theorem fired_length (gates : List Gate) (signals : Signals)
    (same : gates.length = signals.length) : (fire gates signals).length = gates.length := by
  induction gates generalizing signals with
  | nil => rfl
  | cons gate rest ih =>
      cases signals with
      | nil => exact False.elim (Nat.noConfusion same)
      | cons bit tail => exact congrArg Nat.succ (ih tail (Nat.succ.inj same))

theorem fitting_lengths (scope : Scope) (left right : Signals)
    (fits : pulseFits scope left right = true) :
    left.length = scope.length ∧ right.length = scope.length := by
  cases l : (left.length == scope.length) with
  | false =>
      unfold pulseFits at fits
      rw [l] at fits
      exact False.elim (Bool.noConfusion fits)
  | true =>
      cases r : (right.length == scope.length) with
      | false =>
          unfold pulseFits at fits
          rw [l, r] at fits
          exact False.elim (Bool.noConfusion fits)
      | true => exact ⟨of_decide_eq_true l, of_decide_eq_true r⟩

theorem install_coherent (scope : Scope) {live : LiveContinuation.Memory}
    (production : LiveContinuation.Production live) : Coherent scope (install scope production) := by
  constructor
  · exact compile_length scope production
  · constructor
    · change ((route _ _).read .transformed).length = scope.length
      rw [route_reads_transformed]
      exact fire_sensed_length scope _ _
    · change ((route _ _).read .retained).length = scope.length
      rw [route_reads_retained]
      exact sensed_length scope _

theorem pulse_coherent (scope : Scope) (memory : Memory) (left right : Signals)
    (coherent : Coherent scope memory) : Coherent scope (pulse scope memory left right).1 := by
  dsimp only [pulse]
  split
  · rename_i fits
    have lengths := fitting_lengths scope left right fits
    constructor
    · exact coherent.1
    · constructor
      · change ((route _ _).read .transformed).length = scope.length
        rw [route_reads_transformed]
        exact (fired_length memory.gates left (coherent.1.trans lengths.1.symm)).trans coherent.1
      · change ((route _ _).read .retained).length = scope.length
        rw [route_reads_retained]
        exact lengths.2
  · exact coherent

theorem perform_coherent (scope : Scope) (memory : Memory) (request : Request)
    (coherent : Coherent scope memory) : Coherent scope (perform scope memory request).1 := by
  cases request with
  | advance => exact install_coherent scope (LiveContinuation.produce memory.live)
  | sample _ => exact coherent
  | pulse left right => exact pulse_coherent scope memory left right coherent

theorem execute_coherent (scope : Scope) (memory : Memory) (requests : List Request)
    (coherent : Coherent scope memory) : Coherent scope (execute scope memory requests).1 := by
  induction requests generalizing memory with
  | nil => exact coherent
  | cons request rest ih => exact ih _ (perform_coherent scope memory request coherent)

end ConstitutiveSearch.ReconfigurableMachine
/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.ReconfigurableMachine.sensed_length
#print axioms ConstitutiveSearch.ReconfigurableMachine.fired_length
#print axioms ConstitutiveSearch.ReconfigurableMachine.fitting_lengths
#print axioms ConstitutiveSearch.ReconfigurableMachine.install_coherent
#print axioms ConstitutiveSearch.ReconfigurableMachine.pulse_coherent
#print axioms ConstitutiveSearch.ReconfigurableMachine.perform_coherent
#print axioms ConstitutiveSearch.ReconfigurableMachine.execute_coherent
/- AXIOM_AUDIT_END -/
