import RelationalPerimeter.Computation.Machine.ReducedLiveRunner

/-! General checks include refusal followed by more requests, empty scopes,
repeated positions and the actual successor, not only equal final readings. -/
set_option genInjectivity false
set_option autoImplicit false
namespace ConstitutiveSearch.ReconfigurableMachine.LiveReduction
open ConnectedFabric ContinuationSignatures

theorem runReduced_tail {scope : Scope} (memory : Runtime scope)
    (request : ULift.{3} Request) (rest : List (ULift.{3} Request)) :
    (runReduced memory (request :: rest)).tail =
      runReduced (performReduced memory request.down).1 rest := rfl

theorem enabledReduced_pulse (scope : Scope) (left right : Signals) :
    enabledReduced scope ⟨.pulse left right⟩ = pulseFits scope left right := by
  unfold enabledReduced
  cases admission scope (.pulse left right) with
  | inl witness => exact witness.down.down.symm
  | inr impossible =>
      cases check : pulseFits scope left right with
      | false => rfl
      | true => exact False.elim (impossible ⟨⟨check⟩⟩)

theorem runReduced_refused {scope : Scope} (memory : Runtime scope)
    (left right : Signals) (wrong : pulseFits scope left right = false)
    (rest : List (ULift.{3} Request)) :
    runReduced memory (⟨.pulse left right⟩ :: rest) =
      .step (readRuntime memory) false .refused (runReduced memory rest) := by
  rw [runReduced_cons, enabledReduced_pulse, wrong,
    refusal_preserves_runtime memory left right wrong]

theorem runReduced_sample {scope : Scope} (memory : Runtime scope)
    (inlet : Inlet) (rest : List (ULift.{3} Request)) :
    runReduced memory (⟨.sample inlet⟩ :: rest) =
      .step (readRuntime memory) true (.sampled (memory.bank.read inlet))
        (runReduced memory rest) := rfl

theorem runReduced_empty_scope (memory : Memory) (requests : List (ULift.{3} Request)) :
    (runtimeContract []).outcome memory requests =
      runReduced (projectMemory [] memory) requests :=
  executed_all_futures_exact [] memory requests

theorem runReduced_repeated_scope (query : Nat) (memory : Memory)
    (requests : List (ULift.{3} Request)) :
    (runtimeContract [Channel.singleton query, Channel.singleton query]).outcome memory requests =
      runReduced (projectMemory [Channel.singleton query, Channel.singleton query] memory) requests :=
  executed_all_futures_exact _ memory requests

end ConstitutiveSearch.ReconfigurableMachine.LiveReduction
/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.ReconfigurableMachine.LiveReduction.runReduced_tail
#print axioms ConstitutiveSearch.ReconfigurableMachine.LiveReduction.enabledReduced_pulse
#print axioms ConstitutiveSearch.ReconfigurableMachine.LiveReduction.runReduced_refused
#print axioms ConstitutiveSearch.ReconfigurableMachine.LiveReduction.runReduced_sample
#print axioms ConstitutiveSearch.ReconfigurableMachine.LiveReduction.runReduced_empty_scope
#print axioms ConstitutiveSearch.ReconfigurableMachine.LiveReduction.runReduced_repeated_scope
/- AXIOM_AUDIT_END -/
