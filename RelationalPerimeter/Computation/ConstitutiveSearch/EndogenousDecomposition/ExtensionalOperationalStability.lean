import RelationalPerimeter.Computation.ConstitutiveSearch.EndogenousDecomposition.ExecutedOperationalReductionHistory

/-!
# Extensional observation and operational non-factorization

An extensional stability view records the source and retained states, the one
continuation actually observed at each state, acceptance, and the measured
width trace.  It deliberately does not contain the total action of the
transport on arbitrary continuations.

The finite separator at the end proves that this omission is substantive:
two acceptance-preserving transports have the same executed observation and
the same width trace, yet differ on another admissible continuation.
-/

namespace ConstitutiveSearch.EndogenousDecomposition

open SAT

/-- What state-and-width observation retains from one operational reduction. -/
structure ExtensionalOperationalStabilityView (system : SearchSystem) where
  sourceState : system.State
  retainedState : system.State
  observedSource : system.Continuation sourceState
  observedRetained : system.Continuation retainedState
  sourceAccepted : system.Accept sourceState observedSource
  retainedAccepted : system.Accept retainedState observedRetained
  widthTrace : List Nat
  widthBound : WidthTraceAtMost 2 widthTrace

/-- Extensional view of the reduction actually executed at one stage. -/
def executedStepToExtensionalView {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    (run : ThreadedConstitutiveStageRun state stage) :
    ExtensionalOperationalStabilityView
      (generatedStructuralBranchSystem
        (distinctGrowingDiscoveryFormula
          (constructStage (depth + 1)).searchIndex)) :=
  { sourceState := stage.schedule.entry.source
    retainedState := stage.schedule.entry.target
    observedSource := stage.sourceContinuation
    observedRetained := stage.application.output
    sourceAccepted := stage.sourceAccepted
    retainedAccepted := stage.outputAccepted
    widthTrace := executedStageWidthTrace run
    widthBound := by
      change WidthTraceAtMost 2 [1, 2, 1]
      exact .cons (Nat.succ_le_succ (Nat.zero_le 1))
        (.cons (Nat.le_refl 2)
          (.cons (Nat.succ_le_succ (Nat.zero_le 1)) .nil)) }

/-- The observed output in the view is exactly the discovered map application. -/
theorem extensionalView_observedOutput_exact {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    (run : ThreadedConstitutiveStageRun state stage) :
    (executedStepToExtensionalView run).observedRetained =
      stage.schedule.entry.relation.mapContinuation
        (executedStepToExtensionalView run).observedSource :=
  stageApplication_eq_returnedRelationMap run

/-- The projected trace is computed from the actual entry/opened/retained lists. -/
theorem extensionalView_widthTrace_exact {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    (run : ThreadedConstitutiveStageRun state stage) :
    (executedStepToExtensionalView run).widthTrace =
      executedStageWidthTrace run :=
  rfl

/-- Forget a total transport after recording one accepted source observation,
its transported output, and the common transient width profile. -/
def transportToExtensionalStabilityView
    {system : SearchSystem}
    {source retained : system.State}
    (transport : AcceptingContinuationTransport system source retained)
    (observed : system.Continuation source)
    (accepted : system.Accept source observed) :
    ExtensionalOperationalStabilityView system :=
  { sourceState := source
    retainedState := retained
    observedSource := observed
    observedRetained := transport.map observed
    sourceAccepted := accepted
    retainedAccepted := transport.preservesAccept observed accepted
    widthTrace := [1, 2, 1]
    widthBound :=
      .cons (Nat.succ_le_succ (Nat.zero_le 1))
        (.cons (Nat.le_refl 2)
          (.cons (Nat.succ_le_succ (Nat.zero_le 1)) .nil)) }

namespace ExtensionalSeparator

/-- Minimal system in which every Boolean continuation is admissible. -/
def system : SearchSystem :=
  { State := Bool
    Continuation := fun _ => Bool
    Accept := fun _ _ => True }

/-- Transport that preserves both Boolean continuations. -/
def preservingTransport :
    AcceptingContinuationTransport system false true :=
  { map := fun continuation => continuation
    preservesAccept := fun _ _ => True.intro }

/-- Transport with the same observed output at `false`, but a different total map. -/
def collapsingTransport :
    AcceptingContinuationTransport system false true :=
  { map := fun _ => false
    preservesAccept := fun _ _ => True.intro }

/-- Extensional projection of the identity-like total transport. -/
def preservingView : ExtensionalOperationalStabilityView system :=
  transportToExtensionalStabilityView preservingTransport false True.intro

/-- Extensional projection of the collapsing total transport. -/
def collapsingView : ExtensionalOperationalStabilityView system :=
  transportToExtensionalStabilityView collapsingTransport false True.intro

/-- Backward-compatible name for the shared observed view. -/
def commonView : ExtensionalOperationalStabilityView system :=
  preservingView

/-- Both transports produce the same output on the executed continuation. -/
theorem same_executed_output :
    preservingTransport.map preservingView.observedSource =
      collapsingTransport.map collapsingView.observedSource :=
  rfl

/-- Projecting the two distinct total transports yields the same complete
extensional stability view. -/
theorem same_extensional_stability_view : preservingView = collapsingView :=
  rfl

/-- Their actions differ on another admissible continuation. -/
theorem different_arbitrary_continuation_action :
    preservingTransport.map true ≠ collapsingTransport.map true := by
  intro impossible
  exact Bool.noConfusion impossible

/--
No reconstruction from the extensional view can recover both total
operational actions.  The observed state, accepted output, and width trace are
the same; the arbitrary-continuation action is not.
-/
theorem operational_action_not_factors_through_extensional_view
    (recover : ExtensionalOperationalStabilityView system → Bool → Bool)
    (recoversPreserving :
      ∀ continuation,
        recover preservingView continuation = preservingTransport.map continuation)
    (recoversCollapsing :
      ∀ continuation,
        recover collapsingView continuation = collapsingTransport.map continuation) :
    False := by
  have sameRecovered : recover preservingView true = recover collapsingView true :=
    congrArg (fun view => recover view true) same_extensional_stability_view
  exact different_arbitrary_continuation_action
    (Eq.trans (recoversPreserving true).symm
      (Eq.trans sameRecovered (recoversCollapsing true)))

end ExtensionalSeparator

end ConstitutiveSearch.EndogenousDecomposition

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExtensionalOperationalStabilityView
#print axioms ConstitutiveSearch.EndogenousDecomposition.executedStepToExtensionalView
#print axioms ConstitutiveSearch.EndogenousDecomposition.extensionalView_observedOutput_exact
#print axioms ConstitutiveSearch.EndogenousDecomposition.extensionalView_widthTrace_exact
#print axioms ConstitutiveSearch.EndogenousDecomposition.transportToExtensionalStabilityView
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExtensionalSeparator.system
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExtensionalSeparator.preservingTransport
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExtensionalSeparator.collapsingTransport
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExtensionalSeparator.preservingView
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExtensionalSeparator.collapsingView
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExtensionalSeparator.commonView
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExtensionalSeparator.same_executed_output
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExtensionalSeparator.same_extensional_stability_view
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExtensionalSeparator.different_arbitrary_continuation_action
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExtensionalSeparator.operational_action_not_factors_through_extensional_view
/- AXIOM_AUDIT_END -/
