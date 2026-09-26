import RelationalPerimeter.Computation.ConstitutiveSearch.EndogenousDecomposition.ExecutedOperationalReductionHistory

/-!
# Extensional observation and operational non-factorization

An extensional stability view records the source and retained states, the one
continuation actually observed at each state, acceptance, and the measured
width trace.  It deliberately does not contain the total action of the
transport on arbitrary continuations.

Both the executed-system separator and the finite explanatory separator prove
that this omission is substantive: two acceptance-preserving transports agree
on the recorded observation and width trace, yet differ on another admissible
continuation.
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

namespace ExecutedExtensionalSeparator

/-- The acceptance-preserving transport reconstructed by the executed run. -/
def discoveredTransport {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    (_run : ThreadedConstitutiveStageRun state stage) :
    AcceptingContinuationTransport
      (generatedStructuralBranchSystem
        (distinctGrowingDiscoveryFormula
          (constructStage (depth + 1)).searchIndex))
      stage.schedule.entry.source stage.schedule.entry.target :=
  stage.discovery.relation.toAcceptingTransport

/-- A comparison transport on the same executed source and target.  It agrees
with the discovered transport at the continuation actually executed, while
forgetting the discovered action everywhere else. -/
def observedConstantTransport {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    (_run : ThreadedConstitutiveStageRun state stage) :
    AcceptingContinuationTransport
      (generatedStructuralBranchSystem
        (distinctGrowingDiscoveryFormula
          (constructStage (depth + 1)).searchIndex))
      stage.schedule.entry.source stage.schedule.entry.target :=
  { map := fun _ =>
      stage.discovery.relation.mapContinuation stage.sourceContinuation
    preservesAccept := fun _ _ =>
      stage.discovery.relation.mapContinuation_accept
        stage.sourceContinuation stage.sourceAccepted }

/-- A second source continuation obtained by changing the anchor coordinate.
The anchor is distinct from the selected branch variable, so the constituted
source decision remains realized. -/
def alternateContinuation {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    (_run : ThreadedConstitutiveStageRun state stage) :
    GeneratedStructuralBranchContinuation stage.schedule.entry.source := by
  let anchor := stageAnchorVar (depth + 1)
  refine ⟨Assignment.flipAt anchor stage.sourceContinuation.1, ?_⟩
  change
    Assignment.flipAt anchor stage.sourceContinuation.1 stage.discovery.var = false ∧
      True
  constructor
  · rw [Assignment.flipAt_other]
    · exact stage.sourceContinuation.2.1
    · have selected := sequentialStage_selected_exact stage
      change stage.discovery.var = stageSelectedVar (depth + 1) at selected
      dsimp only [anchor]
      rw [selected, stageAnchorVar_eq_selected_succ]
      exact Nat.ne_of_lt (Nat.lt_succ_self _)
  · exact True.intro

/-- The discovered and comparison transports produce the same observed output. -/
theorem same_observed_output {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    (run : ThreadedConstitutiveStageRun state stage) :
    (discoveredTransport run).map stage.sourceContinuation =
      (observedConstantTransport run).map stage.sourceContinuation :=
  rfl

/-- The comparison does not collapse into equality of total actions: on the
alternate continuation, the discovered map retains the changed anchor bit and
the constant map does not. -/
theorem different_total_action {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    (run : ThreadedConstitutiveStageRun state stage) :
    (discoveredTransport run).map (alternateContinuation run) ≠
      (observedConstantTransport run).map (alternateContinuation run) := by
  intro same
  have sameAt := congrArg
    (fun continuation => continuation.1 (stageAnchorVar (depth + 1))) same
  change
    Assignment.flipAt stage.discovery.var
        (Assignment.flipAt (stageAnchorVar (depth + 1))
          stage.sourceContinuation.1)
        (stageAnchorVar (depth + 1)) =
      Assignment.flipAt stage.discovery.var stage.sourceContinuation.1
        (stageAnchorVar (depth + 1)) at sameAt
  have anchorDifferent : stageAnchorVar (depth + 1) ≠ stage.discovery.var := by
    have selected := sequentialStage_selected_exact stage
    change stage.discovery.var = stageSelectedVar (depth + 1) at selected
    rw [selected, stageAnchorVar_eq_selected_succ]
    exact Nat.ne_of_gt (Nat.lt_succ_self _)
  rw [Assignment.flipAt_other _ _ _ anchorDifferent,
    Assignment.flipAt_selected,
    Assignment.flipAt_other _ _ _ anchorDifferent] at sameAt
  cases value : stage.sourceContinuation.1 (stageAnchorVar (depth + 1)) <;>
    rw [value] at sameAt <;> cases sameAt

/-- Both transports induce the same complete extensional view on the executed
system and its actually observed source continuation. -/
theorem same_extensional_view {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    (run : ThreadedConstitutiveStageRun state stage) :
    transportToExtensionalStabilityView (discoveredTransport run)
        stage.sourceContinuation stage.sourceAccepted =
      transportToExtensionalStabilityView (observedConstantTransport run)
        stage.sourceContinuation stage.sourceAccepted :=
  rfl

/-- The comparison transport agrees with the output recorded by the actual
executed projection at its observed source continuation. -/
theorem comparison_matches_executed_observation {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    (run : ThreadedConstitutiveStageRun state stage) :
    (observedConstantTransport run).map
        (executedStepToExtensionalView run).observedSource =
      (executedStepToExtensionalView run).observedRetained :=
  (stageApplication_eq_returnedRelationMap run).symm

/-- On the executed family itself, no function of the extensional view can
recover both the discovered action and the comparison action. -/
theorem operational_action_not_factors_on_executed_system {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    (run : ThreadedConstitutiveStageRun state stage)
    (recover : ExtensionalOperationalStabilityView
      (generatedStructuralBranchSystem
        (distinctGrowingDiscoveryFormula
          (constructStage (depth + 1)).searchIndex)) →
      GeneratedStructuralBranchContinuation stage.schedule.entry.source →
      GeneratedStructuralBranchContinuation stage.schedule.entry.target)
    (recoversDiscovered : ∀ continuation,
      recover
          (executedStepToExtensionalView run)
          continuation =
        (discoveredTransport run).map continuation)
    (recoversConstant : ∀ continuation,
      recover
          (executedStepToExtensionalView run)
          continuation =
        (observedConstantTransport run).map continuation) : False := by
  exact different_total_action run
    ((recoversDiscovered (alternateContinuation run)).symm.trans
      (recoversConstant (alternateContinuation run)))

end ExecutedExtensionalSeparator

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
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedExtensionalSeparator.discoveredTransport
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedExtensionalSeparator.observedConstantTransport
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedExtensionalSeparator.alternateContinuation
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedExtensionalSeparator.same_observed_output
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedExtensionalSeparator.different_total_action
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedExtensionalSeparator.same_extensional_view
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedExtensionalSeparator.comparison_matches_executed_observation
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedExtensionalSeparator.operational_action_not_factors_on_executed_system
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
