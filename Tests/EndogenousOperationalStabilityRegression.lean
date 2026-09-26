import RelationalPerimeter

/-!
# Regression gate for endogenous operational stability

These checks import only the public root.  They protect the semantic raccords,
not merely the final numerical width statements.
-/

namespace Tests.EndogenousOperationalStabilityRegression

open ConstitutiveSearch
open ConstitutiveSearch.SAT
open ConstitutiveSearch.EndogenousDecomposition
open RelationalPerimeter.Computation.EndogenousOperationalDecomposition

/-- The public construction closes every premise at input zero. -/
def publicEvidenceZero : OperationalStabilityEvidence 0 :=
  operationalStabilityEvidence 0

theorem publicStageCountZero :
    operationalStageCount
        (executeConstitutiveResolution 0).feedbackRoleHistory = 1 :=
  operational_stage_count_exact 0

theorem publicStructuralWidthZero :
    structuralWidth (executeConstitutiveResolution 0).feedbackRoleHistory =
      2 ^ operationalStageCount
        (executeConstitutiveResolution 0).feedbackRoleHistory :=
  structural_width_is_exponential 0

theorem publicPendingWidthZero :
    pendingWidth (executeConstitutiveResolution 0).feedbackRoleHistory =
      2 ^ operationalStageCount
        (executeConstitutiveResolution 0).feedbackRoleHistory :=
  pending_operational_width_is_exponential 0

theorem publicRetainedWidthZero :
    executedWidth (executeConstitutiveResolution 0).feedbackRoleHistory = 1 :=
  retained_operational_width_is_one 0

theorem publicTransientBoundZero :
    WidthTraceAtMost 2
      (executedWidthTrace
        (executeConstitutiveResolution 0).feedbackRoleHistory) :=
  transient_operational_width_is_bounded 0

theorem publicStrictSeparationZero :
    executedWidth (executeConstitutiveResolution 0).feedbackRoleHistory <
      pendingWidth (executeConstitutiveResolution 0).feedbackRoleHistory :=
  retained_width_is_strictly_below_pending 0

theorem publicMeasuredFailedMajorityZero :
    9 * (nextDiscoveryCommonOrigin 0).run.discoveryRun.outcome.attempts ≤
      10 * (executedDiscoveryWorkEvidence
        (nextDiscoveryCommonOrigin 0).run).search.failedCandidates.length :=
  initial_discovery_has_measured_failed_majority 0

/-- Every public structural profile is positively accepted and is normalized
through the executed transport history. -/
def normalizeEveryPublicStructuralProfileZero
    (profile : StructuralObligation
      (executeConstitutiveResolution 0).feedbackRoleHistory) :
    OperationalAcceptedPayload
      (executeConstitutiveResolution 0).feedbackRoleHistory :=
  publicEvidenceZero.normalizeAcceptedPayload profile
    (publicEvidenceZero.acceptedPayload profile)

/-- The measured prefix, not a decorative counter, determines attempts. -/
theorem measuredPrefixDeterminesAttempts {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    (run : ThreadedConstitutiveStageRun state stage) :
    run.discoveryRun.outcome.attempts =
      (executedDiscoveryWorkEvidence run).search.failedCandidates.length + 1 :=
  (executedDiscoveryWorkEvidence run).attemptsExact

theorem measuredPrefixContainsOnlyFailures {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    (run : ThreadedConstitutiveStageRun state stage) :
    AllMeasuredCandidatesFail
      (constructStage (depth + 1)).operationalRoot
      (executedDiscoveryWorkEvidence run).search.failedCandidates :=
  (executedDiscoveryWorkEvidence run).failuresMeasured

/-- Opening is available before any operational relation is added to its
relation-free view. -/
theorem actualOpeningIsRelationFree {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    (run : ThreadedConstitutiveStageRun state stage) :
    EndogenousFlipDiscovery.openingView stage.discovery =
      { var := stage.discovery.var
        fresh := stage.discovery.fresh
        split := generatedStructuralSplit
          (constructStage (depth + 1)).operationalRoot
          stage.discovery.var stage.discovery.fresh } :=
  executedOpening_exact run

/-- The transformation consumed by the reduction is the one returned by the
recorded executed search. -/
theorem actualDiscoveryOutcomeIsAuthoritative {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    (run : ThreadedConstitutiveStageRun state stage) :
    run.discoveryRun.outcome.discovered? = some stage.discovery :=
  executedTransformation_from_discoveryOutcome run

/-- The left branch of the reduction uses the discovered total map. -/
theorem actualLeftActionUsesDiscovery {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    (run : ThreadedConstitutiveStageRun state stage)
    (continuation : GeneratedStructuralBranchContinuation
      ((constructStage (depth + 1)).operationalRoot.child
        stage.discovery.var false stage.discovery.fresh)) :
    (executedSiblingReduction run).preservation.forward.map
        (.head continuation) =
      .head (stage.discovery.relation.mapContinuation continuation) :=
  executedSiblingReduction_left_eq_discoveredMap run continuation

theorem actualRightActionIsRetained {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    (run : ThreadedConstitutiveStageRun state stage)
    (continuation : GeneratedStructuralBranchContinuation
      ((constructStage (depth + 1)).operationalRoot.child
        stage.discovery.var true stage.discovery.fresh)) :
    (executedSiblingReduction run).preservation.forward.map
        (.tail (.head continuation)) = .head continuation :=
  executedSiblingReduction_right_eq_identity run continuation

theorem actualLeftActionPreservesCriterion {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    (run : ThreadedConstitutiveStageRun state stage)
    (continuation : GeneratedStructuralBranchContinuation
      ((constructStage (depth + 1)).operationalRoot.child
        stage.discovery.var false stage.discovery.fresh))
    (accepted : GeneratedStructuralBranchAccept
      ((constructStage (depth + 1)).operationalRoot.child
        stage.discovery.var false stage.discovery.fresh) continuation) :
    GeneratedStructuralBranchAccept
      ((constructStage (depth + 1)).operationalRoot.child
        stage.discovery.var true stage.discovery.fresh)
      (stage.discovery.relation.mapContinuation continuation) :=
  executedSiblingReduction_preservesAccept run continuation accepted

theorem fullReductionIsEstablishedConstitutiveStep {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    (run : ThreadedConstitutiveStageRun state stage) :
    executedFullPreservation run =
      EndogenousFlipDiscovery.fullStepPreservation stage.discovery :=
  executedFullPreservation_eq_discoveryFullStep run

theorem acceptedLeftPayloadUsesDiscovery {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    (run : ThreadedConstitutiveStageRun state stage)
    (payload : LocalAcceptedPayload run false) :
    (normalizeLocalAcceptedPayload run false payload).1 =
      stage.discovery.relation.mapContinuation payload.1 :=
  normalizeLocalAcceptedPayload_left_exact run payload

theorem absorbedSiblingRemainsViableAndDistinct {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    (run : ThreadedConstitutiveStageRun state stage) :
    (generatedStructuralBranchSystem
      (distinctGrowingDiscoveryFormula
        (constructStage (depth + 1)).searchIndex)).Viable
        stage.schedule.entry.source ∧
      (constructStage (depth + 1)).operationalRoot.child
          stage.discovery.var false stage.discovery.fresh ≠
        (constructStage (depth + 1)).operationalRoot.child
          stage.discovery.var true stage.discovery.fresh :=
  ⟨executedSourceSibling_viable run, executedSiblingStates_distinct run⟩

theorem executedOutputFeedsNextState {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    (run : ThreadedConstitutiveStageRun state stage) :
    stage.application.output.1 =
      run.nextRun.next.threadedAssignment.assignment :=
  executedOutput_eq_nextOperationalAssignment run

theorem publicStructuralCarrierCompleteZero
    (profile : StructuralObligation
      (executeConstitutiveResolution 0).feedbackRoleHistory) :
    List.Mem profile
      (structuralFrontier
        (executeConstitutiveResolution 0).feedbackRoleHistory) :=
  structuralFrontier_complete _ profile

theorem publicStructuralCarrierNoDuplicatesZero :
    (structuralFrontier
      (executeConstitutiveResolution 0).feedbackRoleHistory).Nodup :=
  structuralFrontier_nodup _

theorem publicOperationalCarrierCompleteZero
    (profile : OperationalObligation
      (executeConstitutiveResolution 0).feedbackRoleHistory) :
    List.Mem profile
      (operationalFrontier
        (executeConstitutiveResolution 0).feedbackRoleHistory) :=
  operationalFrontier_complete _ profile

theorem publicOperationalCarrierNoDuplicatesZero :
    (operationalFrontier
      (executeConstitutiveResolution 0).feedbackRoleHistory).Nodup :=
  operationalFrontier_nodup _

theorem actualStageTraceComesFromFrontiers {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    (run : ThreadedConstitutiveStageRun state stage) :
    executedStageWidthTrace run = [1, 2, 1] :=
  executedStageWidthTrace_exact run

theorem projectedObservedActionIsExecuted {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    (run : ThreadedConstitutiveStageRun state stage) :
    (executedStepToExtensionalView run).observedRetained =
      stage.schedule.entry.relation.mapContinuation
        (executedStepToExtensionalView run).observedSource :=
  extensionalView_observedOutput_exact run

theorem projectedTraceIsExecuted {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    (run : ThreadedConstitutiveStageRun state stage) :
    (executedStepToExtensionalView run).widthTrace =
      executedStageWidthTrace run :=
  extensionalView_widthTrace_exact run

/-- Equal width does not license a wrong retained target. -/
theorem wrongSingletonStillRejected {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    (run : ThreadedConstitutiveStageRun state stage) :
    (wrongSingleton run).length =
        (executedSiblingReduction run).retained.length ∧
      wrongSingleton run ≠ (executedSiblingReduction run).retained :=
  ⟨Eq.trans (wrongSingleton_width run)
      (executedSiblingReduction_width run).symm,
    wrongSingleton_ne_executedRetained run⟩

theorem separatorSameExecutedOutput :
    ExtensionalSeparator.preservingTransport.map
        ExtensionalSeparator.preservingView.observedSource =
      ExtensionalSeparator.collapsingTransport.map
        ExtensionalSeparator.collapsingView.observedSource :=
  ExtensionalSeparator.same_executed_output

theorem separatorProjectedViewsEqual :
    ExtensionalSeparator.preservingView =
      ExtensionalSeparator.collapsingView :=
  ExtensionalSeparator.same_extensional_stability_view

theorem separatorDifferentTotalAction :
    ExtensionalSeparator.preservingTransport.map true ≠
      ExtensionalSeparator.collapsingTransport.map true :=
  ExtensionalSeparator.different_arbitrary_continuation_action

theorem stateWidthViewCannotRecoverBothActions
    (recover : ExtensionalOperationalStabilityView
      ExtensionalSeparator.system → Bool → Bool)
    (leftExact : ∀ continuation,
      recover ExtensionalSeparator.preservingView continuation =
        ExtensionalSeparator.preservingTransport.map continuation)
    (rightExact : ∀ continuation,
      recover ExtensionalSeparator.collapsingView continuation =
        ExtensionalSeparator.collapsingTransport.map continuation) : False :=
  ExtensionalSeparator.operational_action_not_factors_through_extensional_view
    recover leftExact rightExact

end Tests.EndogenousOperationalStabilityRegression

/- AXIOM_AUDIT_BEGIN -/
#print axioms Tests.EndogenousOperationalStabilityRegression.publicEvidenceZero
#print axioms Tests.EndogenousOperationalStabilityRegression.publicStageCountZero
#print axioms Tests.EndogenousOperationalStabilityRegression.publicStructuralWidthZero
#print axioms Tests.EndogenousOperationalStabilityRegression.publicPendingWidthZero
#print axioms Tests.EndogenousOperationalStabilityRegression.publicRetainedWidthZero
#print axioms Tests.EndogenousOperationalStabilityRegression.publicTransientBoundZero
#print axioms Tests.EndogenousOperationalStabilityRegression.publicStrictSeparationZero
#print axioms Tests.EndogenousOperationalStabilityRegression.publicMeasuredFailedMajorityZero
#print axioms Tests.EndogenousOperationalStabilityRegression.normalizeEveryPublicStructuralProfileZero
#print axioms Tests.EndogenousOperationalStabilityRegression.measuredPrefixDeterminesAttempts
#print axioms Tests.EndogenousOperationalStabilityRegression.measuredPrefixContainsOnlyFailures
#print axioms Tests.EndogenousOperationalStabilityRegression.actualOpeningIsRelationFree
#print axioms Tests.EndogenousOperationalStabilityRegression.actualDiscoveryOutcomeIsAuthoritative
#print axioms Tests.EndogenousOperationalStabilityRegression.actualLeftActionUsesDiscovery
#print axioms Tests.EndogenousOperationalStabilityRegression.actualRightActionIsRetained
#print axioms Tests.EndogenousOperationalStabilityRegression.actualLeftActionPreservesCriterion
#print axioms Tests.EndogenousOperationalStabilityRegression.fullReductionIsEstablishedConstitutiveStep
#print axioms Tests.EndogenousOperationalStabilityRegression.acceptedLeftPayloadUsesDiscovery
#print axioms Tests.EndogenousOperationalStabilityRegression.absorbedSiblingRemainsViableAndDistinct
#print axioms Tests.EndogenousOperationalStabilityRegression.executedOutputFeedsNextState
#print axioms Tests.EndogenousOperationalStabilityRegression.publicStructuralCarrierCompleteZero
#print axioms Tests.EndogenousOperationalStabilityRegression.publicStructuralCarrierNoDuplicatesZero
#print axioms Tests.EndogenousOperationalStabilityRegression.publicOperationalCarrierCompleteZero
#print axioms Tests.EndogenousOperationalStabilityRegression.publicOperationalCarrierNoDuplicatesZero
#print axioms Tests.EndogenousOperationalStabilityRegression.actualStageTraceComesFromFrontiers
#print axioms Tests.EndogenousOperationalStabilityRegression.projectedObservedActionIsExecuted
#print axioms Tests.EndogenousOperationalStabilityRegression.projectedTraceIsExecuted
#print axioms Tests.EndogenousOperationalStabilityRegression.wrongSingletonStillRejected
#print axioms Tests.EndogenousOperationalStabilityRegression.separatorSameExecutedOutput
#print axioms Tests.EndogenousOperationalStabilityRegression.separatorProjectedViewsEqual
#print axioms Tests.EndogenousOperationalStabilityRegression.separatorDifferentTotalAction
#print axioms Tests.EndogenousOperationalStabilityRegression.stateWidthViewCannotRecoverBothActions
/- AXIOM_AUDIT_END -/
