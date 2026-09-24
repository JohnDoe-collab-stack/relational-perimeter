import RelationalPerimeter.Computation.Phenomenon
import RelationalPerimeter.Instances.GrowingFeedback
import RelationalPerimeter.Instances.PerimetralComputation

/-!
# Concrete endogenous operational decomposition

The growing reconstruction supplies a closed instance of the generic package.
It also records the unbounded failed prefix and the feedback separator.  The
perimetral adapter places the same operational phenomenon after a unary
constitutive history step.
-/

namespace RelationalPerimeter.Instances.EndogenousOperationalDecomposition

open RelationalPerimeter.Computation
open RelationalPerimeter.Instances.GrowingReconstruction
open RelationalPerimeter.Instances.GrowingFeedback
open RelationalPerimeter.Instances.PerimetralComputation

/-- Full operational-decomposition witness at every stage. -/
def growingDecomposition (stage : Nat) :
    EndogenousOperationalDecomposition
      growingSearchSystem GrowingCandidate GrowingRelation
      .parent .left .right where
  opening := growingOpening
  criterionOpening := growingCriterionOpening
  reconstruction := growingReconstruction stage
  run := growingRun stage
  success := SuccessfulRun.ofRelationExact
    (growingRun stage) (.absorb stage) (growingRun_relation_exact stage)
  failedCandidate := .decoy stage
  failedCandidateExact := rfl
  failedCandidateWasTested := by
    refine ⟨
      (decoyIndices stage).map GrowingCandidate.decoy ++ [.useful],
      ?_⟩
    exact growingRun_tested_exact stage
  action := growingAction
  actionPreserves := growingPreservingAction
  alternativesDistinct := left_ne_right
  absorbedContinuation := leftContinuation
  absorbedContinuationAccepted := leftContinuation_accepted

/--
The concrete family packages the operational witness, distinct decoys, exact
work, strict growth, and the feedback non-factorization result.
-/
structure GrowingPhenomenon (stage : Nat) where
  decomposition :
    EndogenousOperationalDecomposition
      growingSearchSystem GrowingCandidate GrowingRelation
      .parent .left .right
  decoysDistinct : (decoys stage).Nodup
  attemptsExact : decomposition.run.attempts = stage + 2
  failuresExact : decomposition.run.failedAttempts = stage + 1
  attemptsGrow :
    decomposition.run.attempts < (growingRun (stage + 1)).attempts
  producedState : GrowingFeedbackState
  producedStateExact :
    producedState = growingFeedbackStep.next (feedbackInitialState stage)
  feedbackRunIsDecompositionRun :
    HEq
      (reconstructionFromState (feedbackInitialState stage))
      decomposition.run
  producedDecisionExact : producedState.retainedTrace = [⟨stage⟩]
  nextExtractionConsumesProducedDecision :
    extractedCandidatesFromState producedState =
      filterCandidatesByDecisions [⟨stage⟩] (candidates (stage + 1))
  nextReconstructionDependsOnProducedDecision :
    ¬ ValueFactorsThrough (visibleProjection stage) (nextAttemptCount stage)

/-- Construct the complete witness directly from executable definitions. -/
def growingPhenomenon (stage : Nat) : GrowingPhenomenon stage :=
  { decomposition := growingDecomposition stage
    decoysDistinct := decoys_nodup stage
    attemptsExact := growingRun_attempts_exact stage
    failuresExact := growingRun_failedAttempts_exact stage
    attemptsGrow := growingRun_attempts_strict stage
    producedState := growingFeedbackStep.next (feedbackInitialState stage)
    producedStateExact := rfl
    feedbackRunIsDecompositionRun := by
      rw [feedbackInitial_run_exact]
      change HEq (growingRun stage) (growingRun stage)
      rfl
    producedDecisionExact := nextState_decision_exact stage
    nextExtractionConsumesProducedDecision :=
      secondExtraction_consumes_producedDecision stage
    nextReconstructionDependsOnProducedDecision :=
      nextReconstruction_notFactors stage }

/-- The relation exposed by the package is exactly the relation found by the run. -/
theorem growingDecomposition_relation_exact (stage : Nat) :
    (growingDecomposition stage).producedRelation = .absorb stage := by
  have produced :=
    (growingDecomposition stage).relation_comes_from_executed_run
  have expected := growingRun_relation_exact stage
  exact Option.some.inj (produced.symm.trans expected)

/-- The concrete reduction is defined on every structural parent continuation. -/
theorem growingReduction_left_exact
    (stage value : Nat) :
    (growingDecomposition stage).reduction (.inl value) =
      value + stage + 1 := by
  unfold EndogenousOperationalDecomposition.reduction
  rw [growingDecomposition_relation_exact]
  rfl

/-- The concrete reduction retains every right continuation unchanged. -/
theorem growingReduction_right_exact
    (stage value : Nat) :
    (growingDecomposition stage).reduction (.inr value) = value :=
  rfl

end RelationalPerimeter.Instances.EndogenousOperationalDecomposition

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Instances.EndogenousOperationalDecomposition.growingDecomposition
#print axioms RelationalPerimeter.Instances.EndogenousOperationalDecomposition.GrowingPhenomenon
#print axioms RelationalPerimeter.Instances.EndogenousOperationalDecomposition.growingPhenomenon
#print axioms RelationalPerimeter.Instances.EndogenousOperationalDecomposition.growingDecomposition_relation_exact
#print axioms RelationalPerimeter.Instances.EndogenousOperationalDecomposition.growingReduction_left_exact
#print axioms RelationalPerimeter.Instances.EndogenousOperationalDecomposition.growingReduction_right_exact
/- AXIOM_AUDIT_END -/
