import RelationalPerimeter.Instances.GrowingFeedback

/-!
# Regression checks for growing reconstruction and causal feedback

These closed examples expose the executable trace while the general theorems
in the instance modules carry the scientific claims.
-/

namespace RelationalPerimeter.Tests.GrowingReconstructionRegression

open RelationalPerimeter.Instances.GrowingReconstruction
open RelationalPerimeter.Instances.GrowingFeedback

/-- At stage three, four distinct decoys precede the useful candidate. -/
theorem stageThree_candidates_exact :
    candidates 3 =
      [.decoy 3, .decoy 2, .decoy 1, .decoy 0, .useful] :=
  rfl

/-- The complete list, including `useful`, contains no repeated candidate. -/
theorem stageThree_candidates_nodup :
    (candidates 3).Nodup :=
  candidates_nodup 3

/-- The same run executes all five attempts before returning its relation. -/
theorem stageThree_attempts_exact :
    (growingRun 3).attempts = 5 :=
  growingRun_attempts_exact 3

/-- Four of those five calls are proof-carrying failed attempts. -/
theorem stageThree_failures_exact :
    (growingRun 3).failedAttempts = 4 :=
  growingRun_failedAttempts_exact 3

/-- At stage three, the four failures strictly outnumber the one success. -/
theorem stageThree_failures_strictMajority :
    (growingRun 3).failedAttempts + 1 = (growingRun 3).attempts ∧
      1 < (growingRun 3).failedAttempts :=
  growingRun_failures_strictMajority 2

/-- The stage-indexed witness is returned by the successful attempt. -/
theorem stageThree_relation_exact :
    (growingRun 3).relation? = some (.absorb 3) :=
  growingRun_relation_exact 3

/-- The operational reduction accepts arbitrary left continuations. -/
theorem stageThree_absorbs_left :
    stageReduction 3 (.inl 7) = 11 :=
  rfl

/-- The operational reduction also retains arbitrary right continuations. -/
theorem stageThree_retains_right :
    stageReduction 3 (.inr 8) = 8 :=
  rfl

/-- The concrete criterion accepts positive continuations. -/
theorem positive_left_is_accepted :
    growingSearchSystem.Criterion GrowingState.left 1 :=
  leftContinuation_accepted

/-- The same criterion rejects zero, so preservation is not vacuous. -/
theorem zero_left_is_rejected :
    ¬ growingSearchSystem.Criterion GrowingState.left 0 :=
  zeroLeftContinuation_rejected

/-- The first executed run produces the seed read by the next situation. -/
theorem first_feedback_seed_exact :
    (growingFeedbackStep.next initialState).nextSeed = 1 :=
  rfl

/-- The first reconstructed relation produces the retained decision. -/
theorem first_feedback_decision_exact :
    (growingFeedbackStep.next initialState).retainedTrace =
      [⟨0⟩] :=
  rfl

/-- Under decision retention, the next run filters one obligation. -/
theorem retained_feedback_attempts_exact :
    (reconstructionFromState (retainedState 0)).attempts = 2 :=
  retained_nextAttemptCount_exact 0

/-- Forgetting the produced decision leaves that obligation in the next run. -/
theorem forgotten_feedback_attempts_exact :
    (reconstructionFromState (forgottenState 0)).attempts = 3 :=
  forgotten_nextAttemptCount_exact 0

/-- The closed separator inherits the generic non-factorization result. -/
theorem decision_forgetting_is_insufficient :
    ¬ RelationalPerimeter.Computation.ValueFactorsThrough
      (visibleProjection 0) (nextAttemptCount 0) :=
  nextReconstruction_notFactors 0

end RelationalPerimeter.Tests.GrowingReconstructionRegression

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Tests.GrowingReconstructionRegression.stageThree_candidates_exact
#print axioms RelationalPerimeter.Tests.GrowingReconstructionRegression.stageThree_candidates_nodup
#print axioms RelationalPerimeter.Tests.GrowingReconstructionRegression.stageThree_attempts_exact
#print axioms RelationalPerimeter.Tests.GrowingReconstructionRegression.stageThree_failures_exact
#print axioms RelationalPerimeter.Tests.GrowingReconstructionRegression.stageThree_failures_strictMajority
#print axioms RelationalPerimeter.Tests.GrowingReconstructionRegression.stageThree_relation_exact
#print axioms RelationalPerimeter.Tests.GrowingReconstructionRegression.stageThree_absorbs_left
#print axioms RelationalPerimeter.Tests.GrowingReconstructionRegression.stageThree_retains_right
#print axioms RelationalPerimeter.Tests.GrowingReconstructionRegression.positive_left_is_accepted
#print axioms RelationalPerimeter.Tests.GrowingReconstructionRegression.zero_left_is_rejected
#print axioms RelationalPerimeter.Tests.GrowingReconstructionRegression.first_feedback_seed_exact
#print axioms RelationalPerimeter.Tests.GrowingReconstructionRegression.first_feedback_decision_exact
#print axioms RelationalPerimeter.Tests.GrowingReconstructionRegression.retained_feedback_attempts_exact
#print axioms RelationalPerimeter.Tests.GrowingReconstructionRegression.forgotten_feedback_attempts_exact
#print axioms RelationalPerimeter.Tests.GrowingReconstructionRegression.decision_forgetting_is_insufficient
/- AXIOM_AUDIT_END -/
