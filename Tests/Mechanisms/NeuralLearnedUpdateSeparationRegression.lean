import RelationalPerimeter.Agents.Neural.FiniteCounterfactualDivergence

open ConstitutiveSearch NeuralAgent NativeMechanism

example : alignedUpdate.sourceArtifact = bypassUpdate.sourceArtifact := by
  rfl

example : alignedUpdate.intent = bypassUpdate.intent := by
  rfl

example : checkIndependentLearnedInitial independentLearnedInitialNetwork =
    .ok checkedIndependentLearnedInitial :=
  checkIndependentLearnedInitial_accepts_learned

example : CurrentBehaviorEquivalentAfterUpdate checkedIndependentLearnedInitial
    alignedUpdate bypassUpdate :=
  candidateCurrentBehaviorEquivalent

example : primaryAuthorizationConstitutivelyConsumed
    alignedUpdate.targetArtifact = true :=
  alignedUpdate_consumes_authorization

example : primaryAuthorizationConstitutivelyConsumed
    bypassUpdate.targetArtifact = false :=
  bypassUpdate_does_not_consume_authorization

example : checkIndependentLearnedUpdate checkedIndependentLearnedInitial
    alignedUpdate =
    .ok checkedAlignedUpdate :=
  checkIndependentLearnedUpdate_accepts_aligned

example : checkIndependentLearnedUpdate checkedIndependentLearnedInitial
    bypassUpdate =
    .error .missingConstitutiveDependency :=
  checkIndependentLearnedUpdate_rejects_bypass

example : simulateUncheckedUpdate checkedIndependentLearnedInitial alignedUpdate
    independentLearnedCounterfactualInput = [0, 0, 1] :=
  alignedCounterfactualResult_exact

example : simulateUncheckedUpdate checkedIndependentLearnedInitial bypassUpdate
    independentLearnedCounterfactualInput = [1, 0, 1] :=
  bypassCounterfactualResult_exact

example : FutureViolationWitness checkedIndependentLearnedInitial
    alignedUpdate bypassUpdate :=
  alignedBypassFutureViolation

example : ConstitutiveLatentBypassCertificate :=
  constitutiveChecker_detectsLatentBypass

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.NeuralAgent.alignedUpdate
#print axioms ConstitutiveSearch.NeuralAgent.bypassUpdate
#print axioms ConstitutiveSearch.NeuralAgent.checkIndependentLearnedInitial
#print axioms ConstitutiveSearch.NeuralAgent.candidateCurrentBehaviorEquivalent
#print axioms ConstitutiveSearch.NeuralAgent.primaryAuthorizationConstitutivelyConsumed
#print axioms ConstitutiveSearch.NeuralAgent.checkIndependentLearnedUpdate
#print axioms ConstitutiveSearch.NeuralAgent.alignedBypassFutureViolation
#print axioms ConstitutiveSearch.NeuralAgent.constitutiveChecker_detectsLatentBypass
/- AXIOM_AUDIT_END -/
