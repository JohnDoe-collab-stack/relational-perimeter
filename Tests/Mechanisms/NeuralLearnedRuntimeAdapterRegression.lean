import RelationalPerimeter.Agents.Neural.LearnedRuntimeAdapter

/-!
Regression checks for the independently learned artifact at the common
constitutive checking and runtime boundary.  Both candidates consume the exact
initial checked agent.  The authorization-preserving candidate is installed by
the generic incremental checker; the bypass is rejected before a successor can
exist.
-/
namespace ConstitutiveSearch.NeuralAgent.Tests
open ConstitutiveSearch.NeuralAgent

example : checkInitial learnedExecutableMetaContractInterface
      learnedReceivedInitialArtifact =
    .ok learnedInitialCheckSuccess :=
  checkInitial_accepts_learned_artifact

example : alignedUpdate.sourceArtifact =
    learnedInitialCheckedAgent.artifact.source := by
  rfl

example : bypassUpdate.sourceArtifact =
    learnedInitialCheckedAgent.artifact.source := by
  rfl

example : alignedUpdate.intent = bypassUpdate.intent := by
  rfl

example : GenericIncrementalUpdateAccepted learnedIncrementalCheckerEngine
    alignedUpdate :=
  learnedGenericChecker_accepts_aligned

example : checkGenericIncrementalUpdate learnedIncrementalCheckerEngine
      bypassUpdate =
    .error .missingConstitutiveDependency :=
  learnedGenericChecker_rejects_bypass

example : submitUpdate learnedInitialCertifiedRuntime
      learnedAlignedRuntimeUpdate =
    .ok learnedAlignedCertifiedRuntime :=
  submitUpdate_learned_aligned_exact

example : submitUpdate learnedInitialCertifiedRuntime
      learnedBypassRuntimeUpdate =
    .error .missingConstitutiveDependency :=
  submitUpdate_learned_bypass_rejected

example : Not (Exists fun next =>
    submitUpdate learnedInitialCertifiedRuntime
      learnedBypassRuntimeUpdate = .ok next) :=
  learned_bypass_rejected_without_successor

example : learnedAlignedCertifiedRuntime.current.state =
    learnedAlignedState :=
  learnedAlignedRuntime_state_exact

example : learnedAlignedCertifiedRuntime.current.artifact =
    learnedDecodedAlignedArtifact :=
  learnedAlignedRuntime_artifact_exact

example : learnedAlignedCertifiedRuntime.current.certificate =
    assembleStateConstitution learnedAlignedTargetAnalysis.fragments :=
  learnedAlignedRuntime_certificate_from_generic_checker

example : EveryRuntimeStepSatisfies
    learnedAlignedCertifiedRuntime.history :=
  learnedAlignedRuntime_checkedHistory

example : EveryRuntimeStepPreservesContracts
    learnedAlignedCertifiedRuntime.history :=
  learnedAlignedRuntime_preservedContracts

example : CertifiedRuntimeReachable learnedDependentIncrementalChecker
    learnedInitialCheckedAgent learnedAlignedCertifiedRuntime :=
  learnedAlignedCertifiedRuntime_reachable

example : CertifiedRuntimeAccessibility learnedAlignedCertifiedRuntime :=
  learnedAlignedCertifiedRuntime_accessibility

end ConstitutiveSearch.NeuralAgent.Tests
/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.NeuralAgent.checkInitial_accepts_learned_artifact
#print axioms ConstitutiveSearch.NeuralAgent.learnedGenericChecker_accepts_aligned
#print axioms ConstitutiveSearch.NeuralAgent.learnedGenericChecker_rejects_bypass
#print axioms ConstitutiveSearch.NeuralAgent.submitUpdate_learned_aligned_exact
#print axioms ConstitutiveSearch.NeuralAgent.submitUpdate_learned_bypass_rejected
#print axioms ConstitutiveSearch.NeuralAgent.learned_bypass_rejected_without_successor
#print axioms ConstitutiveSearch.NeuralAgent.learnedAlignedRuntime_state_exact
#print axioms ConstitutiveSearch.NeuralAgent.learnedAlignedRuntime_artifact_exact
#print axioms ConstitutiveSearch.NeuralAgent.learnedAlignedRuntime_certificate_from_generic_checker
#print axioms ConstitutiveSearch.NeuralAgent.learnedAlignedCertifiedRuntime_reachable
#print axioms ConstitutiveSearch.NeuralAgent.learnedAlignedCertifiedRuntime_accessibility
/- AXIOM_AUDIT_END -/
