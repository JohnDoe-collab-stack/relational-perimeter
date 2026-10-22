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

theorem learned_initial_contract_uses_canonical_current_domain :
    LearnedInitialOperationalContract.declaredCurrentInputs =
      learnedRuntimeDeclaredCurrentDomain.map
        IndependentLearnedInput.toRequirementInput := by
  rfl

theorem learned_aligned_contract_uses_canonical_current_domain :
    LearnedAlignedOperationalContract.declaredCurrentInputs =
      learnedRuntimeDeclaredCurrentDomain.map
        IndependentLearnedInput.toRequirementInput := by
  rfl

theorem learned_canonical_current_domain_has_four_cases :
    learnedRuntimeDeclaredCurrentDomain.length = 4 := by
  rfl

def learned_initial_contract_covers_every_current_case
    (current : IndependentLearnedCurrentCase) :
    Listed current.input.toRequirementInput
      LearnedInitialOperationalContract.declaredCurrentInputs :=
  independentLearnedDeclaredInputs_complete current

def learned_aligned_contract_covers_every_current_case
    (current : IndependentLearnedCurrentCase) :
    Listed current.input.toRequirementInput
      LearnedAlignedOperationalContract.declaredCurrentInputs :=
  independentLearnedDeclaredInputs_complete current

def learned_initial_causal_basis_covers_every_current_case
    (current : IndependentLearnedCurrentCase) :
    CausalCandidateCoverage learnedDecodedInitialArtifact
      learnedInitialStableNaming learnedInitialCausalReplacements
      current.input.toRequirementInput :=
  learnedInitialCausalCoverage _
    (independentLearnedDeclaredInputs_complete current)

def learned_aligned_causal_basis_covers_every_current_case
    (current : IndependentLearnedCurrentCase) :
    CausalCandidateCoverage learnedDecodedAlignedArtifact
      learnedAlignedStableNaming learnedAlignedCausalReplacements
      current.input.toRequirementInput :=
  learnedAlignedCausalCoverage _
    (independentLearnedDeclaredInputs_complete current)

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
    learnedAlignedSerializedUpdate :=
  learnedGenericChecker_accepts_aligned

example : LearnedIncrementalEngineLocalConditions
    learnedAlignedSerializedUpdate :=
  (analyzeLearnedRuntimeUpdate_complete learnedAlignedSerializedUpdate).mp
    ((checkGenericIncrementalUpdate_complete_for_local_conditions
      learnedIncrementalCheckerEngine learnedAlignedSerializedUpdate).mp
        learnedGenericChecker_accepts_aligned)

example (source : LearnedSerializedConstitutiveUpdate) :
    GenericIncrementalUpdateAccepted learnedIncrementalCheckerEngine source ↔
      LearnedIncrementalEngineLocalConditions source :=
  (checkGenericIncrementalUpdate_complete_for_local_conditions
    learnedIncrementalCheckerEngine source).trans
      (analyzeLearnedRuntimeUpdate_complete source)

example (decision : LearnedAlignedTransitionDecision) :
    (learnedAlignedTargetAnalysisFromDecision decision).transition =
      decision.transition :=
  learnedAlignedTargetAnalysisFromDecision_transition_exact decision

example {source : LearnedSerializedConstitutiveUpdate}
    (analysis : LearnedIncrementalEngineAnalysis source) :
    analysis.target.transition =
      (analysis.executed.receivedDecision.transportRequest
        analysis.executed.decoded.transitionExact).transition := by
  rfl

example {source : LearnedSerializedConstitutiveUpdate}
    (analysis : LearnedIncrementalEngineAnalysis source) :
    analysis.target.execution = analysis.executed.executedSuccessor := by
  rfl

example {source : LearnedSerializedConstitutiveUpdate}
    (analysis : LearnedIncrementalEngineAnalysis source) :
    analysis.target.structuralAssembly =
      analysis.executed.structuralRecalculation := by
  rfl

example : checkGenericIncrementalUpdate learnedIncrementalCheckerEngine
      learnedBypassSerializedUpdate =
    .error .missingConstitutiveDependency :=
  learnedGenericChecker_rejects_bypass

theorem learned_aligned_serialized_update_carries_exact_target :
    learnedAlignedSerializedUpdate.targetNetwork =
    alignedUpdate.targetArtifact := by
  rfl

theorem learned_bypass_serialized_update_carries_exact_target :
    learnedBypassSerializedUpdate.targetNetwork =
    bypassUpdate.targetArtifact := by
  rfl

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
#print axioms ConstitutiveSearch.NeuralAgent.Tests.learned_initial_contract_uses_canonical_current_domain
#print axioms ConstitutiveSearch.NeuralAgent.Tests.learned_aligned_contract_uses_canonical_current_domain
#print axioms ConstitutiveSearch.NeuralAgent.Tests.learned_canonical_current_domain_has_four_cases
#print axioms ConstitutiveSearch.NeuralAgent.Tests.learned_initial_contract_covers_every_current_case
#print axioms ConstitutiveSearch.NeuralAgent.Tests.learned_aligned_contract_covers_every_current_case
#print axioms ConstitutiveSearch.NeuralAgent.Tests.learned_initial_causal_basis_covers_every_current_case
#print axioms ConstitutiveSearch.NeuralAgent.Tests.learned_aligned_causal_basis_covers_every_current_case
#print axioms ConstitutiveSearch.NeuralAgent.checkInitial_accepts_learned_artifact
#print axioms ConstitutiveSearch.NeuralAgent.learnedGenericChecker_accepts_aligned
#print axioms ConstitutiveSearch.NeuralAgent.learnedAlignedTargetAnalysisFromDecision_transition_exact
#print axioms ConstitutiveSearch.NeuralAgent.learnedGenericChecker_rejects_bypass
#print axioms ConstitutiveSearch.NeuralAgent.Tests.learned_aligned_serialized_update_carries_exact_target
#print axioms ConstitutiveSearch.NeuralAgent.Tests.learned_bypass_serialized_update_carries_exact_target
#print axioms ConstitutiveSearch.NeuralAgent.submitUpdate_learned_aligned_exact
#print axioms ConstitutiveSearch.NeuralAgent.submitUpdate_learned_bypass_rejected
#print axioms ConstitutiveSearch.NeuralAgent.learned_bypass_rejected_without_successor
#print axioms ConstitutiveSearch.NeuralAgent.learnedAlignedRuntime_state_exact
#print axioms ConstitutiveSearch.NeuralAgent.learnedAlignedRuntime_artifact_exact
#print axioms ConstitutiveSearch.NeuralAgent.learnedAlignedRuntime_certificate_from_generic_checker
#print axioms ConstitutiveSearch.NeuralAgent.learnedAlignedCertifiedRuntime_reachable
#print axioms ConstitutiveSearch.NeuralAgent.learnedAlignedCertifiedRuntime_accessibility
/- AXIOM_AUDIT_END -/
