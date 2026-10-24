import RelationalPerimeter.Agents.Neural.LearnedRuntimeAdapter

/-!
Regression checks for the independently learned artifact at the common
constitutive checking and runtime boundary.  The first admitted update consumes
the exact initial checked agent and the second consumes exactly the successor
returned by the first.  Rejected updates produce neither a checked action nor a
runtime successor.
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

theorem learned_extended_contract_uses_canonical_current_domain :
    LearnedExtendedOperationalContract.declaredCurrentInputs =
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

example : checkInitial learnedExecutableMetaContractInterface
      learnedReceivedExtendedArtifact =
    .ok learnedExtendedCheckSuccess :=
  checkInitial_accepts_learned_extended_artifact

example : checkLearnedExtendedSerializedUpdate learnedExtendedSerializedUpdate =
    .ok learnedExtendedDependentResult :=
  checkLearnedExtendedSerializedUpdate_accepts

example : learnedDependentIncrementalChecker.check LearnedAlignedCheckedAgent
      learnedExtendedRuntimeUpdate =
    .ok learnedExtendedDependentResult :=
  learnedDependentChecker_accepts_extended

theorem learned_successive_artifact_is_not_the_first_artifact :
    independentLearnedSecondSuccessorNetwork !=
      independentLearnedFirstSuccessorNetwork := by
  decide

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
    HEq analysis.target.transition
      (analysis.executed.receivedDecision.transportRequest
        analysis.executed.decoded.transitionExact).transition :=
  analysis.receivedTransition_installed

example {source : LearnedSerializedConstitutiveUpdate}
    (analysis : LearnedIncrementalEngineAnalysis source) :
    HEq analysis.target.execution
      (learnedAlignedTargetAnalysisForAdmittedNamingFromDecision
        analysis.executed.decoded.admittedStableNaming
        (analysis.executed.receivedDecision.transportRequest
          analysis.executed.decoded.transitionExact)).execution :=
  analysis.receivedExecution_installed

example {source : LearnedSerializedConstitutiveUpdate}
    (analysis : LearnedIncrementalEngineAnalysis source) :
    HEq analysis.target.structuralAssembly
      analysis.executed.decoded.admittedStableNaming.structuralAssembly :=
  analysis.receivedStructuralAssembly_installed

/-- A positive learned update may retain stable identities while adding one
new node.  The checker installs exactly the naming received in the admitted
serialized update. -/
theorem learned_aligned_naming_is_a_real_version_change :
    learnedAlignedSerializedNaming ≠ learnedInitialSerializedNaming := by
  decide

theorem learned_analysis_retains_received_target_network
    {source : LearnedSerializedConstitutiveUpdate}
    (analysis : LearnedIncrementalEngineAnalysis source) :
    source.targetNetwork = independentLearnedFirstSuccessorNetwork :=
  analysis.receivedTargetNetwork_exact

theorem learned_analysis_retains_received_stable_naming
    {source : LearnedSerializedConstitutiveUpdate}
    (analysis : LearnedIncrementalEngineAnalysis source) :
    HEq analysis.target.targetNaming
      analysis.executed.decoded.admittedStableNaming.naming :=
  analysis.receivedStableNaming_installed

theorem learned_installing_action_uses_executed_proposal :
    learnedAlignedInstallingAction.request =
      publicAgentActionChannel.command
        (learnedAlignedActionSourceState.system.proposal
          learnedAlignedActionSourceState.input) := by
  rfl

theorem learned_installing_action_preserves_required_proposal :
    learnedAlignedInstallingAction.request =
      publicAgentActionChannel.command
        (independentLearnedRequirementFamily.requiredProposal
          learnedAlignedActionSourceState.input.requirement
          learnedAlignedActionSourceState.input.context) :=
  learnedAlignedInstallingAction.request_required_exact

theorem learned_installing_action_consumes_authorization :
    learnedAlignedInstallingAction.authorization =
      learnedAlignedActionAuthorizationWitness := by
  rfl

theorem learned_installing_action_consumes_causal_roles :
    learnedAlignedInstallingAction.causal =
      learnedAlignedActionSourceCausalWitness := by
  rfl

theorem learned_installing_action_authorization_is_same_causal_port :
    learnedAlignedInstallingAction.causal.authorizationPort =
      learnedAlignedInstallingAction.authorization.authorizationPort :=
  learnedAlignedInstallingAction.authorizationPortExact

theorem learned_installing_effect_is_executed :
    (learnedAlignedInstallingEffect.successor,
      learnedAlignedInstallingEffect.event) =
      Agent.executeInput learnedInitialState.memory
        learnedAlignedInstallingAction.request :=
  learnedAlignedInstallingEffect_exact

theorem learned_successor_memory_is_effect_output :
    learnedAlignedState.memory =
      learnedAlignedInstallingEffect.successor := by
  rfl

theorem learned_successor_system_is_decoded_target :
    learnedAlignedState.system = learnedDecodedAlignedArtifact.system := by
  rfl

theorem learned_successor_input_is_received_input :
    learnedAlignedState.input = independentLearnedCertifiedInput := by
  rfl

theorem learned_runtime_installs_executed_successor_memory :
    learnedAlignedCertifiedRuntime.current.state.memory =
      learnedAlignedInstallingEffect.successor := by
  rw [learnedAlignedRuntime_state_exact]
  rfl

def substitutedLearnedStableNamingUpdate :
    LearnedSerializedConstitutiveUpdate :=
  learnedRenamedSerializedUpdate

def substitutedLearnedStableNamingRuntimeUpdate :
    learnedDependentIncrementalChecker.Update
      learnedInitialCertifiedRuntime.current :=
  .serialized substitutedLearnedStableNamingUpdate

def substitutedLearnedStableNamingCheckSuccess :
    GenericIncrementalCheckSuccess learnedIncrementalCheckerEngine
      substitutedLearnedStableNamingUpdate :=
  match exact : checkGenericIncrementalUpdate learnedIncrementalCheckerEngine
      substitutedLearnedStableNamingUpdate with
  | .ok success => success
  | .error _ => False.elim (by cases exact)

theorem substituted_learned_stable_naming_accepted_by_generic_checker :
    checkGenericIncrementalUpdate learnedIncrementalCheckerEngine
        substitutedLearnedStableNamingUpdate =
      .ok substitutedLearnedStableNamingCheckSuccess := by
  rfl

def substitutedLearnedStableNamingCertifiedRuntime : CertifiedRuntime
    learnedDependentIncrementalChecker learnedInitialCheckedAgent :=
  match submitUpdate learnedInitialCertifiedRuntime
      substitutedLearnedStableNamingRuntimeUpdate with
  | .ok runtime => runtime
  | .error _ => learnedInitialCertifiedRuntime

theorem substituted_learned_stable_naming_installed :
    submitUpdate learnedInitialCertifiedRuntime
        substitutedLearnedStableNamingRuntimeUpdate =
      .ok substitutedLearnedStableNamingCertifiedRuntime := by
  rfl

theorem substituted_learned_input_identity_installed :
    substitutedLearnedStableNamingCertifiedRuntime.current.certificate.basis.naming.inputSerial
        ⟨0, by decide⟩ = 1100 := by
  rfl

theorem substituted_learned_neuron_identity_installed :
    substitutedLearnedStableNamingCertifiedRuntime.current.certificate.basis.naming.neuronSerial
        ⟨0, by decide⟩ = 1110 := by
  rfl

theorem substituted_learned_output_identity_installed :
    substitutedLearnedStableNamingCertifiedRuntime.current.certificate.basis.naming.outputSerial
        ⟨0, by decide⟩ = 1120 := by
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

example : submitUpdate learnedAlignedCertifiedRuntime
      learnedExtendedSubmittedRuntimeUpdate =
    .ok learnedExtendedCertifiedRuntime :=
  submitUpdate_learned_extended_exact

example :
    learnedExtendedSubmittedRuntimeUpdate =
      .successive learnedAlignedCertifiedRuntime.current rfl
        learnedAlignedSubmittedCurrentContract_eq
        learnedAlignedCertifiedRuntime_current_exact
        learnedExtendedSerializedUpdate :=
  learnedExtendedSubmittedRuntimeUpdate_predecessor_exact

example : learnedExtendedCertifiedRuntime.current.state =
    learnedExtendedState :=
  learnedExtendedRuntime_state_exact

example : HEq learnedExtendedCertifiedRuntime.current.artifact
    learnedDecodedExtendedArtifact :=
  learnedExtendedRuntime_artifact_exact

example : learnedExtendedCertifiedRuntime.current.state.memory =
    (learnedExtendedInstallingActionFor
      learnedAlignedCertifiedRuntime.current.state.memory).result.1 :=
  learnedExtendedRuntime_consumes_first_successor_memory

example : EveryCheckedStepSatisfies learnedTwoStepCheckedTrace :=
  learnedTwoStepCheckedTrace_sound

example : EveryCheckedStepPreservesContracts learnedTwoStepCheckedTrace :=
  learnedTwoStepCheckedTrace_preservesContracts

example :
    learnedExtendedStepContractPreservation.transportPersistent
        .admittedIntent
        (ULift.up AdmittedIndependentLearnedIntent.preserveAuthorizedBehavior) =
      learnedExtendedTransportedIntent :=
  learnedExtendedStep_transportsIntent_exact

example : learnedExtendedCheckedAgent.certificate.authorizationWitness =
    learnedExtendedRecheckedAuthorization :=
  learnedExtendedCertificateAuthorization_is_rechecked

example : EveryRuntimeStepSatisfies
    learnedExtendedCertifiedRuntime.history :=
  learnedExtendedRuntime_checkedHistory

example : EveryRuntimeStepPreservesContracts
    learnedExtendedCertifiedRuntime.history :=
  learnedExtendedRuntime_preservedContracts

example : CertifiedRuntimeReachable learnedDependentIncrementalChecker
    learnedInitialCheckedAgent learnedExtendedCertifiedRuntime :=
  learnedExtendedCertifiedRuntime_reachable

example : CertifiedRuntimeAccessibility learnedExtendedCertifiedRuntime :=
  learnedExtendedCertifiedRuntime_accessibility

example : Not (Exists fun result =>
    learnedDependentIncrementalChecker.check LearnedAlignedCheckedAgent
        learnedWrongSuccessiveRuntimeUpdate = .ok result) :=
  learned_wrong_successive_rejected_without_checked_action

example : Not (Exists fun next =>
    submitUpdate learnedAlignedCertifiedRuntime
      learnedWrongSuccessiveSubmittedRuntimeUpdate = .ok next) :=
  learned_wrong_successive_rejected_without_successor

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

example : HEq learnedAlignedCertifiedRuntime.current.artifact
    learnedDecodedAlignedArtifact :=
  learnedAlignedRuntime_artifact_exact

example : HEq learnedAlignedCertifiedRuntime.current.certificate
    (assembleStateConstitution learnedAlignedTargetAnalysis.fragments) :=
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

theorem learned_local_update_transports_three_fragments :
    learnedTransportedStructuralFragments.length = 3 := by
  rfl

theorem learned_local_transport_reads_certified_source :
    learnedTransportedStructuralFragments =
      (structuralObservationSnapshot
        learnedInitialCheckedAgent.certificate).take 3 := by
  rfl

theorem learned_local_update_recomputes_ten_fragments :
    learnedRecomputedStructuralFragments.length = 10 := by
  rfl

theorem learned_local_assembly_matches_decoded_target :
    learnedCalculatedStructuralAssembly.observations =
      learnedPreCertificateGraph.targetObservations :=
  learnedCalculatedStructuralAssembly.targetExact

theorem learned_extended_update_transports_no_fragment :
    learnedRenamedTransportedStructuralFragments.length = 0 := by
  rfl

theorem learned_extended_update_recomputes_thirteen_fragments :
    learnedRenamedRecomputedStructuralFragments.length = 13 := by
  rfl

theorem learned_extended_assembly_matches_decoded_target :
    learnedRenamedCalculatedStructuralAssembly.observations =
      learnedRenamedPreCertificateGraph.targetObservations :=
  learnedRenamedCalculatedStructuralAssembly.targetExact

example :
    GenericIncrementalUpdateAccepted learnedIncrementalCheckerEngine
        learnedAlignedSerializedUpdate ↔
      LearnedFullUpdateAccepted learnedAlignedSerializedUpdate :=
  learnedAlignedIncrementalAndFullAcceptance_equivalent

example :
    learnedAlignedGenericIncrementalSuccess.checked.next =
      learnedAlignedFullRecheckSuccess.checked.next :=
  learnedAlignedIncrementalAndFullSuccessor_exact

example :
    learnedAlignedGenericIncrementalSuccess.checked.next.certificate =
      learnedAlignedFullRecheckSuccess.checked.next.certificate :=
  learnedAlignedIncrementalAndFullCertificate_exact

example :
    GenericIncrementalUpdateAccepted learnedIncrementalCheckerEngine
        learnedRenamedSerializedUpdate ↔
      LearnedFullUpdateAccepted learnedRenamedSerializedUpdate :=
  learnedRenamedIncrementalAndFullAcceptance_equivalent

example :
    learnedRenamedGenericIncrementalSuccess.checked.next =
      learnedRenamedFullRecheckSuccess.checked.next :=
  learnedRenamedIncrementalAndFullSuccessor_exact

example :
    learnedRenamedGenericIncrementalSuccess.checked.next.certificate =
      learnedRenamedFullRecheckSuccess.checked.next.certificate :=
  learnedRenamedIncrementalAndFullCertificate_exact

example {source : SerializedStableArtifactNaming}
    (admitted : LearnedAdmittedStableNaming source) :
    GenericIncrementalUpdateAccepted learnedIncrementalCheckerEngine
        (learnedSerializedUpdateForAdmittedNaming admitted) ↔
      LearnedFullUpdateAccepted
        (learnedSerializedUpdateForAdmittedNaming admitted) :=
  learnedAdmittedNamingIncrementalAndFullAcceptance_equivalent admitted

example :
    GenericIncrementalUpdateAccepted learnedIncrementalCheckerEngine
        learnedBypassSerializedUpdate ↔
      LearnedFullUpdateAccepted learnedBypassSerializedUpdate :=
  learnedBypassIncrementalAndFullAcceptance_equivalent

end ConstitutiveSearch.NeuralAgent.Tests
/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.NeuralAgent.Tests.learned_initial_contract_uses_canonical_current_domain
#print axioms ConstitutiveSearch.NeuralAgent.Tests.learned_aligned_contract_uses_canonical_current_domain
#print axioms ConstitutiveSearch.NeuralAgent.Tests.learned_extended_contract_uses_canonical_current_domain
#print axioms ConstitutiveSearch.NeuralAgent.Tests.learned_successive_artifact_is_not_the_first_artifact
#print axioms ConstitutiveSearch.NeuralAgent.Tests.learned_canonical_current_domain_has_four_cases
#print axioms ConstitutiveSearch.NeuralAgent.Tests.learned_initial_contract_covers_every_current_case
#print axioms ConstitutiveSearch.NeuralAgent.Tests.learned_aligned_contract_covers_every_current_case
#print axioms ConstitutiveSearch.NeuralAgent.Tests.learned_initial_causal_basis_covers_every_current_case
#print axioms ConstitutiveSearch.NeuralAgent.Tests.learned_aligned_causal_basis_covers_every_current_case
#print axioms ConstitutiveSearch.NeuralAgent.checkInitial_accepts_learned_artifact
#print axioms ConstitutiveSearch.NeuralAgent.learnedGenericChecker_accepts_aligned
#print axioms ConstitutiveSearch.NeuralAgent.learnedAlignedTargetAnalysisFromDecision_transition_exact
#print axioms ConstitutiveSearch.NeuralAgent.Tests.learned_aligned_naming_is_a_real_version_change
#print axioms ConstitutiveSearch.NeuralAgent.Tests.learned_analysis_retains_received_target_network
#print axioms ConstitutiveSearch.NeuralAgent.Tests.learned_analysis_retains_received_stable_naming
#print axioms ConstitutiveSearch.NeuralAgent.Tests.learned_installing_action_uses_executed_proposal
#print axioms ConstitutiveSearch.NeuralAgent.Tests.learned_installing_action_preserves_required_proposal
#print axioms ConstitutiveSearch.NeuralAgent.Tests.learned_installing_action_consumes_authorization
#print axioms ConstitutiveSearch.NeuralAgent.Tests.learned_installing_action_consumes_causal_roles
#print axioms ConstitutiveSearch.NeuralAgent.Tests.learned_installing_action_authorization_is_same_causal_port
#print axioms ConstitutiveSearch.NeuralAgent.Tests.learned_installing_effect_is_executed
#print axioms ConstitutiveSearch.NeuralAgent.Tests.learned_local_update_transports_three_fragments
#print axioms ConstitutiveSearch.NeuralAgent.Tests.learned_local_transport_reads_certified_source
#print axioms ConstitutiveSearch.NeuralAgent.Tests.learned_local_update_recomputes_ten_fragments
#print axioms ConstitutiveSearch.NeuralAgent.Tests.learned_local_assembly_matches_decoded_target
#print axioms ConstitutiveSearch.NeuralAgent.Tests.learned_extended_update_transports_no_fragment
#print axioms ConstitutiveSearch.NeuralAgent.Tests.learned_extended_update_recomputes_thirteen_fragments
#print axioms ConstitutiveSearch.NeuralAgent.Tests.learned_extended_assembly_matches_decoded_target
#print axioms ConstitutiveSearch.NeuralAgent.learnedAlignedIncrementalAndFullAcceptance_equivalent
#print axioms ConstitutiveSearch.NeuralAgent.learnedAlignedIncrementalAndFullSuccessor_exact
#print axioms ConstitutiveSearch.NeuralAgent.learnedAlignedIncrementalAndFullCertificate_exact
#print axioms ConstitutiveSearch.NeuralAgent.learnedRenamedIncrementalAndFullAcceptance_equivalent
#print axioms ConstitutiveSearch.NeuralAgent.learnedRenamedIncrementalAndFullSuccessor_exact
#print axioms ConstitutiveSearch.NeuralAgent.learnedRenamedIncrementalAndFullCertificate_exact
#print axioms ConstitutiveSearch.NeuralAgent.learnedAdmittedNamingIncrementalAndFullAcceptance_equivalent
#print axioms ConstitutiveSearch.NeuralAgent.learnedBypassIncrementalAndFullAcceptance_equivalent
#print axioms ConstitutiveSearch.NeuralAgent.Tests.learned_successor_memory_is_effect_output
#print axioms ConstitutiveSearch.NeuralAgent.Tests.learned_successor_system_is_decoded_target
#print axioms ConstitutiveSearch.NeuralAgent.Tests.learned_successor_input_is_received_input
#print axioms ConstitutiveSearch.NeuralAgent.Tests.learned_runtime_installs_executed_successor_memory
#print axioms ConstitutiveSearch.NeuralAgent.Tests.substitutedLearnedStableNamingUpdate
#print axioms ConstitutiveSearch.NeuralAgent.Tests.substituted_learned_stable_naming_accepted_by_generic_checker
#print axioms ConstitutiveSearch.NeuralAgent.Tests.substituted_learned_stable_naming_installed
#print axioms ConstitutiveSearch.NeuralAgent.Tests.substituted_learned_input_identity_installed
#print axioms ConstitutiveSearch.NeuralAgent.Tests.substituted_learned_neuron_identity_installed
#print axioms ConstitutiveSearch.NeuralAgent.Tests.substituted_learned_output_identity_installed
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
#print axioms ConstitutiveSearch.NeuralAgent.learnedDependentChecker_accepts_extended
#print axioms ConstitutiveSearch.NeuralAgent.learnedTwoStepCheckedTrace_sound
#print axioms ConstitutiveSearch.NeuralAgent.learnedTwoStepCheckedTrace_preservesContracts
#print axioms ConstitutiveSearch.NeuralAgent.learnedExtendedTransportedIntent
#print axioms ConstitutiveSearch.NeuralAgent.learnedExtendedRecheckedAuthorization
#print axioms ConstitutiveSearch.NeuralAgent.learnedExtendedStep_transportsIntent_exact
#print axioms ConstitutiveSearch.NeuralAgent.learnedExtendedCertificateAuthorization_is_rechecked
#print axioms ConstitutiveSearch.NeuralAgent.submitUpdate_learned_extended_exact
#print axioms ConstitutiveSearch.NeuralAgent.learnedExtendedSubmittedRuntimeUpdate_predecessor_exact
#print axioms ConstitutiveSearch.NeuralAgent.learnedExtendedRuntime_consumes_first_successor_memory
#print axioms ConstitutiveSearch.NeuralAgent.learned_wrong_successive_rejected_without_checked_action
#print axioms ConstitutiveSearch.NeuralAgent.learned_wrong_successive_rejected_without_successor
#print axioms ConstitutiveSearch.NeuralAgent.learnedExtendedCertifiedRuntime_reachable
#print axioms ConstitutiveSearch.NeuralAgent.learnedExtendedCertifiedRuntime_accessibility
#print axioms ConstitutiveSearch.NeuralAgent.learnedExtendedRuntime_checkedHistory
#print axioms ConstitutiveSearch.NeuralAgent.learnedExtendedRuntime_preservedContracts
/- AXIOM_AUDIT_END -/
