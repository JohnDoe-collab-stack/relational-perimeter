import RelationalPerimeter

/-!
# L3 regression: causal production and shared action/effect/successor

These checks expose the learned path through its generic reconfiguration
interfaces and through the exact transition production consumed by the
runtime.  They do not reconstruct either a target certificate or a successor.
-/
namespace Tests.Mechanisms.NeuralL3CausalProduction
open ConstitutiveSearch ConstitutiveSearch.NeuralAgent
open ConstitutiveSearch.NativeMechanism

theorem aligned_reconfiguration_is_produced_target :
    learnedAlignedReconfiguration.targetSystem =
      learnedDecodedAlignedArtifact.system :=
  learnedAlignedReconfiguration_target_exact

theorem extended_reconfiguration_is_produced_target :
    learnedExtendedReconfiguration.targetSystem =
      learnedDecodedExtendedArtifact.system :=
  learnedExtendedReconfiguration_target_exact

theorem aligned_proposal_is_derived_from_same_execution :
    learnedAlignedReconfiguration.targetSystem.proposal
        independentLearnedCertifiedInput =
      independentLearnedRequirementFamily.requiredProposal
        independentLearnedCertifiedInput.requirement
        independentLearnedCertifiedInput.context :=
  learnedAlignedReconfiguredProposalDerivation.proposal_exact

theorem extended_proposal_is_derived_from_same_execution :
    learnedExtendedReconfiguration.targetSystem.proposal
        independentLearnedCertifiedInput =
      independentLearnedRequirementFamily.requiredProposal
        independentLearnedCertifiedInput.requirement
        independentLearnedCertifiedInput.context :=
  learnedExtendedReconfiguredProposalDerivation.proposal_exact

theorem aligned_local_composition_is_nonidentity :
    learnedAlignedComposedSourceTransformation 0 = 1 :=
  learnedAlignedComposedSourceTransformation_nonidentity

theorem extended_local_composition_is_nonidentity :
    learnedExtendedComposedSourceTransformation 0 = 1 :=
  learnedExtendedComposedSourceTransformation_nonidentity

theorem aligned_source_occurrence_is_composed_output :
    (ActivationOccurrence.neuronOutput learnedAlignedPrimaryNeuron :
        ActivationOccurrence
          (learnedDecodedAlignedArtifact.system.run
            independentLearnedCertifiedInput)).value =
      learnedAlignedComposedSourceTransformation
        (ActivationOccurrence.receivedInput learnedAlignedContextPort :
          ActivationOccurrence
            (learnedDecodedAlignedArtifact.system.run
              independentLearnedCertifiedInput)).value :=
  learnedAlignedComposedSourceTransformation_output_exact

theorem extended_source_occurrence_is_composed_output :
    (ActivationOccurrence.neuronOutput learnedExtendedPrimaryNeuron :
        ActivationOccurrence
          (learnedDecodedExtendedArtifact.system.run
            independentLearnedCertifiedInput)).value =
      learnedExtendedComposedSourceTransformation
        (ActivationOccurrence.receivedInput learnedExtendedContextPort :
          ActivationOccurrence
            (learnedDecodedExtendedArtifact.system.run
              independentLearnedCertifiedInput)).value :=
  learnedExtendedComposedSourceTransformation_output_exact

def aligned_source_role_is_consumed :
    CausalRole learnedAlignedReconfiguration.targetSystem
      independentLearnedCertifiedInput
      (.receivedInput learnedAlignedRequiredMechanismTransport.sourcePort) :=
  learnedAlignedRequiredMechanismTransport.sourceRole

def aligned_requirement_role_is_consumed :
    CausalRole learnedAlignedReconfiguration.targetSystem
      independentLearnedCertifiedInput
      (.receivedInput learnedAlignedRequiredMechanismTransport.requirementPort) :=
  learnedAlignedRequiredMechanismTransport.requirementRole

def aligned_authorization_role_is_consumed :
    CausalRole learnedAlignedReconfiguration.targetSystem
      independentLearnedCertifiedInput
      (.receivedInput learnedAlignedRequiredMechanismTransport.authorizationPort) :=
  learnedAlignedRequiredMechanismTransport.authorizationRole

def extended_source_role_is_consumed :
    CausalRole learnedExtendedReconfiguration.targetSystem
      independentLearnedCertifiedInput
      (.receivedInput learnedExtendedRequiredMechanismTransport.sourcePort) :=
  learnedExtendedRequiredMechanismTransport.sourceRole

def extended_requirement_role_is_consumed :
    CausalRole learnedExtendedReconfiguration.targetSystem
      independentLearnedCertifiedInput
      (.receivedInput learnedExtendedRequiredMechanismTransport.requirementPort) :=
  learnedExtendedRequiredMechanismTransport.requirementRole

def extended_authorization_role_is_consumed :
    CausalRole learnedExtendedReconfiguration.targetSystem
      independentLearnedCertifiedInput
      (.receivedInput learnedExtendedRequiredMechanismTransport.authorizationPort) :=
  learnedExtendedRequiredMechanismTransport.authorizationRole

def alignedProduction := learnedReferenceTransitionProduction.production

theorem aligned_production_action_is_exact :
    alignedProduction.action = learnedAlignedInstallingAction :=
  alignedProduction.actionExact

def aligned_production_effect_consumes_exact_action :
    LearnedEffectWitness learnedAlignedActionSourceState
      alignedProduction.action :=
  alignedProduction.effect

theorem aligned_production_event_memory_are_same_effect :
    (alignedProduction.effect.successor,
        alignedProduction.effect.event) =
      Agent.executeInput learnedAlignedActionSourceState.memory
        alignedProduction.action.request :=
  alignedProduction.effect.effect_exact

theorem aligned_production_successor_is_same_effect :
    learnedProducedTransitionTarget learnedInitialCheckedAgent
        learnedOperationalTransition .installAligned alignedProduction =
      alignedProduction.effect.targetState := by
  rfl

def extendedProduction := learnedExtendedReferenceTransitionProduction.production

theorem extended_production_action_is_exact :
    extendedProduction.action =
      learnedExtendedInstallingActionFor
        LearnedAlignedCheckedAgent.state.memory :=
  extendedProduction.actionExact

def extended_production_effect_consumes_exact_action :
    LearnedEffectWitness
      (learnedExtendedActionSourceStateFor
        LearnedAlignedCheckedAgent.state.memory)
      extendedProduction.action :=
  extendedProduction.effect

theorem extended_production_successor_is_same_effect :
    learnedProducedTransitionTarget LearnedAlignedCheckedAgent
        learnedExtendedOperationalTransition
        learnedExtendedReferenceTransitionMaterial
        extendedProduction =
      extendedProduction.effect.targetState := by
  rfl

end Tests.Mechanisms.NeuralL3CausalProduction
/- AXIOM_AUDIT_BEGIN -/
#print axioms Tests.Mechanisms.NeuralL3CausalProduction.aligned_reconfiguration_is_produced_target
#print axioms Tests.Mechanisms.NeuralL3CausalProduction.extended_reconfiguration_is_produced_target
#print axioms Tests.Mechanisms.NeuralL3CausalProduction.aligned_proposal_is_derived_from_same_execution
#print axioms Tests.Mechanisms.NeuralL3CausalProduction.extended_proposal_is_derived_from_same_execution
#print axioms Tests.Mechanisms.NeuralL3CausalProduction.aligned_local_composition_is_nonidentity
#print axioms Tests.Mechanisms.NeuralL3CausalProduction.extended_local_composition_is_nonidentity
#print axioms Tests.Mechanisms.NeuralL3CausalProduction.aligned_source_occurrence_is_composed_output
#print axioms Tests.Mechanisms.NeuralL3CausalProduction.extended_source_occurrence_is_composed_output
#print axioms Tests.Mechanisms.NeuralL3CausalProduction.aligned_source_role_is_consumed
#print axioms Tests.Mechanisms.NeuralL3CausalProduction.aligned_requirement_role_is_consumed
#print axioms Tests.Mechanisms.NeuralL3CausalProduction.aligned_authorization_role_is_consumed
#print axioms Tests.Mechanisms.NeuralL3CausalProduction.extended_source_role_is_consumed
#print axioms Tests.Mechanisms.NeuralL3CausalProduction.extended_requirement_role_is_consumed
#print axioms Tests.Mechanisms.NeuralL3CausalProduction.extended_authorization_role_is_consumed
#print axioms Tests.Mechanisms.NeuralL3CausalProduction.aligned_production_action_is_exact
#print axioms Tests.Mechanisms.NeuralL3CausalProduction.aligned_production_effect_consumes_exact_action
#print axioms Tests.Mechanisms.NeuralL3CausalProduction.aligned_production_event_memory_are_same_effect
#print axioms Tests.Mechanisms.NeuralL3CausalProduction.aligned_production_successor_is_same_effect
#print axioms Tests.Mechanisms.NeuralL3CausalProduction.extended_production_action_is_exact
#print axioms Tests.Mechanisms.NeuralL3CausalProduction.extended_production_effect_consumes_exact_action
#print axioms Tests.Mechanisms.NeuralL3CausalProduction.extended_production_successor_is_same_effect
/- AXIOM_AUDIT_END -/
