import RelationalPerimeter.Agents.Neural.ConstitutiveAlignment

namespace Tests.Mechanisms.NeuralConstitutiveAlignmentRegression
open ConstitutiveSearch.NeuralAgent

def scopeZeroDirectInput : PublicRequirementInput := ⟨.scopeZero, .direct⟩
def scopeOneDirectInput : PublicRequirementInput := ⟨.scopeOne, .direct⟩

def completePublicChain :
    PublicConstitutiveAlignmentCertificate scopeZeroDirectInput scopeOneDirectInput
      [scopeZeroDirectInput, scopeOneDirectInput] :=
  constitutive_alignment scopeZeroDirectInput scopeOneDirectInput [scopeZeroDirectInput, scopeOneDirectInput]

/-- C15: the public presentation is obtained from the generic scientific
decomposition; it is not a second public-only theorem. -/
def completePublicScientificDecomposition :=
  publicConstitutiveScientificDecomposition scopeZeroDirectInput
    scopeOneDirectInput [scopeZeroDirectInput, scopeOneDirectInput]

theorem scientific_received_action_contract_is_exact :
    completePublicScientificDecomposition.receivedActionContract =
      publicAgentActionChannel :=
  completePublicScientificDecomposition.receivedActionContractExact

def scientific_produced_incorporation_is_interventional :
    ConstitutiveSearch.NativeMechanism.CausalRole publicRequirementSystem
      scopeZeroDirectInput
      (.receivedInput publicRequirementEncoding.port) :=
  completePublicScientificDecomposition.producedCausalIncorporation

theorem scientific_action_is_produced_by_execution :
    completePublicChain.action.result =
      ConstitutiveSearch.Agent.executeInput publicActionMemory
        completePublicChain.action.request :=
  completePublicScientificDecomposition.producedActionExecution

theorem scientific_initial_proposal_is_derived :
    publicRequirementSystem.proposal scopeZeroDirectInput =
      publicRequirementFamily.requiredProposal
        scopeZeroDirectInput.requirement scopeZeroDirectInput.context :=
  completePublicScientificDecomposition.derivedInitialProposal

theorem scientific_head_authorization_is_only_the_incorporated_permission :
    completePublicScientificDecomposition.authorizedHeadPermission =
      completePublicChain.headStage.action.certificate.configuration.authorization :=
  completePublicScientificDecomposition.authorizedHeadPermissionExact

theorem scientific_future_is_preserved :
    ConstitutiveSearch.ContinuationSignatures.FutureEquivalent
      publicAlignmentFutureContract
      completePublicChain.forgottenLeftExecution.output
      completePublicChain.forgottenRightExecution.output :=
  completePublicScientificDecomposition.preservedFuture

theorem scientific_left_forgetting_trace_is_executed :
    completePublicChain.forgottenLeftExecution.trace =
      (publicHistoricalForgettingProgram scopeZeroDirectInput
        [scopeOneDirectInput, scopeZeroDirectInput, scopeOneDirectInput]).execute
          completePublicChain.forgottenLeftInput.origin :=
  completePublicScientificDecomposition.producedLeftForgettingTrace

theorem scientific_left_forgetting_output_consumes_trace :
    completePublicChain.forgottenLeftExecution.output =
      (publicHistoricalForgettingProgram scopeZeroDirectInput
        [scopeOneDirectInput, scopeZeroDirectInput, scopeOneDirectInput]).reduce
          completePublicChain.forgottenLeftInput.origin
          completePublicChain.forgottenLeftExecution.trace :=
  completePublicScientificDecomposition.producedLeftForgettingReduction

theorem scientific_historical_distinction_is_forgotten :
    completePublicChain.forgottenLeftInput.origin ≠
        completePublicChain.forgottenRightInput.origin ∧
      completePublicChain.forgottenLeftExecution.output =
        completePublicChain.forgottenRightExecution.output :=
  ⟨completePublicScientificDecomposition.forgottenOriginsDistinct,
    completePublicScientificDecomposition.forgottenOutputsEqual⟩

theorem scientific_forgotten_origin_is_irrecoverable
    (recover : ConstitutiveSearch.Agent.Memory -> PublicHistoricalOrigin)
    (leftExact :
      recover completePublicChain.forgottenLeftExecution.output =
        completePublicChain.forgottenLeftInput.origin.origin)
    (rightExact :
      recover completePublicChain.forgottenRightExecution.output =
        completePublicChain.forgottenRightInput.origin.origin) : False :=
  public_executed_forgetting_origin_not_recoverable
    scopeZeroDirectInput
    [scopeOneDirectInput, scopeZeroDirectInput, scopeOneDirectInput]
    recover leftExact rightExact

/-! C16: explicit non-regression of the dependent witness chain. -/

/-- Production and consumption use one dependent chain of witnesses.  Each
later component is typed by the preceding component rather than by a rebuilt
value. -/
def c16_same_witness_is_produced_and_consumed :
    Sigma fun incorporation : RequirementIncorporation
      publicRequirementEncoding scopeZeroDirectInput =>
    Sigma fun transformation : RequirementSignalTransformation
      publicRequirementDecoder incorporation =>
    Sigma fun action : ActionRealization publicAgentActionChannel
      transformation publicActionMemory =>
    EffectRealization action :=
  ⟨completePublicChain.incorporation,
    completePublicChain.transformation,
    completePublicChain.action,
    completePublicChain.effect⟩

/-- The proposal occurrence remains an occurrence indexed by the exact system
and input.  Its read value is exposed separately. -/
def c16_exact_proposal_occurrence :
    ConstitutiveSearch.NativeMechanism.ProposalOccurrence
      publicRequirementSystem scopeZeroDirectInput :=
  publicRequirementSystem.proposalOccurrence scopeZeroDirectInput

theorem c16_occurrence_value_is_separate_readout :
    c16_exact_proposal_occurrence.value =
      publicRequirementSystem.proposal scopeZeroDirectInput :=
  c16_exact_proposal_occurrence.valueExact

theorem c16_action_is_the_actual_execution :
    completePublicChain.action.result =
      ConstitutiveSearch.Agent.executeInput publicActionMemory
        completePublicChain.action.request :=
  completePublicChain.action.execution_exact

theorem c16_effect_is_the_produced_execution_result :
    (completePublicChain.effect.successor,
      completePublicChain.effect.event) =
      ConstitutiveSearch.Agent.executeInput publicActionMemory
        completePublicChain.action.request :=
  completePublicChain.effect.effect_exact

theorem c16_produced_successor_is_transmitted :
    completePublicChain.initialState.memory =
      completePublicChain.effect.successor :=
  completePublicChain.effectConsumed

/-- This is the actual tail stored by the terminal certificate.  Its source is
definitionally the state produced by the first stored stage. -/
def c16_actual_tail_consumes_produced_state :
    ReconfiguredInteractionHistory publicReconfigurationBuilder
      publicAgentActionChannel publicReconfigurationCertificateForState
      completePublicChain.continuation.headStage.nextState
      [scopeZeroDirectInput, scopeOneDirectInput] :=
  completePublicChain.continuation.tail

/-- Consequently the second actual reconfiguration is indexed by the system,
input, and memory produced by the first actual reconfiguration. -/
def c16_second_reconfiguration_consumes_previous_production :
    ReconfiguredCausalStage publicReconfigurationBuilder
      publicAgentActionChannel publicReconfigurationCertificateForState
      completePublicChain.continuation.headStage.nextState
      scopeZeroDirectInput :=
  c16_actual_tail_consumes_produced_state.headStage

theorem public_chain_is_generic_specialization :
    completePublicChain =
      assembleConstitutiveAlignment publicRequirementEncoding
        publicRequirementDecoder publicAgentActionChannel
        publicReconfigurationBuilder publicReconfigurationCertificateForState
        publicActionMemory
        (publicHistoricalForgettingProgram scopeZeroDirectInput
          [scopeOneDirectInput, scopeZeroDirectInput, scopeOneDirectInput])
        ReconfiguredExecutionState.memory
        publicAlignmentFutureContract
        (publicRequirementIncorporation scopeZeroDirectInput)
        (publicRequirementSignalTransformation scopeZeroDirectInput)
        (publicAction scopeZeroDirectInput) (publicEffect scopeZeroDirectInput)
        (publicInitialReconfiguredState scopeZeroDirectInput) rfl rfl rfl
        (publicReconfiguredInteractionHistory scopeZeroDirectInput
          [scopeOneDirectInput, scopeZeroDirectInput, scopeOneDirectInput])
        (publicAlignmentForgettingPolicy scopeZeroDirectInput
          [scopeOneDirectInput, scopeZeroDirectInput, scopeOneDirectInput]) :=
  rfl

theorem alignment_consumes_executed_effect :
    completePublicChain.initialState.memory =
      completePublicChain.effect.successor :=
  completePublicChain.effectConsumed

theorem alignment_continuation_uses_required_requests :
    completePublicChain.continuation.requests =
      requiredRequests publicAgentActionChannel
        [scopeOneDirectInput, scopeZeroDirectInput, scopeOneDirectInput] :=
  completePublicChain.continuationRequestsExact

theorem alignment_continuation_is_exact_execution :
    (completePublicChain.continuation.finalState.memory,
      completePublicChain.continuation.events) =
      ConstitutiveSearch.Agent.executeRequests
        completePublicChain.initialState.memory
        completePublicChain.continuation.requests :=
  completePublicChain.continuationExecutionExact

theorem alignment_forgetting_inputs_remain_distinct :
    completePublicChain.forgottenLeftInput ≠
      completePublicChain.forgottenRightInput :=
  completePublicChain.forgottenInputsDistinct

theorem alignment_left_forgetting_executes_to_continuation :
    completePublicChain.forgottenLeftExecution.output =
      completePublicChain.continuation.finalState.memory :=
  completePublicChain.forgottenLeftExecutionExact

theorem alignment_right_forgetting_executes_to_continuation :
    completePublicChain.forgottenRightExecution.output =
      completePublicChain.continuation.finalState.memory :=
  completePublicChain.forgottenRightExecutionExact

theorem alignment_forgetting_equality_is_computed :
    completePublicChain.forgottenLeftExecution.output =
      completePublicChain.forgottenRightExecution.output :=
  completePublicChain.forgottenStatesEqual

theorem alignment_forgets_origin_but_preserves_future :
    ConstitutiveSearch.ContinuationSignatures.FutureEquivalent
      publicAlignmentFutureContract
      completePublicChain.forgottenLeftExecution.output
      completePublicChain.forgottenRightExecution.output :=
  completePublicChain.forgottenFutureEquivalent

theorem alignment_forgetting_cannot_recover_both_origins
    (recover : ConstitutiveSearch.Agent.Memory -> PublicHistoricalOrigin)
    (leftExact :
      recover completePublicChain.forgottenLeftExecution.output =
        completePublicChain.forgottenLeftInput.origin.origin)
    (rightExact :
      recover completePublicChain.forgottenRightExecution.output =
        completePublicChain.forgottenRightInput.origin.origin) : False :=
  public_executed_forgetting_origin_not_recoverable
    scopeZeroDirectInput
    [scopeOneDirectInput, scopeZeroDirectInput, scopeOneDirectInput]
    recover leftExact rightExact

theorem substantive_instance_has_multiple_requirements :
    publicSubstantiveSource.requirement ≠
      publicSubstantiveNext.requirement :=
  publicSubstantiveInstance.requirementsDistinct

theorem substantive_instance_has_multiple_contexts :
    publicSubstantiveSource.context ≠
      publicSubstantiveContextualNext.context :=
  publicSubstantiveInstance.contextsDistinct

theorem substantive_instance_has_contextual_proposals :
    publicRequirementFamily.requiredProposal
        publicSubstantiveSource.requirement publicSubstantiveSource.context ≠
      publicRequirementFamily.requiredProposal
        publicSubstantiveContextualNext.requirement
        publicSubstantiveContextualNext.context :=
  publicSubstantiveInstance.contextualProposalsDistinct

theorem substantive_instance_has_nontrivial_intermediate_representation :
    (publicReconfiguration publicSubstantiveSource
      publicSubstantiveNext).targetSystem.producedCount = 2 :=
  publicSubstantiveInstance.reconfiguredOutputCountNontrivial

theorem substantive_instance_transformation_is_not_identity :
    publicRequirementEncoding.code publicSubstantiveSource.requirement
        publicSubstantiveSource.context ≠
      publicRequirementDecoder.terminalRepresentation
        publicSubstantiveSource.requirement publicSubstantiveSource.context :=
  publicSubstantiveInstance.signalTransformationNonidentity

theorem substantive_instance_action_preserves_distinction :
    DistinctAccordingToActionContract publicAgentActionChannel
      (publicAction publicSubstantiveSource).request
      (publicAction publicSubstantiveNext).request :=
  publicSubstantiveInstance.actionPreservesRequiredDistinction

theorem substantive_instance_reconfiguration_depends_on_source_state :
    (publicReconfiguration ⟨.scopeZero, .direct⟩
        ⟨.scopeZero, .direct⟩).targetSystem.outputValues
        ⟨.scopeZero, .direct⟩ ≠
      (publicReconfiguration ⟨.scopeOne, .direct⟩
        ⟨.scopeZero, .direct⟩).targetSystem.outputValues
        ⟨.scopeZero, .direct⟩ :=
  publicSubstantiveInstance.sourceStateChangesReconfiguration

theorem substantive_instance_reconfiguration_depends_on_next_requirement :
    (publicReconfiguration ⟨.scopeZero, .direct⟩
        ⟨.scopeZero, .direct⟩).targetSystem.outputValues
        ⟨.scopeZero, .direct⟩ ≠
      (publicReconfiguration ⟨.scopeZero, .direct⟩
        ⟨.scopeOne, .direct⟩).targetSystem.outputValues
        ⟨.scopeOne, .direct⟩ :=
  publicSubstantiveInstance.nextRequirementChangesReconfiguration

theorem substantive_instance_reconfiguration_depends_on_next_context :
    (publicReconfiguration ⟨.scopeZero, .direct⟩
        ⟨.scopeZero, .direct⟩).targetSystem.outputValues
        ⟨.scopeZero, .direct⟩ ≠
      (publicReconfiguration ⟨.scopeZero, .direct⟩
        ⟨.scopeZero, .reversed⟩).targetSystem.outputValues
        ⟨.scopeZero, .reversed⟩ :=
  publicSubstantiveInstance.nextContextChangesReconfiguration

theorem substantive_instance_authorization_is_consumed :
    ((publicReconfiguration publicSubstantiveSource
        publicSubstantiveNext).targetSystem.encode
        publicSubstantiveNext).read
        (publicRequiredMechanismTransport publicSubstantiveSource
          publicSubstantiveNext).authorizationPort =
      publicReconfigurationBuilder.authorizationCode
        publicSubstantiveNext
        (publicReconfiguration publicSubstantiveSource
          publicSubstantiveNext).permission :=
  publicSubstantiveInstance.authorizationConsumed

theorem substantive_instance_continuation_has_two_steps :
    publicSubstantiveAlignment.continuation.requests.length = 2 :=
  publicSubstantiveInstance.continuationHasTwoSteps

theorem substantive_instance_executes_forgetting :
    publicSubstantiveAlignment.forgottenLeftExecution.output =
      publicSubstantiveAlignment.continuation.finalState.memory :=
  publicSubstantiveInstance.forgettingExecuted

theorem substantive_instance_memory_is_strictly_reduced
    (recover : ConstitutiveSearch.Agent.Memory -> PublicHistoricalOrigin)
    (leftExact :
      recover publicSubstantiveAlignment.forgottenLeftExecution.output =
        publicSubstantiveAlignment.forgottenLeftInput.origin.origin)
    (rightExact :
      recover publicSubstantiveAlignment.forgottenRightExecution.output =
        publicSubstantiveAlignment.forgottenRightInput.origin.origin) : False :=
  publicSubstantiveInstance.memoryStrictlyReduced recover leftExact rightExact

theorem substantive_instance_executes_admission :
    publicAlignmentFutureContract.enabled
      publicSubstantiveAlignment.continuation.finalState.memory
      publicTerminalAdmittedRequest = true :=
  publicSubstantiveInstance.futureAdmissionExecuted

theorem substantive_instance_executes_refusal :
    publicAlignmentFutureContract.enabled
      publicSubstantiveAlignment.continuation.finalState.memory
      publicTerminalRefusedRequest = false :=
  publicSubstantiveInstance.futureRefusalExecuted

end Tests.Mechanisms.NeuralConstitutiveAlignmentRegression
/- AXIOM_AUDIT_BEGIN -/
#print axioms Tests.Mechanisms.NeuralConstitutiveAlignmentRegression.completePublicChain
#print axioms Tests.Mechanisms.NeuralConstitutiveAlignmentRegression.completePublicScientificDecomposition
#print axioms Tests.Mechanisms.NeuralConstitutiveAlignmentRegression.scientific_received_action_contract_is_exact
#print axioms Tests.Mechanisms.NeuralConstitutiveAlignmentRegression.scientific_produced_incorporation_is_interventional
#print axioms Tests.Mechanisms.NeuralConstitutiveAlignmentRegression.scientific_action_is_produced_by_execution
#print axioms Tests.Mechanisms.NeuralConstitutiveAlignmentRegression.scientific_initial_proposal_is_derived
#print axioms Tests.Mechanisms.NeuralConstitutiveAlignmentRegression.scientific_head_authorization_is_only_the_incorporated_permission
#print axioms Tests.Mechanisms.NeuralConstitutiveAlignmentRegression.scientific_future_is_preserved
#print axioms Tests.Mechanisms.NeuralConstitutiveAlignmentRegression.scientific_left_forgetting_trace_is_executed
#print axioms Tests.Mechanisms.NeuralConstitutiveAlignmentRegression.scientific_left_forgetting_output_consumes_trace
#print axioms Tests.Mechanisms.NeuralConstitutiveAlignmentRegression.scientific_historical_distinction_is_forgotten
#print axioms Tests.Mechanisms.NeuralConstitutiveAlignmentRegression.scientific_forgotten_origin_is_irrecoverable
#print axioms Tests.Mechanisms.NeuralConstitutiveAlignmentRegression.c16_same_witness_is_produced_and_consumed
#print axioms Tests.Mechanisms.NeuralConstitutiveAlignmentRegression.c16_exact_proposal_occurrence
#print axioms Tests.Mechanisms.NeuralConstitutiveAlignmentRegression.c16_occurrence_value_is_separate_readout
#print axioms Tests.Mechanisms.NeuralConstitutiveAlignmentRegression.c16_action_is_the_actual_execution
#print axioms Tests.Mechanisms.NeuralConstitutiveAlignmentRegression.c16_effect_is_the_produced_execution_result
#print axioms Tests.Mechanisms.NeuralConstitutiveAlignmentRegression.c16_produced_successor_is_transmitted
#print axioms Tests.Mechanisms.NeuralConstitutiveAlignmentRegression.c16_actual_tail_consumes_produced_state
#print axioms Tests.Mechanisms.NeuralConstitutiveAlignmentRegression.c16_second_reconfiguration_consumes_previous_production
#print axioms Tests.Mechanisms.NeuralConstitutiveAlignmentRegression.public_chain_is_generic_specialization
#print axioms Tests.Mechanisms.NeuralConstitutiveAlignmentRegression.alignment_consumes_executed_effect
#print axioms Tests.Mechanisms.NeuralConstitutiveAlignmentRegression.alignment_continuation_uses_required_requests
#print axioms Tests.Mechanisms.NeuralConstitutiveAlignmentRegression.alignment_continuation_is_exact_execution
#print axioms Tests.Mechanisms.NeuralConstitutiveAlignmentRegression.alignment_forgetting_inputs_remain_distinct
#print axioms Tests.Mechanisms.NeuralConstitutiveAlignmentRegression.alignment_left_forgetting_executes_to_continuation
#print axioms Tests.Mechanisms.NeuralConstitutiveAlignmentRegression.alignment_right_forgetting_executes_to_continuation
#print axioms Tests.Mechanisms.NeuralConstitutiveAlignmentRegression.alignment_forgetting_equality_is_computed
#print axioms Tests.Mechanisms.NeuralConstitutiveAlignmentRegression.alignment_forgets_origin_but_preserves_future
#print axioms Tests.Mechanisms.NeuralConstitutiveAlignmentRegression.alignment_forgetting_cannot_recover_both_origins
#print axioms Tests.Mechanisms.NeuralConstitutiveAlignmentRegression.substantive_instance_has_multiple_requirements
#print axioms Tests.Mechanisms.NeuralConstitutiveAlignmentRegression.substantive_instance_has_multiple_contexts
#print axioms Tests.Mechanisms.NeuralConstitutiveAlignmentRegression.substantive_instance_has_contextual_proposals
#print axioms Tests.Mechanisms.NeuralConstitutiveAlignmentRegression.substantive_instance_has_nontrivial_intermediate_representation
#print axioms Tests.Mechanisms.NeuralConstitutiveAlignmentRegression.substantive_instance_transformation_is_not_identity
#print axioms Tests.Mechanisms.NeuralConstitutiveAlignmentRegression.substantive_instance_action_preserves_distinction
#print axioms Tests.Mechanisms.NeuralConstitutiveAlignmentRegression.substantive_instance_reconfiguration_depends_on_source_state
#print axioms Tests.Mechanisms.NeuralConstitutiveAlignmentRegression.substantive_instance_reconfiguration_depends_on_next_requirement
#print axioms Tests.Mechanisms.NeuralConstitutiveAlignmentRegression.substantive_instance_reconfiguration_depends_on_next_context
#print axioms Tests.Mechanisms.NeuralConstitutiveAlignmentRegression.substantive_instance_authorization_is_consumed
#print axioms Tests.Mechanisms.NeuralConstitutiveAlignmentRegression.substantive_instance_continuation_has_two_steps
#print axioms Tests.Mechanisms.NeuralConstitutiveAlignmentRegression.substantive_instance_executes_forgetting
#print axioms Tests.Mechanisms.NeuralConstitutiveAlignmentRegression.substantive_instance_memory_is_strictly_reduced
#print axioms Tests.Mechanisms.NeuralConstitutiveAlignmentRegression.substantive_instance_executes_admission
#print axioms Tests.Mechanisms.NeuralConstitutiveAlignmentRegression.substantive_instance_executes_refusal
/- AXIOM_AUDIT_END -/
