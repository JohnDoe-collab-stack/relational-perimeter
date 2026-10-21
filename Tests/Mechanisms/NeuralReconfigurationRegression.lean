import RelationalPerimeter.Agents.Neural.PublicActionRealization

namespace Tests.Mechanisms.NeuralReconfigurationRegression
open ConstitutiveSearch.NativeMechanism ConstitutiveSearch.NeuralAgent

universe u v w

/-- Positive control for C14.  With the exact certificate returned by
`certify`, the same head and dependent tail used by the negative fixture form
a well-typed interaction history. -/
def canonicalCertificateBuildsHead
    {RequirementCase : Type u} {Context : Type v} {Proposal : Type w}
    {family : RequirementFamily RequirementCase Context Proposal}
    (builder : ReconfigurationBuilder family)
    (channel : AgentActionChannel Proposal)
    (certify : (source : ReconfiguredExecutionState family) ->
      (next : RequirementInput family) ->
      CertifiedReconfiguration (builder := builder)
        (sourceSystem := source.system) (sourceInput := source.input)
        (nextInput := next))
    (source : ReconfiguredExecutionState family)
    (next : RequirementInput family)
    (future : List (RequirementInput family))
    (tail : ReconfiguredInteractionHistory builder channel certify
      (executeReconfiguredAction channel source next
        (certify source next)).targetState future) :
    ReconfiguredInteractionHistory builder channel certify source
      (next :: future) :=
  .step (executeReconfiguredCausalStage builder channel certify source next)
    tail

def scopeZeroDirectInput : PublicRequirementInput := ⟨.scopeZero, .direct⟩
def scopeOneDirectInput : PublicRequirementInput := ⟨.scopeOne, .direct⟩

/-- C6: the first continuation stage is produced only from the current state
and its next requirement. -/
def firstContinuationStage :=
  executeReconfiguredCausalStage publicReconfigurationBuilder
    publicAgentActionChannel publicReconfigurationCertificateForState
    (publicInitialReconfiguredState scopeZeroDirectInput) scopeOneDirectInput

/-- C6: the second stage consumes exactly the state produced by the first.
Its type exposes the same strong causal interface at the later stage. -/
def secondContinuationStage :=
  executeReconfiguredCausalStage publicReconfigurationBuilder
    publicAgentActionChannel publicReconfigurationCertificateForState
    firstContinuationStage.nextState scopeZeroDirectInput

theorem target_is_built_from_exact_source_run_and_next_requirement :
    (publicReconfiguration scopeZeroDirectInput scopeOneDirectInput).targetSystem =
      publicReconfigurationBuilder.build
        publicRequirementSystem (publicRequirementSystem.run scopeZeroDirectInput)
        scopeOneDirectInput (publicReconfiguration scopeZeroDirectInput scopeOneDirectInput).authorization :=
  (publicReconfiguration scopeZeroDirectInput scopeOneDirectInput).target_exact

theorem source_and_requirement_use_distinct_ports :
    (publicRequiredMechanismTransport scopeZeroDirectInput scopeOneDirectInput).sourcePort ≠
      (publicRequiredMechanismTransport scopeZeroDirectInput scopeOneDirectInput).requirementPort :=
  (publicRequiredMechanismTransport scopeZeroDirectInput scopeOneDirectInput).portsDistinct

theorem authorization_uses_a_third_distinct_port :
    (publicRequiredMechanismTransport scopeZeroDirectInput scopeOneDirectInput).sourcePort ≠
        (publicRequiredMechanismTransport scopeZeroDirectInput scopeOneDirectInput).authorizationPort ∧
      (publicRequiredMechanismTransport scopeZeroDirectInput scopeOneDirectInput).requirementPort ≠
        (publicRequiredMechanismTransport scopeZeroDirectInput scopeOneDirectInput).authorizationPort :=
  ⟨(publicRequiredMechanismTransport scopeZeroDirectInput scopeOneDirectInput).sourceAuthorizationDistinct,
    (publicRequiredMechanismTransport scopeZeroDirectInput scopeOneDirectInput).requirementAuthorizationDistinct⟩

theorem source_proposal_is_decoded_from_exact_run :
    publicRequirementSystem.proposal scopeZeroDirectInput =
      proposalFromRun publicRequirementSystem
        (publicRequirementSystem.run scopeZeroDirectInput) :=
  public_source_proposal_is_exact_execution publicRequirementSystem scopeZeroDirectInput

theorem target_combination_is_executed :
    (publicReconfiguration scopeZeroDirectInput scopeOneDirectInput).targetSystem.outputValues
        scopeOneDirectInput =
      publicReconfigurationCombinedOutputs
        (((publicReconfiguration scopeZeroDirectInput scopeOneDirectInput).targetSystem.encode
          scopeOneDirectInput).read
            (publicRequiredMechanismTransport scopeZeroDirectInput scopeOneDirectInput).sourcePort)
        (((publicReconfiguration scopeZeroDirectInput scopeOneDirectInput).targetSystem.encode
          scopeOneDirectInput).read
            (publicRequiredMechanismTransport scopeZeroDirectInput scopeOneDirectInput).requirementPort)
        (((publicReconfiguration scopeZeroDirectInput scopeOneDirectInput).targetSystem.encode
          scopeOneDirectInput).read
            (publicRequiredMechanismTransport scopeZeroDirectInput scopeOneDirectInput).authorizationPort) :=
  public_reconfiguration_combination_executed_from
    publicRequirementSystem scopeZeroDirectInput scopeOneDirectInput

theorem final_proposal_is_derived_not_stored :
    (publicReconfiguration scopeZeroDirectInput scopeOneDirectInput).targetSystem.proposal
        scopeOneDirectInput =
      publicRequirementFamily.requiredProposal
        scopeOneDirectInput.requirement scopeOneDirectInput.context :=
  public_reconfigured_proposal_exact_from_derivation
    publicRequirementSystem scopeZeroDirectInput scopeOneDirectInput

def reconfiguration_is_authorized :
    ConstitutiveSearch.Resources.Ref
      (publicRequirementFamily.received scopeOneDirectInput.requirement).realizedScope
      (publicReconfigurationBuilder.permissionVariable scopeOneDirectInput.requirement) :=
  (publicReconfiguration scopeZeroDirectInput scopeOneDirectInput).permission

theorem permission_is_admitted_before_incorporation :
    (publicRequirementFamily.received scopeOneDirectInput.requirement).permission
        (publicReconfigurationBuilder.permissionVariable scopeOneDirectInput.requirement) =
      some (publicReconfigurationAdmission scopeOneDirectInput).permission :=
  (publicReconfigurationAdmission scopeOneDirectInput).admitted

theorem authorization_occurrence_is_executed_exactly :
    ((publicReconfiguration scopeZeroDirectInput scopeOneDirectInput).targetSystem.encode
      scopeOneDirectInput).read
        (publicRequiredMechanismTransport scopeZeroDirectInput scopeOneDirectInput).authorizationPort =
      publicReconfigurationBuilder.authorizationCode scopeOneDirectInput
        (publicReconfiguration scopeZeroDirectInput scopeOneDirectInput).permission :=
  (publicRequiredMechanismTransport scopeZeroDirectInput scopeOneDirectInput).authorizationExact

def source_occurrence_reaches_reconfigured_output :
    Reaches ((publicReconfiguration scopeZeroDirectInput scopeOneDirectInput).targetSystem.run scopeOneDirectInput)
      (.receivedInput publicReconfigurationSourcePort)
      (.neuronOutput publicReconfigurationProposalOutput) :=
  .step (publicReconfigurationSourceEdge scopeZeroDirectInput scopeOneDirectInput).toReadsFrom
    (.refl _)

def requirement_occurrence_reaches_reconfigured_output :
    Reaches ((publicReconfiguration scopeZeroDirectInput scopeOneDirectInput).targetSystem.run scopeOneDirectInput)
      (.receivedInput publicReconfigurationRequirementPort)
      (.neuronOutput publicReconfigurationProposalOutput) :=
  .step (publicReconfigurationRequirementEdge scopeZeroDirectInput scopeOneDirectInput).toReadsFrom
    (.refl _)

/-- C5: the preceding executed proposal is not represented merely by a graph
path.  Its exact transported occurrence carries the complete intervention,
nontrivial effective propagation, target change, and proposal change. -/
def source_resource_has_causal_role :
    CausalRole (publicReconfiguration scopeZeroDirectInput scopeOneDirectInput).targetSystem
      scopeOneDirectInput (.receivedInput publicReconfigurationSourcePort) :=
  (publicRequiredMechanismTransport scopeZeroDirectInput scopeOneDirectInput).sourceRole

/-- C5: the newly received requirement independently carries the same strong
causal evidence all the way to the reconfigured proposal. -/
def new_requirement_has_causal_role :
    CausalRole (publicReconfiguration scopeZeroDirectInput scopeOneDirectInput).targetSystem
      scopeOneDirectInput (.receivedInput publicReconfigurationRequirementPort) :=
  (publicRequiredMechanismTransport scopeZeroDirectInput scopeOneDirectInput).requirementRole

/-- C7: the admitted permission is incorporated at its own input occurrence
and has a complete causal role in the produced proposal. -/
def incorporated_authorization_has_causal_role :
    CausalRole (publicReconfiguration scopeZeroDirectInput scopeOneDirectInput).targetSystem
      scopeOneDirectInput (.receivedInput publicReconfigurationAuthorizationPort) :=
  (publicRequiredMechanismTransport scopeZeroDirectInput scopeOneDirectInput).authorizationRole

def source_change_reaches_proposal_nontrivially :
    NontrivialExecutedChangePath source_resource_has_causal_role.intervention
      (.neuronOutput publicReconfigurationProposalOutput) :=
  source_resource_has_causal_role.propagation

def requirement_change_reaches_proposal_nontrivially :
    NontrivialExecutedChangePath new_requirement_has_causal_role.intervention
      (.neuronOutput publicReconfigurationProposalOutput) :=
  new_requirement_has_causal_role.propagation

theorem source_change_changes_required_proposal :
    ChangesProposal (publicReconfiguration scopeZeroDirectInput scopeOneDirectInput).targetSystem
      scopeOneDirectInput source_resource_has_causal_role.intervention :=
  source_resource_has_causal_role.proposalChange

theorem requirement_change_changes_required_proposal :
    ChangesProposal (publicReconfiguration scopeZeroDirectInput scopeOneDirectInput).targetSystem
      scopeOneDirectInput new_requirement_has_causal_role.intervention :=
  new_requirement_has_causal_role.proposalChange

theorem authorization_change_changes_required_proposal :
    ChangesProposal (publicReconfiguration scopeZeroDirectInput scopeOneDirectInput).targetSystem
      scopeOneDirectInput incorporated_authorization_has_causal_role.intervention :=
  incorporated_authorization_has_causal_role.proposalChange

theorem changing_source_changes_executed_material :
    ((publicReconfiguration scopeZeroDirectInput scopeZeroDirectInput).targetSystem.encode scopeZeroDirectInput).read
        publicReconfigurationSourcePort ≠
      ((publicReconfiguration scopeOneDirectInput scopeZeroDirectInput).targetSystem.encode scopeZeroDirectInput).read
        publicReconfigurationSourcePort :=
  public_reconfiguration_reads_source_distinction scopeZeroDirectInput

theorem changing_requirement_changes_executed_material :
    ((publicReconfiguration scopeZeroDirectInput scopeZeroDirectInput).targetSystem.encode scopeZeroDirectInput).read
        publicReconfigurationRequirementPort ≠
      ((publicReconfiguration scopeZeroDirectInput scopeOneDirectInput).targetSystem.encode scopeOneDirectInput).read
        publicReconfigurationRequirementPort :=
  public_reconfiguration_reads_requirement_distinction scopeZeroDirectInput

theorem changing_source_changes_reconfigured_output :
    (publicReconfiguration scopeZeroDirectInput scopeZeroDirectInput).targetSystem.outputValues
        scopeZeroDirectInput ≠
      (publicReconfiguration scopeOneDirectInput scopeZeroDirectInput).targetSystem.outputValues
        scopeZeroDirectInput :=
  public_reconfiguration_source_changes_output

theorem changing_requirement_changes_reconfigured_output :
    (publicReconfiguration scopeZeroDirectInput scopeZeroDirectInput).targetSystem.outputValues
        scopeZeroDirectInput ≠
      (publicReconfiguration scopeZeroDirectInput scopeOneDirectInput).targetSystem.outputValues
        scopeOneDirectInput :=
  public_reconfiguration_requirement_changes_output

def first_stage_source_has_causal_role :
    CausalRole
      firstContinuationStage.action.certificate.configuration.targetSystem
      scopeOneDirectInput
      (.receivedInput
        firstContinuationStage.action.certificate.transport.sourcePort) :=
  firstContinuationStage.sourceRole

def first_stage_requirement_has_causal_role :
    CausalRole
      firstContinuationStage.action.certificate.configuration.targetSystem
      scopeOneDirectInput
      (.receivedInput
        firstContinuationStage.action.certificate.transport.requirementPort) :=
  firstContinuationStage.requirementRole

def first_stage_authorization_has_causal_role :
    CausalRole
      firstContinuationStage.action.certificate.configuration.targetSystem
      scopeOneDirectInput
      (.receivedInput
        firstContinuationStage.action.certificate.transport.authorizationPort) :=
  firstContinuationStage.authorizationRole

def second_stage_source_has_causal_role :
    CausalRole
      secondContinuationStage.action.certificate.configuration.targetSystem
      scopeZeroDirectInput
      (.receivedInput
        secondContinuationStage.action.certificate.transport.sourcePort) :=
  secondContinuationStage.sourceRole

def second_stage_requirement_has_causal_role :
    CausalRole
      secondContinuationStage.action.certificate.configuration.targetSystem
      scopeZeroDirectInput
      (.receivedInput
        secondContinuationStage.action.certificate.transport.requirementPort) :=
  secondContinuationStage.requirementRole

def second_stage_authorization_has_causal_role :
    CausalRole
      secondContinuationStage.action.certificate.configuration.targetSystem
      scopeZeroDirectInput
      (.receivedInput
        secondContinuationStage.action.certificate.transport.authorizationPort) :=
  secondContinuationStage.authorizationRole

theorem first_stage_proposal_is_produced :
    firstContinuationStage.proposal =
      publicRequirementFamily.requiredProposal
        scopeOneDirectInput.requirement scopeOneDirectInput.context :=
  firstContinuationStage.proposal_required_exact

theorem second_stage_proposal_is_produced :
    secondContinuationStage.proposal =
      publicRequirementFamily.requiredProposal
        scopeZeroDirectInput.requirement scopeZeroDirectInput.context :=
  secondContinuationStage.proposal_required_exact

theorem second_stage_action_comes_from_its_proposal :
    secondContinuationStage.request =
      publicAgentActionChannel.command secondContinuationStage.proposal :=
  secondContinuationStage.request_from_proposal

theorem second_stage_effect_comes_from_its_action :
    secondContinuationStage.effect =
      ConstitutiveSearch.Agent.executeInput
        firstContinuationStage.nextState.memory
        secondContinuationStage.request :=
  secondContinuationStage.effect_from_request

theorem second_stage_system_is_built_from_first_stage_state :
    secondContinuationStage.action.certificate.configuration.targetSystem =
      publicReconfigurationBuilder.build
        firstContinuationStage.nextState.system
        (firstContinuationStage.nextState.system.run
          firstContinuationStage.nextState.input)
        scopeZeroDirectInput
        secondContinuationStage.action.certificate.configuration.authorization :=
  secondContinuationStage.action.certificate.configuration.target_exact

theorem second_stage_state_carries_its_effect :
    secondContinuationStage.nextState.memory =
      secondContinuationStage.effect.1 :=
  rfl

/-- The actual two-step public history is definitionally the chain of the two
causally complete stages above. -/
theorem two_stage_history_consumes_both_causal_stages :
    publicReconfiguredInteractionHistory scopeZeroDirectInput [scopeOneDirectInput, scopeZeroDirectInput] =
      .step firstContinuationStage
        (.step secondContinuationStage
          (.nil secondContinuationStage.nextState)) :=
  rfl

end Tests.Mechanisms.NeuralReconfigurationRegression
/- AXIOM_AUDIT_BEGIN -/
#print axioms Tests.Mechanisms.NeuralReconfigurationRegression.canonicalCertificateBuildsHead
#print axioms Tests.Mechanisms.NeuralReconfigurationRegression.target_is_built_from_exact_source_run_and_next_requirement
#print axioms Tests.Mechanisms.NeuralReconfigurationRegression.source_and_requirement_use_distinct_ports
#print axioms Tests.Mechanisms.NeuralReconfigurationRegression.authorization_uses_a_third_distinct_port
#print axioms Tests.Mechanisms.NeuralReconfigurationRegression.source_proposal_is_decoded_from_exact_run
#print axioms Tests.Mechanisms.NeuralReconfigurationRegression.target_combination_is_executed
#print axioms Tests.Mechanisms.NeuralReconfigurationRegression.final_proposal_is_derived_not_stored
#print axioms Tests.Mechanisms.NeuralReconfigurationRegression.reconfiguration_is_authorized
#print axioms Tests.Mechanisms.NeuralReconfigurationRegression.permission_is_admitted_before_incorporation
#print axioms Tests.Mechanisms.NeuralReconfigurationRegression.authorization_occurrence_is_executed_exactly
#print axioms Tests.Mechanisms.NeuralReconfigurationRegression.source_occurrence_reaches_reconfigured_output
#print axioms Tests.Mechanisms.NeuralReconfigurationRegression.requirement_occurrence_reaches_reconfigured_output
#print axioms Tests.Mechanisms.NeuralReconfigurationRegression.source_resource_has_causal_role
#print axioms Tests.Mechanisms.NeuralReconfigurationRegression.new_requirement_has_causal_role
#print axioms Tests.Mechanisms.NeuralReconfigurationRegression.incorporated_authorization_has_causal_role
#print axioms Tests.Mechanisms.NeuralReconfigurationRegression.source_change_reaches_proposal_nontrivially
#print axioms Tests.Mechanisms.NeuralReconfigurationRegression.requirement_change_reaches_proposal_nontrivially
#print axioms Tests.Mechanisms.NeuralReconfigurationRegression.source_change_changes_required_proposal
#print axioms Tests.Mechanisms.NeuralReconfigurationRegression.requirement_change_changes_required_proposal
#print axioms Tests.Mechanisms.NeuralReconfigurationRegression.authorization_change_changes_required_proposal
#print axioms Tests.Mechanisms.NeuralReconfigurationRegression.changing_source_changes_executed_material
#print axioms Tests.Mechanisms.NeuralReconfigurationRegression.changing_requirement_changes_executed_material
#print axioms Tests.Mechanisms.NeuralReconfigurationRegression.changing_source_changes_reconfigured_output
#print axioms Tests.Mechanisms.NeuralReconfigurationRegression.changing_requirement_changes_reconfigured_output
#print axioms Tests.Mechanisms.NeuralReconfigurationRegression.first_stage_source_has_causal_role
#print axioms Tests.Mechanisms.NeuralReconfigurationRegression.first_stage_requirement_has_causal_role
#print axioms Tests.Mechanisms.NeuralReconfigurationRegression.first_stage_authorization_has_causal_role
#print axioms Tests.Mechanisms.NeuralReconfigurationRegression.second_stage_source_has_causal_role
#print axioms Tests.Mechanisms.NeuralReconfigurationRegression.second_stage_requirement_has_causal_role
#print axioms Tests.Mechanisms.NeuralReconfigurationRegression.second_stage_authorization_has_causal_role
#print axioms Tests.Mechanisms.NeuralReconfigurationRegression.first_stage_proposal_is_produced
#print axioms Tests.Mechanisms.NeuralReconfigurationRegression.second_stage_proposal_is_produced
#print axioms Tests.Mechanisms.NeuralReconfigurationRegression.second_stage_action_comes_from_its_proposal
#print axioms Tests.Mechanisms.NeuralReconfigurationRegression.second_stage_effect_comes_from_its_action
#print axioms Tests.Mechanisms.NeuralReconfigurationRegression.second_stage_system_is_built_from_first_stage_state
#print axioms Tests.Mechanisms.NeuralReconfigurationRegression.second_stage_state_carries_its_effect
#print axioms Tests.Mechanisms.NeuralReconfigurationRegression.two_stage_history_consumes_both_causal_stages
/- AXIOM_AUDIT_END -/
