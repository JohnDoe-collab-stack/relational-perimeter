import RelationalPerimeter.Agents.Neural.ConstitutiveAlignment

/-!
# Fixed meta-contracts and operational-contract transitions

An operational contract keeps the received requirement interface, neural
encoding, proposal decoder, action interpretation, and the seven families of
obligations separate.  A meta-contract is fixed over a type of operational
contract names.  It supplies admissions, transition permissions, transport of
the obligations that survive a transition, and fresh witnesses for the
obligations that must be checked again.

The certified transition below contains no client-selected preservation
function.  Preservation and rechecking are projections of the fixed
meta-contract applied to the exact transition permission.
-/
set_option genInjectivity false
namespace ConstitutiveSearch.NeuralAgent
open NativeMechanism

/-- One explicitly named family of operational obligations. -/
structure ContractObligationFamily where
  Statement : Type 3
  Witness : Statement -> Type 3

/-- The operational contract keeps every constitutive layer separate.  In
particular, admission and normative satisfaction are not collapsed into the
neural encoding or into the action channel. -/
structure ConstitutiveContract where
  RequirementCase : Type
  Context : Type
  Proposal : Type
  family : RequirementFamily RequirementCase Context Proposal
  inputCount : Nat
  encode : RequirementInput family -> SizedActivations inputCount
  decode : List Activation -> Proposal
  actionChannel : AgentActionChannel Proposal
  declaredCurrentInputs : List (RequirementInput family)
  declaredReplacementValues : List Activation
  FutureSource : Type 3
  FutureInput : Type 3
  FutureEvent : Type 3
  FutureObservation : Type 3
  futureContract : ContinuationSignatures.FutureContract
    FutureSource FutureInput FutureEvent FutureObservation
  futureSourceOfState :
    ReconfiguredExecutionState family -> FutureSource
  requirementEncoding : ContractObligationFamily
  requirementEncodingAt :
    ReconfiguredExecutionState family -> requirementEncoding.Statement
  causalCondition : ContractObligationFamily
  causalConditionAt :
    ReconfiguredExecutionState family -> causalCondition.Statement
  proposalActionPreservation : ContractObligationFamily
  proposalActionPreservationAt :
    ReconfiguredExecutionState family -> proposalActionPreservation.Statement
  authorizationAdmission : ContractObligationFamily
  authorizationAdmissionAt :
    ReconfiguredExecutionState family -> authorizationAdmission.Statement
  effectSatisfaction : ContractObligationFamily
  effectSatisfactionAt :
    ReconfiguredExecutionState family -> effectSatisfaction.Statement
  coveredFuture : ContractObligationFamily
  coveredFutureAt :
    ReconfiguredExecutionState family ->
      List (RequirementInput family) -> coveredFuture.Statement
  historicalPolicy : ContractObligationFamily
  historicalPolicyAt :
    ReconfiguredExecutionState family -> historicalPolicy.Statement

/-- A fixed meta-contract describes which operational contracts exist in its
jurisdiction and owns every rule that can move between them. -/
structure ConstitutiveMetaContract where
  Contract : Type
  operational : Contract -> ConstitutiveContract
  Admits : Contract -> Type
  TransitionPermission : Contract -> Contract -> Type
  PersistentObligation : Contract -> Contract -> Type
  SourcePersistentWitness :
    (current next : Contract) -> PersistentObligation current next -> Type 3
  TargetPersistentWitness :
    (current next : Contract) -> PersistentObligation current next -> Type 3
  transportPersistent :
    {current next : Contract} ->
      TransitionPermission current next ->
      (obligation : PersistentObligation current next) ->
      SourcePersistentWitness current next obligation ->
      TargetPersistentWitness current next obligation
  RecheckObligation : Contract -> Contract -> Type
  RecheckedWitness :
    (current next : Contract) -> RecheckObligation current next -> Type 3
  recheckInvalidated :
    {current next : Contract} ->
      TransitionPermission current next ->
      (obligation : RecheckObligation current next) ->
      RecheckedWitness current next obligation
  ExecutedStateTransition :
    {current next : Contract} ->
      TransitionPermission current next ->
      ReconfiguredExecutionState (operational current).family ->
      ReconfiguredExecutionState (operational next).family -> Type 4

/-- A transition is admitted only through the permission and target admission
owned by the fixed meta-contract.  Its constructor is private so callers
cannot replace those witnesses after the fact. -/
structure OperationalContractTransition
    (constitution : ConstitutiveMetaContract)
    (current next : constitution.Contract) : Type 4 where
  private mk ::
  sourceAdmission : constitution.Admits current
  targetAdmission : constitution.Admits next
  permission : constitution.TransitionPermission current next

def certifyOperationalContractTransition
    {constitution : ConstitutiveMetaContract}
    {current next : constitution.Contract}
    (sourceAdmission : constitution.Admits current)
    (targetAdmission : constitution.Admits next)
    (permission : constitution.TransitionPermission current next) :
    OperationalContractTransition constitution current next :=
  .mk sourceAdmission targetAdmission permission

/-- Surviving evidence is transported only by the rule stored in `meta`. -/
def OperationalContractTransition.transport
    {constitution : ConstitutiveMetaContract}
    {current next : constitution.Contract}
    (transition : OperationalContractTransition constitution current next)
    (obligation : constitution.PersistentObligation current next)
    (witness : constitution.SourcePersistentWitness current next obligation) :
    constitution.TargetPersistentWitness current next obligation :=
  constitution.transportPersistent transition.permission obligation witness

/-- Invalidated evidence is reconstructed only by the rule stored in `meta`. -/
def OperationalContractTransition.recheck
    {constitution : ConstitutiveMetaContract}
    {current next : constitution.Contract}
    (transition : OperationalContractTransition constitution current next)
    (obligation : constitution.RecheckObligation current next) :
    constitution.RecheckedWitness current next obligation :=
  constitution.recheckInvalidated transition.permission obligation

/-! ## Closed public realization -/

inductive PublicOperationalContract where
  | initial
  | reconfigured

structure PublicRequirementEncodingWitness
    (input : PublicRequirementInput) : Type 3 where
  incorporation : RequirementIncorporation publicRequirementEncoding input

structure PublicCausalWitness
    (input : PublicRequirementInput) : Type 3 where
  role : CausalRole publicRequirementSystem input
    (.receivedInput publicRequirementPort)

structure PublicAuthorizationWitness
    (input : PublicRequirementInput) : Type 3 where
  authorization : IncorporatedReconfigurationPermission
    publicRequirementFamily publicReconfigurationBuilder.permissionVariable input

def publicRequirementEncodingObligations : ContractObligationFamily where
  Statement := ULift.{3} PublicRequirementInput
  Witness := fun input => PublicRequirementEncodingWitness input.down

def publicCausalObligations : ContractObligationFamily where
  Statement := ULift.{3} PublicRequirementInput
  Witness := fun input => PublicCausalWitness input.down

def publicProposalActionObligations : ContractObligationFamily where
  Statement := ULift.{3} PublicRequirementInput
  Witness := fun input => ActionRealization publicAgentActionChannel
    (publicRequirementSignalTransformation input.down) publicActionMemory

def publicAuthorizationObligations : ContractObligationFamily where
  Statement := ULift.{3} PublicRequirementInput
  Witness := fun input => PublicAuthorizationWitness input.down

def publicEffectObligations : ContractObligationFamily where
  Statement := ULift.{3} PublicRequirementInput
  Witness := fun input => EffectRealization (publicAction input.down)

def publicFutureObligations : ContractObligationFamily where
  Statement := ULift.{3} (List PublicRequirementInput)
  Witness := fun inputs => InteractionHistory publicRequirementIncorporation
    publicRequirementSignalTransformation publicAgentActionChannel
      publicActionMemory inputs.down

/-- The initial historical obligation is indexed by the exact current state;
the witness must carry a historical predecessor whose current component is
that state. -/
structure PublicInitialHistoricalStateWitness
    (target : ReconfiguredExecutionState publicRequirementFamily) : Type 3 where
  historical : PublicHistoricalOperationalState
  currentExact : historical.current = target

def publicInitialHistoricalObligations : ContractObligationFamily where
  Statement := ReconfiguredExecutionState publicRequirementFamily
  Witness := PublicInitialHistoricalStateWitness

/-- After the operational-contract transition, historical admissibility is no
longer a witness about an initial input.  It is a witness that the exact
reconfigured state was produced by one executed reconfiguration from an
earlier state. -/
structure PublicProducedReconfiguredStateWitness
    (target : ReconfiguredExecutionState publicRequirementFamily) : Type 3 where
  source : ReconfiguredExecutionState publicRequirementFamily
  next : PublicRequirementInput
  production : ReconfiguredActionEffect (builder := publicReconfigurationBuilder)
    publicAgentActionChannel source next
  targetExact : production.targetState = target

def publicReconfiguredHistoricalObligations : ContractObligationFamily where
  Statement := ReconfiguredExecutionState publicRequirementFamily
  Witness := PublicProducedReconfiguredStateWitness

/-- The exact reconfigured native system named by the target operational
contract.  It is produced by the public builder from the exact substantive
source and requirement; it is not reconstructed from its serialized shape. -/
def publicReconfiguredContractSystem :
    NativeSystem PublicRequirementInput Bool :=
  (publicReconfiguration publicSubstantiveSource
    publicSubstantiveNext).targetSystem

/-- Each reconfigured obligation remains a separate type, even though every
one consumes the same exact production.  This prevents requirement encoding,
causal participation, action, authorization, and effect from collapsing into
one opaque acceptance bit. -/
structure PublicReconfiguredRequirementEncodingWitness
    (target : ReconfiguredExecutionState publicRequirementFamily) : Type 3 where
  production : PublicProducedReconfiguredStateWitness target

structure PublicReconfiguredCausalWitness
    (target : ReconfiguredExecutionState publicRequirementFamily) : Type 3 where
  production : PublicProducedReconfiguredStateWitness target

structure PublicReconfiguredProposalActionWitness
    (target : ReconfiguredExecutionState publicRequirementFamily) : Type 3 where
  production : PublicProducedReconfiguredStateWitness target

structure PublicReconfiguredAuthorizationWitness
    (target : ReconfiguredExecutionState publicRequirementFamily) : Type 3 where
  production : PublicProducedReconfiguredStateWitness target

structure PublicReconfiguredEffectWitness
    (target : ReconfiguredExecutionState publicRequirementFamily) : Type 3 where
  production : PublicProducedReconfiguredStateWitness target

structure PublicReconfiguredFutureStatement : Type 3 where
  state : ReconfiguredExecutionState publicRequirementFamily
  requests : List PublicRequirementInput

def publicReconfiguredRequirementEncodingObligations :
    ContractObligationFamily where
  Statement := ReconfiguredExecutionState publicRequirementFamily
  Witness := PublicReconfiguredRequirementEncodingWitness

def publicReconfiguredCausalObligations : ContractObligationFamily where
  Statement := ReconfiguredExecutionState publicRequirementFamily
  Witness := PublicReconfiguredCausalWitness

def publicReconfiguredProposalActionObligations :
    ContractObligationFamily where
  Statement := ReconfiguredExecutionState publicRequirementFamily
  Witness := PublicReconfiguredProposalActionWitness

def publicReconfiguredAuthorizationObligations :
    ContractObligationFamily where
  Statement := ReconfiguredExecutionState publicRequirementFamily
  Witness := PublicReconfiguredAuthorizationWitness

def publicReconfiguredEffectObligations : ContractObligationFamily where
  Statement := ReconfiguredExecutionState publicRequirementFamily
  Witness := PublicReconfiguredEffectWitness

def publicReconfiguredFutureObligations : ContractObligationFamily where
  Statement := PublicReconfiguredFutureStatement
  Witness := fun statement =>
    ReconfiguredInteractionHistory publicReconfigurationBuilder
      publicAgentActionChannel publicReconfigurationCertificateForState
      statement.state statement.requests

def publicDeclaredCurrentInputs : List PublicRequirementInput :=
  [RequirementInput.mk .scopeZero .direct,
   RequirementInput.mk .scopeZero .reversed,
   RequirementInput.mk .scopeOne .direct,
   RequirementInput.mk .scopeOne .reversed]

/-- The finite intervention alphabet declared by the public contract.  The
causal basis below will show, separately for every controlled occurrence,
which of these values are actually candidate replacements. -/
def publicDeclaredReplacementValues : List Activation := [0, 1, 2, 3]

/-- Both public versions retain the same received interface.  Their distinct
names permit the fixed meta-contract to authorize the one intended change;
the interface itself is not reconstructed by the transition. -/
def publicOperationalContract :
    PublicOperationalContract -> ConstitutiveContract
  | .initial =>
      { RequirementCase := PublicRequirementCase
        Context := PublicRequirementContext
        Proposal := Bool
        family := publicRequirementFamily
        inputCount := 1
        encode := encodePublicRequirement
        decode := decodePublicRequirement
        actionChannel := publicAgentActionChannel
        declaredCurrentInputs := publicDeclaredCurrentInputs
        declaredReplacementValues := publicDeclaredReplacementValues
        FutureSource := ReconfiguredExecutionState publicRequirementFamily
        FutureInput := ULift.{3} Agent.Request
        FutureEvent := Agent.Event
        FutureObservation := OperationalMemoryReadout
        futureContract := reconfiguredOperationalStateFutureContract
          (family := publicRequirementFamily)
        futureSourceOfState := fun state => state
        requirementEncoding := publicRequirementEncodingObligations
        requirementEncodingAt := fun state => ULift.up state.input
        causalCondition := publicCausalObligations
        causalConditionAt := fun state => ULift.up state.input
        proposalActionPreservation := publicProposalActionObligations
        proposalActionPreservationAt := fun state => ULift.up state.input
        authorizationAdmission := publicAuthorizationObligations
        authorizationAdmissionAt := fun state => ULift.up state.input
        effectSatisfaction := publicEffectObligations
        effectSatisfactionAt := fun state => ULift.up state.input
        coveredFuture := publicFutureObligations
        coveredFutureAt := fun _ inputs => ULift.up inputs
        historicalPolicy := publicInitialHistoricalObligations
        historicalPolicyAt := fun state => state }
  | .reconfigured =>
      { RequirementCase := PublicRequirementCase
        Context := PublicRequirementContext
        Proposal := Bool
        family := publicRequirementFamily
        inputCount := publicReconfiguredContractSystem.inputCount
        encode := publicReconfiguredContractSystem.encode
        decode := publicReconfiguredContractSystem.decode
        actionChannel := publicAgentActionChannel
        declaredCurrentInputs := [publicSubstantiveNext]
        declaredReplacementValues := publicDeclaredReplacementValues
        FutureSource := ReconfiguredExecutionState publicRequirementFamily
        FutureInput := ULift.{3} Agent.Request
        FutureEvent := Agent.Event
        FutureObservation := OperationalMemoryReadout
        futureContract := reconfiguredOperationalStateFutureContract
          (family := publicRequirementFamily)
        futureSourceOfState := fun state => state
        requirementEncoding := publicReconfiguredRequirementEncodingObligations
        requirementEncodingAt := fun state => state
        causalCondition := publicReconfiguredCausalObligations
        causalConditionAt := fun state => state
        proposalActionPreservation :=
          publicReconfiguredProposalActionObligations
        proposalActionPreservationAt := fun state => state
        authorizationAdmission := publicReconfiguredAuthorizationObligations
        authorizationAdmissionAt := fun state => state
        effectSatisfaction := publicReconfiguredEffectObligations
        effectSatisfactionAt := fun state => state
        coveredFuture := publicReconfiguredFutureObligations
        coveredFutureAt := fun state inputs =>
          { state := state, requests := inputs }
        historicalPolicy := publicReconfiguredHistoricalObligations
        historicalPolicyAt := fun state => state }

/-- The public target-contract history witness is inhabited by the exact state
produced by the already certified reconfiguration execution. -/
def publicContractTransitionProduction :
    ReconfiguredActionEffect (builder := publicReconfigurationBuilder)
      publicAgentActionChannel
      (publicInitialReconfiguredState publicSubstantiveSource)
      publicSubstantiveNext :=
  executeReconfiguredAction publicAgentActionChannel
    (publicInitialReconfiguredState publicSubstantiveSource)
    publicSubstantiveNext
    (publicReconfigurationCertificateForState
      (publicInitialReconfiguredState publicSubstantiveSource)
      publicSubstantiveNext)

def publicContractTransitionHistoricalWitness :
    PublicProducedReconfiguredStateWitness
      publicContractTransitionProduction.targetState :=
  { source := publicInitialReconfiguredState publicSubstantiveSource
    next := publicSubstantiveNext
    production := publicContractTransitionProduction
    targetExact := rfl }

inductive PublicContractAdmission : PublicOperationalContract -> Type where
  | initial : PublicContractAdmission .initial
  | reconfigured : PublicContractAdmission .reconfigured

inductive PublicContractTransitionPermission :
    PublicOperationalContract -> PublicOperationalContract -> Type where
  | executeReconfiguration :
      PublicContractTransitionPermission .initial .reconfigured

inductive PublicPersistentContractObligation where
  | actionDistinction

structure PublicActionDistinctionWitness : Type 3 where
  exact : DistinctAccordingToActionContract publicAgentActionChannel
    (publicAgentActionChannel.command false)
    (publicAgentActionChannel.command true)

def publicPersistentContractWitness
    (_current _next : PublicOperationalContract)
    (_obligation : PublicPersistentContractObligation) : Type 3 :=
  PublicActionDistinctionWitness

inductive PublicRecheckedContractObligation where
  | incorporatedAuthorization

def publicRecheckedContractWitness
    (_current _next : PublicOperationalContract)
    (_obligation : PublicRecheckedContractObligation) : Type 3 :=
  PublicAuthorizationWitness (RequirementInput.mk .scopeOne .direct)

/-- The state transition owned by the public meta-contract is the actual
reconfiguration action executed from the exact source state.  Its target
index is the state produced by that action, so an independently supplied
successor cannot inhabit this type. -/
inductive PublicExecutedContractStateTransition :
    {current next : PublicOperationalContract} ->
      (permission : PublicContractTransitionPermission current next) ->
      ReconfiguredExecutionState
        (publicOperationalContract current).family ->
      ReconfiguredExecutionState
        (publicOperationalContract next).family -> Type 4 where
  | execute
      (source : ReconfiguredExecutionState publicRequirementFamily)
      (nextInput : PublicRequirementInput) :
      PublicExecutedContractStateTransition
        PublicContractTransitionPermission.executeReconfiguration source
        (executeReconfiguredAction publicAgentActionChannel source nextInput
          (publicReconfigurationCertificateForState source nextInput)).targetState

def publicConstitutiveMetaContract : ConstitutiveMetaContract where
  Contract := PublicOperationalContract
  operational := publicOperationalContract
  Admits := PublicContractAdmission
  TransitionPermission := PublicContractTransitionPermission
  PersistentObligation := fun _ _ => PublicPersistentContractObligation
  SourcePersistentWitness := publicPersistentContractWitness
  TargetPersistentWitness := publicPersistentContractWitness
  transportPersistent := by
    intro current next permission obligation witness
    exact witness
  RecheckObligation := fun _ _ => PublicRecheckedContractObligation
  RecheckedWitness := publicRecheckedContractWitness
  recheckInvalidated := by
    intro current next permission obligation
    exact
      { authorization :=
          publicReconfigurationAuthorization ⟨.scopeOne, .direct⟩ }
  ExecutedStateTransition := PublicExecutedContractStateTransition

def publicOperationalTransition : OperationalContractTransition
    publicConstitutiveMetaContract .initial .reconfigured :=
  certifyOperationalContractTransition .initial .reconfigured
    .executeReconfiguration

def publicTransition_preservesActionDistinction :
    publicPersistentContractWitness .initial .reconfigured
      .actionDistinction :=
  publicOperationalTransition.transport .actionDistinction
    { exact := public_required_action_distinction }

def publicTransition_rechecksAuthorization :
    publicRecheckedContractWitness .initial .reconfigured
      .incorporatedAuthorization :=
  publicOperationalTransition.recheck .incorporatedAuthorization

end ConstitutiveSearch.NeuralAgent
/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.NeuralAgent.ContractObligationFamily
#print axioms ConstitutiveSearch.NeuralAgent.ConstitutiveContract
#print axioms ConstitutiveSearch.NeuralAgent.ConstitutiveMetaContract
#print axioms ConstitutiveSearch.NeuralAgent.OperationalContractTransition
#print axioms ConstitutiveSearch.NeuralAgent.certifyOperationalContractTransition
#print axioms ConstitutiveSearch.NeuralAgent.OperationalContractTransition.transport
#print axioms ConstitutiveSearch.NeuralAgent.OperationalContractTransition.recheck
#print axioms ConstitutiveSearch.NeuralAgent.publicOperationalContract
#print axioms ConstitutiveSearch.NeuralAgent.publicDeclaredCurrentInputs
#print axioms ConstitutiveSearch.NeuralAgent.publicDeclaredReplacementValues
#print axioms ConstitutiveSearch.NeuralAgent.PublicInitialHistoricalStateWitness
#print axioms ConstitutiveSearch.NeuralAgent.PublicProducedReconfiguredStateWitness
#print axioms ConstitutiveSearch.NeuralAgent.publicReconfiguredContractSystem
#print axioms ConstitutiveSearch.NeuralAgent.PublicReconfiguredRequirementEncodingWitness
#print axioms ConstitutiveSearch.NeuralAgent.PublicReconfiguredCausalWitness
#print axioms ConstitutiveSearch.NeuralAgent.PublicReconfiguredProposalActionWitness
#print axioms ConstitutiveSearch.NeuralAgent.PublicReconfiguredAuthorizationWitness
#print axioms ConstitutiveSearch.NeuralAgent.PublicReconfiguredEffectWitness
#print axioms ConstitutiveSearch.NeuralAgent.PublicReconfiguredFutureStatement
#print axioms ConstitutiveSearch.NeuralAgent.publicContractTransitionProduction
#print axioms ConstitutiveSearch.NeuralAgent.publicContractTransitionHistoricalWitness
#print axioms ConstitutiveSearch.NeuralAgent.PublicExecutedContractStateTransition
#print axioms ConstitutiveSearch.NeuralAgent.publicConstitutiveMetaContract
#print axioms ConstitutiveSearch.NeuralAgent.publicOperationalTransition
#print axioms ConstitutiveSearch.NeuralAgent.publicTransition_preservesActionDistinction
#print axioms ConstitutiveSearch.NeuralAgent.publicTransition_rechecksAuthorization
/- AXIOM_AUDIT_END -/
