import RelationalPerimeter.Agents.Neural.CheckedState

/-!
# Autonomous contract obligations and expected transitions

This module fixes the RC1/RC3 boundary before any complete or incremental
checker is run.  It does not introduce another contract or runtime.  It makes
explicit, in the existing API, four different layers:

* the obligation families declared by one operational contract;
* their instantiation at one exact executed state;
* the future-observation source produced from that state, before any memory
  realization is supplied;
* admissible continuations and contract transitions after an exact forgetting.

The types below contain no checker verdict.  A later checker may consume their
witnesses, but cannot use its own success to define the obligations it checks.
-/
set_option genInjectivity false
namespace ConstitutiveSearch.NeuralAgent
open NativeMechanism ContinuationSignatures

universe u v w

/-! ## Exact received material of a native reconfiguration -/

/-- Conditions received before a native reconfiguration is constructed.

The source system, source input and next input are indices.  Consequently the
source run is required to be the run of that exact system on that exact source
input, while the new requirement and its context are the two projections of
the exact `nextInput`.  Authorization is an incorporated resource for that
same next input.  No port name or later checker verdict occurs in this type. -/
structure AutonomousReconfigurationConditions
    {RequirementCase : Type u} {Context : Type v} {Proposal : Type w}
    {family : RequirementFamily RequirementCase Context Proposal}
    (builder : ReconfigurationBuilder family)
    (sourceSystem : NativeSystem (RequirementInput family) Proposal)
    (sourceInput nextInput : RequirementInput family) :
    Type (max 3 (max u (max v w))) where
  sourceRun : NativeRun sourceSystem.program
  sourceRunExact : sourceRun = sourceSystem.run sourceInput
  authorization : IncorporatedReconfigurationPermission family
    builder.permissionVariable nextInput

def AutonomousReconfigurationConditions.nextRequirement
    {RequirementCase : Type u} {Context : Type v} {Proposal : Type w}
    {family : RequirementFamily RequirementCase Context Proposal}
    {builder : ReconfigurationBuilder family}
    {sourceSystem : NativeSystem (RequirementInput family) Proposal}
    {sourceInput nextInput : RequirementInput family}
    (_conditions : AutonomousReconfigurationConditions builder sourceSystem
      sourceInput nextInput) : RequirementCase :=
  nextInput.requirement

def AutonomousReconfigurationConditions.nextContext
    {RequirementCase : Type u} {Context : Type v} {Proposal : Type w}
    {family : RequirementFamily RequirementCase Context Proposal}
    {builder : ReconfigurationBuilder family}
    {sourceSystem : NativeSystem (RequirementInput family) Proposal}
    {sourceInput nextInput : RequirementInput family}
    (_conditions : AutonomousReconfigurationConditions builder sourceSystem
      sourceInput nextInput) : Context :=
  nextInput.context

/-- Execute the existing reconfiguration constructor from the autonomous
conditions.  The target remains definitionally produced by `builder.build`
from the exact source-system run, next requirement/context and incorporated
authorization. -/
def AutonomousReconfigurationConditions.execute
    {RequirementCase : Type u} {Context : Type v} {Proposal : Type w}
    {family : RequirementFamily RequirementCase Context Proposal}
    {builder : ReconfigurationBuilder family}
    {sourceSystem : NativeSystem (RequirementInput family) Proposal}
    {sourceInput nextInput : RequirementInput family}
    (conditions : AutonomousReconfigurationConditions builder sourceSystem
      sourceInput nextInput) :
    Reconfiguration builder sourceSystem sourceInput nextInput :=
  reconfigure builder sourceInput nextInput conditions.authorization

theorem AutonomousReconfigurationConditions.executed_target_exact
    {RequirementCase : Type u} {Context : Type v} {Proposal : Type w}
    {family : RequirementFamily RequirementCase Context Proposal}
    {builder : ReconfigurationBuilder family}
    {sourceSystem : NativeSystem (RequirementInput family) Proposal}
    {sourceInput nextInput : RequirementInput family}
    (conditions : AutonomousReconfigurationConditions builder sourceSystem
      sourceInput nextInput) :
    conditions.execute.targetSystem =
      builder.build sourceSystem conditions.sourceRun nextInput
        conditions.authorization := by
  rw [conditions.sourceRunExact]
  exact conditions.execute.targetExact

/-! ## State-indexed obligations fixed before a checker verdict -/

/-- The seven operational obligation families instantiated at one exact
state.  No decoded artifact, checker result or exact future realization is an
argument.  This is the autonomous source-obligation layer required by RC1 and
RC3. -/
structure ContractObligationsAt
    (contract : ConstitutiveContract)
    (state : ReconfiguredExecutionState contract.family) : Type 4 where
  requirementEncoding : contract.requirementEncoding.Witness
    (contract.requirementEncodingAt state)
  causalCondition : contract.causalCondition.Witness
    (contract.causalConditionAt state)
  proposalActionPreservation : contract.proposalActionPreservation.Witness
    (contract.proposalActionPreservationAt state)
  authorizationAdmission : contract.authorizationAdmission.Witness
    (contract.authorizationAdmissionAt state)
  effectSatisfaction : contract.effectSatisfaction.Witness
    (contract.effectSatisfactionAt state)
  coveredFuture : (requests : List (RequirementInput contract.family)) ->
    contract.coveredFuture.Witness (contract.coveredFutureAt state requests)
  historicalPolicy : contract.historicalPolicy.Witness
    (contract.historicalPolicyAt state)

/-- Extract the autonomous obligation witnesses already consumed by one state
certificate.  The future realization remains deliberately outside this
projection: it is a later realization of the fixed future schema, not part of
the definition of the source obligations. -/
def StateConstitutiveCertificate.obligationsAt
    {contract : ConstitutiveContract}
    {artifact : DecodedNeuralArtifact contract}
    {state : ReconfiguredExecutionState contract.family}
    (certificate : StateConstitutiveCertificate contract artifact state) :
    ContractObligationsAt contract state :=
  { requirementEncoding := certificate.requirementEncodingWitness
    causalCondition := certificate.causalConditionWitness
    proposalActionPreservation := certificate.proposalActionWitness
    authorizationAdmission := certificate.authorizationWitness
    effectSatisfaction := certificate.effectWitness
    coveredFuture := certificate.coveredFutureWitness
    historicalPolicy := certificate.historicalWitness }

/-- The future observation source fixed by a contract at an exact state.  It
is produced without receiving a projection, reduced memory, exact realization
or checker-success proof. -/
structure ContractFutureObservationAt
    (contract : ConstitutiveContract)
    (state : ReconfiguredExecutionState contract.family) : Type 4 where
  source : contract.FutureSource
  sourceExact : source = contract.futureSourceOfState state

def contractFutureObservationAt
    {contract : ConstitutiveContract}
    (state : ReconfiguredExecutionState contract.family) :
    ContractFutureObservationAt contract state :=
  { source := contract.futureSourceOfState state
    sourceExact := rfl }

/-- Only after the observation source has been fixed may an arbitrary exact
realization be examined.  The source producer above does not receive this
realization. -/
theorem ContractFutureObservationAt.outcome_exact
    {contract : ConstitutiveContract}
    {state : ReconfiguredExecutionState contract.family}
    (observation : ContractFutureObservationAt contract state)
    {Memory : Type 3}
    (realization : ExactRealization contract.futureContract Memory)
    (requests : List contract.FutureInput) :
    contract.futureContract.outcome observation.source requests =
      realization.reduced.outcome
        (realization.project observation.source) requests :=
  realization.outcome_exact observation.source requests

/-! ## Current-agent-indexed local transition interface -/

/-- Local conditions for one target state, indexed by the exact current
checked agent and current contract.  They are independent of any complete
checker verdict.  A consumer must still build the target certificate and a
`CheckedUpdate`; this structure is not an admission shortcut. -/
structure AutonomousTransitionObligations
    (constitution : ConstitutiveMetaContract)
    {currentContract : constitution.Contract}
    (current : CheckedAgent constitution currentContract)
    {nextContract : constitution.Contract}
    (transition : OperationalContractTransition constitution
      currentContract nextContract)
    (targetState : ReconfiguredExecutionState
      (constitution.operational nextContract).family) : Type 6 where
  execution : constitution.ExecutedStateTransition transition.permission
    current.state targetState
  sourceObligations : ContractObligationsAt
    (constitution.operational currentContract) current.state
  sourceObservation : ContractFutureObservationAt
    (constitution.operational currentContract) current.state
  targetObligations : ContractObligationsAt
    (constitution.operational nextContract) targetState
  targetObservation : ContractFutureObservationAt
    (constitution.operational nextContract) targetState
  persistentSource : (obligation :
    constitution.PersistentObligation currentContract nextContract) ->
      constitution.SourcePersistentWitness currentContract nextContract
        obligation

def AutonomousTransitionObligations.transportedPersistent
    {constitution : ConstitutiveMetaContract}
    {currentContract nextContract : constitution.Contract}
    {current : CheckedAgent constitution currentContract}
    {transition : OperationalContractTransition constitution
      currentContract nextContract}
    {targetState : ReconfiguredExecutionState
      (constitution.operational nextContract).family}
    (obligations : AutonomousTransitionObligations constitution current
      transition targetState)
    (obligation : constitution.PersistentObligation
      currentContract nextContract) :
    constitution.TargetPersistentWitness currentContract nextContract
      obligation :=
  transition.transport obligation (obligations.persistentSource obligation)

def AutonomousTransitionObligations.rechecked
    {constitution : ConstitutiveMetaContract}
    {currentContract nextContract : constitution.Contract}
    {current : CheckedAgent constitution currentContract}
    {transition : OperationalContractTransition constitution
      currentContract nextContract}
    {targetState : ReconfiguredExecutionState
      (constitution.operational nextContract).family}
    (_obligations : AutonomousTransitionObligations constitution current
      transition targetState)
    (obligation : constitution.RecheckObligation currentContract nextContract) :
    constitution.RecheckedWitness currentContract nextContract obligation :=
  transition.recheck obligation

/-- A current-agent-indexed decision interface.  Its local condition type is
fixed before `decide` runs and the result is either a positive construction or
a constructive refusal.  The interface cannot mention the success of a full
checker because no checker or checked-update result occurs in its type. -/
structure CurrentAgentTransitionInterface
    (constitution : ConstitutiveMetaContract)
    {currentContract : constitution.Contract}
    (current : CheckedAgent constitution currentContract) : Type 7 where
  Request : constitution.Contract -> Type 4
  LocalConditions : {nextContract : constitution.Contract} ->
    Request nextContract -> Type 5
  decide : {nextContract : constitution.Contract} ->
    (request : Request nextContract) ->
      PSum (LocalConditions request) (LocalConditions request -> False)

/-! ## Contract-governed continuations after exact forgetting -/

/-- The reduced memory produced from the exact current state by the future
realization already stored in its state certificate. -/
structure ForgottenCurrentAgent
    {constitution : ConstitutiveMetaContract}
    {currentContract : constitution.Contract}
    (current : CheckedAgent constitution currentContract) : Type 5 where
  memory : current.certificate.futureRealization.ReducedMemory
  memoryExact : memory =
    current.certificate.futureRealization.project
      ((constitution.operational currentContract).futureSourceOfState
        current.state)

def forgetCurrentAgent
    {constitution : ConstitutiveMetaContract}
    {currentContract : constitution.Contract}
    (current : CheckedAgent constitution currentContract) :
    ForgottenCurrentAgent current :=
  { memory := current.certificate.futureRealization.project
      ((constitution.operational currentContract).futureSourceOfState
        current.state)
    memoryExact := rfl }

/-- Requests after forgetting remain inside the existing operational contract
API: either continue under the current contract's reduced future semantics, or
request one of the fixed meta-contract's contract transitions. -/
inductive PostForgettingRequest
    {constitution : ConstitutiveMetaContract}
    {currentContract : constitution.Contract}
    (current : CheckedAgent constitution currentContract) : Type 4 where
  | continueCurrent
      (input : (constitution.operational currentContract).FutureInput)
  | changeContract (nextContract : constitution.Contract)

/-- A contract change after forgetting must use an admitted transition of the
same meta-contract and provide every source witness needed for its directed
persistent transport.  Invalidated obligations are rechecked by that exact
transition, never silently copied. -/
structure JustifiedPostForgettingTransition
    {constitution : ConstitutiveMetaContract}
    {currentContract : constitution.Contract}
    (current : CheckedAgent constitution currentContract)
    (nextContract : constitution.Contract) : Type 6 where
  transition : OperationalContractTransition constitution
    currentContract nextContract
  persistentSource : (obligation :
    constitution.PersistentObligation currentContract nextContract) ->
      constitution.SourcePersistentWitness currentContract nextContract
        obligation

def JustifiedPostForgettingTransition.transportedPersistent
    {constitution : ConstitutiveMetaContract}
    {currentContract nextContract : constitution.Contract}
    {current : CheckedAgent constitution currentContract}
    (justification : JustifiedPostForgettingTransition current nextContract)
    (obligation : constitution.PersistentObligation
      currentContract nextContract) :
    constitution.TargetPersistentWitness currentContract nextContract
      obligation :=
  justification.transition.transport obligation
    (justification.persistentSource obligation)

def JustifiedPostForgettingTransition.rechecked
    {constitution : ConstitutiveMetaContract}
    {currentContract nextContract : constitution.Contract}
    {current : CheckedAgent constitution currentContract}
    (justification : JustifiedPostForgettingTransition current nextContract)
    (obligation : constitution.RecheckObligation currentContract nextContract) :
    constitution.RecheckedWitness currentContract nextContract obligation :=
  justification.transition.recheck obligation

/-- Positive permission for a request after forgetting.  Current-contract
continuation consumes the reduced contract's own `Allow`; contract change
consumes a justified transition of the same meta-contract. -/
inductive PostForgettingPermission
    {constitution : ConstitutiveMetaContract}
    {currentContract : constitution.Contract}
    (current : CheckedAgent constitution currentContract)
    (forgotten : ForgottenCurrentAgent current) :
    PostForgettingRequest current -> Type 7 where
  | continueCurrent
      (input : (constitution.operational currentContract).FutureInput)
      (allowed : current.certificate.futureRealization.reducedContract.Allow
        forgotten.memory input) :
      PostForgettingPermission current forgotten (.continueCurrent input)
  | changeContract
      (nextContract : constitution.Contract)
      (justification : JustifiedPostForgettingTransition current nextContract) :
      PostForgettingPermission current forgotten (.changeContract nextContract)

/-- An admissibility decision after forgetting is explicitly positive or a
constructive refusal.  It is not an effectful runtime operation. -/
abbrev PostForgettingDecision
    {constitution : ConstitutiveMetaContract}
    {currentContract : constitution.Contract}
    (current : CheckedAgent constitution currentContract)
    (forgotten : ForgottenCurrentAgent current)
    (request : PostForgettingRequest current) : Type 7 :=
  PSum (PostForgettingPermission current forgotten request)
    (PostForgettingPermission current forgotten request -> False)

end ConstitutiveSearch.NeuralAgent
/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.NeuralAgent.AutonomousReconfigurationConditions
#print axioms ConstitutiveSearch.NeuralAgent.AutonomousReconfigurationConditions.execute
#print axioms ConstitutiveSearch.NeuralAgent.AutonomousReconfigurationConditions.executed_target_exact
#print axioms ConstitutiveSearch.NeuralAgent.ContractObligationsAt
#print axioms ConstitutiveSearch.NeuralAgent.StateConstitutiveCertificate.obligationsAt
#print axioms ConstitutiveSearch.NeuralAgent.ContractFutureObservationAt
#print axioms ConstitutiveSearch.NeuralAgent.contractFutureObservationAt
#print axioms ConstitutiveSearch.NeuralAgent.ContractFutureObservationAt.outcome_exact
#print axioms ConstitutiveSearch.NeuralAgent.AutonomousTransitionObligations
#print axioms ConstitutiveSearch.NeuralAgent.AutonomousTransitionObligations.transportedPersistent
#print axioms ConstitutiveSearch.NeuralAgent.AutonomousTransitionObligations.rechecked
#print axioms ConstitutiveSearch.NeuralAgent.CurrentAgentTransitionInterface
#print axioms ConstitutiveSearch.NeuralAgent.ForgottenCurrentAgent
#print axioms ConstitutiveSearch.NeuralAgent.forgetCurrentAgent
#print axioms ConstitutiveSearch.NeuralAgent.PostForgettingRequest
#print axioms ConstitutiveSearch.NeuralAgent.JustifiedPostForgettingTransition
#print axioms ConstitutiveSearch.NeuralAgent.JustifiedPostForgettingTransition.transportedPersistent
#print axioms ConstitutiveSearch.NeuralAgent.JustifiedPostForgettingTransition.rechecked
#print axioms ConstitutiveSearch.NeuralAgent.PostForgettingPermission
#print axioms ConstitutiveSearch.NeuralAgent.PostForgettingDecision
/- AXIOM_AUDIT_END -/
