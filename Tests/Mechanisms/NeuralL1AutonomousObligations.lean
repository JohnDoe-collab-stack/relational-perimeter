import RelationalPerimeter.Agents.Neural.AutonomousContractTransitions
import RelationalPerimeter.Agents.Neural.ReferenceChecker

/-!
# L1 regression: autonomous obligations and expected transitions

These witnesses exercise the RC1/RC3 specification without supplying a full
checker verdict.  They use the exact public source state, its fixed contract,
the existing meta-contract transition and the existing future realization.
-/
namespace Tests.Mechanisms.NeuralL1AutonomousObligations
open ConstitutiveSearch ConstitutiveSearch.NeuralAgent
open ConstitutiveSearch.NativeMechanism ContinuationSignatures

def publicAutonomousReconfigurationConditions :
    AutonomousReconfigurationConditions publicReconfigurationBuilder
      publicRequirementSystem publicSubstantiveSource publicSubstantiveNext :=
  { sourceRun := publicRequirementSystem.run publicSubstantiveSource
    sourceRunExact := rfl
    authorization := publicReconfigurationAuthorization publicSubstantiveNext }

theorem publicAutonomousReconfiguration_target_exact :
    publicAutonomousReconfigurationConditions.execute.targetSystem =
      publicReconfigurationBuilder.build publicRequirementSystem
        publicAutonomousReconfigurationConditions.sourceRun
        publicSubstantiveNext
        publicAutonomousReconfigurationConditions.authorization :=
  publicAutonomousReconfigurationConditions.executed_target_exact

def publicInitialAutonomousObligations : ContractObligationsAt
    PublicInitialOperationalContract publicInitialCheckedAgent.state :=
  publicInitialCheckedAgent.certificate.obligationsAt

def publicInitialFutureObservation : ContractFutureObservationAt
    PublicInitialOperationalContract publicInitialCheckedAgent.state :=
  contractFutureObservationAt publicInitialCheckedAgent.state

theorem publicInitialFutureObservation_realized
    (requests : List PublicInitialOperationalContract.FutureInput) :
    PublicInitialOperationalContract.futureContract.outcome
        publicInitialFutureObservation.source requests =
      publicInitialCheckedAgent.certificate.futureRealization.reducedContract.outcome
        (publicInitialCheckedAgent.certificate.futureRealization.project
          publicInitialFutureObservation.source) requests :=
  publicInitialFutureObservation.outcome_exact
    publicInitialCheckedAgent.certificate.futureRealization.exact requests

def publicAutonomousTransitionObligations :
    AutonomousTransitionObligations publicConstitutiveMetaContract
      publicInitialCheckedAgent publicOperationalTransition
      publicReferenceNextCheckedAgent.state :=
  { execution := publicReferenceTransitionProduction.execution
    sourceObligations := publicInitialCheckedAgent.certificate.obligationsAt
    sourceObservation := contractFutureObservationAt
      publicInitialCheckedAgent.state
    targetObligations := publicReferenceNextCheckedAgent.certificate.obligationsAt
    targetObservation := contractFutureObservationAt
      publicReferenceNextCheckedAgent.state
    persistentSource := fun obligation => by
      cases obligation
      exact { exact := public_required_action_distinction } }

def publicAutonomousTransition_transport_is_constructed :
    publicConstitutiveMetaContract.TargetPersistentWitness .initial
      .reconfigured .actionDistinction :=
  publicAutonomousTransitionObligations.transportedPersistent
    .actionDistinction

def publicAutonomousTransition_recheck_is_constructed :
    publicConstitutiveMetaContract.RecheckedWitness .initial .reconfigured
      .incorporatedAuthorization :=
  publicAutonomousTransitionObligations.rechecked .incorporatedAuthorization

def publicCurrentAgentTransitionInterface :
    CurrentAgentTransitionInterface publicConstitutiveMetaContract
      publicInitialCheckedAgent where
  Request := fun nextContract =>
    ULift.{4} (PublicContractTransitionPermission .initial nextContract)
  LocalConditions := fun {nextContract} _permission =>
    ULift.{5} (OperationalContractTransition publicConstitutiveMetaContract
      .initial nextContract)
  decide := by
    intro nextContract request
    cases request.down
    exact .inl (ULift.up publicOperationalTransition)

def publicForgottenCurrentAgent : ForgottenCurrentAgent
    publicInitialCheckedAgent :=
  forgetCurrentAgent publicInitialCheckedAgent

def publicContinuationAfterForgetting
    :
    PostForgettingPermission publicInitialCheckedAgent
      publicForgottenCurrentAgent
      (.continueCurrent publicTerminalAdmittedRequest) :=
  @PostForgettingPermission.continueCurrent publicConstitutiveMetaContract
    .initial publicInitialCheckedAgent publicForgottenCurrentAgent
    publicTerminalAdmittedRequest (ULift.up ())

def publicJustifiedContractChangeAfterForgetting :
    JustifiedPostForgettingTransition publicInitialCheckedAgent
      (forgotten := publicForgottenCurrentAgent)
        PublicOperationalContract.reconfigured :=
  { reducedMemory := publicForgottenCurrentAgent.memory
    reducedMemoryExact := rfl
    transition := publicOperationalTransition
    persistentSource := fun obligation => by
      cases obligation
      exact { exact := public_required_action_distinction } }

def publicContractChangeAfterForgetting :
    PostForgettingPermission publicInitialCheckedAgent
      publicForgottenCurrentAgent
      (.changeContract PublicOperationalContract.reconfigured) :=
  @PostForgettingPermission.changeContract publicConstitutiveMetaContract
    .initial publicInitialCheckedAgent publicForgottenCurrentAgent
    PublicOperationalContract.reconfigured
    publicJustifiedContractChangeAfterForgetting

theorem reverseContractChangeAfterForgetting_refused
    (justification : JustifiedPostForgettingTransition
      publicReferenceNextCheckedAgent
        (forgotten := forgetCurrentAgent publicReferenceNextCheckedAgent)
        PublicOperationalContract.initial) :
    False := by
  nomatch justification.transition.permission

end Tests.Mechanisms.NeuralL1AutonomousObligations
/- AXIOM_AUDIT_BEGIN -/
#print axioms Tests.Mechanisms.NeuralL1AutonomousObligations.publicAutonomousReconfigurationConditions
#print axioms Tests.Mechanisms.NeuralL1AutonomousObligations.publicAutonomousReconfiguration_target_exact
#print axioms Tests.Mechanisms.NeuralL1AutonomousObligations.publicInitialAutonomousObligations
#print axioms Tests.Mechanisms.NeuralL1AutonomousObligations.publicInitialFutureObservation
#print axioms Tests.Mechanisms.NeuralL1AutonomousObligations.publicInitialFutureObservation_realized
#print axioms Tests.Mechanisms.NeuralL1AutonomousObligations.publicAutonomousTransitionObligations
#print axioms Tests.Mechanisms.NeuralL1AutonomousObligations.publicAutonomousTransition_transport_is_constructed
#print axioms Tests.Mechanisms.NeuralL1AutonomousObligations.publicAutonomousTransition_recheck_is_constructed
#print axioms Tests.Mechanisms.NeuralL1AutonomousObligations.publicCurrentAgentTransitionInterface
#print axioms Tests.Mechanisms.NeuralL1AutonomousObligations.publicForgottenCurrentAgent
#print axioms Tests.Mechanisms.NeuralL1AutonomousObligations.publicContinuationAfterForgetting
#print axioms Tests.Mechanisms.NeuralL1AutonomousObligations.publicJustifiedContractChangeAfterForgetting
#print axioms Tests.Mechanisms.NeuralL1AutonomousObligations.publicContractChangeAfterForgetting
#print axioms Tests.Mechanisms.NeuralL1AutonomousObligations.reverseContractChangeAfterForgetting_refused
/- AXIOM_AUDIT_END -/
