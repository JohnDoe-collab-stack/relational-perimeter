import RelationalPerimeter.Agents.Neural.CoveredFutureRealization

/-!
# Constitutive certificates for exact neural states

A state certificate is indexed by the fixed operational contract, the exact
decoded artifact, and the exact execution state.  It consumes the finite
causal basis and all seven contract obligation families.  Future preservation
is supplied by the existing exact-realization layer, not by a new runtime.
-/
set_option genInjectivity false
namespace ConstitutiveSearch.NeuralAgent

/-- The complete constitutive evidence attached to one exact execution state.
The constructor is private: later checkers may return this object, but callers
cannot assemble a checked state by replacing one of its dependencies. -/
structure StateConstitutiveCertificate
    (contract : ConstitutiveContract)
    (artifact : DecodedNeuralArtifact contract)
    (state : ReconfiguredExecutionState contract.family) : Type 4 where
  private mk ::
  basis : FiniteCausalBasis contract artifact
  systemExact : state.system = artifact.system
  inputDeclared : Listed state.input contract.declaredCurrentInputs
  requirementEncodingWitness :
    contract.requirementEncoding.Witness
      (contract.requirementEncodingAt state)
  causalConditionWitness :
    contract.causalCondition.Witness
      (contract.causalConditionAt state)
  proposalActionWitness :
    contract.proposalActionPreservation.Witness
      (contract.proposalActionPreservationAt state)
  authorizationWitness :
    contract.authorizationAdmission.Witness
      (contract.authorizationAdmissionAt state)
  effectWitness :
    contract.effectSatisfaction.Witness
      (contract.effectSatisfactionAt state)
  coveredFutureWitness :
    (requests : List (RequirementInput contract.family)) ->
      contract.coveredFuture.Witness (contract.coveredFutureAt state requests)
  historicalWitness :
    contract.historicalPolicy.Witness (contract.historicalPolicyAt state)
  futureRealization : CoveredFutureRealization contract

/-- The only public constructor requires every indexed witness explicitly. -/
def certifyStateConstitution
    {contract : ConstitutiveContract}
    {artifact : DecodedNeuralArtifact contract}
    {state : ReconfiguredExecutionState contract.family}
    (basis : FiniteCausalBasis contract artifact)
    (systemExact : state.system = artifact.system)
    (inputDeclared : Listed state.input contract.declaredCurrentInputs)
    (requirementEncodingWitness :
      contract.requirementEncoding.Witness
        (contract.requirementEncodingAt state))
    (causalConditionWitness :
      contract.causalCondition.Witness
        (contract.causalConditionAt state))
    (proposalActionWitness :
      contract.proposalActionPreservation.Witness
        (contract.proposalActionPreservationAt state))
    (authorizationWitness :
      contract.authorizationAdmission.Witness
        (contract.authorizationAdmissionAt state))
    (effectWitness :
      contract.effectSatisfaction.Witness
        (contract.effectSatisfactionAt state))
    (coveredFutureWitness :
      (requests : List (RequirementInput contract.family)) ->
        contract.coveredFuture.Witness (contract.coveredFutureAt state requests))
    (historicalWitness :
      contract.historicalPolicy.Witness (contract.historicalPolicyAt state))
    (futureRealization : CoveredFutureRealization contract) :
    StateConstitutiveCertificate contract artifact state :=
  .mk basis systemExact inputDeclared requirementEncodingWitness
    causalConditionWitness proposalActionWitness authorizationWitness
    effectWitness coveredFutureWitness historicalWitness futureRealization

/-- Declared-domain completeness places the certified input in the executable
finite domain of the attached basis. -/
def StateConstitutiveCertificate.inputInBasis
    {contract : ConstitutiveContract}
    {artifact : DecodedNeuralArtifact contract}
    {state : ReconfiguredExecutionState contract.family}
    (certificate : StateConstitutiveCertificate contract artifact state) :
    Listed state.input certificate.basis.currentInputs :=
  certificate.basis.currentInputsComplete state.input
    certificate.inputDeclared

/-- The certificate positively exposes the executed causal candidate selected
by the finite basis for this exact declared input. -/
def StateConstitutiveCertificate.causalCoverage
    {contract : ConstitutiveContract}
    {artifact : DecodedNeuralArtifact contract}
    {state : ReconfiguredExecutionState contract.family}
    (certificate : StateConstitutiveCertificate contract artifact state) :
    CausalCandidateCoverage artifact certificate.basis.naming
      certificate.basis.replacements state.input :=
  certificate.basis.replacementCoverage state.input
    certificate.inputDeclared

/-- The exact realization attached to the state preserves every finite future
from the future source selected by the same operational contract. -/
theorem StateConstitutiveCertificate.everyFiniteFuture
    {contract : ConstitutiveContract}
    {artifact : DecodedNeuralArtifact contract}
    {state : ReconfiguredExecutionState contract.family}
    (certificate : StateConstitutiveCertificate contract artifact state)
    (requests : List contract.FutureInput) :
    contract.futureContract.outcome (contract.futureSourceOfState state)
        requests =
      certificate.futureRealization.reducedContract.outcome
        (certificate.futureRealization.project
          (contract.futureSourceOfState state)) requests :=
  certificate.futureRealization.everyFiniteFuture
    (contract.futureSourceOfState state) requests

/-! ## Closed public initial state certificate -/

def publicInitialCoveredFutureRealization :
    CoveredFutureRealization PublicInitialOperationalContract where
  ReducedMemory := Agent.Memory
  reducedContract := reconfiguredOperationalMemoryFutureContract
  project := ReconfiguredExecutionState.memory
  simulation := FutureContractSimulationData.ofExactRealization
    publicReconfiguredOperationalMemoryRealization

def publicInitialCertifiedState :
    ReconfiguredExecutionState PublicInitialOperationalContract.family :=
  publicLeftHistoricalCurrentState

def publicInitialStateConstitutiveCertificate :
    StateConstitutiveCertificate PublicInitialOperationalContract
      publicDecodedRequirementArtifact publicInitialCertifiedState :=
  certifyStateConstitution publicFiniteCausalBasis rfl .head
    { incorporation :=
        publicRequirementIncorporation publicInitialCertifiedState.input }
    { role := publicRequirementCausalRole publicInitialCertifiedState.input }
    (publicAction publicInitialCertifiedState.input)
    { authorization :=
        publicReconfigurationAuthorization publicInitialCertifiedState.input }
    (publicEffect publicInitialCertifiedState.input)
    (fun requests => publicFiniteInteractionHistory requests)
    { historical := publicLeftHistoricalOperationalState
      currentExact := rfl }
    publicInitialCoveredFutureRealization

theorem publicInitialCertifiedState_allFutures
    (requests : List (ULift.{3} Agent.Request)) :
    PublicInitialOperationalContract.futureContract.outcome
        (PublicInitialOperationalContract.futureSourceOfState
          publicInitialCertifiedState) requests =
      publicInitialStateConstitutiveCertificate.futureRealization.reducedContract.outcome
        (publicInitialStateConstitutiveCertificate.futureRealization.project
          (PublicInitialOperationalContract.futureSourceOfState
            publicInitialCertifiedState)) requests :=
  publicInitialStateConstitutiveCertificate.everyFiniteFuture requests

/-! ## Closed full-reference successor certificate -/

/-- The reference update executes from the exact checked initial state. -/
def publicReferenceUpdateExecution :
    ReconfiguredActionEffect (builder := publicReconfigurationBuilder)
      publicAgentActionChannel publicInitialCertifiedState
        publicSubstantiveNext :=
  executeReconfiguredAction publicAgentActionChannel
    publicInitialCertifiedState publicSubstantiveNext
    (publicReconfigurationCertificateForState publicInitialCertifiedState
      publicSubstantiveNext)

def publicReferenceUpdatedState :
    ReconfiguredExecutionState publicRequirementFamily :=
  publicReferenceUpdateExecution.targetState

def publicReferenceProducedStateWitness :
    PublicProducedReconfiguredStateWitness publicReferenceUpdatedState :=
  { source := publicInitialCertifiedState
    next := publicSubstantiveNext
    production := publicReferenceUpdateExecution
    targetExact := rfl }

def publicReferenceUpdatedStateCertificate :
    StateConstitutiveCertificate PublicReconfiguredOperationalContract
      publicDecodedReconfiguredArtifact publicReferenceUpdatedState :=
  certifyStateConstitution publicReconfiguredFiniteCausalBasis rfl .head
    { production := publicReferenceProducedStateWitness }
    { production := publicReferenceProducedStateWitness }
    { production := publicReferenceProducedStateWitness }
    { production := publicReferenceProducedStateWitness }
    { production := publicReferenceProducedStateWitness }
    (fun requests =>
      executeReconfiguredInteractions publicReconfigurationBuilder
        publicAgentActionChannel publicReconfigurationCertificateForState
        publicReferenceUpdatedState requests)
    publicReferenceProducedStateWitness
    publicCoveredFutureRealization

theorem publicReferenceUpdatedState_allFutures
    (requests : List (ULift.{3} Agent.Request)) :
    PublicReconfiguredOperationalContract.futureContract.outcome
        publicReferenceUpdatedState requests =
      publicReferenceUpdatedStateCertificate.futureRealization.reducedContract.outcome
        (publicReferenceUpdatedStateCertificate.futureRealization.project
          publicReferenceUpdatedState) requests :=
  publicReferenceUpdatedStateCertificate.everyFiniteFuture requests

end ConstitutiveSearch.NeuralAgent
/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.NeuralAgent.StateConstitutiveCertificate
#print axioms ConstitutiveSearch.NeuralAgent.certifyStateConstitution
#print axioms ConstitutiveSearch.NeuralAgent.StateConstitutiveCertificate.inputInBasis
#print axioms ConstitutiveSearch.NeuralAgent.StateConstitutiveCertificate.causalCoverage
#print axioms ConstitutiveSearch.NeuralAgent.StateConstitutiveCertificate.everyFiniteFuture
#print axioms ConstitutiveSearch.NeuralAgent.publicInitialCoveredFutureRealization
#print axioms ConstitutiveSearch.NeuralAgent.publicInitialCertifiedState
#print axioms ConstitutiveSearch.NeuralAgent.publicInitialStateConstitutiveCertificate
#print axioms ConstitutiveSearch.NeuralAgent.publicInitialCertifiedState_allFutures
#print axioms ConstitutiveSearch.NeuralAgent.publicReferenceUpdateExecution
#print axioms ConstitutiveSearch.NeuralAgent.publicReferenceUpdatedState
#print axioms ConstitutiveSearch.NeuralAgent.publicReferenceProducedStateWitness
#print axioms ConstitutiveSearch.NeuralAgent.publicReferenceUpdatedStateCertificate
#print axioms ConstitutiveSearch.NeuralAgent.publicReferenceUpdatedState_allFutures
/- AXIOM_AUDIT_END -/
