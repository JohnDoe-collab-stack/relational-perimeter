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
open NativeMechanism

/-- Constructively enumerate every location used by the structural certificate
snapshot.  This definition lives before certificate assembly, so an
incremental assembly can construct the snapshot without an already-built
target certificate. -/
def structuralLocations : (count : Nat) -> List (Fin count)
  | 0 => []
  | count + 1 =>
      ⟨0, Nat.zero_lt_succ count⟩ ::
        (structuralLocations count).map Fin.succ

/-- A weighted read expressed through its persistent source identity. -/
structure StableWeightedRead where
  source : StableNodeKey
  weight : Int

/-- The stable artifact-local observation retained by a state certificate. -/
inductive StableArtifactObservation where
  | receivedInput
  | neuron (reads : List StableWeightedRead) (bias threshold : Int)
  | outputPort (source : StableNodeKey)

def StableArtifactNaming.weightedRead
    {contract : ConstitutiveContract}
    {artifact : DecodedNeuralArtifact contract}
    (naming : StableArtifactNaming artifact)
    (target : Fin artifact.system.producedCount)
    (edge : WeightedInput artifact.system.inputCount target.val) :
    StableWeightedRead :=
  { source := (naming.sourceNode target edge.source).key
    weight := edge.weight }

def StableArtifactNaming.mechanismObservation
    {contract : ConstitutiveContract}
    {artifact : DecodedNeuralArtifact contract}
    (naming : StableArtifactNaming artifact) :
    StableNodeId naming -> StableArtifactObservation
  | .receivedInput _ => .receivedInput
  | .neuron target =>
      let neuron := artifact.system.program.neuronAt target
      .neuron (neuron.inputs.map (naming.weightedRead target))
        neuron.bias neuron.threshold.level

def StableArtifactNaming.outputObservation
    {contract : ConstitutiveContract}
    {artifact : DecodedNeuralArtifact contract}
    (naming : StableArtifactNaming artifact)
    (port : StableOutputPortId naming) : StableArtifactObservation :=
  .outputPort
    (StableNodeId.neuron
      (naming := naming)
      (artifact.system.outputs.sources.get port.index)).key

/-- Complete artifact-local observation snapshot computed from the decoded
artifact and its stable naming, before any state certificate exists. -/
def stableStructuralObservationSnapshot
    {contract : ConstitutiveContract}
    {artifact : DecodedNeuralArtifact contract}
    (naming : StableArtifactNaming artifact) :
    List (StableNodeKey × StableArtifactObservation) :=
  (structuralLocations artifact.system.inputCount).map (fun index =>
      let node : StableNodeId naming := .receivedInput index
      (node.key, naming.mechanismObservation node)) ++
  (structuralLocations artifact.system.producedCount).map (fun index =>
      let node : StableNodeId naming := .neuron index
      (node.key, naming.mechanismObservation node)) ++
  (structuralLocations artifact.system.outputs.sources.length).map (fun index =>
      let port := naming.outputPort index
      (port.key, naming.outputObservation port))

def lookupStructuralObservation (key : StableNodeKey) :
    List (StableNodeKey × StableArtifactObservation) ->
      Option StableArtifactObservation
  | [] => none
  | entry :: rest =>
      if entry.1 = key then some entry.2
      else lookupStructuralObservation key rest

/-- Stable structural evidence for one exact state.  The finite basis carries
the stable artifact naming and its executed causal coverage; the two remaining
fields tie that basis to the exact decoded system and current input. -/
structure StableStructuralCertificateFragment
    (contract : ConstitutiveContract)
    (artifact : DecodedNeuralArtifact contract)
    (state : ReconfiguredExecutionState contract.family) : Type 4 where
  basis : FiniteCausalBasis contract artifact
  systemExact : state.system = artifact.system
  inputDeclared : Listed state.input contract.declaredCurrentInputs
  observations : List (StableNodeKey × StableArtifactObservation)
  observationsExact :
    observations = stableStructuralObservationSnapshot basis.naming

/-- Exact requirement-encoding obligation for the indexed state. -/
structure RequirementEncodingCertificateFragment
    (contract : ConstitutiveContract)
    (_artifact : DecodedNeuralArtifact contract)
    (state : ReconfiguredExecutionState contract.family) : Type 4 where
  witness : contract.requirementEncoding.Witness
    (contract.requirementEncodingAt state)

/-- Exact executed causal-role obligation for the indexed state. -/
structure ExecutedCausalRoleCertificateFragment
    (contract : ConstitutiveContract)
    (_artifact : DecodedNeuralArtifact contract)
    (state : ReconfiguredExecutionState contract.family) : Type 4 where
  witness : contract.causalCondition.Witness
    (contract.causalConditionAt state)

/-- Exact preservation of the proposition-to-action passage. -/
structure ProposalActionCertificateFragment
    (contract : ConstitutiveContract)
    (_artifact : DecodedNeuralArtifact contract)
    (state : ReconfiguredExecutionState contract.family) : Type 4 where
  witness : contract.proposalActionPreservation.Witness
    (contract.proposalActionPreservationAt state)

/-- Exact authorization admitted for the indexed state. -/
structure AuthorizationCertificateFragment
    (contract : ConstitutiveContract)
    (_artifact : DecodedNeuralArtifact contract)
    (state : ReconfiguredExecutionState contract.family) : Type 4 where
  witness : contract.authorizationAdmission.Witness
    (contract.authorizationAdmissionAt state)

/-- Exact effect obligation at the produced successor state. -/
structure EffectSuccessorCertificateFragment
    (contract : ConstitutiveContract)
    (_artifact : DecodedNeuralArtifact contract)
    (state : ReconfiguredExecutionState contract.family) : Type 4 where
  witness : contract.effectSatisfaction.Witness
    (contract.effectSatisfactionAt state)

/-- Exact historical policy attached to the indexed state. -/
structure HistoricalPolicyCertificateFragment
    (contract : ConstitutiveContract)
    (_artifact : DecodedNeuralArtifact contract)
    (state : ReconfiguredExecutionState contract.family) : Type 4 where
  witness : contract.historicalPolicy.Witness
    (contract.historicalPolicyAt state)

/-- Coverage and exact realization of every finite future owned by the
contract.  These two parts stay together because coverage without its exact
realization is not a complete future fragment. -/
structure CoveredFutureCertificateFragment
    (contract : ConstitutiveContract)
    (_artifact : DecodedNeuralArtifact contract)
    (state : ReconfiguredExecutionState contract.family) : Type 4 where
  covered : (requests : List (RequirementInput contract.family)) ->
    contract.coveredFuture.Witness (contract.coveredFutureAt state requests)
  realization : CoveredFutureRealization contract

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
  structuralObservations : List (StableNodeKey × StableArtifactObservation)
  structuralObservationsExact :
    structuralObservations = stableStructuralObservationSnapshot basis.naming
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

/-- The complete dependent decomposition of a state certificate.  Every field
is indexed by the same exact contract, artifact, and state; a fragment from a
different source cannot be inserted by equality of its payload alone. -/
structure StateCertificateFragments
    (contract : ConstitutiveContract)
    (artifact : DecodedNeuralArtifact contract)
    (state : ReconfiguredExecutionState contract.family) : Type 4 where
  structural : StableStructuralCertificateFragment contract artifact state
  requirement : RequirementEncodingCertificateFragment contract artifact state
  causal : ExecutedCausalRoleCertificateFragment contract artifact state
  proposalAction : ProposalActionCertificateFragment contract artifact state
  authorization : AuthorizationCertificateFragment contract artifact state
  effect : EffectSuccessorCertificateFragment contract artifact state
  historical : HistoricalPolicyCertificateFragment contract artifact state
  futures : CoveredFutureCertificateFragment contract artifact state

/-- Assemble a target certificate from its dependent fragments only.  No
already-built target certificate is accepted as an argument. -/
def assembleStateConstitution
    {contract : ConstitutiveContract}
    {artifact : DecodedNeuralArtifact contract}
    {state : ReconfiguredExecutionState contract.family}
    (fragments : StateCertificateFragments contract artifact state) :
    StateConstitutiveCertificate contract artifact state :=
  .mk fragments.structural.basis fragments.structural.systemExact
    fragments.structural.inputDeclared fragments.structural.observations
    fragments.structural.observationsExact fragments.requirement.witness
    fragments.causal.witness fragments.proposalAction.witness
    fragments.authorization.witness fragments.effect.witness
    fragments.futures.covered fragments.historical.witness
    fragments.futures.realization

/-- Decompose an existing certificate without changing any witness. -/
def StateConstitutiveCertificate.fragments
    {contract : ConstitutiveContract}
    {artifact : DecodedNeuralArtifact contract}
    {state : ReconfiguredExecutionState contract.family}
    (certificate : StateConstitutiveCertificate contract artifact state) :
    StateCertificateFragments contract artifact state :=
  { structural :=
      { basis := certificate.basis
        systemExact := certificate.systemExact
        inputDeclared := certificate.inputDeclared
        observations := certificate.structuralObservations
        observationsExact := certificate.structuralObservationsExact }
    requirement := { witness := certificate.requirementEncodingWitness }
    causal := { witness := certificate.causalConditionWitness }
    proposalAction := { witness := certificate.proposalActionWitness }
    authorization := { witness := certificate.authorizationWitness }
    effect := { witness := certificate.effectWitness }
    historical := { witness := certificate.historicalWitness }
    futures :=
      { covered := certificate.coveredFutureWitness
        realization := certificate.futureRealization } }

theorem assemble_fragments_exact
    {contract : ConstitutiveContract}
    {artifact : DecodedNeuralArtifact contract}
    {state : ReconfiguredExecutionState contract.family}
    (certificate : StateConstitutiveCertificate contract artifact state) :
    assembleStateConstitution certificate.fragments = certificate := by
  cases certificate
  rfl

theorem fragments_assemble_exact
    {contract : ConstitutiveContract}
    {artifact : DecodedNeuralArtifact contract}
    {state : ReconfiguredExecutionState contract.family}
    (fragments : StateCertificateFragments contract artifact state) :
    (assembleStateConstitution fragments).fragments = fragments := by
  cases fragments
  rfl

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
  assembleStateConstitution
    { structural :=
        { basis := basis
          systemExact := systemExact
          inputDeclared := inputDeclared
          observations := stableStructuralObservationSnapshot basis.naming
          observationsExact := rfl }
      requirement := { witness := requirementEncodingWitness }
      causal := { witness := causalConditionWitness }
      proposalAction := { witness := proposalActionWitness }
      authorization := { witness := authorizationWitness }
      effect := { witness := effectWitness }
      historical := { witness := historicalWitness }
      futures :=
        { covered := coveredFutureWitness
          realization := futureRealization } }

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

def publicInitialStateCertificateFragments :
    StateCertificateFragments PublicInitialOperationalContract
      publicDecodedRequirementArtifact publicInitialCertifiedState :=
  { structural :=
      { basis := publicFiniteCausalBasis
        systemExact := rfl
        inputDeclared := .head
        observations :=
          stableStructuralObservationSnapshot publicFiniteCausalBasis.naming
        observationsExact := rfl }
    requirement :=
      { witness :=
          { incorporation :=
              publicRequirementIncorporation publicInitialCertifiedState.input } }
    causal :=
      { witness :=
          { role :=
              publicRequirementCausalRole publicInitialCertifiedState.input } }
    proposalAction :=
      { witness := publicAction publicInitialCertifiedState.input }
    authorization :=
      { witness :=
          { authorization :=
              publicReconfigurationAuthorization
                publicInitialCertifiedState.input } }
    effect := { witness := publicEffect publicInitialCertifiedState.input }
    historical :=
      { witness :=
          { historical := publicLeftHistoricalOperationalState
            currentExact := rfl } }
    futures :=
      { covered := fun requests => publicFiniteInteractionHistory requests
        realization := publicInitialCoveredFutureRealization } }

def publicInitialStateConstitutiveCertificate :
    StateConstitutiveCertificate PublicInitialOperationalContract
      publicDecodedRequirementArtifact publicInitialCertifiedState :=
  assembleStateConstitution publicInitialStateCertificateFragments

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

def publicReferenceUpdatedStateFragments :
    StateCertificateFragments PublicReconfiguredOperationalContract
      publicDecodedReconfiguredArtifact publicReferenceUpdatedState :=
  { structural :=
      { basis := publicReconfiguredFiniteCausalBasis
        systemExact := rfl
        inputDeclared := .head
        observations := stableStructuralObservationSnapshot
          publicReconfiguredFiniteCausalBasis.naming
        observationsExact := rfl }
    requirement :=
      { witness := { production := publicReferenceProducedStateWitness } }
    causal :=
      { witness := { production := publicReferenceProducedStateWitness } }
    proposalAction :=
      { witness := { production := publicReferenceProducedStateWitness } }
    authorization :=
      { witness := { production := publicReferenceProducedStateWitness } }
    effect :=
      { witness := { production := publicReferenceProducedStateWitness } }
    historical :=
      { witness := publicReferenceProducedStateWitness }
    futures :=
      { covered := fun requests =>
          executeReconfiguredInteractions publicReconfigurationBuilder
            publicAgentActionChannel publicReconfigurationCertificateForState
            publicReferenceUpdatedState requests
        realization := publicCoveredFutureRealization } }

def publicReferenceUpdatedStateCertificate :
    StateConstitutiveCertificate PublicReconfiguredOperationalContract
      publicDecodedReconfiguredArtifact publicReferenceUpdatedState :=
  assembleStateConstitution publicReferenceUpdatedStateFragments

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
#print axioms ConstitutiveSearch.NeuralAgent.structuralLocations
#print axioms ConstitutiveSearch.NeuralAgent.StableWeightedRead
#print axioms ConstitutiveSearch.NeuralAgent.StableArtifactObservation
#print axioms ConstitutiveSearch.NeuralAgent.StableArtifactNaming.weightedRead
#print axioms ConstitutiveSearch.NeuralAgent.StableArtifactNaming.mechanismObservation
#print axioms ConstitutiveSearch.NeuralAgent.StableArtifactNaming.outputObservation
#print axioms ConstitutiveSearch.NeuralAgent.stableStructuralObservationSnapshot
#print axioms ConstitutiveSearch.NeuralAgent.lookupStructuralObservation
#print axioms ConstitutiveSearch.NeuralAgent.StableStructuralCertificateFragment
#print axioms ConstitutiveSearch.NeuralAgent.RequirementEncodingCertificateFragment
#print axioms ConstitutiveSearch.NeuralAgent.ExecutedCausalRoleCertificateFragment
#print axioms ConstitutiveSearch.NeuralAgent.ProposalActionCertificateFragment
#print axioms ConstitutiveSearch.NeuralAgent.AuthorizationCertificateFragment
#print axioms ConstitutiveSearch.NeuralAgent.EffectSuccessorCertificateFragment
#print axioms ConstitutiveSearch.NeuralAgent.HistoricalPolicyCertificateFragment
#print axioms ConstitutiveSearch.NeuralAgent.CoveredFutureCertificateFragment
#print axioms ConstitutiveSearch.NeuralAgent.StateConstitutiveCertificate
#print axioms ConstitutiveSearch.NeuralAgent.StateCertificateFragments
#print axioms ConstitutiveSearch.NeuralAgent.assembleStateConstitution
#print axioms ConstitutiveSearch.NeuralAgent.StateConstitutiveCertificate.fragments
#print axioms ConstitutiveSearch.NeuralAgent.assemble_fragments_exact
#print axioms ConstitutiveSearch.NeuralAgent.fragments_assemble_exact
#print axioms ConstitutiveSearch.NeuralAgent.certifyStateConstitution
#print axioms ConstitutiveSearch.NeuralAgent.StateConstitutiveCertificate.inputInBasis
#print axioms ConstitutiveSearch.NeuralAgent.StateConstitutiveCertificate.causalCoverage
#print axioms ConstitutiveSearch.NeuralAgent.StateConstitutiveCertificate.everyFiniteFuture
#print axioms ConstitutiveSearch.NeuralAgent.publicInitialCoveredFutureRealization
#print axioms ConstitutiveSearch.NeuralAgent.publicInitialCertifiedState
#print axioms ConstitutiveSearch.NeuralAgent.publicInitialStateCertificateFragments
#print axioms ConstitutiveSearch.NeuralAgent.publicInitialStateConstitutiveCertificate
#print axioms ConstitutiveSearch.NeuralAgent.publicInitialCertifiedState_allFutures
#print axioms ConstitutiveSearch.NeuralAgent.publicReferenceUpdateExecution
#print axioms ConstitutiveSearch.NeuralAgent.publicReferenceUpdatedState
#print axioms ConstitutiveSearch.NeuralAgent.publicReferenceProducedStateWitness
#print axioms ConstitutiveSearch.NeuralAgent.publicReferenceUpdatedStateFragments
#print axioms ConstitutiveSearch.NeuralAgent.publicReferenceUpdatedStateCertificate
#print axioms ConstitutiveSearch.NeuralAgent.publicReferenceUpdatedState_allFutures
/- AXIOM_AUDIT_END -/
