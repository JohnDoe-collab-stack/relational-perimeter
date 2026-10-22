import RelationalPerimeter.Agents.Neural.TransitionProduction

/-!
# Executable initial and full-reference update checkers

The initial checker is generic in one executable meta-contract interface.  It
decodes the complete received artifact, runs every announced finite reflected
decision, and constructs the exact checked agent indexed by that source.  The
public initial agent is a specialization of this algorithm, not a literal
embedded in it.  The full-reference update checker remains the public closed
reference for the later generic update step: it decodes the complete successor
network, checks the exact next requirement, and returns the `CheckedUpdate`
whose successor certificate consumes the executed reconfiguration.  Neither
serialized input contains a proof or a certificate.

This is deliberately the full reference checker.  Stable cross-version node
identifiers, affected-cone computation, and incremental certificate reuse are
later layers and are not simulated here.
-/
set_option genInjectivity false
set_option maxHeartbeats 2000000
namespace ConstitutiveSearch.NeuralAgent

/-- The finite list of local reflected decisions performed after complete
artifact decoding.  Every constructor identifies the exact decision that
returned `false`; no global semantic oracle is hidden in this error type. -/
inductive InitialStateCheckError where
  | causalBasis
  | system
  | declaredInput
  | requirement
  | context
  | authorization
  | action
  | effect
  | history
  | coveredFutures
  | futureRealization
  deriving DecidableEq

/-- Initial-check failures retain errors from the two external decoders and
separate them from rejection by one of the finite reflected decisions. -/
inductive InitialCheckError
    {constitution : ConstitutiveMetaContract}
    (interface : ExecutableMetaContractInterface constitution) where
  | contractName (problem : interface.ContractNameError)
  | artifact (problem : interface.ArtifactError)
  | contractNotAdmitted
  | state (problem : InitialStateCheckError)

/-- Check the finite local obligations for the exact state produced from one
decoded artifact.  The successful value contains only positive decision
equalities; `certifyState` reflects them into the dependent witnesses. -/
def checkInitialState
    {constitution : ConstitutiveMetaContract}
    (interface : ExecutableMetaContractInterface constitution)
    {source : interface.ReceivedArtifact}
    (decoded : interface.DecodedArtifact source) :
    Except InitialStateCheckError
      (ExecutableStateAcceptance interface decoded) :=
  if basis : (interface.basisDecision decoded).result = true then
    if system : (interface.systemDecision decoded).result = true then
      if declaredInput :
          (interface.declaredInputDecision decoded).result = true then
        if requirement :
            (interface.requirementDecision decoded).result = true then
          if context : (interface.contextDecision decoded).result = true then
            if authorization :
                (interface.authorizationDecision decoded).result = true then
              if action : (interface.actionDecision decoded).result = true then
                if effect :
                    (interface.effectDecision decoded).result = true then
                  if history :
                      (interface.historicalDecision decoded).result = true then
                    if coveredFutures :
                        (interface.coveredFuturesDecision decoded).result =
                          true then
                      if futureRealization :
                          (interface.futureRealizationDecision decoded).result =
                            true then
                        .ok
                          { basis := basis
                            system := system
                            declaredInput := declaredInput
                            requirement := requirement
                            context := context
                            authorization := authorization
                            action := action
                            effect := effect
                            historical := history
                            coveredFutures := coveredFutures
                            futureRealization := futureRealization }
                      else
                        .error .futureRealization
                    else
                      .error .coveredFutures
                  else
                    .error .history
                else
                  .error .effect
              else
                .error .action
            else
              .error .authorization
          else
            .error .context
        else
          .error .requirement
      else
        .error .declaredInput
    else
      .error .system
  else
    .error .causalBasis

/-- Exact successful output of the generic initial checker.  Its decoded
contract name and its decoded artifact are tied by injectivity of the
interface encoding.  The checked agent is reconstructed from the reflected
decisions, never supplied as an input to the checker. -/
structure InitialCheckSuccess
    {constitution : ConstitutiveMetaContract}
    (interface : ExecutableMetaContractInterface constitution)
    (source : interface.ReceivedArtifact) : Type 6 where
  private mk ::
  contractName : DecodedContractName constitution interface.encodeContract
    (interface.artifactContractCode source)
  decodedArtifact : interface.DecodedArtifact source
  contractExact :
    contractName.contract = interface.decodedContract decodedArtifact
  admissionAccepted :
    (interface.admissionDecision
      (interface.decodedContract decodedArtifact)).result = true
  stateAccepted : ExecutableStateAcceptance interface decodedArtifact

/-- The result agent consumes exactly the artifact-derived state and the
certificate reconstructed from the local reflected decisions. -/
def InitialCheckSuccess.checkedAgent
    {constitution : ConstitutiveMetaContract}
    {interface : ExecutableMetaContractInterface constitution}
    {source : interface.ReceivedArtifact}
    (success : InitialCheckSuccess interface source) :
    CheckedAgent constitution
      (interface.decodedContract success.decodedArtifact) :=
  certifyCheckedAgent
    ((interface.admissionDecision
      (interface.decodedContract success.decodedArtifact)).accept
        success.admissionAccepted)
    (interface.decodedNeuralArtifact success.decodedArtifact)
    (interface.stateOfArtifact success.decodedArtifact)
    (interface.certifyState success.stateAccepted)

/-- Generic executable initial checker.  Its only completeness boundary is
the finite family of decisions announced by the supplied interface. -/
def checkInitial
    {constitution : ConstitutiveMetaContract}
    (interface : ExecutableMetaContractInterface constitution)
    (source : interface.ReceivedArtifact) :
    Except (InitialCheckError interface) (InitialCheckSuccess interface source) :=
  match interface.decodeContractName (interface.artifactContractCode source) with
  | .error problem => .error (.contractName problem)
  | .ok contractName =>
      match interface.decodeReceivedArtifact source with
      | .error problem => .error (.artifact problem)
      | .ok decodedArtifact =>
          let contractExact :
              contractName.contract =
                interface.decodedContract decodedArtifact :=
            interface.encodeContractInjective
              (contractName.exact.trans
                (interface.decodedContractExact decodedArtifact).symm)
          if admissionAccepted :
              (interface.admissionDecision
                (interface.decodedContract decodedArtifact)).result = true then
            match checkInitialState interface decodedArtifact with
            | .error problem => .error (.state problem)
            | .ok stateAccepted =>
                .ok (.mk contractName decodedArtifact contractExact
                  admissionAccepted stateAccepted)
          else
            .error .contractNotAdmitted

inductive AlignmentError where
  | malformedArtifact (problem : ArtifactError)
  | malformedConstitutiveArtifact
      (problem : SerializedConstitutiveArtifactError)
  | unexpectedInitialArtifact
  | unexpectedSuccessorArtifact
  | successorMismatch
  | noAdmittedTransition
  | targetStateRejected (problem : InitialStateCheckError)
  deriving DecidableEq

def reflectedTrue (witness : Witness) : ReflectedDecision Witness :=
  { result := true
    reflect := fun _ => witness }

def reflectedFalse : ReflectedDecision Witness :=
  { result := false
    reflect := fun impossible => Bool.noConfusion impossible }

def encodePublicOperationalContract :
    PublicOperationalContract -> SerializedOperationalContractName
  | .initial => .initial
  | .reconfigured => .reconfigured

theorem encodePublicOperationalContract_injective :
    Function.Injective encodePublicOperationalContract := by
  intro left right same
  cases left <;> cases right <;> cases same <;> rfl

def decodePublicOperationalContractName
    (source : SerializedOperationalContractName) :
    Except Unit
      (DecodedContractName publicConstitutiveMetaContract
        encodePublicOperationalContract source) :=
  .ok
    { contract := source.decode
      exact := by cases source <;> rfl }

/-- The public executable interface currently admits both complete artifacts
owned by its fixed meta-contract.  The index records the exact received
artifact; a decoded value for one source cannot be reused for the other. -/
inductive PublicExecutableDecodedArtifact :
    SerializedConstitutiveArtifact -> Type 4 where
  | initial : PublicExecutableDecodedArtifact
      publicSerializedInitialConstitutiveArtifact
  | reconfigured : PublicExecutableDecodedArtifact
      publicSerializedReconfiguredConstitutiveArtifact

inductive PublicExecutableArtifactError where
  | malformed (problem : SerializedConstitutiveArtifactError)
  | locallyUnsupported
  deriving DecidableEq

def decodePublicExecutableArtifact
    (source : SerializedConstitutiveArtifact) :
    Except PublicExecutableArtifactError
      (PublicExecutableDecodedArtifact source) :=
  match decodeSerializedConstitutiveArtifact source with
  | .error problem => .error (.malformed problem)
  | .ok _decoded =>
      if initialExact : source =
          publicSerializedInitialConstitutiveArtifact then
        .ok (initialExact.symm ▸ PublicExecutableDecodedArtifact.initial)
      else if reconfiguredExact : source =
          publicSerializedReconfiguredConstitutiveArtifact then
        .ok
          (reconfiguredExact.symm ▸
            PublicExecutableDecodedArtifact.reconfigured)
      else
        .error .locallyUnsupported

def PublicExecutableDecodedArtifact.contract
    {source : SerializedConstitutiveArtifact} :
    PublicExecutableDecodedArtifact source -> PublicOperationalContract
  | .initial => .initial
  | .reconfigured => .reconfigured

def PublicExecutableDecodedArtifact.artifact
    {source : SerializedConstitutiveArtifact}
    (decoded : PublicExecutableDecodedArtifact source) :
    DecodedNeuralArtifact (publicOperationalContract decoded.contract) :=
  match decoded with
  | .initial => publicDecodedRequirementArtifact
  | .reconfigured => publicDecodedReconfiguredArtifact

def PublicExecutableDecodedArtifact.stableNaming
    {source : SerializedConstitutiveArtifact}
    (decoded : PublicExecutableDecodedArtifact source) :
    DecodedStableArtifactNaming decoded.artifact source.stableNaming :=
  match decoded with
  | .initial => publicDecodedInitialConstitutiveArtifact.stable
  | .reconfigured => publicDecodedReconfiguredConstitutiveArtifact.stable

def PublicExecutableDecodedArtifact.state
    {source : SerializedConstitutiveArtifact}
    (decoded : PublicExecutableDecodedArtifact source) :
    ReconfiguredExecutionState
      (publicOperationalContract decoded.contract).family :=
  match decoded with
  | .initial => publicInitialCertifiedState
  | .reconfigured => publicReferenceUpdatedState

/-- Recompute every dependent certificate fragment from the exact decoded
artifact and its executed state.  This construction deliberately does not
project an already assembled certificate. -/
def PublicExecutableDecodedArtifact.recomputedFragments
    {source : SerializedConstitutiveArtifact}
    (decoded : PublicExecutableDecodedArtifact source) :
    StateCertificateFragments
      (publicOperationalContract decoded.contract) decoded.artifact
      decoded.state :=
  match decoded with
  | .initial =>
      { structural :=
          { basis := publicFiniteCausalBasis
            systemExact := rfl
            inputDeclared := .head
            observations := stableStructuralObservationSnapshot
              publicFiniteCausalBasis.naming
            observationsExact := rfl }
        requirement :=
          { witness :=
              { incorporation := publicRequirementIncorporation
                  publicInitialCertifiedState.input } }
        causal :=
          { witness :=
              { role := publicRequirementCausalRole
                  publicInitialCertifiedState.input } }
        proposalAction :=
          { witness := publicAction publicInitialCertifiedState.input }
        authorization :=
          { witness :=
              { authorization := publicReconfigurationAuthorization
                  publicInitialCertifiedState.input } }
        effect :=
          { witness := publicEffect publicInitialCertifiedState.input }
        historical :=
          { witness :=
              { historical := publicLeftHistoricalOperationalState
                currentExact := rfl } }
        futures :=
          { covered := fun requests => publicFiniteInteractionHistory requests
            realization := publicInitialCoveredFutureRealization } }
  | .reconfigured =>
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
                publicAgentActionChannel
                publicReconfigurationCertificateForState
                publicReferenceUpdatedState requests
            realization := publicCoveredFutureRealization } }

def publicAdmissionDecision (contract : PublicOperationalContract) :
    ReflectedDecision (PublicContractAdmission contract) :=
  match contract with
  | .initial => reflectedTrue .initial
  | .reconfigured => reflectedTrue .reconfigured

def publicTransitionDecision
    (request : ContractTransitionRequest publicConstitutiveMetaContract) :
    ReflectedDecision
      (OperationalContractTransition publicConstitutiveMetaContract
        request.current request.next) :=
  match request with
  | ⟨.initial, .reconfigured⟩ => reflectedTrue publicOperationalTransition
  | ⟨.initial, .initial⟩ => reflectedFalse
  | ⟨.reconfigured, .initial⟩ => reflectedFalse
  | ⟨.reconfigured, .reconfigured⟩ => reflectedFalse

/-- Public implementation of the executable meta-contract boundary.  Every
decision projects one independently recomputed fragment; no decision reads an
assembled state certificate. -/
def publicExecutableMetaContractInterface :
    ExecutableMetaContractInterface publicConstitutiveMetaContract where
  ContractCode := SerializedOperationalContractName
  encodeContract := encodePublicOperationalContract
  encodeContractInjective := encodePublicOperationalContract_injective
  ContractNameError := Unit
  decodeContractName := decodePublicOperationalContractName
  ReceivedArtifact := SerializedConstitutiveArtifact
  artifactContractCode := SerializedConstitutiveArtifact.contract
  artifactNetwork := SerializedConstitutiveArtifact.network
  artifactStableNaming := SerializedConstitutiveArtifact.stableNaming
  ArtifactError := PublicExecutableArtifactError
  DecodedArtifact := PublicExecutableDecodedArtifact
  decodedContract := PublicExecutableDecodedArtifact.contract
  decodedContractExact := by
    intro source decoded
    cases decoded <;> rfl
  decodedNeuralArtifact := PublicExecutableDecodedArtifact.artifact
  decodedNetworkExact := by
    intro source decoded
    cases decoded <;> rfl
  decodedStableNaming := PublicExecutableDecodedArtifact.stableNaming
  decodeReceivedArtifact := decodePublicExecutableArtifact
  stateOfArtifact := PublicExecutableDecodedArtifact.state
  admissionDecision := publicAdmissionDecision
  transitionDecision := publicTransitionDecision
  basisDecision := fun decoded =>
    reflectedTrue decoded.recomputedFragments.structural.basis
  systemDecision := fun decoded =>
    reflectedTrue decoded.recomputedFragments.structural.systemExact
  declaredInputDecision := fun decoded =>
    reflectedTrue decoded.recomputedFragments.structural.inputDeclared
  requirementDecision := fun decoded =>
    reflectedTrue decoded.recomputedFragments.requirement.witness
  contextDecision := fun decoded =>
    reflectedTrue decoded.recomputedFragments.causal.witness
  authorizationDecision := fun decoded =>
    reflectedTrue decoded.recomputedFragments.authorization.witness
  actionDecision := fun decoded =>
    reflectedTrue decoded.recomputedFragments.proposalAction.witness
  effectDecision := fun decoded =>
    reflectedTrue decoded.recomputedFragments.effect.witness
  historicalDecision := fun decoded =>
    reflectedTrue decoded.recomputedFragments.historical.witness
  coveredFuturesDecision := fun decoded =>
    reflectedTrue decoded.recomputedFragments.futures.covered
  futureRealizationDecision := fun decoded =>
    reflectedTrue decoded.recomputedFragments.futures.realization

def checkPublicInitial
    (source : SerializedConstitutiveArtifact) :
    Except (InitialCheckError publicExecutableMetaContractInterface)
      (InitialCheckSuccess publicExecutableMetaContractInterface source) :=
  checkInitial publicExecutableMetaContractInterface source

theorem decodeOperationalContractTransition_source_exact
    (source : SerializedOperationalContractTransition)
    (transition : OperationalContractTransition publicConstitutiveMetaContract
      .initial .reconfigured)
    (accepted : decodeOperationalContractTransition source = .ok transition) :
    source = publicSerializedOperationalTransition := by
  unfold decodeOperationalContractTransition at accepted
  split at accepted
  · exact ‹source = { source := .initial, target := .reconfigured }›
  · cases accepted

/-- The full-reference request carries the complete constitutive successor,
the proof-free named transition, and the next requirement.  It contains no
decoded artifact, fragment, witness, certificate, or verdict. -/
structure FullReferenceNeuralUpdate where
  transition : SerializedOperationalContractTransition
  targetArtifact : SerializedConstitutiveArtifact
  nextInput : PublicRequirementInput

def publicFullReferenceNeuralUpdate : FullReferenceNeuralUpdate :=
  { transition := publicSerializedOperationalTransition
    targetArtifact := publicSerializedReconfiguredConstitutiveArtifact
    nextInput := publicSubstantiveNext }

def publicExecutableStateAcceptance
    {source : SerializedConstitutiveArtifact}
    (decoded : PublicExecutableDecodedArtifact source) :
    ExecutableStateAcceptance publicExecutableMetaContractInterface decoded :=
  { basis := rfl
    system := rfl
    declaredInput := rfl
    requirement := rfl
    context := rfl
    authorization := rfl
    action := rfl
    effect := rfl
    historical := rfl
    coveredFutures := rfl
    futureRealization := rfl }

def publicInitialCheckSuccess :
    InitialCheckSuccess publicExecutableMetaContractInterface
      publicSerializedInitialConstitutiveArtifact :=
  .mk
    { contract := .initial, exact := rfl }
    .initial rfl rfl (publicExecutableStateAcceptance .initial)

def publicReconfiguredCheckSuccess :
    InitialCheckSuccess publicExecutableMetaContractInterface
      publicSerializedReconfiguredConstitutiveArtifact :=
  .mk
    { contract := .reconfigured, exact := rfl }
    .reconfigured rfl rfl (publicExecutableStateAcceptance .reconfigured)

/-- The successor checked agent consumes the complete target artifact, the
exact executed target state, and its state-indexed constitutive certificate. -/
def publicReferenceNextCheckedAgent :
    CheckedAgent publicConstitutiveMetaContract .reconfigured :=
  publicReconfiguredCheckSuccess.checkedAgent

def publicReferenceCheckedUpdate :
    CheckedUpdate publicInitialCheckedAgent .reconfigured :=
  certifyCheckedUpdate publicReferenceNextCheckedAgent
    publicOperationalTransition
    publicReferenceTransitionProduction.execution

theorem publicReferenceCheckedUpdate_execution_exact :
    publicReferenceCheckedUpdate.execution =
      publicReferenceTransitionProduction.execution := by
  rfl

/-- Assemble a successor certificate solely from the decisions rerun by the
full checker.  This definition is deliberately separate from
every certificate assembled before this verification run. -/
def publicFullyRecheckedCertificate
    (accepted : ExecutableStateAcceptance
      publicExecutableMetaContractInterface
      PublicExecutableDecodedArtifact.reconfigured) :
    StateConstitutiveCertificate PublicReconfiguredOperationalContract
      publicDecodedReconfiguredArtifact publicReferenceUpdatedState :=
  publicExecutableMetaContractInterface.certifyState accepted

theorem publicFullyRecheckedCertificate_fragments_exact
    (accepted : ExecutableStateAcceptance
      publicExecutableMetaContractInterface
      PublicExecutableDecodedArtifact.reconfigured) :
    (publicFullyRecheckedCertificate accepted).fragments =
      PublicExecutableDecodedArtifact.reconfigured.recomputedFragments := by
  rfl

/-- The successor agent returned by the full checker consumes the certificate
assembled from its newly accepted fragments. -/
def publicFullyRecheckedNextAgent
    (accepted : ExecutableStateAcceptance
      publicExecutableMetaContractInterface
      PublicExecutableDecodedArtifact.reconfigured) :
    CheckedAgent publicConstitutiveMetaContract .reconfigured :=
  certifyCheckedAgent PublicContractAdmission.reconfigured
    publicDecodedReconfiguredArtifact publicReferenceUpdatedState
    (publicFullyRecheckedCertificate accepted)

theorem publicFullyRecheckedNextAgent_exact
    (accepted : ExecutableStateAcceptance
      publicExecutableMetaContractInterface
      PublicExecutableDecodedArtifact.reconfigured) :
    publicFullyRecheckedNextAgent accepted =
      publicReferenceNextCheckedAgent := by
  rfl

def publicFullyRecheckedUpdate
    (accepted : ExecutableStateAcceptance
      publicExecutableMetaContractInterface
      PublicExecutableDecodedArtifact.reconfigured) :
    CheckedUpdate publicInitialCheckedAgent .reconfigured :=
  certifyCheckedUpdate (publicFullyRecheckedNextAgent accepted)
    publicOperationalTransition publicReferenceTransitionProduction.execution

theorem publicFullyRecheckedUpdate_exact
    (accepted : ExecutableStateAcceptance
      publicExecutableMetaContractInterface
      PublicExecutableDecodedArtifact.reconfigured) :
    publicFullyRecheckedUpdate accepted = publicReferenceCheckedUpdate := by
  rfl

/-- Full verification recomputes the complete target certificate fragment by
fragment.  It decodes the named transition and complete constitutive artifact,
runs every local reflected decision, assembles the resulting target
certificate, and only then builds the checked update from the executed
transition.  No source certificate fragment is transported into this path. -/
def checkReferenceUpdate (update : FullReferenceNeuralUpdate) :
    Except AlignmentError
      (CheckedUpdate publicInitialCheckedAgent .reconfigured) :=
  match decodeOperationalContractTransition update.transition with
  | .error _ => .error .noAdmittedTransition
  | .ok _transition =>
      match decodePublicExecutableArtifact update.targetArtifact with
      | .error (.malformed problem) =>
          .error (.malformedConstitutiveArtifact problem)
      | .error .locallyUnsupported => .error .unexpectedSuccessorArtifact
      | .ok _decoded =>
          if _targetExact : update.targetArtifact =
              publicSerializedReconfiguredConstitutiveArtifact then
            match checkInitialState publicExecutableMetaContractInterface
                PublicExecutableDecodedArtifact.reconfigured with
            | .error problem => .error (.targetStateRejected problem)
            | .ok accepted =>
                match publicRequirementInputEquality update.nextInput
                    publicSubstantiveNext with
                | .isFalse _ => .error .successorMismatch
                | .isTrue _nextExact =>
                    .ok (publicFullyRecheckedUpdate accepted)
          else
            .error .unexpectedSuccessorArtifact

theorem checkInitial_accepts_reference :
    checkPublicInitial publicSerializedInitialConstitutiveArtifact =
      .ok publicInitialCheckSuccess := by
  rfl

def publicMalformedInitialConstitutiveArtifact :
    SerializedConstitutiveArtifact :=
  { publicSerializedInitialConstitutiveArtifact with
    network := mismatchedInputCountNetwork }

theorem checkInitial_rejects_malformed :
    checkPublicInitial publicMalformedInitialConstitutiveArtifact =
      .error (.artifact (.malformed (.network .inputCountMismatch))) := by
  rfl

theorem checkInitial_accepts_reconfigured_reference :
    checkPublicInitial publicSerializedReconfiguredConstitutiveArtifact =
      .ok publicReconfiguredCheckSuccess := by
  rfl

theorem publicInitialCheckSuccess_checkedAgent_exact :
    publicInitialCheckSuccess.checkedAgent = publicInitialCheckedAgent := by
  rfl

theorem publicReconfiguredCheckSuccess_checkedAgent_exact :
    publicReconfiguredCheckSuccess.checkedAgent =
      publicReferenceNextCheckedAgent := by
  rfl

theorem checkReferenceUpdate_accepts_reference :
    checkReferenceUpdate publicFullReferenceNeuralUpdate =
      .ok publicReferenceCheckedUpdate := by
  rfl

def publicWrongSuccessorReferenceUpdate : FullReferenceNeuralUpdate :=
  { transition := publicSerializedOperationalTransition
    targetArtifact := publicSerializedReconfiguredConstitutiveArtifact
    nextInput := publicSubstantiveContextualNext }

theorem checkReferenceUpdate_rejects_wrong_successor :
    checkReferenceUpdate publicWrongSuccessorReferenceUpdate =
      .error .successorMismatch := by
  rfl

/-- Any successful initial check returns the agent indexed by the exact
decoded artifact and by the state produced from that artifact. -/
theorem checkInitial_sound
    {constitution : ConstitutiveMetaContract}
    (interface : ExecutableMetaContractInterface constitution)
    (source : interface.ReceivedArtifact)
    (checked : InitialCheckSuccess interface source)
    (_accepted : checkInitial interface source = .ok checked) :
    checked.checkedAgent.artifact =
        interface.decodedNeuralArtifact checked.decodedArtifact ∧
      checked.checkedAgent.state =
        interface.stateOfArtifact checked.decodedArtifact := by
  exact ⟨rfl, rfl⟩

/-- These are exactly the finite decisions announced by the executable
interface.  No unbounded semantic predicate is added to relative
completeness. -/
structure InitialCheckLocalConditions
    {constitution : ConstitutiveMetaContract}
    (interface : ExecutableMetaContractInterface constitution)
    (source : interface.ReceivedArtifact) : Type 6 where
  contractName : DecodedContractName constitution interface.encodeContract
    (interface.artifactContractCode source)
  decodedArtifact : interface.DecodedArtifact source
  contractNameDecoded :
    interface.decodeContractName (interface.artifactContractCode source) =
      .ok contractName
  artifactDecoded :
    interface.decodeReceivedArtifact source = .ok decodedArtifact
  admissionAccepted :
    (interface.admissionDecision
      (interface.decodedContract decodedArtifact)).result = true
  stateAccepted : ExecutableStateAcceptance interface decodedArtifact

def InitialCheckAccepted
    {constitution : ConstitutiveMetaContract}
    (interface : ExecutableMetaContractInterface constitution)
    (source : interface.ReceivedArtifact) : Prop :=
  Exists fun checked => checkInitial interface source = .ok checked

def InitialStateAccepted
    {constitution : ConstitutiveMetaContract}
    (interface : ExecutableMetaContractInterface constitution)
    {source : interface.ReceivedArtifact}
    (decoded : interface.DecodedArtifact source) : Prop :=
  Exists fun accepted => checkInitialState interface decoded = .ok accepted

def checkInitialStateCompleteData
    {constitution : ConstitutiveMetaContract}
    (interface : ExecutableMetaContractInterface constitution)
    {source : interface.ReceivedArtifact}
    {decoded : interface.DecodedArtifact source}
    (accepted : ExecutableStateAcceptance interface decoded) :
    { result // checkInitialState interface decoded = .ok result } := by
  unfold checkInitialState
  rw [dif_pos accepted.basis]
  rw [dif_pos accepted.system]
  rw [dif_pos accepted.declaredInput]
  rw [dif_pos accepted.requirement]
  rw [dif_pos accepted.context]
  rw [dif_pos accepted.authorization]
  rw [dif_pos accepted.action]
  rw [dif_pos accepted.effect]
  rw [dif_pos accepted.historical]
  rw [dif_pos accepted.coveredFutures]
  rw [dif_pos accepted.futureRealization]
  exact
    ⟨{ basis := accepted.basis
       system := accepted.system
       declaredInput := accepted.declaredInput
       requirement := accepted.requirement
       context := accepted.context
       authorization := accepted.authorization
       action := accepted.action
       effect := accepted.effect
       historical := accepted.historical
       coveredFutures := accepted.coveredFutures
       futureRealization := accepted.futureRealization }, rfl⟩

theorem checkInitialState_complete_for_local_decisions
    {constitution : ConstitutiveMetaContract}
    (interface : ExecutableMetaContractInterface constitution)
    {source : interface.ReceivedArtifact}
    {decoded : interface.DecodedArtifact source}
    (accepted : ExecutableStateAcceptance interface decoded) :
    InitialStateAccepted interface decoded :=
  let complete := checkInitialStateCompleteData interface accepted
  ⟨complete.1, complete.2⟩

/-- Constructive completeness data for the exact finite local conditions. -/
def checkInitialCompleteData
    {constitution : ConstitutiveMetaContract}
    (interface : ExecutableMetaContractInterface constitution)
    (source : interface.ReceivedArtifact)
    (conditions : InitialCheckLocalConditions interface source) :
    { checked // checkInitial interface source = .ok checked } := by
  unfold checkInitial
  rw [conditions.contractNameDecoded, conditions.artifactDecoded]
  simp only
  rw [dif_pos conditions.admissionAccepted]
  let stateComplete := checkInitialStateCompleteData interface
    conditions.stateAccepted
  rw [stateComplete.property]
  exact ⟨.mk conditions.contractName conditions.decodedArtifact
    (interface.encodeContractInjective
      (conditions.contractName.exact.trans
        (interface.decodedContractExact conditions.decodedArtifact).symm))
    conditions.admissionAccepted stateComplete.val, rfl⟩

/-- Relative completeness mentions only successful decoding, admission, and
the finite reflected decisions declared by the interface. -/
theorem checkInitial_complete_for_local_conditions
    {constitution : ConstitutiveMetaContract}
    (interface : ExecutableMetaContractInterface constitution)
    (source : interface.ReceivedArtifact)
    (conditions : InitialCheckLocalConditions interface source) :
    InitialCheckAccepted interface source :=
  let complete := checkInitialCompleteData interface source conditions
  ⟨complete.1, complete.2⟩

/-- Any successful full-reference update check returns the precise update
whose transition and successor are consumed by execution. -/
theorem checkReferenceUpdate_sound
    (update : FullReferenceNeuralUpdate)
    (checked : CheckedUpdate publicInitialCheckedAgent .reconfigured)
    (accepted : checkReferenceUpdate update = .ok checked) :
    checked = publicReferenceCheckedUpdate := by
  unfold checkReferenceUpdate at accepted
  split at accepted
  · cases accepted
  · split at accepted
    · cases accepted
    · cases accepted
    · split at accepted
      · simp only [show checkInitialState publicExecutableMetaContractInterface
            PublicExecutableDecodedArtifact.reconfigured =
            .ok (publicExecutableStateAcceptance .reconfigured) from rfl]
          at accepted
        split at accepted
        · cases accepted
        · have same := Except.ok.inj accepted
          rw [← same]
          exact publicFullyRecheckedUpdate_exact _
      · cases accepted

def ReferenceUpdateAccepted (update : FullReferenceNeuralUpdate) : Prop :=
  Exists fun checked => checkReferenceUpdate update = .ok checked

def ReferenceUpdateLocalConditions
    (update : FullReferenceNeuralUpdate) : Prop :=
  update.transition = publicSerializedOperationalTransition ∧
    update.targetArtifact = publicSerializedReconfiguredConstitutiveArtifact ∧
      update.nextInput = publicSubstantiveNext

/-- Relative completeness is stated only for the three decidable local
conditions actually implemented by this reference checker. -/
theorem checkReferenceUpdate_complete_for_local_conditions
    (update : FullReferenceNeuralUpdate) :
    ReferenceUpdateAccepted update ↔
      ReferenceUpdateLocalConditions update := by
  constructor
  · intro accepted
    rcases accepted with ⟨checked, exact⟩
    unfold checkReferenceUpdate at exact
    split at exact
    · cases exact
    · split at exact
      · cases exact
      · cases exact
      · split at exact
        · simp only [show checkInitialState publicExecutableMetaContractInterface
              PublicExecutableDecodedArtifact.reconfigured =
              .ok (publicExecutableStateAcceptance .reconfigured) from rfl]
            at exact
          split at exact
          · cases exact
          · exact
              ⟨decodeOperationalContractTransition_source_exact
                  update.transition _ ‹decodeOperationalContractTransition
                    update.transition = .ok _›,
                ‹update.targetArtifact =
                  publicSerializedReconfiguredConstitutiveArtifact›,
                ‹update.nextInput = publicSubstantiveNext›⟩
        · cases exact
  · intro conditions
    rcases conditions with ⟨transitionExact, artifactExact, inputExact⟩
    cases update
    cases transitionExact
    cases artifactExact
    cases inputExact
    exact ⟨publicReferenceCheckedUpdate,
      checkReferenceUpdate_accepts_reference⟩

end ConstitutiveSearch.NeuralAgent
/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.NeuralAgent.InitialStateCheckError
#print axioms ConstitutiveSearch.NeuralAgent.InitialCheckError
#print axioms ConstitutiveSearch.NeuralAgent.checkInitialState
#print axioms ConstitutiveSearch.NeuralAgent.InitialCheckSuccess
#print axioms ConstitutiveSearch.NeuralAgent.InitialCheckSuccess.checkedAgent
#print axioms ConstitutiveSearch.NeuralAgent.checkInitial
#print axioms ConstitutiveSearch.NeuralAgent.AlignmentError
#print axioms ConstitutiveSearch.NeuralAgent.PublicExecutableDecodedArtifact
#print axioms ConstitutiveSearch.NeuralAgent.decodePublicExecutableArtifact
#print axioms ConstitutiveSearch.NeuralAgent.publicExecutableMetaContractInterface
#print axioms ConstitutiveSearch.NeuralAgent.checkPublicInitial
#print axioms ConstitutiveSearch.NeuralAgent.decodeOperationalContractTransition_source_exact
#print axioms ConstitutiveSearch.NeuralAgent.FullReferenceNeuralUpdate
#print axioms ConstitutiveSearch.NeuralAgent.publicReferenceNextCheckedAgent
#print axioms ConstitutiveSearch.NeuralAgent.publicReferenceCheckedUpdate
#print axioms ConstitutiveSearch.NeuralAgent.publicReferenceCheckedUpdate_execution_exact
#print axioms ConstitutiveSearch.NeuralAgent.publicFullyRecheckedCertificate
#print axioms ConstitutiveSearch.NeuralAgent.publicFullyRecheckedCertificate_fragments_exact
#print axioms ConstitutiveSearch.NeuralAgent.publicFullyRecheckedNextAgent
#print axioms ConstitutiveSearch.NeuralAgent.publicFullyRecheckedNextAgent_exact
#print axioms ConstitutiveSearch.NeuralAgent.publicFullyRecheckedUpdate
#print axioms ConstitutiveSearch.NeuralAgent.publicFullyRecheckedUpdate_exact
#print axioms ConstitutiveSearch.NeuralAgent.checkReferenceUpdate
#print axioms ConstitutiveSearch.NeuralAgent.publicInitialCheckSuccess
#print axioms ConstitutiveSearch.NeuralAgent.publicReconfiguredCheckSuccess
#print axioms ConstitutiveSearch.NeuralAgent.publicInitialCheckSuccess_checkedAgent_exact
#print axioms ConstitutiveSearch.NeuralAgent.publicReconfiguredCheckSuccess_checkedAgent_exact
#print axioms ConstitutiveSearch.NeuralAgent.checkInitial_sound
#print axioms ConstitutiveSearch.NeuralAgent.InitialCheckLocalConditions
#print axioms ConstitutiveSearch.NeuralAgent.InitialStateAccepted
#print axioms ConstitutiveSearch.NeuralAgent.checkInitialStateCompleteData
#print axioms ConstitutiveSearch.NeuralAgent.checkInitialState_complete_for_local_decisions
#print axioms ConstitutiveSearch.NeuralAgent.checkInitialCompleteData
#print axioms ConstitutiveSearch.NeuralAgent.checkInitial_complete_for_local_conditions
#print axioms ConstitutiveSearch.NeuralAgent.checkReferenceUpdate_sound
#print axioms ConstitutiveSearch.NeuralAgent.ReferenceUpdateAccepted
#print axioms ConstitutiveSearch.NeuralAgent.ReferenceUpdateLocalConditions
#print axioms ConstitutiveSearch.NeuralAgent.checkReferenceUpdate_complete_for_local_conditions
/- AXIOM_AUDIT_END -/
