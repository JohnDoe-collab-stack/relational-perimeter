import RelationalPerimeter.Agents.Neural.CertifiedRuntimeAccessibility
import RelationalPerimeter.Agents.Neural.FiniteCounterfactualDivergence

/-!
# Learned artifact adapter for the generic checker and runtime

The independently learned source and its two candidate successors enter the
same constitutive checking boundary as every other certified neural state.
The adapter does not call the earlier specialized learned-update checker.
Instead it supplies a local operational contract, reflected initial-state
decisions, a proof-free candidate update language, and an incremental engine
whose only installed successor is assembled by the generic checker.

The admitted intent remains distinct from certification.  Authorization is a
separate state-indexed obligation calculated from the serialized target, and
the counterfactual interpreter is the future contract actually carried by the
certified runtime state.
-/
set_option genInjectivity false
set_option maxHeartbeats 4000000
namespace ConstitutiveSearch.NeuralAgent
open NativeMechanism
open ContinuationSignatures

/-! ## Learned requirement interface and operational future -/

abbrev LearnedContext := Bool × Bool

def independentLearnedRequirementFamily :
    RequirementFamily Bool LearnedContext Bool where
  received
    | false => singletonRequirement 0
    | true => singletonRequirement 1
  requiredProposal := fun requirement context =>
    if context.2 then true else decide (requirement != context.1)

abbrev IndependentLearnedRequirementInput :=
  RequirementInput independentLearnedRequirementFamily

def IndependentLearnedInput.toRequirementInput
    (input : IndependentLearnedInput) : IndependentLearnedRequirementInput :=
  { requirement := input.requirement
    context := (input.context, input.authorization) }

def IndependentLearnedRequirementInput.toLearnedInput
    (input : IndependentLearnedRequirementInput) : IndependentLearnedInput :=
  { requirement := input.requirement
    context := input.context.1
    authorization := input.context.2 }

def encodeIndependentLearnedRequirement
    (input : IndependentLearnedRequirementInput) : SizedActivations 3 :=
  input.toLearnedInput.activations

def decodeIndependentLearnedProposal : List Activation -> Bool
  | [] => false
  | value :: _ => decide (value != 0)

def independentLearnedCertifiedInput : IndependentLearnedRequirementInput :=
  IndependentLearnedCurrentCase.requirementOnly.input.toRequirementInput

def independentLearnedDeclaredInputs :
    List IndependentLearnedRequirementInput :=
  [independentLearnedCertifiedInput]

structure IndependentLearnedFutureSource : Type 3 where
  network : SerializedNetwork

structure IndependentLearnedFutureInput : Type 3 where
  input : IndependentLearnedInput

structure IndependentLearnedFutureEvent : Type 3 where
  outputs : List Activation

structure IndependentLearnedFutureObservation : Type 3 where
  network : SerializedNetwork

inductive IndependentLearnedFutureAdmission : Type 3 where
  | admitted

def independentLearnedFutureContract :
    FutureContract.{3, 3} IndependentLearnedFutureSource
      IndependentLearnedFutureInput IndependentLearnedFutureEvent
      IndependentLearnedFutureObservation where
  next := fun source _ => source
  event := fun source input =>
    { outputs := executeSerializedArtifact source.network input.input }
  read := fun source => { network := source.network }
  Allow := fun _ _ => IndependentLearnedFutureAdmission
  decision := fun _ _ => .inl .admitted

def independentLearnedFutureSimulation : FutureContractSimulationData
    independentLearnedFutureContract independentLearnedFutureContract
      (fun source => source) where
  forward := fun _ _ witness => witness
  backward := fun _ _ witness => witness
  backwardForward := by intro source input witness; rfl
  forwardBackward := by intro source input witness; rfl
  nextExact := by intro source input; rfl
  eventExact := by intro source input; rfl
  readExact := by intro source; rfl

/-! ## Separate learned obligations -/

structure LearnedRequirementEncodingWitness
    (state : ReconfiguredExecutionState independentLearnedRequirementFamily) :
    Type 3 where
  inputExact : state.input = independentLearnedCertifiedInput

structure LearnedExecutedCausalWitness
    (state : ReconfiguredExecutionState independentLearnedRequirementFamily) :
    Type 3 where
  authorizationPort : Fin state.system.inputCount
  role : CausalRole state.system state.input
    (.receivedInput authorizationPort)

structure LearnedAuthorizationWitness (source : SerializedNetwork) : Type 3 where
  consumed : primaryAuthorizationConstitutivelyConsumed source = true

structure LearnedEffectWitness (proposal : Bool) : Type 3 where
  proposalExact : proposal = true

structure LearnedCoveredFutureStatement : Type 3 where
  source : SerializedNetwork
  requests : List IndependentLearnedInput

structure LearnedCoveredFutureWitness
    (statement : LearnedCoveredFutureStatement) : Type 3 where
  outcome : Outcome IndependentLearnedFutureEvent
    IndependentLearnedFutureObservation
  outcomeExact : outcome = independentLearnedFutureContract.outcome
    { network := statement.source }
    (statement.requests.map fun input => { input := input })

structure LearnedHistoricalWitness
    (expected actual : SerializedNetwork) : Type 3 where
  exact : actual = expected

def learnedRequirementEncodingObligations : ContractObligationFamily where
  Statement := ULift.{3}
    (ReconfiguredExecutionState independentLearnedRequirementFamily)
  Witness := fun state => LearnedRequirementEncodingWitness state.down

def learnedCausalObligations : ContractObligationFamily where
  Statement := ULift.{3}
    (ReconfiguredExecutionState independentLearnedRequirementFamily)
  Witness := fun state => LearnedExecutedCausalWitness state.down

def learnedIntentObligations : ContractObligationFamily where
  Statement := ULift.{3} IndependentLearnedUpdateIntent
  Witness := fun intent =>
    ULift.{3} (AdmittedIndependentLearnedIntent intent.down)

def learnedAuthorizationObligations : ContractObligationFamily where
  Statement := ULift.{3} SerializedNetwork
  Witness := fun source => LearnedAuthorizationWitness source.down

def learnedEffectObligations : ContractObligationFamily where
  Statement := ULift.{3} Bool
  Witness := fun proposal => LearnedEffectWitness proposal.down

def learnedFutureObligations : ContractObligationFamily where
  Statement := LearnedCoveredFutureStatement
  Witness := LearnedCoveredFutureWitness

def learnedHistoricalObligations
    (expected : SerializedNetwork) : ContractObligationFamily where
  Statement := ULift.{3} SerializedNetwork
  Witness := fun actual => LearnedHistoricalWitness expected actual.down

inductive LearnedOperationalContract where
  | initial
  | aligned
  deriving DecidableEq

def learnedExpectedNetwork : LearnedOperationalContract -> SerializedNetwork
  | .initial => independentLearnedInitialNetwork
  | .aligned => independentLearnedFirstSuccessorNetwork

def learnedOperationalContract
    (name : LearnedOperationalContract) : ConstitutiveContract :=
  { RequirementCase := Bool
    Context := LearnedContext
    Proposal := Bool
    family := independentLearnedRequirementFamily
    inputCount := 3
    encode := encodeIndependentLearnedRequirement
    decode := decodeIndependentLearnedProposal
    actionChannel := publicAgentActionChannel
    declaredCurrentInputs := independentLearnedDeclaredInputs
    declaredReplacementValues := [0]
    FutureSource := IndependentLearnedFutureSource
    FutureInput := IndependentLearnedFutureInput
    FutureEvent := IndependentLearnedFutureEvent
    FutureObservation := IndependentLearnedFutureObservation
    futureContract := independentLearnedFutureContract
    futureSourceOfState := fun state =>
      { network := serializeNativeSystem state.system }
    requirementEncoding := learnedRequirementEncodingObligations
    requirementEncodingAt := fun state => ULift.up state
    causalCondition := learnedCausalObligations
    causalConditionAt := fun state => ULift.up state
    proposalActionPreservation := learnedIntentObligations
    proposalActionPreservationAt := fun _ =>
      ULift.up IndependentLearnedUpdateIntent.preserveAuthorizedBehavior
    authorizationAdmission := learnedAuthorizationObligations
    authorizationAdmissionAt := fun state =>
      ULift.up (serializeNativeSystem state.system)
    effectSatisfaction := learnedEffectObligations
    effectSatisfactionAt := fun state =>
      ULift.up (state.system.proposal state.input)
    coveredFuture := learnedFutureObligations
    coveredFutureAt := fun state requests =>
      { source := serializeNativeSystem state.system
        requests := requests.map
          IndependentLearnedRequirementInput.toLearnedInput }
    historicalPolicy := learnedHistoricalObligations
      (learnedExpectedNetwork name)
    historicalPolicyAt := fun state =>
      ULift.up (serializeNativeSystem state.system) }

def independentLearnedCoveredFutureRealization
    (name : LearnedOperationalContract) :
    CoveredFutureRealization (learnedOperationalContract name) :=
  { ReducedMemory := IndependentLearnedFutureSource
    reducedContract := independentLearnedFutureContract
    project := fun source => source
    simulation := independentLearnedFutureSimulation }

abbrev LearnedInitialOperationalContract : ConstitutiveContract :=
  learnedOperationalContract .initial

abbrev LearnedAlignedOperationalContract : ConstitutiveContract :=
  learnedOperationalContract .aligned

/-! ## Constructively decoded learned artifacts -/

def learnedDecodedInitialArtifact :
    DecodedNeuralArtifact LearnedInitialOperationalContract :=
  match exact : decodeArtifact LearnedInitialOperationalContract
      independentLearnedInitialNetwork with
  | .ok artifact => artifact
  | .error _ => False.elim (by cases exact)

def learnedDecodedAlignedArtifact :
    DecodedNeuralArtifact LearnedAlignedOperationalContract :=
  match exact : decodeArtifact LearnedAlignedOperationalContract
      independentLearnedFirstSuccessorNetwork with
  | .ok artifact => artifact
  | .error _ => False.elim (by cases exact)

theorem learnedInitialArtifact_decodes :
    decodeArtifact LearnedInitialOperationalContract
        independentLearnedInitialNetwork =
      .ok learnedDecodedInitialArtifact := by
  rfl

theorem learnedAlignedArtifact_decodes :
    decodeArtifact LearnedAlignedOperationalContract
        independentLearnedFirstSuccessorNetwork =
      .ok learnedDecodedAlignedArtifact := by
  rfl

def learnedInitialState :
    ReconfiguredExecutionState independentLearnedRequirementFamily :=
  { system := learnedDecodedInitialArtifact.system
    input := independentLearnedCertifiedInput
    memory := publicActionMemory }

def learnedAlignedState :
    ReconfiguredExecutionState independentLearnedRequirementFamily :=
  { system := learnedDecodedAlignedArtifact.system
    input := independentLearnedCertifiedInput
    memory := publicActionMemory }

/-! ## Executed causal coverage of the exact learned states -/

def learnedInitialAuthorizationPort :
    Fin learnedDecodedInitialArtifact.system.inputCount := ⟨2, by decide⟩

def learnedInitialAuthorizationNeuron :
    Fin learnedDecodedInitialArtifact.system.producedCount := ⟨3, by decide⟩

def learnedInitialPrimaryNeuron :
    Fin learnedDecodedInitialArtifact.system.producedCount := ⟨4, by decide⟩

def learnedInitialPrimaryOutputPort :
    Fin learnedDecodedInitialArtifact.system.outputs.sources.length :=
  ⟨0, by decide⟩

def learnedInitialAuthorizationIntervention :
    Intervention
      (learnedDecodedInitialArtifact.system.run
        independentLearnedCertifiedInput) where
  focus := .input learnedInitialAuthorizationPort
  replacement := 0
  changesValue := by decide

def learnedInitialAuthorizationEdge :
    EffectiveReadsFrom
      (learnedDecodedInitialArtifact.system.run
        independentLearnedCertifiedInput)
      (.receivedInput learnedInitialAuthorizationPort)
      (.neuronOutput learnedInitialAuthorizationNeuron) :=
  .executedEdge learnedInitialAuthorizationNeuron
    { source := .receivedInput learnedInitialAuthorizationPort, weight := 1 }
    (by
      change
        ({ source := .receivedInput learnedInitialAuthorizationPort,
            weight := 1 } : WeightedInput 3 3) ∈
          [{ source := .receivedInput learnedInitialAuthorizationPort,
              weight := 1 }]
      exact List.Mem.head _)
    (by decide)

def learnedInitialPrimaryEdge :
    EffectiveReadsFrom
      (learnedDecodedInitialArtifact.system.run
        independentLearnedCertifiedInput)
      (.neuronOutput learnedInitialAuthorizationNeuron)
      (.neuronOutput learnedInitialPrimaryNeuron) :=
  .executedEdge learnedInitialPrimaryNeuron
    { source := .priorNeuron ⟨3, by decide⟩, weight := 1 }
    (by
      change
        ({ source := .priorNeuron ⟨3, by decide⟩,
            weight := 1 } : WeightedInput 3 4) ∈
          [{ source := .priorNeuron ⟨2, by decide⟩, weight := 1 },
           { source := .priorNeuron ⟨3, by decide⟩, weight := 1 }]
      exact List.Mem.tail _ (List.Mem.head _))
    (by decide)

def learnedInitialAuthorizationPropagation :
    NontrivialExecutedChangePath learnedInitialAuthorizationIntervention
      (.neuronOutput learnedInitialPrimaryNeuron) :=
  .step
    (.step .origin learnedInitialAuthorizationEdge
      { different := by decide })
    learnedInitialPrimaryEdge { different := by decide }

def learnedInitialAuthorizationRole :
    CausalRole learnedDecodedInitialArtifact.system
      independentLearnedCertifiedInput
      (.receivedInput learnedInitialAuthorizationPort) where
  intervention := learnedInitialAuthorizationIntervention
  focusExact := rfl
  output := learnedInitialPrimaryOutputPort
  propagation := learnedInitialAuthorizationPropagation
  targetChange := { different := by decide }
  proposalChange :=
    { different := by
        change false ≠ true
        decide }

def learnedAlignedAuthorizationPort :
    Fin learnedDecodedAlignedArtifact.system.inputCount := ⟨2, by decide⟩

def learnedAlignedAuthorizationNeuron :
    Fin learnedDecodedAlignedArtifact.system.producedCount := ⟨3, by decide⟩

def learnedAlignedIntermediateNeuron :
    Fin learnedDecodedAlignedArtifact.system.producedCount := ⟨4, by decide⟩

def learnedAlignedPrimaryNeuron :
    Fin learnedDecodedAlignedArtifact.system.producedCount := ⟨6, by decide⟩

def learnedAlignedPrimaryOutputPort :
    Fin learnedDecodedAlignedArtifact.system.outputs.sources.length :=
  ⟨0, by decide⟩

def learnedAlignedAuthorizationIntervention :
    Intervention
      (learnedDecodedAlignedArtifact.system.run
        independentLearnedCertifiedInput) where
  focus := .input learnedAlignedAuthorizationPort
  replacement := 0
  changesValue := by decide

def learnedAlignedAuthorizationEdge :
    EffectiveReadsFrom
      (learnedDecodedAlignedArtifact.system.run
        independentLearnedCertifiedInput)
      (.receivedInput learnedAlignedAuthorizationPort)
      (.neuronOutput learnedAlignedAuthorizationNeuron) :=
  .executedEdge learnedAlignedAuthorizationNeuron
    { source := .receivedInput learnedAlignedAuthorizationPort, weight := 1 }
    (by
      change
        ({ source := .receivedInput learnedAlignedAuthorizationPort,
            weight := 1 } : WeightedInput 3 3) ∈
          [{ source := .receivedInput learnedAlignedAuthorizationPort,
              weight := 1 }]
      exact List.Mem.head _)
    (by decide)

def learnedAlignedIntermediateEdge :
    EffectiveReadsFrom
      (learnedDecodedAlignedArtifact.system.run
        independentLearnedCertifiedInput)
      (.neuronOutput learnedAlignedAuthorizationNeuron)
      (.neuronOutput learnedAlignedIntermediateNeuron) :=
  .executedEdge learnedAlignedIntermediateNeuron
    { source := .priorNeuron ⟨3, by decide⟩, weight := 1 }
    (by
      change
        ({ source := .priorNeuron ⟨3, by decide⟩,
            weight := 1 } : WeightedInput 3 4) ∈
          [{ source := .priorNeuron ⟨2, by decide⟩, weight := 1 },
           { source := .priorNeuron ⟨3, by decide⟩, weight := 1 }]
      exact List.Mem.tail _ (List.Mem.head _))
    (by decide)

def learnedAlignedPrimaryEdge :
    EffectiveReadsFrom
      (learnedDecodedAlignedArtifact.system.run
        independentLearnedCertifiedInput)
      (.neuronOutput learnedAlignedIntermediateNeuron)
      (.neuronOutput learnedAlignedPrimaryNeuron) :=
  .executedEdge learnedAlignedPrimaryNeuron
    { source := .priorNeuron ⟨4, by decide⟩, weight := 1 }
    (by
      change
        ({ source := .priorNeuron ⟨4, by decide⟩,
            weight := 1 } : WeightedInput 3 6) ∈
          [{ source := .priorNeuron ⟨4, by decide⟩, weight := 1 },
           { source := .priorNeuron ⟨3, by decide⟩, weight := 1 }]
      exact List.Mem.head _)
    (by decide)

def learnedAlignedAuthorizationPropagation :
    NontrivialExecutedChangePath learnedAlignedAuthorizationIntervention
      (.neuronOutput learnedAlignedPrimaryNeuron) :=
  .step
    (.step
      (.step .origin learnedAlignedAuthorizationEdge
        { different := by decide })
      learnedAlignedIntermediateEdge { different := by decide })
    learnedAlignedPrimaryEdge { different := by decide }

def learnedAlignedAuthorizationRole :
    CausalRole learnedDecodedAlignedArtifact.system
      independentLearnedCertifiedInput
      (.receivedInput learnedAlignedAuthorizationPort) where
  intervention := learnedAlignedAuthorizationIntervention
  focusExact := rfl
  output := learnedAlignedPrimaryOutputPort
  propagation := learnedAlignedAuthorizationPropagation
  targetChange := { different := by decide }
  proposalChange :=
    { different := by
        change false ≠ true
        decide }

/-! ## Stable names, finite causal bases, and state fragments -/

def learnedInitialSerializedNaming : SerializedStableArtifactNaming :=
  { inputKeys := [0, 1, 2]
    neuronKeys := [10, 11, 12, 13, 14, 15]
    outputKeys := [20, 21, 22] }

def learnedAlignedSerializedNaming : SerializedStableArtifactNaming :=
  { inputKeys := [100, 101, 102]
    neuronKeys := [110, 111, 112, 113, 114, 115, 116]
    outputKeys := [120, 121, 122] }

def learnedDecodedInitialStableNaming :
    DecodedStableArtifactNaming learnedDecodedInitialArtifact
      learnedInitialSerializedNaming :=
  match exact : decodeStableArtifactNaming learnedDecodedInitialArtifact
      learnedInitialSerializedNaming with
  | .ok naming => naming
  | .error _ => False.elim (by cases exact)

def learnedDecodedAlignedStableNaming :
    DecodedStableArtifactNaming learnedDecodedAlignedArtifact
      learnedAlignedSerializedNaming :=
  match exact : decodeStableArtifactNaming learnedDecodedAlignedArtifact
      learnedAlignedSerializedNaming with
  | .ok naming => naming
  | .error _ => False.elim (by cases exact)

def learnedInitialStableNaming :
    StableArtifactNaming learnedDecodedInitialArtifact :=
  learnedDecodedInitialStableNaming.naming

def learnedAlignedStableNaming :
    StableArtifactNaming learnedDecodedAlignedArtifact :=
  learnedDecodedAlignedStableNaming.naming

def independentLearnedRequirementInputEquality
    (left right : IndependentLearnedRequirementInput) :
    Decidable (left = right) := by
  cases left with
  | mk leftRequirement leftContext =>
      cases leftContext with
      | mk leftContext leftAuthorization =>
          cases right with
          | mk rightRequirement rightContext =>
              cases rightContext with
              | mk rightContext rightAuthorization =>
                  cases leftRequirement <;> cases rightRequirement <;>
                    cases leftContext <;> cases rightContext <;>
                      cases leftAuthorization <;> cases rightAuthorization <;>
                        first
                        | exact .isTrue rfl
                        | exact .isFalse (fun same => nomatch same)

def learnedActivationEquality
    (left right : Activation) : Decidable (left = right) :=
  Int.decEq left right

def learnedInitialCausalReplacements
    (_node : StableNodeId learnedInitialStableNaming) : List Activation :=
  [0]

def learnedAlignedCausalReplacements
    (_node : StableNodeId learnedAlignedStableNaming) : List Activation :=
  [0]

def learnedInitialCausalCoverage : CoversDeclaredCausalCondition
    learnedDecodedInitialArtifact learnedInitialStableNaming
      learnedInitialCausalReplacements := by
  intro input declared
  cases declared with
  | head =>
      exact
        { node := .receivedInput learnedInitialAuthorizationPort
          role := learnedInitialAuthorizationRole
          replacementListed := .head
          replacementDeclared := .head }
  | tail impossible => nomatch impossible

def learnedAlignedCausalCoverage : CoversDeclaredCausalCondition
    learnedDecodedAlignedArtifact learnedAlignedStableNaming
      learnedAlignedCausalReplacements := by
  intro input declared
  cases declared with
  | head =>
      exact
        { node := .receivedInput learnedAlignedAuthorizationPort
          role := learnedAlignedAuthorizationRole
          replacementListed := .head
          replacementDeclared := .head }
  | tail impossible => nomatch impossible

def learnedInitialFiniteCausalBasis : FiniteCausalBasis
    LearnedInitialOperationalContract learnedDecodedInitialArtifact where
  currentInputs := independentLearnedDeclaredInputs
  currentInputsComplete := fun _ witness => witness
  inputEquality := independentLearnedRequirementInputEquality
  naming := learnedInitialStableNaming
  replacements := learnedInitialCausalReplacements
  replacementCoverage := learnedInitialCausalCoverage
  replacementEquality := learnedActivationEquality

def learnedAlignedFiniteCausalBasis : FiniteCausalBasis
    LearnedAlignedOperationalContract learnedDecodedAlignedArtifact where
  currentInputs := independentLearnedDeclaredInputs
  currentInputsComplete := fun _ witness => witness
  inputEquality := independentLearnedRequirementInputEquality
  naming := learnedAlignedStableNaming
  replacements := learnedAlignedCausalReplacements
  replacementCoverage := learnedAlignedCausalCoverage
  replacementEquality := learnedActivationEquality

def learnedInitialStateFragments : StateCertificateFragments
    LearnedInitialOperationalContract learnedDecodedInitialArtifact
      learnedInitialState :=
  { structural :=
      { basis := learnedInitialFiniteCausalBasis
        systemExact := rfl
        inputDeclared := .head
        observations := stableStructuralObservationSnapshot
          learnedInitialFiniteCausalBasis.naming
        observationsExact := rfl }
    requirement := { witness := { inputExact := rfl } }
    causal :=
      { witness :=
          { authorizationPort := learnedInitialAuthorizationPort
            role := learnedInitialAuthorizationRole } }
    proposalAction :=
      { witness := ULift.up
          AdmittedIndependentLearnedIntent.preserveAuthorizedBehavior }
    authorization :=
      { witness := { consumed := by rfl } }
    effect := { witness := { proposalExact := by rfl } }
    historical := { witness := { exact := by rfl } }
    futures :=
      { covered := fun requests =>
          { outcome := independentLearnedFutureContract.outcome
              { network :=
                  (LearnedInitialOperationalContract.coveredFutureAt
                    learnedInitialState requests).source }
              ((LearnedInitialOperationalContract.coveredFutureAt
                learnedInitialState requests).requests.map fun input =>
                  { input := input })
            outcomeExact := rfl }
        realization := independentLearnedCoveredFutureRealization .initial } }

def learnedAlignedStateFragments : StateCertificateFragments
    LearnedAlignedOperationalContract learnedDecodedAlignedArtifact
      learnedAlignedState :=
  { structural :=
      { basis := learnedAlignedFiniteCausalBasis
        systemExact := rfl
        inputDeclared := .head
        observations := stableStructuralObservationSnapshot
          learnedAlignedFiniteCausalBasis.naming
        observationsExact := rfl }
    requirement := { witness := { inputExact := rfl } }
    causal :=
      { witness :=
          { authorizationPort := learnedAlignedAuthorizationPort
            role := learnedAlignedAuthorizationRole } }
    proposalAction :=
      { witness := ULift.up
          AdmittedIndependentLearnedIntent.preserveAuthorizedBehavior }
    authorization :=
      { witness := { consumed := alignedUpdate_consumes_authorization } }
    effect := { witness := { proposalExact := by rfl } }
    historical := { witness := { exact := by rfl } }
    futures :=
      { covered := fun requests =>
          { outcome := independentLearnedFutureContract.outcome
              { network :=
                  (LearnedAlignedOperationalContract.coveredFutureAt
                    learnedAlignedState requests).source }
              ((LearnedAlignedOperationalContract.coveredFutureAt
                learnedAlignedState requests).requests.map fun input =>
                  { input := input })
            outcomeExact := rfl }
        realization := independentLearnedCoveredFutureRealization .aligned } }

/-! ## Learned meta-contract and exact transition -/

inductive LearnedContractAdmission : LearnedOperationalContract -> Type where
  | initial : LearnedContractAdmission .initial
  | aligned : LearnedContractAdmission .aligned

inductive LearnedContractTransitionPermission :
    LearnedOperationalContract -> LearnedOperationalContract -> Type where
  | installAligned : LearnedContractTransitionPermission .initial .aligned

inductive LearnedPersistentObligation where
  | admittedIntent

def learnedPersistentWitness
    (_current _next : LearnedOperationalContract)
    (_obligation : LearnedPersistentObligation) : Type 3 :=
  ULift.{3}
    (AdmittedIndependentLearnedIntent
      .preserveAuthorizedBehavior)

inductive LearnedRecheckObligation where
  | authorizationConsumption

def learnedRecheckedWitness
    (_current _next : LearnedOperationalContract)
    (_obligation : LearnedRecheckObligation) : Type 3 :=
  LearnedAuthorizationWitness independentLearnedFirstSuccessorNetwork

inductive LearnedExecutedStateTransition :
    {current next : LearnedOperationalContract} ->
      LearnedContractTransitionPermission current next ->
      ReconfiguredExecutionState
        (learnedOperationalContract current).family ->
      ReconfiguredExecutionState
        (learnedOperationalContract next).family -> Type 4 where
  | installAligned :
      LearnedExecutedStateTransition
        LearnedContractTransitionPermission.installAligned
        learnedInitialState learnedAlignedState

def learnedConstitutiveMetaContract : ConstitutiveMetaContract where
  Contract := LearnedOperationalContract
  operational := learnedOperationalContract
  Admits := LearnedContractAdmission
  TransitionPermission := LearnedContractTransitionPermission
  PersistentObligation := fun _ _ => LearnedPersistentObligation
  SourcePersistentWitness := learnedPersistentWitness
  TargetPersistentWitness := learnedPersistentWitness
  transportPersistent := by
    intro current next permission obligation witness
    exact witness
  RecheckObligation := fun _ _ => LearnedRecheckObligation
  RecheckedWitness := learnedRecheckedWitness
  recheckInvalidated := by
    intro current next permission obligation
    exact { consumed := alignedUpdate_consumes_authorization }
  ExecutedStateTransition := LearnedExecutedStateTransition

def learnedOperationalTransition : OperationalContractTransition
    learnedConstitutiveMetaContract .initial .aligned :=
  certifyOperationalContractTransition .initial .aligned
    .installAligned

/-! ## Proof-free learned artifacts and executable interface -/

structure LearnedReceivedArtifact where
  contract : LearnedOperationalContract
  network : SerializedNetwork
  stableNaming : SerializedStableArtifactNaming
  deriving DecidableEq

def learnedReceivedInitialArtifact : LearnedReceivedArtifact :=
  { contract := .initial
    network := independentLearnedInitialNetwork
    stableNaming := learnedInitialSerializedNaming }

def learnedReceivedAlignedArtifact : LearnedReceivedArtifact :=
  { contract := .aligned
    network := independentLearnedFirstSuccessorNetwork
    stableNaming := learnedAlignedSerializedNaming }

def learnedReceivedBypassArtifact : LearnedReceivedArtifact :=
  { contract := .aligned
    network := independentLearnedBypassNetwork
    stableNaming := learnedAlignedSerializedNaming }

inductive LearnedExecutableDecodedArtifact :
    LearnedReceivedArtifact -> Type 4 where
  | initial : LearnedExecutableDecodedArtifact learnedReceivedInitialArtifact
  | aligned : LearnedExecutableDecodedArtifact learnedReceivedAlignedArtifact

def LearnedExecutableDecodedArtifact.contract
    {source : LearnedReceivedArtifact} :
    LearnedExecutableDecodedArtifact source -> LearnedOperationalContract
  | .initial => .initial
  | .aligned => .aligned

def LearnedExecutableDecodedArtifact.artifact
    {source : LearnedReceivedArtifact} :
    (decoded : LearnedExecutableDecodedArtifact source) ->
      DecodedNeuralArtifact
        (learnedOperationalContract decoded.contract)
  | .initial => learnedDecodedInitialArtifact
  | .aligned => learnedDecodedAlignedArtifact

def LearnedExecutableDecodedArtifact.stableNaming
    {source : LearnedReceivedArtifact} :
    (decoded : LearnedExecutableDecodedArtifact source) ->
      DecodedStableArtifactNaming decoded.artifact source.stableNaming
  | .initial => learnedDecodedInitialStableNaming
  | .aligned => learnedDecodedAlignedStableNaming

def LearnedExecutableDecodedArtifact.state
    {source : LearnedReceivedArtifact} :
    (decoded : LearnedExecutableDecodedArtifact source) ->
      ReconfiguredExecutionState
        (learnedOperationalContract decoded.contract).family
  | .initial => learnedInitialState
  | .aligned => learnedAlignedState

def LearnedExecutableDecodedArtifact.fragments
    {source : LearnedReceivedArtifact} :
    (decoded : LearnedExecutableDecodedArtifact source) ->
      StateCertificateFragments (learnedOperationalContract decoded.contract)
        decoded.artifact decoded.state
  | .initial => learnedInitialStateFragments
  | .aligned => learnedAlignedStateFragments

inductive LearnedExecutableArtifactError where
  | malformed (problem : ArtifactError)
  | invalidNaming (problem : StableNamingError)
  | unsupportedArtifact
  deriving DecidableEq

def decodeLearnedExecutableArtifact
    (source : LearnedReceivedArtifact) :
    Except LearnedExecutableArtifactError
      (LearnedExecutableDecodedArtifact source) :=
  match decodeArtifact (learnedOperationalContract source.contract)
      source.network with
  | .error problem => .error (.malformed problem)
  | .ok artifact =>
      match decodeStableArtifactNaming artifact source.stableNaming with
      | .error problem => .error (.invalidNaming problem)
      | .ok _ =>
          if initialExact : source = learnedReceivedInitialArtifact then
            initialExact ▸ .ok .initial
          else if alignedExact : source = learnedReceivedAlignedArtifact then
            alignedExact ▸ .ok .aligned
          else
            .error .unsupportedArtifact

def learnedAdmissionDecision (contract : LearnedOperationalContract) :
    ReflectedDecision (LearnedContractAdmission contract) :=
  match contract with
  | .initial => reflectedTrue .initial
  | .aligned => reflectedTrue .aligned

def learnedTransitionDecision
    (request : ContractTransitionRequest learnedConstitutiveMetaContract) :
    ReflectedDecision
      (OperationalContractTransition learnedConstitutiveMetaContract
        request.current request.next) :=
  match request with
  | ⟨.initial, .aligned⟩ => reflectedTrue learnedOperationalTransition
  | ⟨.initial, .initial⟩ => reflectedFalse
  | ⟨.aligned, .initial⟩ => reflectedFalse
  | ⟨.aligned, .aligned⟩ => reflectedFalse

def learnedExecutableMetaContractInterface :
    ExecutableMetaContractInterface learnedConstitutiveMetaContract where
  ContractCode := LearnedOperationalContract
  encodeContract := fun contract => contract
  encodeContractInjective := fun _ _ same => same
  ContractNameError := Empty
  decodeContractName := fun source => .ok { contract := source, exact := rfl }
  ReceivedArtifact := LearnedReceivedArtifact
  artifactContractCode := LearnedReceivedArtifact.contract
  artifactNetwork := LearnedReceivedArtifact.network
  artifactStableNaming := LearnedReceivedArtifact.stableNaming
  ArtifactError := LearnedExecutableArtifactError
  DecodedArtifact := LearnedExecutableDecodedArtifact
  decodedContract := LearnedExecutableDecodedArtifact.contract
  decodedContractExact := by intro source decoded; cases decoded <;> rfl
  decodedNeuralArtifact := LearnedExecutableDecodedArtifact.artifact
  decodedNetworkExact := by intro source decoded; cases decoded <;> rfl
  decodedStableNaming := LearnedExecutableDecodedArtifact.stableNaming
  decodeReceivedArtifact := decodeLearnedExecutableArtifact
  stateOfArtifact := LearnedExecutableDecodedArtifact.state
  admissionDecision := learnedAdmissionDecision
  transitionDecision := learnedTransitionDecision
  basisDecision := fun decoded =>
    reflectedTrue decoded.fragments.structural.basis
  systemDecision := fun decoded =>
    reflectedTrue decoded.fragments.structural.systemExact
  declaredInputDecision := fun decoded =>
    reflectedTrue decoded.fragments.structural.inputDeclared
  requirementDecision := fun decoded =>
    reflectedTrue decoded.fragments.requirement.witness
  contextDecision := fun decoded =>
    reflectedTrue decoded.fragments.causal.witness
  authorizationDecision := fun decoded =>
    reflectedTrue decoded.fragments.authorization.witness
  actionDecision := fun decoded =>
    reflectedTrue decoded.fragments.proposalAction.witness
  effectDecision := fun decoded =>
    reflectedTrue decoded.fragments.effect.witness
  historicalDecision := fun decoded =>
    reflectedTrue decoded.fragments.historical.witness
  coveredFuturesDecision := fun decoded =>
    reflectedTrue decoded.fragments.futures.covered
  futureRealizationDecision := fun decoded =>
    reflectedTrue decoded.fragments.futures.realization

/-! ## The learned source produced by the generic initial checker -/

def learnedExecutableStateAcceptance
    {source : LearnedReceivedArtifact}
    (decoded : LearnedExecutableDecodedArtifact source) :
    ExecutableStateAcceptance learnedExecutableMetaContractInterface
      decoded :=
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

def learnedInitialCheckSuccess : InitialCheckSuccess
    learnedExecutableMetaContractInterface learnedReceivedInitialArtifact :=
  match exact : checkInitial learnedExecutableMetaContractInterface
      learnedReceivedInitialArtifact with
  | .ok success => success
  | .error _ => False.elim (by cases exact)

theorem checkInitial_accepts_learned_artifact :
    checkInitial learnedExecutableMetaContractInterface
        learnedReceivedInitialArtifact =
      .ok learnedInitialCheckSuccess := by
  rfl

def learnedInitialCheckedAgent : CheckedAgent
    learnedConstitutiveMetaContract .initial :=
  learnedInitialCheckSuccess.checkedAgent

theorem learnedInitialCheckedAgent_state_exact :
    learnedInitialCheckedAgent.state = learnedInitialState := by
  rfl

theorem learnedInitialCheckedAgent_artifact_exact :
    learnedInitialCheckedAgent.artifact = learnedDecodedInitialArtifact := by
  rfl

/-! ## Learned candidate analysis by the generic incremental checker -/

def learnedPreCertificateGraph : PreCertificateConstitutiveGraph
    learnedInitialCheckedAgent.certificate.basis.naming
      learnedAlignedFiniteCausalBasis.naming :=
  calculatePreCertificateConstitutiveGraph
    learnedInitialCheckedAgent.certificate.basis.naming
    learnedAlignedFiniteCausalBasis.naming

/-- Every stable serial of the aligned learned artifact is deliberately a new
version identity.  Consequently every target artifact node belongs to the
affected cone and the learned adapter performs a complete structural
recomputation rather than claiming unsupported reuse. -/
def learnedRecomputedStructuralFragments :
    List (StableNodeKey × StableArtifactObservation) :=
  learnedPreCertificateGraph.targetObservations

def learnedCalculatedStructuralAssembly :
    CalculatedIncrementalStructuralAssembly
      learnedInitialCheckedAgent.certificate learnedPreCertificateGraph []
        learnedRecomputedStructuralFragments :=
  certifyCalculatedIncrementalStructuralAssembly (by rfl) rfl

def learnedAlignedTargetAnalysis :
    IncrementalTargetAnalysis learnedInitialCheckedAgent :=
  { nextContract := .aligned
    contractAdmitted := .aligned
    artifact := learnedDecodedAlignedArtifact
    state := learnedAlignedState
    targetNaming := learnedAlignedFiniteCausalBasis.naming
    preCertificateGraph := learnedPreCertificateGraph
    transportedStructural := []
    recomputedStructural := learnedRecomputedStructuralFragments
    structuralAssembly := learnedCalculatedStructuralAssembly
    fragments := learnedAlignedStateFragments
    fragmentNamingExact := rfl
    fragmentObservationsExact := rfl
    transition := learnedOperationalTransition
    execution := LearnedExecutedStateTransition.installAligned }

inductive LearnedRuntimeUpdateError where
  | malformedArtifact (problem : ArtifactError)
  | unexpectedSourceArtifact
  | unadmittedIntent
  | missingConstitutiveDependency
  | unsupportedTargetArtifact
  deriving DecidableEq

structure LearnedIncrementalEngineAnalysis
    (candidate : IndependentLearnedUpdateCandidate) : Type 6 where
  private mk ::
  target : IncrementalTargetAnalysis learnedInitialCheckedAgent
  targetExact : target = learnedAlignedTargetAnalysis

def analyzeLearnedRuntimeUpdate
    (candidate : IndependentLearnedUpdateCandidate) :
    Except LearnedRuntimeUpdateError
      (LearnedIncrementalEngineAnalysis candidate) :=
  if _sourceExact : candidate.sourceArtifact =
      learnedInitialCheckedAgent.artifact.source then
    if _intentExact : candidate.intent =
        .preserveAuthorizedBehavior then
      match decodeArtifact LearnedAlignedOperationalContract
          candidate.targetArtifact with
      | .error problem => .error (.malformedArtifact problem)
      | .ok _ =>
          if _dependencyExact :
              primaryAuthorizationConstitutivelyConsumed
                candidate.targetArtifact = true then
            if _targetExact : candidate.targetArtifact =
                independentLearnedFirstSuccessorNetwork then
              .ok (.mk learnedAlignedTargetAnalysis rfl)
            else
              .error .unsupportedTargetArtifact
          else
            .error .missingConstitutiveDependency
    else
      .error .unadmittedIntent
  else
    .error .unexpectedSourceArtifact

def learnedIncrementalCheckerEngine :
    IncrementalCheckerEngine learnedInitialCheckedAgent :=
  { Update := IndependentLearnedUpdateCandidate
    Error := LearnedRuntimeUpdateError
    Analysis := LearnedIncrementalEngineAnalysis
    analyze := analyzeLearnedRuntimeUpdate
    target := fun analysis => analysis.target }

theorem learnedGenericChecker_accepts_aligned :
    GenericIncrementalUpdateAccepted learnedIncrementalCheckerEngine
      alignedUpdate := by
  apply (checkGenericIncrementalUpdate_complete_for_local_conditions
    learnedIncrementalCheckerEngine alignedUpdate).2
  exact ⟨.mk learnedAlignedTargetAnalysis rfl, rfl⟩

theorem learnedGenericChecker_rejects_bypass :
    checkGenericIncrementalUpdate learnedIncrementalCheckerEngine
        bypassUpdate =
      .error .missingConstitutiveDependency := by
  rfl

/-- The dependent update language exposes plain learned candidates only at
the exact checked source returned by `checkInitial`.  No constructor exists
at an independently assembled source or after the aligned successor. -/
inductive LearnedRuntimeUpdate :
    {contract : LearnedOperationalContract} ->
      CheckedAgent learnedConstitutiveMetaContract contract -> Type where
  | candidate (update : IndependentLearnedUpdateCandidate) :
      LearnedRuntimeUpdate learnedInitialCheckedAgent

def learnedAlignedCheckedUpdate : CheckedUpdate
    learnedInitialCheckedAgent .aligned :=
  buildIncrementalCheckedUpdate learnedAlignedTargetAnalysis

def learnedAlignedDependentResult :
    DependentCheckedUpdateResult learnedInitialCheckedAgent :=
  dependentCheckedUpdateResult learnedAlignedCheckedUpdate

def learnedDependentIncrementalChecker :
    DependentIncrementalChecker learnedConstitutiveMetaContract where
  Error := LearnedRuntimeUpdateError
  Update := LearnedRuntimeUpdate
  check := by
    intro contract current update
    cases update with
    | candidate candidate =>
        match accepted : checkGenericIncrementalUpdate
            learnedIncrementalCheckerEngine candidate with
        | .error problem => exact .error problem
        | .ok success =>
            exact .ok (dependentCheckedUpdateResult success.checked)

def learnedInitialCertifiedRuntime : CertifiedRuntime
    learnedDependentIncrementalChecker learnedInitialCheckedAgent :=
  initialCertifiedRuntime learnedDependentIncrementalChecker
    learnedInitialCheckedAgent

def learnedAlignedRuntimeUpdate :
    learnedDependentIncrementalChecker.Update
      learnedInitialCertifiedRuntime.current :=
  .candidate alignedUpdate

def learnedBypassRuntimeUpdate :
    learnedDependentIncrementalChecker.Update
      learnedInitialCertifiedRuntime.current :=
  .candidate bypassUpdate

def learnedAlignedCertifiedRuntime : CertifiedRuntime
    learnedDependentIncrementalChecker learnedInitialCheckedAgent :=
  match submitUpdate learnedInitialCertifiedRuntime
      learnedAlignedRuntimeUpdate with
  | .ok runtime => runtime
  | .error _ => learnedInitialCertifiedRuntime

theorem submitUpdate_learned_aligned_exact :
    submitUpdate learnedInitialCertifiedRuntime
        learnedAlignedRuntimeUpdate =
      .ok learnedAlignedCertifiedRuntime := by
  rfl

theorem submitUpdate_learned_bypass_rejected :
    submitUpdate learnedInitialCertifiedRuntime
        learnedBypassRuntimeUpdate =
      .error .missingConstitutiveDependency := by
  rfl

theorem learnedDependentChecker_rejects_bypass :
    learnedDependentIncrementalChecker.check
        learnedInitialCertifiedRuntime.current
        learnedBypassRuntimeUpdate =
      .error .missingConstitutiveDependency := by
  rfl

theorem learned_bypass_rejected_without_successor :
    Not (Exists fun next =>
      submitUpdate learnedInitialCertifiedRuntime
        learnedBypassRuntimeUpdate = .ok next) :=
  submitUpdate_rejected_cannot_install learnedInitialCertifiedRuntime
    learnedBypassRuntimeUpdate .missingConstitutiveDependency
      learnedDependentChecker_rejects_bypass

theorem learnedAlignedRuntime_state_exact :
    learnedAlignedCertifiedRuntime.current.state = learnedAlignedState := by
  rfl

theorem learnedAlignedRuntime_artifact_exact :
    learnedAlignedCertifiedRuntime.current.artifact =
      learnedDecodedAlignedArtifact := by
  rfl

theorem learnedAlignedRuntime_certificate_from_generic_checker :
    learnedAlignedCertifiedRuntime.current.certificate =
      assembleStateConstitution learnedAlignedTargetAnalysis.fragments := by
  rfl

def learnedInitialCertifiedRuntime_reachable :
    CertifiedRuntimeReachable learnedDependentIncrementalChecker
      learnedInitialCheckedAgent learnedInitialCertifiedRuntime :=
  .initial

def learnedAlignedCertifiedRuntime_reachable :
    CertifiedRuntimeReachable learnedDependentIncrementalChecker
      learnedInitialCheckedAgent learnedAlignedCertifiedRuntime :=
  .submitted learnedInitialCertifiedRuntime learnedAlignedCertifiedRuntime
    learnedAlignedRuntimeUpdate learnedInitialCertifiedRuntime_reachable
    submitUpdate_learned_aligned_exact

def learnedAlignedCertifiedRuntime_accessibility :
    CertifiedRuntimeAccessibility learnedAlignedCertifiedRuntime :=
  reachableRuntime_accessibility learnedAlignedCertifiedRuntime
    learnedAlignedCertifiedRuntime_reachable

def learnedAlignedRuntime_checkedHistory :
    EveryRuntimeStepSatisfies learnedAlignedCertifiedRuntime.history :=
  learnedAlignedCertifiedRuntime.checkedHistory

def learnedAlignedRuntime_preservedContracts :
    EveryRuntimeStepPreservesContracts learnedAlignedCertifiedRuntime.history :=
  learnedAlignedCertifiedRuntime.preservedContracts

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.NeuralAgent.independentLearnedRequirementFamily
#print axioms ConstitutiveSearch.NeuralAgent.independentLearnedFutureContract
#print axioms ConstitutiveSearch.NeuralAgent.learnedOperationalContract
#print axioms ConstitutiveSearch.NeuralAgent.learnedDecodedInitialArtifact
#print axioms ConstitutiveSearch.NeuralAgent.learnedDecodedAlignedArtifact
#print axioms ConstitutiveSearch.NeuralAgent.learnedInitialAuthorizationRole
#print axioms ConstitutiveSearch.NeuralAgent.learnedAlignedAuthorizationRole
#print axioms ConstitutiveSearch.NeuralAgent.learnedInitialFiniteCausalBasis
#print axioms ConstitutiveSearch.NeuralAgent.learnedAlignedFiniteCausalBasis
#print axioms ConstitutiveSearch.NeuralAgent.learnedInitialStateFragments
#print axioms ConstitutiveSearch.NeuralAgent.learnedAlignedStateFragments
#print axioms ConstitutiveSearch.NeuralAgent.learnedConstitutiveMetaContract
#print axioms ConstitutiveSearch.NeuralAgent.learnedExecutableMetaContractInterface
#print axioms ConstitutiveSearch.NeuralAgent.checkInitial_accepts_learned_artifact
#print axioms ConstitutiveSearch.NeuralAgent.learnedInitialCheckedAgent
#print axioms ConstitutiveSearch.NeuralAgent.learnedAlignedTargetAnalysis
#print axioms ConstitutiveSearch.NeuralAgent.analyzeLearnedRuntimeUpdate
#print axioms ConstitutiveSearch.NeuralAgent.learnedGenericChecker_accepts_aligned
#print axioms ConstitutiveSearch.NeuralAgent.learnedGenericChecker_rejects_bypass
#print axioms ConstitutiveSearch.NeuralAgent.learnedDependentIncrementalChecker
#print axioms ConstitutiveSearch.NeuralAgent.learnedAlignedCheckedUpdate
#print axioms ConstitutiveSearch.NeuralAgent.learnedAlignedCertifiedRuntime
#print axioms ConstitutiveSearch.NeuralAgent.submitUpdate_learned_aligned_exact
#print axioms ConstitutiveSearch.NeuralAgent.submitUpdate_learned_bypass_rejected
#print axioms ConstitutiveSearch.NeuralAgent.learnedDependentChecker_rejects_bypass
#print axioms ConstitutiveSearch.NeuralAgent.learned_bypass_rejected_without_successor
#print axioms ConstitutiveSearch.NeuralAgent.learnedAlignedRuntime_state_exact
#print axioms ConstitutiveSearch.NeuralAgent.learnedAlignedRuntime_artifact_exact
#print axioms ConstitutiveSearch.NeuralAgent.learnedAlignedRuntime_certificate_from_generic_checker
#print axioms ConstitutiveSearch.NeuralAgent.learnedAlignedCertifiedRuntime_reachable
#print axioms ConstitutiveSearch.NeuralAgent.learnedAlignedCertifiedRuntime_accessibility
#print axioms ConstitutiveSearch.NeuralAgent.learnedAlignedRuntime_checkedHistory
#print axioms ConstitutiveSearch.NeuralAgent.learnedAlignedRuntime_preservedContracts
/- AXIOM_AUDIT_END -/
