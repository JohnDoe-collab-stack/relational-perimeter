import RelationalPerimeter.Agents.Neural.CertifiedRuntimeAccessibility
import RelationalPerimeter.Agents.Neural.FiniteCounterfactualDivergence

/-!
# Learned artifact adapter for the generic checker and runtime

The independently learned source and its two candidate successors enter the
same constitutive checking boundary as every other certified neural state.
The adapter does not call the earlier specialized learned-update checker.
Instead it supplies a local operational contract, reflected initial-state
decisions, the common proof-free serialized update language, and an incremental engine
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
  learnedRuntimeDeclaredCurrentDomain.map
    IndependentLearnedInput.toRequirementInput

def independentLearnedDeclaredInputs_complete
    (current : IndependentLearnedCurrentCase) :
    Listed current.input.toRequirementInput independentLearnedDeclaredInputs := by
  cases current with
  | neither => exact .head
  | contextOnly => exact .tail .head
  | requirementOnly => exact .tail (.tail .head)
  | both => exact .tail (.tail (.tail .head))

structure IndependentLearnedFutureSource : Type 3 where
  network : SerializedNetwork

structure IndependentLearnedFutureInput : Type 3 where
  input : IndependentLearnedInput

structure IndependentLearnedFutureEvent : Type 3 where
  outputs : List Activation

structure IndependentLearnedFutureObservation : Type 3 where
  operationallyReady : Bool

/-- Admission is a property of the received future request.  It is fixed by
the requirement/context distinction and is independent of the network whose
future is being observed. -/
structure IndependentLearnedFutureAdmission
    (input : IndependentLearnedFutureInput) : Type 3 where
  requirementDiffers : independentLearnedRequirementDiffers
    input.input.requirement input.input.context = true

def decideIndependentLearnedFutureAdmission
    (input : IndependentLearnedFutureInput) :
    PSum (IndependentLearnedFutureAdmission input)
      (IndependentLearnedFutureAdmission input -> False) :=
  if differs : independentLearnedRequirementDiffers
      input.input.requirement input.input.context = true then
    .inl { requirementDiffers := differs }
  else
    .inr (fun witness => differs witness.requirementDiffers)

def independentLearnedFutureContract :
    FutureContract.{3, 3} IndependentLearnedFutureSource
      IndependentLearnedFutureInput IndependentLearnedFutureEvent
      IndependentLearnedFutureObservation where
  next := fun source _ => source
  event := fun source input =>
    { outputs := executeSerializedArtifact source.network input.input }
  read := fun _ => { operationallyReady := true }
  Allow := fun _ input => IndependentLearnedFutureAdmission input
  decision := fun _ input => decideIndependentLearnedFutureAdmission input

/-- The reduced future memory is the finite behavioral table of the declared
three Boolean signals.  It contains neither a serialized network nor a stable
historical identity. -/
structure IndependentLearnedOperationalMemory : Type 3 where
  fff : List Activation
  fft : List Activation
  ftf : List Activation
  ftt : List Activation
  tff : List Activation
  tft : List Activation
  ttf : List Activation
  ttt : List Activation

def IndependentLearnedOperationalMemory.execute
    (memory : IndependentLearnedOperationalMemory) :
    IndependentLearnedInput -> List Activation
  | ⟨false, false, false⟩ => memory.fff
  | ⟨false, false, true⟩ => memory.fft
  | ⟨false, true, false⟩ => memory.ftf
  | ⟨false, true, true⟩ => memory.ftt
  | ⟨true, false, false⟩ => memory.tff
  | ⟨true, false, true⟩ => memory.tft
  | ⟨true, true, false⟩ => memory.ttf
  | ⟨true, true, true⟩ => memory.ttt

def independentLearnedReducedFutureContract :
    FutureContract.{3, 3} IndependentLearnedOperationalMemory
      IndependentLearnedFutureInput IndependentLearnedFutureEvent
      IndependentLearnedFutureObservation where
  next := fun memory _ => memory
  event := fun memory input => { outputs := memory.execute input.input }
  read := fun _ => { operationallyReady := true }
  Allow := fun _ input => IndependentLearnedFutureAdmission input
  decision := fun _ input => decideIndependentLearnedFutureAdmission input

def independentLearnedFutureProjection
    (source : IndependentLearnedFutureSource) :
    IndependentLearnedOperationalMemory :=
  { fff := executeSerializedArtifact source.network ⟨false, false, false⟩
    fft := executeSerializedArtifact source.network ⟨false, false, true⟩
    ftf := executeSerializedArtifact source.network ⟨false, true, false⟩
    ftt := executeSerializedArtifact source.network ⟨false, true, true⟩
    tff := executeSerializedArtifact source.network ⟨true, false, false⟩
    tft := executeSerializedArtifact source.network ⟨true, false, true⟩
    ttf := executeSerializedArtifact source.network ⟨true, true, false⟩
    ttt := executeSerializedArtifact source.network ⟨true, true, true⟩ }

def independentLearnedFutureSimulation : FutureContractSimulationData
    independentLearnedFutureContract independentLearnedReducedFutureContract
      independentLearnedFutureProjection where
  forward := fun _ _ witness => witness
  backward := fun _ _ witness => witness
  backwardForward := by intro source input witness; rfl
  forwardBackward := by intro source input witness; rfl
  nextExact := by intro source input; rfl
  eventExact := by
    intro source input
    cases input with
    | mk input =>
        cases input with
        | mk requirement context authorization =>
            cases requirement <;> cases context <;> cases authorization <;>
              rfl
  readExact := by intro source; rfl

/-! ## Separate learned obligations -/

structure LearnedRequirementEncodingWitness
    (state : ReconfiguredExecutionState independentLearnedRequirementFamily) :
    Type 3 where
  inputExact : state.input = independentLearnedCertifiedInput

structure LearnedExecutedCausalWitness
    (state : ReconfiguredExecutionState independentLearnedRequirementFamily) :
    Type 3 where
  requirementPort : Fin state.system.inputCount
  requirementRole : CausalRole state.system state.input
    (.receivedInput requirementPort)
  contextPort : Fin state.system.inputCount
  contextRole : CausalRole state.system state.input
    (.receivedInput contextPort)
  authorizationPort : Fin state.system.inputCount
  authorizationRole : CausalRole state.system state.input
    (.receivedInput authorizationPort)
  requirementContextDistinct : requirementPort ≠ contextPort
  requirementAuthorizationDistinct : requirementPort ≠ authorizationPort
  contextAuthorizationDistinct : contextPort ≠ authorizationPort

structure LearnedAuthorizationWitness
    (state : ReconfiguredExecutionState independentLearnedRequirementFamily) :
    Type 3 where
  authorizationPort : Fin state.system.inputCount
  authorizationRole : CausalRole state.system state.input
    (.receivedInput authorizationPort)
  consumed : primaryAuthorizationConstitutivelyConsumed
    (serializeNativeSystem state.system) = true

structure LearnedProposalPreservation
    (state : ReconfiguredExecutionState independentLearnedRequirementFamily) :
    Type 3 where
  admittedIntent : AdmittedIndependentLearnedIntent
    .preserveAuthorizedBehavior
  proposalExact : state.system.proposal state.input =
    independentLearnedRequirementFamily.requiredProposal
      state.input.requirement state.input.context

/-- The request and result are calculated from one exact learned state.  The
executed causal roles and authorization witness are inputs to the private
constructor, rather than certificates stored beside an independently supplied
action. -/
structure LearnedActionWitness
    (state : ReconfiguredExecutionState independentLearnedRequirementFamily) :
    Type 3 where
  private mk ::
  preservation : LearnedProposalPreservation state
  causal : LearnedExecutedCausalWitness state
  authorization : LearnedAuthorizationWitness state
  authorizationPortExact :
    causal.authorizationPort = authorization.authorizationPort
  request : Agent.Request
  requestExact : request = publicAgentActionChannel.command
    (state.system.proposal state.input)
  result : Agent.Memory × Agent.Event
  evidence : Agent.RequestEvidence state.memory request result
  resultExact : result = Agent.executeInput state.memory request

def executeLearnedAction
    (state : ReconfiguredExecutionState independentLearnedRequirementFamily)
    (preservation : LearnedProposalPreservation state)
    (causal : LearnedExecutedCausalWitness state)
    (authorization : LearnedAuthorizationWitness state)
    (authorizationPortExact :
      causal.authorizationPort = authorization.authorizationPort) :
    LearnedActionWitness state :=
  let request := publicAgentActionChannel.command
    (state.system.proposal state.input)
  let produced := Agent.executeProducedInput state.memory request
  .mk preservation causal authorization authorizationPortExact
    request rfl produced.1 produced.2 rfl

theorem LearnedActionWitness.request_required_exact
    {state : ReconfiguredExecutionState independentLearnedRequirementFamily}
    (action : LearnedActionWitness state) :
    action.request = publicAgentActionChannel.command
      (independentLearnedRequirementFamily.requiredProposal
        state.input.requirement state.input.context) :=
  action.requestExact.trans
    (congrArg publicAgentActionChannel.command
      action.preservation.proposalExact)

theorem LearnedActionWitness.execution_exact
    {state : ReconfiguredExecutionState independentLearnedRequirementFamily}
    (action : LearnedActionWitness state) :
    action.result = Agent.executeInput state.memory action.request :=
  action.resultExact

/-- Effect satisfaction is the effect produced by the sealed action above.
It is not a proposition about the proposal value. -/
structure LearnedEffectWitness
    (state : ReconfiguredExecutionState independentLearnedRequirementFamily) :
    Type 3 where
  private mk ::
  action : LearnedActionWitness state
  successor : Agent.Memory
  event : Agent.Event
  successorExact : successor = action.result.1
  eventExact : event = action.result.2

def produceLearnedEffect
    {state : ReconfiguredExecutionState independentLearnedRequirementFamily}
    (action : LearnedActionWitness state) : LearnedEffectWitness state :=
  .mk action action.result.1 action.result.2 rfl rfl

theorem LearnedEffectWitness.effect_exact
    {state : ReconfiguredExecutionState independentLearnedRequirementFamily}
    (effect : LearnedEffectWitness state) :
    (effect.successor, effect.event) =
      Agent.executeInput state.memory effect.action.request := by
  rw [effect.successorExact, effect.eventExact]
  exact effect.action.execution_exact

def LearnedEffectWitness.targetState
    {state : ReconfiguredExecutionState independentLearnedRequirementFamily}
    (effect : LearnedEffectWitness state) :
    ReconfiguredExecutionState independentLearnedRequirementFamily :=
  { system := state.system
    input := state.input
    memory := effect.successor }

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

def learnedActionObligations : ContractObligationFamily where
  Statement := ULift.{3}
    (ReconfiguredExecutionState independentLearnedRequirementFamily)
  Witness := fun state => LearnedActionWitness state.down

def learnedAuthorizationObligations : ContractObligationFamily where
  Statement := ULift.{3}
    (ReconfiguredExecutionState independentLearnedRequirementFamily)
  Witness := fun state => LearnedAuthorizationWitness state.down

def learnedEffectObligations : ContractObligationFamily where
  Statement := ULift.{3}
    (ReconfiguredExecutionState independentLearnedRequirementFamily)
  Witness := fun state => LearnedEffectWitness state.down

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
  | extended
  deriving DecidableEq

def learnedExpectedNetwork : LearnedOperationalContract -> SerializedNetwork
  | .initial => independentLearnedInitialNetwork
  | .aligned => independentLearnedFirstSuccessorNetwork
  | .extended => independentLearnedSecondSuccessorNetwork

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
    declaredReplacementValues := [0, 1]
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
    proposalActionPreservation := learnedActionObligations
    proposalActionPreservationAt := fun state => ULift.up state
    authorizationAdmission := learnedAuthorizationObligations
    authorizationAdmissionAt := fun state => ULift.up state
    effectSatisfaction := learnedEffectObligations
    effectSatisfactionAt := fun state => ULift.up state
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
  { ReducedMemory := IndependentLearnedOperationalMemory
    reducedContract := independentLearnedReducedFutureContract
    project := independentLearnedFutureProjection
    simulation := independentLearnedFutureSimulation }

abbrev LearnedInitialOperationalContract : ConstitutiveContract :=
  learnedOperationalContract .initial

abbrev LearnedAlignedOperationalContract : ConstitutiveContract :=
  learnedOperationalContract .aligned

abbrev LearnedExtendedOperationalContract : ConstitutiveContract :=
  learnedOperationalContract .extended

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

def learnedDecodedExtendedArtifact :
    DecodedNeuralArtifact LearnedExtendedOperationalContract :=
  match exact : decodeArtifact LearnedExtendedOperationalContract
      independentLearnedSecondSuccessorNetwork with
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

theorem learnedExtendedArtifact_decodes :
    decodeArtifact LearnedExtendedOperationalContract
        independentLearnedSecondSuccessorNetwork =
      .ok learnedDecodedExtendedArtifact := by
  rfl

def learnedInitialState :
    ReconfiguredExecutionState independentLearnedRequirementFamily :=
  { system := learnedDecodedInitialArtifact.system
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

def learnedExtendedAuthorizationPort :
    Fin learnedDecodedExtendedArtifact.system.inputCount := ⟨2, by decide⟩

def learnedExtendedAuthorizationNeuron :
    Fin learnedDecodedExtendedArtifact.system.producedCount := ⟨3, by decide⟩

def learnedExtendedIntermediateNeuron :
    Fin learnedDecodedExtendedArtifact.system.producedCount := ⟨4, by decide⟩

def learnedExtendedPenultimateNeuron :
    Fin learnedDecodedExtendedArtifact.system.producedCount := ⟨6, by decide⟩

def learnedExtendedPrimaryNeuron :
    Fin learnedDecodedExtendedArtifact.system.producedCount := ⟨7, by decide⟩

def learnedExtendedPrimaryOutputPort :
    Fin learnedDecodedExtendedArtifact.system.outputs.sources.length :=
  ⟨0, by decide⟩

def learnedExtendedAuthorizationIntervention :
    Intervention
      (learnedDecodedExtendedArtifact.system.run
        independentLearnedCertifiedInput) where
  focus := .input learnedExtendedAuthorizationPort
  replacement := 0
  changesValue := by decide

def learnedExtendedAuthorizationEdge :
    EffectiveReadsFrom
      (learnedDecodedExtendedArtifact.system.run
        independentLearnedCertifiedInput)
      (.receivedInput learnedExtendedAuthorizationPort)
      (.neuronOutput learnedExtendedAuthorizationNeuron) :=
  .executedEdge learnedExtendedAuthorizationNeuron
    { source := .receivedInput learnedExtendedAuthorizationPort, weight := 1 }
    (by exact List.Mem.head _) (by decide)

def learnedExtendedIntermediateEdge :
    EffectiveReadsFrom
      (learnedDecodedExtendedArtifact.system.run
        independentLearnedCertifiedInput)
      (.neuronOutput learnedExtendedAuthorizationNeuron)
      (.neuronOutput learnedExtendedIntermediateNeuron) :=
  .executedEdge learnedExtendedIntermediateNeuron
    { source := .priorNeuron ⟨3, by decide⟩, weight := 1 }
    (by exact List.Mem.tail _ (List.Mem.head _)) (by decide)

def learnedExtendedPenultimateEdge :
    EffectiveReadsFrom
      (learnedDecodedExtendedArtifact.system.run
        independentLearnedCertifiedInput)
      (.neuronOutput learnedExtendedIntermediateNeuron)
      (.neuronOutput learnedExtendedPenultimateNeuron) :=
  .executedEdge learnedExtendedPenultimateNeuron
    { source := .priorNeuron ⟨4, by decide⟩, weight := 1 }
    (by exact List.Mem.head _) (by decide)

def learnedExtendedPrimaryEdge :
    EffectiveReadsFrom
      (learnedDecodedExtendedArtifact.system.run
        independentLearnedCertifiedInput)
      (.neuronOutput learnedExtendedPenultimateNeuron)
      (.neuronOutput learnedExtendedPrimaryNeuron) :=
  .executedEdge learnedExtendedPrimaryNeuron
    { source := .priorNeuron ⟨6, by decide⟩, weight := 1 }
    (by exact List.Mem.head _) (by decide)

def learnedExtendedAuthorizationPropagation :
    NontrivialExecutedChangePath learnedExtendedAuthorizationIntervention
      (.neuronOutput learnedExtendedPrimaryNeuron) :=
  .step
    (.step
      (.step
        (.step .origin learnedExtendedAuthorizationEdge
          { different := by decide })
        learnedExtendedIntermediateEdge { different := by decide })
      learnedExtendedPenultimateEdge { different := by decide })
    learnedExtendedPrimaryEdge { different := by decide }

def learnedExtendedAuthorizationRole :
    CausalRole learnedDecodedExtendedArtifact.system
      independentLearnedCertifiedInput
      (.receivedInput learnedExtendedAuthorizationPort) where
  intervention := learnedExtendedAuthorizationIntervention
  focusExact := rfl
  output := learnedExtendedPrimaryOutputPort
  propagation := learnedExtendedAuthorizationPropagation
  targetChange := { different := by decide }
  proposalChange :=
    { different := by
        change false ≠ true
        decide }

/-! ## Executed causal coverage of the canonical four-case domain -/

def IndependentLearnedCurrentCase.requirementReplacement :
    IndependentLearnedCurrentCase -> Activation
  | .neither => 1
  | .contextOnly => 1
  | .requirementOnly => 0
  | .both => 0

def learnedInitialRequirementPort :
    Fin learnedDecodedInitialArtifact.system.inputCount := ⟨0, by decide⟩

def learnedInitialXorNeuron :
    Fin learnedDecodedInitialArtifact.system.producedCount := ⟨2, by decide⟩

def learnedInitialSensitiveNeuron :
    IndependentLearnedCurrentCase ->
      Fin learnedDecodedInitialArtifact.system.producedCount
  | .neither => ⟨0, by decide⟩
  | .contextOnly => ⟨1, by decide⟩
  | .requirementOnly => ⟨0, by decide⟩
  | .both => ⟨1, by decide⟩

def learnedInitialCurrentIntervention
    (current : IndependentLearnedCurrentCase) :
    Intervention
      (learnedDecodedInitialArtifact.system.run
        current.input.toRequirementInput) where
  focus := .input learnedInitialRequirementPort
  replacement := current.requirementReplacement
  changesValue := by cases current <;> decide

def learnedInitialCurrentInputEdge
    (current : IndependentLearnedCurrentCase) :
    EffectiveReadsFrom
      (learnedDecodedInitialArtifact.system.run
        current.input.toRequirementInput)
      (.receivedInput learnedInitialRequirementPort)
      (.neuronOutput (learnedInitialSensitiveNeuron current)) := by
  cases current with
  | neither | requirementOnly =>
      exact .executedEdge ⟨0, by decide⟩
        { source := .receivedInput learnedInitialRequirementPort, weight := 1 }
        (by exact List.Mem.head _) (by decide)
  | contextOnly | both =>
      exact .executedEdge ⟨1, by decide⟩
        { source := .receivedInput learnedInitialRequirementPort, weight := -2 }
        (by exact List.Mem.head _) (by decide)

def learnedInitialCurrentXorEdge
    (current : IndependentLearnedCurrentCase) :
    EffectiveReadsFrom
      (learnedDecodedInitialArtifact.system.run
        current.input.toRequirementInput)
      (.neuronOutput (learnedInitialSensitiveNeuron current))
      (.neuronOutput learnedInitialXorNeuron) := by
  cases current with
  | neither | requirementOnly =>
      exact .executedEdge learnedInitialXorNeuron
        { source := .priorNeuron ⟨0, by decide⟩, weight := 1 }
        (by exact List.Mem.head _) (by decide)
  | contextOnly | both =>
      exact .executedEdge learnedInitialXorNeuron
        { source := .priorNeuron ⟨1, by decide⟩, weight := 1 }
        (by exact List.Mem.tail _ (List.Mem.head _)) (by decide)

def learnedInitialCurrentPrimaryEdge
    (current : IndependentLearnedCurrentCase) :
    EffectiveReadsFrom
      (learnedDecodedInitialArtifact.system.run
        current.input.toRequirementInput)
      (.neuronOutput learnedInitialXorNeuron)
      (.neuronOutput learnedInitialPrimaryNeuron) :=
  .executedEdge learnedInitialPrimaryNeuron
    { source := .priorNeuron ⟨2, by decide⟩, weight := 1 }
    (by exact List.Mem.head _) (by cases current <;> decide)

def learnedInitialCurrentPropagation
    (current : IndependentLearnedCurrentCase) :
    NontrivialExecutedChangePath (learnedInitialCurrentIntervention current)
      (.neuronOutput learnedInitialPrimaryNeuron) :=
  .step
    (.step
      (.step .origin (learnedInitialCurrentInputEdge current)
        { different := by cases current <;> decide })
      (learnedInitialCurrentXorEdge current)
        { different := by cases current <;> decide })
    (learnedInitialCurrentPrimaryEdge current)
      { different := by cases current <;> decide }

def learnedInitialCurrentRole
    (current : IndependentLearnedCurrentCase) :
    CausalRole learnedDecodedInitialArtifact.system
      current.input.toRequirementInput
      (.receivedInput learnedInitialRequirementPort) where
  intervention := learnedInitialCurrentIntervention current
  focusExact := rfl
  output := learnedInitialPrimaryOutputPort
  propagation := learnedInitialCurrentPropagation current
  targetChange := { different := by cases current <;> decide }
  proposalChange :=
    { different := by
        cases current with
        | neither => change true ≠ false; decide
        | contextOnly => change false ≠ true; decide
        | requirementOnly => change false ≠ true; decide
        | both => change true ≠ false; decide }

def learnedAlignedRequirementPort :
    Fin learnedDecodedAlignedArtifact.system.inputCount := ⟨0, by decide⟩

def learnedAlignedXorNeuron :
    Fin learnedDecodedAlignedArtifact.system.producedCount := ⟨2, by decide⟩

def learnedAlignedSensitiveNeuron :
    IndependentLearnedCurrentCase ->
      Fin learnedDecodedAlignedArtifact.system.producedCount
  | .neither => ⟨0, by decide⟩
  | .contextOnly => ⟨1, by decide⟩
  | .requirementOnly => ⟨0, by decide⟩
  | .both => ⟨1, by decide⟩

def learnedAlignedCurrentIntervention
    (current : IndependentLearnedCurrentCase) :
    Intervention
      (learnedDecodedAlignedArtifact.system.run
        current.input.toRequirementInput) where
  focus := .input learnedAlignedRequirementPort
  replacement := current.requirementReplacement
  changesValue := by cases current <;> decide

def learnedAlignedCurrentInputEdge
    (current : IndependentLearnedCurrentCase) :
    EffectiveReadsFrom
      (learnedDecodedAlignedArtifact.system.run
        current.input.toRequirementInput)
      (.receivedInput learnedAlignedRequirementPort)
      (.neuronOutput (learnedAlignedSensitiveNeuron current)) := by
  cases current with
  | neither | requirementOnly =>
      exact .executedEdge ⟨0, by decide⟩
        { source := .receivedInput learnedAlignedRequirementPort, weight := 1 }
        (by exact List.Mem.head _) (by decide)
  | contextOnly | both =>
      exact .executedEdge ⟨1, by decide⟩
        { source := .receivedInput learnedAlignedRequirementPort, weight := -2 }
        (by exact List.Mem.head _) (by decide)

def learnedAlignedCurrentXorEdge
    (current : IndependentLearnedCurrentCase) :
    EffectiveReadsFrom
      (learnedDecodedAlignedArtifact.system.run
        current.input.toRequirementInput)
      (.neuronOutput (learnedAlignedSensitiveNeuron current))
      (.neuronOutput learnedAlignedXorNeuron) := by
  cases current with
  | neither | requirementOnly =>
      exact .executedEdge learnedAlignedXorNeuron
        { source := .priorNeuron ⟨0, by decide⟩, weight := 1 }
        (by exact List.Mem.head _) (by decide)
  | contextOnly | both =>
      exact .executedEdge learnedAlignedXorNeuron
        { source := .priorNeuron ⟨1, by decide⟩, weight := 1 }
        (by exact List.Mem.tail _ (List.Mem.head _)) (by decide)

def learnedAlignedCurrentIntermediateEdge
    (current : IndependentLearnedCurrentCase) :
    EffectiveReadsFrom
      (learnedDecodedAlignedArtifact.system.run
        current.input.toRequirementInput)
      (.neuronOutput learnedAlignedXorNeuron)
      (.neuronOutput learnedAlignedIntermediateNeuron) :=
  .executedEdge learnedAlignedIntermediateNeuron
    { source := .priorNeuron ⟨2, by decide⟩, weight := 1 }
    (by exact List.Mem.head _) (by cases current <;> decide)

def learnedAlignedCurrentPrimaryEdge
    (current : IndependentLearnedCurrentCase) :
    EffectiveReadsFrom
      (learnedDecodedAlignedArtifact.system.run
        current.input.toRequirementInput)
      (.neuronOutput learnedAlignedIntermediateNeuron)
      (.neuronOutput learnedAlignedPrimaryNeuron) :=
  .executedEdge learnedAlignedPrimaryNeuron
    { source := .priorNeuron ⟨4, by decide⟩, weight := 1 }
    (by exact List.Mem.head _) (by cases current <;> decide)

def learnedAlignedCurrentPropagation
    (current : IndependentLearnedCurrentCase) :
    NontrivialExecutedChangePath (learnedAlignedCurrentIntervention current)
      (.neuronOutput learnedAlignedPrimaryNeuron) :=
  .step
    (.step
      (.step
        (.step .origin (learnedAlignedCurrentInputEdge current)
          { different := by cases current <;> decide })
        (learnedAlignedCurrentXorEdge current)
          { different := by cases current <;> decide })
      (learnedAlignedCurrentIntermediateEdge current)
        { different := by cases current <;> decide })
    (learnedAlignedCurrentPrimaryEdge current)
      { different := by cases current <;> decide }

def learnedAlignedCurrentRole
    (current : IndependentLearnedCurrentCase) :
    CausalRole learnedDecodedAlignedArtifact.system
      current.input.toRequirementInput
      (.receivedInput learnedAlignedRequirementPort) where
  intervention := learnedAlignedCurrentIntervention current
  focusExact := rfl
  output := learnedAlignedPrimaryOutputPort
  propagation := learnedAlignedCurrentPropagation current
  targetChange := { different := by cases current <;> decide }
  proposalChange :=
    { different := by
        cases current with
        | neither => change true ≠ false; decide
        | contextOnly => change false ≠ true; decide
        | requirementOnly => change false ≠ true; decide
        | both => change true ≠ false; decide }

def learnedExtendedRequirementPort :
    Fin learnedDecodedExtendedArtifact.system.inputCount := ⟨0, by decide⟩

def learnedExtendedXorNeuron :
    Fin learnedDecodedExtendedArtifact.system.producedCount := ⟨2, by decide⟩

def learnedExtendedSensitiveNeuron :
    IndependentLearnedCurrentCase ->
      Fin learnedDecodedExtendedArtifact.system.producedCount
  | .neither => ⟨0, by decide⟩
  | .contextOnly => ⟨1, by decide⟩
  | .requirementOnly => ⟨0, by decide⟩
  | .both => ⟨1, by decide⟩

def learnedExtendedCurrentIntervention
    (current : IndependentLearnedCurrentCase) :
    Intervention
      (learnedDecodedExtendedArtifact.system.run
        current.input.toRequirementInput) where
  focus := .input learnedExtendedRequirementPort
  replacement := current.requirementReplacement
  changesValue := by cases current <;> decide

def learnedExtendedCurrentInputEdge
    (current : IndependentLearnedCurrentCase) :
    EffectiveReadsFrom
      (learnedDecodedExtendedArtifact.system.run
        current.input.toRequirementInput)
      (.receivedInput learnedExtendedRequirementPort)
      (.neuronOutput (learnedExtendedSensitiveNeuron current)) := by
  cases current with
  | neither | requirementOnly =>
      exact .executedEdge ⟨0, by decide⟩
        { source := .receivedInput learnedExtendedRequirementPort, weight := 1 }
        (by exact List.Mem.head _) (by decide)
  | contextOnly | both =>
      exact .executedEdge ⟨1, by decide⟩
        { source := .receivedInput learnedExtendedRequirementPort, weight := -2 }
        (by exact List.Mem.head _) (by decide)

def learnedExtendedCurrentXorEdge
    (current : IndependentLearnedCurrentCase) :
    EffectiveReadsFrom
      (learnedDecodedExtendedArtifact.system.run
        current.input.toRequirementInput)
      (.neuronOutput (learnedExtendedSensitiveNeuron current))
      (.neuronOutput learnedExtendedXorNeuron) := by
  cases current with
  | neither | requirementOnly =>
      exact .executedEdge learnedExtendedXorNeuron
        { source := .priorNeuron ⟨0, by decide⟩, weight := 1 }
        (by exact List.Mem.head _) (by decide)
  | contextOnly | both =>
      exact .executedEdge learnedExtendedXorNeuron
        { source := .priorNeuron ⟨1, by decide⟩, weight := 1 }
        (by exact List.Mem.tail _ (List.Mem.head _)) (by decide)

def learnedExtendedCurrentIntermediateEdge
    (current : IndependentLearnedCurrentCase) :
    EffectiveReadsFrom
      (learnedDecodedExtendedArtifact.system.run
        current.input.toRequirementInput)
      (.neuronOutput learnedExtendedXorNeuron)
      (.neuronOutput learnedExtendedIntermediateNeuron) :=
  .executedEdge learnedExtendedIntermediateNeuron
    { source := .priorNeuron ⟨2, by decide⟩, weight := 1 }
    (by exact List.Mem.head _) (by cases current <;> decide)

def learnedExtendedCurrentPenultimateEdge
    (current : IndependentLearnedCurrentCase) :
    EffectiveReadsFrom
      (learnedDecodedExtendedArtifact.system.run
        current.input.toRequirementInput)
      (.neuronOutput learnedExtendedIntermediateNeuron)
      (.neuronOutput learnedExtendedPenultimateNeuron) :=
  .executedEdge learnedExtendedPenultimateNeuron
    { source := .priorNeuron ⟨4, by decide⟩, weight := 1 }
    (by exact List.Mem.head _) (by cases current <;> decide)

def learnedExtendedCurrentPrimaryEdge
    (current : IndependentLearnedCurrentCase) :
    EffectiveReadsFrom
      (learnedDecodedExtendedArtifact.system.run
        current.input.toRequirementInput)
      (.neuronOutput learnedExtendedPenultimateNeuron)
      (.neuronOutput learnedExtendedPrimaryNeuron) :=
  .executedEdge learnedExtendedPrimaryNeuron
    { source := .priorNeuron ⟨6, by decide⟩, weight := 1 }
    (by exact List.Mem.head _) (by cases current <;> decide)

def learnedExtendedCurrentPropagation
    (current : IndependentLearnedCurrentCase) :
    NontrivialExecutedChangePath (learnedExtendedCurrentIntervention current)
      (.neuronOutput learnedExtendedPrimaryNeuron) :=
  .step
    (.step
      (.step
        (.step
          (.step .origin (learnedExtendedCurrentInputEdge current)
            { different := by cases current <;> decide })
          (learnedExtendedCurrentXorEdge current)
            { different := by cases current <;> decide })
        (learnedExtendedCurrentIntermediateEdge current)
          { different := by cases current <;> decide })
      (learnedExtendedCurrentPenultimateEdge current)
        { different := by cases current <;> decide })
    (learnedExtendedCurrentPrimaryEdge current)
      { different := by cases current <;> decide }

def learnedExtendedCurrentRole
    (current : IndependentLearnedCurrentCase) :
    CausalRole learnedDecodedExtendedArtifact.system
      current.input.toRequirementInput
      (.receivedInput learnedExtendedRequirementPort) where
  intervention := learnedExtendedCurrentIntervention current
  focusExact := rfl
  output := learnedExtendedPrimaryOutputPort
  propagation := learnedExtendedCurrentPropagation current
  targetChange := { different := by cases current <;> decide }
  proposalChange :=
    { different := by
        cases current with
        | neither => change true ≠ false; decide
        | contextOnly => change false ≠ true; decide
        | requirementOnly => change false ≠ true; decide
        | both => change true ≠ false; decide }

/-! ## Separate executed roles for requirement and context

The complete-domain role above varies the received requirement.  The closed
state certificate additionally retains the distinct context path, so the two
received materials cannot be collapsed into one generic input witness. -/

def learnedInitialContextPort :
    Fin learnedDecodedInitialArtifact.system.inputCount := ⟨1, by decide⟩

def learnedInitialContextIntervention :
    Intervention
      (learnedDecodedInitialArtifact.system.run
        independentLearnedCertifiedInput) where
  focus := .input learnedInitialContextPort
  replacement := 1
  changesValue := by decide

def learnedInitialContextInputEdge :
    EffectiveReadsFrom
      (learnedDecodedInitialArtifact.system.run
        independentLearnedCertifiedInput)
      (.receivedInput learnedInitialContextPort)
      (.neuronOutput ⟨0, by decide⟩) :=
  .executedEdge ⟨0, by decide⟩
    { source := .receivedInput learnedInitialContextPort, weight := -2 }
    (by exact List.Mem.tail _ (List.Mem.head _))
    (by decide)

def learnedInitialContextPropagation :
    NontrivialExecutedChangePath learnedInitialContextIntervention
      (.neuronOutput learnedInitialPrimaryNeuron) :=
  .step
    (.step
      (.step .origin learnedInitialContextInputEdge
        { different := by decide })
      (learnedInitialCurrentXorEdge .requirementOnly)
        { different := by decide })
    (learnedInitialCurrentPrimaryEdge .requirementOnly)
      { different := by decide }

def learnedInitialContextRole :
    CausalRole learnedDecodedInitialArtifact.system
      independentLearnedCertifiedInput
      (.receivedInput learnedInitialContextPort) where
  intervention := learnedInitialContextIntervention
  focusExact := rfl
  output := learnedInitialPrimaryOutputPort
  propagation := learnedInitialContextPropagation
  targetChange := { different := by decide }
  proposalChange :=
    { different := by
        change false ≠ true
        decide }

def learnedAlignedContextPort :
    Fin learnedDecodedAlignedArtifact.system.inputCount := ⟨1, by decide⟩

def learnedAlignedContextIntervention :
    Intervention
      (learnedDecodedAlignedArtifact.system.run
        independentLearnedCertifiedInput) where
  focus := .input learnedAlignedContextPort
  replacement := 1
  changesValue := by decide

def learnedAlignedContextInputEdge :
    EffectiveReadsFrom
      (learnedDecodedAlignedArtifact.system.run
        independentLearnedCertifiedInput)
      (.receivedInput learnedAlignedContextPort)
      (.neuronOutput ⟨0, by decide⟩) :=
  .executedEdge ⟨0, by decide⟩
    { source := .receivedInput learnedAlignedContextPort, weight := -2 }
    (by exact List.Mem.tail _ (List.Mem.head _))
    (by decide)

def learnedAlignedContextPropagation :
    NontrivialExecutedChangePath learnedAlignedContextIntervention
      (.neuronOutput learnedAlignedPrimaryNeuron) :=
  .step
    (.step
      (.step
        (.step .origin learnedAlignedContextInputEdge
          { different := by decide })
        (learnedAlignedCurrentXorEdge .requirementOnly)
          { different := by decide })
      (learnedAlignedCurrentIntermediateEdge .requirementOnly)
        { different := by decide })
    (learnedAlignedCurrentPrimaryEdge .requirementOnly)
      { different := by decide }

def learnedAlignedContextRole :
    CausalRole learnedDecodedAlignedArtifact.system
      independentLearnedCertifiedInput
      (.receivedInput learnedAlignedContextPort) where
  intervention := learnedAlignedContextIntervention
  focusExact := rfl
  output := learnedAlignedPrimaryOutputPort
  propagation := learnedAlignedContextPropagation
  targetChange := { different := by decide }
  proposalChange :=
    { different := by
        change false ≠ true
        decide }

def learnedExtendedContextPort :
    Fin learnedDecodedExtendedArtifact.system.inputCount := ⟨1, by decide⟩

def learnedExtendedContextIntervention :
    Intervention
      (learnedDecodedExtendedArtifact.system.run
        independentLearnedCertifiedInput) where
  focus := .input learnedExtendedContextPort
  replacement := 1
  changesValue := by decide

def learnedExtendedContextInputEdge :
    EffectiveReadsFrom
      (learnedDecodedExtendedArtifact.system.run
        independentLearnedCertifiedInput)
      (.receivedInput learnedExtendedContextPort)
      (.neuronOutput ⟨0, by decide⟩) :=
  .executedEdge ⟨0, by decide⟩
    { source := .receivedInput learnedExtendedContextPort, weight := -2 }
    (by exact List.Mem.tail _ (List.Mem.head _)) (by decide)

def learnedExtendedContextPropagation :
    NontrivialExecutedChangePath learnedExtendedContextIntervention
      (.neuronOutput learnedExtendedPrimaryNeuron) :=
  .step
    (.step
      (.step
        (.step
          (.step .origin learnedExtendedContextInputEdge
            { different := by decide })
          (learnedExtendedCurrentXorEdge .requirementOnly)
            { different := by decide })
        (learnedExtendedCurrentIntermediateEdge .requirementOnly)
          { different := by decide })
      (learnedExtendedCurrentPenultimateEdge .requirementOnly)
        { different := by decide })
    (learnedExtendedCurrentPrimaryEdge .requirementOnly)
      { different := by decide }

def learnedExtendedContextRole :
    CausalRole learnedDecodedExtendedArtifact.system
      independentLearnedCertifiedInput
      (.receivedInput learnedExtendedContextPort) where
  intervention := learnedExtendedContextIntervention
  focusExact := rfl
  output := learnedExtendedPrimaryOutputPort
  propagation := learnedExtendedContextPropagation
  targetChange := { different := by decide }
  proposalChange :=
    { different := by
        change false ≠ true
        decide }

/-! ## Executed action, effect, and calculated successor -/

theorem learnedFin_ne_of_val_ne {size : Nat} {left right : Fin size}
    (different : left.val ≠ right.val) : left ≠ right := by
  intro same
  exact different (congrArg Fin.val same)

def learnedInitialCausalWitness :
    LearnedExecutedCausalWitness learnedInitialState :=
  { requirementPort := learnedInitialRequirementPort
    requirementRole := learnedInitialCurrentRole .requirementOnly
    contextPort := learnedInitialContextPort
    contextRole := learnedInitialContextRole
    authorizationPort := learnedInitialAuthorizationPort
    authorizationRole := learnedInitialAuthorizationRole
    requirementContextDistinct :=
      learnedFin_ne_of_val_ne (by decide)
    requirementAuthorizationDistinct :=
      learnedFin_ne_of_val_ne (by decide)
    contextAuthorizationDistinct :=
      learnedFin_ne_of_val_ne (by decide) }

def learnedInitialAuthorizationWitness :
    LearnedAuthorizationWitness learnedInitialState where
  authorizationPort := learnedInitialAuthorizationPort
  authorizationRole := learnedInitialAuthorizationRole
  consumed := by rfl

def learnedInitialProposalPreservation :
    LearnedProposalPreservation learnedInitialState where
  admittedIntent := .preserveAuthorizedBehavior
  proposalExact := by rfl

def learnedInitialAction : LearnedActionWitness learnedInitialState :=
  executeLearnedAction learnedInitialState learnedInitialProposalPreservation
    learnedInitialCausalWitness learnedInitialAuthorizationWitness rfl

def learnedInitialEffect : LearnedEffectWitness learnedInitialState :=
  produceLearnedEffect learnedInitialAction

/-- The target program and exact next input are combined with the memory of
the preceding state.  This is the state from which the installing action is
actually executed; its memory is not read from the received target artifact. -/
def learnedAlignedActionSourceStateFor (memory : Agent.Memory) :
    ReconfiguredExecutionState independentLearnedRequirementFamily :=
  { system := learnedDecodedAlignedArtifact.system
    input := independentLearnedCertifiedInput
    memory := memory }

def learnedAlignedActionSourceState :
    ReconfiguredExecutionState independentLearnedRequirementFamily :=
  learnedAlignedActionSourceStateFor learnedInitialState.memory

def learnedAlignedActionSourceCausalWitnessFor (memory : Agent.Memory) :
    LearnedExecutedCausalWitness
      (learnedAlignedActionSourceStateFor memory) :=
  { requirementPort := learnedAlignedRequirementPort
    requirementRole := learnedAlignedCurrentRole .requirementOnly
    contextPort := learnedAlignedContextPort
    contextRole := learnedAlignedContextRole
    authorizationPort := learnedAlignedAuthorizationPort
    authorizationRole := learnedAlignedAuthorizationRole
    requirementContextDistinct :=
      learnedFin_ne_of_val_ne (by decide)
    requirementAuthorizationDistinct :=
      learnedFin_ne_of_val_ne (by decide)
    contextAuthorizationDistinct :=
      learnedFin_ne_of_val_ne (by decide) }

def learnedAlignedActionSourceCausalWitness :
    LearnedExecutedCausalWitness learnedAlignedActionSourceState :=
  learnedAlignedActionSourceCausalWitnessFor learnedInitialState.memory

def learnedAlignedActionAuthorizationWitnessFor (memory : Agent.Memory) :
    LearnedAuthorizationWitness
      (learnedAlignedActionSourceStateFor memory) where
  authorizationPort := learnedAlignedAuthorizationPort
  authorizationRole := learnedAlignedAuthorizationRole
  consumed := alignedUpdate_consumes_authorization

def learnedAlignedActionAuthorizationWitness :
    LearnedAuthorizationWitness learnedAlignedActionSourceState :=
  learnedAlignedActionAuthorizationWitnessFor learnedInitialState.memory

def learnedAlignedInstallingProposalPreservationFor (memory : Agent.Memory) :
    LearnedProposalPreservation
      (learnedAlignedActionSourceStateFor memory) where
  admittedIntent := .preserveAuthorizedBehavior
  proposalExact := by rfl

def learnedAlignedInstallingProposalPreservation :
    LearnedProposalPreservation learnedAlignedActionSourceState :=
  learnedAlignedInstallingProposalPreservationFor learnedInitialState.memory

def learnedAlignedInstallingActionFor (memory : Agent.Memory) :
    LearnedActionWitness (learnedAlignedActionSourceStateFor memory) :=
  executeLearnedAction (learnedAlignedActionSourceStateFor memory)
    (learnedAlignedInstallingProposalPreservationFor memory)
    (learnedAlignedActionSourceCausalWitnessFor memory)
    (learnedAlignedActionAuthorizationWitnessFor memory) rfl

def learnedAlignedInstallingAction :
    LearnedActionWitness learnedAlignedActionSourceState :=
  learnedAlignedInstallingActionFor learnedInitialState.memory

def learnedAlignedInstallingEffectFor (memory : Agent.Memory) :
    LearnedEffectWitness (learnedAlignedActionSourceStateFor memory) :=
  produceLearnedEffect (learnedAlignedInstallingActionFor memory)

def learnedAlignedInstallingEffect :
    LearnedEffectWitness learnedAlignedActionSourceState :=
  learnedAlignedInstallingEffectFor learnedInitialState.memory

def learnedAlignedInstalledStateFor (memory : Agent.Memory) :
    ReconfiguredExecutionState independentLearnedRequirementFamily :=
  (learnedAlignedInstallingEffectFor memory).targetState

/-- The installed state is the successor produced by the installing effect.
In particular its memory is not a fixed copy of `publicActionMemory`. -/
def learnedAlignedState :
    ReconfiguredExecutionState independentLearnedRequirementFamily :=
  learnedAlignedInstalledStateFor learnedInitialState.memory

def learnedAlignedCausalWitness :
    LearnedExecutedCausalWitness learnedAlignedState :=
  { requirementPort := learnedAlignedRequirementPort
    requirementRole := learnedAlignedCurrentRole .requirementOnly
    contextPort := learnedAlignedContextPort
    contextRole := learnedAlignedContextRole
    authorizationPort := learnedAlignedAuthorizationPort
    authorizationRole := learnedAlignedAuthorizationRole
    requirementContextDistinct :=
      learnedFin_ne_of_val_ne (by decide)
    requirementAuthorizationDistinct :=
      learnedFin_ne_of_val_ne (by decide)
    contextAuthorizationDistinct :=
      learnedFin_ne_of_val_ne (by decide) }

def learnedAlignedAuthorizationWitness :
    LearnedAuthorizationWitness learnedAlignedState where
  authorizationPort := learnedAlignedAuthorizationPort
  authorizationRole := learnedAlignedAuthorizationRole
  consumed := alignedUpdate_consumes_authorization

def learnedAlignedProposalPreservation :
    LearnedProposalPreservation learnedAlignedState where
  admittedIntent := .preserveAuthorizedBehavior
  proposalExact := by rfl

def learnedAlignedAction : LearnedActionWitness learnedAlignedState :=
  executeLearnedAction learnedAlignedState learnedAlignedProposalPreservation
    learnedAlignedCausalWitness learnedAlignedAuthorizationWitness rfl

def learnedAlignedEffect : LearnedEffectWitness learnedAlignedState :=
  produceLearnedEffect learnedAlignedAction

theorem learnedAlignedState_memory_is_produced :
    learnedAlignedState.memory = learnedAlignedInstallingAction.result.1 :=
  rfl

theorem learnedAlignedInstallingEffect_exact :
    (learnedAlignedInstallingEffect.successor,
      learnedAlignedInstallingEffect.event) =
      Agent.executeInput learnedInitialState.memory
        learnedAlignedInstallingAction.request :=
  learnedAlignedInstallingEffect.effect_exact

/-! ## Executed installation of the second learned successor -/

def learnedExtendedActionSourceStateFor (memory : Agent.Memory) :
    ReconfiguredExecutionState independentLearnedRequirementFamily :=
  { system := learnedDecodedExtendedArtifact.system
    input := independentLearnedCertifiedInput
    memory := memory }

def learnedExtendedActionSourceCausalWitnessFor (memory : Agent.Memory) :
    LearnedExecutedCausalWitness
      (learnedExtendedActionSourceStateFor memory) :=
  { requirementPort := learnedExtendedRequirementPort
    requirementRole := learnedExtendedCurrentRole .requirementOnly
    contextPort := learnedExtendedContextPort
    contextRole := learnedExtendedContextRole
    authorizationPort := learnedExtendedAuthorizationPort
    authorizationRole := learnedExtendedAuthorizationRole
    requirementContextDistinct := learnedFin_ne_of_val_ne (by decide)
    requirementAuthorizationDistinct := learnedFin_ne_of_val_ne (by decide)
    contextAuthorizationDistinct := learnedFin_ne_of_val_ne (by decide) }

def learnedExtendedActionAuthorizationWitnessFor (memory : Agent.Memory) :
    LearnedAuthorizationWitness
      (learnedExtendedActionSourceStateFor memory) where
  authorizationPort := learnedExtendedAuthorizationPort
  authorizationRole := learnedExtendedAuthorizationRole
  consumed := by rfl

def learnedExtendedInstallingProposalPreservationFor (memory : Agent.Memory) :
    LearnedProposalPreservation
      (learnedExtendedActionSourceStateFor memory) where
  admittedIntent := .preserveAuthorizedBehavior
  proposalExact := by rfl

def learnedExtendedInstallingActionFor (memory : Agent.Memory) :
    LearnedActionWitness (learnedExtendedActionSourceStateFor memory) :=
  executeLearnedAction (learnedExtendedActionSourceStateFor memory)
    (learnedExtendedInstallingProposalPreservationFor memory)
    (learnedExtendedActionSourceCausalWitnessFor memory)
    (learnedExtendedActionAuthorizationWitnessFor memory) rfl

def learnedExtendedInstallingEffectFor (memory : Agent.Memory) :
    LearnedEffectWitness (learnedExtendedActionSourceStateFor memory) :=
  produceLearnedEffect (learnedExtendedInstallingActionFor memory)

def learnedExtendedInstalledStateFor (memory : Agent.Memory) :
    ReconfiguredExecutionState independentLearnedRequirementFamily :=
  (learnedExtendedInstallingEffectFor memory).targetState

/-- The second installed state consumes the memory produced by the first
accepted transition.  It cannot be reconstructed from the initial source. -/
def learnedExtendedState :
    ReconfiguredExecutionState independentLearnedRequirementFamily :=
  learnedExtendedInstalledStateFor learnedAlignedState.memory

def learnedExtendedCausalWitness :
    LearnedExecutedCausalWitness learnedExtendedState :=
  { requirementPort := learnedExtendedRequirementPort
    requirementRole := learnedExtendedCurrentRole .requirementOnly
    contextPort := learnedExtendedContextPort
    contextRole := learnedExtendedContextRole
    authorizationPort := learnedExtendedAuthorizationPort
    authorizationRole := learnedExtendedAuthorizationRole
    requirementContextDistinct := learnedFin_ne_of_val_ne (by decide)
    requirementAuthorizationDistinct := learnedFin_ne_of_val_ne (by decide)
    contextAuthorizationDistinct := learnedFin_ne_of_val_ne (by decide) }

def learnedExtendedAuthorizationWitness :
    LearnedAuthorizationWitness learnedExtendedState where
  authorizationPort := learnedExtendedAuthorizationPort
  authorizationRole := learnedExtendedAuthorizationRole
  consumed := by rfl

def learnedExtendedProposalPreservation :
    LearnedProposalPreservation learnedExtendedState where
  admittedIntent := .preserveAuthorizedBehavior
  proposalExact := by rfl

def learnedExtendedAction : LearnedActionWitness learnedExtendedState :=
  executeLearnedAction learnedExtendedState learnedExtendedProposalPreservation
    learnedExtendedCausalWitness learnedExtendedAuthorizationWitness rfl

def learnedExtendedEffect : LearnedEffectWitness learnedExtendedState :=
  produceLearnedEffect learnedExtendedAction

theorem learnedExtendedState_memory_is_produced :
    learnedExtendedState.memory =
      (learnedExtendedInstallingActionFor learnedAlignedState.memory).result.1 :=
  rfl

theorem learnedExtendedInstallingEffect_exact :
    ((learnedExtendedInstallingEffectFor learnedAlignedState.memory).successor,
      (learnedExtendedInstallingEffectFor learnedAlignedState.memory).event) =
      Agent.executeInput learnedAlignedState.memory
        (learnedExtendedInstallingActionFor learnedAlignedState.memory).request :=
  (learnedExtendedInstallingEffectFor learnedAlignedState.memory).effect_exact

/-! ## Stable names, finite causal bases, and state fragments -/

def learnedInitialSerializedNaming : SerializedStableArtifactNaming :=
  { inputKeys := [0, 1, 2]
    neuronKeys := [10, 11, 12, 13, 14, 15]
    outputKeys := [20, 21, 22] }

def learnedAlignedSerializedNaming : SerializedStableArtifactNaming :=
  { inputKeys := [0, 1, 2]
    neuronKeys := [110, 111, 112, 113, 114, 115, 116]
    outputKeys := [120, 121, 122] }

def learnedExtendedSerializedNaming : SerializedStableArtifactNaming :=
  { inputKeys := [0, 1, 2]
    neuronKeys := [110, 111, 112, 113, 114, 115, 116, 117]
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

def learnedDecodedExtendedStableNaming :
    DecodedStableArtifactNaming learnedDecodedExtendedArtifact
      learnedExtendedSerializedNaming :=
  match exact : decodeStableArtifactNaming learnedDecodedExtendedArtifact
      learnedExtendedSerializedNaming with
  | .ok naming => naming
  | .error _ => False.elim (by cases exact)

def learnedInitialStableNaming :
    StableArtifactNaming learnedDecodedInitialArtifact :=
  learnedDecodedInitialStableNaming.naming

def learnedAlignedStableNaming :
    StableArtifactNaming learnedDecodedAlignedArtifact :=
  learnedDecodedAlignedStableNaming.naming

def learnedExtendedStableNaming :
    StableArtifactNaming learnedDecodedExtendedArtifact :=
  learnedDecodedExtendedStableNaming.naming

/-- A second admitted target version.  Its stable serials differ at every
location while its `Fin` locations and executable network remain unchanged.
It is the extended-cone control against the ordinary aligned update, whose
unchanged source nodes retain their constitutive identities. -/
def learnedRenamedSerializedNaming : SerializedStableArtifactNaming :=
  { inputKeys := [1100, 1101, 1102]
    neuronKeys := [1110, 1111, 1112, 1113, 1114, 1115, 1116]
    outputKeys := [1120, 1121, 1122] }

def learnedDecodedRenamedStableNaming :
    DecodedStableArtifactNaming learnedDecodedAlignedArtifact
      learnedRenamedSerializedNaming :=
  match exact : decodeStableArtifactNaming learnedDecodedAlignedArtifact
      learnedRenamedSerializedNaming with
  | .ok naming => naming
  | .error _ => False.elim (by cases exact)

def learnedRenamedStableNaming :
    StableArtifactNaming learnedDecodedAlignedArtifact :=
  learnedDecodedRenamedStableNaming.naming

/-- Stable target identities admitted by this executable learned instance.
The index is the exact proof-free naming received in the update. -/
inductive LearnedAdmittedStableNaming :
    SerializedStableArtifactNaming -> Type 4 where
  | aligned : LearnedAdmittedStableNaming learnedAlignedSerializedNaming
  | renamed : LearnedAdmittedStableNaming learnedRenamedSerializedNaming

def LearnedAdmittedStableNaming.naming
    {source : SerializedStableArtifactNaming} :
    LearnedAdmittedStableNaming source ->
      StableArtifactNaming learnedDecodedAlignedArtifact
  | .aligned => learnedAlignedStableNaming
  | .renamed => learnedRenamedStableNaming

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
  [0, 1]

def learnedAlignedCausalReplacementsFor
    (naming : StableArtifactNaming learnedDecodedAlignedArtifact)
    (_node : StableNodeId naming) : List Activation :=
  [0, 1]

def learnedAlignedCausalReplacements
    (_node : StableNodeId learnedAlignedStableNaming) : List Activation :=
  learnedAlignedCausalReplacementsFor learnedAlignedStableNaming _node

def learnedExtendedCausalReplacements
    (_node : StableNodeId learnedExtendedStableNaming) : List Activation :=
  [0, 1]

def learnedInitialCausalCoverage : CoversDeclaredCausalCondition
    learnedDecodedInitialArtifact learnedInitialStableNaming
      learnedInitialCausalReplacements := by
  intro input declared
  cases declared with
  | head =>
      exact
        { node := .receivedInput learnedInitialRequirementPort
          role := learnedInitialCurrentRole .neither
          replacementListed := .tail .head
          replacementDeclared := .tail .head }
  | tail later =>
      cases later with
      | head =>
          exact
            { node := .receivedInput learnedInitialRequirementPort
              role := learnedInitialCurrentRole .contextOnly
              replacementListed := .tail .head
              replacementDeclared := .tail .head }
      | tail later =>
          cases later with
          | head =>
              exact
                { node := .receivedInput learnedInitialRequirementPort
                  role := learnedInitialCurrentRole .requirementOnly
                  replacementListed := .head
                  replacementDeclared := .head }
          | tail later =>
              cases later with
              | head =>
                  exact
                    { node := .receivedInput learnedInitialRequirementPort
                      role := learnedInitialCurrentRole .both
                      replacementListed := .head
                      replacementDeclared := .head }
              | tail impossible => nomatch impossible

def learnedAlignedCausalCoverageFor
    (naming : StableArtifactNaming learnedDecodedAlignedArtifact) :
    CoversDeclaredCausalCondition learnedDecodedAlignedArtifact naming
      (learnedAlignedCausalReplacementsFor naming) := by
  intro input declared
  cases declared with
  | head =>
      exact
        { node := .receivedInput learnedAlignedRequirementPort
          role := learnedAlignedCurrentRole .neither
          replacementListed := .tail .head
          replacementDeclared := .tail .head }
  | tail later =>
      cases later with
      | head =>
          exact
            { node := .receivedInput learnedAlignedRequirementPort
              role := learnedAlignedCurrentRole .contextOnly
              replacementListed := .tail .head
              replacementDeclared := .tail .head }
      | tail later =>
          cases later with
          | head =>
              exact
                { node := .receivedInput learnedAlignedRequirementPort
                  role := learnedAlignedCurrentRole .requirementOnly
                  replacementListed := .head
                  replacementDeclared := .head }
          | tail later =>
              cases later with
              | head =>
                  exact
                    { node := .receivedInput learnedAlignedRequirementPort
                      role := learnedAlignedCurrentRole .both
                      replacementListed := .head
                      replacementDeclared := .head }
              | tail impossible => nomatch impossible

def learnedAlignedCausalCoverage : CoversDeclaredCausalCondition
    learnedDecodedAlignedArtifact learnedAlignedStableNaming
      learnedAlignedCausalReplacements :=
  learnedAlignedCausalCoverageFor learnedAlignedStableNaming

def learnedExtendedCausalCoverage : CoversDeclaredCausalCondition
    learnedDecodedExtendedArtifact learnedExtendedStableNaming
      learnedExtendedCausalReplacements := by
  intro input declared
  cases declared with
  | head =>
      exact
        { node := .receivedInput learnedExtendedRequirementPort
          role := learnedExtendedCurrentRole .neither
          replacementListed := .tail .head
          replacementDeclared := .tail .head }
  | tail later =>
      cases later with
      | head =>
          exact
            { node := .receivedInput learnedExtendedRequirementPort
              role := learnedExtendedCurrentRole .contextOnly
              replacementListed := .tail .head
              replacementDeclared := .tail .head }
      | tail later =>
          cases later with
          | head =>
              exact
                { node := .receivedInput learnedExtendedRequirementPort
                  role := learnedExtendedCurrentRole .requirementOnly
                  replacementListed := .head
                  replacementDeclared := .head }
          | tail later =>
              cases later with
              | head =>
                  exact
                    { node := .receivedInput learnedExtendedRequirementPort
                      role := learnedExtendedCurrentRole .both
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

def learnedAlignedFiniteCausalBasisFor
    (naming : StableArtifactNaming learnedDecodedAlignedArtifact) :
    FiniteCausalBasis LearnedAlignedOperationalContract
      learnedDecodedAlignedArtifact where
  currentInputs := independentLearnedDeclaredInputs
  currentInputsComplete := fun _ witness => witness
  inputEquality := independentLearnedRequirementInputEquality
  naming := naming
  replacements := learnedAlignedCausalReplacementsFor naming
  replacementCoverage := learnedAlignedCausalCoverageFor naming
  replacementEquality := learnedActivationEquality

def learnedAlignedFiniteCausalBasis : FiniteCausalBasis
    LearnedAlignedOperationalContract learnedDecodedAlignedArtifact :=
  learnedAlignedFiniteCausalBasisFor learnedAlignedStableNaming

def learnedExtendedFiniteCausalBasis : FiniteCausalBasis
    LearnedExtendedOperationalContract learnedDecodedExtendedArtifact where
  currentInputs := independentLearnedDeclaredInputs
  currentInputsComplete := fun _ witness => witness
  inputEquality := independentLearnedRequirementInputEquality
  naming := learnedExtendedStableNaming
  replacements := learnedExtendedCausalReplacements
  replacementCoverage := learnedExtendedCausalCoverage
  replacementEquality := learnedActivationEquality

def learnedInitialStateFragments : StateCertificateFragments
    LearnedInitialOperationalContract learnedDecodedInitialArtifact
      learnedInitialState :=
  { structural :=
      { basis := learnedInitialFiniteCausalBasis
        systemExact := rfl
        inputDeclared := .tail (.tail .head)
        observations := stableStructuralObservationSnapshot
          learnedInitialFiniteCausalBasis.naming
        observationsExact := rfl }
    requirement := { witness := { inputExact := rfl } }
    causal := { witness := learnedInitialCausalWitness }
    proposalAction := { witness := learnedInitialAction }
    authorization := { witness := learnedInitialAuthorizationWitness }
    effect := { witness := learnedInitialEffect }
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

def learnedAlignedStateFragmentsFor
    (naming : StableArtifactNaming learnedDecodedAlignedArtifact) :
    StateCertificateFragments LearnedAlignedOperationalContract
      learnedDecodedAlignedArtifact learnedAlignedState :=
  { structural :=
      { basis := learnedAlignedFiniteCausalBasisFor naming
        systemExact := rfl
        inputDeclared := .tail (.tail .head)
        observations := stableStructuralObservationSnapshot
          naming
        observationsExact := rfl }
    requirement := { witness := { inputExact := rfl } }
    causal := { witness := learnedAlignedCausalWitness }
    proposalAction := { witness := learnedAlignedAction }
    authorization := { witness := learnedAlignedAuthorizationWitness }
    effect := { witness := learnedAlignedEffect }
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

def learnedAlignedStateFragments : StateCertificateFragments
    LearnedAlignedOperationalContract learnedDecodedAlignedArtifact
      learnedAlignedState :=
  learnedAlignedStateFragmentsFor learnedAlignedStableNaming

def learnedExtendedStateFragments : StateCertificateFragments
    LearnedExtendedOperationalContract learnedDecodedExtendedArtifact
      learnedExtendedState :=
  { structural :=
      { basis := learnedExtendedFiniteCausalBasis
        systemExact := rfl
        inputDeclared := .tail (.tail .head)
        observations := stableStructuralObservationSnapshot
          learnedExtendedStableNaming
        observationsExact := rfl }
    requirement := { witness := { inputExact := rfl } }
    causal := { witness := learnedExtendedCausalWitness }
    proposalAction := { witness := learnedExtendedAction }
    authorization := { witness := learnedExtendedAuthorizationWitness }
    effect := { witness := learnedExtendedEffect }
    historical := { witness := { exact := by rfl } }
    futures :=
      { covered := fun requests =>
          { outcome := independentLearnedFutureContract.outcome
              { network :=
                  (LearnedExtendedOperationalContract.coveredFutureAt
                    learnedExtendedState requests).source }
              ((LearnedExtendedOperationalContract.coveredFutureAt
                learnedExtendedState requests).requests.map fun input =>
                  { input := input })
            outcomeExact := rfl }
        realization := independentLearnedCoveredFutureRealization .extended } }

/-! ## Learned meta-contract and exact transition -/

inductive LearnedContractAdmission : LearnedOperationalContract -> Type where
  | initial : LearnedContractAdmission .initial
  | aligned : LearnedContractAdmission .aligned
  | extended : LearnedContractAdmission .extended

inductive LearnedContractTransitionPermission :
    LearnedOperationalContract -> LearnedOperationalContract -> Type where
  | installAligned : LearnedContractTransitionPermission .initial .aligned
  | installExtended : LearnedContractTransitionPermission .aligned .extended

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
    (_current next : LearnedOperationalContract)
    (_obligation : LearnedRecheckObligation) : Type 3 :=
  match next with
  | .initial => LearnedAuthorizationWitness learnedInitialState
  | .aligned => LearnedAuthorizationWitness learnedAlignedState
  | .extended => LearnedAuthorizationWitness learnedExtendedState

inductive LearnedExecutedStateTransition :
    {current next : LearnedOperationalContract} ->
      (permission : LearnedContractTransitionPermission current next) ->
      (currentState : ReconfiguredExecutionState
        (learnedOperationalContract current).family) ->
      (nextState : ReconfiguredExecutionState
        (learnedOperationalContract next).family) -> Type 4 where
  | executed
      (currentState : ReconfiguredExecutionState
        independentLearnedRequirementFamily)
      (installingAction : LearnedActionWitness
        (learnedAlignedActionSourceStateFor currentState.memory))
      (installingActionExact : installingAction =
        learnedAlignedInstallingActionFor currentState.memory)
      (installingEffect : LearnedEffectWitness
        (learnedAlignedActionSourceStateFor currentState.memory))
      (installingEffectExact : installingEffect =
        produceLearnedEffect installingAction) :
      LearnedExecutedStateTransition
        LearnedContractTransitionPermission.installAligned
        currentState installingEffect.targetState
  | executedExtended
      (currentState : ReconfiguredExecutionState
        independentLearnedRequirementFamily)
      (installingAction : LearnedActionWitness
        (learnedExtendedActionSourceStateFor currentState.memory))
      (installingActionExact : installingAction =
        learnedExtendedInstallingActionFor currentState.memory)
      (installingEffect : LearnedEffectWitness
        (learnedExtendedActionSourceStateFor currentState.memory))
      (installingEffectExact : installingEffect =
        produceLearnedEffect installingAction) :
      LearnedExecutedStateTransition
        LearnedContractTransitionPermission.installExtended
        currentState installingEffect.targetState

def executeLearnedAlignedStateTransition :
    LearnedExecutedStateTransition
      LearnedContractTransitionPermission.installAligned
      learnedInitialState learnedAlignedState :=
  .executed learnedInitialState learnedAlignedInstallingAction rfl
    learnedAlignedInstallingEffect rfl

def executeLearnedExtendedStateTransition :
    LearnedExecutedStateTransition
      LearnedContractTransitionPermission.installExtended
      learnedAlignedState learnedExtendedState :=
  .executedExtended learnedAlignedState
    (learnedExtendedInstallingActionFor learnedAlignedState.memory) rfl
    (learnedExtendedInstallingEffectFor learnedAlignedState.memory) rfl

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
    cases permission with
    | installAligned => exact learnedAlignedAuthorizationWitness
    | installExtended => exact learnedExtendedAuthorizationWitness
  ExecutedStateTransition := LearnedExecutedStateTransition

def learnedOperationalTransition : OperationalContractTransition
    learnedConstitutiveMetaContract .initial .aligned :=
  certifyOperationalContractTransition .initial .aligned
    .installAligned

def learnedExtendedOperationalTransition : OperationalContractTransition
    learnedConstitutiveMetaContract .aligned .extended :=
  certifyOperationalContractTransition .aligned .extended
    .installExtended

/-! ## Learned transition production shared by full and incremental checking -/

inductive LearnedTransitionMaterial :
    LearnedOperationalContract -> LearnedOperationalContract -> Type 3 where
  | installAligned : LearnedTransitionMaterial .initial .aligned
  | installExtended : LearnedTransitionMaterial .aligned .extended

structure LearnedTransitionProductionData
    (current : CheckedAgent learnedConstitutiveMetaContract .initial) : Type 3 where
  private mk ::
  action : LearnedActionWitness
    (learnedAlignedActionSourceStateFor current.state.memory)
  actionExact : action =
    learnedAlignedInstallingActionFor current.state.memory
  effect : LearnedEffectWitness
    (learnedAlignedActionSourceStateFor current.state.memory)
  effectExact : effect = produceLearnedEffect action

structure LearnedExtendedTransitionProductionData
    (current : CheckedAgent learnedConstitutiveMetaContract .aligned) : Type 3 where
  private mk ::
  action : LearnedActionWitness
    (learnedExtendedActionSourceStateFor current.state.memory)
  actionExact : action =
    learnedExtendedInstallingActionFor current.state.memory
  effect : LearnedEffectWitness
    (learnedExtendedActionSourceStateFor current.state.memory)
  effectExact : effect = produceLearnedEffect action

def learnedTransitionProductionData
    {currentContract nextContract : LearnedOperationalContract}
    (current : CheckedAgent learnedConstitutiveMetaContract currentContract)
    (_transition : OperationalContractTransition learnedConstitutiveMetaContract
      currentContract nextContract) :
    LearnedTransitionMaterial currentContract nextContract -> Type 3
  | .installAligned => LearnedTransitionProductionData current
  | .installExtended => LearnedExtendedTransitionProductionData current

def produceLearnedTransitionData
    {currentContract nextContract : LearnedOperationalContract}
    (current : CheckedAgent learnedConstitutiveMetaContract currentContract)
    (_transition : OperationalContractTransition learnedConstitutiveMetaContract
      currentContract nextContract) :
    (material : LearnedTransitionMaterial currentContract nextContract) ->
      learnedTransitionProductionData current _transition material := by
  intro material
  cases material
  · exact
      .mk (learnedAlignedInstallingActionFor current.state.memory) rfl
        (learnedAlignedInstallingEffectFor current.state.memory) rfl
  · exact
      .mk (learnedExtendedInstallingActionFor current.state.memory) rfl
        (learnedExtendedInstallingEffectFor current.state.memory) rfl

def learnedProducedTransitionTarget
    {currentContract nextContract : LearnedOperationalContract}
    (current : CheckedAgent learnedConstitutiveMetaContract currentContract)
    (transition : OperationalContractTransition learnedConstitutiveMetaContract
      currentContract nextContract)
    (material : LearnedTransitionMaterial currentContract nextContract)
    (production : learnedTransitionProductionData current transition material) :
    ReconfiguredExecutionState
      (learnedOperationalContract nextContract).family := by
  cases material with
  | installAligned => exact production.effect.targetState
  | installExtended => exact production.effect.targetState

def learnedProducedTransitionExecution
    {currentContract nextContract : LearnedOperationalContract}
    (current : CheckedAgent learnedConstitutiveMetaContract currentContract)
    (transition : OperationalContractTransition learnedConstitutiveMetaContract
      currentContract nextContract)
    (material : LearnedTransitionMaterial currentContract nextContract)
    (production : learnedTransitionProductionData current transition material) :
    LearnedExecutedStateTransition transition.permission current.state
      (learnedProducedTransitionTarget current transition material
        production) := by
  cases material with
  | installAligned =>
      cases transition.permission
      exact .executed current.state production.action production.actionExact
        production.effect production.effectExact
  | installExtended =>
      cases transition.permission
      exact .executedExtended current.state production.action
        production.actionExact production.effect production.effectExact

def learnedTransitionProductionKernel :
    TransitionProductionKernel learnedConstitutiveMetaContract where
  Material := LearnedTransitionMaterial
  Production := learnedTransitionProductionData
  produce := produceLearnedTransitionData
  targetOf := learnedProducedTransitionTarget
  execution := learnedProducedTransitionExecution

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

def learnedReceivedExtendedArtifact : LearnedReceivedArtifact :=
  { contract := .extended
    network := independentLearnedSecondSuccessorNetwork
    stableNaming := learnedExtendedSerializedNaming }

def learnedReceivedRenamedArtifact : LearnedReceivedArtifact :=
  { contract := .aligned
    network := independentLearnedFirstSuccessorNetwork
    stableNaming := learnedRenamedSerializedNaming }

def learnedReceivedBypassArtifact : LearnedReceivedArtifact :=
  { contract := .aligned
    network := independentLearnedBypassNetwork
    stableNaming := learnedAlignedSerializedNaming }

/-- The learned checker uses the same proof-free serialized update envelope as
the public checker.  Only its contract code, next-input code and intention
code are instance-specific. -/
abbrev LearnedSerializedConstitutiveUpdate :=
  SerializedConstitutiveUpdate
    (ContractTransitionRequest learnedConstitutiveMetaContract)
    IndependentLearnedRequirementInput IndependentLearnedUpdateIntent

def IndependentLearnedUpdateCandidate.toSerializedUpdate
    (candidate : IndependentLearnedUpdateCandidate) :
    LearnedSerializedConstitutiveUpdate :=
  { transition := { current := .initial, next := .aligned }
    targetNetwork := candidate.targetArtifact
    targetStableNaming := learnedAlignedSerializedNaming
    nextInput := independentLearnedCertifiedInput
    intent := candidate.intent }

def learnedAlignedSerializedUpdate : LearnedSerializedConstitutiveUpdate :=
  alignedUpdate.toSerializedUpdate

def learnedExtendedSerializedUpdate : LearnedSerializedConstitutiveUpdate :=
  { transition := { current := .aligned, next := .extended }
    targetNetwork := independentLearnedSecondSuccessorNetwork
    targetStableNaming := learnedExtendedSerializedNaming
    nextInput := independentLearnedCertifiedInput
    intent := .preserveAuthorizedBehavior }

def learnedRenamedSerializedUpdate : LearnedSerializedConstitutiveUpdate :=
  { learnedAlignedSerializedUpdate with
    targetStableNaming := learnedRenamedSerializedNaming }

/-- The complete admitted naming domain of the learned update.  The received
network, transition, input and intent remain those of the same aligned update;
only the proof-free stable naming varies through an admitted constructor. -/
def learnedSerializedUpdateForAdmittedNaming
    {source : SerializedStableArtifactNaming}
    (_admitted : LearnedAdmittedStableNaming source) :
    LearnedSerializedConstitutiveUpdate :=
  { learnedAlignedSerializedUpdate with targetStableNaming := source }

def learnedBypassSerializedUpdate : LearnedSerializedConstitutiveUpdate :=
  bypassUpdate.toSerializedUpdate

def LearnedSerializedConstitutiveUpdate.targetReceivedArtifact
    (source : LearnedSerializedConstitutiveUpdate) :
    LearnedReceivedArtifact :=
  { contract := source.transition.next
    network := source.targetNetwork
    stableNaming := source.targetStableNaming }

theorem learnedAlignedSerializedUpdate_target_exact :
    learnedAlignedSerializedUpdate.targetReceivedArtifact =
      learnedReceivedAlignedArtifact := by
  rfl

theorem learnedExtendedSerializedUpdate_target_exact :
    learnedExtendedSerializedUpdate.targetReceivedArtifact =
      learnedReceivedExtendedArtifact := by
  rfl

theorem learnedRenamedSerializedUpdate_target_exact :
    learnedRenamedSerializedUpdate.targetReceivedArtifact =
      learnedReceivedRenamedArtifact := by
  rfl

theorem learnedBypassSerializedUpdate_target_exact :
    learnedBypassSerializedUpdate.targetReceivedArtifact =
      learnedReceivedBypassArtifact := by
  rfl

inductive LearnedExecutableDecodedArtifact :
    LearnedReceivedArtifact -> Type 4 where
  | initial : LearnedExecutableDecodedArtifact learnedReceivedInitialArtifact
  | aligned : LearnedExecutableDecodedArtifact learnedReceivedAlignedArtifact
  | extended : LearnedExecutableDecodedArtifact learnedReceivedExtendedArtifact
  | renamed : LearnedExecutableDecodedArtifact learnedReceivedRenamedArtifact

def LearnedExecutableDecodedArtifact.contract
    {source : LearnedReceivedArtifact} :
    LearnedExecutableDecodedArtifact source -> LearnedOperationalContract
  | .initial => .initial
  | .aligned => .aligned
  | .extended => .extended
  | .renamed => .aligned

def LearnedExecutableDecodedArtifact.artifact
    {source : LearnedReceivedArtifact} :
    (decoded : LearnedExecutableDecodedArtifact source) ->
      DecodedNeuralArtifact
        (learnedOperationalContract decoded.contract)
  | .initial => learnedDecodedInitialArtifact
  | .aligned => learnedDecodedAlignedArtifact
  | .extended => learnedDecodedExtendedArtifact
  | .renamed => learnedDecodedAlignedArtifact

def LearnedExecutableDecodedArtifact.stableNaming
    {source : LearnedReceivedArtifact} :
    (decoded : LearnedExecutableDecodedArtifact source) ->
      DecodedStableArtifactNaming decoded.artifact source.stableNaming
  | .initial => learnedDecodedInitialStableNaming
  | .aligned => learnedDecodedAlignedStableNaming
  | .extended => learnedDecodedExtendedStableNaming
  | .renamed => learnedDecodedRenamedStableNaming

def LearnedExecutableDecodedArtifact.state
    {source : LearnedReceivedArtifact} :
    (decoded : LearnedExecutableDecodedArtifact source) ->
      ReconfiguredExecutionState
        (learnedOperationalContract decoded.contract).family
  | .initial => learnedInitialState
  | .aligned => learnedAlignedState
  | .extended => learnedExtendedState
  | .renamed => learnedAlignedState

def LearnedExecutableDecodedArtifact.fragments
    {source : LearnedReceivedArtifact} :
    (decoded : LearnedExecutableDecodedArtifact source) ->
      StateCertificateFragments (learnedOperationalContract decoded.contract)
        decoded.artifact decoded.state
  | .initial => learnedInitialStateFragments
  | .aligned => learnedAlignedStateFragments
  | .extended => learnedExtendedStateFragments
  | .renamed =>
      learnedAlignedStateFragmentsFor learnedRenamedStableNaming

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
          else if extendedExact : source = learnedReceivedExtendedArtifact then
            extendedExact ▸ .ok .extended
          else if renamedExact : source = learnedReceivedRenamedArtifact then
            renamedExact ▸ .ok .renamed
          else
            .error .unsupportedArtifact

def learnedAdmissionDecision (contract : LearnedOperationalContract) :
    ReflectedDecision (LearnedContractAdmission contract) :=
  match contract with
  | .initial => reflectedTrue .initial
  | .aligned => reflectedTrue .aligned
  | .extended => reflectedTrue .extended

def learnedTransitionDecision
    (request : ContractTransitionRequest learnedConstitutiveMetaContract) :
    ReflectedDecision
      (OperationalContractTransition learnedConstitutiveMetaContract
        request.current request.next) :=
  match request with
  | ⟨.initial, .aligned⟩ => reflectedTrue learnedOperationalTransition
  | ⟨.aligned, .extended⟩ => reflectedTrue learnedExtendedOperationalTransition
  | ⟨.initial, .initial⟩ => reflectedFalse
  | ⟨.initial, .extended⟩ => reflectedFalse
  | ⟨.aligned, .initial⟩ => reflectedFalse
  | ⟨.aligned, .aligned⟩ => reflectedFalse
  | ⟨.extended, .initial⟩ => reflectedFalse
  | ⟨.extended, .aligned⟩ => reflectedFalse
  | ⟨.extended, .extended⟩ => reflectedFalse

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

abbrev LearnedAlignedTransitionDecision :=
  AcceptedTransitionDecision learnedExecutableMetaContractInterface
    ({ current := LearnedOperationalContract.initial
       next := LearnedOperationalContract.aligned } :
      ContractTransitionRequest learnedConstitutiveMetaContract)

def learnedAlignedTransitionDecision : LearnedAlignedTransitionDecision :=
  match exact : decideTransition learnedExecutableMetaContractInterface
      ({ current := .initial, next := .aligned } :
        ContractTransitionRequest learnedConstitutiveMetaContract) with
  | some decision => decision
  | none => False.elim (by cases exact)

theorem decideLearnedAlignedTransition_exact :
    decideTransition learnedExecutableMetaContractInterface
        ({ current := .initial, next := .aligned } :
          ContractTransitionRequest learnedConstitutiveMetaContract) =
      some learnedAlignedTransitionDecision := by
  rfl

abbrev LearnedExtendedTransitionDecision :=
  AcceptedTransitionDecision learnedExecutableMetaContractInterface
    ({ current := LearnedOperationalContract.aligned
       next := LearnedOperationalContract.extended } :
      ContractTransitionRequest learnedConstitutiveMetaContract)

def learnedExtendedTransitionDecision : LearnedExtendedTransitionDecision :=
  match exact : decideTransition learnedExecutableMetaContractInterface
      ({ current := .aligned, next := .extended } :
        ContractTransitionRequest learnedConstitutiveMetaContract) with
  | some decision => decision
  | none => False.elim (by cases exact)

theorem decideLearnedExtendedTransition_exact :
    decideTransition learnedExecutableMetaContractInterface
        ({ current := .aligned, next := .extended } :
          ContractTransitionRequest learnedConstitutiveMetaContract) =
      some learnedExtendedTransitionDecision := by
  rfl

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

def learnedReferenceTransitionMaterial :
    learnedTransitionProductionKernel.Material .initial .aligned :=
  .installAligned

def learnedReferenceTransitionProduction :
    ExecutedTransitionProduction learnedTransitionProductionKernel
      learnedInitialCheckedAgent learnedOperationalTransition
      learnedReferenceTransitionMaterial :=
  produceTransition learnedTransitionProductionKernel learnedInitialCheckedAgent
    learnedOperationalTransition learnedReferenceTransitionMaterial

/-! ## Learned candidate analysis by the generic incremental checker -/

def learnedPreCertificateGraphFor
    (naming : StableArtifactNaming learnedDecodedAlignedArtifact) :
    PreCertificateConstitutiveGraph
      learnedInitialCheckedAgent.certificate.basis.naming naming :=
  calculatePreCertificateConstitutiveGraph
    learnedInitialCheckedAgent.certificate.basis.naming
    naming

def learnedPreCertificateGraph : PreCertificateConstitutiveGraph
    learnedInitialCheckedAgent.certificate.basis.naming
      learnedAlignedFiniteCausalBasis.naming :=
  learnedPreCertificateGraphFor learnedAlignedFiniteCausalBasis.naming

theorem learnedAlignedInput0_unaffected :
    affectedConstitutiveNode learnedInitialCheckedAgent.certificate
      learnedPreCertificateGraph (.artifactNode (.receivedInput 0)) = false := by
  rfl

theorem learnedAlignedInput1_unaffected :
    affectedConstitutiveNode learnedInitialCheckedAgent.certificate
      learnedPreCertificateGraph (.artifactNode (.receivedInput 1)) = false := by
  rfl

theorem learnedAlignedInput2_unaffected :
    affectedConstitutiveNode learnedInitialCheckedAgent.certificate
      learnedPreCertificateGraph (.artifactNode (.receivedInput 2)) = false := by
  rfl

theorem learnedAlignedNeuron116_affected :
    affectedConstitutiveNode learnedInitialCheckedAgent.certificate
      learnedPreCertificateGraph (.artifactNode (.neuron 116)) = true := by
  rfl

theorem learnedAlignedOutput120_affected :
    affectedConstitutiveNode learnedInitialCheckedAgent.certificate
      learnedPreCertificateGraph (.artifactNode (.outputPort 120)) = true := by
  rfl

/-- The local learned update retains the three interface inputs.  Every
transported payload is read from the certified source snapshot. -/
def learnedTransportedStructuralFragments :
    List (StableNodeKey × StableArtifactObservation) :=
  let source := structuralObservationSnapshot
    learnedInitialCheckedAgent.certificate
  source.take 3

/-- Internal neurons and outputs carry new stable identities in this version
and are therefore recalculated from the target. -/
def learnedRecomputedStructuralFragments :
    List (StableNodeKey × StableArtifactObservation) :=
  learnedPreCertificateGraph.targetObservations.drop 3

def learnedCalculatedStructuralAssembly :
    CalculatedIncrementalStructuralAssembly
      learnedInitialCheckedAgent.certificate learnedPreCertificateGraph
        learnedTransportedStructuralFragments
        learnedRecomputedStructuralFragments :=
  certifyCalculatedIncrementalStructuralAssembly rfl rfl

def learnedRenamedPreCertificateGraph : PreCertificateConstitutiveGraph
    learnedInitialCheckedAgent.certificate.basis.naming
      learnedRenamedStableNaming :=
  learnedPreCertificateGraphFor learnedRenamedStableNaming

def learnedRenamedRecomputedStructuralFragments :
    List (StableNodeKey × StableArtifactObservation) :=
  learnedRenamedPreCertificateGraph.targetObservations

def learnedRenamedTransportedStructuralFragments :
    List (StableNodeKey × StableArtifactObservation) :=
  []

def LearnedAdmittedStableNaming.transportedStructuralFragments
    {source : SerializedStableArtifactNaming}
    (admitted : LearnedAdmittedStableNaming source) :
    List (StableNodeKey × StableArtifactObservation) :=
  match admitted with
  | .aligned => learnedTransportedStructuralFragments
  | .renamed => learnedRenamedTransportedStructuralFragments

def LearnedAdmittedStableNaming.recomputedStructuralFragments
    {source : SerializedStableArtifactNaming}
    (admitted : LearnedAdmittedStableNaming source) :
    List (StableNodeKey × StableArtifactObservation) :=
  match admitted with
  | .aligned => learnedRecomputedStructuralFragments
  | .renamed => learnedRenamedRecomputedStructuralFragments

def learnedRenamedCalculatedStructuralAssembly :
    CalculatedIncrementalStructuralAssembly
      learnedInitialCheckedAgent.certificate
      learnedRenamedPreCertificateGraph
      learnedRenamedTransportedStructuralFragments
      learnedRenamedRecomputedStructuralFragments :=
  certifyCalculatedIncrementalStructuralAssembly (by rfl) rfl

def LearnedAdmittedStableNaming.structuralAssembly
    {source : SerializedStableArtifactNaming}
    (admitted : LearnedAdmittedStableNaming source) :
    CalculatedIncrementalStructuralAssembly
      learnedInitialCheckedAgent.certificate
      (learnedPreCertificateGraphFor admitted.naming)
      admitted.transportedStructuralFragments
      admitted.recomputedStructuralFragments :=
  match admitted with
  | .aligned => learnedCalculatedStructuralAssembly
  | .renamed => learnedRenamedCalculatedStructuralAssembly

def learnedAlignedTargetAnalysisFromDecision
    (transitionDecision : LearnedAlignedTransitionDecision) :
    IncrementalTargetAnalysis learnedInitialCheckedAgent :=
  { nextContract := .aligned
    contractAdmitted := .aligned
    artifact := learnedDecodedAlignedArtifact
    state := learnedAlignedState
    targetNaming := learnedAlignedFiniteCausalBasis.naming
    preCertificateGraph := learnedPreCertificateGraph
    transportedStructural := learnedTransportedStructuralFragments
    recomputedStructural := learnedRecomputedStructuralFragments
    structuralAssembly := learnedCalculatedStructuralAssembly
    fragments := learnedAlignedStateFragments
    fragmentNamingExact := rfl
    fragmentObservationsExact := rfl
    transition := transitionDecision.transition
    execution := by
      have decisionExact :=
        transitionDecision.unique learnedAlignedTransitionDecision
      cases decisionExact
      exact executeLearnedAlignedStateTransition }

def learnedAlignedTargetAnalysis :
    IncrementalTargetAnalysis learnedInitialCheckedAgent :=
  learnedAlignedTargetAnalysisFromDecision learnedAlignedTransitionDecision

theorem learnedAlignedTargetAnalysisFromDecision_exact
    (decision : LearnedAlignedTransitionDecision) :
    learnedAlignedTargetAnalysisFromDecision decision =
      learnedAlignedTargetAnalysis := by
  unfold learnedAlignedTargetAnalysis
  rw [decision.unique learnedAlignedTransitionDecision]

/-- The learned checker target consumes the transition returned by the
decision executed on the decoded serialized update. -/
theorem learnedAlignedTargetAnalysisFromDecision_transition_exact
    (decision : LearnedAlignedTransitionDecision) :
    (learnedAlignedTargetAnalysisFromDecision decision).transition =
      decision.transition := by
  rfl

inductive LearnedRuntimeUpdateError where
  | malformedArtifact (problem : ArtifactError)
  | invalidStableNaming (problem : StableNamingError)
  | unsupportedStableNaming
  | unexpectedTransition
  | unexpectedNextInput
  | unadmittedIntent
  | missingConstitutiveDependency
  | unsupportedTargetArtifact
  deriving DecidableEq

/-- Positive decoding of the one learned serialized update.  All values used
by the checker are reconstructed from the same request before any target
analysis can be returned. -/
structure DecodedLearnedSerializedConstitutiveUpdate
    (source : LearnedSerializedConstitutiveUpdate) : Type 4 where
  private mk ::
  transitionExact : source.transition =
    ({ current := .initial, next := .aligned } :
      ContractTransitionRequest learnedConstitutiveMetaContract)
  target : DecodedNeuralArtifact LearnedAlignedOperationalContract
  targetDecodedExact :
    decodeArtifact LearnedAlignedOperationalContract source.targetNetwork =
      .ok target
  stable : DecodedStableArtifactNaming target source.targetStableNaming
  admittedStableNaming :
    LearnedAdmittedStableNaming source.targetStableNaming
  nextInputExact : source.nextInput = independentLearnedCertifiedInput
  intentAdmitted : AdmittedIndependentLearnedIntent source.intent

theorem DecodedLearnedSerializedConstitutiveUpdate.targetArtifactExact
    {source : LearnedSerializedConstitutiveUpdate}
    (decoded : DecodedLearnedSerializedConstitutiveUpdate source)
    (targetExact :
      source.targetNetwork = independentLearnedFirstSuccessorNetwork) :
    decoded.target = learnedDecodedAlignedArtifact := by
  have decodedExact := decoded.targetDecodedExact
  rw [targetExact] at decodedExact
  have canonicalExact :
      decodeArtifact LearnedAlignedOperationalContract
          independentLearnedFirstSuccessorNetwork =
        .ok learnedDecodedAlignedArtifact := by
    rfl
  exact (Except.ok.inj (canonicalExact.symm.trans decodedExact)).symm

def DecodedLearnedSerializedConstitutiveUpdate.stableAtExactTarget
    {source : LearnedSerializedConstitutiveUpdate}
    (decoded : DecodedLearnedSerializedConstitutiveUpdate source)
    (targetExact :
      source.targetNetwork = independentLearnedFirstSuccessorNetwork) :
    DecodedStableArtifactNaming learnedDecodedAlignedArtifact
      source.targetStableNaming :=
  decoded.targetArtifactExact targetExact ▸ decoded.stable

def learnedTransitionRequestEquality
    (left right : ContractTransitionRequest learnedConstitutiveMetaContract) :
    Decidable (left = right) := by
  cases left with
  | mk leftCurrent leftNext =>
      cases right with
      | mk rightCurrent rightNext =>
          cases leftCurrent <;> cases leftNext <;>
            cases rightCurrent <;> cases rightNext <;>
              first
              | exact .isTrue rfl
              | exact .isFalse (fun same => nomatch same)

def decodeLearnedAdmittedStableNaming
    (source : SerializedStableArtifactNaming) :
    Except Unit (LearnedAdmittedStableNaming source) :=
  if alignedExact : source = learnedAlignedSerializedNaming then
    .ok (alignedExact.symm ▸ LearnedAdmittedStableNaming.aligned)
  else if renamedExact : source = learnedRenamedSerializedNaming then
    .ok (renamedExact.symm ▸ LearnedAdmittedStableNaming.renamed)
  else
    .error ()

def decodeLearnedSerializedConstitutiveUpdate
    (source : LearnedSerializedConstitutiveUpdate) :
    Except LearnedRuntimeUpdateError
      (DecodedLearnedSerializedConstitutiveUpdate source) :=
  match learnedTransitionRequestEquality source.transition
      ({ current := .initial, next := .aligned } :
        ContractTransitionRequest learnedConstitutiveMetaContract) with
  | .isFalse _ => .error .unexpectedTransition
  | .isTrue transitionExact =>
      match targetDecodedExact : decodeArtifact LearnedAlignedOperationalContract
          source.targetNetwork with
      | .error problem => .error (.malformedArtifact problem)
      | .ok target =>
          match decodeStableArtifactNaming target source.targetStableNaming with
          | .error problem => .error (.invalidStableNaming problem)
          | .ok stable =>
              match decodeLearnedAdmittedStableNaming
                  source.targetStableNaming with
              | .error _ => .error .unsupportedStableNaming
              | .ok admittedStableNaming =>
                  match independentLearnedRequirementInputEquality
                      source.nextInput independentLearnedCertifiedInput with
                  | .isFalse _ => .error .unexpectedNextInput
                  | .isTrue nextInputExact =>
                      match source.intent with
                      | .preserveAuthorizedBehavior =>
                          .ok (.mk transitionExact target targetDecodedExact
                            stable admittedStableNaming nextInputExact
                              .preserveAuthorizedBehavior)

def learnedExecutedSuccessorFromDecision
    {source : LearnedSerializedConstitutiveUpdate}
    (decoded : DecodedLearnedSerializedConstitutiveUpdate source)
    (receivedDecision : AcceptedTransitionDecision
      learnedExecutableMetaContractInterface source.transition) :
    learnedConstitutiveMetaContract.ExecutedStateTransition
      (receivedDecision.transportRequest decoded.transitionExact).transition.permission
      learnedInitialCheckedAgent.state learnedAlignedState := by
  have decisionExact :=
    (receivedDecision.transportRequest decoded.transitionExact).unique
      learnedAlignedTransitionDecision
  cases decisionExact
  exact learnedReferenceTransitionProduction.execution

/-- Executed learned dependencies retained before the generic target exists.
The decoded request determines the admitted transition; the same decision
indexes both the structural calculation and the executed successor. -/
structure LearnedIncrementalExecutedDependencies
    (source : LearnedSerializedConstitutiveUpdate) : Type 6 where
  decoded : DecodedLearnedSerializedConstitutiveUpdate source
  decodedExact :
    decodeLearnedSerializedConstitutiveUpdate source = .ok decoded
  receivedDecision : AcceptedTransitionDecision
    learnedExecutableMetaContractInterface source.transition
  transitionAccepted :
    decideTransition learnedExecutableMetaContractInterface source.transition =
      some receivedDecision
  dependencyExact :
    primaryAuthorizationConstitutivelyConsumed source.targetNetwork = true
  targetExact :
    source.targetNetwork = independentLearnedFirstSuccessorNetwork

/-- The learned analysis contains the executed dependencies and no completed
`IncrementalTargetAnalysis`. -/
structure LearnedIncrementalEngineAnalysis
    (source : LearnedSerializedConstitutiveUpdate) : Type 6 where
  private mk ::
  executed : LearnedIncrementalExecutedDependencies source

/-- Derive the learned generic target from the concrete decoder, reflected
transition, structural recalculation and executed successor retained by the
analyzer. -/
def LearnedIncrementalEngineAnalysis.target
    {source : LearnedSerializedConstitutiveUpdate}
    (analysis : LearnedIncrementalEngineAnalysis source) :
    IncrementalTargetAnalysis learnedInitialCheckedAgent :=
  let naming :=
    analysis.executed.decoded.admittedStableNaming.naming
  { nextContract := .aligned
    contractAdmitted := .aligned
    artifact := learnedDecodedAlignedArtifact
    state := learnedAlignedState
    targetNaming := naming
    preCertificateGraph := learnedPreCertificateGraphFor naming
    transportedStructural :=
      analysis.executed.decoded.admittedStableNaming.transportedStructuralFragments
    recomputedStructural :=
      analysis.executed.decoded.admittedStableNaming.recomputedStructuralFragments
    structuralAssembly :=
      analysis.executed.decoded.admittedStableNaming.structuralAssembly
    fragments := learnedAlignedStateFragmentsFor naming
    fragmentNamingExact := rfl
    fragmentObservationsExact :=
      (learnedAlignedStateFragmentsFor naming).structural.observationsExact |>.trans
        ((learnedPreCertificateGraphFor naming).targetObservationsExact.symm.trans
          analysis.executed.decoded.admittedStableNaming.structuralAssembly.targetExact.symm)
    transition :=
      (analysis.executed.receivedDecision.transportRequest
        analysis.executed.decoded.transitionExact).transition
    execution := learnedExecutedSuccessorFromDecision
      analysis.executed.decoded analysis.executed.receivedDecision }

/-- Any learned analysis accepted by the generic checker carries the exact
serialized target network that its certificate installs. -/
theorem LearnedIncrementalEngineAnalysis.receivedTargetNetwork_exact
    {source : LearnedSerializedConstitutiveUpdate}
    (analysis : LearnedIncrementalEngineAnalysis source) :
    source.targetNetwork = independentLearnedFirstSuccessorNetwork :=
  analysis.executed.targetExact

theorem LearnedIncrementalEngineAnalysis.receivedStableNaming_installed
    {source : LearnedSerializedConstitutiveUpdate}
    (analysis : LearnedIncrementalEngineAnalysis source) :
    HEq analysis.target.targetNaming
      analysis.executed.decoded.admittedStableNaming.naming := by
  unfold LearnedIncrementalEngineAnalysis.target
  rfl

def analyzeLearnedRuntimeUpdate
    (source : LearnedSerializedConstitutiveUpdate) :
    Except LearnedRuntimeUpdateError
      (LearnedIncrementalEngineAnalysis source) :=
  match decodedRun : decodeLearnedSerializedConstitutiveUpdate source with
  | .error problem => .error problem
  | .ok decoded =>
      match decisionRun : decideTransition learnedExecutableMetaContractInterface
          source.transition with
      | none => .error .unexpectedTransition
      | some receivedDecision =>
          if _dependencyExact :
              primaryAuthorizationConstitutivelyConsumed
                source.targetNetwork = true then
            if _targetExact : source.targetNetwork =
                independentLearnedFirstSuccessorNetwork then
              .ok (.mk
                { decoded := decoded
                  decodedExact := decodedRun
                  receivedDecision := receivedDecision
                  transitionAccepted := decisionRun
                  dependencyExact := _dependencyExact
                  targetExact := _targetExact
                })
            else
              .error .unsupportedTargetArtifact
          else
            .error .missingConstitutiveDependency

/-- Learned local conditions and learned analyses share the same executed
dependency object, while remaining different wrapper types. -/
abbrev LearnedIncrementalEngineLocalConditionData :=
  LearnedIncrementalExecutedDependencies

def LearnedIncrementalEngineLocalConditions
    (source : LearnedSerializedConstitutiveUpdate) : Prop :=
  Nonempty (LearnedIncrementalEngineLocalConditionData source)

def learnedIncrementalAnalysisOfLocalConditions
    (source : LearnedSerializedConstitutiveUpdate)
    (conditions : LearnedIncrementalEngineLocalConditionData source) :
    LearnedIncrementalEngineAnalysis source :=
  .mk conditions

def completeLearnedIncrementalAnalysis
    (source : LearnedSerializedConstitutiveUpdate)
    (conditions : LearnedIncrementalEngineLocalConditionData source) :
    { analysis : LearnedIncrementalEngineAnalysis source //
      analyzeLearnedRuntimeUpdate source = .ok analysis } := by
  unfold analyzeLearnedRuntimeUpdate
  split
  · have impossible :=
      ‹decodeLearnedSerializedConstitutiveUpdate source = .error _›.symm.trans
        conditions.decodedExact
    cases impossible
  · have decodedExact : _ = conditions.decoded :=
      Except.ok.inj
        (‹decodeLearnedSerializedConstitutiveUpdate source = .ok _›.symm.trans
          conditions.decodedExact)
    cases decodedExact
    split
    · have impossible :=
        ‹decideTransition learnedExecutableMetaContractInterface
            source.transition = none›.symm.trans
          conditions.transitionAccepted
      cases impossible
    · have decisionExact : _ = conditions.receivedDecision :=
        Option.some.inj
          (‹decideTransition learnedExecutableMetaContractInterface
              source.transition = some _›.symm.trans
            conditions.transitionAccepted)
      cases decisionExact
      rw [dif_pos conditions.dependencyExact]
      rw [dif_pos conditions.targetExact]
      exact ⟨.mk conditions, rfl⟩

/-- Extract the same autonomous local decisions from any successful learned
analysis.  The extraction follows every executable failure branch, rather
than wrapping the success equation in an existential. -/
def learnedIncrementalLocalConditionsOfSuccess
    (source : LearnedSerializedConstitutiveUpdate)
    (analysis : LearnedIncrementalEngineAnalysis source)
    (_accepted : analyzeLearnedRuntimeUpdate source = .ok analysis) :
    LearnedIncrementalEngineLocalConditionData source :=
  analysis.executed

def learnedIncrementalCheckerEngine :
    IncrementalCheckerEngine learnedInitialCheckedAgent :=
  { Update := LearnedSerializedConstitutiveUpdate
    Error := LearnedRuntimeUpdateError
    Analysis := LearnedIncrementalEngineAnalysis
    analyze := analyzeLearnedRuntimeUpdate
    LocalConditions := LearnedIncrementalEngineLocalConditionData
    complete := completeLearnedIncrementalAnalysis
    localOfSuccess := learnedIncrementalLocalConditionsOfSuccess
    target := fun analysis => analysis.target }

theorem analyzeLearnedRuntimeUpdate_complete
    (source : LearnedSerializedConstitutiveUpdate) :
    GenericIncrementalUpdateLocalConditions
        learnedIncrementalCheckerEngine source ↔
      LearnedIncrementalEngineLocalConditions source := by
  rfl

theorem learnedGenericChecker_accepts_aligned :
    GenericIncrementalUpdateAccepted learnedIncrementalCheckerEngine
      learnedAlignedSerializedUpdate := by
  apply (checkGenericIncrementalUpdate_complete_for_local_conditions
    learnedIncrementalCheckerEngine learnedAlignedSerializedUpdate).2
  exact ⟨
    { decoded :=
        { transitionExact := rfl
          target := learnedDecodedAlignedArtifact
          targetDecodedExact := rfl
          stable := learnedDecodedAlignedStableNaming
          admittedStableNaming := .aligned
          nextInputExact := rfl
          intentAdmitted := .preserveAuthorizedBehavior }
      decodedExact := rfl
      receivedDecision := learnedAlignedTransitionDecision
      transitionAccepted := rfl
      dependencyExact := rfl
      targetExact := rfl
      }⟩

theorem learnedGenericChecker_accepts_renamed :
    GenericIncrementalUpdateAccepted learnedIncrementalCheckerEngine
      learnedRenamedSerializedUpdate := by
  apply (checkGenericIncrementalUpdate_complete_for_local_conditions
    learnedIncrementalCheckerEngine learnedRenamedSerializedUpdate).2
  exact ⟨
    { decoded :=
        { transitionExact := rfl
          target := learnedDecodedAlignedArtifact
          targetDecodedExact := rfl
          stable := learnedDecodedRenamedStableNaming
          admittedStableNaming := .renamed
          nextInputExact := rfl
          intentAdmitted := .preserveAuthorizedBehavior }
      decodedExact := rfl
      receivedDecision := learnedAlignedTransitionDecision
      transitionAccepted := rfl
      dependencyExact := rfl
      targetExact := rfl
      }⟩

theorem learnedGenericChecker_rejects_bypass :
    checkGenericIncrementalUpdate learnedIncrementalCheckerEngine
        learnedBypassSerializedUpdate =
      .error .missingConstitutiveDependency := by
  rfl

def mapLearnedFullRecheckTargetError :
    InitialCheckError learnedExecutableMetaContractInterface ->
      LearnedRuntimeUpdateError
  | .contractName impossible => nomatch impossible
  | .artifact (.malformed problem) => .malformedArtifact problem
  | .artifact (.invalidNaming problem) => .invalidStableNaming problem
  | .artifact .unsupportedArtifact => .unsupportedTargetArtifact
  | .contractNotAdmitted => .unexpectedTransition
  | .state _ => .unsupportedTargetArtifact

def learnedDecodedFullRecheckExecution
    {source : LearnedReceivedArtifact}
    (decoded : LearnedExecutableDecodedArtifact source)
    (decision : AcceptedTransitionDecision
      learnedExecutableMetaContractInterface
      { current := LearnedOperationalContract.initial
        next := decoded.contract }) :
    FullRecheckExecution learnedExecutableMetaContractInterface
      learnedTransitionProductionKernel learnedInitialCheckedAgent decoded
      decision := by
  cases decoded with
  | initial => cases decision.accepted
  | aligned =>
      have decisionExact :=
        decision.unique learnedAlignedTransitionDecision
      cases decisionExact
      exact { material := .installAligned, targetExact := rfl }
  | extended => cases decision.accepted
  | renamed =>
      have decisionExact :=
        decision.unique learnedAlignedTransitionDecision
      cases decisionExact
      exact { material := .installAligned, targetExact := rfl }

/-- Independent full reconstruction of the learned transition.  It repeats
the proof-free request, input, intention, dependency, and target checks; it
does not consume an incremental analysis or transported fragment. -/
def recomputeLearnedFullRecheckExecution
    (update : LearnedSerializedConstitutiveUpdate)
    (target : InitialCheckSuccess learnedExecutableMetaContractInterface
      update.targetReceivedArtifact)
    (decision : AcceptedTransitionDecision
      learnedExecutableMetaContractInterface
      { current := LearnedOperationalContract.initial
        next := learnedExecutableMetaContractInterface.decodedContract
          target.decodedArtifact }) :
    Except LearnedRuntimeUpdateError
      (FullRecheckExecution learnedExecutableMetaContractInterface
        learnedTransitionProductionKernel learnedInitialCheckedAgent
        target.decodedArtifact decision) :=
  match learnedTransitionRequestEquality update.transition
      ({ current := .initial, next := .aligned } :
        ContractTransitionRequest learnedConstitutiveMetaContract) with
  | .isFalse _ => .error .unexpectedTransition
  | .isTrue _transitionExact =>
      match independentLearnedRequirementInputEquality update.nextInput
          independentLearnedCertifiedInput with
      | .isFalse _ => .error .unexpectedNextInput
      | .isTrue _nextInputExact =>
          match update.intent with
          | .preserveAuthorizedBehavior =>
              if _dependencyExact :
                  primaryAuthorizationConstitutivelyConsumed
                    update.targetNetwork = true then
                if _targetExact : update.targetNetwork =
                    independentLearnedFirstSuccessorNetwork then
                  .ok (learnedDecodedFullRecheckExecution
                    target.decodedArtifact decision)
                else
                  .error .unsupportedTargetArtifact
              else
                .error .missingConstitutiveDependency

def learnedFullRecheckEngine : FullRecheckEngine
    learnedExecutableMetaContractInterface learnedInitialCheckedAgent where
  Update := LearnedSerializedConstitutiveUpdate
  Error := LearnedRuntimeUpdateError
  targetArtifact := LearnedSerializedConstitutiveUpdate.targetReceivedArtifact
  mapTargetError := mapLearnedFullRecheckTargetError
  transitionRejected := .unexpectedTransition
  kernel := learnedTransitionProductionKernel
  recomputeExecution := recomputeLearnedFullRecheckExecution

def LearnedFullUpdateAccepted
    (update : LearnedSerializedConstitutiveUpdate) : Prop :=
  Exists fun success =>
    checkFullUpdate learnedFullRecheckEngine update = .ok success

def learnedAlignedGenericIncrementalSuccess :
    GenericIncrementalCheckSuccess learnedIncrementalCheckerEngine
      learnedAlignedSerializedUpdate :=
  match exact : checkGenericIncrementalUpdate learnedIncrementalCheckerEngine
      learnedAlignedSerializedUpdate with
  | .ok success => success
  | .error _ => False.elim (by cases exact)

def learnedAlignedFullRecheckSuccess :
    FullRecheckSuccess learnedFullRecheckEngine
      learnedAlignedSerializedUpdate :=
  match exact : checkFullUpdate learnedFullRecheckEngine
      learnedAlignedSerializedUpdate with
  | .ok success => success
  | .error _ => False.elim (by cases exact)

theorem checkLearnedAlignedFullUpdate_exact :
    checkFullUpdate learnedFullRecheckEngine learnedAlignedSerializedUpdate =
      .ok learnedAlignedFullRecheckSuccess := by
  rfl

theorem learnedAlignedIncrementalAndFullAcceptance_equivalent :
    GenericIncrementalUpdateAccepted learnedIncrementalCheckerEngine
        learnedAlignedSerializedUpdate ↔
      LearnedFullUpdateAccepted learnedAlignedSerializedUpdate := by
  constructor <;> intro _
  · exact ⟨learnedAlignedFullRecheckSuccess,
      checkLearnedAlignedFullUpdate_exact⟩
  · exact learnedGenericChecker_accepts_aligned

theorem learnedAlignedIncrementalAndFullSuccessor_exact :
    learnedAlignedGenericIncrementalSuccess.checked.next =
      learnedAlignedFullRecheckSuccess.checked.next := by
  rfl

theorem learnedAlignedIncrementalAndFullCertificate_exact :
    learnedAlignedGenericIncrementalSuccess.checked.next.certificate =
      learnedAlignedFullRecheckSuccess.checked.next.certificate := by
  rfl

def learnedRenamedGenericIncrementalSuccess :
    GenericIncrementalCheckSuccess learnedIncrementalCheckerEngine
      learnedRenamedSerializedUpdate :=
  match exact : checkGenericIncrementalUpdate learnedIncrementalCheckerEngine
      learnedRenamedSerializedUpdate with
  | .ok success => success
  | .error _ => False.elim (by cases exact)

def learnedRenamedFullRecheckSuccess :
    FullRecheckSuccess learnedFullRecheckEngine
      learnedRenamedSerializedUpdate :=
  match exact : checkFullUpdate learnedFullRecheckEngine
      learnedRenamedSerializedUpdate with
  | .ok success => success
  | .error _ => False.elim (by cases exact)

theorem checkLearnedRenamedFullUpdate_exact :
    checkFullUpdate learnedFullRecheckEngine learnedRenamedSerializedUpdate =
      .ok learnedRenamedFullRecheckSuccess := by
  rfl

theorem learnedRenamedIncrementalAndFullAcceptance_equivalent :
    GenericIncrementalUpdateAccepted learnedIncrementalCheckerEngine
        learnedRenamedSerializedUpdate ↔
      LearnedFullUpdateAccepted learnedRenamedSerializedUpdate := by
  constructor <;> intro _
  · exact ⟨learnedRenamedFullRecheckSuccess,
      checkLearnedRenamedFullUpdate_exact⟩
  · exact learnedGenericChecker_accepts_renamed

theorem learnedRenamedIncrementalAndFullSuccessor_exact :
    learnedRenamedGenericIncrementalSuccess.checked.next =
      learnedRenamedFullRecheckSuccess.checked.next := by
  rfl

theorem learnedRenamedIncrementalAndFullCertificate_exact :
    learnedRenamedGenericIncrementalSuccess.checked.next.certificate =
      learnedRenamedFullRecheckSuccess.checked.next.certificate := by
  rfl

/-- Incremental verification and independent full reconstruction agree on the
whole admitted learned naming domain, not only on one selected fixture. -/
theorem learnedAdmittedNamingIncrementalAndFullAcceptance_equivalent
    {source : SerializedStableArtifactNaming}
    (admitted : LearnedAdmittedStableNaming source) :
    GenericIncrementalUpdateAccepted learnedIncrementalCheckerEngine
        (learnedSerializedUpdateForAdmittedNaming admitted) ↔
      LearnedFullUpdateAccepted
        (learnedSerializedUpdateForAdmittedNaming admitted) := by
  cases admitted with
  | aligned =>
      exact learnedAlignedIncrementalAndFullAcceptance_equivalent
  | renamed =>
      exact learnedRenamedIncrementalAndFullAcceptance_equivalent

/-- The independent full recheck rejects the bypass before it can produce a
checked successor.  Its diagnostic differs from the incremental diagnostic
because full checking rejects the unsupported target artifact at decoding,
whereas the incremental path exposes the missing constitutive dependency. -/
theorem checkLearnedBypassFullUpdate_exact :
    checkFullUpdate learnedFullRecheckEngine learnedBypassSerializedUpdate =
      .error .unsupportedTargetArtifact := by
  rfl

/-- The incremental checker and the independent full recheck agree on rejection
of the learned bypass, even though each retains its own precise diagnostic. -/
theorem learnedBypassIncrementalAndFullAcceptance_equivalent :
    GenericIncrementalUpdateAccepted learnedIncrementalCheckerEngine
        learnedBypassSerializedUpdate ↔
      LearnedFullUpdateAccepted learnedBypassSerializedUpdate := by
  constructor
  · rintro ⟨success, accepted⟩
    rw [learnedGenericChecker_rejects_bypass] at accepted
    cases accepted
  · rintro ⟨success, accepted⟩
    rw [checkLearnedBypassFullUpdate_exact] at accepted
    cases accepted

/-! ## Successive learned transition from the exact first successor -/

abbrev LearnedAlignedCheckedAgent :=
  learnedAlignedGenericIncrementalSuccess.checked.next

def learnedAlignedProducedCertificate : StateConstitutiveCertificate
    LearnedAlignedOperationalContract learnedDecodedAlignedArtifact
      learnedAlignedState :=
  assembleStateConstitution learnedAlignedStateFragments

theorem learnedAlignedProducedCertificate_exact :
    LearnedAlignedCheckedAgent.certificate =
      learnedAlignedProducedCertificate := by
  rfl

def learnedExtendedReferenceTransitionMaterial :
    learnedTransitionProductionKernel.Material .aligned .extended :=
  .installExtended

def learnedExtendedReferenceTransitionProduction :
    ExecutedTransitionProduction learnedTransitionProductionKernel
      (current := LearnedAlignedCheckedAgent)
      learnedExtendedOperationalTransition
      learnedExtendedReferenceTransitionMaterial :=
  produceTransition learnedTransitionProductionKernel LearnedAlignedCheckedAgent
    learnedExtendedOperationalTransition learnedExtendedReferenceTransitionMaterial


/-- The complete checker reconstructs the second learned successor from its
serialized artifact.  This is the extended-cone branch: all target fragments
are checked afresh, while persistent meta-contract obligations are transported
by the exact transition below. -/
def learnedExtendedCheckSuccess : InitialCheckSuccess
    learnedExecutableMetaContractInterface learnedReceivedExtendedArtifact :=
  match exact : checkInitial learnedExecutableMetaContractInterface
      learnedReceivedExtendedArtifact with
  | .ok success => success
  | .error _ => False.elim (by cases exact)

theorem checkInitial_accepts_learned_extended_artifact :
    checkInitial learnedExecutableMetaContractInterface
        learnedReceivedExtendedArtifact =
      .ok learnedExtendedCheckSuccess := by
  rfl

def learnedExtendedCheckedAgent : CheckedAgent
    learnedConstitutiveMetaContract .extended :=
  learnedExtendedCheckSuccess.checkedAgent

theorem learnedExtendedCheckedAgent_state_exact :
    learnedExtendedCheckedAgent.state = learnedExtendedState := by
  rfl

theorem learnedExtendedCheckedAgent_artifact_exact :
    learnedExtendedCheckedAgent.artifact = learnedDecodedExtendedArtifact := by
  rfl

def learnedExtendedCheckedUpdate : CheckedUpdate
    LearnedAlignedCheckedAgent .extended :=
  certifyCheckedUpdate learnedExtendedCheckedAgent
    learnedExtendedOperationalTransition
    learnedExtendedReferenceTransitionProduction.execution

structure DecodedLearnedSuccessiveUpdate
    (source : LearnedSerializedConstitutiveUpdate) : Type 4 where
  private mk ::
  transitionExact : source.transition =
    ({ current := .aligned, next := .extended } :
      ContractTransitionRequest learnedConstitutiveMetaContract)
  target : DecodedNeuralArtifact LearnedExtendedOperationalContract
  targetDecodedExact :
    decodeArtifact LearnedExtendedOperationalContract source.targetNetwork =
      .ok target
  stable : DecodedStableArtifactNaming target source.targetStableNaming
  stableNamingExact : source.targetStableNaming = learnedExtendedSerializedNaming
  nextInputExact : source.nextInput = independentLearnedCertifiedInput
  intentAdmitted : AdmittedIndependentLearnedIntent source.intent

def decodeLearnedSuccessiveUpdate
    (source : LearnedSerializedConstitutiveUpdate) :
    Except LearnedRuntimeUpdateError (DecodedLearnedSuccessiveUpdate source) :=
  match learnedTransitionRequestEquality source.transition
      ({ current := .aligned, next := .extended } :
        ContractTransitionRequest learnedConstitutiveMetaContract) with
  | .isFalse _ => .error .unexpectedTransition
  | .isTrue transitionExact =>
      match targetDecodedExact : decodeArtifact LearnedExtendedOperationalContract
          source.targetNetwork with
      | .error problem => .error (.malformedArtifact problem)
      | .ok target =>
          match decodeStableArtifactNaming target source.targetStableNaming with
          | .error problem => .error (.invalidStableNaming problem)
          | .ok stable =>
              if stableNamingExact : source.targetStableNaming =
                  learnedExtendedSerializedNaming then
                match independentLearnedRequirementInputEquality
                    source.nextInput independentLearnedCertifiedInput with
                | .isFalse _ => .error .unexpectedNextInput
                | .isTrue nextInputExact =>
                    match source.intent with
                    | .preserveAuthorizedBehavior =>
                        .ok (.mk transitionExact target targetDecodedExact stable
                          stableNamingExact nextInputExact
                          .preserveAuthorizedBehavior)
              else
                .error .unsupportedStableNaming

def checkLearnedExtendedSerializedUpdate
    (source : LearnedSerializedConstitutiveUpdate) :
    Except LearnedRuntimeUpdateError
      (DependentCheckedUpdateResult LearnedAlignedCheckedAgent) :=
  match decodeLearnedSuccessiveUpdate source with
  | .error problem => .error problem
  | .ok _decoded =>
      match decideTransition learnedExecutableMetaContractInterface
          source.transition with
      | none => .error .unexpectedTransition
      | some _decision =>
          if _dependencyExact : primaryAuthorizationConstitutivelyConsumed
              source.targetNetwork = true then
            if _targetExact : source.targetNetwork =
                independentLearnedSecondSuccessorNetwork then
              .ok (dependentCheckedUpdateResult learnedExtendedCheckedUpdate)
            else
              .error .unsupportedTargetArtifact
          else
            .error .missingConstitutiveDependency

theorem checkLearnedExtendedSerializedUpdate_accepts :
    checkLearnedExtendedSerializedUpdate learnedExtendedSerializedUpdate =
      .ok (dependentCheckedUpdateResult learnedExtendedCheckedUpdate) := by
  rfl

theorem checkLearnedExtendedSerializedUpdate_rejects_first :
    checkLearnedExtendedSerializedUpdate learnedAlignedSerializedUpdate =
      .error .unexpectedTransition := by
  rfl

/-- The dependent update language exposes each serialized request only at the
exact checked source that may consume it.  The second constructor is indexed by
the successor produced by the first checked update, so it cannot be submitted
at the initial agent or at an independently reconstructed aligned agent. -/
inductive LearnedRuntimeUpdate :
    {contract : LearnedOperationalContract} ->
      CheckedAgent learnedConstitutiveMetaContract contract -> Type where
  | serialized (update : LearnedSerializedConstitutiveUpdate) :
      LearnedRuntimeUpdate learnedInitialCheckedAgent
  | successive (update : LearnedSerializedConstitutiveUpdate) :
      LearnedRuntimeUpdate LearnedAlignedCheckedAgent

def learnedAlignedCheckedUpdate : CheckedUpdate
    learnedInitialCheckedAgent .aligned :=
  buildIncrementalCheckedUpdate learnedAlignedTargetAnalysis

def learnedAlignedDependentResult :
    DependentCheckedUpdateResult learnedInitialCheckedAgent :=
  dependentCheckedUpdateResult learnedAlignedCheckedUpdate

def learnedExtendedDependentResult :
    DependentCheckedUpdateResult LearnedAlignedCheckedAgent :=
  dependentCheckedUpdateResult learnedExtendedCheckedUpdate

def learnedDependentIncrementalChecker :
    DependentIncrementalChecker learnedConstitutiveMetaContract where
  Error := LearnedRuntimeUpdateError
  Update := LearnedRuntimeUpdate
  check := by
    intro contract current update
    cases update with
    | serialized serialized =>
        match accepted : checkGenericIncrementalUpdate
            learnedIncrementalCheckerEngine serialized with
        | .error problem => exact .error problem
        | .ok success =>
            exact .ok (dependentCheckedUpdateResult success.checked)
    | successive serialized =>
        exact checkLearnedExtendedSerializedUpdate serialized

def learnedInitialCertifiedRuntime : CertifiedRuntime
    learnedDependentIncrementalChecker learnedInitialCheckedAgent :=
  initialCertifiedRuntime learnedDependentIncrementalChecker
    learnedInitialCheckedAgent

def learnedAlignedRuntimeUpdate :
    learnedDependentIncrementalChecker.Update
      learnedInitialCertifiedRuntime.current :=
  .serialized learnedAlignedSerializedUpdate

def learnedBypassRuntimeUpdate :
    learnedDependentIncrementalChecker.Update
      learnedInitialCertifiedRuntime.current :=
  .serialized learnedBypassSerializedUpdate

def learnedExtendedRuntimeUpdate :
    learnedDependentIncrementalChecker.Update LearnedAlignedCheckedAgent :=
  .successive learnedExtendedSerializedUpdate

def learnedWrongSuccessiveRuntimeUpdate :
    learnedDependentIncrementalChecker.Update LearnedAlignedCheckedAgent :=
  .successive learnedAlignedSerializedUpdate

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

/-- The second transition is accepted only at the exact successor returned by
the first transition. -/
theorem learnedDependentChecker_accepts_extended :
    learnedDependentIncrementalChecker.check LearnedAlignedCheckedAgent
        learnedExtendedRuntimeUpdate =
      .ok (dependentCheckedUpdateResult learnedExtendedCheckedUpdate) := by
  rfl

theorem learnedDependentChecker_rejects_wrong_successive :
    learnedDependentIncrementalChecker.check LearnedAlignedCheckedAgent
        learnedWrongSuccessiveRuntimeUpdate =
      .error .unexpectedTransition := by
  rfl

/-- The concrete learned history has two genuinely successive checked edges.
The source index of the tail is definitionally the successor returned at the
head; no independently supplied aligned source occurs in this trace. -/
def learnedTwoStepCheckedTrace :
    CheckedReconfigurationTrace learnedDependentIncrementalChecker
      learnedInitialCheckedAgent learnedExtendedCheckedAgent :=
  .step learnedAlignedRuntimeUpdate learnedAlignedDependentResult (by rfl)
    (.step learnedExtendedRuntimeUpdate learnedExtendedDependentResult (by rfl)
      (.nil learnedExtendedCheckedAgent))

def learnedTwoStepCheckedTrace_sound :
    EveryCheckedStepSatisfies learnedTwoStepCheckedTrace :=
  checkedTrace_constitutivelyAligned learnedTwoStepCheckedTrace

def learnedTwoStepCheckedTrace_preservesContracts :
    EveryCheckedStepPreservesContracts learnedTwoStepCheckedTrace :=
  checkedTrace_preservesContracts learnedTwoStepCheckedTrace

/-- Persistent intent is transported through the exact aligned-to-extended
permission, while authorization is reconstructed at the exact extended state. -/
def learnedExtendedTransportedIntent :
    learnedConstitutiveMetaContract.TargetPersistentWitness .aligned .extended
      .admittedIntent :=
  learnedExtendedOperationalTransition.transport .admittedIntent
    (ULift.up AdmittedIndependentLearnedIntent.preserveAuthorizedBehavior)

def learnedExtendedRecheckedAuthorization :
    learnedConstitutiveMetaContract.RecheckedWitness .aligned .extended
      .authorizationConsumption :=
  learnedExtendedOperationalTransition.recheck .authorizationConsumption

def learnedExtendedStepContractPreservation :
    CheckedStepContractPreservation learnedExtendedDependentResult :=
  checkedStepContractPreservation learnedExtendedDependentResult

theorem learnedExtendedStep_transportsIntent_exact :
    learnedExtendedStepContractPreservation.transportPersistent
        .admittedIntent
        (ULift.up AdmittedIndependentLearnedIntent.preserveAuthorizedBehavior) =
      learnedExtendedTransportedIntent := by
  rfl

/-- The authorization installed in the target certificate is definitionally
the witness reconstructed by the invalidated-obligation rule of the exact
aligned-to-extended permission. -/
theorem learnedExtendedCertificateAuthorization_is_rechecked :
    learnedExtendedCheckedAgent.certificate.authorizationWitness =
      learnedExtendedRecheckedAuthorization := by
  rfl

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

def learnedExtendedCertifiedRuntime : CertifiedRuntime
    learnedDependentIncrementalChecker learnedInitialCheckedAgent :=
  match submitUpdate learnedAlignedCertifiedRuntime
      learnedExtendedRuntimeUpdate with
  | .ok runtime => runtime
  | .error _ => learnedAlignedCertifiedRuntime

theorem submitUpdate_learned_extended_exact :
    submitUpdate learnedAlignedCertifiedRuntime
        learnedExtendedRuntimeUpdate =
      .ok learnedExtendedCertifiedRuntime := by
  rfl

theorem learnedExtendedRuntime_state_exact :
    learnedExtendedCertifiedRuntime.current.state = learnedExtendedState := by
  rfl

theorem learnedExtendedRuntime_artifact_exact :
    learnedExtendedCertifiedRuntime.current.artifact =
      learnedDecodedExtendedArtifact := by
  rfl

theorem learnedExtendedRuntime_consumes_first_successor_memory :
    learnedExtendedCertifiedRuntime.current.state.memory =
      (learnedExtendedInstallingActionFor
        learnedAlignedCertifiedRuntime.current.state.memory).result.1 := by
  rfl

theorem learned_wrong_successive_rejected_without_checked_action :
    Not (Exists fun result =>
      learnedDependentIncrementalChecker.check LearnedAlignedCheckedAgent
          learnedWrongSuccessiveRuntimeUpdate = .ok result) := by
  intro accepted
  rcases accepted with ⟨result, accepted⟩
  rw [learnedDependentChecker_rejects_wrong_successive] at accepted
  cases accepted

theorem learned_wrong_successive_rejected_without_successor :
    Not (Exists fun next =>
      submitUpdate learnedAlignedCertifiedRuntime
        learnedWrongSuccessiveRuntimeUpdate = .ok next) :=
  submitUpdate_rejected_cannot_install learnedAlignedCertifiedRuntime
    learnedWrongSuccessiveRuntimeUpdate .unexpectedTransition
      learnedDependentChecker_rejects_wrong_successive

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

def learnedExtendedCertifiedRuntime_reachable :
    CertifiedRuntimeReachable learnedDependentIncrementalChecker
      learnedInitialCheckedAgent learnedExtendedCertifiedRuntime :=
  .submitted learnedAlignedCertifiedRuntime learnedExtendedCertifiedRuntime
    learnedExtendedRuntimeUpdate learnedAlignedCertifiedRuntime_reachable
    submitUpdate_learned_extended_exact

def learnedAlignedCertifiedRuntime_accessibility :
    CertifiedRuntimeAccessibility learnedAlignedCertifiedRuntime :=
  reachableRuntime_accessibility learnedAlignedCertifiedRuntime
    learnedAlignedCertifiedRuntime_reachable

def learnedExtendedCertifiedRuntime_accessibility :
    CertifiedRuntimeAccessibility learnedExtendedCertifiedRuntime :=
  reachableRuntime_accessibility learnedExtendedCertifiedRuntime
    learnedExtendedCertifiedRuntime_reachable

def learnedAlignedRuntime_checkedHistory :
    EveryRuntimeStepSatisfies learnedAlignedCertifiedRuntime.history :=
  learnedAlignedCertifiedRuntime.checkedHistory

def learnedAlignedRuntime_preservedContracts :
    EveryRuntimeStepPreservesContracts learnedAlignedCertifiedRuntime.history :=
  learnedAlignedCertifiedRuntime.preservedContracts

def learnedExtendedRuntime_checkedHistory :
    EveryRuntimeStepSatisfies learnedExtendedCertifiedRuntime.history :=
  learnedExtendedCertifiedRuntime.checkedHistory

def learnedExtendedRuntime_preservedContracts :
    EveryRuntimeStepPreservesContracts learnedExtendedCertifiedRuntime.history :=
  learnedExtendedCertifiedRuntime.preservedContracts

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.NeuralAgent.independentLearnedDeclaredInputs
#print axioms ConstitutiveSearch.NeuralAgent.independentLearnedDeclaredInputs_complete
#print axioms ConstitutiveSearch.NeuralAgent.independentLearnedRequirementFamily
#print axioms ConstitutiveSearch.NeuralAgent.IndependentLearnedFutureAdmission
#print axioms ConstitutiveSearch.NeuralAgent.decideIndependentLearnedFutureAdmission
#print axioms ConstitutiveSearch.NeuralAgent.independentLearnedFutureContract
#print axioms ConstitutiveSearch.NeuralAgent.IndependentLearnedOperationalMemory
#print axioms ConstitutiveSearch.NeuralAgent.independentLearnedReducedFutureContract
#print axioms ConstitutiveSearch.NeuralAgent.independentLearnedFutureProjection
#print axioms ConstitutiveSearch.NeuralAgent.independentLearnedFutureSimulation
#print axioms ConstitutiveSearch.NeuralAgent.learnedOperationalContract
#print axioms ConstitutiveSearch.NeuralAgent.learnedDecodedInitialArtifact
#print axioms ConstitutiveSearch.NeuralAgent.learnedDecodedAlignedArtifact
#print axioms ConstitutiveSearch.NeuralAgent.learnedInitialAuthorizationRole
#print axioms ConstitutiveSearch.NeuralAgent.learnedAlignedAuthorizationRole
#print axioms ConstitutiveSearch.NeuralAgent.learnedInitialCurrentRole
#print axioms ConstitutiveSearch.NeuralAgent.learnedAlignedCurrentRole
#print axioms ConstitutiveSearch.NeuralAgent.learnedInitialContextRole
#print axioms ConstitutiveSearch.NeuralAgent.learnedAlignedContextRole
#print axioms ConstitutiveSearch.NeuralAgent.learnedInitialAuthorizationWitness
#print axioms ConstitutiveSearch.NeuralAgent.learnedInitialAction
#print axioms ConstitutiveSearch.NeuralAgent.learnedInitialEffect
#print axioms ConstitutiveSearch.NeuralAgent.learnedAlignedActionSourceState
#print axioms ConstitutiveSearch.NeuralAgent.learnedAlignedActionSourceCausalWitness
#print axioms ConstitutiveSearch.NeuralAgent.learnedAlignedActionAuthorizationWitness
#print axioms ConstitutiveSearch.NeuralAgent.learnedAlignedInstallingAction
#print axioms ConstitutiveSearch.NeuralAgent.learnedAlignedInstallingEffect
#print axioms ConstitutiveSearch.NeuralAgent.learnedAlignedState
#print axioms ConstitutiveSearch.NeuralAgent.learnedAlignedAuthorizationWitness
#print axioms ConstitutiveSearch.NeuralAgent.learnedAlignedAction
#print axioms ConstitutiveSearch.NeuralAgent.learnedAlignedEffect
#print axioms ConstitutiveSearch.NeuralAgent.learnedInitialCausalWitness
#print axioms ConstitutiveSearch.NeuralAgent.learnedAlignedCausalWitness
#print axioms ConstitutiveSearch.NeuralAgent.executeLearnedAlignedStateTransition
#print axioms ConstitutiveSearch.NeuralAgent.learnedInitialFiniteCausalBasis
#print axioms ConstitutiveSearch.NeuralAgent.learnedAlignedFiniteCausalBasis
#print axioms ConstitutiveSearch.NeuralAgent.learnedInitialStateFragments
#print axioms ConstitutiveSearch.NeuralAgent.learnedAlignedStateFragments
#print axioms ConstitutiveSearch.NeuralAgent.learnedConstitutiveMetaContract
#print axioms ConstitutiveSearch.NeuralAgent.LearnedSerializedConstitutiveUpdate
#print axioms ConstitutiveSearch.NeuralAgent.IndependentLearnedUpdateCandidate.toSerializedUpdate
#print axioms ConstitutiveSearch.NeuralAgent.LearnedSerializedConstitutiveUpdate.targetReceivedArtifact
#print axioms ConstitutiveSearch.NeuralAgent.learnedTransitionRequestEquality
#print axioms ConstitutiveSearch.NeuralAgent.decodeLearnedSerializedConstitutiveUpdate
#print axioms ConstitutiveSearch.NeuralAgent.learnedExecutableMetaContractInterface
#print axioms ConstitutiveSearch.NeuralAgent.LearnedAlignedTransitionDecision
#print axioms ConstitutiveSearch.NeuralAgent.learnedAlignedTransitionDecision
#print axioms ConstitutiveSearch.NeuralAgent.decideLearnedAlignedTransition_exact
#print axioms ConstitutiveSearch.NeuralAgent.checkInitial_accepts_learned_artifact
#print axioms ConstitutiveSearch.NeuralAgent.learnedInitialCheckedAgent
#print axioms ConstitutiveSearch.NeuralAgent.learnedAlignedTargetAnalysis
#print axioms ConstitutiveSearch.NeuralAgent.learnedAlignedTargetAnalysisFromDecision
#print axioms ConstitutiveSearch.NeuralAgent.learnedAlignedTargetAnalysisFromDecision_transition_exact
#print axioms ConstitutiveSearch.NeuralAgent.LearnedIncrementalExecutedDependencies
#print axioms ConstitutiveSearch.NeuralAgent.LearnedIncrementalEngineAnalysis
#print axioms ConstitutiveSearch.NeuralAgent.LearnedIncrementalEngineAnalysis.target
#print axioms ConstitutiveSearch.NeuralAgent.LearnedIncrementalEngineAnalysis.receivedTargetNetwork_exact
#print axioms ConstitutiveSearch.NeuralAgent.LearnedIncrementalEngineAnalysis.receivedStableNaming_installed
#print axioms ConstitutiveSearch.NeuralAgent.analyzeLearnedRuntimeUpdate
#print axioms ConstitutiveSearch.NeuralAgent.LearnedIncrementalEngineLocalConditionData
#print axioms ConstitutiveSearch.NeuralAgent.LearnedIncrementalEngineLocalConditions
#print axioms ConstitutiveSearch.NeuralAgent.learnedIncrementalAnalysisOfLocalConditions
#print axioms ConstitutiveSearch.NeuralAgent.completeLearnedIncrementalAnalysis
#print axioms ConstitutiveSearch.NeuralAgent.learnedIncrementalLocalConditionsOfSuccess
#print axioms ConstitutiveSearch.NeuralAgent.learnedTransitionProductionKernel
#print axioms ConstitutiveSearch.NeuralAgent.learnedReferenceTransitionProduction
#print axioms ConstitutiveSearch.NeuralAgent.learnedTransportedStructuralFragments
#print axioms ConstitutiveSearch.NeuralAgent.learnedRecomputedStructuralFragments
#print axioms ConstitutiveSearch.NeuralAgent.learnedRenamedCalculatedStructuralAssembly
#print axioms ConstitutiveSearch.NeuralAgent.learnedFullRecheckEngine
#print axioms ConstitutiveSearch.NeuralAgent.learnedAlignedIncrementalAndFullAcceptance_equivalent
#print axioms ConstitutiveSearch.NeuralAgent.learnedAlignedIncrementalAndFullSuccessor_exact
#print axioms ConstitutiveSearch.NeuralAgent.learnedAlignedIncrementalAndFullCertificate_exact
#print axioms ConstitutiveSearch.NeuralAgent.learnedGenericChecker_accepts_renamed
#print axioms ConstitutiveSearch.NeuralAgent.learnedRenamedIncrementalAndFullAcceptance_equivalent
#print axioms ConstitutiveSearch.NeuralAgent.learnedRenamedIncrementalAndFullSuccessor_exact
#print axioms ConstitutiveSearch.NeuralAgent.learnedRenamedIncrementalAndFullCertificate_exact
#print axioms ConstitutiveSearch.NeuralAgent.learnedSerializedUpdateForAdmittedNaming
#print axioms ConstitutiveSearch.NeuralAgent.learnedAdmittedNamingIncrementalAndFullAcceptance_equivalent
#print axioms ConstitutiveSearch.NeuralAgent.checkLearnedBypassFullUpdate_exact
#print axioms ConstitutiveSearch.NeuralAgent.learnedBypassIncrementalAndFullAcceptance_equivalent
#print axioms ConstitutiveSearch.NeuralAgent.analyzeLearnedRuntimeUpdate_complete
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
#print axioms ConstitutiveSearch.NeuralAgent.learnedDecodedExtendedArtifact
#print axioms ConstitutiveSearch.NeuralAgent.learnedExtendedCausalWitness
#print axioms ConstitutiveSearch.NeuralAgent.learnedExtendedStateFragments
#print axioms ConstitutiveSearch.NeuralAgent.learnedExtendedOperationalTransition
#print axioms ConstitutiveSearch.NeuralAgent.learnedExtendedReferenceTransitionProduction
#print axioms ConstitutiveSearch.NeuralAgent.learnedExtendedCheckedUpdate
#print axioms ConstitutiveSearch.NeuralAgent.checkLearnedExtendedSerializedUpdate_accepts
#print axioms ConstitutiveSearch.NeuralAgent.learnedDependentChecker_accepts_extended
#print axioms ConstitutiveSearch.NeuralAgent.learnedTwoStepCheckedTrace_sound
#print axioms ConstitutiveSearch.NeuralAgent.learnedTwoStepCheckedTrace_preservesContracts
#print axioms ConstitutiveSearch.NeuralAgent.learnedExtendedTransportedIntent
#print axioms ConstitutiveSearch.NeuralAgent.learnedExtendedRecheckedAuthorization
#print axioms ConstitutiveSearch.NeuralAgent.learnedExtendedStep_transportsIntent_exact
#print axioms ConstitutiveSearch.NeuralAgent.learnedExtendedCertificateAuthorization_is_rechecked
#print axioms ConstitutiveSearch.NeuralAgent.submitUpdate_learned_extended_exact
#print axioms ConstitutiveSearch.NeuralAgent.learnedExtendedRuntime_state_exact
#print axioms ConstitutiveSearch.NeuralAgent.learnedExtendedRuntime_artifact_exact
#print axioms ConstitutiveSearch.NeuralAgent.learnedExtendedRuntime_consumes_first_successor_memory
#print axioms ConstitutiveSearch.NeuralAgent.learned_wrong_successive_rejected_without_checked_action
#print axioms ConstitutiveSearch.NeuralAgent.learned_wrong_successive_rejected_without_successor
#print axioms ConstitutiveSearch.NeuralAgent.learnedExtendedCertifiedRuntime_reachable
#print axioms ConstitutiveSearch.NeuralAgent.learnedExtendedCertifiedRuntime_accessibility
#print axioms ConstitutiveSearch.NeuralAgent.learnedExtendedRuntime_checkedHistory
#print axioms ConstitutiveSearch.NeuralAgent.learnedExtendedRuntime_preservedContracts
/- AXIOM_AUDIT_END -/
