import RelationalPerimeter.Agents.Neural.IncrementalChecker

/-!
# Parameterized family for the compiled constitutive checker

This module builds a genuine family of native artifacts whose chronological
neural graph grows with the parameter.  It is not a repetition counter around
the fixed public example.  Every member is consumed through the generic
compiled initial, incremental, and full-reference checker interfaces.

The family is an experimental workload.  Its deliberately small operational
contract does not replace the independent learned artifact or the public
alignment instance.  It exists to compare the two checker paths on the same
growing artifact, certificate property, and executed transition.
-/
set_option genInjectivity false
set_option maxHeartbeats 4000000
namespace ConstitutiveSearch.NeuralAgent
open NativeMechanism

def scalingInput : PublicRequirementInput :=
  RequirementInput.mk .scopeZero .direct

abbrev ScalingUnit3 := ULift.{3} Unit

def scalingUnit3 : ScalingUnit3 := ULift.up ()

abbrev ScalingUnit4 := ULift.{4} Unit

def scalingUnit4 : ScalingUnit4 := ULift.up ()

def scalingUnitObligation : ContractObligationFamily where
  Statement := ScalingUnit3
  Witness := fun _ => ScalingUnit3

def scalingFutureContract :
    ContinuationSignatures.FutureContract
      ScalingUnit3 ScalingUnit3 ScalingUnit3 ScalingUnit3 where
  next := fun _ _ => scalingUnit3
  event := fun _ _ => scalingUnit3
  read := fun _ => scalingUnit3
  Allow := fun _ _ => ScalingUnit3
  decision := fun _ _ => .inl scalingUnit3

def scalingContract : ConstitutiveContract where
  RequirementCase := PublicRequirementCase
  Context := PublicRequirementContext
  Proposal := Bool
  family := publicRequirementFamily
  inputCount := 1
  encode := encodePublicRequirement
  decode := decodePublicRequirement
  actionChannel := publicAgentActionChannel
  declaredCurrentInputs := [scalingInput]
  declaredReplacementValues := [3]
  FutureSource := ScalingUnit3
  FutureInput := ScalingUnit3
  FutureEvent := ScalingUnit3
  FutureObservation := ScalingUnit3
  futureContract := scalingFutureContract
  futureSourceOfState := fun _ => scalingUnit3
  requirementEncoding := scalingUnitObligation
  requirementEncodingAt := fun _ => scalingUnit3
  causalCondition := scalingUnitObligation
  causalConditionAt := fun _ => scalingUnit3
  proposalActionPreservation := scalingUnitObligation
  proposalActionPreservationAt := fun _ => scalingUnit3
  authorizationAdmission := scalingUnitObligation
  authorizationAdmissionAt := fun _ => scalingUnit3
  effectSatisfaction := scalingUnitObligation
  effectSatisfactionAt := fun _ => scalingUnit3
  coveredFuture := scalingUnitObligation
  coveredFutureAt := fun _ _ => scalingUnit3
  historicalPolicy := scalingUnitObligation
  historicalPolicyAt := fun _ => scalingUnit3

inductive ScalingArtifactVersion where
  | source
  | local
  | extended
  deriving DecidableEq, Repr

def scalingBaseNeuron : ScalingArtifactVersion -> NeuronSpec 1 0
  | .source => publicRequirementNeuron
  | .local => publicRequirementNeuron
  | .extended =>
      { inputs :=
          [{ source := .receivedInput publicRequirementPort, weight := 2 }]
        bias := 0
        threshold := ⟨5⟩ }

def scalingTailNeuron (prior : Nat) : NeuronSpec 1 (prior + 1) :=
  { inputs :=
      [{ source := .priorNeuron (Fin.last prior), weight := 1 }]
    bias := 0
    threshold := ⟨1⟩ }

def scalingLocalTailNeuron (prior : Nat) : NeuronSpec 1 (prior + 1) :=
  { inputs :=
      [{ source := .priorNeuron (Fin.last prior), weight := 1 }]
    bias := 0
    threshold := ⟨2⟩ }

def scalingPrefix (base : NeuronSpec 1 0) :
    (extra : Nat) -> NetworkProgram 1 (extra + 1)
  | 0 => .extend .empty base
  | extra + 1 => .extend (scalingPrefix base extra) (scalingTailNeuron extra)

def scalingProgram (size : Nat) :
    ScalingArtifactVersion -> NetworkProgram 1 (size + 2)
  | .source =>
      .extend (scalingPrefix (scalingBaseNeuron .source) size)
        (scalingTailNeuron size)
  | .local =>
      .extend (scalingPrefix (scalingBaseNeuron .local) size)
        (scalingLocalTailNeuron size)
  | .extended =>
      .extend (scalingPrefix (scalingBaseNeuron .extended) size)
        (scalingTailNeuron size)

def scalingFirstNeuron (size : Nat) : Fin (size + 2) :=
  ⟨0, Nat.zero_lt_succ (size + 1)⟩

def scalingOutputs (size : Nat) : OutputPorts (size + 2) where
  sources := [scalingFirstNeuron size]
  nonempty := by intro impossible; cases impossible

def scalingSystem (size : Nat) (version : ScalingArtifactVersion) :
    NativeSystem PublicRequirementInput Bool where
  inputCount := 1
  producedCount := size + 2
  encode := encodePublicRequirement
  program := scalingProgram size version
  outputs := scalingOutputs size
  decode := decodePublicRequirement

def scalingSerializedNetwork (size : Nat)
    (version : ScalingArtifactVersion) : SerializedNetwork :=
  serializeNativeSystem (scalingSystem size version)

def scalingDecodedArtifact (size : Nat)
    (version : ScalingArtifactVersion) :
    DecodedNeuralArtifact scalingContract :=
  certifyDecodedNeuralArtifact scalingContract
    (scalingSerializedNetwork size version)
    (scalingSystem size version)
    { inputCountExact := rfl
      contractInputCountExact := rfl
      neuronsExact := rfl
      outputsExact := rfl
      encodingExact := by intro input; rfl
      decoderExact := by intro values; rfl }

def descendingSerials : Nat -> List Nat
  | 0 => []
  | count + 1 => count :: descendingSerials count

def serialAbsentAtOrAbove : (value count : Nat) -> count ≤ value ->
    StableSerialAbsent value (descendingSerials count)
  | _, 0, _ => .nil
  | value, count + 1, within =>
      .cons
        (by
          intro same
          subst value
          exact (Nat.not_succ_le_self count) within)
        (serialAbsentAtOrAbove value count
          (Nat.le_trans (Nat.le_succ count) within))

def descendingSerialLayout : (count : Nat) ->
    StableSerialLayout count (descendingSerials count)
  | 0 => .nil
  | count + 1 =>
      .cons (serialAbsentAtOrAbove count count (Nat.le_refl count))
        (descendingSerialLayout count)

def scalingSerializedStableNaming (size : Nat) :
    SerializedStableArtifactNaming :=
  { inputKeys := descendingSerials 1
    neuronKeys := descendingSerials (size + 2)
    outputKeys := descendingSerials 1 }

def scalingDecodedStableNaming (size : Nat)
    (version : ScalingArtifactVersion) :
    DecodedStableArtifactNaming (scalingDecodedArtifact size version)
      (scalingSerializedStableNaming size) where
  inputLayout := descendingSerialLayout 1
  neuronLayout := descendingSerialLayout (size + 2)
  outputLayout := descendingSerialLayout 1

def scalingStableNaming (size : Nat)
    (version : ScalingArtifactVersion) :
    StableArtifactNaming (scalingDecodedArtifact size version) :=
  (scalingDecodedStableNaming size version).naming

theorem scalingPrefix_neuronAt_first
    (base : NeuronSpec 1 0) (extra : Nat) :
    (scalingPrefix base extra).neuronAt
        ⟨0, Nat.zero_lt_succ extra⟩ = base := by
  induction extra with
  | zero => rfl
  | succ extra ih =>
      unfold scalingPrefix NetworkProgram.neuronAt
      rw [dif_pos (Nat.zero_lt_succ extra)]
      exact ih

theorem scalingProgram_neuronAt_first
    (size : Nat) (version : ScalingArtifactVersion) :
    (scalingProgram size version).neuronAt (scalingFirstNeuron size) =
      scalingBaseNeuron version := by
  cases version <;>
    unfold scalingProgram NetworkProgram.neuronAt scalingFirstNeuron <;>
    rw [dif_pos (Nat.zero_lt_succ size)] <;>
    exact scalingPrefix_neuronAt_first _ _

theorem sizedActivations_zero_eq_empty
    (values : SizedActivations 0) : values = SizedActivations.empty := by
  apply SizedActivations.eq_of_values_eq
  cases values with
  | mk entries lengthExact =>
      cases entries with
      | nil => rfl
      | cons head tail => cases lengthExact

theorem scalingFirstActivation_exact
    (size : Nat) (version : ScalingArtifactVersion)
    (input : PublicRequirementInput) :
    ((scalingSystem size version).run input).activations.read
        (scalingFirstNeuron size) =
      fireNeuron (scalingBaseNeuron version)
        (encodePublicRequirement input) SizedActivations.empty := by
  have execution :=
    ((scalingSystem size version).run input).trace.neuron_output_exact
      (scalingFirstNeuron size)
  change
    ((scalingSystem size version).run input).activations.read
        (scalingFirstNeuron size) =
      fireNeuron ((scalingProgram size version).neuronAt
        (scalingFirstNeuron size)) (encodePublicRequirement input)
        (((scalingSystem size version).run input).trace.activationsBefore
          (scalingFirstNeuron size)) at execution
  rw [scalingProgram_neuronAt_first] at execution
  have prefixExact :
      ((scalingSystem size version).run input).trace.activationsBefore
          (scalingFirstNeuron size) = SizedActivations.empty :=
    sizedActivations_zero_eq_empty _
  rw [prefixExact] at execution
  exact execution

def scalingIntervention (size : Nat) (version : ScalingArtifactVersion) :
    Intervention ((scalingSystem size version).run scalingInput) where
  focus := .input publicRequirementPort
  replacement := 3
  changesValue := by
    change (3 : Int) ≠ 2
    decide

theorem scalingIntervention_focus_exact
    (size : Nat) (version : ScalingArtifactVersion) :
    (scalingIntervention size version).focusOccurrence =
      (.receivedInput publicRequirementPort : ActivationOccurrence
        ((scalingSystem size version).run scalingInput)) := by
  rfl

def scalingFirstEdge
    (size : Nat) (version : ScalingArtifactVersion) :
    EffectiveReadsFrom ((scalingSystem size version).run scalingInput)
      (.receivedInput publicRequirementPort)
      (.neuronOutput (scalingFirstNeuron size)) := by
  cases version
  · exact .executedEdge (scalingFirstNeuron size)
      { source := .receivedInput publicRequirementPort, weight := 1 }
      (by
        change
          ({ source := .receivedInput publicRequirementPort, weight := 1 } :
            WeightedInput 1 0) ∈
            ((scalingProgram size .source).neuronAt
              (scalingFirstNeuron size)).inputs
        rw [scalingProgram_neuronAt_first]
        exact List.Mem.head _)
      (show (1 : Int) ≠ 0 by decide)
  · exact .executedEdge (scalingFirstNeuron size)
      { source := .receivedInput publicRequirementPort, weight := 1 }
      (by
        change
          ({ source := .receivedInput publicRequirementPort, weight := 1 } :
            WeightedInput 1 0) ∈
            ((scalingProgram size .local).neuronAt
              (scalingFirstNeuron size)).inputs
        rw [scalingProgram_neuronAt_first]
        exact List.Mem.head _)
      (show (1 : Int) ≠ 0 by decide)
  · exact .executedEdge (scalingFirstNeuron size)
      { source := .receivedInput publicRequirementPort, weight := 2 }
      (by
        change
          ({ source := .receivedInput publicRequirementPort, weight := 2 } :
            WeightedInput 1 0) ∈
            ((scalingProgram size .extended).neuronAt
              (scalingFirstNeuron size)).inputs
        rw [scalingProgram_neuronAt_first]
        exact List.Mem.head _)
      (show (2 : Int) ≠ 0 by decide)

theorem scalingFirstOutput_original
    (size : Nat) (version : ScalingArtifactVersion) :
    ((scalingSystem size version).run scalingInput).activations.read
      (scalingFirstNeuron size) = 0 := by
  rw [scalingFirstActivation_exact]
  cases version <;> rfl

theorem scalingFirstOutput_intervened
    (size : Nat) (version : ScalingArtifactVersion) :
    (executeIntervened (scalingIntervention size version)).read
      (scalingFirstNeuron size) = 1 := by
  change
    (executeProgram (scalingProgram size version)
      ((encodePublicRequirement scalingInput).replace publicRequirementPort 3)).read
        (scalingFirstNeuron size) = 1
  have firstExact := scalingFirstActivation_exact size version
    (RequirementInput.mk .scopeZero .reversed)
  have inputExact :
      (encodePublicRequirement scalingInput).replace publicRequirementPort 3 =
        encodePublicRequirement
          (RequirementInput.mk .scopeZero .reversed) := by
    apply SizedActivations.eq_of_values_eq
    rfl
  rw [inputExact]
  change
    ((scalingSystem size version).run
      (RequirementInput.mk .scopeZero .reversed)).activations.read
        (scalingFirstNeuron size) = 1
  rw [firstExact]
  cases version <;> rfl

theorem scalingFirstOutput_changed
    (size : Nat) (version : ScalingArtifactVersion) :
    OccurrenceChanged (scalingIntervention size version)
      (.neuronOutput (scalingFirstNeuron size)) :=
  { different := by
      simp only [intervenedValue, ActivationOccurrence.value]
      rw [scalingFirstOutput_intervened, scalingFirstOutput_original]
      decide }

def scalingPropagation
    (size : Nat) (version : ScalingArtifactVersion) :
    NontrivialExecutedChangePath (scalingIntervention size version)
      (.neuronOutput (scalingFirstNeuron size)) :=
  let edge : EffectiveReadsFrom
      ((scalingSystem size version).run scalingInput)
      (scalingIntervention size version).focusOccurrence
      (.neuronOutput (scalingFirstNeuron size)) :=
    Eq.mp
      (congrArg
        (fun source => EffectiveReadsFrom
          ((scalingSystem size version).run scalingInput) source
          (.neuronOutput (scalingFirstNeuron size)))
        (scalingIntervention_focus_exact size version).symm)
      (scalingFirstEdge size version)
  .step .origin edge (scalingFirstOutput_changed size version)

theorem scalingTarget_changed
    (size : Nat) (version : ScalingArtifactVersion) :
    ChangesTarget ((scalingSystem size version).run scalingInput)
      (scalingIntervention size version) (scalingOutputs size) :=
  { different := by
      change
        [(executeIntervened (scalingIntervention size version)).read
          (scalingFirstNeuron size)] ≠
        [((scalingSystem size version).run scalingInput).activations.read
          (scalingFirstNeuron size)]
      rw [scalingFirstOutput_intervened, scalingFirstOutput_original]
      decide }

theorem scalingProposal_changed
    (size : Nat) (version : ScalingArtifactVersion) :
    ChangesProposal (scalingSystem size version) scalingInput
      (scalingIntervention size version) :=
  { different := by
      change
        decodePublicRequirement
            [(executeIntervened (scalingIntervention size version)).read
              (scalingFirstNeuron size)] ≠
          decodePublicRequirement
            [((scalingSystem size version).run scalingInput).activations.read
              (scalingFirstNeuron size)]
      rw [scalingFirstOutput_intervened, scalingFirstOutput_original]
      decide }

def scalingCausalRole
    (size : Nat) (version : ScalingArtifactVersion) :
    CausalRole (scalingSystem size version) scalingInput
      (.receivedInput publicRequirementPort) where
  intervention := scalingIntervention size version
  focusExact := scalingIntervention_focus_exact size version
  output := (⟨0, by decide⟩ : Fin 1)
  propagation := scalingPropagation size version
  targetChange := scalingTarget_changed size version
  proposalChange := scalingProposal_changed size version

def scalingReplacements
    {size : Nat} {version : ScalingArtifactVersion}
    (_node : StableNodeId (scalingStableNaming size version)) :
    List Activation := [3]

def scalingFiniteCausalBasis
    (size : Nat) (version : ScalingArtifactVersion) :
    FiniteCausalBasis scalingContract
      (scalingDecodedArtifact size version) where
  currentInputs := [scalingInput]
  currentInputsComplete := fun _ listed => listed
  inputEquality := publicRequirementInputEquality
  naming := scalingStableNaming size version
  replacements := scalingReplacements
  replacementCoverage := by
    intro input declared
    cases declared with
    | head =>
        exact
          { node := .receivedInput publicRequirementPort
            role := scalingCausalRole size version
            replacementListed := .head
            replacementDeclared := .head }
    | tail later => nomatch later
  replacementEquality := publicActivationEquality

def scalingState (size : Nat) (version : ScalingArtifactVersion) :
    ReconfiguredExecutionState publicRequirementFamily :=
  { system := scalingSystem size version
    input := scalingInput
    memory := publicActionMemory }

def scalingFutureRealization : CoveredFutureRealization scalingContract where
  ReducedMemory := ScalingUnit3
  reducedContract := scalingFutureContract
  project := fun source => source
  simulation :=
    { forward := fun _ _ witness => witness
      backward := fun _ _ witness => witness
      backwardForward := by intro source input witness; rfl
      forwardBackward := by intro source input witness; rfl
      nextExact := by intro source input; rfl
      eventExact := by intro source input; rfl
      readExact := by intro source; rfl }

def scalingStateFragments
    (size : Nat) (version : ScalingArtifactVersion) :
    StateCertificateFragments scalingContract
      (scalingDecodedArtifact size version) (scalingState size version) :=
  let basis := scalingFiniteCausalBasis size version
  { structural :=
      { basis := basis
        systemExact := rfl
        inputDeclared := .head
        observations := stableStructuralObservationSnapshot basis.naming
        observationsExact := rfl }
    requirement := { witness := scalingUnit3 }
    causal := { witness := scalingUnit3 }
    proposalAction := { witness := scalingUnit3 }
    authorization := { witness := scalingUnit3 }
    effect := { witness := scalingUnit3 }
    historical := { witness := scalingUnit3 }
    futures :=
      { covered := fun _ => scalingUnit3
        realization := scalingFutureRealization } }

def scalingStateCertificate
    (size : Nat) (version : ScalingArtifactVersion) :
    StateConstitutiveCertificate scalingContract
      (scalingDecodedArtifact size version) (scalingState size version) :=
  assembleStateConstitution (scalingStateFragments size version)

def scalingMetaContract : ConstitutiveMetaContract where
  Contract := Unit
  operational := fun _ => scalingContract
  Admits := fun _ => Unit
  TransitionPermission := fun _ _ => Unit
  PersistentObligation := fun _ _ => Unit
  SourcePersistentWitness := fun _ _ _ => ScalingUnit3
  TargetPersistentWitness := fun _ _ _ => ScalingUnit3
  transportPersistent := fun _ _ _ => scalingUnit3
  RecheckObligation := fun _ _ => Unit
  RecheckedWitness := fun _ _ _ => ScalingUnit3
  recheckInvalidated := fun _ _ => scalingUnit3
  ExecutedStateTransition := fun _ _ _ => ScalingUnit4

def scalingOperationalTransition :
    OperationalContractTransition scalingMetaContract () () :=
  certifyOperationalContractTransition () () ()

def scalingTransitionKernel : TransitionProductionKernel scalingMetaContract where
  Material := fun _ _ => ReconfiguredExecutionState publicRequirementFamily
  Production := fun _ _ _ => ScalingUnit3
  produce := fun _ _ _ => scalingUnit3
  targetOf := fun _ _ target _ => target
  execution := fun _ _ _ _ => scalingUnit4

structure ScalingReceivedArtifact where
  size : Nat
  version : ScalingArtifactVersion
  deriving DecidableEq

def scalingReceivedNetwork (source : ScalingReceivedArtifact) :
    SerializedNetwork :=
  scalingSerializedNetwork source.size source.version

def scalingReceivedStableNaming (source : ScalingReceivedArtifact) :
    SerializedStableArtifactNaming :=
  scalingSerializedStableNaming source.size

abbrev ScalingDecodedToken := ULift.{4} Unit

def scalingDecodedToken : ScalingDecodedToken := ULift.up ()

def scalingReflectedTrue {Witness : Sort u} (witness : Witness) :
    ReflectedDecision Witness where
  result := true
  reflect := fun _ => witness

def scalingExecutableInterface :
    ExecutableMetaContractInterface scalingMetaContract where
  ContractCode := Unit
  encodeContract := fun _ => ()
  encodeContractInjective := by intro left right same; cases left; cases right; rfl
  ContractNameError := Empty
  decodeContractName := fun _ =>
    .ok { contract := (), exact := rfl }
  ReceivedArtifact := ScalingReceivedArtifact
  artifactContractCode := fun _ => ()
  artifactNetwork := scalingReceivedNetwork
  artifactStableNaming := scalingReceivedStableNaming
  ArtifactError := Empty
  DecodedArtifact := fun _ => ScalingDecodedToken
  decodedContract := fun _ => ()
  decodedContractExact := fun _ => rfl
  decodedNeuralArtifact := fun {source} _ =>
    scalingDecodedArtifact source.size source.version
  decodedNetworkExact := fun _ => rfl
  decodedStableNaming := fun {source} _ =>
    scalingDecodedStableNaming source.size source.version
  decodeReceivedArtifact := fun _ => .ok scalingDecodedToken
  stateOfArtifact := fun {source} _ => scalingState source.size source.version
  admissionDecision := fun _ => scalingReflectedTrue ()
  transitionDecision := fun _ =>
    scalingReflectedTrue scalingOperationalTransition
  basisDecision := fun {source} _ =>
    scalingReflectedTrue (scalingFiniteCausalBasis source.size source.version)
  systemDecision := fun _ => scalingReflectedTrue rfl
  declaredInputDecision := fun _ => scalingReflectedTrue Listed.head
  requirementDecision := fun _ => scalingReflectedTrue scalingUnit3
  contextDecision := fun _ => scalingReflectedTrue scalingUnit3
  authorizationDecision := fun _ => scalingReflectedTrue scalingUnit3
  actionDecision := fun _ => scalingReflectedTrue scalingUnit3
  effectDecision := fun _ => scalingReflectedTrue scalingUnit3
  historicalDecision := fun _ => scalingReflectedTrue scalingUnit3
  coveredFuturesDecision := fun _ =>
    scalingReflectedTrue (fun _ => scalingUnit3)
  futureRealizationDecision := fun _ =>
    scalingReflectedTrue scalingFutureRealization

def scalingSourceArtifact (size : Nat) : ScalingReceivedArtifact :=
  { size := size, version := .source }

def scalingTargetArtifact (size : Nat)
    (version : ScalingArtifactVersion) : ScalingReceivedArtifact :=
  { size := size, version := version }

def checkScalingInitial (size : Nat) :=
  checkInitial scalingExecutableInterface (scalingSourceArtifact size)

inductive ScalingCheckerError where
  | initial
  | target
  | transition
  | structuralAssembly
  | structuralMismatch
  deriving DecidableEq

def scalingFullRecheckEngine
    (current : CheckedAgent scalingMetaContract ()) :
    FullRecheckEngine scalingExecutableInterface current where
  Update := ScalingReceivedArtifact
  Error := ScalingCheckerError
  targetArtifact := fun update => update
  mapTargetError := fun _ => .target
  transitionRejected := .transition
  kernel := scalingTransitionKernel
  recomputeExecution := fun _ target _decision =>
    .ok
      { material := scalingExecutableInterface.stateOfArtifact
          target.decodedArtifact
        targetExact := rfl }

structure ScalingIncrementalLocalConditions
    (current : CheckedAgent scalingMetaContract ())
    (update : ScalingReceivedArtifact) : Type 6 where
  target : InitialCheckSuccess scalingExecutableInterface update
  graph : PreCertificateConstitutiveGraph
    current.certificate.basis.naming
    (scalingExecutableInterface.decodedStableNaming
      target.decodedArtifact).naming
  transported : List (StableNodeKey × StableArtifactObservation)
  recomputed : List (StableNodeKey × StableArtifactObservation)
  assembly : CalculatedIncrementalStructuralAssembly
    current.certificate graph transported recomputed
  transitionDecision : AcceptedTransitionDecision scalingExecutableInterface
    { current := ()
      next := scalingExecutableInterface.decodedContract
        target.decodedArtifact }

def calculateScalingIncrementalLocalConditions
    (current : CheckedAgent scalingMetaContract ())
    (update : ScalingReceivedArtifact) :
    Except ScalingCheckerError
      (ScalingIncrementalLocalConditions current update) :=
  match checkInitial scalingExecutableInterface update with
  | .error _ => .error .target
  | .ok target =>
      let targetNaming :=
        (scalingExecutableInterface.decodedStableNaming
          target.decodedArtifact).naming
      let graph := calculatePreCertificateConstitutiveGraph
        current.certificate.basis.naming targetNaming
      let transported := structuralObservationSnapshot current.certificate
      let recomputed := graph.targetObservations
      match calculated : calculateIncrementalStructuralAssembly
          current.certificate graph transported recomputed with
      | .error _ => .error .structuralAssembly
      | .ok observations =>
          if targetExact : observations = graph.targetObservations then
            let assembly := certifyCalculatedIncrementalStructuralAssembly
              calculated targetExact
            match decideDecodedTransition scalingExecutableInterface ()
                target.decodedArtifact with
            | none => .error .transition
            | some transitionDecision =>
                .ok
                  { target := target
                    graph := graph
                    transported := transported
                    recomputed := recomputed
                    assembly := assembly
                    transitionDecision := transitionDecision }
          else
            .error .structuralMismatch

structure ScalingIncrementalEvidence
    (current : CheckedAgent scalingMetaContract ())
    (update : ScalingReceivedArtifact) : Type 6 where
  conditions : ScalingIncrementalLocalConditions current update
  calculated : calculateScalingIncrementalLocalConditions current update =
    .ok conditions

def scalingIncrementalTargetAnalysis
    {current : CheckedAgent scalingMetaContract ()}
    {update : ScalingReceivedArtifact}
    (conditions : ScalingIncrementalLocalConditions current update) :
    IncrementalTargetAnalysis current :=
  let fragments := scalingExecutableInterface.certifyFragments
    conditions.target.stateAccepted
  { nextContract := ()
    contractAdmitted := ()
    artifact := scalingExecutableInterface.decodedNeuralArtifact
      conditions.target.decodedArtifact
    state := scalingExecutableInterface.stateOfArtifact
      conditions.target.decodedArtifact
    targetNaming :=
      (scalingExecutableInterface.decodedStableNaming
        conditions.target.decodedArtifact).naming
    preCertificateGraph := conditions.graph
    transportedStructural := conditions.transported
    recomputedStructural := conditions.recomputed
    structuralAssembly := conditions.assembly
    fragments := fragments
    fragmentNamingExact := rfl
    fragmentObservationsExact := by
      exact
        (conditions.assembly.targetExact.trans
          conditions.graph.targetObservationsExact).symm
    transition := conditions.transitionDecision.transition
    execution := scalingUnit4 }

def scalingIncrementalCheckerEngine
    (current : CheckedAgent scalingMetaContract ()) :
    IncrementalCheckerEngine current where
  Update := ScalingReceivedArtifact
  Error := ScalingCheckerError
  Analysis := fun update => ScalingIncrementalLocalConditions current update
  analyze := calculateScalingIncrementalLocalConditions current
  LocalConditions := fun update => ScalingIncrementalEvidence current update
  complete := fun _ evidence => ⟨evidence.conditions, evidence.calculated⟩
  localOfSuccess := fun _ conditions calculated =>
    { conditions := conditions, calculated := calculated }
  target := scalingIncrementalTargetAnalysis

structure ScalingPairMetrics where
  neuralNodeCount : Nat
  /-- Width of the exact structural profile consumed by the checker. -/
  profileWidth : Nat
  causalGraphNodeCount : Nat
  causalGraphEdgeCount : Nat
  affectedConeCount : Nat
  transportedFragmentCount : Nat
  recomputedFragmentCount : Nat
  deriving DecidableEq, Repr

def scalingPairMetrics
    {current : CheckedAgent scalingMetaContract ()}
    {update : ScalingReceivedArtifact}
    (analysis : ScalingIncrementalLocalConditions current update) :
    ScalingPairMetrics :=
  let targetKeys := analysis.graph.targetKeys
  let affected := affectedConstitutiveCone current.certificate analysis.graph
  let transported := analysis.graph.targetObservations.filter (fun entry =>
    !(affectedConstitutiveNode current.certificate analysis.graph
      (.artifactNode entry.1)))
  let recomputed := analysis.graph.targetObservations.filter (fun entry =>
    affectedConstitutiveNode current.certificate analysis.graph
      (.artifactNode entry.1))
  { neuralNodeCount := update.size + 2
    profileWidth := analysis.graph.targetObservations.length
    causalGraphNodeCount := targetKeys.length
    causalGraphEdgeCount := analysis.graph.dependencyEdges.length
    affectedConeCount := affected.length
    transportedFragmentCount := transported.length
    recomputedFragmentCount := recomputed.length }

structure ScalingPairedCheckResult
    (size : Nat) (version : ScalingArtifactVersion) : Type 7 where
  current : CheckedAgent scalingMetaContract ()
  incremental : GenericIncrementalCheckSuccess
    (scalingIncrementalCheckerEngine current)
    (scalingTargetArtifact size version)
  full : FullRecheckSuccess (scalingFullRecheckEngine current)
    (scalingTargetArtifact size version)
  successorExact : incremental.checked.next = full.checked.next
  metrics : ScalingPairMetrics
  metricsExact : metrics = scalingPairMetrics incremental.analysis

/-- Paired execution from one exact master state.  Both checker paths consume
the same received artifact, and the resulting successor is identified in the
type rather than compared after measurement. -/
structure ScalingPairedStepResult
    (current : CheckedAgent scalingMetaContract ())
    (update : ScalingReceivedArtifact) : Type 7 where
  incremental : GenericIncrementalCheckSuccess
    (scalingIncrementalCheckerEngine current) update
  full : FullRecheckSuccess (scalingFullRecheckEngine current) update
  successorExact : incremental.checked.next = full.checked.next
  metrics : ScalingPairMetrics
  metricsExact : metrics = scalingPairMetrics incremental.analysis

def checkScalingStep
    (current : CheckedAgent scalingMetaContract ())
    (update : ScalingReceivedArtifact) :
    Except ScalingCheckerError (ScalingPairedStepResult current update) :=
  match checkGenericIncrementalUpdate
      (scalingIncrementalCheckerEngine current) update with
  | .error problem => .error problem
  | .ok incremental =>
      match checkFullUpdate (scalingFullRecheckEngine current) update with
      | .error problem => .error problem
      | .ok full =>
          .ok
            { incremental := incremental
              full := full
              successorExact := rfl
              metrics := scalingPairMetrics incremental.analysis
              metricsExact := rfl }

def checkScalingPair (size : Nat) (version : ScalingArtifactVersion) :
    Except ScalingCheckerError (ScalingPairedCheckResult size version) :=
  match checkScalingInitial size with
  | .error _ => .error .initial
  | .ok initialized =>
      let current := initialized.checkedAgent
      match checkScalingStep current (scalingTargetArtifact size version) with
      | .error problem => .error problem
      | .ok checked =>
          .ok
            { current := current
              incremental := checked.incremental
              full := checked.full
              successorExact := checked.successorExact
              metrics := checked.metrics
              metricsExact := checked.metricsExact }

/-- Pre-run parameters of one generated checker-family member.  `size`
controls the causal-chain length; `traceLength` controls how many accepted
updates are checked successively from the one initialized master state. -/
structure ScalingFamilyParameters where
  size : Nat
  traceLength : Nat
  deriving DecidableEq, Repr

/-- The fixed schedule contains both local and upstream changes.  Returning to
the source between them makes the corresponding cone sizes directly
comparable on the same generated family member. -/
def scalingVersionAt : Nat -> ScalingArtifactVersion
  | 0 => .local
  | 1 => .source
  | 2 => .extended
  | step + 3 => scalingVersionAt step

structure ScalingStepObservation where
  step : Nat
  version : ScalingArtifactVersion
  metrics : ScalingPairMetrics
  deriving Repr

structure ScalingTraceResult (parameters : ScalingFamilyParameters) where
  observations : List ScalingStepObservation
  lengthExact : observations.length = parameters.traceLength

def checkScalingTraceFrom
    (size step : Nat)
    (current : CheckedAgent scalingMetaContract ()) :
    (remaining : Nat) ->
      Except ScalingCheckerError
        { observations : List ScalingStepObservation //
          observations.length = remaining }
  | 0 => .ok ⟨[], rfl⟩
  | remaining + 1 =>
      let version := scalingVersionAt step
      let target := scalingTargetArtifact size version
      match checkScalingStep current target with
      | .error problem => .error problem
      | .ok checked =>
          match checkScalingTraceFrom size (step + 1)
              checked.incremental.checked.next remaining with
          | .error problem => .error problem
          | .ok tail =>
              .ok
                ⟨{ step := step
                   version := version
                   metrics := checked.metrics } :: tail.1,
                  congrArg Nat.succ tail.2⟩

/-- Execute the complete parameterized family member: one initialization,
then paired incremental/full checks for every generated update. -/
def checkScalingFamily (parameters : ScalingFamilyParameters) :
    Except ScalingCheckerError (ScalingTraceResult parameters) :=
  match checkScalingInitial parameters.size with
  | .error _ => .error .initial
  | .ok initialized =>
      match checkScalingTraceFrom parameters.size 0 initialized.checkedAgent
          parameters.traceLength with
      | .error problem => .error problem
      | .ok observations =>
          .ok
            { observations := observations.1
              lengthExact := observations.2 }

def scalingFamilyMetrics
    (parameters : ScalingFamilyParameters) :
    Except ScalingCheckerError (List ScalingStepObservation) :=
  match checkScalingFamily parameters with
  | .error problem => .error problem
  | .ok result => .ok result.observations

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.NeuralAgent.scalingContract
#print axioms ConstitutiveSearch.NeuralAgent.scalingProgram
#print axioms ConstitutiveSearch.NeuralAgent.scalingSystem
#print axioms ConstitutiveSearch.NeuralAgent.scalingDecodedArtifact
#print axioms ConstitutiveSearch.NeuralAgent.descendingSerialLayout
#print axioms ConstitutiveSearch.NeuralAgent.scalingStableNaming
#print axioms ConstitutiveSearch.NeuralAgent.scalingCausalRole
#print axioms ConstitutiveSearch.NeuralAgent.scalingFiniteCausalBasis
#print axioms ConstitutiveSearch.NeuralAgent.scalingStateCertificate
#print axioms ConstitutiveSearch.NeuralAgent.scalingMetaContract
#print axioms ConstitutiveSearch.NeuralAgent.scalingExecutableInterface
#print axioms ConstitutiveSearch.NeuralAgent.checkScalingInitial
#print axioms ConstitutiveSearch.NeuralAgent.scalingFullRecheckEngine
#print axioms ConstitutiveSearch.NeuralAgent.scalingIncrementalCheckerEngine
#print axioms ConstitutiveSearch.NeuralAgent.checkScalingStep
#print axioms ConstitutiveSearch.NeuralAgent.checkScalingPair
#print axioms ConstitutiveSearch.NeuralAgent.ScalingFamilyParameters
#print axioms ConstitutiveSearch.NeuralAgent.checkScalingFamily
/- AXIOM_AUDIT_END -/
