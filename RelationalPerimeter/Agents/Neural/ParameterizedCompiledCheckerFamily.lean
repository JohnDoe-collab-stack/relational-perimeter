import RelationalPerimeter.Agents.Neural.IncrementalChecker

/-!
# Parameterized family for the compiled constitutive checker

This module builds a genuine family of native artifacts whose chronological
neural graph grows with the parameter.  It is not a repetition counter around
the fixed public example.  Every member is consumed through the generic
compiled initial, incremental, and full-reference checker interfaces.

The family is an experimental workload.  Its operational contract carries
the same seven distinct classes of substantive certificate obligation as the
compiled checker architecture.  It does not replace the independent learned
artifact or the public alignment instance.  It exists to compare the two
checker paths on the same growing artifact, complete certificate property,
and executed transition.
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

/-! ## Substantive obligations measured by the family

The parameterized family used to place `Unit` in all seven semantic fragments.
That was sufficient for structural checker tests, but it was not a measurement
of the complete certificate property.  The following obligations are indexed
by the exact decoded state.  Their witnesses consume the requirement encoding,
one executed causal role, the produced action and effect, the incorporated
authorization, every requested finite continuation, and the exact native run.
-/

structure ScalingRequirementEncodingWitness
    (state : ReconfiguredExecutionState publicRequirementFamily) : Type 3 where
  incorporation : RequirementIncorporation publicRequirementEncoding state.input
  port : Fin state.system.inputCount
  encodedValue : Activation
  encodedExact :
    encodedValue = (state.system.run state.input).inputs.read port

structure ScalingExecutedCausalWitness
    (state : ReconfiguredExecutionState publicRequirementFamily) : Type 3 where
  port : Fin state.system.inputCount
  role : CausalRole state.system state.input (.receivedInput port)

structure ScalingActionWitness
    (state : ReconfiguredExecutionState publicRequirementFamily) : Type 3 where
  private mk ::
  request : Agent.Request
  requestExact : request = publicAgentActionChannel.command
    (state.system.proposal state.input)
  result : Agent.Memory × Agent.Event
  evidence : Agent.RequestEvidence state.memory request result
  resultExact : result = Agent.executeInput state.memory request

def executeScalingAction
    (state : ReconfiguredExecutionState publicRequirementFamily) :
    ScalingActionWitness state :=
  let request := publicAgentActionChannel.command
    (state.system.proposal state.input)
  let produced := Agent.executeProducedInput state.memory request
  .mk request rfl produced.1 produced.2 rfl

structure ScalingAuthorizationWitness
    (state : ReconfiguredExecutionState publicRequirementFamily) : Type 3 where
  incorporated : IncorporatedReconfigurationPermission
    publicRequirementFamily publicReconfigurationBuilder.permissionVariable
      state.input

structure ScalingEffectWitness
    (state : ReconfiguredExecutionState publicRequirementFamily) : Type 3 where
  action : ScalingActionWitness state
  successor : Agent.Memory
  event : Agent.Event
  successorExact : successor = action.result.1
  eventExact : event = action.result.2

def produceScalingEffect
    (state : ReconfiguredExecutionState publicRequirementFamily) :
    ScalingEffectWitness state :=
  let action := executeScalingAction state
  { action := action
    successor := action.result.1
    event := action.result.2
    successorExact := rfl
    eventExact := rfl }

structure ScalingCoveredFutureStatement : Type 3 where
  state : ReconfiguredExecutionState publicRequirementFamily
  requests : List PublicRequirementInput

def scalingCoveredFutureObligations : ContractObligationFamily where
  Statement := ScalingCoveredFutureStatement
  Witness := fun statement =>
    InteractionHistory publicRequirementIncorporation
      publicRequirementSignalTransformation publicAgentActionChannel
      statement.state.memory statement.requests

structure ScalingHistoricalWitness
    (state : ReconfiguredExecutionState publicRequirementFamily) : Type 3 where
  run : NativeRun state.system.program
  runExact : run = state.system.run state.input

def scalingStateObligation
    (Witness : ReconfiguredExecutionState publicRequirementFamily -> Type 3) :
    ContractObligationFamily where
  Statement := ULift.{3}
    (ReconfiguredExecutionState publicRequirementFamily)
  Witness := fun state => Witness state.down

def scalingRequirementEncodingObligations : ContractObligationFamily :=
  scalingStateObligation ScalingRequirementEncodingWitness

def scalingCausalObligations : ContractObligationFamily :=
  scalingStateObligation ScalingExecutedCausalWitness

def scalingActionObligations : ContractObligationFamily :=
  scalingStateObligation ScalingActionWitness

def scalingAuthorizationObligations : ContractObligationFamily :=
  scalingStateObligation ScalingAuthorizationWitness

def scalingEffectObligations : ContractObligationFamily :=
  scalingStateObligation ScalingEffectWitness

def scalingHistoricalObligations : ContractObligationFamily :=
  scalingStateObligation ScalingHistoricalWitness

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
  FutureSource := ReconfiguredExecutionState publicRequirementFamily
  FutureInput := ULift.{3} Agent.Request
  FutureEvent := Agent.Event
  FutureObservation := OperationalMemoryReadout
  futureContract := reconfiguredOperationalStateFutureContract
    (family := publicRequirementFamily)
  futureSourceOfState := fun state => state
  requirementEncoding := scalingRequirementEncodingObligations
  requirementEncodingAt := fun state => ULift.up state
  causalCondition := scalingCausalObligations
  causalConditionAt := fun state => ULift.up state
  proposalActionPreservation := scalingActionObligations
  proposalActionPreservationAt := fun state => ULift.up state
  authorizationAdmission := scalingAuthorizationObligations
  authorizationAdmissionAt := fun state => ULift.up state
  effectSatisfaction := scalingEffectObligations
  effectSatisfactionAt := fun state => ULift.up state
  coveredFuture := scalingCoveredFutureObligations
  coveredFutureAt := fun state requests =>
    { state := state, requests := requests }
  historicalPolicy := scalingHistoricalObligations
  historicalPolicyAt := fun state => ULift.up state

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

def scalingFinalNeuron (prior : Nat) :
    ScalingArtifactVersion -> NeuronSpec 1 (prior + 1)
  | .source =>
      { inputs :=
          [{ source := .receivedInput publicRequirementPort, weight := 1 },
           { source := .priorNeuron (Fin.last prior), weight := 1 }]
        bias := 0
        threshold := ⟨4⟩ }
  | .local =>
      { inputs :=
          [{ source := .receivedInput publicRequirementPort, weight := 1 },
           { source := .priorNeuron (Fin.last prior), weight := 2 }]
        bias := 0
        threshold := ⟨4⟩ }
  | .extended =>
      { inputs :=
          [{ source := .receivedInput publicRequirementPort, weight := 1 },
           { source := .priorNeuron (Fin.last prior), weight := 1 }]
        bias := 0
        threshold := ⟨4⟩ }

def scalingPrefix (base : NeuronSpec 1 0) :
    (extra : Nat) -> NetworkProgram 1 (extra + 1)
  | 0 => .extend .empty base
  | extra + 1 => .extend (scalingPrefix base extra) (scalingTailNeuron extra)

def scalingProgram (size : Nat) :
    ScalingArtifactVersion -> NetworkProgram 1 (size + 2)
  | .source =>
      .extend (scalingPrefix (scalingBaseNeuron .source) size)
        (scalingFinalNeuron size .source)
  | .local =>
      .extend (scalingPrefix (scalingBaseNeuron .local) size)
        (scalingFinalNeuron size .local)
  | .extended =>
      .extend (scalingPrefix (scalingBaseNeuron .extended) size)
        (scalingFinalNeuron size .extended)

def scalingFirstNeuron (size : Nat) : Fin (size + 2) :=
  ⟨0, Nat.zero_lt_succ (size + 1)⟩

def scalingLastNeuron (size : Nat) : Fin (size + 2) :=
  Fin.last (size + 1)

def scalingOutputs (size : Nat) : OutputPorts (size + 2) where
  sources := [scalingLastNeuron size]
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

theorem scalingProgram_neuronAt_last
    (size : Nat) (version : ScalingArtifactVersion) :
    (scalingProgram size version).neuronAt (scalingLastNeuron size) =
      scalingFinalNeuron size version := by
  have lastNotBefore :
      ¬(scalingLastNeuron size).val < size + 1 := by
    unfold scalingLastNeuron
    exact Nat.lt_irrefl (size + 1)
  cases version <;>
    unfold scalingProgram NetworkProgram.neuronAt <;>
    rw [dif_neg lastNotBefore]

theorem executeProgram_extend_exact
    (prior : NetworkProgram inputCount produced)
    (neuron : NeuronSpec inputCount produced)
    (inputs : SizedActivations inputCount) :
    executeProgram (.extend prior neuron) inputs =
      SizedActivations.snoc (executeProgram prior inputs)
        (fireNeuron neuron inputs (executeProgram prior inputs)) := by
  rfl

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

theorem scalingTailOutput_zero
    (size : Nat) (inputs : SizedActivations 1)
    (prior : SizedActivations (size + 1))
    (priorExact : prior.read (Fin.last size) = 0) :
    fireNeuron (scalingTailNeuron size) inputs prior = 0 := by
  change
    asActivation (fires ⟨1⟩
      (prior.read (Fin.last size) * 1 + 0 + 0)) = 0
  rw [priorExact]
  rfl

theorem scalingTailOutput_one
    (size : Nat) (inputs : SizedActivations 1)
    (prior : SizedActivations (size + 1))
    (priorExact : prior.read (Fin.last size) = 1) :
    fireNeuron (scalingTailNeuron size) inputs prior = 1 := by
  change
    asActivation (fires ⟨1⟩
      (prior.read (Fin.last size) * 1 + 0 + 0)) = 1
  rw [priorExact]
  rfl

theorem scalingFinalOutput_zero
    (size : Nat) (version : ScalingArtifactVersion)
    (inputs : SizedActivations 1)
    (prior : SizedActivations (size + 1))
    (inputExact : inputs.read publicRequirementPort = 2)
    (priorExact : prior.read (Fin.last size) = 0) :
    fireNeuron (scalingFinalNeuron size version) inputs prior = 0 := by
  cases version
  · change
      asActivation (fires ⟨4⟩
        (inputs.read publicRequirementPort * 1 +
          (prior.read (Fin.last size) * 1 + 0) + 0)) = 0
    rw [inputExact, priorExact]
    rfl
  · change
      asActivation (fires ⟨4⟩
        (inputs.read publicRequirementPort * 1 +
          (prior.read (Fin.last size) * 2 + 0) + 0)) = 0
    rw [inputExact, priorExact]
    rfl
  · change
      asActivation (fires ⟨4⟩
        (inputs.read publicRequirementPort * 1 +
          (prior.read (Fin.last size) * 1 + 0) + 0)) = 0
    rw [inputExact, priorExact]
    rfl

theorem scalingFinalOutput_one
    (size : Nat) (version : ScalingArtifactVersion)
    (inputs : SizedActivations 1)
    (prior : SizedActivations (size + 1))
    (inputExact : inputs.read publicRequirementPort = 3)
    (priorExact : prior.read (Fin.last size) = 1) :
    fireNeuron (scalingFinalNeuron size version) inputs prior = 1 := by
  cases version
  · change
      asActivation (fires ⟨4⟩
        (inputs.read publicRequirementPort * 1 +
          (prior.read (Fin.last size) * 1 + 0) + 0)) = 1
    rw [inputExact, priorExact]
    rfl
  · change
      asActivation (fires ⟨4⟩
        (inputs.read publicRequirementPort * 1 +
          (prior.read (Fin.last size) * 2 + 0) + 0)) = 1
    rw [inputExact, priorExact]
    rfl
  · change
      asActivation (fires ⟨4⟩
        (inputs.read publicRequirementPort * 1 +
          (prior.read (Fin.last size) * 1 + 0) + 0)) = 1
    rw [inputExact, priorExact]
    rfl

/-- The received input change is insufficient by itself: with the intervened
input but without the value carried through the generated causal chain, the
final neuron still does not fire.  Together with `scalingFinalOutput_one`,
this makes the preceding chain operationally necessary for the measured
output, rather than irrelevant size padding. -/
theorem scalingFinalWithoutPrior_zero
    (size : Nat) (version : ScalingArtifactVersion)
    (inputs : SizedActivations 1)
    (prior : SizedActivations (size + 1))
    (inputExact : inputs.read publicRequirementPort = 3)
    (priorExact : prior.read (Fin.last size) = 0) :
    fireNeuron (scalingFinalNeuron size version) inputs prior = 0 := by
  cases version
  · change
      asActivation (fires ⟨4⟩
        (inputs.read publicRequirementPort * 1 +
          (prior.read (Fin.last size) * 1 + 0) + 0)) = 0
    rw [inputExact, priorExact]
    rfl
  · change
      asActivation (fires ⟨4⟩
        (inputs.read publicRequirementPort * 1 +
          (prior.read (Fin.last size) * 2 + 0) + 0)) = 0
    rw [inputExact, priorExact]
    rfl
  · change
      asActivation (fires ⟨4⟩
        (inputs.read publicRequirementPort * 1 +
          (prior.read (Fin.last size) * 1 + 0) + 0)) = 0
    rw [inputExact, priorExact]
    rfl

theorem scalingPrefixLast_original
    (size : Nat) (version : ScalingArtifactVersion) :
    (executeProgram
      (scalingPrefix (scalingBaseNeuron version) size)
      (encodePublicRequirement scalingInput)).read (Fin.last size) = 0 := by
  induction size with
  | zero => cases version <;> rfl
  | succ size ih =>
      unfold scalingPrefix
      rw [executeProgram_extend_exact, SizedActivations.read_snoc_last]
      exact scalingTailOutput_zero size _ _ ih

theorem scalingPrefixLast_intervened
    (size : Nat) (version : ScalingArtifactVersion) :
    (executeProgram
      (scalingPrefix (scalingBaseNeuron version) size)
      ((encodePublicRequirement scalingInput).replace
        publicRequirementPort 3)).read (Fin.last size) = 1 := by
  induction size with
  | zero => cases version <;> rfl
  | succ size ih =>
      unfold scalingPrefix
      rw [executeProgram_extend_exact, SizedActivations.read_snoc_last]
      exact scalingTailOutput_one size _ _ ih

theorem scalingLastOutput_original
    (size : Nat) (version : ScalingArtifactVersion) :
    ((scalingSystem size version).run scalingInput).activations.read
      (scalingLastNeuron size) = 0 := by
  change
    (executeProgram (scalingProgram size version)
      (encodePublicRequirement scalingInput)).read
        (scalingLastNeuron size) = 0
  cases version <;>
    unfold scalingProgram scalingLastNeuron <;>
    rw [executeProgram_extend_exact, SizedActivations.read_snoc_last]
  all_goals
    apply scalingFinalOutput_zero
    · rfl
    · exact scalingPrefixLast_original size _

theorem scalingLastOutput_intervened
    (size : Nat) (version : ScalingArtifactVersion) :
    (executeIntervened (scalingIntervention size version)).read
      (scalingLastNeuron size) = 1 := by
  change
    (executeProgram (scalingProgram size version)
      ((encodePublicRequirement scalingInput).replace
        publicRequirementPort 3)).read
          (scalingLastNeuron size) = 1
  cases version <;>
    unfold scalingProgram scalingLastNeuron <;>
    rw [executeProgram_extend_exact, SizedActivations.read_snoc_last]
  all_goals
    apply scalingFinalOutput_one
    · rfl
    · exact scalingPrefixLast_intervened size _

def scalingLastEdge
    (size : Nat) (version : ScalingArtifactVersion) :
    EffectiveReadsFrom ((scalingSystem size version).run scalingInput)
      (.receivedInput publicRequirementPort)
      (.neuronOutput (scalingLastNeuron size)) := by
  cases version
  · exact .executedEdge (scalingLastNeuron size)
      { source := .receivedInput publicRequirementPort, weight := 1 }
      (by
        change
          ({ source := .receivedInput publicRequirementPort, weight := 1 } :
            WeightedInput 1 (size + 1)) ∈
            ((scalingProgram size .source).neuronAt
              (scalingLastNeuron size)).inputs
        rw [scalingProgram_neuronAt_last]
        exact List.Mem.head _)
      (show (1 : Int) ≠ 0 by decide)
  · exact .executedEdge (scalingLastNeuron size)
      { source := .receivedInput publicRequirementPort, weight := 1 }
      (by
        change
          ({ source := .receivedInput publicRequirementPort, weight := 1 } :
            WeightedInput 1 (size + 1)) ∈
            ((scalingProgram size .local).neuronAt
              (scalingLastNeuron size)).inputs
        rw [scalingProgram_neuronAt_last]
        exact List.Mem.head _)
      (show (1 : Int) ≠ 0 by decide)
  · exact .executedEdge (scalingLastNeuron size)
      { source := .receivedInput publicRequirementPort, weight := 1 }
      (by
        change
          ({ source := .receivedInput publicRequirementPort, weight := 1 } :
            WeightedInput 1 (size + 1)) ∈
            ((scalingProgram size .extended).neuronAt
              (scalingLastNeuron size)).inputs
        rw [scalingProgram_neuronAt_last]
        exact List.Mem.head _)
      (show (1 : Int) ≠ 0 by decide)

theorem scalingLastOutput_changed
    (size : Nat) (version : ScalingArtifactVersion) :
    OccurrenceChanged (scalingIntervention size version)
      (.neuronOutput (scalingLastNeuron size)) :=
  { different := by
      simp only [intervenedValue, ActivationOccurrence.value]
      rw [scalingLastOutput_intervened, scalingLastOutput_original]
      decide }

def scalingPropagation
    (size : Nat) (version : ScalingArtifactVersion) :
    NontrivialExecutedChangePath (scalingIntervention size version)
      (.neuronOutput (scalingLastNeuron size)) :=
  let edge : EffectiveReadsFrom
      ((scalingSystem size version).run scalingInput)
      (scalingIntervention size version).focusOccurrence
      (.neuronOutput (scalingLastNeuron size)) :=
    Eq.mp
      (congrArg
        (fun source => EffectiveReadsFrom
          ((scalingSystem size version).run scalingInput) source
          (.neuronOutput (scalingLastNeuron size)))
        (scalingIntervention_focus_exact size version).symm)
      (scalingLastEdge size version)
  .step .origin edge (scalingLastOutput_changed size version)

theorem scalingTarget_changed
    (size : Nat) (version : ScalingArtifactVersion) :
    ChangesTarget ((scalingSystem size version).run scalingInput)
      (scalingIntervention size version) (scalingOutputs size) :=
  { different := by
      change
        [(executeIntervened (scalingIntervention size version)).read
          (scalingLastNeuron size)] ≠
        [((scalingSystem size version).run scalingInput).activations.read
          (scalingLastNeuron size)]
      rw [scalingLastOutput_intervened, scalingLastOutput_original]
      decide }

theorem scalingProposal_changed
    (size : Nat) (version : ScalingArtifactVersion) :
    ChangesProposal (scalingSystem size version) scalingInput
      (scalingIntervention size version) :=
  { different := by
      change
        decodePublicRequirement
            [(executeIntervened (scalingIntervention size version)).read
              (scalingLastNeuron size)] ≠
          decodePublicRequirement
            [((scalingSystem size version).run scalingInput).activations.read
              (scalingLastNeuron size)]
      rw [scalingLastOutput_intervened, scalingLastOutput_original]
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
  ReducedMemory := Agent.Memory
  reducedContract := reconfiguredOperationalMemoryFutureContract
  project := ReconfiguredExecutionState.memory
  simulation := FutureContractSimulationData.ofExactRealization
    (reconfiguredOperationalMemoryRealization
      (family := publicRequirementFamily))

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
    requirement :=
      { witness :=
          { incorporation := publicRequirementIncorporation scalingInput
            port := publicRequirementPort
            encodedValue := 2
            encodedExact := rfl } }
    causal :=
      { witness :=
          { port := publicRequirementPort
            role := scalingCausalRole size version } }
    proposalAction :=
      { witness := executeScalingAction (scalingState size version) }
    authorization :=
      { witness :=
          { incorporated := publicReconfigurationAuthorization scalingInput } }
    effect :=
      { witness := produceScalingEffect (scalingState size version) }
    historical :=
      { witness :=
          { run := (scalingState size version).system.run
              (scalingState size version).input
            runExact := rfl } }
    futures :=
      { covered := fun requests =>
          publicInteractionHistory (scalingState size version).memory requests
        realization := scalingFutureRealization } }

/-- Semantic obligations recalculated for the exact scaling target.  This
package deliberately omits the structural snapshot: that component is
constructed later from the incremental transport/recompute assembly. -/
def scalingRecomputedCertificateFragments
    (size : Nat) (version : ScalingArtifactVersion) :
    RecomputedStateCertificateFragments scalingContract
      (scalingDecodedArtifact size version) (scalingState size version) :=
  let fragments := scalingStateFragments size version
  { requirement := fragments.requirement
    causal := fragments.causal
    proposalAction := fragments.proposalAction
    authorization := fragments.authorization
    effect := fragments.effect
    historical := fragments.historical
    futures := fragments.futures }

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
  requirementDecision := fun {source} _ =>
    scalingReflectedTrue
      { incorporation := publicRequirementIncorporation
          (scalingState source.size source.version).input
        port := publicRequirementPort
        encodedValue := 2
        encodedExact := rfl }
  contextDecision := fun {source} _ =>
    scalingReflectedTrue
      { port := publicRequirementPort
        role := scalingCausalRole source.size source.version }
  authorizationDecision := fun {source} _ =>
    scalingReflectedTrue
      { incorporated := publicReconfigurationAuthorization
          (scalingState source.size source.version).input }
  actionDecision := fun {source} _ =>
    scalingReflectedTrue
      (executeScalingAction (scalingState source.size source.version))
  effectDecision := fun {source} _ =>
    scalingReflectedTrue
      (produceScalingEffect (scalingState source.size source.version))
  historicalDecision := fun {source} _ =>
    scalingReflectedTrue
      { run := (scalingState source.size source.version).system.run
          (scalingState source.size source.version).input
        runExact := rfl }
  coveredFuturesDecision := fun {source} _ =>
    scalingReflectedTrue (fun requests =>
      publicInteractionHistory
        (scalingState source.size source.version).memory requests)
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

/-- The incremental path decodes the received target without certifying its
complete state first.  This receipt contains only the value returned by the
artifact decoder and the equation tying it to the exact received update. -/
structure ScalingIncrementalDecodedTarget
    (update : ScalingReceivedArtifact) : Type 5 where
  decodedArtifact : scalingExecutableInterface.DecodedArtifact
    update
  decodedExact :
    scalingExecutableInterface.decodeReceivedArtifact update =
      .ok decodedArtifact

/-- Target decoding is a local pre-certificate check.  In particular this
function does not call `checkInitial`, `checkInitialState`, or either complete
recheck interface. -/
def decodeScalingIncrementalTarget
    (update : ScalingReceivedArtifact) :
    Except ScalingCheckerError (ScalingIncrementalDecodedTarget update) :=
  match exact : scalingExecutableInterface.decodeReceivedArtifact update with
  | .error _ => .error .target
  | .ok decoded => .ok { decodedArtifact := decoded, decodedExact := exact }

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

/-- The exact graph calculated from the certified source and the stable naming
decoded from the received target.  It is a function of the two checker inputs,
not a graph supplied by the caller. -/
def scalingIncrementalGraph
    (current : CheckedAgent scalingMetaContract ())
    {update : ScalingReceivedArtifact}
    (target : ScalingIncrementalDecodedTarget update) :
    PreCertificateConstitutiveGraph
      current.certificate.basis.naming
      (scalingExecutableInterface.decodedStableNaming
        target.decodedArtifact).naming :=
  calculatePreCertificateConstitutiveGraph
    current.certificate.basis.naming
    (scalingExecutableInterface.decodedStableNaming
      target.decodedArtifact).naming

/-- Reusable occurrences selected from the exact current certificate by the
calculated version correspondence and affected cone. -/
def scalingIncrementalTransportLicenses
    (current : CheckedAgent scalingMetaContract ())
    {update : ScalingReceivedArtifact}
    (target : ScalingIncrementalDecodedTarget update) :
    List (LicensedStructuralTransport current.certificate
      (scalingIncrementalGraph current target)) :=
  calculateLicensedStructuralTransports current.certificate
    (scalingIncrementalGraph current target)

def scalingIncrementalTransported
    (current : CheckedAgent scalingMetaContract ())
    {update : ScalingReceivedArtifact}
    (target : ScalingIncrementalDecodedTarget update) :
    List (StableNodeKey × StableArtifactObservation) :=
  licensedStructuralEntries
    (scalingIncrementalTransportLicenses current target)

/-- The target observations selected for direct recalculation by the
calculated pre-certificate graph.  A complete target snapshot is not built on
the incremental path. -/
def scalingIncrementalRecomputed
    (current : CheckedAgent scalingMetaContract ())
    {update : ScalingReceivedArtifact}
    (target : ScalingIncrementalDecodedTarget update) :
    List (StableNodeKey × StableArtifactObservation) :=
  recomputeAffectedStructuralObservations current.certificate
    (scalingExecutableInterface.decodedStableNaming
      target.decodedArtifact).naming
    (scalingIncrementalGraph current target)

/-- One named executable boundary for the structural calculation.  Keeping
this calculation distinct from its later certificate makes its receipt a
local condition rather than a preassembled target certificate. -/
def calculateScalingIncrementalStructuralAssembly
    (current : CheckedAgent scalingMetaContract ())
    {update : ScalingReceivedArtifact}
    (target : ScalingIncrementalDecodedTarget update) :=
  calculateIncrementalStructuralAssembly current.certificate
    (scalingIncrementalGraph current target)
    (scalingIncrementalTransported current target)
    (scalingIncrementalRecomputed current target)

/-- Execute only the structural assembly subcheck.  Its successful value is
the certificate of that local calculation, not an incremental checker
result. -/
def checkScalingIncrementalStructuralAssembly
    (current : CheckedAgent scalingMetaContract ())
    {update : ScalingReceivedArtifact}
    (target : ScalingIncrementalDecodedTarget update) :
    Except ScalingCheckerError
      (CalculatedIncrementalStructuralAssembly current.certificate
        (scalingIncrementalGraph current target)
        (scalingIncrementalTransported current target)
        (scalingIncrementalRecomputed current target)) :=
  let graph := scalingIncrementalGraph current target
  match calculated :
      calculateScalingIncrementalStructuralAssembly current target with
  | .error _ => .error .structuralAssembly
  | .ok observations =>
      if targetExact : observations = graph.targetObservations then
        .ok (certifyCalculatedIncrementalStructuralAssembly
          calculated targetExact)
      else
        .error .structuralMismatch

/-- Positive output of the parameterized analyzer.  Receipts of the smaller
checks do not live here: they belong to the autonomous specification below. -/
structure ScalingIncrementalAnalysis
    (current : CheckedAgent scalingMetaContract ())
    (update : ScalingReceivedArtifact) : Type 6 where
  target : ScalingIncrementalDecodedTarget update
  assembly : CalculatedIncrementalStructuralAssembly current.certificate
    (scalingIncrementalGraph current target)
    (scalingIncrementalTransported current target)
    (scalingIncrementalRecomputed current target)
  transitionDecision : AcceptedTransitionDecision scalingExecutableInterface
    { current := ()
      next := scalingExecutableInterface.decodedContract
        target.decodedArtifact }

/-- Autonomous local conditions for the parameterized incremental checker.
Each equation is the receipt of a strictly smaller executable decision:
complete target decoding and admission, structural assembly, or transition
admission.  This type contains neither an incremental analysis result nor an
equation saying that the whole incremental analyzer has already succeeded. -/
structure ScalingIncrementalLocalConditions
    (current : CheckedAgent scalingMetaContract ())
    (update : ScalingReceivedArtifact) : Type 6 where
  target : ScalingIncrementalDecodedTarget update
  targetChecked : decodeScalingIncrementalTarget update = .ok target
  assembly : CalculatedIncrementalStructuralAssembly current.certificate
    (scalingIncrementalGraph current target)
    (scalingIncrementalTransported current target)
    (scalingIncrementalRecomputed current target)
  assemblyChecked :
    checkScalingIncrementalStructuralAssembly current target = .ok assembly
  transitionDecision : AcceptedTransitionDecision scalingExecutableInterface
    { current := ()
      next := scalingExecutableInterface.decodedContract
        target.decodedArtifact }
  transitionAccepted :
    decideDecodedTransition scalingExecutableInterface ()
        target.decodedArtifact = some transitionDecision

def ScalingIncrementalAnalysis.graph
    {current : CheckedAgent scalingMetaContract ()}
    {update : ScalingReceivedArtifact}
    (analysis : ScalingIncrementalAnalysis current update) :=
  scalingIncrementalGraph current analysis.target

def ScalingIncrementalAnalysis.transported
    {current : CheckedAgent scalingMetaContract ()}
    {update : ScalingReceivedArtifact}
    (analysis : ScalingIncrementalAnalysis current update) :=
  scalingIncrementalTransported current analysis.target

def ScalingIncrementalAnalysis.transportedLicenses
    {current : CheckedAgent scalingMetaContract ()}
    {update : ScalingReceivedArtifact}
    (analysis : ScalingIncrementalAnalysis current update) :=
  scalingIncrementalTransportLicenses current analysis.target

def ScalingIncrementalAnalysis.recomputed
    {current : CheckedAgent scalingMetaContract ()}
    {update : ScalingReceivedArtifact}
    (analysis : ScalingIncrementalAnalysis current update) :=
  scalingIncrementalRecomputed current analysis.target

def analyzeScalingIncrementalUpdate
    (current : CheckedAgent scalingMetaContract ())
    (update : ScalingReceivedArtifact) :
    Except ScalingCheckerError
      (ScalingIncrementalAnalysis current update) :=
  match _targetChecked : decodeScalingIncrementalTarget update with
  | .error _ => .error .target
  | .ok target =>
      match checkScalingIncrementalStructuralAssembly current target with
      | .error problem => .error problem
      | .ok assembly =>
        match _transitionAccepted :
            decideDecodedTransition scalingExecutableInterface ()
            target.decodedArtifact with
        | none => .error .transition
        | some transitionDecision =>
            .ok
              { target := target
                assembly := assembly
                transitionDecision := transitionDecision }

/-- Autonomous local decisions are sufficient to replay the analyzer.  The
proof consumes only the three smaller receipts stored above; it never assumes
the success equation that it constructs. -/
def completeScalingIncrementalAnalysis
    (current : CheckedAgent scalingMetaContract ())
    (update : ScalingReceivedArtifact)
    (conditions : ScalingIncrementalLocalConditions current update) :
    { analysis : ScalingIncrementalAnalysis current update //
      analyzeScalingIncrementalUpdate current update =
        .ok analysis } := by
  unfold analyzeScalingIncrementalUpdate
  split
  · have impossible :=
      ‹decodeScalingIncrementalTarget update = .error _›.symm.trans
        conditions.targetChecked
    cases impossible
  · have targetExact : _ = conditions.target :=
      Except.ok.inj
        (‹decodeScalingIncrementalTarget update = .ok _›.symm.trans
          conditions.targetChecked)
    cases targetExact
    rw [conditions.assemblyChecked]
    rw [conditions.transitionAccepted]
    exact ⟨_, rfl⟩

/-- A successful top-level analysis exposes the independent receipts that
made its three local checks succeed. -/
def scalingIncrementalLocalConditionsOfSuccess
    (current : CheckedAgent scalingMetaContract ())
    (update : ScalingReceivedArtifact)
    (analysis : ScalingIncrementalAnalysis current update)
    (accepted : analyzeScalingIncrementalUpdate current update =
      .ok analysis) :
    ScalingIncrementalLocalConditions current update := by
  unfold analyzeScalingIncrementalUpdate at accepted
  split at accepted
  · cases accepted
  · rename_i target targetChecked
    split at accepted
    · cases accepted
    · rename_i assembly assemblyChecked
      split at accepted
      · cases accepted
      · rename_i transitionDecision transitionAccepted
        have analysisExact :
            ({ target := target
               assembly := assembly
               transitionDecision := transitionDecision } :
                ScalingIncrementalAnalysis current update) = analysis :=
          Except.ok.inj accepted
        cases analysisExact
        exact
          { target := target
            targetChecked := targetChecked
            assembly := assembly
            assemblyChecked := assemblyChecked
            transitionDecision := transitionDecision
            transitionAccepted := transitionAccepted }

def scalingIncrementalTargetAnalysis
    {current : CheckedAgent scalingMetaContract ()}
    {update : ScalingReceivedArtifact}
    (conditions : ScalingIncrementalAnalysis current update) :
    IncrementalTargetAnalysis current :=
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
    transportedLicenses := conditions.transportedLicenses
    recomputedStructural := conditions.recomputed
    structuralAssembly := conditions.assembly
    structuralBasis := scalingFiniteCausalBasis update.size update.version
    structuralBasisNamingExact := rfl
    structuralSystemExact := rfl
    structuralInputDeclared := .head
    recomputedCertificateFragments :=
      scalingRecomputedCertificateFragments update.size update.version
    transition := conditions.transitionDecision.transition
    execution := scalingUnit4 }

theorem scalingIncrementalFragments_eq_full
    {current : CheckedAgent scalingMetaContract ()}
    {update : ScalingReceivedArtifact}
    (analysis : ScalingIncrementalAnalysis current update) :
    (scalingIncrementalTargetAnalysis analysis).fragments =
      scalingStateFragments update.size update.version := by
  apply StateCertificateFragments.eq_of_components
  · apply StableStructuralCertificateFragment.eq_of_basis_observations
    · rfl
    · rfl
    · exact analysis.assembly.targetExact
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def scalingIncrementalCheckerEngine
    (current : CheckedAgent scalingMetaContract ()) :
    IncrementalCheckerEngine current where
  Update := ScalingReceivedArtifact
  Error := ScalingCheckerError
  Analysis := fun update => ScalingIncrementalAnalysis current update
  analyze := analyzeScalingIncrementalUpdate current
  LocalConditions := fun update => ScalingIncrementalLocalConditions current update
  complete := completeScalingIncrementalAnalysis current
  localOfSuccess := scalingIncrementalLocalConditionsOfSuccess current
  target := scalingIncrementalTargetAnalysis

theorem analyzeScalingIncrementalUpdate_complete
    (current : CheckedAgent scalingMetaContract ())
    (update : ScalingReceivedArtifact) :
    GenericIncrementalUpdateAccepted
        (scalingIncrementalCheckerEngine current) update ↔
      GenericIncrementalUpdateLocalConditions
        (scalingIncrementalCheckerEngine current) update :=
  checkGenericIncrementalUpdate_complete_for_local_conditions
    (scalingIncrementalCheckerEngine current) update

structure ScalingPairMetrics where
  neuralNodeCount : Nat
  /-- Width of the exact structural profile consumed by the checker. -/
  profileWidth : Nat
  causalGraphNodeCount : Nat
  causalGraphEdgeCount : Nat
  affectedConeCount : Nat
  transportedFragmentCount : Nat
  recomputedFragmentCount : Nat
  /-- Separately reported non-fragment work units: one target decode plus the
  material graph keys, dependency edges, and affected nodes inspected by this
  executable analysis.  This is an accounting convention, not an asymptotic
  running-time or allocation bound. -/
  otherNecessaryCalculationCount : Nat
  deriving DecidableEq, Repr

def scalingPairMetrics
    {current : CheckedAgent scalingMetaContract ()}
    {update : ScalingReceivedArtifact}
    (analysis : ScalingIncrementalAnalysis current update) :
    ScalingPairMetrics :=
  let targetKeys := analysis.graph.targetKeys
  let affected := affectedConstitutiveCone current.certificate analysis.graph
  let structuralKeys := stableStructuralKeys
    (scalingExecutableInterface.decodedStableNaming
      analysis.target.decodedArtifact).naming
  let recomputed := analysis.recomputed
  { neuralNodeCount := update.size + 2
    profileWidth := structuralKeys.length
    causalGraphNodeCount := targetKeys.length
    causalGraphEdgeCount := analysis.graph.dependencyEdges.length
    affectedConeCount := affected.length
    transportedFragmentCount := analysis.transportedLicenses.length
    recomputedFragmentCount := recomputed.length
    otherNecessaryCalculationCount :=
      1 + targetKeys.length + analysis.graph.dependencyEdges.length +
        affected.length }

structure ScalingPairedCheckResult
    (size : Nat) (version : ScalingArtifactVersion) : Type 7 where
  current : CheckedAgent scalingMetaContract ()
  incremental : GenericIncrementalCheckSuccess
    (scalingIncrementalCheckerEngine current)
    (scalingTargetArtifact size version)
  full : FullRecheckSuccess (scalingFullRecheckEngine current)
    (scalingTargetArtifact size version)
  metrics : ScalingPairMetrics
  metricsExact : metrics = scalingPairMetrics incremental.analysis

/-- Paired execution from one exact master state.  Both checker paths consume
the same received artifact.  The full path remains an independent reference;
its result is not an input to the incremental analysis or its metrics. -/
structure ScalingPairedStepResult
    (current : CheckedAgent scalingMetaContract ())
    (update : ScalingReceivedArtifact) : Type 7 where
  incremental : GenericIncrementalCheckSuccess
    (scalingIncrementalCheckerEngine current) update
  full : FullRecheckSuccess (scalingFullRecheckEngine current) update
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
#print axioms ConstitutiveSearch.NeuralAgent.ScalingRequirementEncodingWitness
#print axioms ConstitutiveSearch.NeuralAgent.ScalingExecutedCausalWitness
#print axioms ConstitutiveSearch.NeuralAgent.ScalingActionWitness
#print axioms ConstitutiveSearch.NeuralAgent.executeScalingAction
#print axioms ConstitutiveSearch.NeuralAgent.ScalingAuthorizationWitness
#print axioms ConstitutiveSearch.NeuralAgent.ScalingEffectWitness
#print axioms ConstitutiveSearch.NeuralAgent.produceScalingEffect
#print axioms ConstitutiveSearch.NeuralAgent.ScalingCoveredFutureStatement
#print axioms ConstitutiveSearch.NeuralAgent.ScalingHistoricalWitness
#print axioms ConstitutiveSearch.NeuralAgent.scalingContract
#print axioms ConstitutiveSearch.NeuralAgent.scalingProgram
#print axioms ConstitutiveSearch.NeuralAgent.scalingPrefixLast_original
#print axioms ConstitutiveSearch.NeuralAgent.scalingPrefixLast_intervened
#print axioms ConstitutiveSearch.NeuralAgent.scalingFinalWithoutPrior_zero
#print axioms ConstitutiveSearch.NeuralAgent.scalingLastOutput_original
#print axioms ConstitutiveSearch.NeuralAgent.scalingLastOutput_intervened
#print axioms ConstitutiveSearch.NeuralAgent.scalingLastOutput_changed
#print axioms ConstitutiveSearch.NeuralAgent.scalingPropagation
#print axioms ConstitutiveSearch.NeuralAgent.scalingTarget_changed
#print axioms ConstitutiveSearch.NeuralAgent.scalingProposal_changed
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
#print axioms ConstitutiveSearch.NeuralAgent.ScalingIncrementalDecodedTarget
#print axioms ConstitutiveSearch.NeuralAgent.decodeScalingIncrementalTarget
#print axioms ConstitutiveSearch.NeuralAgent.scalingIncrementalTransportLicenses
#print axioms ConstitutiveSearch.NeuralAgent.scalingIncrementalTransported
#print axioms ConstitutiveSearch.NeuralAgent.scalingRecomputedCertificateFragments
#print axioms ConstitutiveSearch.NeuralAgent.checkScalingIncrementalStructuralAssembly
#print axioms ConstitutiveSearch.NeuralAgent.ScalingIncrementalAnalysis
#print axioms ConstitutiveSearch.NeuralAgent.ScalingIncrementalLocalConditions
#print axioms ConstitutiveSearch.NeuralAgent.completeScalingIncrementalAnalysis
#print axioms ConstitutiveSearch.NeuralAgent.scalingIncrementalLocalConditionsOfSuccess
#print axioms ConstitutiveSearch.NeuralAgent.scalingIncrementalCheckerEngine
#print axioms ConstitutiveSearch.NeuralAgent.scalingIncrementalFragments_eq_full
#print axioms ConstitutiveSearch.NeuralAgent.analyzeScalingIncrementalUpdate_complete
#print axioms ConstitutiveSearch.NeuralAgent.ScalingPairMetrics
#print axioms ConstitutiveSearch.NeuralAgent.scalingPairMetrics
#print axioms ConstitutiveSearch.NeuralAgent.checkScalingStep
#print axioms ConstitutiveSearch.NeuralAgent.checkScalingPair
#print axioms ConstitutiveSearch.NeuralAgent.ScalingFamilyParameters
#print axioms ConstitutiveSearch.NeuralAgent.checkScalingFamily
/- AXIOM_AUDIT_END -/
