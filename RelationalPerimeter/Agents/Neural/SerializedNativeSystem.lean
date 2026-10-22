import RelationalPerimeter.Agents.Neural.OperationalContract

/-!
# Serialized native systems and certified decoding

The received artifact is plain data.  Its decoder validates input arity,
chronological neuron references, output indices, and output non-emptiness
before producing a complete `NativeSystem`.  The input encoder and proposal
decoder come from the already fixed operational contract; the network program
and output ports come only from the serialized artifact.
-/
set_option genInjectivity false
namespace ConstitutiveSearch.NeuralAgent
open NativeMechanism

inductive SerializedSource where
  | receivedInput (index : Nat)
  | priorNeuron (index : Nat)
  deriving DecidableEq

structure SerializedWeightedInput where
  source : SerializedSource
  weight : Int
  deriving DecidableEq

structure SerializedNeuron where
  inputs : List SerializedWeightedInput
  bias : Int
  threshold : Int
  deriving DecidableEq

structure SerializedNetwork where
  inputCount : Nat
  neurons : List SerializedNeuron
  outputs : List Nat
  deriving DecidableEq

inductive ArtifactError where
  | inputCountMismatch
  | invalidReceivedInput
  | invalidPriorNeuron
  | invalidOutput
  | emptyOutputs
  deriving DecidableEq

def serializeSource {inputCount produced : Nat} :
    SourceIndex inputCount produced -> SerializedSource
  | .receivedInput index => .receivedInput index.val
  | .priorNeuron index => .priorNeuron index.val

def serializeWeightedInput {inputCount produced : Nat}
    (edge : WeightedInput inputCount produced) : SerializedWeightedInput :=
  { source := serializeSource edge.source
    weight := edge.weight }

def serializeNeuron {inputCount produced : Nat}
    (neuron : NeuronSpec inputCount produced) : SerializedNeuron :=
  { inputs := neuron.inputs.map serializeWeightedInput
    bias := neuron.bias
    threshold := neuron.threshold.level }

def serializeProgram {inputCount : Nat} :
    {produced : Nat} -> NetworkProgram inputCount produced ->
      List SerializedNeuron
  | _, .empty => []
  | _, .extend prior neuron => serializeProgram prior ++ [serializeNeuron neuron]

/-- Complete serialization of one native system.  This is used by the full
reference checker; no program fragment or output port is omitted. -/
def serializeNativeSystem
    {Input Proposal : Type}
    (system : NativeSystem Input Proposal) : SerializedNetwork :=
  { inputCount := system.inputCount
    neurons := serializeProgram system.program
    outputs := system.outputs.sources.map Fin.val }

theorem serializedAppendNil (values : List SerializedNeuron) :
    values ++ [] = values := by
  induction values with
  | nil => rfl
  | cons head tail ih => exact congrArg (List.cons head) ih

theorem serializedAppendAssoc
    (first second third : List SerializedNeuron) :
    (first ++ second) ++ third = first ++ (second ++ third) := by
  induction first with
  | nil => rfl
  | cons head tail ih => exact congrArg (List.cons head) ih

structure DecodedSource (inputCount produced : Nat)
    (source : SerializedSource) where
  value : SourceIndex inputCount produced
  exact : serializeSource value = source

def decodeSerializedSource (inputCount produced : Nat)
    (source : SerializedSource) :
    Except ArtifactError (DecodedSource inputCount produced source) :=
  match source with
  | .receivedInput index =>
      if within : index < inputCount then
        .ok { value := .receivedInput ⟨index, within⟩, exact := rfl }
      else
        .error .invalidReceivedInput
  | .priorNeuron index =>
      if before : index < produced then
        .ok { value := .priorNeuron ⟨index, before⟩, exact := rfl }
      else
        .error .invalidPriorNeuron

structure DecodedWeightedInput (inputCount produced : Nat)
    (source : SerializedWeightedInput) where
  value : WeightedInput inputCount produced
  exact : serializeWeightedInput value = source

def decodeSerializedWeightedInput (inputCount produced : Nat)
    (source : SerializedWeightedInput) :
    Except ArtifactError (DecodedWeightedInput inputCount produced source) :=
  match decodeSerializedSource inputCount produced source.source with
  | .error problem => .error problem
  | .ok result =>
      .ok
        { value := { source := result.value, weight := source.weight }
          exact := by
            cases source with
            | mk serializedSource weight =>
                change
                  SerializedWeightedInput.mk (serializeSource result.value)
                      weight =
                    SerializedWeightedInput.mk serializedSource weight
                exact congrArg
                  (fun candidate => SerializedWeightedInput.mk candidate weight)
                  result.exact }

structure DecodedWeightedInputs (inputCount produced : Nat)
    (source : List SerializedWeightedInput) where
  values : List (WeightedInput inputCount produced)
  exact : values.map serializeWeightedInput = source

def decodeSerializedWeightedInputs (inputCount produced : Nat) :
    (source : List SerializedWeightedInput) ->
      Except ArtifactError (DecodedWeightedInputs inputCount produced source)
  | [] => .ok { values := [], exact := rfl }
  | edge :: rest =>
      match decodeSerializedWeightedInput inputCount produced edge,
          decodeSerializedWeightedInputs inputCount produced rest with
      | .ok decodedEdge, .ok decodedRest =>
          .ok
            { values := decodedEdge.value :: decodedRest.values
              exact := by
                change serializeWeightedInput decodedEdge.value ::
                    decodedRest.values.map serializeWeightedInput = edge :: rest
                rw [decodedEdge.exact, decodedRest.exact] }
      | .error problem, _ => .error problem
      | _, .error problem => .error problem

structure DecodedNeuron (inputCount produced : Nat)
    (source : SerializedNeuron) where
  value : NeuronSpec inputCount produced
  exact : serializeNeuron value = source

def decodeSerializedNeuron (inputCount produced : Nat)
    (source : SerializedNeuron) :
    Except ArtifactError (DecodedNeuron inputCount produced source) :=
  match decodeSerializedWeightedInputs inputCount produced source.inputs with
  | .error problem => .error problem
  | .ok decoded =>
      .ok
        { value :=
            { inputs := decoded.values
              bias := source.bias
              threshold := ⟨source.threshold⟩ }
          exact := by
            unfold serializeNeuron
            rw [decoded.exact] }

structure DecodedProgramExtension
    {inputCount baseCount : Nat}
    (base : NetworkProgram inputCount baseCount)
    (source : List SerializedNeuron) where
  producedCount : Nat
  program : NetworkProgram inputCount producedCount
  exact : serializeProgram program = serializeProgram base ++ source

def decodeSerializedProgramFrom
    {inputCount baseCount : Nat}
    (base : NetworkProgram inputCount baseCount) :
    (source : List SerializedNeuron) ->
      Except ArtifactError (DecodedProgramExtension base source)
  | [] =>
      .ok
        { producedCount := baseCount
          program := base
          exact := (serializedAppendNil (serializeProgram base)).symm }
  | neuron :: rest =>
      match decodeSerializedNeuron inputCount baseCount neuron with
      | .error problem => .error problem
      | .ok decodedNeuron =>
          match decodeSerializedProgramFrom
              (.extend base decodedNeuron.value) rest with
          | .error problem => .error problem
          | .ok decodedRest =>
              .ok
                { producedCount := decodedRest.producedCount
                  program := decodedRest.program
                  exact := by
                    rw [decodedRest.exact]
                    change (serializeProgram base ++
                      [serializeNeuron decodedNeuron.value]) ++ rest =
                        serializeProgram base ++ neuron :: rest
                    rw [decodedNeuron.exact]
                    rw [serializedAppendAssoc]
                    rfl }

abbrev DecodedProgram (inputCount : Nat) (source : List SerializedNeuron) :=
  DecodedProgramExtension (NetworkProgram.empty : NetworkProgram inputCount 0)
    source

def decodeSerializedProgram (inputCount : Nat)
    (source : List SerializedNeuron) :
    Except ArtifactError (DecodedProgram inputCount source) :=
  decodeSerializedProgramFrom
    (NetworkProgram.empty : NetworkProgram inputCount 0) source

structure DecodedOutputs (produced : Nat) (source : List Nat) where
  values : List (Fin produced)
  exact : values.map Fin.val = source

def decodeSerializedOutputs (produced : Nat) :
    (source : List Nat) -> Except ArtifactError (DecodedOutputs produced source)
  | [] => .ok { values := [], exact := rfl }
  | index :: rest =>
      if within : index < produced then
        match decodeSerializedOutputs produced rest with
        | .error problem => .error problem
        | .ok decoded =>
            .ok
              { values := ⟨index, within⟩ :: decoded.values
                exact := by
                  change index :: decoded.values.map Fin.val = index :: rest
                  rw [decoded.exact] }
      else
        .error .invalidOutput

structure ArtifactDecodingExact
    (contract : ConstitutiveContract)
    (source : SerializedNetwork)
    (system : NativeSystem (RequirementInput contract.family)
      contract.Proposal) : Type 4 where
  inputCountExact : source.inputCount = system.inputCount
  contractInputCountExact : system.inputCount = contract.inputCount
  neuronsExact : serializeProgram system.program = source.neurons
  outputsExact : system.outputs.sources.map Fin.val = source.outputs
  encodingExact : forall input,
    contractInputCountExact ▸ system.encode input = contract.encode input
  decoderExact : forall values, system.decode values = contract.decode values

structure DecodedNeuralArtifact (contract : ConstitutiveContract) : Type 4 where
  private mk ::
  source : SerializedNetwork
  system : NativeSystem (RequirementInput contract.family) contract.Proposal
  decodingExact : ArtifactDecodingExact contract source system

/-- Construct a decoded artifact from a complete positive decoding witness.
This is the constructive boundary used by generated artifact families: the
caller must supply the same equations that the byte decoder reconstructs, so
no unchecked native system can be relabelled as decoded. -/
def certifyDecodedNeuralArtifact
    (contract : ConstitutiveContract)
    (source : SerializedNetwork)
    (system : NativeSystem (RequirementInput contract.family)
      contract.Proposal)
    (exact : ArtifactDecodingExact contract source system) :
    DecodedNeuralArtifact contract :=
  .mk source system exact

def decodeArtifact (contract : ConstitutiveContract)
    (source : SerializedNetwork) :
    Except ArtifactError (DecodedNeuralArtifact contract) :=
  if inputExact : source.inputCount = contract.inputCount then
    match decodeSerializedProgram contract.inputCount source.neurons with
    | .error problem => .error problem
    | .ok decodedProgram =>
        match decodeSerializedOutputs decodedProgram.producedCount
            source.outputs with
        | .error problem => .error problem
        | .ok decodedOutputs =>
            if outputsNonempty : source.outputs ≠ [] then
              let ports : OutputPorts decodedProgram.producedCount :=
                { sources := decodedOutputs.values
                  nonempty := by
                    intro empty
                    apply outputsNonempty
                    rw [← decodedOutputs.exact, empty]
                    rfl }
              let system : NativeSystem
                  (RequirementInput contract.family) contract.Proposal :=
                { inputCount := contract.inputCount
                  producedCount := decodedProgram.producedCount
                  encode := contract.encode
                  program := decodedProgram.program
                  outputs := ports
                  decode := contract.decode }
              .ok (.mk source system
                { inputCountExact := inputExact
                  contractInputCountExact := rfl
                  neuronsExact := by
                    have programExact := decodedProgram.exact
                    change serializeProgram decodedProgram.program =
                      serializeProgram
                        (NetworkProgram.empty :
                          NetworkProgram contract.inputCount 0) ++
                            source.neurons at programExact
                    change serializeProgram decodedProgram.program =
                      source.neurons
                    have emptyExact : serializeProgram
                        (NetworkProgram.empty :
                          NetworkProgram contract.inputCount 0) = [] := rfl
                    rw [emptyExact, List.nil_append] at programExact
                    exact programExact
                  outputsExact := decodedOutputs.exact
                  encodingExact := by intro input; rfl
                  decoderExact := by intro values; rfl })
            else
              .error .emptyOutputs
  else
    .error .inputCountMismatch

/-! ## Closed public serialized artifact -/

def publicSerializedRequirementNetwork : SerializedNetwork :=
  { inputCount := 1
    neurons :=
      [{ inputs :=
          [{ source := .receivedInput 0, weight := 1 }]
         bias := 0
         threshold := 3 }]
    outputs := [0] }

abbrev PublicInitialOperationalContract : ConstitutiveContract :=
  publicOperationalContract .initial

def publicDecodedRequirementArtifact :
    DecodedNeuralArtifact PublicInitialOperationalContract :=
  .mk publicSerializedRequirementNetwork publicRequirementSystem
    { inputCountExact := rfl
      contractInputCountExact := rfl
      neuronsExact := rfl
      outputsExact := rfl
      encodingExact := by intro input; rfl
      decoderExact := by intro values; rfl }

theorem publicSerializedRequirementNetwork_decodes :
    decodeArtifact PublicInitialOperationalContract
      publicSerializedRequirementNetwork =
        .ok publicDecodedRequirementArtifact := by
  rfl

theorem publicDecodedRequirementArtifact_system_exact :
    publicDecodedRequirementArtifact.system = publicRequirementSystem :=
  rfl

theorem publicDecodedRequirementArtifact_proposal_exact
    (input : PublicRequirementInput) :
    publicDecodedRequirementArtifact.system.proposal input =
      publicRequirementFamily.requiredProposal input.requirement input.context :=
  public_proposal_aligned input

/-! ## Complete reconfigured reference artifact -/

abbrev PublicReconfiguredOperationalContract : ConstitutiveContract :=
  publicOperationalContract .reconfigured

def publicSerializedReconfiguredNetwork : SerializedNetwork :=
  serializeNativeSystem publicReconfiguredContractSystem

def publicDecodedReconfiguredArtifact :
    DecodedNeuralArtifact PublicReconfiguredOperationalContract :=
  .mk publicSerializedReconfiguredNetwork publicReconfiguredContractSystem
    { inputCountExact := rfl
      contractInputCountExact := rfl
      neuronsExact := rfl
      outputsExact := rfl
      encodingExact := by intro input; rfl
      decoderExact := by intro values; rfl }

theorem publicSerializedReconfiguredNetwork_decodes :
    decodeArtifact PublicReconfiguredOperationalContract
      publicSerializedReconfiguredNetwork =
        .ok publicDecodedReconfiguredArtifact := by
  rfl

def invalidForwardReferenceNetwork : SerializedNetwork :=
  { inputCount := 1
    neurons :=
      [{ inputs := [{ source := .priorNeuron 0, weight := 1 }]
         bias := 0
         threshold := 1 }]
    outputs := [0] }

theorem invalidForwardReferenceNetwork_rejected :
    decodeArtifact PublicInitialOperationalContract
      invalidForwardReferenceNetwork = .error .invalidPriorNeuron := by
  rfl

def mismatchedInputCountNetwork : SerializedNetwork :=
  { publicSerializedRequirementNetwork with inputCount := 2 }

theorem mismatchedInputCountNetwork_rejected :
    decodeArtifact PublicInitialOperationalContract
      mismatchedInputCountNetwork = .error .inputCountMismatch := by
  rfl

def invalidReceivedInputNetwork : SerializedNetwork :=
  { inputCount := 1
    neurons :=
      [{ inputs := [{ source := .receivedInput 1, weight := 1 }]
         bias := 0
         threshold := 3 }]
    outputs := [0] }

theorem invalidReceivedInputNetwork_rejected :
    decodeArtifact PublicInitialOperationalContract
      invalidReceivedInputNetwork = .error .invalidReceivedInput := by
  rfl

def invalidOutputNetwork : SerializedNetwork :=
  { publicSerializedRequirementNetwork with outputs := [1] }

theorem invalidOutputNetwork_rejected :
    decodeArtifact PublicInitialOperationalContract invalidOutputNetwork =
      .error .invalidOutput := by
  rfl

def emptyOutputNetwork : SerializedNetwork :=
  { inputCount := 1
    neurons := publicSerializedRequirementNetwork.neurons
    outputs := [] }

theorem emptyOutputNetwork_rejected :
    decodeArtifact PublicInitialOperationalContract emptyOutputNetwork =
      .error .emptyOutputs := by
  rfl

end ConstitutiveSearch.NeuralAgent
/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.NeuralAgent.SerializedSource
#print axioms ConstitutiveSearch.NeuralAgent.SerializedNetwork
#print axioms ConstitutiveSearch.NeuralAgent.serializeNativeSystem
#print axioms ConstitutiveSearch.NeuralAgent.serializeProgram
#print axioms ConstitutiveSearch.NeuralAgent.serializedAppendNil
#print axioms ConstitutiveSearch.NeuralAgent.serializedAppendAssoc
#print axioms ConstitutiveSearch.NeuralAgent.decodeSerializedSource
#print axioms ConstitutiveSearch.NeuralAgent.decodeSerializedNeuron
#print axioms ConstitutiveSearch.NeuralAgent.decodeSerializedProgram
#print axioms ConstitutiveSearch.NeuralAgent.decodeSerializedOutputs
#print axioms ConstitutiveSearch.NeuralAgent.ArtifactDecodingExact
#print axioms ConstitutiveSearch.NeuralAgent.DecodedNeuralArtifact
#print axioms ConstitutiveSearch.NeuralAgent.certifyDecodedNeuralArtifact
#print axioms ConstitutiveSearch.NeuralAgent.decodeArtifact
#print axioms ConstitutiveSearch.NeuralAgent.publicSerializedRequirementNetwork_decodes
#print axioms ConstitutiveSearch.NeuralAgent.publicDecodedRequirementArtifact_system_exact
#print axioms ConstitutiveSearch.NeuralAgent.publicDecodedRequirementArtifact_proposal_exact
#print axioms ConstitutiveSearch.NeuralAgent.publicSerializedReconfiguredNetwork
#print axioms ConstitutiveSearch.NeuralAgent.publicDecodedReconfiguredArtifact
#print axioms ConstitutiveSearch.NeuralAgent.publicSerializedReconfiguredNetwork_decodes
#print axioms ConstitutiveSearch.NeuralAgent.invalidForwardReferenceNetwork_rejected
#print axioms ConstitutiveSearch.NeuralAgent.mismatchedInputCountNetwork_rejected
#print axioms ConstitutiveSearch.NeuralAgent.invalidReceivedInputNetwork_rejected
#print axioms ConstitutiveSearch.NeuralAgent.invalidOutputNetwork_rejected
#print axioms ConstitutiveSearch.NeuralAgent.emptyOutputNetwork_rejected
/- AXIOM_AUDIT_END -/
