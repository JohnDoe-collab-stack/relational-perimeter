import RelationalPerimeter.Agents.Neural.SerializedNativeSystem

/-!
# Stable neural identities

Stable identities are separate from the `Fin` indices used to execute one
decoded program.  A naming assigns persistent serials to received inputs,
neurons, and output ports, while the indices only locate those identities in
one artifact version.  Injectivity prevents two locations of the same kind in
one version from claiming the same identity.
-/
set_option genInjectivity false
namespace ConstitutiveSearch.NeuralAgent
open NativeMechanism

/-- The version-independent part of an artifact-node identity. -/
inductive StableNodeKey where
  | receivedInput (serial : Nat)
  | neuron (serial : Nat)
  | outputPort (serial : Nat)
  deriving DecidableEq

/-- A complete stable naming for one decoded artifact.  The serials are data
separate from execution indices; only the location maps mention `Fin`. -/
structure StableArtifactNaming
    {contract : ConstitutiveContract}
    (artifact : DecodedNeuralArtifact contract) where
  inputSerial : Fin artifact.system.inputCount -> Nat
  neuronSerial : Fin artifact.system.producedCount -> Nat
  outputSerial : Fin artifact.system.outputs.sources.length -> Nat
  inputSerialInjective : Function.Injective inputSerial
  neuronSerialInjective : Function.Injective neuronSerial
  outputSerialInjective : Function.Injective outputSerial

/-- A stably named occurrence that can be the focus of an intervention.  Its
identity is read through the naming; its `Fin` component is only its location
in this artifact version. -/
inductive StableNodeId
    {contract : ConstitutiveContract}
    {artifact : DecodedNeuralArtifact contract}
    (naming : StableArtifactNaming artifact) where
  | receivedInput (index : Fin artifact.system.inputCount)
  | neuron (index : Fin artifact.system.producedCount)

def StableNodeId.key
    {contract : ConstitutiveContract}
    {artifact : DecodedNeuralArtifact contract}
    {naming : StableArtifactNaming artifact} :
    StableNodeId naming -> StableNodeKey
  | .receivedInput index => .receivedInput (naming.inputSerial index)
  | .neuron index => .neuron (naming.neuronSerial index)

def StableNodeId.focus
    {contract : ConstitutiveContract}
    {artifact : DecodedNeuralArtifact contract}
    {naming : StableArtifactNaming artifact} :
    StableNodeId naming ->
      InterventionFocus artifact.system.inputCount
        artifact.system.producedCount
  | .receivedInput index => .input index
  | .neuron index => .neuron index

def StableNodeId.occurrence
    {contract : ConstitutiveContract}
    {artifact : DecodedNeuralArtifact contract}
    {naming : StableArtifactNaming artifact}
    (node : StableNodeId naming)
    (input : RequirementInput contract.family) :
    ActivationOccurrence (artifact.system.run input) :=
  match node with
  | .receivedInput index => .receivedInput index
  | .neuron index => .neuronOutput index

/-- Every activation occurrence of the exact artifact run has a unique located
stable node.  This is the bridge consumed by the heterogeneous causal graph. -/
def StableArtifactNaming.nodeOfOccurrence
    {contract : ConstitutiveContract}
    {artifact : DecodedNeuralArtifact contract}
    (naming : StableArtifactNaming artifact)
    {input : RequirementInput contract.family} :
    ActivationOccurrence (artifact.system.run input) -> StableNodeId naming
  | .receivedInput index => .receivedInput index
  | .neuronOutput index => .neuron index

/-- Output-port identities use the same stable naming but a different located
type, because ports are observations rather than intervention foci. -/
structure StableOutputPortId
    {contract : ConstitutiveContract}
    {artifact : DecodedNeuralArtifact contract}
    (naming : StableArtifactNaming artifact) where
  index : Fin artifact.system.outputs.sources.length

def StableOutputPortId.key
    {contract : ConstitutiveContract}
    {artifact : DecodedNeuralArtifact contract}
    {naming : StableArtifactNaming artifact}
    (port : StableOutputPortId naming) : StableNodeKey :=
  .outputPort (naming.outputSerial port.index)

def StableArtifactNaming.sourceNode
    {contract : ConstitutiveContract}
    {artifact : DecodedNeuralArtifact contract}
    (naming : StableArtifactNaming artifact)
    (target : Fin artifact.system.producedCount) :
    SourceIndex artifact.system.inputCount target.val -> StableNodeId naming
  | .receivedInput index => .receivedInput index
  | .priorNeuron index =>
      .neuron ⟨index.val, Nat.lt_trans index.isLt target.isLt⟩

def StableArtifactNaming.targetNode
    {contract : ConstitutiveContract}
    {artifact : DecodedNeuralArtifact contract}
    (naming : StableArtifactNaming artifact)
    (target : Fin artifact.system.producedCount) : StableNodeId naming :=
  .neuron target

def StableArtifactNaming.outputPort
    {contract : ConstitutiveContract}
    {artifact : DecodedNeuralArtifact contract}
    (naming : StableArtifactNaming artifact)
    (port : Fin artifact.system.outputs.sources.length) :
    StableOutputPortId naming :=
  ⟨port⟩

def publicInitialStableNaming :
    StableArtifactNaming publicDecodedRequirementArtifact where
  inputSerial := fun _ => 1
  neuronSerial := fun index => index.val
  outputSerial := fun index => index.val
  inputSerialInjective := by
    intro left right _
    apply Fin.ext
    have leftZero : left.val = 0 :=
      Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ left.isLt)
    have rightZero : right.val = 0 :=
      Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ right.isLt)
    exact leftZero.trans rightZero.symm
  neuronSerialInjective := fun _ _ same => Fin.ext same
  outputSerialInjective := fun _ _ same => Fin.ext same

/-- Target input serials use their explicit persistent namespace, while their
execution positions remain ordinary `Fin` indices. -/
def publicReconfiguredInputSerial
    (index : Fin publicDecodedReconfiguredArtifact.system.inputCount) : Nat :=
  index.val

theorem publicReconfiguredInputSerial_injective :
    Function.Injective publicReconfiguredInputSerial := by
  intro left right same
  exact Fin.ext same

def publicReconfiguredStableNaming :
    StableArtifactNaming publicDecodedReconfiguredArtifact where
  inputSerial := publicReconfiguredInputSerial
  neuronSerial := fun index => index.val
  outputSerial := fun index => index.val
  inputSerialInjective := publicReconfiguredInputSerial_injective
  neuronSerialInjective := fun _ _ same => Fin.ext same
  outputSerialInjective := fun _ _ same => Fin.ext same

theorem publicRequirementStableKey_survives_reindexing :
    (StableNodeId.receivedInput (naming := publicInitialStableNaming)
        publicRequirementPort).key =
      (StableNodeId.receivedInput (naming := publicReconfiguredStableNaming)
        publicReconfigurationRequirementPort).key := by
  rfl

theorem publicRequirementStableLocation_changes :
    publicRequirementPort.val ≠ publicReconfigurationRequirementPort.val := by
  decide

end ConstitutiveSearch.NeuralAgent
/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.NeuralAgent.StableNodeKey
#print axioms ConstitutiveSearch.NeuralAgent.StableArtifactNaming
#print axioms ConstitutiveSearch.NeuralAgent.StableNodeId
#print axioms ConstitutiveSearch.NeuralAgent.StableNodeId.key
#print axioms ConstitutiveSearch.NeuralAgent.StableNodeId.focus
#print axioms ConstitutiveSearch.NeuralAgent.StableNodeId.occurrence
#print axioms ConstitutiveSearch.NeuralAgent.StableArtifactNaming.nodeOfOccurrence
#print axioms ConstitutiveSearch.NeuralAgent.StableOutputPortId
#print axioms ConstitutiveSearch.NeuralAgent.StableOutputPortId.key
#print axioms ConstitutiveSearch.NeuralAgent.StableArtifactNaming.sourceNode
#print axioms ConstitutiveSearch.NeuralAgent.publicInitialStableNaming
#print axioms ConstitutiveSearch.NeuralAgent.publicReconfiguredStableNaming
#print axioms ConstitutiveSearch.NeuralAgent.publicRequirementStableKey_survives_reindexing
#print axioms ConstitutiveSearch.NeuralAgent.publicRequirementStableLocation_changes
/- AXIOM_AUDIT_END -/
