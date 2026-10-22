import RelationalPerimeter.Agents.Neural.StableNodeIdentity

/-!
# Serialized constitutive neural artifacts

The received artifact contains the operational-contract name, the complete
network data, and all stable keys.  Stable identities are therefore validated
while the artifact is decoded; they are not attached afterwards by a public
definition specialized to one example.
-/
set_option genInjectivity false
namespace ConstitutiveSearch.NeuralAgent

/-- Proof-free external names for the operational contracts admitted by the
current public meta-contract. -/
inductive SerializedOperationalContractName where
  | initial
  | reconfigured
  deriving DecidableEq

def SerializedOperationalContractName.decode :
    SerializedOperationalContractName -> PublicOperationalContract
  | .initial => .initial
  | .reconfigured => .reconfigured

theorem SerializedOperationalContractName.decode_injective :
    Function.Injective SerializedOperationalContractName.decode := by
  intro left right same
  cases left <;> cases right <;> cases same <;> rfl

/-- A transition request is plain data.  Keeping both endpoint names makes an
invalid or reversed request representable and therefore rejectable. -/
structure SerializedOperationalContractTransition where
  source : SerializedOperationalContractName
  target : SerializedOperationalContractName
  deriving DecidableEq

inductive SerializedContractTransitionError where
  | transitionNotAdmitted
  deriving DecidableEq

def decodeOperationalContractTransition
    (source : SerializedOperationalContractTransition) :
    Except SerializedContractTransitionError
      (OperationalContractTransition publicConstitutiveMetaContract
        .initial .reconfigured) :=
  if _sourceSame : source =
      { source := .initial, target := .reconfigured } then
    .ok publicOperationalTransition
  else
    .error .transitionNotAdmitted

/-- Stable serials are transmitted separately for every kind of artifact
location.  The three lists are ordinary proof-free serialized data. -/
structure SerializedStableArtifactNaming where
  inputKeys : List Nat
  neuronKeys : List Nat
  outputKeys : List Nat
  deriving DecidableEq

/-- A proof-free description of how one stable key changes location across two
serialized artifact versions. -/
inductive SerializedStableKeyChange where
  | preserved (serial index : Nat)
  | reindexed (serial sourceIndex targetIndex : Nat)
  | deleted (serial sourceIndex : Nat)
  | inserted (serial targetIndex : Nat)
  deriving DecidableEq

def findStableSerialIndex (serial : Nat) :
    Nat -> List Nat -> Option Nat
  | _, [] => none
  | index, head :: tail =>
      if head = serial then
        some index
      else
        findStableSerialIndex serial (Nat.succ index) tail

def existingStableKeyChanges (target : List Nat) :
    Nat -> List Nat -> List SerializedStableKeyChange
  | _, [] => []
  | sourceIndex, serial :: tail =>
      let current :=
        match findStableSerialIndex serial 0 target with
        | none => .deleted serial sourceIndex
        | some targetIndex =>
            if sourceIndex = targetIndex then
              .preserved serial sourceIndex
            else
              .reindexed serial sourceIndex targetIndex
      current :: existingStableKeyChanges target (Nat.succ sourceIndex) tail

def insertedStableKeyChanges (source : List Nat) :
    Nat -> List Nat -> List SerializedStableKeyChange
  | _, [] => []
  | targetIndex, serial :: tail =>
      let rest :=
        insertedStableKeyChanges source (Nat.succ targetIndex) tail
      match findStableSerialIndex serial 0 source with
      | none => .inserted serial targetIndex :: rest
      | some _ => rest

def serializedStableKeyChanges (source target : List Nat) :
    List SerializedStableKeyChange :=
  existingStableKeyChanges target 0 source ++
    insertedStableKeyChanges source 0 target

structure SerializedStableArtifactChanges where
  inputs : List SerializedStableKeyChange
  neurons : List SerializedStableKeyChange
  outputs : List SerializedStableKeyChange
  deriving DecidableEq

def serializedStableArtifactChanges
    (source target : SerializedStableArtifactNaming) :
    SerializedStableArtifactChanges :=
  { inputs := serializedStableKeyChanges source.inputKeys target.inputKeys
    neurons := serializedStableKeyChanges source.neuronKeys target.neuronKeys
    outputs := serializedStableKeyChanges source.outputKeys target.outputKeys }

inductive StableNamingError where
  | inputCountMismatch
  | neuronCountMismatch
  | outputCountMismatch
  | duplicateInputKey
  | duplicateNeuronKey
  | duplicateOutputKey
  deriving DecidableEq

/-- Positive, computational evidence that one serial does not occur in a
list.  This avoids hiding stable-key validation behind proposition-level list
decidability. -/
inductive StableSerialAbsent (serial : Nat) : List Nat -> Type where
  | nil : StableSerialAbsent serial []
  | cons {head : Nat} {tail : List Nat} :
      serial ≠ head -> StableSerialAbsent serial tail ->
        StableSerialAbsent serial (head :: tail)

def decodeStableSerialAbsent (serial : Nat) :
    (source : List Nat) -> Except Unit (StableSerialAbsent serial source)
  | [] => .ok .nil
  | head :: tail =>
      if same : serial = head then
        .error ()
      else
        match decodeStableSerialAbsent serial tail with
        | .error _ => .error ()
        | .ok absent => .ok (.cons same absent)
/-- Positive evidence that a serialized list has exactly the requested length
and contains pairwise distinct serials.  The count and the list are indexed by
the witness itself, so decoding never relies on proposition-level casts. -/
inductive StableSerialLayout : Nat -> List Nat -> Type where
  | nil : StableSerialLayout 0 []
  | cons {count head tail} :
      StableSerialAbsent head tail -> StableSerialLayout count tail ->
        StableSerialLayout (Nat.succ count) (head :: tail)

def decodeStableSerialLayout
    (lengthError duplicateError : StableNamingError) :
    (count : Nat) -> (source : List Nat) ->
      Except StableNamingError (StableSerialLayout count source)
  | 0, [] => .ok .nil
  | 0, _ :: _ => .error lengthError
  | Nat.succ _, [] => .error lengthError
  | Nat.succ count, head :: tail =>
      match decodeStableSerialAbsent head tail with
      | .error _ => .error duplicateError
      | .ok absent =>
          match decodeStableSerialLayout lengthError duplicateError count tail with
          | .error problem => .error problem
          | .ok layout => .ok (.cons absent layout)

def StableSerialLayout.serial
    {count : Nat} {source : List Nat}
    (layout : StableSerialLayout count source) : Fin count -> Nat :=
  match layout with
  | .nil => fun index => Fin.elim0 index
  | @cons count head _ _ tailLayout =>
      fun index =>
        match index with
        | ⟨0, _⟩ => head
        | ⟨Nat.succ prior, within⟩ =>
            tailLayout.serial
              ⟨prior, Nat.lt_of_succ_lt_succ within⟩

theorem StableSerialAbsent.ne_serial
    {serial : Nat} {count : Nat} {source : List Nat}
    (absent : StableSerialAbsent serial source)
    (layout : StableSerialLayout count source) :
    forall index, serial ≠ layout.serial index := by
  induction layout generalizing serial with
  | nil =>
      intro index
      exact Fin.elim0 index
  | @cons count head tail headAbsent tailLayout ih =>
      cases absent with
      | cons serialNeHead serialAbsentTail =>
          intro index
          cases index with
          | mk value within =>
              cases value with
              | zero => exact serialNeHead
              | succ prior =>
                  exact ih serialAbsentTail
                    ⟨prior, Nat.lt_of_succ_lt_succ within⟩

theorem StableSerialLayout.serial_injective
    {count : Nat} {source : List Nat}
    (layout : StableSerialLayout count source) :
    Function.Injective layout.serial := by
  induction layout with
  | nil =>
      intro left
      exact Fin.elim0 left
  | @cons count head tail headAbsent tailLayout ih =>
      intro left right same
      cases left with
      | mk leftValue leftWithin =>
          cases right with
          | mk rightValue rightWithin =>
              cases leftValue with
              | zero =>
                  cases rightValue with
                  | zero => rfl
                  | succ rightPrior =>
                      exact False.elim
                        ((headAbsent.ne_serial tailLayout
                          ⟨rightPrior,
                            Nat.lt_of_succ_lt_succ rightWithin⟩) same)
              | succ leftPrior =>
                  cases rightValue with
                  | zero =>
                      exact False.elim
                        ((headAbsent.ne_serial tailLayout
                          ⟨leftPrior,
                            Nat.lt_of_succ_lt_succ leftWithin⟩) same.symm)
                  | succ rightPrior =>
                      have tailSame :
                          (⟨leftPrior,
                              Nat.lt_of_succ_lt_succ leftWithin⟩ : Fin count) =
                            ⟨rightPrior,
                              Nat.lt_of_succ_lt_succ rightWithin⟩ :=
                        ih same
                      exact Fin.ext
                        (congrArg Nat.succ (congrArg Fin.val tailSame))

def decodeStableSerials (count : Nat) (source : List Nat)
    (lengthError duplicateError : StableNamingError) :
    Except StableNamingError (StableSerialLayout count source) :=
  decodeStableSerialLayout lengthError duplicateError count source

structure DecodedStableArtifactNaming
    {contract : ConstitutiveContract}
    (artifact : DecodedNeuralArtifact contract)
    (source : SerializedStableArtifactNaming) : Type 4 where
  inputLayout : StableSerialLayout artifact.system.inputCount source.inputKeys
  neuronLayout :
    StableSerialLayout artifact.system.producedCount source.neuronKeys
  outputLayout :
    StableSerialLayout artifact.system.outputs.sources.length source.outputKeys

/-- The stable naming is reconstructed from the validated serialized keys. -/
def DecodedStableArtifactNaming.naming
    {contract : ConstitutiveContract}
    {artifact : DecodedNeuralArtifact contract}
    {source : SerializedStableArtifactNaming}
    (decoded : DecodedStableArtifactNaming artifact source) :
    StableArtifactNaming artifact :=
  { inputSerial := decoded.inputLayout.serial
    neuronSerial := decoded.neuronLayout.serial
    outputSerial := decoded.outputLayout.serial
    inputSerialInjective := decoded.inputLayout.serial_injective
    neuronSerialInjective := decoded.neuronLayout.serial_injective
    outputSerialInjective := decoded.outputLayout.serial_injective }

def decodeStableArtifactNaming
    {contract : ConstitutiveContract}
    (artifact : DecodedNeuralArtifact contract)
    (source : SerializedStableArtifactNaming) :
    Except StableNamingError (DecodedStableArtifactNaming artifact source) :=
  match decodeStableSerials artifact.system.inputCount source.inputKeys
      .inputCountMismatch .duplicateInputKey with
  | .error problem => .error problem
  | .ok inputs =>
      match decodeStableSerials artifact.system.producedCount source.neuronKeys
          .neuronCountMismatch .duplicateNeuronKey with
      | .error problem => .error problem
      | .ok neurons =>
          match decodeStableSerials artifact.system.outputs.sources.length
              source.outputKeys .outputCountMismatch .duplicateOutputKey with
          | .error problem => .error problem
          | .ok outputs =>
              .ok
                { inputLayout := inputs
                  neuronLayout := neurons
                  outputLayout := outputs }

/-- Complete proof-free constitutive artifact received by a checker.  Choosing
the contract name chooses its decoder, authorization obligations, memory
projection, and future contract through `publicOperationalContract`. -/
structure SerializedConstitutiveArtifact where
  contract : SerializedOperationalContractName
  network : SerializedNetwork
  stableNaming : SerializedStableArtifactNaming
  deriving DecidableEq

inductive SerializedConstitutiveArtifactError where
  | network (problem : ArtifactError)
  | naming (problem : StableNamingError)
  deriving DecidableEq

structure DecodedSerializedConstitutiveArtifact
    (source : SerializedConstitutiveArtifact) : Type 4 where
  artifact : DecodedNeuralArtifact
    (publicOperationalContract source.contract.decode)
  stable : DecodedStableArtifactNaming artifact source.stableNaming

def decodeSerializedConstitutiveArtifact
    (source : SerializedConstitutiveArtifact) :
    Except SerializedConstitutiveArtifactError
      (DecodedSerializedConstitutiveArtifact source) :=
  match decodeArtifact (publicOperationalContract source.contract.decode)
      source.network with
  | .error problem => .error (.network problem)
  | .ok artifact =>
      match decodeStableArtifactNaming artifact source.stableNaming with
      | .error problem => .error (.naming problem)
          | .ok stable => .ok { artifact := artifact, stable := stable }

/-- Proof-free terminal update header.  Later checker layers must validate
that the named transition starts at the certified source contract and ends at
the contract named by `target`; neither equality is stored as a proof here. -/
structure SerializedConstitutiveUpdate where
  transition : SerializedOperationalContractTransition
  target : SerializedConstitutiveArtifact
  deriving DecidableEq

def publicSerializedOperationalTransition :
    SerializedOperationalContractTransition :=
  { source := .initial, target := .reconfigured }

def publicSerializedInitialStableNaming : SerializedStableArtifactNaming :=
  { inputKeys := [1]
    neuronKeys := [0]
    outputKeys := [0] }

def publicSerializedReconfiguredStableNaming :
    SerializedStableArtifactNaming :=
  { inputKeys := [0, 1, 2]
    neuronKeys := [0, 1]
    outputKeys := [0, 1] }

def publicSerializedInitialConstitutiveArtifact :
    SerializedConstitutiveArtifact :=
  { contract := .initial
    network := publicSerializedRequirementNetwork
    stableNaming := publicSerializedInitialStableNaming }

def publicSerializedReconfiguredConstitutiveArtifact :
    SerializedConstitutiveArtifact :=
  { contract := .reconfigured
    network := publicSerializedReconfiguredNetwork
    stableNaming := publicSerializedReconfiguredStableNaming }

def publicSerializedConstitutiveUpdate : SerializedConstitutiveUpdate :=
  { transition := publicSerializedOperationalTransition
    target := publicSerializedReconfiguredConstitutiveArtifact }

theorem publicSerializedOperationalTransition_decodes :
    decodeOperationalContractTransition publicSerializedOperationalTransition =
      .ok publicOperationalTransition := by
  rfl

theorem reversedSerializedOperationalTransition_rejected :
    decodeOperationalContractTransition
        { source := .reconfigured, target := .initial } =
      .error .transitionNotAdmitted := by
  rfl

theorem stationaryInitialOperationalTransition_rejected :
    decodeOperationalContractTransition
        { source := .initial, target := .initial } =
      .error .transitionNotAdmitted := by
  rfl

theorem stationaryReconfiguredOperationalTransition_rejected :
    decodeOperationalContractTransition
        { source := .reconfigured, target := .reconfigured } =
      .error .transitionNotAdmitted := by
  rfl

theorem publicSerializedStableArtifactChanges_exact :
    serializedStableArtifactChanges publicSerializedInitialStableNaming
        publicSerializedReconfiguredStableNaming =
      { inputs :=
          [ .reindexed 1 0 1,
            .inserted 0 0,
            .inserted 2 2 ]
        neurons := [ .preserved 0 0, .inserted 1 1 ]
        outputs := [ .preserved 0 0, .inserted 1 1 ] } := by
  rfl

def publicInitialInputKeyLayout : StableSerialLayout 1 [1] :=
  .cons .nil .nil

def publicInitialNeuronKeyLayout : StableSerialLayout 1 [0] :=
  .cons .nil .nil

def publicInitialOutputKeyLayout : StableSerialLayout 1 [0] :=
  .cons .nil .nil

def publicReconfiguredInputKeyLayout :
    StableSerialLayout 3 [0, 1, 2] :=
  .cons (.cons (by decide) (.cons (by decide) .nil))
    (.cons (.cons (by decide) .nil) (.cons .nil .nil))

def publicReconfiguredNeuronKeyLayout :
    StableSerialLayout 2 [0, 1] :=
  .cons (.cons (by decide) .nil) (.cons .nil .nil)

def publicReconfiguredOutputKeyLayout :
    StableSerialLayout 2 [0, 1] :=
  .cons (.cons (by decide) .nil) (.cons .nil .nil)

def publicDecodedInitialConstitutiveArtifact :
    DecodedSerializedConstitutiveArtifact
      publicSerializedInitialConstitutiveArtifact :=
  { artifact := publicDecodedRequirementArtifact
    stable :=
      { inputLayout := publicInitialInputKeyLayout
        neuronLayout := publicInitialNeuronKeyLayout
        outputLayout := publicInitialOutputKeyLayout } }

def publicDecodedReconfiguredConstitutiveArtifact :
    DecodedSerializedConstitutiveArtifact
      publicSerializedReconfiguredConstitutiveArtifact :=
  { artifact := publicDecodedReconfiguredArtifact
    stable :=
      { inputLayout := publicReconfiguredInputKeyLayout
        neuronLayout := publicReconfiguredNeuronKeyLayout
        outputLayout := publicReconfiguredOutputKeyLayout } }

theorem publicSerializedInitialConstitutiveArtifact_decodes :
    decodeSerializedConstitutiveArtifact
        publicSerializedInitialConstitutiveArtifact =
      .ok publicDecodedInitialConstitutiveArtifact := by
  rfl

theorem publicSerializedReconfiguredConstitutiveArtifact_decodes :
    decodeSerializedConstitutiveArtifact
        publicSerializedReconfiguredConstitutiveArtifact =
      .ok publicDecodedReconfiguredConstitutiveArtifact := by
  rfl

def publicInitialStableNaming :
    StableArtifactNaming publicDecodedRequirementArtifact :=
  publicDecodedInitialConstitutiveArtifact.stable.naming

def publicReconfiguredStableNaming :
    StableArtifactNaming publicDecodedReconfiguredArtifact :=
  publicDecodedReconfiguredConstitutiveArtifact.stable.naming

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
#print axioms ConstitutiveSearch.NeuralAgent.SerializedOperationalContractName
#print axioms ConstitutiveSearch.NeuralAgent.SerializedOperationalContractName.decode
#print axioms ConstitutiveSearch.NeuralAgent.SerializedOperationalContractName.decode_injective
#print axioms ConstitutiveSearch.NeuralAgent.SerializedOperationalContractTransition
#print axioms ConstitutiveSearch.NeuralAgent.PublicContractTransitionPermission.executeReconfiguration
#print axioms ConstitutiveSearch.NeuralAgent.decodeOperationalContractTransition
#print axioms ConstitutiveSearch.NeuralAgent.SerializedStableArtifactNaming
#print axioms ConstitutiveSearch.NeuralAgent.SerializedStableKeyChange
#print axioms ConstitutiveSearch.NeuralAgent.findStableSerialIndex
#print axioms ConstitutiveSearch.NeuralAgent.serializedStableArtifactChanges
#print axioms ConstitutiveSearch.NeuralAgent.decodeStableSerialAbsent
#print axioms ConstitutiveSearch.NeuralAgent.StableSerialLayout
#print axioms ConstitutiveSearch.NeuralAgent.decodeStableSerialLayout
#print axioms ConstitutiveSearch.NeuralAgent.StableSerialAbsent.ne_serial
#print axioms ConstitutiveSearch.NeuralAgent.StableSerialLayout.serial_injective
#print axioms ConstitutiveSearch.NeuralAgent.decodeStableSerials
#print axioms ConstitutiveSearch.NeuralAgent.DecodedStableArtifactNaming.naming
#print axioms ConstitutiveSearch.NeuralAgent.decodeStableArtifactNaming
#print axioms ConstitutiveSearch.NeuralAgent.SerializedConstitutiveArtifact
#print axioms ConstitutiveSearch.NeuralAgent.decodeSerializedConstitutiveArtifact
#print axioms ConstitutiveSearch.NeuralAgent.SerializedConstitutiveUpdate
#print axioms ConstitutiveSearch.NeuralAgent.publicSerializedOperationalTransition_decodes
#print axioms ConstitutiveSearch.NeuralAgent.reversedSerializedOperationalTransition_rejected
#print axioms ConstitutiveSearch.NeuralAgent.stationaryInitialOperationalTransition_rejected
#print axioms ConstitutiveSearch.NeuralAgent.stationaryReconfiguredOperationalTransition_rejected
#print axioms ConstitutiveSearch.NeuralAgent.publicSerializedStableArtifactChanges_exact
#print axioms ConstitutiveSearch.NeuralAgent.publicSerializedInitialConstitutiveArtifact_decodes
#print axioms ConstitutiveSearch.NeuralAgent.publicSerializedReconfiguredConstitutiveArtifact_decodes
#print axioms ConstitutiveSearch.NeuralAgent.publicInitialStableNaming
#print axioms ConstitutiveSearch.NeuralAgent.publicReconfiguredStableNaming
#print axioms ConstitutiveSearch.NeuralAgent.publicRequirementStableKey_survives_reindexing
#print axioms ConstitutiveSearch.NeuralAgent.publicRequirementStableLocation_changes
/- AXIOM_AUDIT_END -/
