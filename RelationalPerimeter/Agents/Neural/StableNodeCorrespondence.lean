import RelationalPerimeter.Agents.Neural.ReferenceChecker

/-!
# Validated stable-node correspondence between artifact versions

A correspondence is partial: removed old nodes may have no image and inserted
new nodes may have no antecedent.  Every transported location must preserve
its stable key, and each partial location map is injective on successful
results.  Reindexing is therefore allowed, but silent identification is not.
-/
set_option genInjectivity false
namespace ConstitutiveSearch.NeuralAgent

/-- Injectivity restricted to the successfully transported part of a partial
map. -/
def PartialInjective {Source : Type u} {Target : Type v}
    (transport : Source -> Option Target) : Prop :=
  (left right : Source) -> (target : Target) ->
    transport left = some target -> transport right = some target ->
      left = right

/-- A validated correspondence between the stable namings of two decoded
artifacts.  Key preservation is checked separately for inputs, neurons, and
output ports, so a node cannot change constitutive kind while being reused. -/
structure ValidatedStableNodeCorrespondence
    {oldContract newContract : ConstitutiveContract}
    {oldArtifact : DecodedNeuralArtifact oldContract}
    {newArtifact : DecodedNeuralArtifact newContract}
    (oldNaming : StableArtifactNaming oldArtifact)
    (newNaming : StableArtifactNaming newArtifact) : Type where
  inputMap : Fin oldArtifact.system.inputCount ->
    Option (Fin newArtifact.system.inputCount)
  neuronMap : Fin oldArtifact.system.producedCount ->
    Option (Fin newArtifact.system.producedCount)
  outputMap : Fin oldArtifact.system.outputs.sources.length ->
    Option (Fin newArtifact.system.outputs.sources.length)
  inputKeyExact : (source : Fin oldArtifact.system.inputCount) ->
    match inputMap source with
    | none => True
    | some target =>
        oldNaming.inputSerial source = newNaming.inputSerial target
  neuronKeyExact : (source : Fin oldArtifact.system.producedCount) ->
    match neuronMap source with
    | none => True
    | some target =>
        oldNaming.neuronSerial source = newNaming.neuronSerial target
  outputKeyExact :
    (source : Fin oldArtifact.system.outputs.sources.length) ->
    match outputMap source with
    | none => True
    | some target =>
        oldNaming.outputSerial source = newNaming.outputSerial target
  inputMapInjective : PartialInjective inputMap
  neuronMapInjective : PartialInjective neuronMap
  outputMapInjective : PartialInjective outputMap

/-- A positive result of searching a validated target naming for one stable
serial.  The equality is produced by the search together with the location;
it is not reconstructed from a later certificate. -/
structure StableSerialMatch {count : Nat}
    (serial : Nat) (targetSerial : Fin count -> Nat) : Type where
  target : Fin count
  serialExact : serial = targetSerial target

/-- Executable search through the finite target layout. -/
def findStableSerialMatch {count : Nat}
    (serial : Nat) (targetSerial : Fin count -> Nat) :
    List (Fin count) -> Option (StableSerialMatch serial targetSerial)
  | [] => none
  | target :: rest =>
      if same : serial = targetSerial target then
        some { target := target, serialExact := same }
      else
        findStableSerialMatch serial targetSerial rest

/-- A stable-location map is calculated from the source and target namings.
It searches the target layout for the source serial; deletions yield `none`,
preservations and reindexings yield the unique target location. -/
def calculatedStableLocationMap {sourceCount targetCount : Nat}
    (sourceSerial : Fin sourceCount -> Nat)
    (targetSerial : Fin targetCount -> Nat)
    (source : Fin sourceCount) : Option (Fin targetCount) :=
  match findStableSerialMatch (sourceSerial source) targetSerial
      (structuralLocations targetCount) with
  | none => none
  | some matched => some matched.target

theorem calculatedStableLocationMap_keyExact
    {sourceCount targetCount : Nat}
    (sourceSerial : Fin sourceCount -> Nat)
    (targetSerial : Fin targetCount -> Nat)
    (source : Fin sourceCount) :
    match calculatedStableLocationMap sourceSerial targetSerial source with
    | none => True
    | some target => sourceSerial source = targetSerial target := by
  unfold calculatedStableLocationMap
  generalize found : findStableSerialMatch (sourceSerial source) targetSerial
      (structuralLocations targetCount) = result
  cases result with
  | none => trivial
  | some matched => exact matched.serialExact

theorem calculatedStableLocationMap_partialInjective
    {sourceCount targetCount : Nat}
    (sourceSerial : Fin sourceCount -> Nat)
    (targetSerial : Fin targetCount -> Nat)
    (sourceSerialInjective : Function.Injective sourceSerial) :
    PartialInjective
      (calculatedStableLocationMap sourceSerial targetSerial) := by
  intro left right target leftExact rightExact
  have leftKey := calculatedStableLocationMap_keyExact
    sourceSerial targetSerial left
  have rightKey := calculatedStableLocationMap_keyExact
    sourceSerial targetSerial right
  rw [leftExact] at leftKey
  rw [rightExact] at rightKey
  exact sourceSerialInjective (leftKey.trans rightKey.symm)

/-- The calculated map, its key equation, and its partial injectivity are one
constitutive product.  Keeping them together prevents a later caller from
substituting a map while reusing proofs produced for another calculation. -/
structure CalculatedStableLocationMap {sourceCount targetCount : Nat}
    (sourceSerial : Fin sourceCount -> Nat)
    (targetSerial : Fin targetCount -> Nat) : Type where
  map : Fin sourceCount -> Option (Fin targetCount)
  keyExact : (source : Fin sourceCount) ->
    match map source with
    | none => True
    | some target => sourceSerial source = targetSerial target
  mapInjective : PartialInjective map

def calculateStableLocationMap {sourceCount targetCount : Nat}
    (sourceSerial : Fin sourceCount -> Nat)
    (targetSerial : Fin targetCount -> Nat)
    (sourceSerialInjective : Function.Injective sourceSerial) :
    CalculatedStableLocationMap sourceSerial targetSerial :=
  { map := calculatedStableLocationMap sourceSerial targetSerial
    keyExact := calculatedStableLocationMap_keyExact sourceSerial targetSerial
    mapInjective := calculatedStableLocationMap_partialInjective
      sourceSerial targetSerial sourceSerialInjective }

/-- The complete partial correspondence is calculated from the two validated
stable namings.  No cross-version map or target certificate is supplied by a
caller. -/
def calculateStableNodeCorrespondence
    {oldContract newContract : ConstitutiveContract}
    {oldArtifact : DecodedNeuralArtifact oldContract}
    {newArtifact : DecodedNeuralArtifact newContract}
    (oldNaming : StableArtifactNaming oldArtifact)
    (newNaming : StableArtifactNaming newArtifact) :
    ValidatedStableNodeCorrespondence oldNaming newNaming := by
  let inputs := calculateStableLocationMap
    oldNaming.inputSerial newNaming.inputSerial oldNaming.inputSerialInjective
  let neurons := calculateStableLocationMap
    oldNaming.neuronSerial newNaming.neuronSerial oldNaming.neuronSerialInjective
  let outputs := calculateStableLocationMap
    oldNaming.outputSerial newNaming.outputSerial oldNaming.outputSerialInjective
  exact
    { inputMap := inputs.map
      neuronMap := neurons.map
      outputMap := outputs.map
      inputKeyExact := by
        intro source
        cases mapped : inputs.map source with
        | none => trivial
        | some target =>
            have exact := inputs.keyExact source
            rw [mapped] at exact
            exact exact
      neuronKeyExact := by
        intro source
        cases mapped : neurons.map source with
        | none => trivial
        | some target =>
            have exact := neurons.keyExact source
            rw [mapped] at exact
            exact exact
      outputKeyExact := by
        intro source
        cases mapped : outputs.map source with
        | none => trivial
        | some target =>
            have exact := outputs.keyExact source
            rw [mapped] at exact
            exact exact
      inputMapInjective := inputs.mapInjective
      neuronMapInjective := neurons.mapInjective
      outputMapInjective := outputs.mapInjective }

/-- A successful node transport carries its target together with the exact
stable-key equation.  Preservation is therefore produced with the transport,
not reconstructed from its result afterwards. -/
structure TransportedStableNode
    {oldContract newContract : ConstitutiveContract}
    {oldArtifact : DecodedNeuralArtifact oldContract}
    {newArtifact : DecodedNeuralArtifact newContract}
    {oldNaming : StableArtifactNaming oldArtifact}
    (newNaming : StableArtifactNaming newArtifact)
    (source : StableNodeId oldNaming) : Type where
  target : StableNodeId newNaming
  keyExact : source.key = target.key

def ValidatedStableNodeCorrespondence.transportNode
    {oldContract newContract : ConstitutiveContract}
    {oldArtifact : DecodedNeuralArtifact oldContract}
    {newArtifact : DecodedNeuralArtifact newContract}
    {oldNaming : StableArtifactNaming oldArtifact}
    {newNaming : StableArtifactNaming newArtifact}
    (correspondence :
      ValidatedStableNodeCorrespondence oldNaming newNaming) :
    (source : StableNodeId oldNaming) ->
      Option (TransportedStableNode newNaming source)
  | .receivedInput source =>
      match mapped : correspondence.inputMap source with
      | none => none
      | some target => some
          { target := .receivedInput target
            keyExact := by
              have exact := correspondence.inputKeyExact source
              rw [mapped] at exact
              exact congrArg StableNodeKey.receivedInput exact }
  | .neuron source =>
      match mapped : correspondence.neuronMap source with
      | none => none
      | some target => some
          { target := .neuron target
            keyExact := by
              have exact := correspondence.neuronKeyExact source
              rw [mapped] at exact
              exact congrArg StableNodeKey.neuron exact }

/-- Output-port transport has the same positive preservation discipline. -/
structure TransportedStableOutput
    {oldContract newContract : ConstitutiveContract}
    {oldArtifact : DecodedNeuralArtifact oldContract}
    {newArtifact : DecodedNeuralArtifact newContract}
    {oldNaming : StableArtifactNaming oldArtifact}
    (newNaming : StableArtifactNaming newArtifact)
    (source : StableOutputPortId oldNaming) : Type where
  target : StableOutputPortId newNaming
  keyExact : source.key = target.key

def ValidatedStableNodeCorrespondence.transportOutput
    {oldContract newContract : ConstitutiveContract}
    {oldArtifact : DecodedNeuralArtifact oldContract}
    {newArtifact : DecodedNeuralArtifact newContract}
    {oldNaming : StableArtifactNaming oldArtifact}
    {newNaming : StableArtifactNaming newArtifact}
    (correspondence :
      ValidatedStableNodeCorrespondence oldNaming newNaming)
    (source : StableOutputPortId oldNaming) :
    Option (TransportedStableOutput newNaming source) :=
  match mapped : correspondence.outputMap source.index with
  | none => none
  | some target => some
      { target := ⟨target⟩
        keyExact := by
          have exact := correspondence.outputKeyExact source.index
          rw [mapped] at exact
          exact congrArg StableNodeKey.outputPort exact }

theorem ValidatedStableNodeCorrespondence.transportNode_key_exact
    {oldContract newContract : ConstitutiveContract}
    {oldArtifact : DecodedNeuralArtifact oldContract}
    {newArtifact : DecodedNeuralArtifact newContract}
    {oldNaming : StableArtifactNaming oldArtifact}
    {newNaming : StableArtifactNaming newArtifact}
    (_correspondence :
      ValidatedStableNodeCorrespondence oldNaming newNaming)
    (source : StableNodeId oldNaming)
    (transported : TransportedStableNode newNaming source) :
    source.key = transported.target.key :=
  transported.keyExact

theorem ValidatedStableNodeCorrespondence.transportOutput_key_exact
    {oldContract newContract : ConstitutiveContract}
    {oldArtifact : DecodedNeuralArtifact oldContract}
    {newArtifact : DecodedNeuralArtifact newContract}
    {oldNaming : StableArtifactNaming oldArtifact}
    {newNaming : StableArtifactNaming newArtifact}
    (_correspondence :
      ValidatedStableNodeCorrespondence oldNaming newNaming)
    (source : StableOutputPortId oldNaming)
    (transported : TransportedStableOutput newNaming source) :
    source.key = transported.target.key :=
  transported.keyExact

def publicReferenceInputMap
    (_source : Fin publicDecodedRequirementArtifact.system.inputCount) :
    Option (Fin publicDecodedReconfiguredArtifact.system.inputCount) :=
  some publicReconfigurationRequirementPort

def publicReferenceNeuronMap
    (_source : Fin publicDecodedRequirementArtifact.system.producedCount) :
    Option (Fin publicDecodedReconfiguredArtifact.system.producedCount) :=
  some publicReconfigurationProposalOutput

def publicReferenceOutputMap
    (_source : Fin publicDecodedRequirementArtifact.system.outputs.sources.length) :
    Option (Fin publicDecodedReconfiguredArtifact.system.outputs.sources.length) :=
  some publicReconfigurationProposalOutputPort

theorem finOne_equal (left right : Fin 1) : left = right := by
  apply Fin.ext
  have leftZero : left.val = 0 :=
    Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ left.isLt)
  have rightZero : right.val = 0 :=
    Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ right.isLt)
  exact leftZero.trans rightZero.symm

def publicStableNodeCorrespondence :
    ValidatedStableNodeCorrespondence publicInitialStableNaming
      publicReconfiguredStableNaming :=
  calculateStableNodeCorrespondence publicInitialStableNaming
    publicReconfiguredStableNaming

theorem publicStableNodeCorrespondence_reindexes_requirement :
    Option.map (TransportedStableNode.target
      (newNaming := publicReconfiguredStableNaming))
        (publicStableNodeCorrespondence.transportNode
          (.receivedInput publicRequirementPort)) =
      some (.receivedInput publicReconfigurationRequirementPort) := by
  rfl

theorem publicStableNodeCorrespondence_preserves_requirement_key :
    (StableNodeId.receivedInput (naming := publicInitialStableNaming)
        publicRequirementPort).key =
      (StableNodeId.receivedInput (naming := publicReconfiguredStableNaming)
        publicReconfigurationRequirementPort).key :=
  publicRequirementStableKey_survives_reindexing

theorem publicStableNodeCorrespondence_reindexes_proposal_neuron :
    Option.map (TransportedStableNode.target
      (newNaming := publicReconfiguredStableNaming))
        (publicStableNodeCorrespondence.transportNode
          (.neuron publicRequirementOutput)) =
      some (.neuron publicReconfigurationProposalOutput) := by
  rfl

theorem publicStableNodeCorrespondence_reindexes_output :
    Option.map (TransportedStableOutput.target
      (newNaming := publicReconfiguredStableNaming))
        (publicStableNodeCorrespondence.transportOutput
          (publicInitialStableNaming.outputPort
            publicRequirementOutputPort)) =
      some (publicReconfiguredStableNaming.outputPort
        publicReconfigurationProposalOutputPort) := by
  rfl

/-- The incorporated authorization input is an insertion in the target
version and therefore has no old input antecedent in the validated partial
correspondence. -/
def PublicAuthorizationHasOldInputAntecedent : Prop :=
  Exists fun source : Fin publicDecodedRequirementArtifact.system.inputCount =>
    publicStableNodeCorrespondence.inputMap source =
      some publicReconfigurationAuthorizationPort

theorem publicAuthorization_has_no_old_input_antecedent :
    PublicAuthorizationHasOldInputAntecedent -> False := by
  intro antecedent
  rcases antecedent with ⟨source, exact⟩
  have sourceExact : source = publicRequirementPort :=
    finOne_equal source publicRequirementPort
  subst source
  change some publicReconfigurationRequirementPort =
    some publicReconfigurationAuthorizationPort at exact
  have portExact : publicReconfigurationRequirementPort =
      publicReconfigurationAuthorizationPort :=
    Option.some.inj exact
  have impossible : (1 : Nat) = 2 := congrArg Fin.val portExact
  exact (by decide : (1 : Nat) ≠ 2) impossible

end ConstitutiveSearch.NeuralAgent
/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.NeuralAgent.PartialInjective
#print axioms ConstitutiveSearch.NeuralAgent.ValidatedStableNodeCorrespondence
#print axioms ConstitutiveSearch.NeuralAgent.StableSerialMatch
#print axioms ConstitutiveSearch.NeuralAgent.findStableSerialMatch
#print axioms ConstitutiveSearch.NeuralAgent.calculatedStableLocationMap
#print axioms ConstitutiveSearch.NeuralAgent.calculatedStableLocationMap_keyExact
#print axioms ConstitutiveSearch.NeuralAgent.calculatedStableLocationMap_partialInjective
#print axioms ConstitutiveSearch.NeuralAgent.CalculatedStableLocationMap
#print axioms ConstitutiveSearch.NeuralAgent.calculateStableLocationMap
#print axioms ConstitutiveSearch.NeuralAgent.calculateStableNodeCorrespondence
#print axioms ConstitutiveSearch.NeuralAgent.TransportedStableNode
#print axioms ConstitutiveSearch.NeuralAgent.ValidatedStableNodeCorrespondence.transportNode
#print axioms ConstitutiveSearch.NeuralAgent.TransportedStableOutput
#print axioms ConstitutiveSearch.NeuralAgent.ValidatedStableNodeCorrespondence.transportNode_key_exact
#print axioms ConstitutiveSearch.NeuralAgent.ValidatedStableNodeCorrespondence.transportOutput_key_exact
#print axioms ConstitutiveSearch.NeuralAgent.publicStableNodeCorrespondence
#print axioms ConstitutiveSearch.NeuralAgent.publicStableNodeCorrespondence_reindexes_requirement
#print axioms ConstitutiveSearch.NeuralAgent.publicStableNodeCorrespondence_preserves_requirement_key
#print axioms ConstitutiveSearch.NeuralAgent.publicStableNodeCorrespondence_reindexes_proposal_neuron
#print axioms ConstitutiveSearch.NeuralAgent.publicStableNodeCorrespondence_reindexes_output
#print axioms ConstitutiveSearch.NeuralAgent.publicAuthorization_has_no_old_input_antecedent
/- AXIOM_AUDIT_END -/
