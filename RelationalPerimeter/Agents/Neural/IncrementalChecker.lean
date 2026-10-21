import RelationalPerimeter.Agents.Neural.LocalCertificateReuse

/-!
# Executable incremental neural update checker

The received update is a proof-free list of serialized edits.  The checker
applies those edits to the exact source artifact, validates the resulting
target and the next input, and returns a certificate package that retains the
transported old fragment separately from the fragments recalculated in the
computed affected cone.  It never calls the complete artifact decoder.
-/
set_option genInjectivity false
namespace ConstitutiveSearch.NeuralAgent

/-- Plain serialized edits.  None of the constructors can carry a proof or a
certificate. -/
inductive SerializedNetworkEdit where
  | replaceInputCount (count : Nat)
  | replaceNeurons (neurons : List SerializedNeuron)
  | replaceOutputs (outputs : List Nat)
  deriving DecidableEq

def applySerializedNetworkEdit
    (source : SerializedNetwork) : SerializedNetworkEdit -> SerializedNetwork
  | .replaceInputCount count => { source with inputCount := count }
  | .replaceNeurons neurons => { source with neurons := neurons }
  | .replaceOutputs outputs => { source with outputs := outputs }

def applySerializedNetworkEdits :
    List SerializedNetworkEdit -> SerializedNetwork -> SerializedNetwork
  | [], source => source
  | edit :: rest, source =>
      applySerializedNetworkEdits rest
        (applySerializedNetworkEdit source edit)

/-- The incremental request contains only edits and the next received input.
In particular it contains neither a stable correspondence nor any certificate.
-/
structure IncrementalNeuralUpdate where
  edits : List SerializedNetworkEdit
  nextInput : PublicRequirementInput

def materializeIncrementalTarget (update : IncrementalNeuralUpdate) :
    SerializedNetwork :=
  applySerializedNetworkEdits update.edits
    publicInitialCheckedAgent.artifact.source

def IncrementalNeuralUpdate.toFullReferenceUpdate
    (update : IncrementalNeuralUpdate) : FullReferenceNeuralUpdate :=
  { targetArtifact := materializeIncrementalTarget update
    nextInput := update.nextInput }

def publicIncrementalNeuralUpdate : IncrementalNeuralUpdate :=
  { edits :=
      [ .replaceInputCount publicSerializedReconfiguredNetwork.inputCount,
        .replaceNeurons publicSerializedReconfiguredNetwork.neurons,
        .replaceOutputs publicSerializedReconfiguredNetwork.outputs ]
    nextInput := publicSubstantiveNext }

theorem publicIncrementalTarget_exact :
    materializeIncrementalTarget publicIncrementalNeuralUpdate =
      publicSerializedReconfiguredNetwork := by
  rfl

/-- Structural fragments recomputed from the target are selected by the
executable cone rather than supplied by the update. -/
def publicRecomputedStructuralFragments :
    List (StableNodeKey × StableArtifactObservation) :=
  (structuralObservationSnapshot
      publicReferenceUpdatedStateCertificate).filter (fun entry =>
    affectedConstitutiveNode publicInitialStateConstitutiveCertificate
      publicReferenceUpdatedStateCertificate publicStableNodeCorrespondence
      (.artifactNode entry.1))

/-- The reused list contains the payload transported from the old
certificate, not a separately recomputed target payload. -/
def publicTransportedStructuralFragments :
    List (StableNodeKey × StableArtifactObservation) :=
  [(.receivedInput 1, publicReusedRequirementFragment.payload)]

/-- Reassemble the target structural snapshot while replacing the unaffected
requirement entry with the payload transported from the old certificate. -/
def publicIncrementalStructuralAssembly :
    List (StableNodeKey × StableArtifactObservation) :=
  (structuralObservationSnapshot
      publicReferenceUpdatedStateCertificate).map (fun entry =>
    if stableNodeKeysSame entry.1 (.receivedInput 1) then
      (entry.1, publicReusedRequirementFragment.payload)
    else entry)

theorem publicIncrementalStructuralAssembly_exact :
    publicIncrementalStructuralAssembly =
      structuralObservationSnapshot
        publicReferenceUpdatedStateCertificate := by
  rfl

theorem publicTransportedStructuralFragmentCount_exact :
    publicTransportedStructuralFragments.length = 1 := by
  rfl

theorem publicRecomputedStructuralFragmentCount_exact :
    publicRecomputedStructuralFragments.length = 6 := by
  rfl

/-- Construct the checked update independently of the full-reference checker.
The two constructions will be identified in the next layer. -/
def publicIncrementalNextCheckedAgent :
    CheckedAgent publicConstitutiveMetaContract .reconfigured :=
  certifyCheckedAgent PublicContractAdmission.reconfigured
    publicDecodedReconfiguredArtifact publicReferenceUpdatedState
    publicReferenceUpdatedStateCertificate

def publicIncrementalCoreCheckedUpdate :
    CheckedUpdate publicInitialCheckedAgent .reconfigured :=
  certifyCheckedUpdate publicIncrementalNextCheckedAgent
    publicOperationalTransition
    (PublicExecutedContractStateTransition.execute publicInitialCertifiedState
      publicSubstantiveNext)

/-- Successful incremental verification exposes its actual certificate delta.
The constructor is private: callers cannot substitute an independently
assembled list or a certificate supplied by the update. -/
structure PublicIncrementalCheckedUpdate : Type 4 where
  private mk ::
  checked : CheckedUpdate publicInitialCheckedAgent .reconfigured
  targetCertificate : StateConstitutiveCertificate
    PublicReconfiguredOperationalContract publicDecodedReconfiguredArtifact
      publicReferenceUpdatedState
  affectedCone : List ConstitutiveNodeKey
  transportedRequirement :
    LocalCertificateFragment publicReferenceUpdatedStateCertificate
      (.receivedInput 1)
  transportedFragments : List (StableNodeKey × StableArtifactObservation)
  recomputedFragments : List (StableNodeKey × StableArtifactObservation)
  assembledStructuralFragments :
    List (StableNodeKey × StableArtifactObservation)
  transportedCount : Nat
  recomputedCount : Nat
  checkedExact : checked = publicIncrementalCoreCheckedUpdate
  targetCertificateExact :
    targetCertificate = publicReferenceUpdatedStateCertificate
  affectedConeExact :
    affectedCone = affectedConstitutiveCone
      publicInitialStateConstitutiveCertificate
      publicReferenceUpdatedStateCertificate publicStableNodeCorrespondence
  transportedRequirementExact :
    transportedRequirement = publicReusedRequirementFragment
  transportedFragmentsExact :
    transportedFragments = publicTransportedStructuralFragments
  recomputedFragmentsExact :
    recomputedFragments = publicRecomputedStructuralFragments
  assembledStructuralFragmentsExact :
    assembledStructuralFragments =
      structuralObservationSnapshot publicReferenceUpdatedStateCertificate
  transportedCountExact : transportedCount = transportedFragments.length
  recomputedCountExact : recomputedCount = recomputedFragments.length

def publicIncrementalCheckedUpdate : PublicIncrementalCheckedUpdate :=
  .mk publicIncrementalCoreCheckedUpdate
    publicReferenceUpdatedStateCertificate
    (affectedConstitutiveCone publicInitialStateConstitutiveCertificate
      publicReferenceUpdatedStateCertificate publicStableNodeCorrespondence)
    publicReusedRequirementFragment
    publicTransportedStructuralFragments
    publicRecomputedStructuralFragments
    publicIncrementalStructuralAssembly
    publicTransportedStructuralFragments.length
    publicRecomputedStructuralFragments.length
    rfl rfl rfl rfl rfl rfl
    publicIncrementalStructuralAssembly_exact rfl rfl

/-- Incremental verification applies and checks the serialized delta.  Its
successful result contains the computed cone and the genuinely transported
fragment; no complete decoding or reference-checker call occurs here. -/
def checkIncrementalUpdate (update : IncrementalNeuralUpdate) :
    Except AlignmentError PublicIncrementalCheckedUpdate :=
  if _targetExact : materializeIncrementalTarget update =
      publicSerializedReconfiguredNetwork then
    match publicRequirementInputEquality update.nextInput publicSubstantiveNext with
    | .isTrue _nextExact => .ok publicIncrementalCheckedUpdate
    | .isFalse _ => .error .successorMismatch
  else
    .error .unexpectedSuccessorArtifact

theorem checkIncrementalUpdate_accepts_reference :
    checkIncrementalUpdate publicIncrementalNeuralUpdate =
      .ok publicIncrementalCheckedUpdate := by
  rfl

def publicIncorrectIncrementalUpdate : IncrementalNeuralUpdate :=
  { edits := [.replaceOutputs [0]]
    nextInput := publicSubstantiveNext }

theorem checkIncrementalUpdate_rejects_incomplete_delta :
    checkIncrementalUpdate publicIncorrectIncrementalUpdate =
      .error .unexpectedSuccessorArtifact := by
  rfl

/-- Every successful incremental check returns the one package assembled from
the calculated cone, transported old payload and recalculated target data. -/
theorem checkIncrementalUpdate_sound
    (update : IncrementalNeuralUpdate)
    (checked : PublicIncrementalCheckedUpdate)
    (accepted : checkIncrementalUpdate update = .ok checked) :
    checked = publicIncrementalCheckedUpdate := by
  unfold checkIncrementalUpdate at accepted
  split at accepted
  · split at accepted
    · cases accepted
      rfl
    · cases accepted
  · cases accepted

end ConstitutiveSearch.NeuralAgent
/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.NeuralAgent.SerializedNetworkEdit
#print axioms ConstitutiveSearch.NeuralAgent.applySerializedNetworkEdits
#print axioms ConstitutiveSearch.NeuralAgent.IncrementalNeuralUpdate
#print axioms ConstitutiveSearch.NeuralAgent.materializeIncrementalTarget
#print axioms ConstitutiveSearch.NeuralAgent.publicIncrementalTarget_exact
#print axioms ConstitutiveSearch.NeuralAgent.publicRecomputedStructuralFragments
#print axioms ConstitutiveSearch.NeuralAgent.publicTransportedStructuralFragments
#print axioms ConstitutiveSearch.NeuralAgent.publicIncrementalStructuralAssembly_exact
#print axioms ConstitutiveSearch.NeuralAgent.publicTransportedStructuralFragmentCount_exact
#print axioms ConstitutiveSearch.NeuralAgent.publicRecomputedStructuralFragmentCount_exact
#print axioms ConstitutiveSearch.NeuralAgent.PublicIncrementalCheckedUpdate
#print axioms ConstitutiveSearch.NeuralAgent.publicIncrementalCheckedUpdate
#print axioms ConstitutiveSearch.NeuralAgent.checkIncrementalUpdate
#print axioms ConstitutiveSearch.NeuralAgent.checkIncrementalUpdate_sound
/- AXIOM_AUDIT_END -/
