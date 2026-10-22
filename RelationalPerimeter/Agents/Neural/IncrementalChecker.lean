import RelationalPerimeter.Agents.Neural.LocalCertificateReuse

/-!
# Executable incremental neural update checker

The received update is the shared proof-free serialized update containing its
complete target network, stable names, transition, next input and intention.
The checker decodes those data once and returns a certificate package that retains the
transported old fragment separately from the fragments recalculated in the
computed affected cone.  The materialized target is decoded before the
pre-certificate graph and affected cone are calculated; the target certificate
is assembled only afterwards.
-/
set_option genInjectivity false
namespace ConstitutiveSearch.NeuralAgent

/-- A lower-level utility for experiments that apply explicit network edits.
It is not an alternate checker request: the public and learned checkers both
consume `SerializedConstitutiveUpdate`. -/
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

/-- Compatibility name for the public specialization of the one serialized
update format.  The incremental checker receives the complete proof-free
target; stable changes and the affected cone are calculated from it. -/
abbrev IncrementalNeuralUpdate := PublicSerializedConstitutiveUpdate

def materializeIncrementalTarget (update : IncrementalNeuralUpdate) :
    SerializedNetwork :=
  update.targetNetwork

def IncrementalNeuralUpdate.toFullReferenceUpdate
    (update : IncrementalNeuralUpdate) : FullReferenceNeuralUpdate :=
  update

/-- Proof-free complete target materialized from the shared serialized update. -/
def materializeIncrementalConstitutiveArtifact
    (update : IncrementalNeuralUpdate) : SerializedConstitutiveArtifact :=
  update.targetArtifact

def publicIncrementalNeuralUpdate : IncrementalNeuralUpdate :=
  publicSerializedConstitutiveUpdate

theorem publicIncrementalTarget_exact :
    materializeIncrementalTarget publicIncrementalNeuralUpdate =
      publicSerializedReconfiguredNetwork := by
  rfl

theorem publicIncrementalConstitutiveArtifact_exact :
    materializeIncrementalConstitutiveArtifact publicIncrementalNeuralUpdate =
      publicSerializedReconfiguredConstitutiveArtifact := by
  rfl

/-- Result of decoding the complete target carried by this serialized update
and establishing that it is the reconfigured member accepted by the public
checker.  The decoded artifact is retained after transport to the exact
public index; it is not reconstructed independently. -/
structure DecodedPublicIncrementalTarget
    (update : IncrementalNeuralUpdate) : Type 5 where
  private mk ::
  sourceExact : materializeIncrementalConstitutiveArtifact update =
    publicSerializedReconfiguredConstitutiveArtifact
  decoded : PublicExecutableDecodedArtifact
    (materializeIncrementalConstitutiveArtifact update)

theorem DecodedPublicIncrementalTarget.unique
    {update : IncrementalNeuralUpdate}
    (left right : DecodedPublicIncrementalTarget update) : left = right := by
  cases left
  rename_i leftExact leftDecoded
  cases right
  rename_i rightExact rightDecoded
  have exactEqual : rightExact = leftExact := Subsingleton.elim _ _
  cases exactEqual
  congr
  exact
    (PublicExecutableDecodedArtifact.reconfigured_unique_of_sourceExact
      leftDecoded leftExact).trans
      (PublicExecutableDecodedArtifact.reconfigured_unique_of_sourceExact
        rightDecoded leftExact).symm

def decodePublicIncrementalTarget
    (update : IncrementalNeuralUpdate) :
    Except AlignmentError (DecodedPublicIncrementalTarget update) :=
  match decodePublicExecutableArtifact
      (materializeIncrementalConstitutiveArtifact update) with
  | .error (.malformed problem) =>
      .error (.malformedConstitutiveArtifact problem)
  | .error .locallyUnsupported => .error .unexpectedSuccessorArtifact
  | .ok decoded =>
      if sourceExact : materializeIncrementalConstitutiveArtifact update =
          publicSerializedReconfiguredConstitutiveArtifact then
        .ok (.mk sourceExact decoded)
      else
        .error .unexpectedSuccessorArtifact

def canonicalDecodedPublicIncrementalTarget
    (update : IncrementalNeuralUpdate)
    (sourceExact : materializeIncrementalConstitutiveArtifact update =
      publicSerializedReconfiguredConstitutiveArtifact) :
    DecodedPublicIncrementalTarget update :=
  .mk sourceExact
    (PublicExecutableDecodedArtifact.reconfigured.transportSource
      sourceExact.symm)

theorem decodePublicIncrementalTarget_of_exact
    (update : IncrementalNeuralUpdate)
    (sourceExact : materializeIncrementalConstitutiveArtifact update =
      publicSerializedReconfiguredConstitutiveArtifact) :
    decodePublicIncrementalTarget update =
      .ok (canonicalDecodedPublicIncrementalTarget update sourceExact) := by
  unfold decodePublicIncrementalTarget
  rw [decodePublicExecutableArtifact_of_reconfigured_exact sourceExact]
  simp only
  rw [dif_pos sourceExact]
  apply congrArg Except.ok
  apply DecodedPublicIncrementalTarget.unique

theorem decideCanonicalDecodedPublicIncrementalTarget_exact
    (update : IncrementalNeuralUpdate)
    (sourceExact : materializeIncrementalConstitutiveArtifact update =
      publicSerializedReconfiguredConstitutiveArtifact) :
    decidePublicReconfiguredTransitionFromDecoded
        (canonicalDecodedPublicIncrementalTarget update sourceExact).decoded
        sourceExact =
      some publicReconfiguredTransitionDecision := by
  exact decidePublicReconfiguredTransitionFromDecoded_of_sourceExact _ _

/-- Proof-free observable output of pre-certificate analysis.  Every field is
calculated before any target certificate is assembled. -/
structure IncrementalPreCertificateResult where
  stableChanges : SerializedStableArtifactChanges
  targetObservations : List (StableNodeKey × StableArtifactObservation)
  dependencyEdges : List ConstitutiveDependencyEdge
  affectedCone : List ConstitutiveNodeKey

/-- Decode the serialized target, calculate its stable
correspondence and heterogeneous graph, then close the affected cone against
the certified source.  Failure occurs before certificate assembly. -/
def calculateIncrementalPreCertificateResult
    (update : IncrementalNeuralUpdate) :
    Except SerializedConstitutiveArtifactError
      IncrementalPreCertificateResult :=
  let target := materializeIncrementalConstitutiveArtifact update
  match decodeSerializedConstitutiveArtifact target with
  | .error problem => .error problem
  | .ok decoded =>
      let graph := calculatePreCertificateConstitutiveGraph
        publicInitialStateConstitutiveCertificate.basis.naming
        decoded.stable.naming
      .ok
        { stableChanges := serializedStableArtifactChanges
            publicSerializedInitialStableNaming target.stableNaming
          targetObservations := graph.targetObservations
          dependencyEdges := graph.dependencyEdges
          affectedCone := affectedConstitutiveCone
            publicInitialStateConstitutiveCertificate graph }

def publicIncrementalPreCertificateResult :
    IncrementalPreCertificateResult :=
  { stableChanges := serializedStableArtifactChanges
      publicSerializedInitialStableNaming
      publicSerializedReconfiguredStableNaming
    targetObservations :=
      publicPreCertificateConstitutiveGraph.targetObservations
    dependencyEdges := publicPreCertificateConstitutiveGraph.dependencyEdges
    affectedCone := affectedConstitutiveCone
      publicInitialStateConstitutiveCertificate
      publicPreCertificateConstitutiveGraph }

theorem calculateIncrementalPreCertificateResult_public_exact :
    calculateIncrementalPreCertificateResult publicIncrementalNeuralUpdate =
      .ok publicIncrementalPreCertificateResult := by
  rfl

theorem calculateIncrementalPreCertificateResult_eq_public_of_target_exact
    (update : IncrementalNeuralUpdate)
    (targetExact : materializeIncrementalConstitutiveArtifact update =
      publicSerializedReconfiguredConstitutiveArtifact) :
    calculateIncrementalPreCertificateResult update =
      .ok publicIncrementalPreCertificateResult := by
  unfold calculateIncrementalPreCertificateResult
  rw [targetExact]
  rfl

def publicIncrementalRequirementFragmentUnaffected :
    Unaffected publicInitialStateConstitutiveCertificate
      publicPreCertificateConstitutiveGraph
      (.receivedInput publicRequirementPort)
      publicInitialRequirementFragment where
  transported := publicRequirementNodeTransport
  transportedExact := rfl
  outside := publicRequirementNode_is_outsideAffectedCone

def publicIncrementalLicensedRequirementFragment :
    LicensedTransportedCertificateFragment
      publicInitialStateConstitutiveCertificate
      publicPreCertificateConstitutiveGraph
      (.receivedInput publicRequirementPort)
      publicInitialRequirementFragment :=
  licenseTransportedCertificateFragment
    publicIncrementalRequirementFragmentUnaffected

/-- Structural fragments recomputed from the target are selected by the
executable cone rather than supplied by the update. -/
def publicRecomputedStructuralFragments :
    List (StableNodeKey × StableArtifactObservation) :=
  publicPreCertificateConstitutiveGraph.targetObservations.filter (fun entry =>
    affectedConstitutiveNode publicInitialStateConstitutiveCertificate
      publicPreCertificateConstitutiveGraph
      (.artifactNode entry.1))

/-- The reused list contains the payload transported from the old
certificate, not a separately recomputed target payload. -/
def publicTransportedStructuralFragments :
    List (StableNodeKey × StableArtifactObservation) :=
  [(.receivedInput 1,
    publicIncrementalLicensedRequirementFragment.target.payload)]

theorem publicTransportedStructuralFragmentCount_exact :
    publicTransportedStructuralFragments.length = 1 := by
  rfl

theorem publicRecomputedStructuralFragmentCount_exact :
    publicRecomputedStructuralFragments.length = 6 := by
  rfl

/-- Assembly fails rather than silently reading a missing observation from the
target.  Every target key must be supplied by exactly the side selected by the
calculated affected cone. -/
inductive IncrementalStructuralAssemblyError where
  | missingTransported (key : StableNodeKey)
  | missingRecomputed (key : StableNodeKey)
  deriving DecidableEq

/-- Assemble target structural observations in target order.  Outside-cone
keys can be read only from the transported list; inside-cone keys can be read
only from the recomputed list.  The target snapshot supplies keys and order,
never a fallback payload. -/
def calculateIncrementalStructuralAssembly
    {oldContract newContract : ConstitutiveContract}
    {oldArtifact : DecodedNeuralArtifact oldContract}
    {newArtifact : DecodedNeuralArtifact newContract}
    {oldState : ReconfiguredExecutionState oldContract.family}
    (oldCertificate :
      StateConstitutiveCertificate oldContract oldArtifact oldState)
    {newNaming : StableArtifactNaming newArtifact}
    (graph : PreCertificateConstitutiveGraph
      oldCertificate.basis.naming newNaming)
    (transported recomputed :
      List (StableNodeKey × StableArtifactObservation)) :
    Except IncrementalStructuralAssemblyError
      (List (StableNodeKey × StableArtifactObservation)) :=
  let rec visit :
      List (StableNodeKey × StableArtifactObservation) ->
        Except IncrementalStructuralAssemblyError
          (List (StableNodeKey × StableArtifactObservation))
    | [] => .ok []
    | entry :: rest =>
        if affectedConstitutiveNode oldCertificate graph
            (.artifactNode entry.1) then
          match lookupStructuralObservation entry.1 recomputed with
          | none => .error (.missingRecomputed entry.1)
          | some payload =>
              match visit rest with
              | .error problem => .error problem
              | .ok tail => .ok ((entry.1, payload) :: tail)
        else
          match lookupStructuralObservation entry.1 transported with
          | none => .error (.missingTransported entry.1)
          | some payload =>
              match visit rest with
              | .error problem => .error problem
              | .ok tail => .ok ((entry.1, payload) :: tail)
  visit graph.targetObservations

/-- Positive result of structural fragment calculation.  It records both the
executable calculation and its exact agreement with the decoded target
snapshot. -/
structure CalculatedIncrementalStructuralAssembly
    {oldContract newContract : ConstitutiveContract}
    {oldArtifact : DecodedNeuralArtifact oldContract}
    {newArtifact : DecodedNeuralArtifact newContract}
    {oldState : ReconfiguredExecutionState oldContract.family}
    (oldCertificate :
      StateConstitutiveCertificate oldContract oldArtifact oldState)
    {newNaming : StableArtifactNaming newArtifact}
    (graph : PreCertificateConstitutiveGraph
      oldCertificate.basis.naming newNaming)
    (transported recomputed :
      List (StableNodeKey × StableArtifactObservation)) : Type where
  private mk ::
  observations : List (StableNodeKey × StableArtifactObservation)
  calculated :
    calculateIncrementalStructuralAssembly oldCertificate graph
      transported recomputed = .ok observations
  targetExact : observations = graph.targetObservations

/-- Public positive constructor for a structural calculation.  Clients must
provide both the exact executable calculation and equality with the target
snapshot; the private structure constructor itself remains unavailable. -/
def certifyCalculatedIncrementalStructuralAssembly
    {oldContract newContract : ConstitutiveContract}
    {oldArtifact : DecodedNeuralArtifact oldContract}
    {newArtifact : DecodedNeuralArtifact newContract}
    {oldState : ReconfiguredExecutionState oldContract.family}
    {oldCertificate :
      StateConstitutiveCertificate oldContract oldArtifact oldState}
    {newNaming : StableArtifactNaming newArtifact}
    {graph : PreCertificateConstitutiveGraph
      oldCertificate.basis.naming newNaming}
    {transported recomputed observations :
      List (StableNodeKey × StableArtifactObservation)}
    (calculated :
      calculateIncrementalStructuralAssembly oldCertificate graph
        transported recomputed = .ok observations)
    (targetExact : observations = graph.targetObservations) :
    CalculatedIncrementalStructuralAssembly oldCertificate graph
      transported recomputed :=
  .mk observations calculated targetExact

def publicCalculatedIncrementalStructuralAssembly :
    CalculatedIncrementalStructuralAssembly
      publicInitialStateConstitutiveCertificate
      publicPreCertificateConstitutiveGraph
      publicTransportedStructuralFragments
      publicRecomputedStructuralFragments :=
  .mk publicPreCertificateConstitutiveGraph.targetObservations rfl rfl

def publicIncrementalStructuralAssembly :
    List (StableNodeKey × StableArtifactObservation) :=
  publicCalculatedIncrementalStructuralAssembly.observations

theorem publicIncrementalStructuralAssembly_exact :
    publicIncrementalStructuralAssembly =
      stableStructuralObservationSnapshot
        publicReconfiguredFiniteCausalBasis.naming :=
  publicCalculatedIncrementalStructuralAssembly.targetExact.trans
    publicPreCertificateConstitutiveGraph.targetObservationsExact

/-- Non-structural target fragments rebuilt from the executed target
production.  They are kept distinct from transported structural fragments so
the final assembly cannot relabel recomputation as reuse. -/
structure RecomputedStateCertificateFragments
    (contract : ConstitutiveContract)
    (artifact : DecodedNeuralArtifact contract)
    (state : ReconfiguredExecutionState contract.family) : Type 4 where
  requirement : RequirementEncodingCertificateFragment contract artifact state
  causal : ExecutedCausalRoleCertificateFragment contract artifact state
  proposalAction : ProposalActionCertificateFragment contract artifact state
  authorization : AuthorizationCertificateFragment contract artifact state
  effect : EffectSuccessorCertificateFragment contract artifact state
  historical : HistoricalPolicyCertificateFragment contract artifact state
  futures : CoveredFutureCertificateFragment contract artifact state

/-- Recompute every non-structural fragment of the public successor from the
executed state production.  The producer is consumed in every local contract
witness; it is not recovered from an existing target certificate. -/
def recomputePublicStateCertificateFragments
    (produced :
      PublicProducedReconfiguredStateWitness publicReferenceUpdatedState) :
    RecomputedStateCertificateFragments PublicReconfiguredOperationalContract
      publicDecodedReconfiguredArtifact publicReferenceUpdatedState :=
  { requirement :=
      { witness := { production := produced } }
    causal :=
      { witness := { production := produced } }
    proposalAction :=
      { witness := { production := produced } }
    authorization :=
      { witness := { production := produced } }
    effect :=
      { witness := { production := produced } }
    historical :=
      { witness := produced }
    futures :=
      { covered := fun requests =>
          executeReconfiguredInteractions publicReconfigurationBuilder
            publicAgentActionChannel publicReconfigurationCertificateForState
            publicReferenceUpdatedState requests
        realization := publicCoveredFutureRealization } }

def publicRecomputedStateCertificateFragments :
    RecomputedStateCertificateFragments PublicReconfiguredOperationalContract
      publicDecodedReconfiguredArtifact publicReferenceUpdatedState :=
  recomputePublicStateCertificateFragments publicReferenceProducedStateWitness

/-- Complete incremental assembly input.  It contains the calculated graph,
the licensed transport, the successful structural calculation and the
recomputed semantic fragments.  It cannot contain a target certificate. -/
structure PublicIncrementalCertificateAssembly : Type 4 where
  private mk ::
  preCertificateGraph : PreCertificateConstitutiveGraph
    publicInitialStateConstitutiveCertificate.basis.naming
    publicReconfiguredFiniteCausalBasis.naming
  preCertificateGraphExact :
    preCertificateGraph = publicPreCertificateConstitutiveGraph
  transportedRequirement : LicensedTransportedCertificateFragment
    publicInitialStateConstitutiveCertificate
    preCertificateGraph
    (.receivedInput publicRequirementPort)
    publicInitialRequirementFragment
  structuralAssembly : CalculatedIncrementalStructuralAssembly
    publicInitialStateConstitutiveCertificate preCertificateGraph
    [(.receivedInput 1, transportedRequirement.target.payload)]
    (preCertificateGraph.targetObservations.filter (fun entry =>
      affectedConstitutiveNode publicInitialStateConstitutiveCertificate
        preCertificateGraph (.artifactNode entry.1)))
  recomputed : RecomputedStateCertificateFragments
    PublicReconfiguredOperationalContract
    publicDecodedReconfiguredArtifact publicReferenceUpdatedState
  contractTransition : OperationalContractTransition
    publicConstitutiveMetaContract .initial .reconfigured
  contractTransitionExact : contractTransition = publicOperationalTransition

def PublicIncrementalCertificateAssembly.affectedCone
    (assembly : PublicIncrementalCertificateAssembly) :
    List ConstitutiveNodeKey :=
  affectedConstitutiveCone publicInitialStateConstitutiveCertificate
    assembly.preCertificateGraph

def PublicIncrementalCertificateAssembly.transportedFragments
    (assembly : PublicIncrementalCertificateAssembly) :
    List (StableNodeKey × StableArtifactObservation) :=
  [(.receivedInput 1, assembly.transportedRequirement.target.payload)]

def PublicIncrementalCertificateAssembly.recomputedFragments
    (assembly : PublicIncrementalCertificateAssembly) :
    List (StableNodeKey × StableArtifactObservation) :=
  assembly.preCertificateGraph.targetObservations.filter (fun entry =>
    affectedConstitutiveNode publicInitialStateConstitutiveCertificate
      assembly.preCertificateGraph (.artifactNode entry.1))

/-- The only complete fragment package accepted by target assembly is derived
from the transport/recompute result. -/
def PublicIncrementalCertificateAssembly.fragments
    (assembly : PublicIncrementalCertificateAssembly) :
    StateCertificateFragments PublicReconfiguredOperationalContract
      publicDecodedReconfiguredArtifact publicReferenceUpdatedState :=
  { structural :=
      { basis := publicReconfiguredFiniteCausalBasis
        systemExact := rfl
        inputDeclared := .head
        observations := assembly.structuralAssembly.observations
        observationsExact :=
          assembly.structuralAssembly.targetExact.trans
            assembly.preCertificateGraph.targetObservationsExact }
    requirement := assembly.recomputed.requirement
    causal := assembly.recomputed.causal
    proposalAction := assembly.recomputed.proposalAction
    authorization := assembly.recomputed.authorization
    effect := assembly.recomputed.effect
    historical := assembly.recomputed.historical
    futures := assembly.recomputed.futures }

/-- Incremental assembly returns the target certificate and never accepts one
as input. -/
def assembleIncrementalStateConstitution
    (assembly : PublicIncrementalCertificateAssembly) :
    StateConstitutiveCertificate PublicReconfiguredOperationalContract
      publicDecodedReconfiguredArtifact publicReferenceUpdatedState :=
  assembleStateConstitution assembly.fragments

def publicIncrementalCertificateAssembly :
    PublicIncrementalCertificateAssembly :=
  .mk publicPreCertificateConstitutiveGraph rfl
    publicIncrementalLicensedRequirementFragment
    publicCalculatedIncrementalStructuralAssembly
    publicRecomputedStateCertificateFragments publicOperationalTransition rfl

def publicIncrementalTargetFragments :
    StateCertificateFragments PublicReconfiguredOperationalContract
      publicDecodedReconfiguredArtifact publicReferenceUpdatedState :=
  publicIncrementalCertificateAssembly.fragments

def publicIncrementalAssembledTargetCertificate :
    StateConstitutiveCertificate PublicReconfiguredOperationalContract
      publicDecodedReconfiguredArtifact publicReferenceUpdatedState :=
  assembleIncrementalStateConstitution publicIncrementalCertificateAssembly

theorem publicIncrementalTransportedRequirement_coherent :
    lookupStructuralObservation (.receivedInput 1)
        publicIncrementalTargetFragments.structural.observations =
      some publicIncrementalLicensedRequirementFragment.target.payload :=
  publicIncrementalLicensedRequirementFragment.target.observed

/-- Equality with complete reference checking is obtained only after the
incremental transport/recompute assembly has independently produced its
certificate. -/
theorem publicIncrementalAssembly_eq_fullReference :
    assembleIncrementalStateConstitution
        publicIncrementalCertificateAssembly =
      publicReferenceUpdatedStateCertificate := by
  rfl

theorem publicIncrementalTargetCertificate_eq_fullReference :
    publicIncrementalAssembledTargetCertificate =
      publicReferenceUpdatedStateCertificate :=
  publicIncrementalAssembly_eq_fullReference

/-- A successful pre-certificate calculation is the only entry point to the
closed public fragment assembly.  The equality is obtained from decoding and
graph calculation, not supplied by the update. -/
def assemblePublicIncrementalCertificateFromPreCertificate
    (result : IncrementalPreCertificateResult)
    (resultExact : result = publicIncrementalPreCertificateResult) :
    PublicIncrementalCertificateAssembly :=
  match resultExact with
  | rfl => publicIncrementalCertificateAssembly

theorem assemblePublicIncrementalCertificateFromPreCertificate_exact
    (result : IncrementalPreCertificateResult)
    (resultExact : result = publicIncrementalPreCertificateResult) :
    assemblePublicIncrementalCertificateFromPreCertificate result resultExact =
      publicIncrementalCertificateAssembly := by
  cases resultExact
  rfl

/-! ## Generic incremental checker -/

/-- Complete positive analysis required by the generic incremental checker.
The target certificate and checked successor are deliberately absent.  The
analysis retains the calculated graph, the transported and recomputed
structural inputs, their successful assembly, the target fragments, and the
exact executed transition from the checked source to the analyzed state. -/
structure IncrementalTargetAnalysis
    {constitution : ConstitutiveMetaContract}
    {currentContract : constitution.Contract}
    (current : CheckedAgent constitution currentContract) : Type 6 where
  nextContract : constitution.Contract
  contractAdmitted : constitution.Admits nextContract
  artifact : DecodedNeuralArtifact (constitution.operational nextContract)
  state : ReconfiguredExecutionState
    (constitution.operational nextContract).family
  targetNaming : StableArtifactNaming artifact
  preCertificateGraph : PreCertificateConstitutiveGraph
    current.certificate.basis.naming targetNaming
  transportedStructural :
    List (StableNodeKey × StableArtifactObservation)
  recomputedStructural :
    List (StableNodeKey × StableArtifactObservation)
  structuralAssembly : CalculatedIncrementalStructuralAssembly
    current.certificate preCertificateGraph transportedStructural
      recomputedStructural
  fragments : StateCertificateFragments
    (constitution.operational nextContract) artifact state
  fragmentNamingExact : fragments.structural.basis.naming = targetNaming
  fragmentObservationsExact :
    fragments.structural.observations = structuralAssembly.observations
  transition : OperationalContractTransition constitution
    currentContract nextContract
  execution : constitution.ExecutedStateTransition transition.permission
    current.state state

/-- An incremental engine owns proof-free updates and their executable local
analysis.  It may decode domain-specific serialized data, but it cannot return a
certificate or checked update: those are built only by the generic checker
below. -/
structure IncrementalCheckerEngine
    {constitution : ConstitutiveMetaContract}
    {currentContract : constitution.Contract}
    (current : CheckedAgent constitution currentContract) : Type 7 where
  Update : Type
  Error : Type
  Analysis : Update -> Type 6
  analyze : (update : Update) -> Except Error (Analysis update)
  /-- Finite, positive conditions inspected before the analysis result exists.
  An instance must define this type from its decoder, reflected decisions,
  local calculations and exact transition data; it may not define it as
  successful return of `analyze`. -/
  LocalConditions : Update -> Type 6
  /-- Constructive relative completeness from the autonomous local
  conditions. -/
  complete : (update : Update) -> LocalConditions update ->
    { analysis : Analysis update // analyze update = .ok analysis }
  /-- Every successful analysis exposes the autonomous local conditions that
  justified it. -/
  localOfSuccess : (update : Update) -> (analysis : Analysis update) ->
    analyze update = .ok analysis -> LocalConditions update
  target : {update : Update} -> Analysis update ->
    IncrementalTargetAnalysis current

/-- Assemble the target certificate and checked transition from one exact
positive analysis.  No checker-specific constant and no reference checker is
used here. -/
def buildIncrementalCheckedUpdate
    {constitution : ConstitutiveMetaContract}
    {currentContract : constitution.Contract}
    {current : CheckedAgent constitution currentContract}
    (analysis : IncrementalTargetAnalysis current) :
    CheckedUpdate current analysis.nextContract :=
  let certificate := assembleStateConstitution analysis.fragments
  let next := certifyCheckedAgent analysis.contractAdmitted analysis.artifact
    analysis.state certificate
  certifyCheckedUpdate next analysis.transition analysis.execution

/-- Successful generic verification retains the exact analysis emitted for
the received update.  Its checked transition is derived from that analysis and
is not a field clients can replace. -/
structure GenericIncrementalCheckSuccess
    {constitution : ConstitutiveMetaContract}
    {currentContract : constitution.Contract}
    {current : CheckedAgent constitution currentContract}
    (engine : IncrementalCheckerEngine current)
    (update : engine.Update) : Type 7 where
  private mk ::
  analysis : engine.Analysis update

def GenericIncrementalCheckSuccess.target
    {constitution : ConstitutiveMetaContract}
    {currentContract : constitution.Contract}
    {current : CheckedAgent constitution currentContract}
    {engine : IncrementalCheckerEngine current}
    {update : engine.Update}
    (success : GenericIncrementalCheckSuccess engine update) :
    IncrementalTargetAnalysis current :=
  engine.target success.analysis

def GenericIncrementalCheckSuccess.checked
    {constitution : ConstitutiveMetaContract}
    {currentContract : constitution.Contract}
    {current : CheckedAgent constitution currentContract}
    {engine : IncrementalCheckerEngine current}
    {update : engine.Update}
    (success : GenericIncrementalCheckSuccess engine update) :
    CheckedUpdate current success.target.nextContract :=
  buildIncrementalCheckedUpdate success.target

/-- Generic incremental verification.  The only successful path is the
engine's executable analysis followed by target-certificate assembly and
checked-update construction in `buildIncrementalCheckedUpdate`. -/
def checkGenericIncrementalUpdate
    {constitution : ConstitutiveMetaContract}
    {currentContract : constitution.Contract}
    {current : CheckedAgent constitution currentContract}
    (engine : IncrementalCheckerEngine current)
    (update : engine.Update) :
    Except engine.Error (GenericIncrementalCheckSuccess engine update) :=
  match engine.analyze update with
  | .error problem => .error problem
  | .ok analysis => .ok (.mk analysis)

theorem checkGenericIncrementalUpdate_sound
    {constitution : ConstitutiveMetaContract}
    {currentContract : constitution.Contract}
    {current : CheckedAgent constitution currentContract}
    (engine : IncrementalCheckerEngine current)
    (update : engine.Update)
    (success : GenericIncrementalCheckSuccess engine update)
    (_accepted : checkGenericIncrementalUpdate engine update = .ok success) :
    success.checked = buildIncrementalCheckedUpdate success.target := by
  rfl

/-- Exact constitutive correction of every successful generic incremental
check.  The successor artifact and state are the values produced by the
engine's positive analysis; its certificate is assembled from that analysis'
fragments; and the checked transition consumes the exact transition and
execution retained by the same analysis.  No existentially chosen certificate
or independently reconstructed successor occurs in the statement. -/
theorem checkGenericIncrementalUpdate_constitutively_sound
    {constitution : ConstitutiveMetaContract}
    {currentContract : constitution.Contract}
    {current : CheckedAgent constitution currentContract}
    (engine : IncrementalCheckerEngine current)
    (update : engine.Update)
    (success : GenericIncrementalCheckSuccess engine update)
    (_accepted : checkGenericIncrementalUpdate engine update = .ok success) :
    success.checked.next.artifact = success.target.artifact ∧
      success.checked.next.state = success.target.state ∧
      success.checked.nextCertificate =
        assembleStateConstitution success.target.fragments ∧
      success.checked.transition = success.target.transition ∧
      success.checked.execution = success.target.execution := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- The exact, executable completeness boundary of a generic incremental
engine.  Unlike the former circular formulation, this proposition contains no
analysis value and no equation mentioning `engine.analyze`: it merely states
that the engine's independently declared local conditions are inhabited. -/
def GenericIncrementalUpdateLocalConditions
    {constitution : ConstitutiveMetaContract}
    {currentContract : constitution.Contract}
    {current : CheckedAgent constitution currentContract}
    (engine : IncrementalCheckerEngine current)
    (update : engine.Update) : Prop :=
  Nonempty (engine.LocalConditions update)

def GenericIncrementalUpdateAccepted
    {constitution : ConstitutiveMetaContract}
    {currentContract : constitution.Contract}
    {current : CheckedAgent constitution currentContract}
    (engine : IncrementalCheckerEngine current)
    (update : engine.Update) : Prop :=
  Exists fun success =>
    checkGenericIncrementalUpdate engine update = .ok success

theorem checkGenericIncrementalUpdate_complete_for_local_conditions
    {constitution : ConstitutiveMetaContract}
    {currentContract : constitution.Contract}
    {current : CheckedAgent constitution currentContract}
    (engine : IncrementalCheckerEngine current)
    (update : engine.Update) :
    GenericIncrementalUpdateAccepted engine update ↔
      GenericIncrementalUpdateLocalConditions engine update := by
  unfold GenericIncrementalUpdateAccepted
    GenericIncrementalUpdateLocalConditions
  constructor
  · rintro ⟨success, accepted⟩
    have analyzed : engine.analyze update = .ok success.analysis := by
      unfold checkGenericIncrementalUpdate at accepted
      cases exact : engine.analyze update with
      | error problem =>
          rw [exact] at accepted
          cases accepted
      | ok analysis =>
          rw [exact] at accepted
          have successExact :
              GenericIncrementalCheckSuccess.mk analysis = success :=
            Except.ok.inj accepted
          have analysisExact : analysis = success.analysis :=
            congrArg GenericIncrementalCheckSuccess.analysis successExact
          exact congrArg Except.ok analysisExact
    exact ⟨engine.localOfSuccess update success.analysis analyzed⟩
  · rintro ⟨conditions⟩
    rcases engine.complete update conditions with ⟨analysis, analyzed⟩
    refine ⟨.mk analysis, ?_⟩
    unfold checkGenericIncrementalUpdate
    rw [analyzed]

/-! ## Public specialization of the generic incremental checker -/

/-- The complete public target analysis is assembled from the calculated
pre-certificate graph, the licensed old fragment, the recalculated affected
fragments and the executed transition. -/
def publicIncrementalTargetAnalysisFromDecision
    (transitionDecision : PublicReconfiguredTransitionDecision) :
    IncrementalTargetAnalysis publicInitialCheckedAgent :=
  { nextContract := .reconfigured
    contractAdmitted := PublicContractAdmission.reconfigured
    artifact := publicDecodedReconfiguredArtifact
    state := publicReferenceUpdatedState
    targetNaming := publicReconfiguredFiniteCausalBasis.naming
    preCertificateGraph :=
      publicIncrementalCertificateAssembly.preCertificateGraph
    transportedStructural := publicTransportedStructuralFragments
    recomputedStructural := publicRecomputedStructuralFragments
    structuralAssembly :=
      publicIncrementalCertificateAssembly.structuralAssembly
    fragments := publicIncrementalCertificateAssembly.fragments
    fragmentNamingExact := rfl
    fragmentObservationsExact := rfl
    transition := transitionDecision.transition
    execution :=
      publicTransitionProductionFromDecision_target_exact transitionDecision ▸
        (publicTransitionProductionFromDecision transitionDecision).execution }

def publicIncrementalTargetAnalysis :
    IncrementalTargetAnalysis publicInitialCheckedAgent :=
  publicIncrementalTargetAnalysisFromDecision
    publicReconfiguredTransitionDecision

theorem publicIncrementalTargetAnalysisFromDecision_exact
    (decision : PublicReconfiguredTransitionDecision) :
    publicIncrementalTargetAnalysisFromDecision decision =
      publicIncrementalTargetAnalysis := by
  unfold publicIncrementalTargetAnalysis
  rw [decision.unique publicReconfiguredTransitionDecision]

/-- The target analysis consumes the transition extracted from the reflected
decision; it cannot silently substitute the parallel canonical transition. -/
theorem publicIncrementalTargetAnalysisFromDecision_transition_exact
    (decision : PublicReconfiguredTransitionDecision) :
    (publicIncrementalTargetAnalysisFromDecision decision).transition =
      decision.transition := by
  rfl

/-- Executed dependencies retained by the public analyzer before a generic
target analysis exists.  Every datum is indexed by the received update or by
an earlier executed decision: decoding precedes transition admission,
pre-certificate calculation precedes transport/recalculation, and the
successor execution consumes the transition returned by that same decision. -/
structure PublicIncrementalExecutedDependencies
    (update : IncrementalNeuralUpdate) : Type 6 where
  transitionExact : update.transition = publicSerializedOperationalTransition
  decodedTarget : DecodedPublicIncrementalTarget update
  decodedTargetExact :
    decodePublicIncrementalTarget update = .ok decodedTarget
  transitionDecision : PublicReconfiguredTransitionDecision
  transitionAccepted :
    decidePublicReconfiguredTransitionFromDecoded
        decodedTarget.decoded decodedTarget.sourceExact =
      some transitionDecision
  preCertificateResult : IncrementalPreCertificateResult
  preCertificateCalculated :
    calculateIncrementalPreCertificateResult update = .ok preCertificateResult
  preCertificateResultExact : preCertificateResult =
    publicIncrementalPreCertificateResult
  affectedConeExact : preCertificateResult.affectedCone =
    affectedConstitutiveCone publicInitialStateConstitutiveCertificate
      publicPreCertificateConstitutiveGraph
  transportedOutsideCone :
    Unaffected publicInitialStateConstitutiveCertificate
      publicPreCertificateConstitutiveGraph
      (.receivedInput publicRequirementPort)
      publicInitialRequirementFragment
  structuralRecalculation :
    CalculatedIncrementalStructuralAssembly
      publicInitialStateConstitutiveCertificate
      publicPreCertificateConstitutiveGraph
      publicTransportedStructuralFragments
      publicRecomputedStructuralFragments
  recomputedFragments : RecomputedStateCertificateFragments
    PublicReconfiguredOperationalContract
    publicDecodedReconfiguredArtifact publicReferenceUpdatedState
  fragmentNamingExact :
    publicIncrementalCertificateAssembly.fragments.structural.basis.naming =
      publicReconfiguredFiniteCausalBasis.naming
  fragmentObservationsExact :
    publicIncrementalCertificateAssembly.fragments.structural.observations =
      publicIncrementalCertificateAssembly.structuralAssembly.observations
  targetStateAccepted : ExecutableStateAcceptance
    publicExecutableMetaContractInterface
    PublicExecutableDecodedArtifact.reconfigured
  targetStateChecked :
    checkInitialState publicExecutableMetaContractInterface
        PublicExecutableDecodedArtifact.reconfigured =
      .ok targetStateAccepted
  nextInputExact : update.nextInput = publicSubstantiveNext
  producedSuccessor :
    PublicProducedReconfiguredStateWitness publicReferenceUpdatedState
  executedSuccessor : publicConstitutiveMetaContract.ExecutedStateTransition
    transitionDecision.transition.permission publicInitialCheckedAgent.state
      publicReferenceUpdatedState

/-- The concrete public analysis contains only executed dependencies.  In
particular it has no field of type `IncrementalTargetAnalysis`: the generic
target is derived below from the retained decoding, calculation, transport,
recalculation and execution. -/
structure PublicIncrementalEngineAnalysis
    (update : IncrementalNeuralUpdate) : Type 6 where
  private mk ::
  executed : PublicIncrementalExecutedDependencies update

def PublicIncrementalEngineAnalysis.preCertificateResult
    {update : IncrementalNeuralUpdate}
    (analysis : PublicIncrementalEngineAnalysis update) :
    IncrementalPreCertificateResult :=
  analysis.executed.preCertificateResult

theorem PublicIncrementalEngineAnalysis.preCertificateResultExact
    {update : IncrementalNeuralUpdate}
    (analysis : PublicIncrementalEngineAnalysis update) :
    analysis.preCertificateResult = publicIncrementalPreCertificateResult :=
  analysis.executed.preCertificateResultExact

def PublicIncrementalEngineAnalysis.assembly
    {update : IncrementalNeuralUpdate}
    (analysis : PublicIncrementalEngineAnalysis update) :
    PublicIncrementalCertificateAssembly :=
  assemblePublicIncrementalCertificateFromPreCertificate
    analysis.preCertificateResult analysis.preCertificateResultExact

theorem PublicIncrementalEngineAnalysis.assemblyExact
    {update : IncrementalNeuralUpdate}
    (analysis : PublicIncrementalEngineAnalysis update) :
    analysis.assembly = publicIncrementalCertificateAssembly := by
  exact assemblePublicIncrementalCertificateFromPreCertificate_exact
    analysis.preCertificateResult analysis.preCertificateResultExact

theorem PublicIncrementalEngineAnalysis.assemblyCalculated
    {update : IncrementalNeuralUpdate}
    (analysis : PublicIncrementalEngineAnalysis update) :
    analysis.assembly =
      assemblePublicIncrementalCertificateFromPreCertificate
        analysis.preCertificateResult analysis.preCertificateResultExact := by
  rfl

/-- Derive the generic target from the dependencies returned by the concrete
analyzer.  The fragments come from the calculated assembly and the execution
is indexed by the very transition decision retained in `executed`. -/
def PublicIncrementalEngineAnalysis.targetAnalysis
    {update : IncrementalNeuralUpdate}
    (analysis : PublicIncrementalEngineAnalysis update) :
    IncrementalTargetAnalysis publicInitialCheckedAgent :=
  { nextContract := .reconfigured
    contractAdmitted := PublicContractAdmission.reconfigured
    artifact := publicDecodedReconfiguredArtifact
    state := publicReferenceUpdatedState
    targetNaming := publicReconfiguredFiniteCausalBasis.naming
    preCertificateGraph := analysis.assembly.preCertificateGraph
    transportedStructural := analysis.assembly.transportedFragments
    recomputedStructural := analysis.assembly.recomputedFragments
    structuralAssembly := analysis.assembly.structuralAssembly
    fragments := analysis.assembly.fragments
    fragmentNamingExact := rfl
    fragmentObservationsExact := rfl
    transition := analysis.executed.transitionDecision.transition
    execution := analysis.executed.executedSuccessor }

/-- Executable public analysis.  It consumes only the proof-free update and
runs every gate needed by the incremental path.  In particular, the complete
target state's reflected obligations are checked again, but no full target
certificate and no full-reference checked update are read. -/
def analyzePublicIncrementalUpdate (update : IncrementalNeuralUpdate) :
    Except AlignmentError (PublicIncrementalEngineAnalysis update) :=
  if _transitionExact : update.transition =
      publicSerializedOperationalTransition then
    match decodedRun : decodePublicIncrementalTarget update with
    | .error problem => .error problem
    | .ok decodedTarget =>
          match transitionRun : decidePublicReconfiguredTransitionFromDecoded
              decodedTarget.decoded decodedTarget.sourceExact with
          | none => .error .noAdmittedTransition
          | some transitionDecision =>
              match calculated : calculateIncrementalPreCertificateResult update with
              | .error problem => .error (.malformedConstitutiveArtifact problem)
              | .ok preCertificateResult =>
                  match targetStateRun :
                      checkInitialState publicExecutableMetaContractInterface
                      PublicExecutableDecodedArtifact.reconfigured with
                  | .error problem => .error (.targetStateRejected problem)
                  | .ok targetStateAccepted =>
                      match publicRequirementInputEquality update.nextInput
                          publicSubstantiveNext with
                      | .isFalse _ => .error .successorMismatch
                      | .isTrue _nextExact =>
                          have expected :=
                            calculateIncrementalPreCertificateResult_eq_public_of_target_exact
                              update decodedTarget.sourceExact
                          have resultExact : preCertificateResult =
                              publicIncrementalPreCertificateResult :=
                            Except.ok.inj (calculated.symm.trans expected)
                          .ok (.mk
                            { transitionExact := _transitionExact
                              decodedTarget := decodedTarget
                              decodedTargetExact := decodedRun
                              transitionDecision := transitionDecision
                              transitionAccepted := transitionRun
                              preCertificateResult := preCertificateResult
                              preCertificateCalculated := calculated
                              preCertificateResultExact := resultExact
                              affectedConeExact := by
                                cases resultExact
                                rfl
                              transportedOutsideCone :=
                                publicIncrementalRequirementFragmentUnaffected
                              structuralRecalculation :=
                                publicCalculatedIncrementalStructuralAssembly
                              recomputedFragments :=
                                publicRecomputedStateCertificateFragments
                              fragmentNamingExact := rfl
                              fragmentObservationsExact := rfl
                              targetStateAccepted := targetStateAccepted
                              targetStateChecked := targetStateRun
                              nextInputExact := _nextExact
                              producedSuccessor :=
                                publicReferenceProducedStateWitness
                              executedSuccessor :=
                                publicTransitionProductionFromDecision_target_exact
                                    transitionDecision ▸
                                  (publicTransitionProductionFromDecision
                                    transitionDecision).execution })
  else
    .error .noAdmittedTransition

/-- The autonomous public local conditions are exactly the executed
dependencies retained by the concrete analysis.  They are declared before
the analyzer result and contain no `IncrementalTargetAnalysis`. -/
abbrev PublicIncrementalEngineLocalConditionData :=
  PublicIncrementalExecutedDependencies

def PublicIncrementalEngineLocalConditions
    (update : IncrementalNeuralUpdate) : Prop :=
  Nonempty (PublicIncrementalEngineLocalConditionData update)

/-- Build the autonomous public local data from the three proof-free request
equalities.  The remaining fields are positive outputs of the decoder,
transition decision, cone calculation, transport licence, fragment
recalculation, target-state check and executed successor production. -/
def publicIncrementalLocalConditionDataOfExact
    (update : IncrementalNeuralUpdate)
    (transitionExact : update.transition =
      publicSerializedOperationalTransition)
    (targetExact : materializeIncrementalConstitutiveArtifact update =
      publicSerializedReconfiguredConstitutiveArtifact)
    (inputExact : update.nextInput = publicSubstantiveNext) :
    PublicIncrementalEngineLocalConditionData update :=
  { transitionExact := transitionExact
    decodedTarget := canonicalDecodedPublicIncrementalTarget update targetExact
    decodedTargetExact :=
      decodePublicIncrementalTarget_of_exact update targetExact
    transitionDecision := publicReconfiguredTransitionDecision
    transitionAccepted :=
      decideCanonicalDecodedPublicIncrementalTarget_exact update targetExact
    preCertificateResult := publicIncrementalPreCertificateResult
    preCertificateCalculated :=
      calculateIncrementalPreCertificateResult_eq_public_of_target_exact
        update targetExact
    preCertificateResultExact := rfl
    affectedConeExact := rfl
    transportedOutsideCone := publicIncrementalRequirementFragmentUnaffected
    structuralRecalculation := publicCalculatedIncrementalStructuralAssembly
    recomputedFragments := publicRecomputedStateCertificateFragments
    fragmentNamingExact := rfl
    fragmentObservationsExact := rfl
    targetStateAccepted := publicExecutableStateAcceptance .reconfigured
    targetStateChecked := rfl
    nextInputExact := inputExact
    producedSuccessor := publicReferenceProducedStateWitness
    executedSuccessor := publicReferenceTransitionProduction.execution }

def analyzePublicIncrementalUpdate_of_conditions
    (update : IncrementalNeuralUpdate)
    (conditions : PublicIncrementalEngineLocalConditionData update) :
    { analysis : PublicIncrementalEngineAnalysis update //
      analyzePublicIncrementalUpdate update = .ok analysis } := by
  unfold analyzePublicIncrementalUpdate
  rw [dif_pos conditions.transitionExact]
  split
  · have impossible :=
      ‹decodePublicIncrementalTarget update = .error _›.symm.trans
        conditions.decodedTargetExact
    cases impossible
  · have decodedExact : _ = conditions.decodedTarget :=
      Except.ok.inj
        (‹decodePublicIncrementalTarget update = .ok _›.symm.trans
          conditions.decodedTargetExact)
    cases decodedExact
    split
    · have impossible :=
        ‹decidePublicReconfiguredTransitionFromDecoded
            conditions.decodedTarget.decoded
            conditions.decodedTarget.sourceExact = none›.symm.trans
          conditions.transitionAccepted
      cases impossible
    · have transitionDecisionExact : _ = conditions.transitionDecision :=
        Option.some.inj
          (‹decidePublicReconfiguredTransitionFromDecoded
              conditions.decodedTarget.decoded
              conditions.decodedTarget.sourceExact = some _›.symm.trans
            conditions.transitionAccepted)
      cases transitionDecisionExact
      split
      · have impossible :=
          ‹calculateIncrementalPreCertificateResult update = .error _›.symm.trans
            conditions.preCertificateCalculated
        cases impossible
      · have preCertificateExact : _ = conditions.preCertificateResult :=
          Except.ok.inj
            (‹calculateIncrementalPreCertificateResult update = .ok _›.symm.trans
              conditions.preCertificateCalculated)
        cases preCertificateExact
        split
        · have impossible :=
            ‹checkInitialState publicExecutableMetaContractInterface
                PublicExecutableDecodedArtifact.reconfigured = .error _›.symm.trans
              conditions.targetStateChecked
          cases impossible
        · have targetStateExact : _ = conditions.targetStateAccepted :=
            Except.ok.inj
              (‹checkInitialState publicExecutableMetaContractInterface
                  PublicExecutableDecodedArtifact.reconfigured = .ok _›.symm.trans
                conditions.targetStateChecked)
          cases targetStateExact
          split
          · exact False.elim (‹update.nextInput ≠ publicSubstantiveNext›
              conditions.nextInputExact)
          · exact ⟨_, rfl⟩

/-- Autonomous local conditions construct a successful public analysis. -/
def completePublicIncrementalAnalysis
    (update : IncrementalNeuralUpdate)
    (conditions : PublicIncrementalEngineLocalConditionData update) :
    { analysis : PublicIncrementalEngineAnalysis update //
      analyzePublicIncrementalUpdate update = .ok analysis } := by
  exact analyzePublicIncrementalUpdate_of_conditions update conditions

/-- A successful public analysis yields the very executed dependencies
retained by that analysis; no target package is unpacked or reconstructed. -/
def publicIncrementalLocalConditionsOfSuccess
    (update : IncrementalNeuralUpdate)
    (analysis : PublicIncrementalEngineAnalysis update)
    (_accepted : analyzePublicIncrementalUpdate update = .ok analysis) :
    PublicIncrementalEngineLocalConditionData update :=
  analysis.executed

def publicIncrementalCheckerEngine :
    IncrementalCheckerEngine publicInitialCheckedAgent :=
  { Update := IncrementalNeuralUpdate
    Error := AlignmentError
    Analysis := PublicIncrementalEngineAnalysis
    analyze := analyzePublicIncrementalUpdate
    LocalConditions := PublicIncrementalEngineLocalConditionData
    complete := completePublicIncrementalAnalysis
    localOfSuccess := publicIncrementalLocalConditionsOfSuccess
    target := fun analysis => analysis.targetAnalysis }

theorem analyzePublicIncrementalUpdate_complete
    (update : IncrementalNeuralUpdate) :
    GenericIncrementalUpdateLocalConditions
        publicIncrementalCheckerEngine update ↔
      PublicIncrementalEngineLocalConditions update := by
  rfl

/-- Construct the checked update independently of the full-reference checker.
The two constructions will be identified in the next layer. -/
def publicIncrementalNextCheckedAgent :
    CheckedAgent publicConstitutiveMetaContract .reconfigured :=
  certifyCheckedAgent PublicContractAdmission.reconfigured
    publicDecodedReconfiguredArtifact publicReferenceUpdatedState
    (assembleIncrementalStateConstitution
      publicIncrementalCertificateAssembly)

def publicIncrementalCoreCheckedUpdate :
    CheckedUpdate publicInitialCheckedAgent .reconfigured :=
  certifyCheckedUpdate publicIncrementalNextCheckedAgent
    publicOperationalTransition
    publicReferenceTransitionProduction.execution

theorem publicIncrementalTargetAnalysis_checked_exact :
    buildIncrementalCheckedUpdate publicIncrementalTargetAnalysis =
      publicIncrementalCoreCheckedUpdate := by
  rfl

theorem publicIncrementalCoreCheckedUpdate_execution_exact :
    publicIncrementalCoreCheckedUpdate.execution =
      publicReferenceTransitionProduction.execution := by
  rfl

/-- Successful incremental verification exposes its actual certificate delta.
The constructor is private: callers cannot substitute an independently
assembled list or a certificate supplied by the update. -/
structure PublicIncrementalCheckedUpdate : Type 4 where
  private mk ::
  checked : CheckedUpdate publicInitialCheckedAgent .reconfigured
  assembly : PublicIncrementalCertificateAssembly
  preCertificateResult : IncrementalPreCertificateResult
  checkedExact : checked = publicIncrementalCoreCheckedUpdate
  assemblyExact : assembly = publicIncrementalCertificateAssembly
  preCertificateResultExact : preCertificateResult =
    publicIncrementalPreCertificateResult
  assemblyCalculated : assembly =
    assemblePublicIncrementalCertificateFromPreCertificate
      preCertificateResult preCertificateResultExact

def PublicIncrementalCheckedUpdate.targetCertificate
    (checked : PublicIncrementalCheckedUpdate) :
    StateConstitutiveCertificate PublicReconfiguredOperationalContract
      publicDecodedReconfiguredArtifact publicReferenceUpdatedState :=
  assembleIncrementalStateConstitution checked.assembly

def PublicIncrementalCheckedUpdate.affectedCone
    (checked : PublicIncrementalCheckedUpdate) : List ConstitutiveNodeKey :=
  checked.preCertificateResult.affectedCone

theorem PublicIncrementalCheckedUpdate.affectedConeExact
    (checked : PublicIncrementalCheckedUpdate) :
    checked.affectedCone = checked.assembly.affectedCone := by
  unfold PublicIncrementalCheckedUpdate.affectedCone
  rw [checked.preCertificateResultExact]
  rw [checked.assemblyExact]
  rfl

def PublicIncrementalCheckedUpdate.transportedRequirement
    (checked : PublicIncrementalCheckedUpdate) :
    LocalCertificateFragment checked.targetCertificate (.receivedInput 1) :=
  checked.assembly.transportedRequirement.target
  |> realizePreCertificateFragment checked.targetCertificate
      checked.assembly.preCertificateGraph (.receivedInput 1)

def PublicIncrementalCheckedUpdate.transportedFragments
    (checked : PublicIncrementalCheckedUpdate) :
    List (StableNodeKey × StableArtifactObservation) :=
  [(.receivedInput 1, checked.transportedRequirement.payload)]

def PublicIncrementalCheckedUpdate.recomputedFragments
    (checked : PublicIncrementalCheckedUpdate) :
    List (StableNodeKey × StableArtifactObservation) :=
  checked.assembly.recomputedFragments

def PublicIncrementalCheckedUpdate.assembledStructuralFragments
    (checked : PublicIncrementalCheckedUpdate) :
    List (StableNodeKey × StableArtifactObservation) :=
  checked.targetCertificate.structuralObservations

def PublicIncrementalCheckedUpdate.transportedCount
    (checked : PublicIncrementalCheckedUpdate) : Nat :=
  checked.transportedFragments.length

def PublicIncrementalCheckedUpdate.recomputedCount
    (checked : PublicIncrementalCheckedUpdate) : Nat :=
  checked.recomputedFragments.length

theorem PublicIncrementalCheckedUpdate.targetCertificateExact
    (checked : PublicIncrementalCheckedUpdate) :
    checked.targetCertificate = publicReferenceUpdatedStateCertificate := by
  exact (congrArg assembleIncrementalStateConstitution
    checked.assemblyExact).trans publicIncrementalAssembly_eq_fullReference

theorem PublicIncrementalCheckedUpdate.transportedRequirementPayloadExact
    (checked : PublicIncrementalCheckedUpdate) :
    checked.transportedRequirement.payload =
      publicReusedRequirementFragment.payload := by
  exact congrArg
    (fun assembly : PublicIncrementalCertificateAssembly =>
      assembly.transportedRequirement.target.payload)
    checked.assemblyExact

theorem PublicIncrementalCheckedUpdate.transportedFragmentsExact
    (checked : PublicIncrementalCheckedUpdate) :
    checked.transportedFragments = publicTransportedStructuralFragments := by
  exact congrArg
    (fun assembly : PublicIncrementalCertificateAssembly =>
      [(StableNodeKey.receivedInput 1,
        assembly.transportedRequirement.target.payload)])
    checked.assemblyExact

theorem PublicIncrementalCheckedUpdate.recomputedFragmentsExact
    (checked : PublicIncrementalCheckedUpdate) :
    checked.recomputedFragments = publicRecomputedStructuralFragments := by
  exact congrArg PublicIncrementalCertificateAssembly.recomputedFragments
    checked.assemblyExact

theorem PublicIncrementalCheckedUpdate.assembledStructuralFragmentsExact
    (checked : PublicIncrementalCheckedUpdate) :
    checked.assembledStructuralFragments =
      structuralObservationSnapshot publicReferenceUpdatedStateCertificate := by
  exact congrArg StateConstitutiveCertificate.structuralObservations
    checked.targetCertificateExact

theorem PublicIncrementalCheckedUpdate.transportedCountExact
    (checked : PublicIncrementalCheckedUpdate) :
    checked.transportedCount = checked.transportedFragments.length := by
  rfl

theorem PublicIncrementalCheckedUpdate.recomputedCountExact
    (checked : PublicIncrementalCheckedUpdate) :
    checked.recomputedCount = checked.recomputedFragments.length := by
  rfl

def publicIncrementalCheckedUpdate : PublicIncrementalCheckedUpdate :=
  .mk publicIncrementalCoreCheckedUpdate publicIncrementalCertificateAssembly
    publicIncrementalPreCertificateResult rfl rfl rfl rfl

theorem PublicIncrementalCheckedUpdate.unique
    (left right : PublicIncrementalCheckedUpdate) : left = right := by
  cases left
  cases right
  subst_vars
  rfl

/-- Incremental verification is the public specialization of the generic
checker.  The wrapper only exposes the public accounting package; all gates,
certificate assembly and checked-update production have already happened in
`checkGenericIncrementalUpdate`. -/
def checkIncrementalUpdate (update : IncrementalNeuralUpdate) :
    Except AlignmentError PublicIncrementalCheckedUpdate :=
  match checkGenericIncrementalUpdate publicIncrementalCheckerEngine update with
  | .error problem => .error problem
  | .ok success =>
      .ok (.mk publicIncrementalCoreCheckedUpdate
        success.analysis.assembly
        success.analysis.preCertificateResult rfl
        success.analysis.assemblyExact
        success.analysis.preCertificateResultExact
        success.analysis.assemblyCalculated)

theorem checkIncrementalUpdate_accepts_reference :
    checkIncrementalUpdate publicIncrementalNeuralUpdate =
      .ok publicIncrementalCheckedUpdate := by
  rfl

def publicIncorrectIncrementalUpdate : IncrementalNeuralUpdate :=
  { publicSerializedConstitutiveUpdate with
    targetNetwork :=
      applySerializedNetworkEdit publicSerializedReconfiguredNetwork
        (.replaceOutputs [0]) }

def PublicIncrementalCheckerAccepted
    (update : IncrementalNeuralUpdate) : Prop :=
  Exists fun checked => checkIncrementalUpdate update = .ok checked

theorem publicIncrementalAcceptance_iff_generic
    (update : IncrementalNeuralUpdate) :
    PublicIncrementalCheckerAccepted update ↔
      GenericIncrementalUpdateAccepted
        publicIncrementalCheckerEngine update := by
  unfold PublicIncrementalCheckerAccepted GenericIncrementalUpdateAccepted
  cases analyzed :
      checkGenericIncrementalUpdate publicIncrementalCheckerEngine update with
  | error problem =>
      constructor
      · rintro ⟨checked, accepted⟩
        unfold checkIncrementalUpdate at accepted
        rw [analyzed] at accepted
        cases accepted
      · rintro ⟨success, accepted⟩
        cases accepted
  | ok success =>
      constructor
      · intro _
        exact ⟨success, rfl⟩
      · intro _
        refine ⟨?_, ?_⟩
        · exact
            { checked := publicIncrementalCoreCheckedUpdate
              assembly := success.analysis.assembly
              preCertificateResult := success.analysis.preCertificateResult
              checkedExact := rfl
              assemblyExact := success.analysis.assemblyExact
              preCertificateResultExact :=
                success.analysis.preCertificateResultExact
              assemblyCalculated := success.analysis.assemblyCalculated }
        · unfold checkIncrementalUpdate
          rw [analyzed]

theorem checkIncrementalUpdate_rejects_incomplete_delta :
    Not (PublicIncrementalCheckerAccepted publicIncorrectIncrementalUpdate) := by
  intro accepted
  have genericAccepted :=
    (publicIncrementalAcceptance_iff_generic
      publicIncorrectIncrementalUpdate).mp accepted
  have localConditions :=
    (checkGenericIncrementalUpdate_complete_for_local_conditions
      publicIncrementalCheckerEngine publicIncorrectIncrementalUpdate).mp
        genericAccepted
  have publicConditions :=
    (analyzePublicIncrementalUpdate_complete
      publicIncorrectIncrementalUpdate).mp localConditions
  rcases publicConditions with ⟨publicConditionData⟩
  have targetExact := publicConditionData.decodedTarget.sourceExact
  have outputsExact := congrArg
    (fun artifact : SerializedConstitutiveArtifact => artifact.network.outputs)
    targetExact
  have outputsDifferent : [0] ≠ publicSerializedReconfiguredNetwork.outputs := by
    decide
  apply outputsDifferent
  simpa [publicIncorrectIncrementalUpdate,
    materializeIncrementalConstitutiveArtifact,
    publicSerializedConstitutiveUpdate,
    publicSerializedReconfiguredConstitutiveArtifact,
    PublicSerializedConstitutiveUpdate.targetArtifact,
    applySerializedNetworkEdit] using outputsExact

/-- Every successful incremental check returns the one package assembled from
the calculated cone, transported old payload and recalculated target data. -/
theorem checkIncrementalUpdate_sound
    (update : IncrementalNeuralUpdate)
    (checked : PublicIncrementalCheckedUpdate)
    (_accepted : checkIncrementalUpdate update = .ok checked) :
    checked = publicIncrementalCheckedUpdate :=
  PublicIncrementalCheckedUpdate.unique _ _

end ConstitutiveSearch.NeuralAgent
/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.NeuralAgent.SerializedNetworkEdit
#print axioms ConstitutiveSearch.NeuralAgent.applySerializedNetworkEdits
#print axioms ConstitutiveSearch.NeuralAgent.IncrementalNeuralUpdate
#print axioms ConstitutiveSearch.NeuralAgent.materializeIncrementalTarget
#print axioms ConstitutiveSearch.NeuralAgent.materializeIncrementalConstitutiveArtifact
#print axioms ConstitutiveSearch.NeuralAgent.publicIncrementalTarget_exact
#print axioms ConstitutiveSearch.NeuralAgent.publicIncrementalConstitutiveArtifact_exact
#print axioms ConstitutiveSearch.NeuralAgent.DecodedPublicIncrementalTarget
#print axioms ConstitutiveSearch.NeuralAgent.decodePublicIncrementalTarget
#print axioms ConstitutiveSearch.NeuralAgent.decodePublicIncrementalTarget_of_exact
#print axioms ConstitutiveSearch.NeuralAgent.decideCanonicalDecodedPublicIncrementalTarget_exact
#print axioms ConstitutiveSearch.NeuralAgent.IncrementalPreCertificateResult
#print axioms ConstitutiveSearch.NeuralAgent.calculateIncrementalPreCertificateResult
#print axioms ConstitutiveSearch.NeuralAgent.publicIncrementalPreCertificateResult
#print axioms ConstitutiveSearch.NeuralAgent.calculateIncrementalPreCertificateResult_eq_public_of_target_exact
#print axioms ConstitutiveSearch.NeuralAgent.publicIncrementalTargetFragments
#print axioms ConstitutiveSearch.NeuralAgent.publicIncrementalAssembledTargetCertificate
#print axioms ConstitutiveSearch.NeuralAgent.publicIncrementalTargetCertificate_eq_fullReference
#print axioms ConstitutiveSearch.NeuralAgent.publicIncrementalLicensedRequirementFragment
#print axioms ConstitutiveSearch.NeuralAgent.publicRecomputedStructuralFragments
#print axioms ConstitutiveSearch.NeuralAgent.publicTransportedStructuralFragments
#print axioms ConstitutiveSearch.NeuralAgent.IncrementalStructuralAssemblyError
#print axioms ConstitutiveSearch.NeuralAgent.calculateIncrementalStructuralAssembly
#print axioms ConstitutiveSearch.NeuralAgent.CalculatedIncrementalStructuralAssembly
#print axioms ConstitutiveSearch.NeuralAgent.certifyCalculatedIncrementalStructuralAssembly
#print axioms ConstitutiveSearch.NeuralAgent.publicCalculatedIncrementalStructuralAssembly
#print axioms ConstitutiveSearch.NeuralAgent.publicIncrementalStructuralAssembly_exact
#print axioms ConstitutiveSearch.NeuralAgent.publicTransportedStructuralFragmentCount_exact
#print axioms ConstitutiveSearch.NeuralAgent.publicRecomputedStructuralFragmentCount_exact
#print axioms ConstitutiveSearch.NeuralAgent.RecomputedStateCertificateFragments
#print axioms ConstitutiveSearch.NeuralAgent.recomputePublicStateCertificateFragments
#print axioms ConstitutiveSearch.NeuralAgent.publicRecomputedStateCertificateFragments
#print axioms ConstitutiveSearch.NeuralAgent.PublicIncrementalCertificateAssembly
#print axioms ConstitutiveSearch.NeuralAgent.PublicIncrementalCertificateAssembly.fragments
#print axioms ConstitutiveSearch.NeuralAgent.assembleIncrementalStateConstitution
#print axioms ConstitutiveSearch.NeuralAgent.publicIncrementalTransportedRequirement_coherent
#print axioms ConstitutiveSearch.NeuralAgent.publicIncrementalCertificateAssembly
#print axioms ConstitutiveSearch.NeuralAgent.publicIncrementalAssembly_eq_fullReference
#print axioms ConstitutiveSearch.NeuralAgent.assemblePublicIncrementalCertificateFromPreCertificate
#print axioms ConstitutiveSearch.NeuralAgent.assemblePublicIncrementalCertificateFromPreCertificate_exact
#print axioms ConstitutiveSearch.NeuralAgent.IncrementalTargetAnalysis
#print axioms ConstitutiveSearch.NeuralAgent.IncrementalCheckerEngine
#print axioms ConstitutiveSearch.NeuralAgent.buildIncrementalCheckedUpdate
#print axioms ConstitutiveSearch.NeuralAgent.GenericIncrementalCheckSuccess
#print axioms ConstitutiveSearch.NeuralAgent.checkGenericIncrementalUpdate
#print axioms ConstitutiveSearch.NeuralAgent.checkGenericIncrementalUpdate_sound
#print axioms ConstitutiveSearch.NeuralAgent.checkGenericIncrementalUpdate_constitutively_sound
#print axioms ConstitutiveSearch.NeuralAgent.GenericIncrementalUpdateLocalConditions
#print axioms ConstitutiveSearch.NeuralAgent.GenericIncrementalUpdateAccepted
#print axioms ConstitutiveSearch.NeuralAgent.checkGenericIncrementalUpdate_complete_for_local_conditions
#print axioms ConstitutiveSearch.NeuralAgent.publicIncrementalTargetAnalysis
#print axioms ConstitutiveSearch.NeuralAgent.publicIncrementalTargetAnalysisFromDecision
#print axioms ConstitutiveSearch.NeuralAgent.publicIncrementalTargetAnalysisFromDecision_transition_exact
#print axioms ConstitutiveSearch.NeuralAgent.PublicIncrementalExecutedDependencies
#print axioms ConstitutiveSearch.NeuralAgent.PublicIncrementalEngineAnalysis
#print axioms ConstitutiveSearch.NeuralAgent.PublicIncrementalEngineAnalysis.targetAnalysis
#print axioms ConstitutiveSearch.NeuralAgent.analyzePublicIncrementalUpdate
#print axioms ConstitutiveSearch.NeuralAgent.PublicIncrementalEngineLocalConditionData
#print axioms ConstitutiveSearch.NeuralAgent.publicIncrementalCheckerEngine
#print axioms ConstitutiveSearch.NeuralAgent.PublicIncrementalEngineLocalConditions
#print axioms ConstitutiveSearch.NeuralAgent.analyzePublicIncrementalUpdate_of_conditions
#print axioms ConstitutiveSearch.NeuralAgent.publicIncrementalLocalConditionDataOfExact
#print axioms ConstitutiveSearch.NeuralAgent.completePublicIncrementalAnalysis
#print axioms ConstitutiveSearch.NeuralAgent.publicIncrementalLocalConditionsOfSuccess
#print axioms ConstitutiveSearch.NeuralAgent.analyzePublicIncrementalUpdate_complete
#print axioms ConstitutiveSearch.NeuralAgent.publicIncrementalTargetAnalysis_checked_exact
#print axioms ConstitutiveSearch.NeuralAgent.publicIncrementalCoreCheckedUpdate_execution_exact
#print axioms ConstitutiveSearch.NeuralAgent.PublicIncrementalCheckedUpdate
#print axioms ConstitutiveSearch.NeuralAgent.PublicIncrementalCheckedUpdate.targetCertificate
#print axioms ConstitutiveSearch.NeuralAgent.PublicIncrementalCheckedUpdate.affectedConeExact
#print axioms ConstitutiveSearch.NeuralAgent.PublicIncrementalCheckedUpdate.targetCertificateExact
#print axioms ConstitutiveSearch.NeuralAgent.PublicIncrementalCheckedUpdate.unique
#print axioms ConstitutiveSearch.NeuralAgent.publicIncrementalCheckedUpdate
#print axioms ConstitutiveSearch.NeuralAgent.checkIncrementalUpdate
#print axioms ConstitutiveSearch.NeuralAgent.PublicIncrementalCheckerAccepted
#print axioms ConstitutiveSearch.NeuralAgent.publicIncrementalAcceptance_iff_generic
#print axioms ConstitutiveSearch.NeuralAgent.checkIncrementalUpdate_sound
/- AXIOM_AUDIT_END -/
