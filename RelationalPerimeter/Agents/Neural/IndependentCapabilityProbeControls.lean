import RelationalPerimeter.Agents.Neural.IndependentCapabilityComparison

/-!
# Exact comparison controls for P2--P6

P2 executes one fixed learned network once.  A genuinely changed decoder that
agrees on this execution is accepted after rebuilding its decoder-indexed
fragment, while a changed decoder that violates the produced proposal is
rejected by both the local checker and an independently written recheck.
Consequently, P2 neither accepts every change nor rejects every change.
P3 holds every artifact field fixed and varies only the contract transition.
P4 exhibits both exact executed forgetting and an incorrect collapsing
projection refuted by the produced nonempty future separator.
P5 executes the installed post-forgetting contract-change interface, not an
ordinary continuation.
P6 observes one successive received update through the incremental checker and
the independent full recheck, and records the transported/recomputed fragments
from that exact successive execution.
-/
namespace ConstitutiveSearch.NeuralAgent
open ContinuationSignatures

def observeIndependentFullRecheck
    (update : LearnedSerializedConstitutiveUpdate) :
    GenericIncrementalObservation :=
  match checkFullUpdate learnedFullRecheckEngine update with
  | .ok _ => .accepted
  | .error _ => .rejected

def observePostForgettingFullRecheck
    (request : SerializedLearnedPostForgettingRequest) :
    GenericIncrementalObservation :=
  match recheckLearnedPostForgettingCompletely request with
  | .ok _ => .accepted
  | .error _ => .rejected

def observePostForgettingIncremental
    (request : SerializedLearnedPostForgettingRequest) :
    GenericIncrementalObservation :=
  match analyzeLearnedPostForgettingIncrementally request with
  | .ok _ => .accepted
  | .error _ => .rejected

inductive LearnedP2PathObservation where
  | accepted
  | rejected
  deriving DecidableEq, Repr

/-- The output of the one fixed network execution shared by both P2 paths. -/
def learnedP2FixedNetworkOutputs : List NativeMechanism.Activation :=
  learnedAlignedState.system.outputValues learnedAlignedState.input

/-- The canonical decoder applied after the shared network execution. -/
def learnedP2CanonicalProposal : Bool :=
  decodeIndependentLearnedProposal learnedP2FixedNetworkOutputs

/-- An admissible decoder modification.  It is genuinely different from the
canonical decoder on the empty output, but agrees on every nonempty output and
therefore on the output produced by the fixed network used by P2. -/
def learnedP2AdmissibleDecoder : List NativeMechanism.Activation -> Bool
  | [] => true
  | value :: _ => decide (value != 0)

/-- A forbidden decoder modification.  It consumes the same network output and
changes its produced proposal on that exact execution. -/
def learnedP2ModifiedDecoder (outputs : List NativeMechanism.Activation) : Bool :=
  !decodeIndependentLearnedProposal outputs

def learnedP2AdmissibleProposal : Bool :=
  learnedP2AdmissibleDecoder learnedP2FixedNetworkOutputs

def learnedP2ModifiedProposal : Bool :=
  learnedP2ModifiedDecoder learnedP2FixedNetworkOutputs

def learnedP2AdmissibleRequest : Agent.Request :=
  publicAgentActionChannel.command learnedP2AdmissibleProposal

def learnedP2CanonicalRequest : Agent.Request :=
  publicAgentActionChannel.command learnedP2CanonicalProposal

def learnedP2ModifiedRequest : Agent.Request :=
  publicAgentActionChannel.command learnedP2ModifiedProposal

theorem learnedP2CanonicalProposal_is_executed :
    learnedP2CanonicalProposal =
      learnedAlignedState.system.proposal learnedAlignedState.input := by
  rfl

theorem learnedP2CanonicalRequest_is_executed :
    learnedP2CanonicalRequest = learnedAlignedAction.request := by
  rw [learnedAlignedAction.requestExact]
  exact congrArg publicAgentActionChannel.command
    learnedP2CanonicalProposal_is_executed

/-- The dependent fragment rebuilt for one exact consumer.  Indexing the
fragment by the decoder prevents a fragment produced for one consumer version
from being reused as evidence for another consumer version. -/
structure LearnedP2ConsumerFragment
    (decoder : List NativeMechanism.Activation -> Bool) where
  proposal : Bool
  proposalProduced :
    proposal = decoder learnedP2FixedNetworkOutputs
  proposalCanonical : proposal = learnedP2CanonicalProposal
  request : Agent.Request
  requestProduced : request = publicAgentActionChannel.command proposal
  requestCanonical :
    request = publicAgentActionChannel.command learnedP2CanonicalProposal

def checkLearnedP2Path
    (decoder : List NativeMechanism.Activation -> Bool) :
    Option (LearnedP2ConsumerFragment decoder) :=
  if same : decoder learnedP2FixedNetworkOutputs = learnedP2CanonicalProposal
  then some {
    proposal := decoder learnedP2FixedNetworkOutputs
    proposalProduced := rfl
    proposalCanonical := same
    request := publicAgentActionChannel.command
      (decoder learnedP2FixedNetworkOutputs)
    requestProduced := rfl
    requestCanonical := congrArg publicAgentActionChannel.command same }
  else none

/-- A separately defined full recheck of the P2 consumer contract.  It receives
only the decoder and independently recalculates the fixed network output and
the required proposal; it does not consume the local checker's fragment or
verdict. -/
def recheckLearnedP2Path
    (decoder : List NativeMechanism.Activation -> Bool) :
    LearnedP2PathObservation :=
  if decoder (learnedAlignedState.system.outputValues learnedAlignedState.input) =
      decodeIndependentLearnedProposal
        (learnedAlignedState.system.outputValues learnedAlignedState.input)
  then .accepted
  else .rejected

def observeLearnedP2Path
    (decoder : List NativeMechanism.Activation -> Bool) :
    LearnedP2PathObservation :=
  match checkLearnedP2Path decoder with
  | some _ => .accepted
  | none => .rejected

theorem learnedP2CanonicalPathAccepted :
    observeLearnedP2Path decodeIndependentLearnedProposal = .accepted := by
  rfl

theorem learnedP2AdmissibleDecoderChanged :
    learnedP2AdmissibleDecoder ≠ decodeIndependentLearnedProposal := by
  intro same
  have emptySame := congrArg (fun decoder => decoder []) same
  cases emptySame

theorem learnedP2AdmissibleProposalCanonical :
    learnedP2AdmissibleProposal = learnedP2CanonicalProposal := by
  rfl

theorem learnedP2AdmissibleRequestCanonical :
    learnedP2AdmissibleRequest = learnedP2CanonicalRequest := by
  exact congrArg publicAgentActionChannel.command
    learnedP2AdmissibleProposalCanonical

theorem learnedP2AdmissiblePathAccepted :
    observeLearnedP2Path learnedP2AdmissibleDecoder = .accepted := by
  rfl

def learnedP2CanonicalFragment :
    LearnedP2ConsumerFragment decodeIndependentLearnedProposal :=
  match exact : checkLearnedP2Path decodeIndependentLearnedProposal with
  | some fragment => fragment
  | none => False.elim (by cases exact)

def learnedP2AdmissibleFragment :
    LearnedP2ConsumerFragment learnedP2AdmissibleDecoder :=
  match exact : checkLearnedP2Path learnedP2AdmissibleDecoder with
  | some fragment => fragment
  | none => False.elim (by cases exact)

theorem checkLearnedP2CanonicalFragment_exact :
    checkLearnedP2Path decodeIndependentLearnedProposal =
      some learnedP2CanonicalFragment := by
  rfl

theorem checkLearnedP2AdmissibleFragment_exact :
    checkLearnedP2Path learnedP2AdmissibleDecoder =
      some learnedP2AdmissibleFragment := by
  rfl

theorem learnedP2ModifiedProposalDifferent :
    learnedP2ModifiedProposal ≠ learnedP2CanonicalProposal := by
  unfold learnedP2ModifiedProposal learnedP2ModifiedDecoder
    learnedP2CanonicalProposal
  cases decodeIndependentLearnedProposal learnedP2FixedNetworkOutputs <;>
    intro same <;> cases same

theorem learnedP2ModifiedRequestDifferent :
    learnedP2ModifiedRequest ≠ learnedP2CanonicalRequest := by
  unfold learnedP2ModifiedRequest learnedP2CanonicalRequest
  exact publicAgentActionChannel.preserves_required_distinction
    learnedP2ModifiedProposalDifferent

theorem learnedP2ModifiedPathRejected :
    observeLearnedP2Path learnedP2ModifiedDecoder = .rejected := by
  have different :
      learnedP2ModifiedDecoder learnedP2FixedNetworkOutputs ≠
        learnedP2CanonicalProposal :=
    learnedP2ModifiedProposalDifferent
  unfold observeLearnedP2Path checkLearnedP2Path
  rw [dif_neg different]

theorem learnedP2CanonicalRecheckAccepted :
    recheckLearnedP2Path decodeIndependentLearnedProposal = .accepted := by
  rfl

theorem learnedP2AdmissibleRecheckAccepted :
    recheckLearnedP2Path learnedP2AdmissibleDecoder = .accepted := by
  rfl

theorem learnedP2ModifiedRecheckRejected :
    recheckLearnedP2Path learnedP2ModifiedDecoder = .rejected := by
  unfold recheckLearnedP2Path learnedP2ModifiedDecoder
  cases decodeIndependentLearnedProposal
      (learnedAlignedState.system.outputValues learnedAlignedState.input) <;>
    rfl

/-! ## P2 through the generic incremental checker and full recheck -/

/-- A finite, serializable name for each consumer implementation used by the
P2 comparison.  The network and received target remain fixed; only this
consumer version varies. -/
inductive LearnedP2ConsumerVersion where
  | canonical
  | admissible
  | forbidden
  deriving DecidableEq, Repr

def LearnedP2ConsumerVersion.decoder :
    LearnedP2ConsumerVersion -> List NativeMechanism.Activation -> Bool
  | .canonical => decodeIndependentLearnedProposal
  | .admissible => learnedP2AdmissibleDecoder
  | .forbidden => learnedP2ModifiedDecoder

/-- The action installed for P2 is calculated from the proposal retained by
the exact decoder-indexed fragment.  The equality in the fragment licenses
that produced proposal for the learned state, but does not replace it by the
canonical proposal before execution. -/
def LearnedP2ConsumerFragment.action
    {decoder : List NativeMechanism.Activation -> Bool}
    (fragment : LearnedP2ConsumerFragment decoder) :
    LearnedActionWitness learnedAlignedState :=
  executeLearnedActionFromProducedProposal learnedAlignedState
    fragment.proposal
    (fragment.proposalCanonical.trans learnedP2CanonicalProposal_is_executed)
    learnedAlignedProposalPreservation learnedAlignedCausalWitness
    learnedAlignedAuthorizationWitness rfl

/-- The effect is produced from the same action occurrence that consumed the
decoder output. -/
def LearnedP2ConsumerFragment.effect
    {decoder : List NativeMechanism.Activation -> Bool}
    (fragment : LearnedP2ConsumerFragment decoder) :
    LearnedEffectWitness learnedAlignedState fragment.action :=
  produceLearnedEffect fragment.action

/-- Recomputed target evidence whose action and effect consume the exact P2
consumer fragment.  The remaining obligations are unchanged because P2 holds
the network, state, contract and future regime fixed. -/
def learnedP2RecomputedCertificateFragments
    {decoder : List NativeMechanism.Activation -> Bool}
    (fragment : LearnedP2ConsumerFragment decoder) :
    RecomputedStateCertificateFragments LearnedAlignedOperationalContract
      learnedDecodedAlignedArtifact learnedAlignedState :=
  { learnedAlignedRecomputedCertificateFragments with
    proposalAction := { witness := fragment.action }
    effect :=
      { witness :=
          { action := fragment.action
            effect := fragment.effect } } }

/-- The incremental target consumes the decoder fragment in the certificate
assembly itself.  It is not a side condition stored beside the old target. -/
def learnedP2TargetAnalysisForAdmittedNamingFromDecision
    {decoder : List NativeMechanism.Activation -> Bool}
    (fragment : LearnedP2ConsumerFragment decoder)
    {source : SerializedStableArtifactNaming}
    (admitted : LearnedAdmittedStableNaming source)
    (transitionDecision : LearnedAlignedTransitionDecision) :
    IncrementalTargetAnalysis learnedInitialCheckedAgent :=
  { learnedAlignedTargetAnalysisForAdmittedNamingFromDecision admitted
      transitionDecision with
    recomputedCertificateFragments :=
      learnedP2RecomputedCertificateFragments fragment }

/-- Transport the already decoded artifact index to the P2 target without
reconstructing a second artifact. -/
def learnedP2ReceivedTargetAnalysis
    {decoder : List NativeMechanism.Activation -> Bool}
    (fragment : LearnedP2ConsumerFragment decoder)
    (target : DecodedNeuralArtifact LearnedAlignedOperationalContract)
    (targetExact : target = learnedDecodedAlignedArtifact)
    {source : SerializedStableArtifactNaming}
    (admitted : LearnedAdmittedStableNaming source)
    (transitionDecision : LearnedAlignedTransitionDecision) :
    IncrementalTargetAnalysis learnedInitialCheckedAgent :=
  match targetExact with
  | rfl =>
      learnedP2TargetAnalysisForAdmittedNamingFromDecision fragment admitted
        transitionDecision

inductive LearnedP2CheckerError where
  | consumerRejected
  | targetRejected
  | learned (problem : LearnedRuntimeUpdateError)
  deriving DecidableEq

/-- The incremental analysis keeps the fragment indexed by the exact consumer
version and the independently executed learned target analysis in one value. -/
structure LearnedP2IncrementalAnalysis
    (version : LearnedP2ConsumerVersion) where
  fragment : LearnedP2ConsumerFragment version.decoder
  learned : LearnedIncrementalEngineAnalysis learnedAlignedSerializedUpdate

structure LearnedP2IncrementalLocalConditions
    (version : LearnedP2ConsumerVersion) where
  fragment : LearnedP2ConsumerFragment version.decoder
  learned :
    LearnedIncrementalEngineLocalConditionData learnedAlignedSerializedUpdate

def analyzeLearnedP2Incrementally
    (version : LearnedP2ConsumerVersion) :
    Except LearnedP2CheckerError (LearnedP2IncrementalAnalysis version) :=
  match _fragmentAccepted : checkLearnedP2Path version.decoder with
  | none => .error .consumerRejected
  | some fragment =>
      match _learnedAccepted :
          analyzeLearnedRuntimeUpdate learnedAlignedSerializedUpdate with
      | .error problem => .error (.learned problem)
      | .ok learned =>
          .ok { fragment := fragment
                learned := learned }

def completeLearnedP2IncrementalAnalysis
    (version : LearnedP2ConsumerVersion)
    (conditions : LearnedP2IncrementalLocalConditions version) :
    { analysis : LearnedP2IncrementalAnalysis version //
      analyzeLearnedP2Incrementally version = .ok analysis } := by
  cases version with
  | canonical =>
      let analysis : LearnedP2IncrementalAnalysis .canonical := {
        fragment := learnedP2CanonicalFragment
        learned := learnedAlignedGenericIncrementalSuccess.analysis
      }
      exact ⟨analysis, rfl⟩
  | admissible =>
      let analysis : LearnedP2IncrementalAnalysis .admissible := {
        fragment := learnedP2AdmissibleFragment
        learned := learnedAlignedGenericIncrementalSuccess.analysis
      }
      exact ⟨analysis, rfl⟩
  | forbidden =>
      have impossible : learnedP2ModifiedProposal = learnedP2CanonicalProposal :=
        conditions.fragment.proposalProduced.symm.trans
          conditions.fragment.proposalCanonical
      exact False.elim (learnedP2ModifiedProposalDifferent impossible)

def learnedP2IncrementalLocalConditionsOfSuccess
    (version : LearnedP2ConsumerVersion)
    (analysis : LearnedP2IncrementalAnalysis version)
    (_accepted : analyzeLearnedP2Incrementally version = .ok analysis) :
    LearnedP2IncrementalLocalConditions version :=
  { fragment := analysis.fragment
    learned := analysis.learned.executed }

def learnedP2IncrementalCheckerEngine :
    IncrementalCheckerEngine learnedInitialCheckedAgent where
  Update := LearnedP2ConsumerVersion
  Error := LearnedP2CheckerError
  Analysis := LearnedP2IncrementalAnalysis
  analyze := analyzeLearnedP2Incrementally
  LocalConditions := LearnedP2IncrementalLocalConditions
  complete := completeLearnedP2IncrementalAnalysis
  localOfSuccess := learnedP2IncrementalLocalConditionsOfSuccess
  target := fun analysis =>
    learnedP2ReceivedTargetAnalysis analysis.fragment
      analysis.learned.executed.decoded.target
      analysis.learned.executed.decoded.targetExact
      analysis.learned.executed.decoded.admittedStableNaming
      (analysis.learned.executed.receivedDecision.transportRequest
        analysis.learned.executed.decoded.transitionExact)

def observeLearnedP2Incremental
    (version : LearnedP2ConsumerVersion) : GenericIncrementalObservation :=
  match checkGenericIncrementalUpdate learnedP2IncrementalCheckerEngine version with
  | .ok _ => .accepted
  | .error _ => .rejected

/-! ### Independent target decoding for the P2 full recheck -/

/-- A full P2 decode retains both receipts from the fixed network artifact and
the independently recomputed decoder fragment. -/
structure LearnedP2DecodedArtifact
    (version : LearnedP2ConsumerVersion) : Type 4 where
  artifact : DecodedNeuralArtifact LearnedAlignedOperationalContract
  artifactDecodedExact :
    decodeArtifact LearnedAlignedOperationalContract
      learnedReceivedAlignedArtifact.network = .ok artifact
  artifactExact : artifact = learnedDecodedAlignedArtifact
  stable : DecodedStableArtifactNaming artifact
    learnedReceivedAlignedArtifact.stableNaming
  stableDecodedExact :
    decodeStableArtifactNaming artifact
      learnedReceivedAlignedArtifact.stableNaming = .ok stable
  fragment : LearnedP2ConsumerFragment version.decoder

inductive LearnedP2ArtifactError where
  | learned (problem : LearnedExecutableArtifactError)
  | consumerRejected
  deriving DecidableEq

def decodeLearnedP2Artifact
    (version : LearnedP2ConsumerVersion) :
    Except LearnedP2ArtifactError (LearnedP2DecodedArtifact version) :=
  match decodeLearnedExecutableArtifact learnedReceivedAlignedArtifact with
  | .error problem => .error (.learned problem)
  | .ok (.aligned artifact artifactDecodedExact artifactExact stable
      stableDecodedExact) =>
      match checkLearnedP2Path version.decoder with
      | none => .error .consumerRejected
      | some fragment =>
          .ok
            { artifact := artifact
              artifactDecodedExact := artifactDecodedExact
              artifactExact := artifactExact
              stable := stable
              stableDecodedExact := stableDecodedExact
              fragment := fragment }

def LearnedP2DecodedArtifact.fragments
    {version : LearnedP2ConsumerVersion}
    (decoded : LearnedP2DecodedArtifact version) :
    StateCertificateFragments LearnedAlignedOperationalContract
      decoded.artifact learnedAlignedState := by
  cases decoded with
  | mk artifact artifactDecodedExact artifactExact stable stableDecodedExact
      fragment =>
      cases artifactExact
      exact
        { learnedAlignedStateFragments with
          proposalAction := { witness := fragment.action }
          effect :=
            { witness :=
                { action := fragment.action
                  effect := fragment.effect } } }

/-- The complete-reference interface reconstructs its checked target from the
same decoder fragment.  Thus the full recheck cannot accept P2 and then install
the certificate produced by the canonical consumer. -/
def learnedP2ExecutableMetaContractInterface :
    ExecutableMetaContractInterface learnedConstitutiveMetaContract where
  ContractCode := LearnedOperationalContract
  encodeContract := fun contract => contract
  encodeContractInjective := fun _ _ same => same
  ContractNameError := Empty
  decodeContractName := fun source => .ok { contract := source, exact := rfl }
  ReceivedArtifact := LearnedP2ConsumerVersion
  artifactContractCode := fun _ => .aligned
  artifactNetwork := fun _ => learnedReceivedAlignedArtifact.network
  artifactStableNaming := fun _ => learnedReceivedAlignedArtifact.stableNaming
  ArtifactError := LearnedP2ArtifactError
  DecodedArtifact := LearnedP2DecodedArtifact
  decodedContract := fun _ => .aligned
  decodedContractExact := by intro source decoded; rfl
  decodedNeuralArtifact := LearnedP2DecodedArtifact.artifact
  decodedNetworkExact := by
    intro source decoded
    exact (congrArg DecodedNeuralArtifact.source decoded.artifactExact).trans
      (by rfl)
  decodedStableNaming := LearnedP2DecodedArtifact.stable
  decodeReceivedArtifact := decodeLearnedP2Artifact
  stateOfArtifact := fun _ => learnedAlignedState
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

abbrev LearnedP2AlignedTransitionDecision :=
  AcceptedTransitionDecision learnedP2ExecutableMetaContractInterface
    ({ current := LearnedOperationalContract.initial
       next := LearnedOperationalContract.aligned } :
      ContractTransitionRequest learnedConstitutiveMetaContract)

def learnedP2AlignedTransitionDecision : LearnedP2AlignedTransitionDecision :=
  match exact : decideTransition learnedP2ExecutableMetaContractInterface
      ({ current := .initial, next := .aligned } :
        ContractTransitionRequest learnedConstitutiveMetaContract) with
  | some decision => decision
  | none => False.elim (by cases exact)

def mapLearnedP2FullRecheckTargetError
    (_problem : InitialCheckError learnedP2ExecutableMetaContractInterface) :
    LearnedP2CheckerError :=
  .targetRejected

def recomputeLearnedP2FullRecheckExecution
    (version : LearnedP2ConsumerVersion)
    (target : InitialCheckSuccess learnedP2ExecutableMetaContractInterface
      version)
    (decision : AcceptedTransitionDecision
      learnedP2ExecutableMetaContractInterface
      { current := LearnedOperationalContract.initial
        next := learnedP2ExecutableMetaContractInterface.decodedContract
          target.decodedArtifact }) :
    Except LearnedP2CheckerError
      (FullRecheckExecution learnedP2ExecutableMetaContractInterface
        learnedTransitionProductionKernel learnedInitialCheckedAgent
        target.decodedArtifact decision) :=
by
  have decisionExact := decision.unique learnedP2AlignedTransitionDecision
  cases decisionExact
  exact .ok
    { material := .installAligned
      targetExact := rfl }

def learnedP2FullRecheckEngine : FullRecheckEngine
    learnedP2ExecutableMetaContractInterface learnedInitialCheckedAgent where
  Update := LearnedP2ConsumerVersion
  Error := LearnedP2CheckerError
  targetArtifact := fun version => version
  mapTargetError := mapLearnedP2FullRecheckTargetError
  transitionRejected := .learned .unexpectedTransition
  kernel := learnedTransitionProductionKernel
  recomputeExecution := recomputeLearnedP2FullRecheckExecution

def observeLearnedP2FullRecheck
    (version : LearnedP2ConsumerVersion) : GenericIncrementalObservation :=
  match checkFullUpdate learnedP2FullRecheckEngine version with
  | .ok _ => .accepted
  | .error _ => .rejected

theorem learnedP2CanonicalIncrementalPathAccepted :
    observeLearnedP2Incremental .canonical = .accepted := by
  rfl

theorem learnedP2AdmissibleIncrementalPathAccepted :
    observeLearnedP2Incremental .admissible = .accepted := by
  rfl

theorem learnedP2ForbiddenIncrementalPathRejected :
    observeLearnedP2Incremental .forbidden = .rejected := by
  rfl

theorem learnedP2CanonicalFullRecheckPathAccepted :
    observeLearnedP2FullRecheck .canonical = .accepted := by
  rfl

theorem learnedP2AdmissibleFullRecheckPathAccepted :
    observeLearnedP2FullRecheck .admissible = .accepted := by
  rfl

theorem learnedP2ForbiddenFullRecheckPathRejected :
    observeLearnedP2FullRecheck .forbidden = .rejected := by
  rfl

def learnedP2CanonicalIncrementalSuccess :
    GenericIncrementalCheckSuccess learnedP2IncrementalCheckerEngine
      .canonical :=
  match exact : checkGenericIncrementalUpdate
      learnedP2IncrementalCheckerEngine .canonical with
  | .ok success => success
  | .error _ => False.elim (by cases exact)

def learnedP2AdmissibleIncrementalSuccess :
    GenericIncrementalCheckSuccess learnedP2IncrementalCheckerEngine
      .admissible :=
  match exact : checkGenericIncrementalUpdate
      learnedP2IncrementalCheckerEngine .admissible with
  | .ok success => success
  | .error _ => False.elim (by cases exact)

def learnedP2AdmissibleFullRecheckSuccess :
    FullRecheckSuccess learnedP2FullRecheckEngine .admissible :=
  match exact : checkFullUpdate learnedP2FullRecheckEngine .admissible with
  | .ok success => success
  | .error _ => False.elim (by cases exact)

theorem learnedP2AdmissibleIncrementalAction_exact :
    (learnedP2AdmissibleIncrementalSuccess.checked.next.certificate
        ).proposalActionWitness = learnedP2AdmissibleFragment.action := by
  rfl

theorem learnedP2AdmissibleFullRecheckAction_exact :
    (learnedP2AdmissibleFullRecheckSuccess.checked.next.certificate
        ).proposalActionWitness = learnedP2AdmissibleFragment.action := by
  rfl

theorem learnedP2AdmissibleIncrementalEffect_consumes_action :
    (learnedP2AdmissibleIncrementalSuccess.checked.next.certificate
        ).effectWitness.action = learnedP2AdmissibleFragment.action := by
  rfl

theorem learnedP2AdmissibleFullRecheckEffect_consumes_action :
    (learnedP2AdmissibleFullRecheckSuccess.checked.next.certificate
        ).effectWitness.action = learnedP2AdmissibleFragment.action := by
  rfl

theorem learnedP2AdmissibleIncrementalAndFullSuccessor_exact :
    learnedP2AdmissibleIncrementalSuccess.checked.next =
      learnedP2AdmissibleFullRecheckSuccess.checked.next := by
  rfl

theorem learnedP2AdmissibleIncrementalAndFullCertificate_exact :
    learnedP2AdmissibleIncrementalSuccess.checked.next.certificate =
      learnedP2AdmissibleFullRecheckSuccess.checked.next.certificate := by
  rfl

/-! ## P4: the incorrect forgetting control -/

/-- The deliberately incorrect projection erases every behavioral distinction
by returning the aligned memory for every source. -/
def learnedP4IncorrectForgetting
    (_source : IndependentLearnedFutureSource) :
    IndependentLearnedOperationalMemory :=
  independentLearnedFutureProjection
    (learnedCandidateFutureSource learnedAlignedCandidateAtInitial)

theorem learnedP4IncorrectForgettingCollapsesSeparatedSources :
    learnedP4IncorrectForgetting
        (learnedCandidateFutureSource learnedAlignedCandidateAtInitial) =
      learnedP4IncorrectForgetting
        (learnedCandidateFutureSource learnedBypassCandidateAtInitial) := by
  rfl

theorem learnedP4SeparatorRevealsRequiredDistinction :
    independentLearnedFutureContract.outcome
        (learnedCandidateFutureSource learnedAlignedCandidateAtInitial)
        learnedAlignedBypassFutureSeparator.requests ≠
      independentLearnedFutureContract.outcome
        (learnedCandidateFutureSource learnedBypassCandidateAtInitial)
        learnedAlignedBypassFutureSeparator.requests :=
  learnedAlignedBypassFutureSeparator.different

theorem learnedP4IncorrectForgettingCannotBeExact
    (realization : ExactRealization independentLearnedFutureContract
      IndependentLearnedOperationalMemory)
    (projectExact : realization.project = learnedP4IncorrectForgetting) :
    False := by
  have separated := learnedEveryExactRealizationSeparatesAlignedFromBypass
    IndependentLearnedOperationalMemory realization
  apply separated
  rw [projectExact]
  exact learnedP4IncorrectForgettingCollapsesSeparatedSources

/-! ## P6: one exact successive execution for both checker paths -/

def observeLearnedP6SuccessiveIncremental : GenericIncrementalObservation :=
  match checkGenericIncrementalUpdate learnedSuccessiveIncrementalCheckerEngine
      learnedExtendedSerializedUpdate with
  | .ok _ => .accepted
  | .error _ => .rejected

def observeLearnedP6SuccessiveFullRecheck : GenericIncrementalObservation :=
  match checkFullUpdate learnedSuccessiveFullRecheckEngine
      learnedExtendedSerializedUpdate with
  | .ok _ => .accepted
  | .error _ => .rejected

/-- One typed P6 result binds both decisions, the exact received update, the
transport/recompute assembly, and the equality of independently produced
successors.  The executable rows project from this single value. -/
structure LearnedP6SuccessiveComparisonOutput : Type 8 where
  receivedUpdate : LearnedSerializedConstitutiveUpdate
  receivedUpdateExact : receivedUpdate = learnedExtendedSerializedUpdate
  incrementalDecision : GenericIncrementalObservation
  fullRecheckDecision : GenericIncrementalObservation
  incrementalDecisionExact : incrementalDecision = .accepted
  fullRecheckDecisionExact : fullRecheckDecision = .accepted
  transportedStructuralCount : Nat
  recomputedStructuralCount : Nat
  transportedStructuralCountExact :
    transportedStructuralCount =
      learnedSuccessiveTransportedStructuralFragments.length
  recomputedStructuralCountExact :
    recomputedStructuralCount =
      learnedSuccessiveRecomputedStructuralFragments.length
  installedAssemblyExact :
    (learnedSuccessiveIncrementalSuccess.checked.next.certificate
        ).structuralObservations =
      learnedSuccessiveCalculatedStructuralAssembly.observations
  transportReadsCheckedSource :
    learnedSuccessiveTransportedStructuralFragments =
      let source :=
        structuralObservationSnapshot LearnedAlignedCheckedAgent.certificate
      source.take 10
  acceptedSuccessorExact :
    learnedSuccessiveIncrementalSuccess.checked.next =
      learnedSuccessiveFullRecheckSuccess.checked.next
  acceptedCertificateExact :
    learnedSuccessiveIncrementalSuccess.checked.next.certificate =
      learnedSuccessiveFullRecheckSuccess.checked.next.certificate

def runLearnedP6SuccessiveComparison :
    LearnedP6SuccessiveComparisonOutput :=
  { receivedUpdate := learnedExtendedSerializedUpdate
    receivedUpdateExact := rfl
    incrementalDecision := observeLearnedP6SuccessiveIncremental
    fullRecheckDecision := observeLearnedP6SuccessiveFullRecheck
    incrementalDecisionExact := by
      unfold observeLearnedP6SuccessiveIncremental
      rw [checkLearnedSuccessiveIncremental_exact]
    fullRecheckDecisionExact := by
      unfold observeLearnedP6SuccessiveFullRecheck
      rw [checkLearnedSuccessiveFullRecheck_exact]
    transportedStructuralCount :=
      learnedSuccessiveTransportedStructuralFragments.length
    recomputedStructuralCount :=
      learnedSuccessiveRecomputedStructuralFragments.length
    transportedStructuralCountExact := rfl
    recomputedStructuralCountExact := rfl
    installedAssemblyExact := learnedSuccessiveInstalledStructuralAssembly_exact
    transportReadsCheckedSource := learnedSuccessiveTransport_reads_checked_source
    acceptedSuccessorExact := learnedSuccessiveIncrementalAndFullSuccessor_exact
    acceptedCertificateExact :=
      learnedSuccessiveIncrementalAndFullCertificate_exact }

def learnedP2ChangedConsumerInputUpdate :
    LearnedSerializedConstitutiveUpdate :=
  { learnedAlignedSerializedUpdate with
    nextInput := IndependentLearnedCurrentCase.neither.input.toRequirementInput }

def learnedP3RejectedContractTransitionUpdate :
    LearnedSerializedConstitutiveUpdate :=
  { learnedAlignedSerializedUpdate with
    transition := { current := .initial, next := .initial } }

theorem learnedP2NetworkHeldFixed :
    learnedP2ChangedConsumerInputUpdate.targetNetwork =
      learnedAlignedSerializedUpdate.targetNetwork := rfl

theorem learnedP2ConsumerInputChanged :
    learnedP2ChangedConsumerInputUpdate.nextInput ≠
      learnedAlignedSerializedUpdate.nextInput := by
  intro same
  have requirementSame :=
    congrArg (fun input => input.requirement) same
  cases requirementSame

theorem learnedP3ArtifactHeldFixed :
    learnedP3RejectedContractTransitionUpdate.targetNetwork =
        learnedAlignedSerializedUpdate.targetNetwork ∧
      learnedP3RejectedContractTransitionUpdate.targetStableNaming =
        learnedAlignedSerializedUpdate.targetStableNaming ∧
      learnedP3RejectedContractTransitionUpdate.nextInput =
        learnedAlignedSerializedUpdate.nextInput ∧
      learnedP3RejectedContractTransitionUpdate.intent =
        learnedAlignedSerializedUpdate.intent := ⟨rfl, rfl, rfl, rfl⟩

theorem learnedP3TransitionChanged :
    learnedP3RejectedContractTransitionUpdate.transition ≠
      learnedAlignedSerializedUpdate.transition := by
  intro same
  have targetSame := congrArg (fun transition => transition.next) same
  cases targetSame

theorem learnedP2CanonicalIncrementalAccepted :
    observeGenericIncremental learnedAlignedSerializedUpdate = .accepted := by
  rfl

theorem learnedP2ChangedConsumerIncrementalRejected :
    observeGenericIncremental learnedP2ChangedConsumerInputUpdate = .rejected := by
  rfl

theorem learnedP3AllowedIncrementalAccepted :
    observeGenericIncremental learnedAlignedSerializedUpdate = .accepted :=
  learnedP2CanonicalIncrementalAccepted

theorem learnedP3ChangedIncrementalRejected :
    observeGenericIncremental learnedP3RejectedContractTransitionUpdate =
      .rejected := by
  rfl

theorem learnedP3AllowedFullRecheckAccepted :
    observeIndependentFullRecheck learnedAlignedSerializedUpdate = .accepted := by
  rfl

theorem learnedP3ChangedFullRecheckRejected :
    observeIndependentFullRecheck learnedP3RejectedContractTransitionUpdate =
      .rejected := by
  rfl

end ConstitutiveSearch.NeuralAgent
/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.NeuralAgent.observeIndependentFullRecheck
#print axioms ConstitutiveSearch.NeuralAgent.observePostForgettingFullRecheck
#print axioms ConstitutiveSearch.NeuralAgent.observePostForgettingIncremental
#print axioms ConstitutiveSearch.NeuralAgent.LearnedP2PathObservation
#print axioms ConstitutiveSearch.NeuralAgent.learnedP2FixedNetworkOutputs
#print axioms ConstitutiveSearch.NeuralAgent.learnedP2CanonicalProposal
#print axioms ConstitutiveSearch.NeuralAgent.learnedP2AdmissibleDecoder
#print axioms ConstitutiveSearch.NeuralAgent.learnedP2ModifiedDecoder
#print axioms ConstitutiveSearch.NeuralAgent.learnedP2AdmissibleProposal
#print axioms ConstitutiveSearch.NeuralAgent.learnedP2ModifiedProposal
#print axioms ConstitutiveSearch.NeuralAgent.learnedP2AdmissibleRequest
#print axioms ConstitutiveSearch.NeuralAgent.learnedP2CanonicalRequest
#print axioms ConstitutiveSearch.NeuralAgent.learnedP2ModifiedRequest
#print axioms ConstitutiveSearch.NeuralAgent.learnedP2CanonicalProposal_is_executed
#print axioms ConstitutiveSearch.NeuralAgent.learnedP2CanonicalRequest_is_executed
#print axioms ConstitutiveSearch.NeuralAgent.LearnedP2ConsumerFragment
#print axioms ConstitutiveSearch.NeuralAgent.checkLearnedP2Path
#print axioms ConstitutiveSearch.NeuralAgent.recheckLearnedP2Path
#print axioms ConstitutiveSearch.NeuralAgent.observeLearnedP2Path
#print axioms ConstitutiveSearch.NeuralAgent.learnedP2CanonicalPathAccepted
#print axioms ConstitutiveSearch.NeuralAgent.learnedP2AdmissibleDecoderChanged
#print axioms ConstitutiveSearch.NeuralAgent.learnedP2AdmissibleProposalCanonical
#print axioms ConstitutiveSearch.NeuralAgent.learnedP2AdmissibleRequestCanonical
#print axioms ConstitutiveSearch.NeuralAgent.learnedP2AdmissiblePathAccepted
#print axioms ConstitutiveSearch.NeuralAgent.learnedP2CanonicalFragment
#print axioms ConstitutiveSearch.NeuralAgent.learnedP2AdmissibleFragment
#print axioms ConstitutiveSearch.NeuralAgent.checkLearnedP2CanonicalFragment_exact
#print axioms ConstitutiveSearch.NeuralAgent.checkLearnedP2AdmissibleFragment_exact
#print axioms ConstitutiveSearch.NeuralAgent.learnedP2ModifiedProposalDifferent
#print axioms ConstitutiveSearch.NeuralAgent.learnedP2ModifiedRequestDifferent
#print axioms ConstitutiveSearch.NeuralAgent.learnedP2ModifiedPathRejected
#print axioms ConstitutiveSearch.NeuralAgent.learnedP2CanonicalRecheckAccepted
#print axioms ConstitutiveSearch.NeuralAgent.learnedP2AdmissibleRecheckAccepted
#print axioms ConstitutiveSearch.NeuralAgent.learnedP2ModifiedRecheckRejected
#print axioms ConstitutiveSearch.NeuralAgent.LearnedP2ConsumerVersion
#print axioms ConstitutiveSearch.NeuralAgent.LearnedP2ConsumerVersion.decoder
#print axioms ConstitutiveSearch.NeuralAgent.LearnedP2ConsumerFragment.action
#print axioms ConstitutiveSearch.NeuralAgent.LearnedP2ConsumerFragment.effect
#print axioms ConstitutiveSearch.NeuralAgent.learnedP2RecomputedCertificateFragments
#print axioms ConstitutiveSearch.NeuralAgent.learnedP2TargetAnalysisForAdmittedNamingFromDecision
#print axioms ConstitutiveSearch.NeuralAgent.learnedP2ReceivedTargetAnalysis
#print axioms ConstitutiveSearch.NeuralAgent.LearnedP2CheckerError
#print axioms ConstitutiveSearch.NeuralAgent.LearnedP2IncrementalAnalysis
#print axioms ConstitutiveSearch.NeuralAgent.LearnedP2IncrementalLocalConditions
#print axioms ConstitutiveSearch.NeuralAgent.analyzeLearnedP2Incrementally
#print axioms ConstitutiveSearch.NeuralAgent.completeLearnedP2IncrementalAnalysis
#print axioms ConstitutiveSearch.NeuralAgent.learnedP2IncrementalLocalConditionsOfSuccess
#print axioms ConstitutiveSearch.NeuralAgent.learnedP2IncrementalCheckerEngine
#print axioms ConstitutiveSearch.NeuralAgent.observeLearnedP2Incremental
#print axioms ConstitutiveSearch.NeuralAgent.LearnedP2DecodedArtifact
#print axioms ConstitutiveSearch.NeuralAgent.LearnedP2ArtifactError
#print axioms ConstitutiveSearch.NeuralAgent.decodeLearnedP2Artifact
#print axioms ConstitutiveSearch.NeuralAgent.LearnedP2DecodedArtifact.fragments
#print axioms ConstitutiveSearch.NeuralAgent.learnedP2ExecutableMetaContractInterface
#print axioms ConstitutiveSearch.NeuralAgent.LearnedP2AlignedTransitionDecision
#print axioms ConstitutiveSearch.NeuralAgent.learnedP2AlignedTransitionDecision
#print axioms ConstitutiveSearch.NeuralAgent.mapLearnedP2FullRecheckTargetError
#print axioms ConstitutiveSearch.NeuralAgent.recomputeLearnedP2FullRecheckExecution
#print axioms ConstitutiveSearch.NeuralAgent.learnedP2FullRecheckEngine
#print axioms ConstitutiveSearch.NeuralAgent.observeLearnedP2FullRecheck
#print axioms ConstitutiveSearch.NeuralAgent.learnedP2CanonicalIncrementalPathAccepted
#print axioms ConstitutiveSearch.NeuralAgent.learnedP2AdmissibleIncrementalPathAccepted
#print axioms ConstitutiveSearch.NeuralAgent.learnedP2ForbiddenIncrementalPathRejected
#print axioms ConstitutiveSearch.NeuralAgent.learnedP2CanonicalFullRecheckPathAccepted
#print axioms ConstitutiveSearch.NeuralAgent.learnedP2AdmissibleFullRecheckPathAccepted
#print axioms ConstitutiveSearch.NeuralAgent.learnedP2ForbiddenFullRecheckPathRejected
#print axioms ConstitutiveSearch.NeuralAgent.learnedP2CanonicalIncrementalSuccess
#print axioms ConstitutiveSearch.NeuralAgent.learnedP2AdmissibleIncrementalSuccess
#print axioms ConstitutiveSearch.NeuralAgent.learnedP2AdmissibleFullRecheckSuccess
#print axioms ConstitutiveSearch.NeuralAgent.learnedP2AdmissibleIncrementalAction_exact
#print axioms ConstitutiveSearch.NeuralAgent.learnedP2AdmissibleFullRecheckAction_exact
#print axioms ConstitutiveSearch.NeuralAgent.learnedP2AdmissibleIncrementalEffect_consumes_action
#print axioms ConstitutiveSearch.NeuralAgent.learnedP2AdmissibleFullRecheckEffect_consumes_action
#print axioms ConstitutiveSearch.NeuralAgent.learnedP2AdmissibleIncrementalAndFullSuccessor_exact
#print axioms ConstitutiveSearch.NeuralAgent.learnedP2AdmissibleIncrementalAndFullCertificate_exact
#print axioms ConstitutiveSearch.NeuralAgent.learnedP4IncorrectForgetting
#print axioms ConstitutiveSearch.NeuralAgent.learnedP4IncorrectForgettingCollapsesSeparatedSources
#print axioms ConstitutiveSearch.NeuralAgent.learnedP4SeparatorRevealsRequiredDistinction
#print axioms ConstitutiveSearch.NeuralAgent.learnedP4IncorrectForgettingCannotBeExact
#print axioms ConstitutiveSearch.NeuralAgent.observeLearnedP6SuccessiveIncremental
#print axioms ConstitutiveSearch.NeuralAgent.observeLearnedP6SuccessiveFullRecheck
#print axioms ConstitutiveSearch.NeuralAgent.LearnedP6SuccessiveComparisonOutput
#print axioms ConstitutiveSearch.NeuralAgent.runLearnedP6SuccessiveComparison
#print axioms ConstitutiveSearch.NeuralAgent.learnedP2ChangedConsumerInputUpdate
#print axioms ConstitutiveSearch.NeuralAgent.learnedP3RejectedContractTransitionUpdate
#print axioms ConstitutiveSearch.NeuralAgent.learnedP2NetworkHeldFixed
#print axioms ConstitutiveSearch.NeuralAgent.learnedP2ConsumerInputChanged
#print axioms ConstitutiveSearch.NeuralAgent.learnedP3ArtifactHeldFixed
#print axioms ConstitutiveSearch.NeuralAgent.learnedP3TransitionChanged
#print axioms ConstitutiveSearch.NeuralAgent.learnedP2CanonicalIncrementalAccepted
#print axioms ConstitutiveSearch.NeuralAgent.learnedP2ChangedConsumerIncrementalRejected
#print axioms ConstitutiveSearch.NeuralAgent.learnedP3AllowedIncrementalAccepted
#print axioms ConstitutiveSearch.NeuralAgent.learnedP3ChangedIncrementalRejected
#print axioms ConstitutiveSearch.NeuralAgent.learnedP3AllowedFullRecheckAccepted
#print axioms ConstitutiveSearch.NeuralAgent.learnedP3ChangedFullRecheckRejected
/- AXIOM_AUDIT_END -/
