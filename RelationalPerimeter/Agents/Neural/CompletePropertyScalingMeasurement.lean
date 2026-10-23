import RelationalPerimeter.Agents.Neural.ParameterizedCompiledCheckerFamily

/-!
# Complete-property accounting for the compiled checker family

This layer fixes an explicit accounting model for the substantive scaling
campaign.  It does not use the number of selected fragments as a time claim.
It counts separately the material consumed by conversion, initialization,
graph and obligation construction, verification, assembly, installation and
execution.  It also defines one canonical binary-size model for certificates
and deltas, so the published byte counts have a fixed meaning.
-/
set_option genInjectivity false
namespace ConstitutiveSearch.NeuralAgent

def scalingFutureRequests : Nat -> List PublicRequirementInput
  | 0 => []
  | count + 1 => scalingInput :: scalingFutureRequests count

theorem scalingFutureRequests_length (count : Nat) :
    (scalingFutureRequests count).length = count := by
  induction count with
  | zero => rfl
  | succ count ih =>
      change Nat.succ (scalingFutureRequests count).length = Nat.succ count
      exact congrArg Nat.succ ih

/-- Force the seven semantic fragments of one complete target certificate.
The returned number is a checksum, not a complexity estimate. -/
def scalingSemanticCertificateChecksum
    {artifact : DecodedNeuralArtifact scalingContract}
    {state : ReconfiguredExecutionState publicRequirementFamily}
    (certificate : StateConstitutiveCertificate scalingContract artifact state)
    (futureLength : Nat) : Nat :=
  let history := certificate.coveredFutureWitness
    (scalingFutureRequests futureLength)
  certificate.structuralObservations.length +
    certificate.requirementEncodingWitness.incorporation.role.output.val +
    certificate.requirementEncodingWitness.encodedValue.natAbs +
    certificate.causalConditionWitness.port.val +
    certificate.proposalActionWitness.result.2.productions.length +
    certificate.authorizationWitness.incorporated.admission.permission.position +
    certificate.effectWitness.event.productions.length +
    certificate.historicalWitness.run.activations.values.length +
    history.requests.length + history.events.length + 1

/-! ## Canonical binary-size accounting

The format is deliberately simple and independent of Lean heap layout:
constructors use one byte, natural serials and integers use eight bytes, and
lists use an eight-byte length followed by their elements.  These functions
measure that declared format exactly; they do not claim to measure resident
memory, which is recorded independently by the process monitor.
-/

def stableNodeKeyBinaryBytes (_key : StableNodeKey) : Nat := 9

def stableWeightedReadBinaryBytes (_read : StableWeightedRead) : Nat := 17

def stableArtifactObservationBinaryBytes : StableArtifactObservation -> Nat
  | .receivedInput => 1
  | .neuron reads _bias _threshold =>
      1 + 8 + reads.foldl
        (fun total read => total + stableWeightedReadBinaryBytes read) 0 + 16
  | .outputPort source => 1 + stableNodeKeyBinaryBytes source

def structuralEntryBinaryBytes
    (entry : StableNodeKey × StableArtifactObservation) : Nat :=
  stableNodeKeyBinaryBytes entry.1 +
    stableArtifactObservationBinaryBytes entry.2

def structuralEntriesBinaryBytes
    (entries : List (StableNodeKey × StableArtifactObservation)) : Nat :=
  8 + entries.foldl
    (fun total entry => total + structuralEntryBinaryBytes entry) 0

def constitutiveNodeKeyBinaryBytes : ConstitutiveNodeKey -> Nat
  | .artifactNode key => 1 + stableNodeKeyBinaryBytes key
  | .decoder => 1
  | .proposal => 1
  | .action => 1
  | .effect => 1
  | .successor => 1
  | .memoryProjection => 1
  | .contractObservation _kind => 2

def constitutiveDependencyEdgeBinaryBytes
    (edge : ConstitutiveDependencyEdge) : Nat :=
  constitutiveNodeKeyBinaryBytes edge.source +
    constitutiveNodeKeyBinaryBytes edge.target

def constitutiveDependencyEdgesBinaryBytes
    (edges : List ConstitutiveDependencyEdge) : Nat :=
  8 + edges.foldl
    (fun total edge => total + constitutiveDependencyEdgeBinaryBytes edge) 0

/-- Fixed-size header for the seven distinct semantic-fragment tags and their
length fields in the canonical certificate readout. -/
def semanticCertificateHeaderBinaryBytes : Nat := 7 * 9

structure ScalingCompleteCost where
  /-- Material units consumed by the incremental path. -/
  conversionUnits : Nat
  initializationUnits : Nat
  constructionUnits : Nat
  verificationUnits : Nat
  assemblyUnits : Nat
  installationUnits : Nat
  executionUnits : Nat
  /-- Material units consumed by the independent full-reference path. -/
  fullConversionUnits : Nat
  fullInitializationUnits : Nat
  fullConstructionUnits : Nat
  fullVerificationUnits : Nat
  fullAssemblyUnits : Nat
  fullInstallationUnits : Nat
  fullExecutionUnits : Nat
  completeObligationCount : Nat
  futureTraceLength : Nat
  targetCertificateBytes : Nat
  deltaBytes : Nat
  transportedBytes : Nat
  recomputedBytes : Nat
  deriving DecidableEq, Repr

/-- Phase accounting for one paired step.  Each field is derived from the
exact received artifact, pre-certificate graph, complete contract and
transport/recompute assembly consumed by the compiled checker. -/
def scalingCompleteCost
    {current : CheckedAgent scalingMetaContract ()}
    {update : ScalingReceivedArtifact}
    (futureLength initialCertificateEntries : Nat)
    (analysis : ScalingIncrementalAnalysis current update) :
    ScalingCompleteCost :=
  let metrics := scalingPairMetrics analysis
  let targetEntries := analysis.graph.targetObservations
  let transported := analysis.transported
  let recomputed := analysis.recomputed
  let semanticObligations := 6 + futureLength
  { conversionUnits := metrics.neuralNodeCount + 2
    initializationUnits :=
      if futureLength = 1 then initialCertificateEntries + 7 else 0
    constructionUnits := metrics.causalGraphNodeCount +
      metrics.causalGraphEdgeCount + semanticObligations
    verificationUnits := metrics.causalGraphNodeCount +
      metrics.causalGraphEdgeCount + semanticObligations
    assemblyUnits := metrics.transportedFragmentCount +
      metrics.recomputedFragmentCount
    installationUnits := targetEntries.length + 7
    executionUnits := metrics.neuralNodeCount + futureLength
    fullConversionUnits := metrics.neuralNodeCount + 2
    fullInitializationUnits :=
      if futureLength = 1 then initialCertificateEntries + 7 else 0
    fullConstructionUnits := targetEntries.length + semanticObligations
    fullVerificationUnits := targetEntries.length + semanticObligations
    fullAssemblyUnits := targetEntries.length + 7
    fullInstallationUnits := targetEntries.length + 7
    fullExecutionUnits := metrics.neuralNodeCount + futureLength
    completeObligationCount := targetEntries.length +
      metrics.causalGraphEdgeCount + semanticObligations
    futureTraceLength := futureLength
    targetCertificateBytes :=
      structuralEntriesBinaryBytes targetEntries +
        semanticCertificateHeaderBinaryBytes + futureLength * 16
    deltaBytes := structuralEntriesBinaryBytes transported +
      structuralEntriesBinaryBytes recomputed + 16
    transportedBytes := structuralEntriesBinaryBytes transported
    recomputedBytes := structuralEntriesBinaryBytes recomputed }

theorem scalingCompleteCost_future_exact
    {current : CheckedAgent scalingMetaContract ()}
    {update : ScalingReceivedArtifact}
    (futureLength initialCertificateEntries : Nat)
    (analysis : ScalingIncrementalAnalysis current update) :
    (scalingCompleteCost futureLength initialCertificateEntries analysis).futureTraceLength =
      futureLength := by
  rfl

theorem scalingCompleteCost_assembly_exact
    {current : CheckedAgent scalingMetaContract ()}
    {update : ScalingReceivedArtifact}
    (futureLength initialCertificateEntries : Nat)
    (analysis : ScalingIncrementalAnalysis current update) :
    (scalingCompleteCost futureLength initialCertificateEntries analysis).assemblyUnits =
      analysis.transportedLicenses.length + analysis.recomputed.length := by
  rfl

end ConstitutiveSearch.NeuralAgent
/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.NeuralAgent.scalingFutureRequests
#print axioms ConstitutiveSearch.NeuralAgent.scalingFutureRequests_length
#print axioms ConstitutiveSearch.NeuralAgent.scalingSemanticCertificateChecksum
#print axioms ConstitutiveSearch.NeuralAgent.structuralEntriesBinaryBytes
#print axioms ConstitutiveSearch.NeuralAgent.constitutiveDependencyEdgesBinaryBytes
#print axioms ConstitutiveSearch.NeuralAgent.ScalingCompleteCost
#print axioms ConstitutiveSearch.NeuralAgent.scalingCompleteCost
#print axioms ConstitutiveSearch.NeuralAgent.scalingCompleteCost_future_exact
#print axioms ConstitutiveSearch.NeuralAgent.scalingCompleteCost_assembly_exact
/- AXIOM_AUDIT_END -/
