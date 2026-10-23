import RelationalPerimeter.Agents.Neural.CausalParameterizedCompiledCheckerFamily
import RelationalPerimeter.Agents.Neural.CompletePropertyScalingMeasurement

/-!
# Complete-property accounting for the causal compiled family

This module defines the accounting model of the successor campaign.  It keeps
the historical v11 model untouched and measures the causal family whose target
is produced from the exact checked source through one action and one effect.
The counters are material readouts; they are not asymptotic-time theorems.
-/
set_option genInjectivity false
namespace ConstitutiveSearch.NeuralAgent

def causalScalingCompleteCost
    {current : CheckedAgent causalScalingMetaContract ()}
    {update : CausalScalingReceivedArtifact}
    (futureLength initialCertificateEntries : Nat)
    (analysis : CausalScalingIncrementalAnalysis current update) :
    ScalingCompleteCost :=
  let metrics := causalScalingPairMetrics analysis
  let graph := causalScalingIncrementalGraph current analysis.target
  let targetEntries := graph.targetObservations
  let transported := causalScalingIncrementalTransported current analysis.target
  let recomputed := causalScalingIncrementalRecomputed current analysis.target
  let semanticObligations := 6 + futureLength
  /- The two additional construction/execution units are the produced action
  and effect that connect the checked source to the successor. -/
  { conversionUnits := metrics.neuralNodeCount + 2
    initializationUnits :=
      if futureLength = 1 then initialCertificateEntries + 7 else 0
    constructionUnits := metrics.causalGraphNodeCount +
      metrics.causalGraphEdgeCount + semanticObligations + 2
    verificationUnits := metrics.causalGraphNodeCount +
      metrics.causalGraphEdgeCount + semanticObligations + 3
    assemblyUnits := metrics.transportedFragmentCount +
      metrics.recomputedFragmentCount
    installationUnits := targetEntries.length + 7
    executionUnits := metrics.neuralNodeCount + futureLength + 2
    fullConversionUnits := metrics.neuralNodeCount + 2
    fullInitializationUnits :=
      if futureLength = 1 then initialCertificateEntries + 7 else 0
    fullConstructionUnits := targetEntries.length + semanticObligations + 2
    fullVerificationUnits := targetEntries.length + semanticObligations + 3
    fullAssemblyUnits := targetEntries.length + 7
    fullInstallationUnits := targetEntries.length + 7
    fullExecutionUnits := metrics.neuralNodeCount + futureLength + 2
    completeObligationCount := targetEntries.length +
      metrics.causalGraphEdgeCount + semanticObligations + 3
    futureTraceLength := futureLength
    targetCertificateBytes :=
      structuralEntriesBinaryBytes targetEntries +
        semanticCertificateHeaderBinaryBytes + futureLength * 16
    deltaBytes := structuralEntriesBinaryBytes transported +
      structuralEntriesBinaryBytes recomputed + 16
    transportedBytes := structuralEntriesBinaryBytes transported
    recomputedBytes := structuralEntriesBinaryBytes recomputed }

theorem causalScalingCompleteCost_future_exact
    {current : CheckedAgent causalScalingMetaContract ()}
    {update : CausalScalingReceivedArtifact}
    (futureLength initialCertificateEntries : Nat)
    (analysis : CausalScalingIncrementalAnalysis current update) :
    (causalScalingCompleteCost futureLength initialCertificateEntries analysis).futureTraceLength =
      futureLength := by
  rfl

theorem causalScalingCompleteCost_assembly_exact
    {current : CheckedAgent causalScalingMetaContract ()}
    {update : CausalScalingReceivedArtifact}
    (futureLength initialCertificateEntries : Nat)
    (analysis : CausalScalingIncrementalAnalysis current update) :
    (causalScalingCompleteCost futureLength initialCertificateEntries analysis).assemblyUnits =
      (causalScalingIncrementalTransportLicenses current analysis.target).length +
        (causalScalingIncrementalRecomputed current analysis.target).length := by
  rfl

end ConstitutiveSearch.NeuralAgent
/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.NeuralAgent.causalScalingCompleteCost
#print axioms ConstitutiveSearch.NeuralAgent.causalScalingCompleteCost_future_exact
#print axioms ConstitutiveSearch.NeuralAgent.causalScalingCompleteCost_assembly_exact
/- AXIOM_AUDIT_END -/
