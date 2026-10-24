import RelationalPerimeter.Agents.Neural.LearnedSuccessiveEngine

/-!
# Autonomous local completeness for the learned successive checker

The local conditions are stated independently of the global checker result.
Their positive data reconstructs exactly the analysis produced by the
successive execution engine.
-/
set_option genInjectivity false
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
namespace ConstitutiveSearch.NeuralAgent
open NativeMechanism
open ContinuationSignatures

structure LearnedSuccessiveLocalConditionData
    (source : LearnedSerializedConstitutiveUpdate) : Type 6 where
  executed : LearnedSuccessiveExecutedDependencies source
  structuralAssembly : CalculatedIncrementalStructuralAssembly
    LearnedAlignedCheckedAgent.certificate executed.preCertificateGraph
    (licensedStructuralEntries executed.transportedLicenses)
    executed.recomputedStructural
  structuralAssemblyChecked :
    checkLearnedSuccessiveStructuralAssembly executed = .ok structuralAssembly

def learnedSuccessiveAnalysisOfLocalConditions
    {source : LearnedSerializedConstitutiveUpdate}
    (conditions : LearnedSuccessiveLocalConditionData source) :
    LearnedSuccessiveEngineAnalysis source :=
  LearnedSuccessiveEngineAnalysis.ofExecuted
    conditions.executed conditions.structuralAssembly
    conditions.structuralAssemblyChecked

theorem analyzeLearnedSuccessiveUpdate_of_local_conditions
    (source : LearnedSerializedConstitutiveUpdate)
    (conditions : LearnedSuccessiveLocalConditionData source) :
    analyzeLearnedSuccessiveUpdate source =
      .ok (learnedSuccessiveAnalysisOfLocalConditions conditions) := by
  unfold analyzeLearnedSuccessiveUpdate
  split
  · have impossible :=
      ‹decodeLearnedSuccessiveUpdate source = .error _›.symm.trans
        conditions.executed.decodedExact
    cases impossible
  · rename_i decoded decodedExact
    have decodedValueExact : decoded = conditions.executed.decoded :=
      Except.ok.inj (decodedExact.symm.trans
        conditions.executed.decodedExact)
    cases decodedValueExact
    unfold analyzeDecodedLearnedSuccessiveUpdate
    split
    · have impossible :=
        ‹decideTransition learnedExecutableMetaContractInterface
          source.transition = none›.symm.trans
          conditions.executed.transitionAccepted
      cases impossible
    · rename_i receivedDecision transitionAccepted
      have decisionExact : receivedDecision = conditions.executed.receivedDecision :=
        Option.some.inj
          (transitionAccepted.symm.trans
            conditions.executed.transitionAccepted)
      cases decisionExact
      rw [dif_pos conditions.executed.authorizationConsumed,
        dif_pos conditions.executed.targetNetworkExact]
      let executed : LearnedSuccessiveExecutedDependencies source :=
        { decoded := conditions.executed.decoded
          decodedExact := decodedExact
          receivedDecision := conditions.executed.receivedDecision
          transitionAccepted := transitionAccepted
          authorizationConsumed := conditions.executed.authorizationConsumed
          targetNetworkExact := conditions.executed.targetNetworkExact }
      have executedExact : executed = conditions.executed :=
        LearnedSuccessiveExecutedDependencies.unique executed
          conditions.executed
      cases executedExact
      change analyzeLearnedSuccessiveExecutedDependencies
          conditions.executed =
        .ok (learnedSuccessiveAnalysisOfLocalConditions conditions)
      unfold analyzeLearnedSuccessiveExecutedDependencies
      split
      · have impossible :=
          ‹checkLearnedSuccessiveStructuralAssembly conditions.executed =
            .error _›.symm.trans conditions.structuralAssemblyChecked
        cases impossible
      · rename_i actualAssembly assemblyChecked
        have assemblyExact : actualAssembly = conditions.structuralAssembly :=
          Except.ok.inj
            (assemblyChecked.symm.trans
              conditions.structuralAssemblyChecked)
        cases assemblyExact
        rfl

def completeLearnedSuccessiveAnalysis
    (source : LearnedSerializedConstitutiveUpdate)
    (conditions : LearnedSuccessiveLocalConditionData source) :
    { analysis : LearnedSuccessiveEngineAnalysis source //
      analyzeLearnedSuccessiveUpdate source = .ok analysis } :=
  ⟨learnedSuccessiveAnalysisOfLocalConditions conditions,
    analyzeLearnedSuccessiveUpdate_of_local_conditions source conditions⟩

def LearnedSuccessiveEngineAnalysis.localConditions
    {source : LearnedSerializedConstitutiveUpdate}
    (analysis : LearnedSuccessiveEngineAnalysis source) :
    LearnedSuccessiveLocalConditionData source :=
  { executed := analysis.executed
    structuralAssembly := analysis.structuralAssembly
    structuralAssemblyChecked := analysis.structuralAssemblyChecked }

/-- Extracting the autonomous local conditions from an analysis and rebuilding
through the sole public formation rule preserves that exact analysis. -/
@[simp] theorem learnedSuccessiveAnalysisOfLocalConditions_localConditions
    {source : LearnedSerializedConstitutiveUpdate}
    (analysis : LearnedSuccessiveEngineAnalysis source) :
    learnedSuccessiveAnalysisOfLocalConditions analysis.localConditions =
      analysis := by
  cases analysis
  rfl

def learnedSuccessiveLocalConditionsOfSuccess
    (source : LearnedSerializedConstitutiveUpdate)
    (analysis : LearnedSuccessiveEngineAnalysis source)
    (_accepted : analyzeLearnedSuccessiveUpdate source = .ok analysis) :
    LearnedSuccessiveLocalConditionData source :=
  analysis.localConditions

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.NeuralAgent.LearnedSuccessiveLocalConditionData
#print axioms ConstitutiveSearch.NeuralAgent.analyzeLearnedSuccessiveUpdate_of_local_conditions
#print axioms ConstitutiveSearch.NeuralAgent.completeLearnedSuccessiveAnalysis
#print axioms ConstitutiveSearch.NeuralAgent.learnedSuccessiveAnalysisOfLocalConditions_localConditions
#print axioms ConstitutiveSearch.NeuralAgent.learnedSuccessiveLocalConditionsOfSuccess
/- AXIOM_AUDIT_END -/
