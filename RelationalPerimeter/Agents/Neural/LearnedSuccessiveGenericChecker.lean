import RelationalPerimeter.Agents.Neural.LearnedSuccessiveReference

/-! # Generic learned successive checker -/
set_option genInjectivity false
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
namespace ConstitutiveSearch.NeuralAgent
open NativeMechanism
open ContinuationSignatures

def learnedExtendedCheckedUpdate : CheckedUpdate
    LearnedAlignedCheckedAgent .extended :=
  buildIncrementalCheckedUpdate learnedReferenceSuccessiveAnalysis.target

def learnedSuccessiveIncrementalCheckerEngine :
    IncrementalCheckerEngine LearnedAlignedCheckedAgent :=
  { Update := LearnedSerializedConstitutiveUpdate
    Error := LearnedRuntimeUpdateError
    Analysis := LearnedSuccessiveEngineAnalysis
    analyze := analyzeLearnedSuccessiveUpdate
    LocalConditions := LearnedSuccessiveLocalConditionData
    complete := completeLearnedSuccessiveAnalysis
    localOfSuccess := learnedSuccessiveLocalConditionsOfSuccess
    target := fun analysis => analysis.target }

theorem learnedSuccessiveIncrementalAccepted :
    GenericIncrementalUpdateAccepted learnedSuccessiveIncrementalCheckerEngine
      learnedExtendedSerializedUpdate := by
  apply (checkGenericIncrementalUpdate_complete_for_local_conditions
    learnedSuccessiveIncrementalCheckerEngine
      learnedExtendedSerializedUpdate).2
  exact ⟨learnedReferenceSuccessiveLocalConditions⟩

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.NeuralAgent.learnedSuccessiveIncrementalCheckerEngine
#print axioms ConstitutiveSearch.NeuralAgent.learnedSuccessiveIncrementalAccepted
/- AXIOM_AUDIT_END -/
