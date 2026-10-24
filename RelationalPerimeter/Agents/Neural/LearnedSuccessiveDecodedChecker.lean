import RelationalPerimeter.Agents.Neural.LearnedSuccessiveGenericChecker

/-!
# Decoded learned successive checker

The runtime entry point consumes the predecessor received by the dependent
checker and forwards it to the material transition analysis.
-/
set_option genInjectivity false
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
namespace ConstitutiveSearch.NeuralAgent
open NativeMechanism
open ContinuationSignatures

def checkDecodedLearnedExtendedSerializedUpdate
    (source : LearnedSerializedConstitutiveUpdate)
    (decoded : DecodedLearnedSuccessiveUpdate source)
    (decodedExact : decodeLearnedSuccessiveUpdate source = .ok decoded) :
    Except LearnedRuntimeUpdateError
      (DependentCheckedUpdateResult LearnedAlignedCheckedAgent) :=
  match analyzeDecodedLearnedSuccessiveUpdate source decoded decodedExact with
  | .error problem => .error problem
  | .ok analysis =>
      .ok (dependentCheckedUpdateResult
        (buildIncrementalCheckedUpdate analysis.target))

def checkDecodedLearnedExtendedSerializedUpdateAtCurrent
    (current : CheckedAgent learnedConstitutiveMetaContract .aligned)
    (currentExact : current = LearnedAlignedCheckedAgent)
    (source : LearnedSerializedConstitutiveUpdate)
    (decoded : DecodedLearnedSuccessiveUpdate source)
    (decodedExact : decodeLearnedSuccessiveUpdate source = .ok decoded) :
    Except LearnedRuntimeUpdateError (DependentCheckedUpdateResult current) :=
  match analyzeDecodedLearnedSuccessiveUpdateAtCurrent current currentExact source
      decoded decodedExact with
  | .error problem => .error problem
  | .ok analysis =>
      .ok (dependentCheckedUpdateResult
        (buildIncrementalCheckedUpdate analysis))

theorem checkDecodedLearnedExtendedSerializedUpdate_of_analysis
    (source : LearnedSerializedConstitutiveUpdate)
    (decoded : DecodedLearnedSuccessiveUpdate source)
    (decodedExact : decodeLearnedSuccessiveUpdate source = .ok decoded)
    (analysis : LearnedSuccessiveEngineAnalysis source)
    (accepted :
      analyzeDecodedLearnedSuccessiveUpdate source decoded decodedExact =
        .ok analysis) :
    checkDecodedLearnedExtendedSerializedUpdate source decoded decodedExact =
      .ok (dependentCheckedUpdateResult
        (buildIncrementalCheckedUpdate analysis.target)) := by
  unfold checkDecodedLearnedExtendedSerializedUpdate
  split
  · have impossible :=
      ‹analyzeDecodedLearnedSuccessiveUpdate source decoded decodedExact =
        .error _›.symm.trans accepted
    cases impossible
  · rename_i actual actualExact
    have analysisExact : actual = analysis :=
      Except.ok.inj (actualExact.symm.trans accepted)
    cases analysisExact
    rfl

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.NeuralAgent.checkDecodedLearnedExtendedSerializedUpdate
#print axioms ConstitutiveSearch.NeuralAgent.checkDecodedLearnedExtendedSerializedUpdateAtCurrent
#print axioms ConstitutiveSearch.NeuralAgent.checkDecodedLearnedExtendedSerializedUpdate_of_analysis
/- AXIOM_AUDIT_END -/
