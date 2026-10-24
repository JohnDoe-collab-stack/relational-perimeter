import RelationalPerimeter.Agents.Neural.LearnedSuccessiveCanonicalChecker

/-! # Canonical successive checker regression closure -/
set_option genInjectivity false
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
namespace ConstitutiveSearch.NeuralAgent
open NativeMechanism
open ContinuationSignatures

theorem checkLearnedExtendedSerializedUpdate_accepts :
    checkLearnedExtendedSerializedUpdate learnedExtendedSerializedUpdate =
      .ok (dependentCheckedUpdateResult learnedExtendedCheckedUpdate) := by
  unfold checkLearnedExtendedSerializedUpdate
  split
  · have impossible :=
      ‹decodeLearnedSuccessiveUpdate learnedExtendedSerializedUpdate =
        .error _›.symm.trans decodeLearnedSuccessiveUpdate_reference_exact
    cases impossible
  · rename_i decoded decodedExact
    have decodedValueExact : decoded = learnedReferenceDecodedSuccessiveUpdate :=
      Except.ok.inj (decodedExact.symm.trans
        decodeLearnedSuccessiveUpdate_reference_exact)
    cases decodedValueExact
    unfold learnedExtendedCheckedUpdate
    exact checkDecodedLearnedExtendedSerializedUpdate_of_analysis
      learnedExtendedSerializedUpdate learnedReferenceDecodedSuccessiveUpdate
      decodedExact learnedReferenceSuccessiveAnalysis
      analyzeLearnedSuccessiveUpdate_reference_exact

theorem checkLearnedExtendedSerializedUpdate_rejects_first :
    checkLearnedExtendedSerializedUpdate learnedAlignedSerializedUpdate =
      .error .unexpectedTransition := by
  rfl

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.NeuralAgent.checkLearnedExtendedSerializedUpdate_accepts
#print axioms ConstitutiveSearch.NeuralAgent.checkLearnedExtendedSerializedUpdate_rejects_first
/- AXIOM_AUDIT_END -/
