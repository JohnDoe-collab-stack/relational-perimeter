import RelationalPerimeter.Agents.Neural.LearnedSuccessiveCompleteness

/-!
# Received-predecessor reference equation

This equation closes the public successive member through the material
current-aware producer.  It does not identify that producer with the
standalone canonical engine for arbitrary inputs.
-/
set_option genInjectivity false
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
namespace ConstitutiveSearch.NeuralAgent
open NativeMechanism
open ContinuationSignatures

theorem analyzeDecodedLearnedSuccessiveUpdateAtCurrent_reference_exact :
    analyzeDecodedLearnedSuccessiveUpdateAtCurrent LearnedAlignedCheckedAgent
        rfl learnedExtendedSerializedUpdate
        learnedReferenceDecodedSuccessiveUpdate
        decodeLearnedSuccessiveUpdate_reference_exact =
      .ok learnedReferenceSuccessiveAnalysis.target := by
  unfold analyzeDecodedLearnedSuccessiveUpdateAtCurrent
  have transitionAccepted :
      decideTransition learnedExecutableMetaContractInterface
          learnedExtendedSerializedUpdate.transition =
        some learnedExtendedTransitionDecision := by
    rfl
  split
  · have impossible :=
      ‹decideTransition learnedExecutableMetaContractInterface
          learnedExtendedSerializedUpdate.transition = none›.symm.trans
        transitionAccepted
    cases impossible
  · rename_i receivedDecision receivedExact
    have decisionExact : receivedDecision = learnedExtendedTransitionDecision :=
      Option.some.inj (receivedExact.symm.trans transitionAccepted)
    cases decisionExact
    rw [dif_pos (by rfl), dif_pos (by rfl)]
    have namingExact :
        learnedReferenceDecodedSuccessiveUpdate.stable.naming =
          learnedExtendedStableNaming := by
      rfl
    cases namingExact
    dsimp only
    split
    · have impossible :=
        ‹calculateIncrementalStructuralAssembly
            LearnedAlignedCheckedAgent.certificate _ _ _ = .error _›.symm.trans
          learnedSuccessiveCalculatedStructuralAssembly.calculated
      cases impossible
    · rename_i observations calculated
      have observationsExact : observations =
          learnedSuccessiveCalculatedStructuralAssembly.observations :=
        Except.ok.inj (calculated.symm.trans
          learnedSuccessiveCalculatedStructuralAssembly.calculated)
      cases observationsExact
      rw [dif_pos (by rfl)]
      rfl

theorem checkDecodedLearnedExtendedSerializedUpdateAtCurrent_reference_exact :
    checkDecodedLearnedExtendedSerializedUpdateAtCurrent
        LearnedAlignedCheckedAgent rfl learnedExtendedSerializedUpdate
        learnedReferenceDecodedSuccessiveUpdate
        decodeLearnedSuccessiveUpdate_reference_exact =
      .ok (dependentCheckedUpdateResult
        (buildIncrementalCheckedUpdate
          learnedReferenceSuccessiveAnalysis.target)) := by
  unfold checkDecodedLearnedExtendedSerializedUpdateAtCurrent
  rw [analyzeDecodedLearnedSuccessiveUpdateAtCurrent_reference_exact]
  rfl

/-- The exact public successive source is accepted through the current-aware
decoder/checker path, not through the standalone canonical compatibility
wrapper. -/
theorem checkLearnedSuccessiveSourceAtCurrent_reference_exact :
    (match decodedExact :
        decodeLearnedSuccessiveUpdate learnedExtendedSerializedUpdate with
      | .error problem => Except.error problem
      | .ok decoded =>
          checkDecodedLearnedExtendedSerializedUpdateAtCurrent
            LearnedAlignedCheckedAgent rfl learnedExtendedSerializedUpdate
            decoded decodedExact) =
      .ok (dependentCheckedUpdateResult
        (buildIncrementalCheckedUpdate
          learnedReferenceSuccessiveAnalysis.target)) := by
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
    exact checkDecodedLearnedExtendedSerializedUpdateAtCurrent_reference_exact

theorem checkLearnedSuccessiveSourceAtCurrent_rejects_first :
    (match decodedExact :
        decodeLearnedSuccessiveUpdate learnedAlignedSerializedUpdate with
      | .error problem => Except.error problem
      | .ok decoded =>
          checkDecodedLearnedExtendedSerializedUpdateAtCurrent
            LearnedAlignedCheckedAgent rfl learnedAlignedSerializedUpdate
            decoded decodedExact) =
      .error .unexpectedTransition := by
  rfl

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.NeuralAgent.analyzeDecodedLearnedSuccessiveUpdateAtCurrent_reference_exact
#print axioms ConstitutiveSearch.NeuralAgent.checkDecodedLearnedExtendedSerializedUpdateAtCurrent_reference_exact
#print axioms ConstitutiveSearch.NeuralAgent.checkLearnedSuccessiveSourceAtCurrent_reference_exact
#print axioms ConstitutiveSearch.NeuralAgent.checkLearnedSuccessiveSourceAtCurrent_rejects_first
/- AXIOM_AUDIT_END -/
