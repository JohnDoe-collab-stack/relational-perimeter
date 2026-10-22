import RelationalPerimeter.Agents.Neural.IncrementalReferenceEquivalence

/-! Regression checks for proof-free incremental verification and its exact
agreement with complete reference verification. -/
namespace ConstitutiveSearch.NeuralAgent.Tests
open ConstitutiveSearch.NeuralAgent

example :
    materializeIncrementalTarget publicIncrementalNeuralUpdate =
      publicSerializedReconfiguredNetwork :=
  publicIncrementalTarget_exact

example :
    checkIncrementalUpdate publicIncrementalNeuralUpdate =
      .ok publicIncrementalCheckedUpdate :=
  checkIncrementalUpdate_accepts_reference

example :
    GenericIncrementalUpdateLocalConditions publicIncrementalCheckerEngine
      publicIncrementalNeuralUpdate :=
  (analyzePublicIncrementalUpdate_complete
    publicIncrementalNeuralUpdate).mpr
      ⟨publicIncrementalLocalConditionDataOfExact
        publicIncrementalNeuralUpdate rfl rfl rfl⟩

example : PublicIncrementalEngineLocalConditions
    publicIncrementalNeuralUpdate :=
  ⟨publicIncrementalLocalConditionDataOfExact
    publicIncrementalNeuralUpdate rfl rfl rfl⟩

example :
    (publicIncrementalLocalConditionDataOfExact
      publicIncrementalNeuralUpdate rfl rfl rfl).preCertificateResult.affectedCone =
      affectedConstitutiveCone publicInitialStateConstitutiveCertificate
        publicPreCertificateConstitutiveGraph := by
  rfl

example (decision : PublicReconfiguredTransitionDecision) :
    (publicIncrementalTargetAnalysisFromDecision decision).transition =
      decision.transition :=
  publicIncrementalTargetAnalysisFromDecision_transition_exact decision

example {update : IncrementalNeuralUpdate}
    (analysis : PublicIncrementalEngineAnalysis update) :
    analysis.targetAnalysis.transition =
      analysis.executed.transitionDecision.transition := by
  rfl

example {update : IncrementalNeuralUpdate}
    (analysis : PublicIncrementalEngineAnalysis update) :
    analysis.targetAnalysis.execution =
      analysis.executed.executedSuccessor := by
  rfl

example {update : IncrementalNeuralUpdate}
    (analysis : PublicIncrementalEngineAnalysis update) :
    analysis.targetAnalysis.fragments = analysis.assembly.fragments := by
  rfl

example :
    GenericIncrementalUpdateAccepted publicIncrementalCheckerEngine
      publicIncrementalNeuralUpdate :=
  (publicIncrementalAcceptance_iff_generic
    publicIncrementalNeuralUpdate).mp
      ⟨publicIncrementalCheckedUpdate,
        checkIncrementalUpdate_accepts_reference⟩

example (update : IncrementalNeuralUpdate) :
    GenericIncrementalUpdateAccepted publicIncrementalCheckerEngine update ↔
      GenericIncrementalUpdateLocalConditions
        publicIncrementalCheckerEngine update :=
  checkGenericIncrementalUpdate_complete_for_local_conditions
    publicIncrementalCheckerEngine update

example
    (success : GenericIncrementalCheckSuccess
      publicIncrementalCheckerEngine publicIncrementalNeuralUpdate) :
    success.checked.nextCertificate =
      assembleStateConstitution success.target.fragments := by
  rfl

example
    (success : GenericIncrementalCheckSuccess
      publicIncrementalCheckerEngine publicIncrementalNeuralUpdate)
    (accepted : checkGenericIncrementalUpdate publicIncrementalCheckerEngine
      publicIncrementalNeuralUpdate = .ok success) :
    success.checked.next.artifact = success.target.artifact ∧
      success.checked.next.state = success.target.state ∧
      success.checked.nextCertificate =
        assembleStateConstitution success.target.fragments ∧
      success.checked.transition = success.target.transition ∧
      success.checked.execution = success.target.execution :=
  checkGenericIncrementalUpdate_constitutively_sound
    publicIncrementalCheckerEngine publicIncrementalNeuralUpdate success
      accepted

example :
    publicIncrementalCheckedUpdate.transportedRequirement.payload =
      publicReusedRequirementFragment.payload :=
  publicIncrementalCheckedUpdate.transportedRequirementPayloadExact

example :
    publicIncrementalCheckedUpdate.targetCertificate =
      assembleIncrementalStateConstitution
        publicIncrementalCheckedUpdate.assembly := by
  rfl

example :
    publicIncrementalCheckedUpdate.targetCertificate =
      publicReferenceUpdatedStateCertificate :=
  publicIncrementalCheckedUpdate.targetCertificateExact

example :
    lookupStructuralObservation (.receivedInput 1)
        publicIncrementalTargetFragments.structural.observations =
      some publicIncrementalLicensedRequirementFragment.target.payload :=
  publicIncrementalTransportedRequirement_coherent

example :
    calculateIncrementalStructuralAssembly
        publicInitialStateConstitutiveCertificate
        publicPreCertificateConstitutiveGraph
        publicTransportedStructuralFragments
        publicRecomputedStructuralFragments =
      .ok publicIncrementalStructuralAssembly :=
  publicCalculatedIncrementalStructuralAssembly.calculated

example :
    calculateIncrementalStructuralAssembly
        publicInitialStateConstitutiveCertificate
        publicPreCertificateConstitutiveGraph []
        publicRecomputedStructuralFragments =
      .error (.missingTransported (.receivedInput 1)) := by
  rfl

example :
    calculateIncrementalStructuralAssembly
        publicInitialStateConstitutiveCertificate
        publicPreCertificateConstitutiveGraph
        publicTransportedStructuralFragments [] =
      .error (.missingRecomputed (.receivedInput 0)) := by
  rfl

example :
    publicIncrementalCertificateAssembly.fragments =
      publicIncrementalTargetFragments := by
  rfl

example :
    publicIncrementalCheckedUpdate.assembly =
      assemblePublicIncrementalCertificateFromPreCertificate
        publicIncrementalCheckedUpdate.preCertificateResult
        publicIncrementalCheckedUpdate.preCertificateResultExact :=
  publicIncrementalCheckedUpdate.assemblyCalculated

example : publicIncrementalCheckedUpdate.transportedCount = 1 := by
  rw [publicIncrementalCheckedUpdate.transportedCountExact,
    publicIncrementalCheckedUpdate.transportedFragmentsExact]
  exact publicTransportedStructuralFragmentCount_exact

example : publicIncrementalCheckedUpdate.recomputedCount = 6 := by
  rw [publicIncrementalCheckedUpdate.recomputedCountExact,
    publicIncrementalCheckedUpdate.recomputedFragmentsExact]
  exact publicRecomputedStructuralFragmentCount_exact

example :
    publicIncrementalCheckedUpdate.assembledStructuralFragments =
      structuralObservationSnapshot publicReferenceUpdatedStateCertificate :=
  publicIncrementalCheckedUpdate.assembledStructuralFragmentsExact

example :
    publicIncrementalCheckedUpdate.checked = publicReferenceCheckedUpdate := by
  calc
    publicIncrementalCheckedUpdate.checked =
        publicIncrementalCoreCheckedUpdate :=
      publicIncrementalCheckedUpdate.checkedExact
    _ = publicReferenceCheckedUpdate :=
      publicIncrementalCoreCheckedUpdate_eq_reference

example (update : IncrementalNeuralUpdate) :
    IncrementalUpdateAccepted update ↔
      ReferenceUpdateAccepted update.toFullReferenceUpdate :=
  incrementalAndReferenceAcceptance_equivalent update

example
    (update : IncrementalNeuralUpdate)
    (incremental : PublicIncrementalCheckedUpdate)
    (complete : CheckedUpdate publicInitialCheckedAgent .reconfigured)
    (incrementalAccepted :
      checkIncrementalUpdate update = .ok incremental)
    (completeAccepted :
      checkReferenceUpdate update.toFullReferenceUpdate = .ok complete) :
    incremental.checked = complete :=
  incrementalAndReferenceSuccessfulResults_exact update incremental complete
    incrementalAccepted completeAccepted

example :
    eraseIncrementalCheckResult
        (checkIncrementalUpdate publicIncrementalNeuralUpdate) =
      checkReferenceUpdate publicFullReferenceNeuralUpdate :=
  publicIncrementalAndReferenceChecks_exact

theorem public_incremental_and_reference_use_same_serialized_update :
    publicIncrementalNeuralUpdate = publicFullReferenceNeuralUpdate := by
  rfl

end ConstitutiveSearch.NeuralAgent.Tests
/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.NeuralAgent.checkIncrementalUpdate
#print axioms ConstitutiveSearch.NeuralAgent.publicIncrementalTargetAnalysisFromDecision_transition_exact
#print axioms ConstitutiveSearch.NeuralAgent.checkIncrementalUpdate_sound
#print axioms ConstitutiveSearch.NeuralAgent.checkGenericIncrementalUpdate
#print axioms ConstitutiveSearch.NeuralAgent.checkGenericIncrementalUpdate_sound
#print axioms ConstitutiveSearch.NeuralAgent.checkGenericIncrementalUpdate_constitutively_sound
#print axioms ConstitutiveSearch.NeuralAgent.checkGenericIncrementalUpdate_complete_for_local_conditions
#print axioms ConstitutiveSearch.NeuralAgent.incrementalAndReferenceAcceptance_equivalent
#print axioms ConstitutiveSearch.NeuralAgent.incrementalSuccess_matches_reference
#print axioms ConstitutiveSearch.NeuralAgent.incrementalAndReferenceSuccessfulResults_exact
#print axioms ConstitutiveSearch.NeuralAgent.publicIncrementalAndReferenceChecks_exact
#print axioms ConstitutiveSearch.NeuralAgent.Tests.public_incremental_and_reference_use_same_serialized_update
/- AXIOM_AUDIT_END -/
