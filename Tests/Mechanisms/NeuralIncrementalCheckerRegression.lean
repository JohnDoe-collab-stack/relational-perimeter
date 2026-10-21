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
    publicIncrementalCheckedUpdate.transportedRequirement =
      publicReusedRequirementFragment :=
  publicIncrementalCheckedUpdate.transportedRequirementExact

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

example :
    eraseIncrementalCheckResult
        (checkIncrementalUpdate publicIncrementalNeuralUpdate) =
      checkReferenceUpdate publicFullReferenceNeuralUpdate :=
  publicIncrementalAndReferenceChecks_exact

end ConstitutiveSearch.NeuralAgent.Tests
/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.NeuralAgent.checkIncrementalUpdate
#print axioms ConstitutiveSearch.NeuralAgent.checkIncrementalUpdate_sound
#print axioms ConstitutiveSearch.NeuralAgent.incrementalAndReferenceAcceptance_equivalent
#print axioms ConstitutiveSearch.NeuralAgent.incrementalSuccess_matches_reference
#print axioms ConstitutiveSearch.NeuralAgent.publicIncrementalAndReferenceChecks_exact
/- AXIOM_AUDIT_END -/
