import RelationalPerimeter.Agents.Neural.AutonomousCheckerClosure
import RelationalPerimeter.Agents.Neural.ParameterizedCompiledCheckerFamily

/-!
Regression floor for L6: exact heterogeneous dependencies, source-derived
transport, assembly consumption, independent full-reference agreement, and
successive checked updates.
-/
namespace ConstitutiveSearch.NeuralAgent.Tests
open ConstitutiveSearch.NeuralAgent

def learnedInstalledHeterogeneousChain :
    InstalledHeterogeneousCausalChain
      learnedAlignedGenericIncrementalSuccess.checked.next.certificate :=
  installedHeterogeneousCausalChain
    learnedAlignedGenericIncrementalSuccess.checked.next.certificate

theorem learned_local_installed_certificate_consumes_assembly :
    (learnedAlignedGenericIncrementalSuccess.checked.next.certificate
        ).structuralObservations =
      learnedCalculatedStructuralAssembly.observations :=
  learnedAlignedInstalledStructuralAssembly_exact

theorem learned_local_transport_is_nonempty :
    learnedTransportedStructuralFragments.length = 3 := by
  rfl

theorem learned_local_transport_has_three_source_licenses :
    learnedLicensedStructuralTransports.length = 3 := by
  rfl

theorem learned_local_transport_is_projection_of_licenses :
    learnedTransportedStructuralFragments =
      licensedStructuralEntries learnedLicensedStructuralTransports := by
  rfl

theorem learned_local_transport_comes_from_checked_source :
    learnedTransportedStructuralFragments =
      (structuralObservationSnapshot
        learnedInitialCheckedAgent.certificate).take 3 := by
  rfl

theorem learned_full_recalculation_installed_certificate_consumes_assembly :
    (learnedRenamedGenericIncrementalSuccess.checked.next.certificate
        ).structuralObservations =
      learnedRenamedCalculatedStructuralAssembly.observations :=
  learnedRenamedInstalledStructuralAssembly_exact

theorem learned_full_recalculation_transports_nothing :
    learnedRenamedTransportedStructuralFragments = [] := by
  rfl

theorem learned_full_recalculation_covers_target :
    learnedRenamedRecomputedStructuralFragments =
      learnedRenamedPreCertificateGraph.targetObservations := by
  rfl

theorem learned_local_acceptance_matches_independent_reference :
    GenericIncrementalUpdateAccepted learnedIncrementalCheckerEngine
        learnedAlignedSerializedUpdate ↔
      LearnedFullUpdateAccepted learnedAlignedSerializedUpdate :=
  learnedAlignedIncrementalAndFullAcceptance_equivalent

theorem learned_local_successor_matches_independent_reference :
    learnedAlignedGenericIncrementalSuccess.checked.next =
      learnedAlignedFullRecheckSuccess.checked.next :=
  learnedAlignedIncrementalAndFullSuccessor_exact

theorem learned_full_recalculation_successor_matches_independent_reference :
    learnedRenamedGenericIncrementalSuccess.checked.next =
      learnedRenamedFullRecheckSuccess.checked.next :=
  learnedRenamedIncrementalAndFullSuccessor_exact

theorem learned_successive_transport_comes_from_checked_predecessor :
    learnedSuccessiveTransportedStructuralFragments =
      let source :=
        structuralObservationSnapshot LearnedAlignedCheckedAgent.certificate
      source.take 10 :=
  learnedSuccessiveTransport_reads_checked_source

theorem learned_successive_transport_is_nonempty :
    learnedSuccessiveTransportedStructuralFragments.length = 10 := by
  rfl

theorem learned_successive_transport_has_ten_source_licenses :
    learnedSuccessiveLicensedStructuralTransports.length = 10 := by
  rfl

theorem learned_successive_installed_certificate_consumes_assembly :
    (learnedSuccessiveIncrementalSuccess.checked.next.certificate
        ).structuralObservations =
      learnedSuccessiveCalculatedStructuralAssembly.observations :=
  learnedSuccessiveInstalledStructuralAssembly_exact

theorem learned_successive_acceptance_matches_independent_reference :
    GenericIncrementalUpdateAccepted learnedSuccessiveIncrementalCheckerEngine
        learnedExtendedSerializedUpdate ↔
      FullRecheckAccepted learnedSuccessiveFullRecheckEngine
        learnedExtendedSerializedUpdate :=
  learnedSuccessiveIncrementalAndFullAcceptance_equivalent

theorem learned_successive_successor_matches_independent_reference :
    learnedSuccessiveIncrementalSuccess.checked.next =
      learnedSuccessiveFullRecheckSuccess.checked.next :=
  learnedSuccessiveIncrementalAndFullSuccessor_exact

end ConstitutiveSearch.NeuralAgent.Tests
/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.NeuralAgent.Tests.learnedInstalledHeterogeneousChain
#print axioms ConstitutiveSearch.NeuralAgent.Tests.learned_local_installed_certificate_consumes_assembly
#print axioms ConstitutiveSearch.NeuralAgent.Tests.learned_local_transport_is_nonempty
#print axioms ConstitutiveSearch.NeuralAgent.Tests.learned_local_transport_has_three_source_licenses
#print axioms ConstitutiveSearch.NeuralAgent.Tests.learned_local_transport_is_projection_of_licenses
#print axioms ConstitutiveSearch.NeuralAgent.Tests.learned_local_transport_comes_from_checked_source
#print axioms ConstitutiveSearch.NeuralAgent.Tests.learned_full_recalculation_installed_certificate_consumes_assembly
#print axioms ConstitutiveSearch.NeuralAgent.Tests.learned_full_recalculation_transports_nothing
#print axioms ConstitutiveSearch.NeuralAgent.Tests.learned_full_recalculation_covers_target
#print axioms ConstitutiveSearch.NeuralAgent.Tests.learned_local_acceptance_matches_independent_reference
#print axioms ConstitutiveSearch.NeuralAgent.Tests.learned_local_successor_matches_independent_reference
#print axioms ConstitutiveSearch.NeuralAgent.Tests.learned_full_recalculation_successor_matches_independent_reference
#print axioms ConstitutiveSearch.NeuralAgent.Tests.learned_successive_transport_comes_from_checked_predecessor
#print axioms ConstitutiveSearch.NeuralAgent.Tests.learned_successive_transport_is_nonempty
#print axioms ConstitutiveSearch.NeuralAgent.Tests.learned_successive_transport_has_ten_source_licenses
#print axioms ConstitutiveSearch.NeuralAgent.Tests.learned_successive_installed_certificate_consumes_assembly
#print axioms ConstitutiveSearch.NeuralAgent.Tests.learned_successive_acceptance_matches_independent_reference
#print axioms ConstitutiveSearch.NeuralAgent.Tests.learned_successive_successor_matches_independent_reference
/- AXIOM_AUDIT_END -/
