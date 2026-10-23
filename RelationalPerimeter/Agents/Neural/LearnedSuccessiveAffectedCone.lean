import RelationalPerimeter.Agents.Neural.LearnedFutureConstitutiveClosure

/-!
# Successive learned affected cone material

This module fixes the exact pre-certificate graph and the two structural
supplies consumed by the successive incremental assembly.
-/
namespace ConstitutiveSearch.NeuralAgent

def learnedSuccessivePreCertificateGraph : PreCertificateConstitutiveGraph
    LearnedAlignedCheckedAgent.certificate.basis.naming
      learnedExtendedStableNaming :=
  calculatePreCertificateConstitutiveGraph
    LearnedAlignedCheckedAgent.certificate.basis.naming
    learnedExtendedStableNaming

/-- Exact source occurrences licensed outside the successive cone. -/
def learnedSuccessiveLicensedStructuralTransports :
    List (LicensedStructuralTransport
      LearnedAlignedCheckedAgent.certificate
      learnedSuccessivePreCertificateGraph) :=
  calculateLicensedStructuralTransports
    LearnedAlignedCheckedAgent.certificate
    learnedSuccessivePreCertificateGraph

/-- Exact source-certificate payloads projected from those licenses. -/
def learnedSuccessiveTransportedStructuralFragments :
    List (StableNodeKey × StableArtifactObservation) :=
  licensedStructuralEntries learnedSuccessiveLicensedStructuralTransports

/-- Exact target payloads recalculated directly at the changed final neuron
and at the conservatively invalidated output representation boundary.  No
complete target snapshot is constructed and sliced on this path. -/
def learnedSuccessiveRecomputedStructuralFragments :
    List (StableNodeKey × StableArtifactObservation) :=
  recomputeAffectedStructuralObservations
    LearnedAlignedCheckedAgent.certificate learnedExtendedStableNaming
    learnedSuccessivePreCertificateGraph

end ConstitutiveSearch.NeuralAgent
/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.NeuralAgent.learnedSuccessivePreCertificateGraph
#print axioms ConstitutiveSearch.NeuralAgent.learnedSuccessiveLicensedStructuralTransports
#print axioms ConstitutiveSearch.NeuralAgent.learnedSuccessiveTransportedStructuralFragments
#print axioms ConstitutiveSearch.NeuralAgent.learnedSuccessiveRecomputedStructuralFragments
/- AXIOM_AUDIT_END -/
