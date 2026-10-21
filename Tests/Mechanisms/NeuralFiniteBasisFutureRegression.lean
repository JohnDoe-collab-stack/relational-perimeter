import RelationalPerimeter.Agents.Neural.CoveredFutureRealization

namespace Tests.Mechanisms.NeuralFiniteBasisFutureRegression
open ConstitutiveSearch ConstitutiveSearch.NeuralAgent

def finiteBasis : FiniteCausalBasis
    PublicInitialOperationalContract publicDecodedRequirementArtifact :=
  publicFiniteCausalBasis

def firstInputCoverage : CausalCandidateCoverage
    publicDecodedRequirementArtifact publicInitialStableNaming
      publicCausalReplacements
      publicFirstDeclaredInput :=
  publicFiniteCausalBasis.replacementCoverage publicFirstDeclaredInput .head

theorem firstInputDecision_returns_positive_witness :
    Nonempty (Listed publicFirstDeclaredInput finiteBasis.currentInputs) :=
  publicFirstDeclaredInput_is_decided

theorem replacementDecision_returns_positive_witness :
    Nonempty (Listed (3 : NativeMechanism.Activation)
      (finiteBasis.replacements
        (.receivedInput publicRequirementPort))) :=
  publicInputReplacement_is_decided

def exactCoveredFutures :
    CoveredFutureRealization PublicReconfiguredOperationalContract :=
  publicCoveredFutureRealization

theorem everyFiniteRequestList_is_preserved
    (source : ReconfiguredExecutionState publicRequirementFamily)
    (requests : List (ULift.{3} Agent.Request)) :
    PublicReconfiguredOperationalContract.futureContract.outcome source
        requests =
      reconfiguredOperationalMemoryFutureContract.outcome source.memory
        requests :=
  publicOperationalContract_preserves_every_finite_future source requests

end Tests.Mechanisms.NeuralFiniteBasisFutureRegression
/- AXIOM_AUDIT_BEGIN -/
#print axioms Tests.Mechanisms.NeuralFiniteBasisFutureRegression.finiteBasis
#print axioms Tests.Mechanisms.NeuralFiniteBasisFutureRegression.firstInputCoverage
#print axioms Tests.Mechanisms.NeuralFiniteBasisFutureRegression.firstInputDecision_returns_positive_witness
#print axioms Tests.Mechanisms.NeuralFiniteBasisFutureRegression.replacementDecision_returns_positive_witness
#print axioms Tests.Mechanisms.NeuralFiniteBasisFutureRegression.exactCoveredFutures
#print axioms Tests.Mechanisms.NeuralFiniteBasisFutureRegression.everyFiniteRequestList_is_preserved
/- AXIOM_AUDIT_END -/
