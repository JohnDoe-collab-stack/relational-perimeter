import RelationalPerimeter.Agents.Neural.CheckedState

/-! Regression checks for state-indexed certificates and checked states. -/
namespace ConstitutiveSearch.NeuralAgent.Tests
open ConstitutiveSearch.NeuralAgent

example :
    publicInitialCheckedAgent.state.system =
      publicInitialCheckedAgent.artifact.system :=
  publicInitialCheckedAgent_system_exact

example : Nonempty (Listed publicInitialCheckedAgent.state.input
    publicInitialCheckedAgent.certificate.basis.currentInputs) :=
  publicInitialCheckedAgent_input_decided

example : CausalCandidateCoverage publicDecodedRequirementArtifact
    publicInitialCheckedAgent.certificate.basis.naming
    publicInitialCheckedAgent.certificate.basis.replacements
    publicInitialCheckedAgent.state.input :=
  publicInitialCheckedAgent.certificate.causalCoverage

example (requests : List (ULift.{3} Agent.Request)) :
    PublicInitialOperationalContract.futureContract.outcome
        (PublicInitialOperationalContract.futureSourceOfState
          publicInitialCheckedAgent.state) requests =
      publicInitialCheckedAgent.certificate.futureRealization.reducedContract.outcome
        (publicInitialCheckedAgent.certificate.futureRealization.project
          (PublicInitialOperationalContract.futureSourceOfState
            publicInitialCheckedAgent.state)) requests :=
  publicInitialCheckedAgent.certificate.everyFiniteFuture requests

#check certifyCheckedUpdate

end ConstitutiveSearch.NeuralAgent.Tests
/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.NeuralAgent.publicInitialCheckedAgent
#print axioms ConstitutiveSearch.NeuralAgent.publicInitialCheckedAgent_system_exact
#print axioms ConstitutiveSearch.NeuralAgent.publicInitialCheckedAgent_input_decided
#print axioms ConstitutiveSearch.NeuralAgent.StateConstitutiveCertificate.causalCoverage
#print axioms ConstitutiveSearch.NeuralAgent.StateConstitutiveCertificate.everyFiniteFuture
#print axioms ConstitutiveSearch.NeuralAgent.certifyCheckedUpdate
/- AXIOM_AUDIT_END -/
