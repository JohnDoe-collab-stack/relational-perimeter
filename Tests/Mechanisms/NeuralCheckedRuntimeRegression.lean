import RelationalPerimeter.Agents.Neural.CertifiedRuntimeAccessibility

/-! Regression checks for dependent checked traces and the closed runtime API. -/
namespace ConstitutiveSearch.NeuralAgent.Tests
open ConstitutiveSearch.NeuralAgent

example :
    Exists fun result => checkUpdates [] = .ok result :=
  checkUpdates_accepts_empty

example :
    Exists fun result =>
      checkUpdates [publicIncrementalNeuralUpdate] = .ok result :=
  checkUpdates_accepts_public_singleton

example :
    checkUpdates [publicIncrementalNeuralUpdate,
        publicIncrementalNeuralUpdate] =
      .error .noAdmittedTransition :=
  checkUpdates_rejects_unadmitted_continuation

example :
    submitUpdate initialCertifiedRuntime publicIncrementalNeuralUpdate =
      .ok publicUpdatedCertifiedRuntime :=
  submitUpdate_public_result_exact

example :
    submitUpdate publicUpdatedCertifiedRuntime publicIncrementalNeuralUpdate =
      .error .noAdmittedTransition :=
  submitUpdate_rejects_unadmitted_second_transition

example : EveryCheckedStepSatisfies publicUpdatedCertifiedRuntime.trace :=
  publicUpdatedCertifiedRuntime.checkedTrace

example : CertifiedRuntimeReachable publicUpdatedCertifiedRuntime :=
  publicUpdatedCertifiedRuntime_reachable

example : CertifiedRuntimeAccessibility publicUpdatedCertifiedRuntime :=
  publicUpdatedCertifiedRuntime_accessibility

example :
    Not (Exists fun next =>
      submitUpdate publicUpdatedCertifiedRuntime
        publicIncrementalNeuralUpdate = .ok next) :=
  publicUpdatedCertifiedRuntime_has_no_successor

end ConstitutiveSearch.NeuralAgent.Tests
/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.NeuralAgent.CheckedReconfigurationTrace
#print axioms ConstitutiveSearch.NeuralAgent.checkUpdates
#print axioms ConstitutiveSearch.NeuralAgent.CertifiedRuntime
#print axioms ConstitutiveSearch.NeuralAgent.submitUpdate
#print axioms ConstitutiveSearch.NeuralAgent.submitUpdate_public_result_exact
#print axioms ConstitutiveSearch.NeuralAgent.CertifiedRuntimeReachable
#print axioms ConstitutiveSearch.NeuralAgent.reachableRuntime_accessibility
/- AXIOM_AUDIT_END -/
