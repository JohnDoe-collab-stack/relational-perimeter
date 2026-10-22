import RelationalPerimeter.Agents.Neural.CertifiedRuntimeAccessibility

/-! Regression checks for dependent checked traces and the closed runtime API. -/
namespace ConstitutiveSearch.NeuralAgent.Tests
open ConstitutiveSearch.NeuralAgent

example :
    checkUpdates publicDependentIncrementalChecker
        publicInitialCheckedAgent publicGenericSingletonProgram =
      .ok publicGenericSingletonResult :=
  checkUpdates_accepts_public_singleton

example :
    checkUpdates publicDependentIncrementalChecker
        publicInitialCheckedAgent publicGenericSingletonProgram =
      .ok publicGenericSingletonResult.executed.result :=
  checkUpdates_complete publicGenericSingletonResult.executed

example :
    EveryCheckedStepSatisfies
      publicGenericSingletonResult.executed.toTrace :=
  checkUpdates_sound publicGenericSingletonResult
    checkUpdates_accepts_public_singleton

example :
    EveryCheckedStepPreservesContracts
      publicGenericSingletonResult.executed.toTrace :=
  checkUpdates_preservesContracts publicGenericSingletonResult
    checkUpdates_accepts_public_singleton

example :
    submitUpdate publicInitialCertifiedRuntime
        (.reconfigure publicIncrementalNeuralUpdate) =
      .ok publicUpdatedCertifiedRuntime :=
  submitUpdate_public_result_exact

example :
    EveryRuntimeStepSatisfies
      publicUpdatedCertifiedRuntime.history :=
  publicUpdatedCertifiedRuntime.checkedHistory

example :
    EveryRuntimeStepPreservesContracts
      publicUpdatedCertifiedRuntime.history :=
  publicUpdatedCertifiedRuntime.preservedContracts

example :
    CertifiedRuntimeReachable publicDependentIncrementalChecker
      publicInitialCheckedAgent publicUpdatedCertifiedRuntime :=
  publicUpdatedCertifiedRuntime_reachable

example :
    CertifiedRuntimeAccessibility
      publicUpdatedCertifiedRuntime :=
  publicUpdatedCertifiedRuntime_accessibility

example :
    Exists fun result => checkPublicUpdates [] = .ok result :=
  checkPublicUpdates_accepts_empty

example :
    Exists fun result =>
      checkPublicUpdates [publicIncrementalNeuralUpdate] = .ok result :=
  checkPublicUpdates_accepts_singleton

example :
    checkPublicUpdates [publicIncrementalNeuralUpdate,
        publicIncrementalNeuralUpdate] =
      .error .noAdmittedTransition :=
  checkPublicUpdates_rejects_unadmitted_continuation

example :
    submitPublicUpdate initialPublicCertifiedRuntime publicIncrementalNeuralUpdate =
      .ok publicUpdatedPublicCertifiedRuntime :=
  submitPublicUpdate_result_exact

example :
    submitPublicUpdate publicUpdatedPublicCertifiedRuntime publicIncrementalNeuralUpdate =
      .error .noAdmittedTransition :=
  submitPublicUpdate_rejects_unadmitted_second_transition

example : EveryPublicCheckedStepSatisfies publicUpdatedPublicCertifiedRuntime.trace :=
  publicUpdatedPublicCertifiedRuntime.checkedTrace

example : PublicCertifiedRuntimeReachable publicUpdatedPublicCertifiedRuntime :=
  publicUpdatedPublicCertifiedRuntime_reachable

example : PublicCertifiedRuntimeAccessibility publicUpdatedPublicCertifiedRuntime :=
  publicUpdatedPublicCertifiedRuntime_accessibility

example :
    Not (Exists fun next =>
      submitPublicUpdate publicUpdatedPublicCertifiedRuntime
        publicIncrementalNeuralUpdate = .ok next) :=
  publicUpdatedPublicCertifiedRuntime_has_no_successor

end ConstitutiveSearch.NeuralAgent.Tests
/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.NeuralAgent.CheckedUpdateProgram
#print axioms ConstitutiveSearch.NeuralAgent.checkUpdates
#print axioms ConstitutiveSearch.NeuralAgent.checkUpdates_complete
#print axioms ConstitutiveSearch.NeuralAgent.checkUpdates_preservesContracts
#print axioms ConstitutiveSearch.NeuralAgent.submitUpdate
#print axioms ConstitutiveSearch.NeuralAgent.submitUpdate_rejected_cannot_install
#print axioms ConstitutiveSearch.NeuralAgent.CertifiedRuntime.preservedContracts
#print axioms ConstitutiveSearch.NeuralAgent.CheckedReconfigurationTrace
#print axioms ConstitutiveSearch.NeuralAgent.CertifiedRuntime
#print axioms ConstitutiveSearch.NeuralAgent.submitUpdate_public_result_exact
#print axioms ConstitutiveSearch.NeuralAgent.CertifiedRuntimeReachable
#print axioms ConstitutiveSearch.NeuralAgent.reachableRuntime_accessibility
#print axioms ConstitutiveSearch.NeuralAgent.PublicCertifiedRuntime
#print axioms ConstitutiveSearch.NeuralAgent.submitPublicUpdate
/- AXIOM_AUDIT_END -/
