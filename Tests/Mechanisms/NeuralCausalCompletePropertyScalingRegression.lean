import RelationalPerimeter.Agents.Neural.CausalCompletePropertyScalingMeasurement

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

/-!
# Regression checks for the causal scaling family

These checks pin the exact source/action/effect/successor chain, agreement of
the independent full recheck, fragment accounting, and successive consumption
of the installed successor.  They are not confirmatory performance results.
-/
namespace Tests.Mechanisms.NeuralCausalCompletePropertyScalingRegression
open ConstitutiveSearch.NeuralAgent

theorem action_reads_exact_source
    (source : ReconfiguredExecutionState publicRequirementFamily)
    (size : Nat) (version : ScalingArtifactVersion) :
    (causalScalingActionState source size version).memory = source.memory :=
  causalScalingAction_reads_exact_source source size version

theorem action_effectively_advances_the_source
    (source : ReconfiguredExecutionState publicRequirementFamily)
    (size : Nat) (version : ScalingArtifactVersion) :
    (causalScalingAction source size version).result.1.register.length =
      source.memory.register.length + 1 :=
  causalScalingAction_register_progress source size version

theorem effect_consumes_exact_action
    (source : ReconfiguredExecutionState publicRequirementFamily)
    (size : Nat) (version : ScalingArtifactVersion) :
    (causalScalingEffect source size version).action =
      causalScalingAction source size version :=
  causalScalingEffect_consumes_produced_action source size version

theorem successor_consumes_exact_effect
    (source : ReconfiguredExecutionState publicRequirementFamily)
    (size : Nat) (version : ScalingArtifactVersion) :
    (causalScalingTargetState source size version).memory =
      (causalScalingEffect source size version).successor :=
  causalScalingTarget_consumes_produced_effect source size version

theorem paired_step_accepts_the_produced_successor :
    ∃ result,
      checkCausalScalingStep (causalScalingInitialAgent 2)
        { size := 2, version := .local } = .ok result := by
  exact ⟨_, rfl⟩

theorem paired_paths_install_the_same_successor
    (result : CausalScalingPairedStepResult (causalScalingInitialAgent 2)
      { size := 2, version := .local }) :
    result.incremental.checked.next.state = result.full.checked.next.state :=
  result.sameTarget

theorem checked_trace_has_the_requested_length
    (parameters : ScalingFamilyParameters)
    (result : CausalScalingTraceResult parameters) :
    result.observations.length = parameters.traceLength :=
  result.lengthExact

theorem causal_cost_counts_the_real_assembly
    {current : CheckedAgent causalScalingMetaContract ()}
    {update : CausalScalingReceivedArtifact}
    (analysis : CausalScalingIncrementalAnalysis current update) :
    (causalScalingCompleteCost 4 7 analysis).assemblyUnits =
      (causalScalingIncrementalTransportLicenses current analysis.target).length +
        (causalScalingIncrementalRecomputed current analysis.target).length :=
  causalScalingCompleteCost_assembly_exact 4 7 analysis

end Tests.Mechanisms.NeuralCausalCompletePropertyScalingRegression
/- AXIOM_AUDIT_BEGIN -/
#print axioms Tests.Mechanisms.NeuralCausalCompletePropertyScalingRegression.action_reads_exact_source
#print axioms Tests.Mechanisms.NeuralCausalCompletePropertyScalingRegression.action_effectively_advances_the_source
#print axioms Tests.Mechanisms.NeuralCausalCompletePropertyScalingRegression.effect_consumes_exact_action
#print axioms Tests.Mechanisms.NeuralCausalCompletePropertyScalingRegression.successor_consumes_exact_effect
#print axioms Tests.Mechanisms.NeuralCausalCompletePropertyScalingRegression.paired_step_accepts_the_produced_successor
#print axioms Tests.Mechanisms.NeuralCausalCompletePropertyScalingRegression.paired_paths_install_the_same_successor
#print axioms Tests.Mechanisms.NeuralCausalCompletePropertyScalingRegression.checked_trace_has_the_requested_length
#print axioms Tests.Mechanisms.NeuralCausalCompletePropertyScalingRegression.causal_cost_counts_the_real_assembly
/- AXIOM_AUDIT_END -/
