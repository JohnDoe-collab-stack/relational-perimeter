import RelationalPerimeter.Agents.Neural.ParameterizedCompiledCheckerFamily

/-!
# Regression checks for the parameterized compiled checker family

These checks pin the growing artifact family and its paired incremental/full
checker execution.  They are compile-time regressions, not confirmatory cost
measurements.
-/
namespace Tests.Mechanisms.NeuralParameterizedCompiledCheckerFamilyRegression
open ConstitutiveSearch.NeuralAgent

theorem generated_network_grows :
    (scalingSystem 0 .source).producedCount = 2 /\
      (scalingSystem 3 .source).producedCount = 5 := by
  exact ⟨rfl, rfl⟩

theorem schedule_contains_local_and_upstream_changes :
    scalingVersionAt 0 = .local /\
      scalingVersionAt 1 = .source /\
      scalingVersionAt 2 = .extended := by
  exact ⟨rfl, rfl, rfl⟩

theorem local_change_preserves_the_upstream_neuron :
    scalingBaseNeuron .local = scalingBaseNeuron .source := by
  rfl

theorem upstream_change_replaces_the_upstream_neuron :
    scalingBaseNeuron .extended ≠ scalingBaseNeuron .source := by
  intro same
  have thresholdSame := congrArg (fun neuron => neuron.threshold.level) same
  exact (show (5 : Int) ≠ 3 by decide) thresholdSame

theorem local_change_replaces_the_terminal_neuron (prior : Nat) :
    scalingLocalTailNeuron prior ≠ scalingTailNeuron prior := by
  intro same
  have thresholdSame := congrArg (fun neuron => neuron.threshold.level) same
  exact (show (2 : Int) ≠ 1 by decide) thresholdSame

theorem profile_width_is_computed_by_the_checker :
    (scalingFamilyMetrics { size := 2, traceLength := 1 }).map
        (fun observations => observations.map (fun observation =>
          observation.metrics.profileWidth)) =
      .ok [6] := by
  rfl

end Tests.Mechanisms.NeuralParameterizedCompiledCheckerFamilyRegression
/- AXIOM_AUDIT_BEGIN -/
#print axioms Tests.Mechanisms.NeuralParameterizedCompiledCheckerFamilyRegression.generated_network_grows
#print axioms Tests.Mechanisms.NeuralParameterizedCompiledCheckerFamilyRegression.schedule_contains_local_and_upstream_changes
#print axioms Tests.Mechanisms.NeuralParameterizedCompiledCheckerFamilyRegression.local_change_preserves_the_upstream_neuron
#print axioms Tests.Mechanisms.NeuralParameterizedCompiledCheckerFamilyRegression.upstream_change_replaces_the_upstream_neuron
#print axioms Tests.Mechanisms.NeuralParameterizedCompiledCheckerFamilyRegression.local_change_replaces_the_terminal_neuron
#print axioms Tests.Mechanisms.NeuralParameterizedCompiledCheckerFamilyRegression.profile_width_is_computed_by_the_checker
/- AXIOM_AUDIT_END -/
