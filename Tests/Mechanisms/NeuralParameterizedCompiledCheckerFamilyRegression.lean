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
    scalingFinalNeuron prior .local ≠ scalingFinalNeuron prior .source := by
  intro same
  have inputsSame := congrArg (fun neuron => neuron.inputs) same
  simp only [scalingFinalNeuron] at inputsSame
  have tailSame := (List.cons.inj inputsSame).2
  have secondSame := (List.cons.inj tailSame).1
  have weightSame := congrArg (fun input => input.weight) secondSame
  exact (show (2 : Int) ≠ 1 by decide) weightSame

theorem profile_width_is_computed_by_the_checker :
    (scalingFamilyMetrics { size := 2, traceLength := 1 }).map
        (fun observations => observations.map (fun observation =>
          observation.metrics.profileWidth)) =
      .ok [6] := by
  rfl

/-- The generated family obeys the same non-circular completeness boundary as
the public and learned checkers: success is equivalent to autonomous local
receipts, not to an equation restating success of the whole analyzer. -/
theorem success_iff_autonomous_local_conditions
    (current : CheckedAgent scalingMetaContract ())
    (update : ScalingReceivedArtifact) :
    GenericIncrementalUpdateAccepted
        (scalingIncrementalCheckerEngine current) update ↔
      GenericIncrementalUpdateLocalConditions
        (scalingIncrementalCheckerEngine current) update :=
  analyzeScalingIncrementalUpdate_complete current update

end Tests.Mechanisms.NeuralParameterizedCompiledCheckerFamilyRegression
/- AXIOM_AUDIT_BEGIN -/
#print axioms Tests.Mechanisms.NeuralParameterizedCompiledCheckerFamilyRegression.generated_network_grows
#print axioms Tests.Mechanisms.NeuralParameterizedCompiledCheckerFamilyRegression.schedule_contains_local_and_upstream_changes
#print axioms Tests.Mechanisms.NeuralParameterizedCompiledCheckerFamilyRegression.local_change_preserves_the_upstream_neuron
#print axioms Tests.Mechanisms.NeuralParameterizedCompiledCheckerFamilyRegression.upstream_change_replaces_the_upstream_neuron
#print axioms Tests.Mechanisms.NeuralParameterizedCompiledCheckerFamilyRegression.local_change_replaces_the_terminal_neuron
#print axioms Tests.Mechanisms.NeuralParameterizedCompiledCheckerFamilyRegression.profile_width_is_computed_by_the_checker
#print axioms Tests.Mechanisms.NeuralParameterizedCompiledCheckerFamilyRegression.success_iff_autonomous_local_conditions
/- AXIOM_AUDIT_END -/
