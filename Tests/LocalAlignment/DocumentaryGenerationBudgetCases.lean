import Tests.LocalAlignment.DocumentaryControlGenerationBudget
import Tests.LocalAlignment.DocumentaryControlRoleFormation

/-! Generic agreement and readiness of the opened generation component.
Readiness here is on the received positive source, not the whole documentary
fallback or a physical resource envelope. -/
set_option genInjectivity false
set_option maxHeartbeats 8000000
namespace ConstitutiveSearch.Agent.Local.Documentary.GenerationBudgetCases
open StrongPerimetralTurning EndogenousDecomposition Control ControlBindings ControlMasterData

def source (depth : Nat) : PositiveConstitution Example.examplePresentation :=
  (constructStage depth).history.endpoint

theorem bootstrap_then_generation (depth : Nat) :
    ∃ (allowance : Actual (ControlConstitutiveGeneration.bound (source depth) + 1)) (bootstrap : List Label),
      runCtl (ControlGenerationBudget.canonicalBootstrapBound (source depth))
        (ControlGenerationBudget.canonicalBoundCode (source depth)) = some (allowance, bootstrap) ∧
      ∃ (produced : Actual (generateCanonicalStageFromSource (source depth) rfl)) (labels : List Label),
        runCtl allowance.1 (ControlConstitutiveGeneration.canonicalCode (source depth) rfl) =
          some (produced, labels) := by
  obtain ⟨allowance, labels, actual⟩ :=
    within_complete (ControlGenerationBudget.canonical_bound_bounded (source depth))
  exact ⟨allowance, labels, actual, ControlGenerationBudget.computed_allowance_ready _ rfl allowance⟩

theorem whole_packet_actual {depth : Nat}
    (actual : Actual (generateCanonicalStageFromSource (source depth) rfl)) :
    actual.1 = generateCanonicalStageFromSource (source depth) rfl := actual.2

theorem generation_surplus_stable {depth fuel more produced labels}
    (actual : runCtl fuel (ControlConstitutiveGeneration.canonicalCode (source depth) rfl) =
      some (produced, labels)) (increase : fuel ≤ more) :
    runCtl more (ControlConstitutiveGeneration.canonicalCode (source depth) rfl) = some (produced, labels) :=
  ctl_mono fuel more actual increase

theorem generation_insufficient_fuel {depth labels produced}
    (trace : Eval (ControlConstitutiveGeneration.canonicalCode (source depth) rfl) labels produced)
    (fuel : Nat) (short : fuel < labels.length) :
    runCtl fuel (ControlConstitutiveGeneration.canonicalCode (source depth) rfl) = none :=
  fuel_short trace fuel short

theorem realized_occurrence_from_retained_endpoint {source : CausalConstitutiveState}
    {run : CausalConstitutiveStageExecution source} (role : RelationalConstitutiveRoleStage run)
    (position : OpeningRolePosition role) (state : SAT.GeneratedStructuralBranchContext source.rootFormula)
    (actual : state = position.state role) :
    (ControlRoleFormation.realizationFromState role position state actual).state = state := rfl

end ConstitutiveSearch.Agent.Local.Documentary.GenerationBudgetCases

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Agent.Local.Documentary.GenerationBudgetCases.source
#print axioms ConstitutiveSearch.Agent.Local.Documentary.GenerationBudgetCases.bootstrap_then_generation
#print axioms ConstitutiveSearch.Agent.Local.Documentary.GenerationBudgetCases.whole_packet_actual
#print axioms ConstitutiveSearch.Agent.Local.Documentary.GenerationBudgetCases.generation_surplus_stable
#print axioms ConstitutiveSearch.Agent.Local.Documentary.GenerationBudgetCases.generation_insufficient_fuel
#print axioms ConstitutiveSearch.Agent.Local.Documentary.GenerationBudgetCases.realized_occurrence_from_retained_endpoint
/- AXIOM_AUDIT_END -/
