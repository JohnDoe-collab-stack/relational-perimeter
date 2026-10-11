import Tests.LocalAlignment.DocumentaryControlConstitutiveGeneration

/-! Compute the free-generation allowance from the received boundary code.
This bootstrap walks only that code, never the controlled generator or its
result. Its own labelled cost has a separate structural bound. These local
bounds do not close the costs of the other master operations or the runner. -/
set_option genInjectivity false
set_option maxHeartbeats 8000000
namespace ConstitutiveSearch.Agent.Local.Documentary.ControlGenerationBudget
open StrongPerimetralTurning EndogenousDecomposition Control ControlBindings ControlMasterData
open ControlConstitutiveGeneration

def obstructionBoundCode {P : CircularPresentation} :
    {cursor : PerimeterCursor P} → (difference : BoundaryDifferenceCode P cursor) →
    Code Label (Actual (obstructionBound difference))
  | _, .initial _ => .step .controlInspect (fun _ => .done ⟨1, rfl⟩)
  | _, .afterFormation previous _ _ => .step .controlInspect (fun _ =>
      (obstructionBoundCode previous).bind (fun prior =>
        .step .formationValues (fun _ => .done ⟨prior.1 + 1, congrArg Nat.succ prior.2⟩)))

def bootstrapBound {P : CircularPresentation} :
    {cursor : PerimeterCursor P} → BoundaryDifferenceCode P cursor → Nat
  | _, .initial _ => 1
  | _, .afterFormation previous _ _ => (bootstrapBound previous + 1) + 1

theorem obstruction_bound_bounded {P : CircularPresentation} {cursor : PerimeterCursor P}
    (difference : BoundaryDifferenceCode P cursor) :
    Within (obstructionBoundCode difference) (bootstrapBound difference) := by
  induction difference with
  | initial obstruction => exact within_step _ _ (within_done _)
  | afterFormation previous term same ih =>
    apply within_step
    apply within_bind ih
    intro prior
    exact within_step _ _ (within_done _)

theorem canonical_bound_scalar {P : CircularPresentation} (source : PositiveConstitution P) :
    bound source + 1 = obstructionBound source.2.1.1 + 31 := by
  unfold bound layerBound
  rw [Nat.add_left_comm 9 (obstructionBound source.2.1.1) 4]

def canonicalBoundCode {P : CircularPresentation} (source : PositiveConstitution P) :
    Code Label (Actual (bound source + 1)) :=
  (obstructionBoundCode source.2.1.1).bind (fun obstruction =>
    (ControlArithmetic.addCode obstruction.1 31).bind (fun allowance =>
      .step .masterConstructionReturn (fun _ => .done
        ⟨allowance.1, allowance.2.trans
          ((congrArg (fun n => n + 31) obstruction.2).trans (canonical_bound_scalar source).symm)⟩)))

def canonicalBootstrapBound {P : CircularPresentation} (source : PositiveConstitution P) : Nat :=
  bootstrapBound source.2.1.1 + (ControlArithmetic.addBound 31 + 1)

theorem canonical_bound_bounded {P : CircularPresentation} (source : PositiveConstitution P) :
    Within (canonicalBoundCode source) (canonicalBootstrapBound source) := by
  apply within_bind (obstruction_bound_bounded source.2.1.1); intro obstruction
  apply within_bind (ControlArithmetic.add_bounded obstruction.1 31); intro allowance
  exact within_step _ _ (within_done _)

theorem computed_allowance_ready {depth : Nat}
    (source : PositiveConstitution Example.examplePresentation)
    (sourceExact : source = (constructStage depth).history.endpoint)
    (allowance : Actual (bound source + 1)) :
    ∃ (actual : Actual (generateCanonicalStageFromSource source sourceExact)) (labels : List Label),
      runCtl allowance.1 (canonicalCode source sourceExact) = some (actual, labels) := by
  rw [allowance.2]
  exact within_complete (canonical_bounded source sourceExact)

end ConstitutiveSearch.Agent.Local.Documentary.ControlGenerationBudget

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlGenerationBudget.obstructionBoundCode
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlGenerationBudget.bootstrapBound
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlGenerationBudget.obstruction_bound_bounded
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlGenerationBudget.canonical_bound_scalar
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlGenerationBudget.canonicalBoundCode
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlGenerationBudget.canonicalBootstrapBound
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlGenerationBudget.canonical_bound_bounded
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlGenerationBudget.computed_allowance_ready
/- AXIOM_AUDIT_END -/
