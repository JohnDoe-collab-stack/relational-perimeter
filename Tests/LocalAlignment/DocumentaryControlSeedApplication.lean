import Tests.LocalAlignment.DocumentaryControlAssignmentApplication
import Tests.LocalAlignment.DocumentarySelection

/-! The concrete seed closes the assignment-reader interface with the same
constant assignment carried by the original entire Seed. Closure formation,
positive seed formation and reader formation are paid separately. -/
set_option genInjectivity false
set_option backward.match.sparseCases false
namespace ConstitutiveSearch.Agent.Local.Documentary.ControlSeedApplication
open SAT Selection Control ControlBindings ControlMasterData ControlAssignmentApplication

inductive Produced (selected : Var) (left right : Bool) where
  | blocked (impossible : (value : Bool) → (if value then right else left) = true → False)
      (actual : Seed.blocked impossible = seed selected left right)
  | viable (assignment : Assignment) (accepted : Satisfies assignment (choiceFormula selected left right))
      (reader : Reader assignment) (limited : reader.queryBound selected ≤ 1)
      (actual : Seed.viable assignment accepted = seed selected left right)

def code (selected : Var) (left right : Bool) : Code Label (Produced selected left right) :=
  .step .citationSeed (fun _ => match left, right with
    | false, false => .step .formationWitness (fun _ =>
        .done (.blocked (fun value accepted => by cases value <;> cases accepted) rfl))
    | false, true => .step .controlClosure (fun _ =>
        let assignment : Assignment := fun _ => true
        .step .formationWitness (fun _ =>
          let accepted : Satisfies assignment (choiceFormula selected false true) :=
            (choiceFormula_exact selected false true assignment).2 rfl
          (constantReaderCode true).bind (fun executable =>
            .done (.viable assignment accepted executable.1 (by rw [executable.2]; exact Nat.le_refl _) rfl))))
    | true, false => .step .controlClosure (fun _ =>
        let assignment : Assignment := fun _ => false
        .step .formationWitness (fun _ =>
          let accepted : Satisfies assignment (choiceFormula selected true false) :=
            (choiceFormula_exact selected true false assignment).2 rfl
          (constantReaderCode false).bind (fun executable =>
            .done (.viable assignment accepted executable.1 (by rw [executable.2]; exact Nat.le_refl _) rfl))))
    | true, true => .step .controlClosure (fun _ =>
        let assignment : Assignment := fun _ => false
        .step .formationWitness (fun _ =>
          let accepted : Satisfies assignment (choiceFormula selected true true) :=
            (choiceFormula_exact selected true true assignment).2 rfl
          (constantReaderCode false).bind (fun executable =>
            .done (.viable assignment accepted executable.1 (by rw [executable.2]; exact Nat.le_refl _) rfl)))))

theorem bounded (selected : Var) (left right : Bool) : Within (code selected left right) 6 := by
  apply within_step; cases left <;> cases right
  · apply within_weaken (bound := 1) (increase := by decide)
    exact within_step _ _ (within_done _)
  all_goals
    apply within_step; apply within_step
    apply within_bind (more := 0) (constant_reader_bounded _); intro executable
    exact within_done _

theorem finite (selected : Var) (left right : Bool) : Finite (code selected left right) := by
  obtain ⟨value, labels, trace, _⟩ := bounded selected left right
  exact ⟨value, labels, trace⟩

end ConstitutiveSearch.Agent.Local.Documentary.ControlSeedApplication

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlSeedApplication.Produced
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlSeedApplication.code
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlSeedApplication.bounded
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlSeedApplication.finite
/- AXIOM_AUDIT_END -/
