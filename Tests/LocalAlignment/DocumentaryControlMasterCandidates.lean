import Tests.LocalAlignment.DocumentaryControlMasterGeneration
import Tests.LocalAlignment.DocumentaryControlMeasuredDiscovery

/-! Candidate traversal consumes the paid attempt and its actual counters.
The retained candidates, produced endpoints and tested prefix are unchanged. -/
set_option genInjectivity false
set_option maxHeartbeats 5000000
namespace ConstitutiveSearch.Agent.Local.Documentary.ControlMasterCandidates
open SAT EndogenousDecomposition Control ControlBindings ControlMasterData
universe u

def lengthCode {α : Type u} (items : List α) : Code Label (Actual items.length) :=
  .step .masterExtractionCell (fun _ => match items with
    | [] => .done ⟨0, rfl⟩
    | _ :: rest => (lengthCode rest).bind (fun tail =>
      .step .masterExtractionReturn (fun _ => .done ⟨tail.1 + 1, congrArg Nat.succ tail.2⟩)))

theorem length_finite {α : Type u} (items : List α) : Finite (lengthCode items) := by
  induction items with
  | nil => exact finite_step _ _ (finite_done _)
  | cons head rest previous =>
    apply finite_step; apply finite_bind previous; intro tail
    exact finite_step _ _ (finite_done _)

def literalsCode (formula : Cnf) : Code Label (Actual formula.literalCount) :=
  .step .masterExtractionCell (fun _ => match formula with
    | [] => .done ⟨0, rfl⟩
    | clause :: rest => (lengthCode clause).bind (fun head =>
      (literalsCode rest).bind (fun tail =>
      (ControlArithmetic.addCode head.1 tail.1).bind (fun actual => .done
        ⟨actual.1, by
          obtain ⟨_, same⟩ := actual; cases same
          obtain ⟨_, same⟩ := tail; cases same
          obtain ⟨_, same⟩ := head; cases same; rfl⟩))))

theorem literals_finite (formula : Cnf) : Finite (literalsCode formula) := by
  induction formula with
  | nil => exact finite_step _ _ (finite_done _)
  | cons clause rest previous =>
    apply finite_step
    apply finite_bind (length_finite clause); intro head
    apply finite_bind previous; intro tail
    apply finite_bind
    · obtain ⟨value, labels, trace, _⟩ := ControlArithmetic.add_bounded head.1 tail.1
      exact ⟨value, labels, trace⟩
    · intro actual; exact finite_done _

def attemptWorkCode {root : Cnf} (state : GeneratedStructuralBranchContext root) :
    Code Label (Actual (candidateAttemptWork state)) :=
  (literalsCode state.context.formula).bind (fun formula =>
    (lengthCode state.context.decisions).bind (fun history =>
    .step .masterCandidateReturn (fun _ =>
      let visits := history.1 + 1
      (ControlArithmetic.addCode formula.1 visits).bind (fun total => .done
        ⟨⟨2, total.1, formula.1, visits, 1⟩, by
          obtain ⟨_, actual⟩ := total; cases actual
          obtain ⟨_, actual⟩ := history; cases actual
          obtain ⟨_, actual⟩ := formula; cases actual; rfl⟩))))

theorem attempt_work_finite {root : Cnf} (state : GeneratedStructuralBranchContext root) :
    Finite (attemptWorkCode state) := by
  apply finite_bind (literals_finite _); intro formula
  apply finite_bind (length_finite _); intro history
  apply finite_step
  apply finite_bind
  · obtain ⟨value, labels, trace, _⟩ := ControlArithmetic.add_bounded formula.1 (history.1 + 1)
    exact ⟨value, labels, trace⟩
  · intro total; exact finite_done _

def addCode (left right : Nat) := ControlArithmetic.addCode left right
theorem add_finite (left right : Nat) : Finite (addCode left right) := by
  obtain ⟨value, labels, trace, _⟩ := ControlArithmetic.add_bounded left right
  exact ⟨value, labels, trace⟩

def code {root : Cnf} (state : GeneratedStructuralBranchContext root) (candidates : List Var) :
    Code Label (Actual (exploreRecordedCandidates state candidates)) :=
  .step .masterCandidateCell (fun _ => match candidates with
    | [] => .step .masterCandidateReturn (fun _ => .done
      ⟨⟨none, [], 0, 0, 0, 0, 0, 0, .zero, .zero⟩, rfl⟩)
    | candidate :: rest => (attemptWorkCode state).bind (fun work =>
      .step .masterCandidateAttempt (fun _ =>
        (ControlMeasuredDiscovery.candidateCode state candidate).bind (fun actual =>
        let measured := actual.1
        match produced : measured.produced? with
        | some discovered => (workCode measured.freshnessWork measured.relationWork).bind (fun compared =>
          .step .masterCandidateReturn (fun _ => .done
            ⟨⟨some ⟨candidate, discovered⟩, [candidate], 1, work.1.candidateConstructions,
                work.1.variableComparisonUnits, work.1.formulaComparisonLiteralVisits,
                work.1.historyComparisonDecisionVisits, work.1.relationQueries, compared.1, measured.constructionWork⟩,
              by obtain ⟨_, actual⟩ := compared; cases actual
                 obtain ⟨_, actual⟩ := work; cases actual
                 obtain ⟨_, same⟩ := actual; cases same
                 rw [exploreRecordedCandidates, produced]⟩))
        | none => (code state rest).bind (fun tail =>
          (addCode tail.1.candidateConstructions work.1.candidateConstructions).bind (fun constructions =>
          (addCode tail.1.variableComparisonUnits work.1.variableComparisonUnits).bind (fun variables =>
          (addCode tail.1.formulaComparisonLiteralVisits work.1.formulaComparisonLiteralVisits).bind (fun formulas =>
          (addCode tail.1.historyComparisonDecisionVisits work.1.historyComparisonDecisionVisits).bind (fun histories =>
          (addCode tail.1.relationQueries work.1.relationQueries).bind (fun queries =>
          (workCode measured.freshnessWork measured.relationWork).bind (fun compared =>
          (workCode compared.1 tail.1.comparisonWork).bind (fun totalComparison =>
          (workCode measured.constructionWork tail.1.constructionWork).bind (fun totalConstruction =>
            .step .masterCandidateReturn (fun _ => .done
              ⟨⟨tail.1.produced?, candidate :: tail.1.testedCandidates, tail.1.attempts + 1,
                  constructions.1, variables.1, formulas.1, histories.1, queries.1,
                  totalComparison.1, totalConstruction.1⟩, by
                obtain ⟨_, actual⟩ := totalConstruction; cases actual
                obtain ⟨_, actual⟩ := totalComparison; cases actual
                obtain ⟨_, actual⟩ := compared; cases actual
                obtain ⟨_, actual⟩ := queries; cases actual
                obtain ⟨_, actual⟩ := histories; cases actual
                obtain ⟨_, actual⟩ := formulas; cases actual
                obtain ⟨_, actual⟩ := variables; cases actual
                obtain ⟨_, actual⟩ := constructions; cases actual
                obtain ⟨_, actual⟩ := tail; cases actual
                obtain ⟨_, actual⟩ := work; cases actual
                obtain ⟨_, same⟩ := actual; cases same
                rw [exploreRecordedCandidates, produced]⟩))))))))))))))

theorem finite {root : Cnf} (state : GeneratedStructuralBranchContext root) (candidates : List Var) :
    Finite (code state candidates) := by
  induction candidates with
  | nil => exact finite_step _ _ (finite_step _ _ (finite_done _))
  | cons candidate rest previous =>
    apply finite_step
    apply finite_bind (attempt_work_finite state); intro work
    apply finite_step
    apply finite_bind (ControlMeasuredDiscovery.candidate_finite _ _); intro actual
    dsimp only
    split
    · apply finite_bind (work_finite _ _); intro compared
      exact finite_step _ _ (finite_done _)
    · apply finite_bind previous; intro tail
      apply finite_bind (add_finite _ _); intro constructions
      apply finite_bind (add_finite _ _); intro variables
      apply finite_bind (add_finite _ _); intro formulas
      apply finite_bind (add_finite _ _); intro histories
      apply finite_bind (add_finite _ _); intro queries
      apply finite_bind (work_finite _ _); intro compared
      apply finite_bind (work_finite _ _); intro totalComparison
      apply finite_bind (work_finite _ _); intro totalConstruction
      exact finite_step _ _ (finite_done _)

end ConstitutiveSearch.Agent.Local.Documentary.ControlMasterCandidates

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMasterCandidates.lengthCode
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMasterCandidates.length_finite
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMasterCandidates.literalsCode
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMasterCandidates.literals_finite
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMasterCandidates.attemptWorkCode
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMasterCandidates.attempt_work_finite
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMasterCandidates.addCode
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMasterCandidates.add_finite
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMasterCandidates.code
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMasterCandidates.finite
/- AXIOM_AUDIT_END -/
