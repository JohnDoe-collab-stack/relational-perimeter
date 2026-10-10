import Tests.LocalAlignment.DocumentaryControlMeasuredState

/-! One candidate's relation search consumes its actual generated endpoints.
Its full packet retains transformations, comparisons and the same witnesses. -/
set_option genInjectivity false
set_option maxHeartbeats 8000000
namespace ConstitutiveSearch.Agent.Local.Documentary.ControlMeasuredDiscovery
open SAT EndogenousDecomposition Control ControlBindings ControlMasterData

def relationCode {root : Cnf} (selected : Var) (source target : GeneratedStructuralBranchContext root) :
    Code Label (Actual (searchMeasuredRelation selected source target)) :=
  (ControlMeasuredTransformation.cnfCode selected source.context.formula).bind (fun flippedFormula =>
    (ControlMeasuredComparison.cnfCode target.context.formula flippedFormula.1.value).bind (fun formulas =>
      match found : formulas.1.result with
      | .isFalse _ => .step .masterCandidateReturn (fun _ => .done
        ⟨⟨none, flippedFormula.1.work, formulas.1.work, .zero, .zero⟩, by
          obtain ⟨_, actual⟩ := formulas; cases actual
          obtain ⟨_, actual⟩ := flippedFormula; cases actual
          rw [searchMeasuredRelation, found]⟩)
      | .isTrue sameFormula =>
        (ControlMeasuredTransformation.historyCode selected source.context.decisions).bind (fun flippedHistory =>
        (ControlMeasuredComparison.historyCode target.context.decisions flippedHistory.1.value).bind (fun histories =>
        .step .masterCandidateReturn (fun _ => match historyFound : histories.1.result with
          | .isFalse _ => .done
            ⟨⟨none, flippedFormula.1.work, formulas.1.work, flippedHistory.1.work, histories.1.work⟩, by
              obtain ⟨_, actual⟩ := histories; cases actual
              obtain ⟨_, actual⟩ := flippedHistory; cases actual
              obtain ⟨_, actual⟩ := formulas; cases actual
              obtain ⟨_, actual⟩ := flippedFormula; cases actual
              rw [searchMeasuredRelation, found]; dsimp only; rw [historyFound]⟩
          | .isTrue sameHistory => .done
            ⟨⟨some ⟨Eq.trans sameFormula flippedFormula.1.valueExact,
                Eq.trans sameHistory flippedHistory.1.valueExact⟩,
                flippedFormula.1.work, formulas.1.work, flippedHistory.1.work, histories.1.work⟩, by
              obtain ⟨_, actual⟩ := histories; cases actual
              obtain ⟨_, actual⟩ := flippedHistory; cases actual
              obtain ⟨_, actual⟩ := formulas; cases actual
              obtain ⟨_, actual⟩ := flippedFormula; cases actual
              rw [searchMeasuredRelation, found]; dsimp only; rw [historyFound]⟩)))))

theorem relation_finite {root : Cnf} (selected : Var) (source target : GeneratedStructuralBranchContext root) :
    Finite (relationCode selected source target) := by
  apply finite_bind (ControlMeasuredTransformation.cnf_finite _ _); intro flippedFormula
  apply finite_bind (ControlMeasuredComparison.cnf_finite _ _); intro formulas
  split
  · exact finite_step _ _ (finite_done _)
  · apply finite_bind (ControlMeasuredTransformation.history_finite _ _); intro flippedHistory
    apply finite_bind (ControlMeasuredComparison.history_finite _ _); intro histories
    apply finite_step; split <;> exact finite_done _

def fromDataCode {root : Cnf} (selected : Var) {source target : GeneratedStructuralBranchContext root}
    (left : MeasuredValue source) (right : MeasuredValue target) :
    Code Label (Actual (searchMeasuredRelationFromData selected left right)) :=
  (relationCode selected left.value right.value).bind (fun searched =>
    .step .masterCandidateReturn (fun _ =>
      let reindexedSource := Eq.rec
        (motive := fun source _ => MeasuredRelationRun selected source right.value) searched.1 left.valueExact
      let reindexed := Eq.rec (motive := fun target _ => MeasuredRelationRun selected source target)
        reindexedSource right.valueExact
      .done ⟨reindexed, by
        obtain ⟨_, actual⟩ := searched; cases actual
        cases left with
        | mk left actual leftWork =>
          cases actual
          cases right with
          | mk right actual rightWork => cases actual; rfl⟩))

theorem from_data_finite {root : Cnf} (selected : Var) {source target : GeneratedStructuralBranchContext root}
    (left : MeasuredValue source) (right : MeasuredValue target) : Finite (fromDataCode selected left right) := by
  apply finite_bind (relation_finite _ _ _); intro searched
  exact finite_step _ _ (finite_done _)

def relationWorkCode {root : Cnf} {selected : Var} {source target : GeneratedStructuralBranchContext root}
    (run : MeasuredRelationRun selected source target) : Code Label (Actual run.work) :=
  (workCode run.formulaTransform run.formulaComparison).bind (fun first =>
    (workCode first.1 run.historyTransform).bind (fun second =>
    (workCode second.1 run.historyComparison).bind (fun third => .done ⟨third.1, by
      obtain ⟨_, actual⟩ := third; cases actual
      obtain ⟨_, actual⟩ := second; cases actual
      obtain ⟨_, actual⟩ := first; cases actual; rfl⟩)))

theorem relation_work_finite {root : Cnf} {selected : Var} {source target : GeneratedStructuralBranchContext root}
    (run : MeasuredRelationRun selected source target) : Finite (relationWorkCode run) := by
  apply finite_bind (work_finite _ _); intro first
  apply finite_bind (work_finite _ _); intro second
  apply finite_bind (work_finite _ _); intro third; exact finite_done _

def candidateCode {root : Cnf} (state : GeneratedStructuralBranchContext root) (candidate : Var) :
    Code Label (Actual (tryMeasuredCandidate state candidate)) :=
  (ControlMeasuredTransformation.freshnessCode candidate state.context.decisions).bind (fun freshness =>
    match fresh : freshness.1.value with
    | false => .step .masterCandidateReturn (fun _ => .done
      ⟨⟨none, freshness.1.work, .zero, .zero⟩, by
        obtain ⟨_, actual⟩ := freshness; cases actual
        rw [tryMeasuredCandidate]; split
        · rfl
        · rename_i hit; cases (fresh.symm.trans hit : false = true)⟩)
    | true =>
      let checked := EndogenousDecomposition.structuralDecisionsAvoid_of_check_true candidate state.context.decisions
        (Eq.trans freshness.1.valueExact.symm fresh)
      (ControlMeasuredState.childCode state candidate false checked).bind (fun left =>
      (ControlMeasuredState.childCode state candidate true checked).bind (fun right =>
      (fromDataCode candidate left.1 right.1).bind (fun searched =>
      (workCode left.1.work right.1.work).bind (fun constructed =>
      (relationWorkCode searched.1).bind (fun relationWork =>
      .step .masterCandidateReturn (fun _ => match found : searched.1.result with
        | none => .done ⟨⟨none, freshness.1.work, constructed.1, relationWork.1⟩, by
            obtain ⟨_, actual⟩ := relationWork; cases actual
            obtain ⟨_, actual⟩ := constructed; cases actual
            obtain ⟨_, actual⟩ := searched; cases actual
            obtain ⟨_, actual⟩ := right; cases actual
            obtain ⟨_, actual⟩ := left; cases actual
            obtain ⟨_, actual⟩ := freshness; cases actual
            rw [tryMeasuredCandidate]; split
            · rename_i hit; cases (fresh.symm.trans hit : true = false)
            · dsimp only; rw [found]⟩
        | some relation => .done
          ⟨⟨some ⟨⟨checked, relation⟩, left.1, right.1⟩, freshness.1.work, constructed.1, relationWork.1⟩, by
            obtain ⟨_, actual⟩ := relationWork; cases actual
            obtain ⟨_, actual⟩ := constructed; cases actual
            obtain ⟨_, actual⟩ := searched; cases actual
            obtain ⟨_, actual⟩ := right; cases actual
            obtain ⟨_, actual⟩ := left; cases actual
            obtain ⟨_, actual⟩ := freshness; cases actual
            rw [tryMeasuredCandidate]; split
            · rename_i hit; cases (fresh.symm.trans hit : true = false)
            · dsimp only; rw [found]⟩)))))))

theorem candidate_finite {root : Cnf} (state : GeneratedStructuralBranchContext root) (candidate : Var) :
    Finite (candidateCode state candidate) := by
  apply finite_bind (ControlMeasuredTransformation.freshness_finite _ _); intro freshness
  split
  · exact finite_step _ _ (finite_done _)
  · apply finite_bind (ControlMeasuredState.child_finite _ _ _ _); intro left
    apply finite_bind (ControlMeasuredState.child_finite _ _ _ _); intro right
    apply finite_bind (from_data_finite _ _ _); intro searched
    apply finite_bind (work_finite _ _); intro constructed
    apply finite_bind (relation_work_finite _); intro relationWork
    apply finite_step; split <;> exact finite_done _

end ConstitutiveSearch.Agent.Local.Documentary.ControlMeasuredDiscovery

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMeasuredDiscovery.relationCode
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMeasuredDiscovery.relation_finite
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMeasuredDiscovery.fromDataCode
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMeasuredDiscovery.from_data_finite
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMeasuredDiscovery.relationWorkCode
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMeasuredDiscovery.relation_work_finite
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMeasuredDiscovery.candidateCode
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMeasuredDiscovery.candidate_finite
/- AXIOM_AUDIT_END -/
