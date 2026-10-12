import Tests.LocalAlignment.DocumentaryControlFrontierApplicationComposition

/-! Applications of the actual exact split retain the real produced children.
The selected bit is obtained from the paid reader. Merge retains that same
assignment and drops only the newest structural decision proof. -/
set_option genInjectivity false
set_option backward.match.sparseCases false
set_option maxHeartbeats 10000000
namespace ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierApplication
open SAT Selection Control ControlBindings ControlMasterData ControlAssignmentApplication

def expandForward {formula : Cnf} (selected : Var) (parent : GeneratedStructuralBranchContext formula)
    (fresh : StructuralDecisionsAvoid selected parent.context.decisions)
    (left : Actual (parent.child selected false fresh)) (right : Actual (parent.child selected true fresh))
    (splitter : ControlFrontierOpening.Split parent selected fresh left right)
    {rest : List (GeneratedStructuralBranchContext formula)}
    (actual : Actual (AcceptedFrontierPreservation.expandHead (rest := rest) splitter.1))
    (input : FrontierContinuation (generatedStructuralBranchSystem formula) (parent :: rest))
    (budget : Nat) (reader : Reader (frontierAssignment (formula := formula) (frontier := parent :: rest) input))
    (limited : reader.queryBound selected ≤ budget) :
    Code Label (Applied (formula := formula) (frontier := left.1 :: right.1 :: rest) selected (actual.1.forward.map input) budget) :=
  .step .transportApplicationCell (fun _ => (match (motive :=
      (input : FrontierContinuation (generatedStructuralBranchSystem formula) (parent :: rest)) →
      (reader : Reader (frontierAssignment (formula := formula) (frontier := parent :: rest) input)) →
      reader.queryBound selected ≤ budget → Code Label (Applied (formula := formula) (frontier := left.1 :: right.1 :: rest)
        selected (actual.1.forward.map input) budget)) input with
    | .head received => fun reader limited => (reader.readCode selected).bind (fun bit =>
        .step .transportSplitDecision (fun _ => match bit with
          | ⟨false, same⟩ => .step .formationWitness (fun _ =>
              let child : GeneratedStructuralBranchContinuation left.1 :=
                ⟨received.1, by rw [left.2]; exact ⟨same.symm, received.2⟩⟩
              .step .transportApplicationPacket (fun _ =>
                let produced : Actual (actual.1.forward.map (.head received)) :=
                  ⟨.head child, by
                    have valueFalse : received.1 selected = false := same.symm
                    obtain ⟨_, actualSame⟩ := actual; cases actualSame
                    obtain ⟨_, leftSame⟩ := left; cases leftSame
                    obtain ⟨_, rightSame⟩ := right; cases rightSame
                    obtain ⟨_, splitterSame⟩ := splitter; cases splitterSame
                    simp only [AcceptedFrontierPreservation.expandHead, AcceptingFrontierTransport.expandHead,
                      generatedStructuralSplit, structuralContextSplit, splitStructuralContextContinuation, dif_pos valueFalse]
                    rfl⟩
                .done ⟨produced, reader, limited⟩))
          | ⟨true, same⟩ => .step .formationWitness (fun _ =>
              let child : GeneratedStructuralBranchContinuation right.1 :=
                ⟨received.1, by rw [right.2]; exact ⟨same.symm, received.2⟩⟩
              .step .transportApplicationPacket (fun _ =>
                let produced : Actual (actual.1.forward.map (.head received)) :=
                  ⟨.tail (.head child), by
                    obtain ⟨_, actualSame⟩ := actual; cases actualSame
                    obtain ⟨_, leftSame⟩ := left; cases leftSame
                    obtain ⟨_, rightSame⟩ := right; cases rightSame
                    obtain ⟨_, splitterSame⟩ := splitter; cases splitterSame
                    have notFalse : received.1 selected ≠ false := fun contrary => Bool.noConfusion (same.trans contrary)
                    simp only [AcceptedFrontierPreservation.expandHead, AcceptingFrontierTransport.expandHead,
                      generatedStructuralSplit, structuralContextSplit, splitStructuralContextContinuation, dif_neg notFalse]
                    rfl⟩
                .done ⟨produced, reader, limited⟩))))
    | .tail received => fun reader limited => .step .transportApplicationPacket (fun _ =>
        let produced : Actual (actual.1.forward.map (.tail received)) :=
          ⟨.tail (.tail received), by obtain ⟨_, same⟩ := actual; cases same; rfl⟩
        .done ⟨produced, reader, limited⟩)) reader limited)

def expandBackward {formula : Cnf} (selected : Var) (parent : GeneratedStructuralBranchContext formula)
    (fresh : StructuralDecisionsAvoid selected parent.context.decisions)
    (left : Actual (parent.child selected false fresh)) (right : Actual (parent.child selected true fresh))
    (splitter : ControlFrontierOpening.Split parent selected fresh left right)
    {rest : List (GeneratedStructuralBranchContext formula)}
    (actual : Actual (AcceptedFrontierPreservation.expandHead (rest := rest) splitter.1))
    (input : FrontierContinuation (generatedStructuralBranchSystem formula) (left.1 :: right.1 :: rest))
    (budget : Nat) (reader : Reader (frontierAssignment (formula := formula) (frontier := left.1 :: right.1 :: rest) input))
    (limited : reader.queryBound selected ≤ budget) :
    Code Label (Applied (formula := formula) (frontier := parent :: rest) selected (actual.1.backward.map input) budget) :=
  .step .transportApplicationCell (fun _ => match input with
    | .head received => .step .formationWitness (fun _ =>
        let merged : GeneratedStructuralBranchContinuation parent :=
          ⟨received.1, by
            have holds := Eq.mp (congrArg (StructuralDecisionsHold received.1)
              (congrArg (fun context => context.context.decisions) left.2)) received.2
            exact holds.2⟩
        .step .transportApplicationPacket (fun _ =>
          let produced : Actual (actual.1.backward.map (.head received)) := ⟨.head merged, by
            obtain ⟨_, actualSame⟩ := actual; cases actualSame
            obtain ⟨_, leftSame⟩ := left; cases leftSame
            obtain ⟨_, rightSame⟩ := right; cases rightSame
            obtain ⟨_, splitterSame⟩ := splitter; cases splitterSame
            rfl⟩
          .done ⟨produced, reader, limited⟩))
    | .tail tail => .step .transportApplicationCell (fun _ => match tail with
      | .head received => .step .formationWitness (fun _ =>
          let merged : GeneratedStructuralBranchContinuation parent :=
            ⟨received.1, by
              have holds := Eq.mp (congrArg (StructuralDecisionsHold received.1)
                (congrArg (fun context => context.context.decisions) right.2)) received.2
              exact holds.2⟩
          .step .transportApplicationPacket (fun _ =>
            let produced : Actual (actual.1.backward.map (.tail (.head received))) := ⟨.head merged, by
              obtain ⟨_, actualSame⟩ := actual; cases actualSame
              obtain ⟨_, leftSame⟩ := left; cases leftSame
              obtain ⟨_, rightSame⟩ := right; cases rightSame
              obtain ⟨_, splitterSame⟩ := splitter; cases splitterSame
              rfl⟩
            .done ⟨produced, reader, limited⟩))
      | .tail received => .step .transportApplicationPacket (fun _ =>
          let produced : Actual (actual.1.backward.map (.tail (.tail received))) :=
            ⟨.tail received, by obtain ⟨_, same⟩ := actual; cases same; rfl⟩
          .done ⟨produced, reader, limited⟩)))

theorem expand_forward_bounded {formula : Cnf} (selected : Var) (parent : GeneratedStructuralBranchContext formula)
    (fresh : StructuralDecisionsAvoid selected parent.context.decisions)
    (left : Actual (parent.child selected false fresh)) (right : Actual (parent.child selected true fresh))
    (splitter : ControlFrontierOpening.Split parent selected fresh left right)
    {rest : List (GeneratedStructuralBranchContext formula)}
    (actual : Actual (AcceptedFrontierPreservation.expandHead (rest := rest) splitter.1))
    (input : FrontierContinuation (generatedStructuralBranchSystem formula) (parent :: rest))
    (budget : Nat) (reader : Reader (frontierAssignment (formula := formula) (frontier := parent :: rest) input))
    (limited : reader.queryBound selected ≤ budget) :
    Within (expandForward selected parent fresh left right splitter actual input budget reader limited) ((budget + 3) + 1) := by
  revert reader limited; cases input with
  | head received =>
      intro reader limited
      apply within_step
      apply within_bind (more := 3) (within_weaken (reader.bounded selected) limited)
      intro bit
      apply within_step; cases bit with
      | mk value same => cases value <;> exact within_step _ _ (within_step _ _ (within_done _))
  | tail received =>
      intro reader limited
      apply within_step
      apply within_weaken (bound := 1) (increase := Nat.le_trans (by decide : 1 ≤ 3) (Nat.le_add_left _ _))
      exact within_step _ _ (within_done _)

theorem expand_backward_bounded {formula : Cnf} (selected : Var) (parent : GeneratedStructuralBranchContext formula)
    (fresh : StructuralDecisionsAvoid selected parent.context.decisions)
    (left : Actual (parent.child selected false fresh)) (right : Actual (parent.child selected true fresh))
    (splitter : ControlFrontierOpening.Split parent selected fresh left right)
    {rest : List (GeneratedStructuralBranchContext formula)}
    (actual : Actual (AcceptedFrontierPreservation.expandHead (rest := rest) splitter.1))
    (input : FrontierContinuation (generatedStructuralBranchSystem formula) (left.1 :: right.1 :: rest))
    (budget : Nat) (reader : Reader (frontierAssignment (formula := formula) (frontier := left.1 :: right.1 :: rest) input))
    (limited : reader.queryBound selected ≤ budget) :
    Within (expandBackward selected parent fresh left right splitter actual input budget reader limited) 4 := by
  apply within_step; cases input with
  | head received =>
      apply within_weaken (bound := 2) (increase := by decide)
      exact within_step _ _ (within_step _ _ (within_done _))
  | tail tail =>
      apply within_step; cases tail with
      | head received => exact within_step _ _ (within_step _ _ (within_done _))
      | tail received =>
          apply within_weaken (bound := 1) (increase := by decide)
          exact within_step _ _ (within_done _)

def expandCode {formula : Cnf} (selected : Var) (parent : GeneratedStructuralBranchContext formula)
    (fresh : StructuralDecisionsAvoid selected parent.context.decisions)
    (left : Actual (parent.child selected false fresh)) (right : Actual (parent.child selected true fresh))
    (splitter : ControlFrontierOpening.Split parent selected fresh left right)
    {rest : List (GeneratedStructuralBranchContext formula)} :
    Code Label (Formed selected (AcceptedFrontierPreservation.expandHead (rest := rest) splitter.1)) :=
  (ControlFrontierOpening.expandCode (rest := rest) splitter.1).bind (fun actual =>
    .step .executionPayload (fun _ => .step .controlClosure (fun _ =>
      let forward := expandForward selected parent fresh left right splitter actual
      .step .controlClosure (fun _ =>
        let backward := expandBackward selected parent fresh left right splitter actual
        .step .formationResources (fun _ => .done
          ⟨⟨actual.1, fun budget => (budget + 3) + 1, fun _ => 4, id, id, forward, backward,
            expand_forward_bounded selected parent fresh left right splitter actual,
            expand_backward_bounded selected parent fresh left right splitter actual⟩, actual.2⟩)))))

theorem expand_bounded {formula : Cnf} (selected : Var) (parent : GeneratedStructuralBranchContext formula)
    (fresh : StructuralDecisionsAvoid selected parent.context.decisions)
    (left : Actual (parent.child selected false fresh)) (right : Actual (parent.child selected true fresh))
    (splitter : ControlFrontierOpening.Split parent selected fresh left right)
    {rest : List (GeneratedStructuralBranchContext formula)} :
    Within (expandCode selected parent fresh left right splitter (rest := rest)) 7 := by
  apply within_bind (more := 4) (ControlFrontierOpening.expand_bounded splitter.1); intro actual
  repeat apply within_step
  exact within_done _

end ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierApplication

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierApplication.expandForward
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierApplication.expandBackward
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierApplication.expand_forward_bounded
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierApplication.expand_backward_bounded
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierApplication.expandCode
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierApplication.expand_bounded
/- AXIOM_AUDIT_END -/
