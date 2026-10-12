import Tests.LocalAlignment.DocumentaryControlFrontierCeilingLeaves

/-! Each composite consumes its actual child Applications and their positive
Nat ceilings. The second child never receives a native bound closure result.
The original complete preservation is formed from the same actual children and
retained as data; its historical executor is stored for agreement only. -/
set_option genInjectivity false
set_option backward.match.sparseCases false
set_option maxHeartbeats 18000000
namespace ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierCeilingApplication
open SAT Selection Control ControlBindings ControlMasterData ControlAssignmentApplication

def prependForward {formula : Cnf} {selected : Var} {head : GeneratedStructuralBranchContext formula} {source target}
    (child : ExecutablePreservation formula selected source target)
    (actual : Actual (child.original.preservation.prepend (head := head)))
    (input : FrontierContinuation (generatedStructuralBranchSystem formula) (head :: source))
    (budget : Nat)
    (reader : Reader (frontierAssignment (formula := formula) (frontier := head :: source) input))
    (limited : reader.queryBound selected ≤ budget) :
    Code Label (Applied (formula := formula) (frontier := head :: target) selected
      (actual.1.forward.map input) (max budget (child.original.forwardReaderBound budget))) :=
  .step .transportApplicationCell (fun _ => match input with
    | .head received => (ControlReaderCeiling.code child.forwardCeiling budget).bind (fun childCeiling =>
        (ControlReaderCeiling.maxCode budget childCeiling.1).bind (fun combined =>
          .step .transportApplicationPacket (fun _ =>
            let output : Actual (actual.1.forward.map (.head received)) :=
              ⟨.head received, by obtain ⟨_, same⟩ := actual; cases same; rfl⟩
            let ceiling : Actual (max budget (child.original.forwardReaderBound budget)) :=
              ⟨combined.1, combined.2.trans (congrArg (max budget) childCeiling.2)⟩
            .done ⟨⟨output, reader, Nat.le_trans limited
              (ControlFrontierApplication.reader_max_left _ _)⟩, ceiling⟩)))
    | .tail received => (child.forward received budget reader limited).bind (fun output =>
        (ControlReaderCeiling.maxCode budget output.ceiling.1).bind (fun combined =>
          .step .transportApplicationPacket (fun _ =>
            let produced : Actual (actual.1.forward.map (.tail received)) :=
              ⟨.tail output.application.continuation.1, by
                obtain ⟨_, same⟩ := actual; cases same
                exact congrArg FrontierCompletion.tail output.application.continuation.2⟩
            let ceiling : Actual (max budget (child.original.forwardReaderBound budget)) :=
              ⟨combined.1, combined.2.trans (congrArg (max budget) output.ceiling.2)⟩
            .done ⟨⟨produced, output.application.reader,
              Nat.le_trans output.application.limited
                (ControlFrontierApplication.reader_max_right _ _)⟩, ceiling⟩))))

def prependBackward {formula : Cnf} {selected : Var} {head : GeneratedStructuralBranchContext formula} {source target}
    (child : ExecutablePreservation formula selected source target)
    (actual : Actual (child.original.preservation.prepend (head := head)))
    (input : FrontierContinuation (generatedStructuralBranchSystem formula) (head :: target))
    (budget : Nat)
    (reader : Reader (frontierAssignment (formula := formula) (frontier := head :: target) input))
    (limited : reader.queryBound selected ≤ budget) :
    Code Label (Applied (formula := formula) (frontier := head :: source) selected
      (actual.1.backward.map input) (max budget (child.original.backwardReaderBound budget))) :=
  .step .transportApplicationCell (fun _ => match input with
    | .head received => (ControlReaderCeiling.code child.backwardCeiling budget).bind (fun childCeiling =>
        (ControlReaderCeiling.maxCode budget childCeiling.1).bind (fun combined =>
          .step .transportApplicationPacket (fun _ =>
            let output : Actual (actual.1.backward.map (.head received)) :=
              ⟨.head received, by obtain ⟨_, same⟩ := actual; cases same; rfl⟩
            let ceiling : Actual (max budget (child.original.backwardReaderBound budget)) :=
              ⟨combined.1, combined.2.trans (congrArg (max budget) childCeiling.2)⟩
            .done ⟨⟨output, reader, Nat.le_trans limited
              (ControlFrontierApplication.reader_max_left _ _)⟩, ceiling⟩)))
    | .tail received => (child.backward received budget reader limited).bind (fun output =>
        (ControlReaderCeiling.maxCode budget output.ceiling.1).bind (fun combined =>
          .step .transportApplicationPacket (fun _ =>
            let produced : Actual (actual.1.backward.map (.tail received)) :=
              ⟨.tail output.application.continuation.1, by
                obtain ⟨_, same⟩ := actual; cases same
                exact congrArg FrontierCompletion.tail output.application.continuation.2⟩
            let ceiling : Actual (max budget (child.original.backwardReaderBound budget)) :=
              ⟨combined.1, combined.2.trans (congrArg (max budget) output.ceiling.2)⟩
            .done ⟨⟨produced, output.application.reader,
              Nat.le_trans output.application.limited
                (ControlFrontierApplication.reader_max_right _ _)⟩, ceiling⟩))))

theorem prepend_forward_finite {formula : Cnf} {selected : Var} {head : GeneratedStructuralBranchContext formula} {source target}
    (child : ExecutablePreservation formula selected source target)
    (actual : Actual (child.original.preservation.prepend (head := head)))
    (input : FrontierContinuation (generatedStructuralBranchSystem formula) (head :: source))
    (budget : Nat)
    (reader : Reader (frontierAssignment (formula := formula) (frontier := head :: source) input))
    (limited : reader.queryBound selected ≤ budget) :
    Finite (prependForward child actual input budget reader limited) := by
  apply finite_step
  cases input with
  | head received =>
      apply finite_bind (ControlReaderCeiling.finite _ _); intro childCeiling
      apply finite_bind (ControlReaderCeiling.max_finite _ _); intro combined
      exact finite_step _ _ (finite_done _)
  | tail received =>
      apply finite_bind (child.forward_finite _ _ _ _); intro output
      apply finite_bind (ControlReaderCeiling.max_finite _ _); intro combined
      exact finite_step _ _ (finite_done _)

theorem prepend_backward_finite {formula : Cnf} {selected : Var} {head : GeneratedStructuralBranchContext formula} {source target}
    (child : ExecutablePreservation formula selected source target)
    (actual : Actual (child.original.preservation.prepend (head := head)))
    (input : FrontierContinuation (generatedStructuralBranchSystem formula) (head :: target))
    (budget : Nat)
    (reader : Reader (frontierAssignment (formula := formula) (frontier := head :: target) input))
    (limited : reader.queryBound selected ≤ budget) :
    Finite (prependBackward child actual input budget reader limited) := by
  apply finite_step
  cases input with
  | head received =>
      apply finite_bind (ControlReaderCeiling.finite _ _); intro childCeiling
      apply finite_bind (ControlReaderCeiling.max_finite _ _); intro combined
      exact finite_step _ _ (finite_done _)
  | tail received =>
      apply finite_bind (child.backward_finite _ _ _ _); intro output
      apply finite_bind (ControlReaderCeiling.max_finite _ _); intro combined
      exact finite_step _ _ (finite_done _)

def transForward {formula : Cnf} {selected : Var} {source middle target}
    (left : ExecutablePreservation formula selected source middle)
    (right : ExecutablePreservation formula selected middle target)
    (actual : Actual (left.original.preservation.trans right.original.preservation))
    (input : FrontierContinuation (generatedStructuralBranchSystem formula) source)
    (budget : Nat)
    (reader : Reader (frontierAssignment (formula := formula) (frontier := source) input))
    (limited : reader.queryBound selected ≤ budget) :
    Code Label (Applied (formula := formula) (frontier := target) selected
      (actual.1.forward.map input)
      (right.original.forwardReaderBound (left.original.forwardReaderBound budget))) :=
  .step .transportApplicationCell (fun _ =>
    (left.forward input budget reader limited).bind (fun first =>
      (right.forward first.application.continuation.1 first.ceiling.1 first.application.reader
        (applied_limited first)).bind (fun second =>
        .step .transportApplicationPacket (fun _ =>
          let produced : Actual (actual.1.forward.map input) :=
            ⟨second.application.continuation.1, by
              obtain ⟨_, same⟩ := actual; cases same
              exact second.application.continuation.2.trans
                (congrArg right.original.preservation.forward.map first.application.continuation.2)⟩
          let ceiling : Actual
              (right.original.forwardReaderBound (left.original.forwardReaderBound budget)) :=
            ⟨second.ceiling.1, second.ceiling.2.trans
              (congrArg right.original.forwardReaderBound first.ceiling.2)⟩
          let finalLimited : second.application.reader.queryBound selected ≤
              right.original.forwardReaderBound (left.original.forwardReaderBound budget) := by
            exact Nat.le_trans (applied_limited second) (Nat.le_of_eq ceiling.2)
          .done ⟨⟨produced, second.application.reader, finalLimited⟩, ceiling⟩))))

def transBackward {formula : Cnf} {selected : Var} {source middle target}
    (left : ExecutablePreservation formula selected source middle)
    (right : ExecutablePreservation formula selected middle target)
    (actual : Actual (left.original.preservation.trans right.original.preservation))
    (input : FrontierContinuation (generatedStructuralBranchSystem formula) target)
    (budget : Nat)
    (reader : Reader (frontierAssignment (formula := formula) (frontier := target) input))
    (limited : reader.queryBound selected ≤ budget) :
    Code Label (Applied (formula := formula) (frontier := source) selected
      (actual.1.backward.map input)
      (left.original.backwardReaderBound (right.original.backwardReaderBound budget))) :=
  .step .transportApplicationCell (fun _ =>
    (right.backward input budget reader limited).bind (fun first =>
      (left.backward first.application.continuation.1 first.ceiling.1 first.application.reader
        (applied_limited first)).bind (fun second =>
        .step .transportApplicationPacket (fun _ =>
          let produced : Actual (actual.1.backward.map input) :=
            ⟨second.application.continuation.1, by
              obtain ⟨_, same⟩ := actual; cases same
              exact second.application.continuation.2.trans
                (congrArg left.original.preservation.backward.map first.application.continuation.2)⟩
          let ceiling : Actual
              (left.original.backwardReaderBound (right.original.backwardReaderBound budget)) :=
            ⟨second.ceiling.1, second.ceiling.2.trans
              (congrArg left.original.backwardReaderBound first.ceiling.2)⟩
          let finalLimited : second.application.reader.queryBound selected ≤
              left.original.backwardReaderBound (right.original.backwardReaderBound budget) := by
            exact Nat.le_trans (applied_limited second) (Nat.le_of_eq ceiling.2)
          .done ⟨⟨produced, second.application.reader, finalLimited⟩, ceiling⟩))))

theorem trans_forward_finite {formula : Cnf} {selected : Var} {source middle target}
    (left : ExecutablePreservation formula selected source middle)
    (right : ExecutablePreservation formula selected middle target)
    (actual : Actual (left.original.preservation.trans right.original.preservation))
    (input : FrontierContinuation (generatedStructuralBranchSystem formula) source)
    (budget : Nat)
    (reader : Reader (frontierAssignment (formula := formula) (frontier := source) input))
    (limited : reader.queryBound selected ≤ budget) :
    Finite (transForward left right actual input budget reader limited) := by
  apply finite_step
  apply finite_bind (left.forward_finite _ _ _ _); intro first
  apply finite_bind (right.forward_finite _ _ _ _); intro second
  exact finite_step _ _ (finite_done _)

theorem trans_backward_finite {formula : Cnf} {selected : Var} {source middle target}
    (left : ExecutablePreservation formula selected source middle)
    (right : ExecutablePreservation formula selected middle target)
    (actual : Actual (left.original.preservation.trans right.original.preservation))
    (input : FrontierContinuation (generatedStructuralBranchSystem formula) target)
    (budget : Nat)
    (reader : Reader (frontierAssignment (formula := formula) (frontier := target) input))
    (limited : reader.queryBound selected ≤ budget) :
    Finite (transBackward left right actual input budget reader limited) := by
  apply finite_step
  apply finite_bind (right.backward_finite _ _ _ _); intro first
  apply finite_bind (left.backward_finite _ _ _ _); intro second
  exact finite_step _ _ (finite_done _)

def prependCode {formula : Cnf} {selected : Var} {head : GeneratedStructuralBranchContext formula} {source target}
    (child : ExecutablePreservation formula selected source target) :
    Code Label (Formed selected (child.original.preservation.prepend (head := head))) :=
  (ControlFrontierOpening.prependCode (head := head) child.original.preservation).bind (fun actual =>
    .step .executionPayload (fun _ => .step .controlClosure (fun _ =>
      let originalForward := ControlFrontierApplication.prependForward child.original actual
      .step .controlClosure (fun _ =>
        let originalBackward := ControlFrontierApplication.prependBackward child.original actual
        .step .formationResources (fun _ =>
          let original : ControlFrontierApplication.ExecutablePreservation formula selected (head :: source) (head :: target) :=
            ControlFrontierCeilingOriginal.assembled
            (actual.1)
            (fun budget => (child.original.forwardCost budget + 1) + 1)
            (fun budget => (child.original.backwardCost budget + 1) + 1)
            (fun budget => max budget (child.original.forwardReaderBound budget))
            (fun budget => max budget (child.original.backwardReaderBound budget))
            (originalForward)
            (originalBackward)
            (ControlFrontierApplication.prepend_forward_bounded child.original actual)
            (ControlFrontierApplication.prepend_backward_bounded child.original actual)
          let receivedWhole : Actual (ControlFrontierCeilingOriginal.prepend child.original actual) := ⟨original, rfl⟩
          formedCode receivedWhole.1 (.maximum child.forwardCeiling) (.maximum child.backwardCeiling)
            (prependForward child actual) (prependBackward child actual)
            (prepend_forward_finite child actual) (prepend_backward_finite child actual) actual.2)))))

theorem prepend_finite {formula : Cnf} {selected : Var} {head : GeneratedStructuralBranchContext formula} {source target}
    (child : ExecutablePreservation formula selected source target) :
    Finite (prependCode (head := head) child) := by
  apply finite_bind (finite_of_within (ControlFrontierOpening.prepend_bounded child.original.preservation)); intro actual
  repeat apply finite_step
  exact finite_done _

def transCode {formula : Cnf} {selected : Var} {source middle target}
    (left : ExecutablePreservation formula selected source middle)
    (right : ExecutablePreservation formula selected middle target) :
    Code Label (Formed selected (left.original.preservation.trans right.original.preservation)) :=
  (ControlFrontierOpening.transCode left.original.preservation right.original.preservation).bind (fun actual =>
    .step .executionPayload (fun _ => .step .controlClosure (fun _ =>
      let originalForward := ControlFrontierApplication.transForward left.original right.original actual
      .step .controlClosure (fun _ =>
        let originalBackward := ControlFrontierApplication.transBackward left.original right.original actual
        .step .formationResources (fun _ =>
          let original : ControlFrontierApplication.ExecutablePreservation formula selected source target :=
            ControlFrontierCeilingOriginal.assembled
            (actual.1)
            (fun budget => (left.original.forwardCost budget +
                (right.original.forwardCost (left.original.forwardReaderBound budget) + 1)) + 1)
            (fun budget => (right.original.backwardCost budget +
                (left.original.backwardCost (right.original.backwardReaderBound budget) + 1)) + 1)
            (fun budget => right.original.forwardReaderBound (left.original.forwardReaderBound budget))
            (fun budget => left.original.backwardReaderBound (right.original.backwardReaderBound budget))
            (originalForward)
            (originalBackward)
            (ControlFrontierApplication.trans_forward_bounded left.original right.original actual)
            (ControlFrontierApplication.trans_backward_bounded left.original right.original actual)
          let receivedWhole : Actual (ControlFrontierCeilingOriginal.trans left.original right.original actual) := ⟨original, rfl⟩
          formedCode receivedWhole.1 (ControlReaderCeiling.Realized.trans
              (firstExpected := left.original.forwardReaderBound) (secondExpected := right.original.forwardReaderBound)
              left.forwardCeiling right.forwardCeiling)
            (ControlReaderCeiling.Realized.trans
              (firstExpected := right.original.backwardReaderBound) (secondExpected := left.original.backwardReaderBound)
              right.backwardCeiling left.backwardCeiling)
            (transForward left right actual) (transBackward left right actual)
            (trans_forward_finite left right actual) (trans_backward_finite left right actual) actual.2)))))

theorem trans_finite {formula : Cnf} {selected : Var} {source middle target}
    (left : ExecutablePreservation formula selected source middle)
    (right : ExecutablePreservation formula selected middle target) :
    Finite (transCode left right) := by
  apply finite_bind (finite_of_within (ControlFrontierOpening.trans_bounded _ _)); intro actual
  repeat apply finite_step
  exact finite_done _

end ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierCeilingApplication

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierCeilingApplication.prependForward
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierCeilingApplication.prependBackward
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierCeilingApplication.prepend_forward_finite
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierCeilingApplication.prepend_backward_finite
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierCeilingApplication.transForward
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierCeilingApplication.transBackward
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierCeilingApplication.trans_forward_finite
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierCeilingApplication.trans_backward_finite
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierCeilingApplication.prependCode
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierCeilingApplication.prepend_finite
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierCeilingApplication.transCode
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierCeilingApplication.trans_finite
/- AXIOM_AUDIT_END -/
