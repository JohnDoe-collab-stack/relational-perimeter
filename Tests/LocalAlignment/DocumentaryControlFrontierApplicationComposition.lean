import Tests.LocalAlignment.DocumentaryControlFrontierApplication

/-! Composition uses the actual prior execution payloads and their complete
produced continuations. Backward composition executes the right child first.
Prepend preserves head readers and consumes the child's reader on tail routes. -/
set_option genInjectivity false
set_option maxHeartbeats 10000000
namespace ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierApplication
open SAT Selection Control ControlBindings ControlMasterData ControlAssignmentApplication

theorem reader_max_left (left right : Nat) : left ≤ max left right := by
  cases Nat.decLe left right with
  | isTrue bounded => rw [Nat.max_def, if_pos bounded]; exact bounded
  | isFalse unbounded => rw [Nat.max_def, if_neg unbounded]; exact Nat.le_refl _

theorem reader_max_right (left right : Nat) : right ≤ max left right := by
  cases Nat.decLe left right with
  | isTrue bounded => rw [Nat.max_def, if_pos bounded]; exact Nat.le_refl _
  | isFalse unbounded => rw [Nat.max_def, if_neg unbounded]; exact Nat.le_of_not_ge unbounded

def swapApplication {formula : Cnf} (selected : Var) {first second : GeneratedStructuralBranchContext formula}
    {rest : List (GeneratedStructuralBranchContext formula)}
    (actual : Actual (AcceptingFrontierTransport.swapFirstTwo
      (system := generatedStructuralBranchSystem formula) (first := first) (second := second) (rest := rest)))
    (input : FrontierContinuation (generatedStructuralBranchSystem formula) (first :: second :: rest))
    (budget : Nat) (reader : Reader (frontierAssignment (formula := formula) (frontier := first :: second :: rest) input)) (limited : reader.queryBound selected ≤ budget) :
    Code Label (Applied (formula := formula) (frontier := second :: first :: rest) selected (actual.1.map input) budget) :=
  .step .transportApplicationCell (fun _ => match input with
    | .head received => .step .transportApplicationPacket (fun _ =>
        let output : Actual (actual.1.map (.head received)) :=
          ⟨.tail (.head received), by obtain ⟨_, same⟩ := actual; cases same; rfl⟩
        .done ⟨output, reader, limited⟩)
    | .tail tail => .step .transportApplicationCell (fun _ => match tail with
      | .head received => .step .transportApplicationPacket (fun _ =>
          let output : Actual (actual.1.map (.tail (.head received))) :=
            ⟨.head received, by obtain ⟨_, same⟩ := actual; cases same; rfl⟩
          .done ⟨output, reader, limited⟩)
      | .tail received => .step .transportApplicationPacket (fun _ =>
          let output : Actual (actual.1.map (.tail (.tail received))) :=
            ⟨.tail (.tail received), by obtain ⟨_, same⟩ := actual; cases same; rfl⟩
          .done ⟨output, reader, limited⟩)))

theorem swap_application_bounded {formula : Cnf} (selected : Var) {first second : GeneratedStructuralBranchContext formula}
    {rest : List (GeneratedStructuralBranchContext formula)}
    (actual : Actual (AcceptingFrontierTransport.swapFirstTwo
      (system := generatedStructuralBranchSystem formula) (first := first) (second := second) (rest := rest)))
    (input : FrontierContinuation (generatedStructuralBranchSystem formula) (first :: second :: rest))
    (budget : Nat) (reader : Reader (frontierAssignment (formula := formula) (frontier := first :: second :: rest) input)) (limited : reader.queryBound selected ≤ budget) :
    Within (swapApplication selected actual input budget reader limited) 3 := by
  apply within_step
  cases input with
  | head received => exact within_weaken (within_step _ _ (within_done _)) (by decide : 1 ≤ 2)
  | tail tail => apply within_step; cases tail <;> exact within_step _ _ (within_done _)

def swapCode (formula : Cnf) (selected : Var) {first second : GeneratedStructuralBranchContext formula}
    {rest : List (GeneratedStructuralBranchContext formula)} :
    Code Label (Formed selected (AcceptedFrontierPreservation.swapFirstTwo
      (system := generatedStructuralBranchSystem formula) (first := first) (second := second) (rest := rest))) :=
  ControlFrontierEvaluation.swapCode.bind (fun actual =>
    .step .executionPayload (fun _ => .step .controlClosure (fun _ =>
      let forward := swapApplication selected
        ⟨actual.1.forward, congrArg AcceptedFrontierPreservation.forward actual.2⟩
      .step .controlClosure (fun _ =>
        let backward := swapApplication selected
          ⟨actual.1.backward, congrArg AcceptedFrontierPreservation.backward actual.2⟩
        .step .formationResources (fun _ => .done
          ⟨⟨actual.1, fun _ => 3, fun _ => 3, id, id, forward, backward,
            swap_application_bounded selected _, swap_application_bounded selected _⟩, actual.2⟩)))))

theorem swap_bounded (formula : Cnf) (selected : Var) {first second : GeneratedStructuralBranchContext formula}
    {rest : List (GeneratedStructuralBranchContext formula)} :
    Within (swapCode formula selected (first := first) (second := second) (rest := rest)) (3 + 4) := by
  apply within_bind ControlFrontierEvaluation.swap_bounded; intro actual
  repeat apply within_step
  exact within_done _

def prependForward {formula : Cnf} {selected : Var} {head : GeneratedStructuralBranchContext formula} {source target}
    (child : ExecutablePreservation formula selected source target)
    (actual : Actual (child.preservation.prepend (head := head)))
    (input : FrontierContinuation (generatedStructuralBranchSystem formula) (head :: source))
    (budget : Nat) (reader : Reader (frontierAssignment (formula := formula) (frontier := head :: source) input)) (limited : reader.queryBound selected ≤ budget) :
    Code Label (Applied (formula := formula) (frontier := head :: target) selected (actual.1.forward.map input) (max budget (child.forwardReaderBound budget))) :=
  .step .transportApplicationCell (fun _ => match input with
    | .head received => .step .transportApplicationPacket (fun _ =>
        let output : Actual (actual.1.forward.map (.head received)) :=
          ⟨.head received, by obtain ⟨_, same⟩ := actual; cases same; rfl⟩
        .done ⟨output, reader, Nat.le_trans limited (reader_max_left budget (child.forwardReaderBound budget))⟩)
    | .tail received => (child.forward received budget reader limited).bind (fun output =>
        .step .transportApplicationPacket (fun _ =>
          let produced : Actual (actual.1.forward.map (.tail received)) :=
            ⟨.tail output.continuation.1, by
            obtain ⟨_, same⟩ := actual; cases same
            exact congrArg FrontierCompletion.tail output.continuation.2⟩
          .done ⟨produced, output.reader, Nat.le_trans output.limited (reader_max_right budget (child.forwardReaderBound budget))⟩)))

def prependBackward {formula : Cnf} {selected : Var} {head : GeneratedStructuralBranchContext formula} {source target}
    (child : ExecutablePreservation formula selected source target)
    (actual : Actual (child.preservation.prepend (head := head)))
    (input : FrontierContinuation (generatedStructuralBranchSystem formula) (head :: target))
    (budget : Nat) (reader : Reader (frontierAssignment (formula := formula) (frontier := head :: target) input)) (limited : reader.queryBound selected ≤ budget) :
    Code Label (Applied (formula := formula) (frontier := head :: source) selected (actual.1.backward.map input) (max budget (child.backwardReaderBound budget))) :=
  .step .transportApplicationCell (fun _ => match input with
    | .head received => .step .transportApplicationPacket (fun _ =>
        let output : Actual (actual.1.backward.map (.head received)) :=
          ⟨.head received, by obtain ⟨_, same⟩ := actual; cases same; rfl⟩
        .done ⟨output, reader, Nat.le_trans limited (reader_max_left budget (child.backwardReaderBound budget))⟩)
    | .tail received => (child.backward received budget reader limited).bind (fun output =>
        .step .transportApplicationPacket (fun _ =>
          let produced : Actual (actual.1.backward.map (.tail received)) :=
            ⟨.tail output.continuation.1, by
            obtain ⟨_, same⟩ := actual; cases same
            exact congrArg FrontierCompletion.tail output.continuation.2⟩
          .done ⟨produced, output.reader, Nat.le_trans output.limited (reader_max_right budget (child.backwardReaderBound budget))⟩)))

theorem prepend_forward_bounded {formula : Cnf} {selected : Var} {head : GeneratedStructuralBranchContext formula} {source target}
    (child : ExecutablePreservation formula selected source target)
    (actual : Actual (child.preservation.prepend (head := head)))
    (input : FrontierContinuation (generatedStructuralBranchSystem formula) (head :: source))
    (budget : Nat) (reader : Reader (frontierAssignment (formula := formula) (frontier := (head :: source)) input)) (limited : reader.queryBound selected ≤ budget) :
    Within (prependForward child actual input budget reader limited) ((child.forwardCost budget + 1) + 1) := by
  apply within_step
  cases input with
  | head received => exact within_weaken (within_step _ _ (within_done _)) (Nat.le_add_left _ _)
  | tail received =>
      apply within_bind (child.forward_bounded _ _ _ _); intro output
      exact within_step _ _ (within_done _)

theorem prepend_backward_bounded {formula : Cnf} {selected : Var} {head : GeneratedStructuralBranchContext formula} {source target}
    (child : ExecutablePreservation formula selected source target)
    (actual : Actual (child.preservation.prepend (head := head)))
    (input : FrontierContinuation (generatedStructuralBranchSystem formula) (head :: target))
    (budget : Nat) (reader : Reader (frontierAssignment (formula := formula) (frontier := (head :: target)) input)) (limited : reader.queryBound selected ≤ budget) :
    Within (prependBackward child actual input budget reader limited) ((child.backwardCost budget + 1) + 1) := by
  apply within_step
  cases input with
  | head received => exact within_weaken (within_step _ _ (within_done _)) (Nat.le_add_left _ _)
  | tail received =>
      apply within_bind (child.backward_bounded _ _ _ _); intro output
      exact within_step _ _ (within_done _)

def prependCode {formula : Cnf} {selected : Var} {head : GeneratedStructuralBranchContext formula} {source target}
    (child : ExecutablePreservation formula selected source target) :
    Code Label (Formed selected (child.preservation.prepend (head := head))) :=
  (ControlFrontierOpening.prependCode (head := head) child.preservation).bind (fun actual =>
    .step .executionPayload (fun _ => .step .controlClosure (fun _ =>
      let forward := prependForward child actual
      .step .controlClosure (fun _ =>
        let backward := prependBackward child actual
        .step .formationResources (fun _ => .done
          ⟨⟨actual.1, fun budget => (child.forwardCost budget + 1) + 1,
            fun budget => (child.backwardCost budget + 1) + 1,
            fun budget => max budget (child.forwardReaderBound budget),
            fun budget => max budget (child.backwardReaderBound budget),
            forward, backward, prepend_forward_bounded child actual, prepend_backward_bounded child actual⟩, actual.2⟩)))))

theorem prepend_bounded {formula : Cnf} {selected : Var} {head : GeneratedStructuralBranchContext formula} {source target}
    (child : ExecutablePreservation formula selected source target) :
    Within (prependCode (head := head) child) (3 + 4) := by
  apply within_bind (ControlFrontierOpening.prepend_bounded child.preservation); intro actual
  repeat apply within_step
  exact within_done _

def transForward {formula : Cnf} {selected : Var} {source middle target}
    (left : ExecutablePreservation formula selected source middle)
    (right : ExecutablePreservation formula selected middle target)
    (actual : Actual (left.preservation.trans right.preservation))
    (input : FrontierContinuation (generatedStructuralBranchSystem formula) source)
    (budget : Nat) (reader : Reader (frontierAssignment (formula := formula) (frontier := source) input)) (limited : reader.queryBound selected ≤ budget) :
    Code Label (Applied (formula := formula) (frontier := target) selected (actual.1.forward.map input)
      (right.forwardReaderBound (left.forwardReaderBound budget))) :=
  .step .transportApplicationCell (fun _ =>
    (left.forward input budget reader limited).bind (fun first =>
      (right.forward first.continuation.1 (left.forwardReaderBound budget) first.reader first.limited).bind (fun second =>
        .step .transportApplicationPacket (fun _ => .done
          ⟨⟨second.continuation.1, by
            obtain ⟨_, same⟩ := actual; cases same
            exact second.continuation.2.trans (congrArg right.preservation.forward.map first.continuation.2)⟩,
            second.reader, second.limited⟩))))

def transBackward {formula : Cnf} {selected : Var} {source middle target}
    (left : ExecutablePreservation formula selected source middle)
    (right : ExecutablePreservation formula selected middle target)
    (actual : Actual (left.preservation.trans right.preservation))
    (input : FrontierContinuation (generatedStructuralBranchSystem formula) target)
    (budget : Nat) (reader : Reader (frontierAssignment (formula := formula) (frontier := target) input)) (limited : reader.queryBound selected ≤ budget) :
    Code Label (Applied (formula := formula) (frontier := source) selected (actual.1.backward.map input)
      (left.backwardReaderBound (right.backwardReaderBound budget))) :=
  .step .transportApplicationCell (fun _ =>
    (right.backward input budget reader limited).bind (fun first =>
      (left.backward first.continuation.1 (right.backwardReaderBound budget) first.reader first.limited).bind (fun second =>
        .step .transportApplicationPacket (fun _ => .done
          ⟨⟨second.continuation.1, by
            obtain ⟨_, same⟩ := actual; cases same
            exact second.continuation.2.trans (congrArg left.preservation.backward.map first.continuation.2)⟩,
            second.reader, second.limited⟩))))

theorem trans_forward_bounded {formula : Cnf} {selected : Var} {source middle target}
    (left : ExecutablePreservation formula selected source middle)
    (right : ExecutablePreservation formula selected middle target)
    (actual : Actual (left.preservation.trans right.preservation))
    (input : FrontierContinuation (generatedStructuralBranchSystem formula) source)
    (budget : Nat) (reader : Reader (frontierAssignment (formula := formula) (frontier := source) input)) (limited : reader.queryBound selected ≤ budget) :
    Within (transForward left right actual input budget reader limited)
      ((left.forwardCost budget + (right.forwardCost (left.forwardReaderBound budget) + 1)) + 1) := by
  apply within_step
  apply within_bind (left.forward_bounded _ _ _ _); intro first
  apply within_bind (right.forward_bounded _ _ _ _); intro second
  exact within_step _ _ (within_done _)

theorem trans_backward_bounded {formula : Cnf} {selected : Var} {source middle target}
    (left : ExecutablePreservation formula selected source middle)
    (right : ExecutablePreservation formula selected middle target)
    (actual : Actual (left.preservation.trans right.preservation))
    (input : FrontierContinuation (generatedStructuralBranchSystem formula) target)
    (budget : Nat) (reader : Reader (frontierAssignment (formula := formula) (frontier := target) input)) (limited : reader.queryBound selected ≤ budget) :
    Within (transBackward left right actual input budget reader limited)
      ((right.backwardCost budget + (left.backwardCost (right.backwardReaderBound budget) + 1)) + 1) := by
  apply within_step
  apply within_bind (right.backward_bounded _ _ _ _); intro first
  apply within_bind (left.backward_bounded _ _ _ _); intro second
  exact within_step _ _ (within_done _)

def transCode {formula : Cnf} {selected : Var} {source middle target}
    (left : ExecutablePreservation formula selected source middle)
    (right : ExecutablePreservation formula selected middle target) :
    Code Label (Formed selected (left.preservation.trans right.preservation)) :=
  (ControlFrontierOpening.transCode left.preservation right.preservation).bind (fun actual =>
    .step .executionPayload (fun _ => .step .controlClosure (fun _ =>
      let forward := transForward left right actual
      .step .controlClosure (fun _ =>
        let backward := transBackward left right actual
        .step .formationResources (fun _ => .done
          ⟨⟨actual.1,
            fun budget => (left.forwardCost budget + (right.forwardCost (left.forwardReaderBound budget) + 1)) + 1,
            fun budget => (right.backwardCost budget + (left.backwardCost (right.backwardReaderBound budget) + 1)) + 1,
            fun budget => right.forwardReaderBound (left.forwardReaderBound budget),
            fun budget => left.backwardReaderBound (right.backwardReaderBound budget),
            forward, backward, trans_forward_bounded left right actual, trans_backward_bounded left right actual⟩,
            actual.2⟩)))))

theorem trans_bounded {formula : Cnf} {selected : Var} {source middle target}
    (left : ExecutablePreservation formula selected source middle)
    (right : ExecutablePreservation formula selected middle target) :
    Within (transCode left right) (3 + 4) := by
  apply within_bind (ControlFrontierOpening.trans_bounded _ _); intro actual
  repeat apply within_step
  exact within_done _

end ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierApplication

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierApplication.reader_max_left
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierApplication.reader_max_right
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierApplication.swapApplication
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierApplication.swap_application_bounded
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierApplication.swapCode
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierApplication.swap_bounded
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierApplication.prependForward
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierApplication.prependBackward
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierApplication.prepend_forward_bounded
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierApplication.prepend_backward_bounded
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierApplication.prependCode
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierApplication.prepend_bounded
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierApplication.transForward
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierApplication.transBackward
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierApplication.trans_forward_bounded
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierApplication.trans_backward_bounded
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierApplication.transCode
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierApplication.trans_bounded
/- AXIOM_AUDIT_END -/
