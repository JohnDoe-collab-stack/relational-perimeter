import Tests.LocalAlignment.DocumentaryControlFrontierApplicationComposition

/-! Flip applications form the original complete structural continuation and
its executable reader together. Backward absorption is the original inclusion;
it never applies an inverse flip. Reader applications remain individually paid.
The directed relation and the actual transport formed from it are shared. -/
set_option genInjectivity false
set_option backward.match.sparseCases false
set_option maxHeartbeats 10000000
namespace ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierApplication
open SAT Selection Control ControlBindings ControlMasterData ControlAssignmentApplication

structure BranchApplied {formula : Cnf} (selected : Var) {target : GeneratedStructuralBranchContext formula}
    (expected : GeneratedStructuralBranchContinuation target) (ceiling : Nat) where
  continuation : Actual expected
  reader : Reader continuation.1.1
  limited : reader.queryBound selected ≤ ceiling

def flipContinuationCode {formula : Cnf} (selected : Var)
    {source target : GeneratedStructuralBranchContext formula}
    (relation : GeneratedStructuralFlipAtRelation selected source target)
    (actual : Actual relation.toAcceptingTransport)
    (input : GeneratedStructuralBranchContinuation source)
    (budget : Nat) (reader : Reader input.1) (limited : reader.queryBound selected ≤ budget) :
    Code Label (BranchApplied selected (actual.1.map input) (flipEnvelope selected budget)) :=
  .step .controlClosure (fun _ =>
    let assignment : Assignment := fun query =>
      if query = selected then !(input.1 query) else input.1 query
    .step .formationWitness (fun _ =>
      let produced : Actual (actual.1.map input) :=
        ⟨⟨assignment, (relation.mapContinuation input).2⟩, by
          obtain ⟨_, same⟩ := actual; cases same; rfl⟩
      (flipReaderCode selected reader).bind (fun executable =>
        .done ⟨produced, executable.1, by
          rw [executable.2]
          exact flip_query_envelope selected reader budget limited⟩)))

theorem flip_continuation_bounded {formula : Cnf} (selected : Var)
    {source target : GeneratedStructuralBranchContext formula}
    (relation : GeneratedStructuralFlipAtRelation selected source target)
    (actual : Actual relation.toAcceptingTransport)
    (input : GeneratedStructuralBranchContinuation source)
    (budget : Nat) (reader : Reader input.1) (limited : reader.queryBound selected ≤ budget) :
    Within (flipContinuationCode selected relation actual input budget reader limited) 5 := by
  apply within_step; apply within_step
  exact within_bind (flip_reader_bounded selected reader) (fun executable => within_done _)

theorem budget_le_flip (selected : Var) (budget : Nat) : budget ≤ flipEnvelope selected budget :=
  Nat.le_trans (Nat.le_add_right budget 1)
    (Nat.le_trans (Nat.le_add_left (budget + 1) (ControlFrontierSyntax.equalBound selected)) (Nat.le_add_right _ 1))

def absorbFirstForward {formula : Cnf} (selected : Var)
    {first second : GeneratedStructuralBranchContext formula} {rest : List (GeneratedStructuralBranchContext formula)}
    (relation : GeneratedStructuralFlipAtRelation selected first second)
    (transport : Actual relation.toAcceptingTransport)
    (actual : Actual (AcceptedFrontierPreservation.absorbFirstIntoSecond (rest := rest) transport.1))
    (input : FrontierContinuation (generatedStructuralBranchSystem formula) (first :: second :: rest))
    (budget : Nat) (reader : Reader (frontierAssignment (formula := formula) (frontier := first :: second :: rest) input))
    (limited : reader.queryBound selected ≤ budget) :
    Code Label (Applied (formula := formula) (frontier := second :: rest) selected (actual.1.forward.map input) (flipEnvelope selected budget)) :=
  .step .transportApplicationCell (fun _ => (match (motive := (input : FrontierContinuation (generatedStructuralBranchSystem formula) (first :: second :: rest)) →
      (reader : Reader (frontierAssignment (formula := formula) (frontier := first :: second :: rest) input)) →
      reader.queryBound selected ≤ budget → Code Label (Applied (formula := formula) (frontier := second :: rest)
        selected (actual.1.forward.map input) (flipEnvelope selected budget))) input with
    | .head received => fun reader limited => (flipContinuationCode selected relation transport received budget reader limited).bind (fun output =>
        .step .transportApplicationPacket (fun _ =>
          let produced : Actual (actual.1.forward.map (.head received)) :=
            ⟨.head output.continuation.1, by
              obtain ⟨_, same⟩ := actual; cases same
              exact congrArg FrontierCompletion.head output.continuation.2⟩
          .done ⟨produced, output.reader, output.limited⟩))
    | .tail received => fun reader limited => .step .transportApplicationPacket (fun _ =>
        let produced : Actual (actual.1.forward.map (.tail received)) :=
          ⟨received, by obtain ⟨_, same⟩ := actual; cases same; rfl⟩
        .done ⟨produced, reader, Nat.le_trans limited (budget_le_flip selected budget)⟩)) reader limited)

def absorbFirstBackward {formula : Cnf} (selected : Var)
    {first second : GeneratedStructuralBranchContext formula} {rest : List (GeneratedStructuralBranchContext formula)}
    (transport : AcceptingContinuationTransport (generatedStructuralBranchSystem formula) first second)
    (actual : Actual (AcceptedFrontierPreservation.absorbFirstIntoSecond (rest := rest) transport))
    (input : FrontierContinuation (generatedStructuralBranchSystem formula) (second :: rest))
    (budget : Nat) (reader : Reader (frontierAssignment (formula := formula) (frontier := second :: rest) input))
    (limited : reader.queryBound selected ≤ budget) :
    Code Label (Applied (formula := formula) (frontier := first :: second :: rest) selected (actual.1.backward.map input) budget) :=
  .step .transportApplicationCell (fun _ => .step .transportApplicationPacket (fun _ =>
    let produced : Actual (actual.1.backward.map input) :=
      ⟨.tail input, by obtain ⟨_, same⟩ := actual; cases same; rfl⟩
    .done ⟨produced, reader, limited⟩))

theorem absorb_first_forward_bounded {formula : Cnf} (selected : Var)
    {first second : GeneratedStructuralBranchContext formula} {rest : List (GeneratedStructuralBranchContext formula)}
    (relation : GeneratedStructuralFlipAtRelation selected first second)
    (transport : Actual relation.toAcceptingTransport)
    (actual : Actual (AcceptedFrontierPreservation.absorbFirstIntoSecond (rest := rest) transport.1))
    (input : FrontierContinuation (generatedStructuralBranchSystem formula) (first :: second :: rest))
    (budget : Nat) (reader : Reader (frontierAssignment (formula := formula) (frontier := first :: second :: rest) input))
    (limited : reader.queryBound selected ≤ budget) :
    Within (absorbFirstForward selected relation transport actual input budget reader limited) 7 := by
  revert reader limited
  cases input with
  | head received =>
      intro reader limited
      dsimp only [absorbFirstForward]
      apply within_step
      apply within_bind (more := 1) (flip_continuation_bounded selected relation transport received budget reader limited)
      intro output
      exact within_step _ _ (within_done _)
  | tail received =>
      intro reader limited
      dsimp only [absorbFirstForward]
      apply within_step
      apply within_weaken (bound := 1) (more := 6) (increase := by decide)
      exact within_step _ _ (within_done _)

theorem absorb_first_backward_bounded {formula : Cnf} (selected : Var)
    {first second : GeneratedStructuralBranchContext formula} {rest : List (GeneratedStructuralBranchContext formula)}
    (transport : AcceptingContinuationTransport (generatedStructuralBranchSystem formula) first second)
    (actual : Actual (AcceptedFrontierPreservation.absorbFirstIntoSecond (rest := rest) transport))
    (input : FrontierContinuation (generatedStructuralBranchSystem formula) (second :: rest))
    (budget : Nat) (reader : Reader (frontierAssignment (formula := formula) (frontier := second :: rest) input))
    (limited : reader.queryBound selected ≤ budget) :
    Within (absorbFirstBackward selected transport actual input budget reader limited) 2 :=
  within_step _ _ (within_step _ _ (within_done _))

def absorbFirstCode {formula : Cnf} (selected : Var)
    {first second : GeneratedStructuralBranchContext formula} {rest : List (GeneratedStructuralBranchContext formula)}
    (relation : GeneratedStructuralFlipAtRelation selected first second) :
    Code Label (Formed selected (AcceptedFrontierPreservation.absorbFirstIntoSecond (rest := rest) relation.toAcceptingTransport)) :=
  (ControlFrontierEvaluation.transportCode selected relation).bind (fun transport =>
    (ControlFrontierEvaluation.absorbFirstCode (rest := rest) transport.1).bind (fun actual =>
      .step .executionPayload (fun _ => .step .controlClosure (fun _ =>
        let forward := absorbFirstForward selected relation transport actual
        .step .controlClosure (fun _ =>
          let backward := absorbFirstBackward selected transport.1 actual
          .step .formationResources (fun _ => .done
            ⟨⟨actual.1, fun _ => 7, fun _ => 2, flipEnvelope selected, id, forward, backward,
              absorb_first_forward_bounded selected relation transport actual, absorb_first_backward_bounded selected transport.1 actual⟩,
              by
                change actual.1 = _
                exact actual.2.trans (congrArg (AcceptedFrontierPreservation.absorbFirstIntoSecond (rest := rest)) transport.2)⟩))))))

theorem absorb_first_bounded {formula : Cnf} (selected : Var)
    {first second : GeneratedStructuralBranchContext formula} {rest : List (GeneratedStructuralBranchContext formula)}
    (relation : GeneratedStructuralFlipAtRelation selected first second) :
    Within (absorbFirstCode selected (rest := rest) relation) (3 + (3 + 4)) := by
  apply within_bind (ControlFrontierEvaluation.transport_bounded selected relation); intro transport
  apply within_bind (ControlFrontierEvaluation.absorb_first_bounded transport.1); intro actual
  repeat apply within_step
  exact within_done _

def absorbSecondForward {formula : Cnf} (selected : Var)
    {first second : GeneratedStructuralBranchContext formula} {rest : List (GeneratedStructuralBranchContext formula)}
    (relation : GeneratedStructuralFlipAtRelation selected second first)
    (transport : Actual relation.toAcceptingTransport)
    (actual : Actual (AcceptedFrontierPreservation.absorbSecondIntoFirst (rest := rest) transport.1))
    (input : FrontierContinuation (generatedStructuralBranchSystem formula) (first :: second :: rest))
    (budget : Nat) (reader : Reader (frontierAssignment (formula := formula) (frontier := first :: second :: rest) input))
    (limited : reader.queryBound selected ≤ budget) :
    Code Label (Applied (formula := formula) (frontier := first :: rest) selected (actual.1.forward.map input) (flipEnvelope selected budget)) :=
  .step .transportApplicationCell (fun _ => (match (motive := (input : FrontierContinuation (generatedStructuralBranchSystem formula) (first :: second :: rest)) →
      (reader : Reader (frontierAssignment (formula := formula) (frontier := first :: second :: rest) input)) →
      reader.queryBound selected ≤ budget → Code Label (Applied (formula := formula) (frontier := first :: rest)
        selected (actual.1.forward.map input) (flipEnvelope selected budget))) input with
    | .head received => fun reader limited => .step .transportApplicationPacket (fun _ =>
        let produced : Actual (actual.1.forward.map (.head received)) :=
          ⟨.head received, by obtain ⟨_, same⟩ := actual; cases same; rfl⟩
        .done ⟨produced, reader, Nat.le_trans limited (budget_le_flip selected budget)⟩)
    | .tail tail => fun reader limited => .step .transportApplicationCell (fun _ => (match (motive := (tail : FrontierContinuation (generatedStructuralBranchSystem formula) (second :: rest)) →
        (reader : Reader (frontierAssignment (formula := formula) (frontier := second :: rest) tail)) →
        reader.queryBound selected ≤ budget → Code Label (Applied (formula := formula) (frontier := first :: rest)
          selected (actual.1.forward.map (.tail tail)) (flipEnvelope selected budget))) tail with
      | .head received => fun reader limited => (flipContinuationCode selected relation transport received budget reader limited).bind (fun output =>
          .step .transportApplicationPacket (fun _ =>
            let produced : Actual (actual.1.forward.map (.tail (.head received))) :=
              ⟨.head output.continuation.1, by
                obtain ⟨_, same⟩ := actual; cases same
                exact congrArg FrontierCompletion.head output.continuation.2⟩
            .done ⟨produced, output.reader, output.limited⟩))
      | .tail received => fun reader limited => .step .transportApplicationPacket (fun _ =>
          let produced : Actual (actual.1.forward.map (.tail (.tail received))) :=
            ⟨.tail received, by obtain ⟨_, same⟩ := actual; cases same; rfl⟩
          .done ⟨produced, reader, Nat.le_trans limited (budget_le_flip selected budget)⟩)) reader limited)) reader limited)

def absorbSecondBackward {formula : Cnf} (selected : Var)
    {first second : GeneratedStructuralBranchContext formula} {rest : List (GeneratedStructuralBranchContext formula)}
    (transport : AcceptingContinuationTransport (generatedStructuralBranchSystem formula) second first)
    (actual : Actual (AcceptedFrontierPreservation.absorbSecondIntoFirst (rest := rest) transport))
    (input : FrontierContinuation (generatedStructuralBranchSystem formula) (first :: rest))
    (budget : Nat) (reader : Reader (frontierAssignment (formula := formula) (frontier := first :: rest) input))
    (limited : reader.queryBound selected ≤ budget) :
    Code Label (Applied (formula := formula) (frontier := first :: second :: rest) selected (actual.1.backward.map input) budget) :=
  .step .transportApplicationCell (fun _ => match input with
    | .head received => .step .transportApplicationPacket (fun _ =>
        let produced : Actual (actual.1.backward.map (.head received)) :=
          ⟨.head received, by obtain ⟨_, same⟩ := actual; cases same; rfl⟩
        .done ⟨produced, reader, limited⟩)
    | .tail received => .step .transportApplicationPacket (fun _ =>
        let produced : Actual (actual.1.backward.map (.tail received)) :=
          ⟨.tail (.tail received), by obtain ⟨_, same⟩ := actual; cases same; rfl⟩
        .done ⟨produced, reader, limited⟩))

theorem absorb_second_forward_bounded {formula : Cnf} (selected : Var)
    {first second : GeneratedStructuralBranchContext formula} {rest : List (GeneratedStructuralBranchContext formula)}
    (relation : GeneratedStructuralFlipAtRelation selected second first)
    (transport : Actual relation.toAcceptingTransport)
    (actual : Actual (AcceptedFrontierPreservation.absorbSecondIntoFirst (rest := rest) transport.1))
    (input : FrontierContinuation (generatedStructuralBranchSystem formula) (first :: second :: rest))
    (budget : Nat) (reader : Reader (frontierAssignment (formula := formula) (frontier := first :: second :: rest) input))
    (limited : reader.queryBound selected ≤ budget) :
    Within (absorbSecondForward selected relation transport actual input budget reader limited) 8 := by
  revert reader limited
  cases input with
  | head received =>
      intro reader limited
      dsimp only [absorbSecondForward]
      apply within_step
      apply within_weaken (bound := 1) (more := 7) (increase := by decide)
      exact within_step _ _ (within_done _)
  | tail tail =>
      cases tail with
      | head received =>
          intro reader limited
          dsimp only [absorbSecondForward]
          apply within_step; apply within_step
          apply within_bind (more := 1) (flip_continuation_bounded selected relation transport received budget reader limited)
          intro output
          exact within_step _ _ (within_done _)
      | tail received =>
          intro reader limited
          dsimp only [absorbSecondForward]
          apply within_step; apply within_step
          apply within_weaken (bound := 1) (more := 6) (increase := by decide)
          exact within_step _ _ (within_done _)

theorem absorb_second_backward_bounded {formula : Cnf} (selected : Var)
    {first second : GeneratedStructuralBranchContext formula} {rest : List (GeneratedStructuralBranchContext formula)}
    (transport : AcceptingContinuationTransport (generatedStructuralBranchSystem formula) second first)
    (actual : Actual (AcceptedFrontierPreservation.absorbSecondIntoFirst (rest := rest) transport))
    (input : FrontierContinuation (generatedStructuralBranchSystem formula) (first :: rest))
    (budget : Nat) (reader : Reader (frontierAssignment (formula := formula) (frontier := first :: rest) input))
    (limited : reader.queryBound selected ≤ budget) :
    Within (absorbSecondBackward selected transport actual input budget reader limited) 2 := by
  apply within_step; cases input <;> exact within_step _ _ (within_done _)

def absorbSecondCode {formula : Cnf} (selected : Var)
    {first second : GeneratedStructuralBranchContext formula} {rest : List (GeneratedStructuralBranchContext formula)}
    (relation : GeneratedStructuralFlipAtRelation selected second first) :
    Code Label (Formed selected (AcceptedFrontierPreservation.absorbSecondIntoFirst (rest := rest) relation.toAcceptingTransport)) :=
  (ControlFrontierEvaluation.transportCode selected relation).bind (fun transport =>
    (ControlFrontierEvaluation.absorbSecondCode (rest := rest) transport.1).bind (fun actual =>
      .step .executionPayload (fun _ => .step .controlClosure (fun _ =>
        let forward := absorbSecondForward selected relation transport actual
        .step .controlClosure (fun _ =>
          let backward := absorbSecondBackward selected transport.1 actual
          .step .formationResources (fun _ => .done
            ⟨⟨actual.1, fun _ => 8, fun _ => 2, flipEnvelope selected, id, forward, backward,
              absorb_second_forward_bounded selected relation transport actual, absorb_second_backward_bounded selected transport.1 actual⟩,
              by
                change actual.1 = _
                exact actual.2.trans (congrArg (AcceptedFrontierPreservation.absorbSecondIntoFirst (rest := rest)) transport.2)⟩))))))

theorem absorb_second_bounded {formula : Cnf} (selected : Var)
    {first second : GeneratedStructuralBranchContext formula} {rest : List (GeneratedStructuralBranchContext formula)}
    (relation : GeneratedStructuralFlipAtRelation selected second first) :
    Within (absorbSecondCode selected (rest := rest) relation) (3 + (3 + 4)) := by
  apply within_bind (ControlFrontierEvaluation.transport_bounded selected relation); intro transport
  apply within_bind (ControlFrontierEvaluation.absorb_second_bounded transport.1); intro actual
  repeat apply within_step
  exact within_done _

end ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierApplication

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierApplication.BranchApplied
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierApplication.flipContinuationCode
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierApplication.flip_continuation_bounded
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierApplication.budget_le_flip
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierApplication.absorbFirstForward
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierApplication.absorbFirstBackward
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierApplication.absorb_first_forward_bounded
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierApplication.absorb_first_backward_bounded
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierApplication.absorbFirstCode
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierApplication.absorb_first_bounded
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierApplication.absorbSecondForward
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierApplication.absorbSecondBackward
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierApplication.absorb_second_forward_bounded
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierApplication.absorb_second_backward_bounded
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierApplication.absorbSecondCode
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierApplication.absorb_second_bounded
/- AXIOM_AUDIT_END -/
