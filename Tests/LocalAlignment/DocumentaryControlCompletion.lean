import Tests.LocalAlignment.DocumentaryControlCitation

/-! Open the actual retained continuation and completion. Routing and assignment
application remain named complex primitives. Bounds count the declared catalogue;
computing those bounds is a separate bootstrap obligation. -/
set_option genInjectivity false
set_option maxHeartbeats 3000000
namespace ConstitutiveSearch.Agent.Local.Documentary.ControlCompletion
open Resources SAT Selection Control ControlBindings EndogenousDecomposition
universe uRelation

abbrev AssignmentRead {formula : Cnf} {frontier : List (GeneratedStructuralBranchContext formula)}
    (continuation : FrontierContinuation (generatedStructuralBranchSystem formula) frontier) :=
  {assignment : Assignment // assignment = frontierAssignment continuation}

def assignmentCode {formula : Cnf} {frontier : List (GeneratedStructuralBranchContext formula)}
    (continuation : FrontierContinuation (generatedStructuralBranchSystem formula) frontier) :
    Code Label (AssignmentRead continuation) :=
  .step .citationContinuationCell (fun _ => match continuation with
    | .head received => .done ⟨received.1, rfl⟩
    | .tail rest => assignmentCode rest)

def assignmentBound {formula : Cnf} {frontier : List (GeneratedStructuralBranchContext formula)} :
    FrontierContinuation (generatedStructuralBranchSystem formula) frontier → Nat
  | .head _ => 1
  | .tail rest => assignmentBound rest + 1

theorem assignment_bounded {formula : Cnf} {frontier : List (GeneratedStructuralBranchContext formula)}
    (continuation : FrontierContinuation (generatedStructuralBranchSystem formula) frontier) :
    Within (assignmentCode continuation) (assignmentBound continuation) := by
  induction continuation with
  | head received => exact within_step _ _ (within_done _)
  | tail rest previous => exact within_step _ _ previous

abbrev Completion {context cursor sources contract demand left right}
    (stage : @Master.Stage context cursor sources contract demand left right) (memory : Memory sources contract)
    (continuation : FrontierContinuation (generatedStructuralBranchSystem stage.formula) stage.reduction.retained)
    (accepted : FrontierAccept (generatedStructuralBranchSystem stage.formula) stage.reduction.retained continuation) :=
  {packet : Master.Completion stage memory // packet = Master.complete stage memory continuation accepted}

def completeCode {context cursor sources contract demand left right}
    (stage : @Master.Stage context cursor sources contract demand left right) (memory : Memory sources contract)
    (continuation : FrontierContinuation (generatedStructuralBranchSystem stage.formula) stage.reduction.retained)
    (accepted : FrontierAccept (generatedStructuralBranchSystem stage.formula) stage.reduction.retained continuation) :
    Code Label (Completion stage memory continuation accepted) :=
  (assignmentCode continuation).bind (fun assignment =>
    .step .citationAssignment (fun _ =>
      let bit : {bit : Bool // bit = assignment.1 (VariableMaster.selected stage.head)} :=
        ⟨assignment.1 (VariableMaster.selected stage.head), rfl⟩
      .step .citationCandidate (fun _ =>
        have rootAccepted : Satisfies assignment.1 stage.formula :=
          assignment.2.symm ▸ frontier_root_accept continuation accepted
        let candidate := stage.candidateFromBit assignment.1 rootAccepted bit
        have candidateActual : candidate = stage.candidate (frontierAssignment continuation)
            (frontier_root_accept continuation accepted) := by
          obtain ⟨assignment, same⟩ := assignment
          cases same
          exact stage.candidateFromBit_actual _ _ bit
        (ControlCitation.extractCode sources candidate.origin).bind (fun action =>
          (ControlCitation.readoutCode action.1).bind (fun readout =>
            .step .citationAuthorize (fun _ =>
              let output := authorizeFromCitation contract action.1 candidate.permission readout.1 readout.2
              have outputActual := authorizeFromCitation_actual contract action.1 candidate.permission readout.1 readout.2
              .step .citationIncorporate (fun _ =>
                let result := incorporate memory output
                .step .citationCompletion (fun _ => .done
                  ⟨Master.completionFromParts stage memory continuation accepted candidate candidateActual
                    action.1 action.2 output outputActual result rfl,
                    Master.completionFromParts_actual stage memory continuation accepted candidate candidateActual
                      action.1 action.2 output outputActual result rfl⟩))))))))

def completeBound {context cursor sources contract demand left right}
    (stage : @Master.Stage context cursor sources contract demand left right) (memory : Memory sources contract)
    (continuation : FrontierContinuation (generatedStructuralBranchSystem stage.formula) stage.reduction.retained)
    (accepted : FrontierAccept (generatedStructuralBranchSystem stage.formula) stage.reduction.retained continuation) : Nat :=
  let _ := memory
  let candidate := stage.candidate (frontierAssignment continuation) (frontier_root_accept continuation accepted)
  assignmentBound continuation +
    ((ControlCitation.extractBound sources candidate.origin +
      (ControlCitation.readoutBound (extract sources candidate.origin) + 3)) + 2)

theorem complete_bounded {context cursor sources contract demand left right}
    (stage : @Master.Stage context cursor sources contract demand left right) (memory : Memory sources contract)
    (continuation : FrontierContinuation (generatedStructuralBranchSystem stage.formula) stage.reduction.retained)
    (accepted : FrontierAccept (generatedStructuralBranchSystem stage.formula) stage.reduction.retained continuation) :
    Within (completeCode stage memory continuation accepted) (completeBound stage memory continuation accepted) := by
  apply within_bind (assignment_bounded continuation)
  intro assignment
  obtain ⟨assignment, actualAssignment⟩ := assignment
  cases actualAssignment
  apply within_step; apply within_step
  apply within_bind (ControlCitation.extract_bounded _ _)
  intro action
  apply within_bind (ControlCitation.readout_bounded action.1)
  intro readout
  apply within_step; apply within_step; apply within_step
  exact within_done _

abbrev Decision {context cursor sources contract demand left right}
    (stage : @Master.Stage context cursor sources contract demand left right) (memory : Memory sources contract) :=
  {decision : Master.Decision stage memory // decision = Master.decide stage memory}

def decideCode {context cursor sources contract demand left right}
    (stage : @Master.Stage context cursor sources contract demand left right) (memory : Memory sources contract) :
    Code Label (Decision stage memory) :=
  .step .citationSeed (fun _ =>
    match found : seed (VariableMaster.selected stage.head) stage.leftCheck.flag stage.rightCheck.flag with
    | .blocked impossible => .step .citationDecision (fun _ => .done
        ⟨.blocked
          (fun permission meets => impossible false (stage.leftCheck.complete permission meets))
          (fun permission meets => impossible true (stage.rightCheck.complete permission meets)), by
            unfold Master.decide
            rw [found]⟩)
    | .viable assignment accepted =>
      .step .citationInput (fun _ =>
        let input : FrontierContinuation (generatedStructuralBranchSystem stage.formula)
            [GeneratedStructuralBranchContext.root stage.formula] := .head ⟨assignment, True.intro⟩
        .step .citationPreservation (fun _ =>
          let preservation := stage.preservation
          .step .citationRouting (fun _ =>
            let retained := preservation.forward.map input
            let retainedAccepted := preservation.forward.preservesAccept input accepted
            (completeCode stage memory retained retainedAccepted).bind (fun packet =>
              .step .citationDecision (fun _ => .done ⟨.complete packet.1, by
                unfold Master.decide
                rw [found]
                exact congrArg Master.Decision.complete packet.2⟩))))))

def decideBound {context cursor sources contract demand left right}
    (stage : @Master.Stage context cursor sources contract demand left right) (memory : Memory sources contract) : Nat :=
  match seed (VariableMaster.selected stage.head) stage.leftCheck.flag stage.rightCheck.flag with
  | .blocked _ => 2
  | .viable assignment accepted =>
      let input : FrontierContinuation (generatedStructuralBranchSystem stage.formula)
          [GeneratedStructuralBranchContext.root stage.formula] := .head ⟨assignment, True.intro⟩
      let retained := stage.preservation.forward.map input
      let retainedAccepted := stage.preservation.forward.preservesAccept input accepted
      (completeBound stage memory retained retainedAccepted + 1) + 4

theorem decide_bounded {context cursor sources contract demand left right}
    (stage : @Master.Stage context cursor sources contract demand left right) (memory : Memory sources contract) :
    Within (decideCode stage memory) (decideBound stage memory) := by
  unfold decideCode decideBound
  split
  · rename_i impossible found
    conv => arg 2; rw [found]
    apply within_step; apply within_step
    exact within_done _
  · rename_i assignment accepted found
    conv => arg 2; rw [found]
    apply within_step; apply within_step; apply within_step; apply within_step
    apply within_bind (complete_bounded _ _ _ _)
    intro packet
    exact within_step _ _ (within_done _)

/-- Structural width bounds are proved from the executed normalization algorithm;
the driver does not run that algorithm to discover its fuel allocation. -/
theorem insertion_length {system : SearchSystem}
    {Relation : system.State → system.State → Type uRelation}
    (search : RelationSearch Relation) (action : AcceptedRelationalAction system Relation)
    (state : system.State) (rest : List system.State) (irreducible : SearchIrreducible search rest) :
    (insertAcceptedIntoIrreducible search action state rest irreducible).retained.length ≤ rest.length + 1 := by
  induction rest with
  | nil => exact Nat.le_refl _
  | cons current tail previous =>
      dsimp only [insertAcceptedIntoIrreducible]
      split
      · exact Nat.le_succ _
      · exact Nat.le_succ _
      · exact Nat.le_trans (previous irreducible.2) (Nat.le_succ _)
      · exact Nat.succ_le_succ (previous irreducible.2)

theorem normalization_length {system : SearchSystem}
    {Relation : system.State → system.State → Type uRelation}
    (search : RelationSearch Relation) (action : AcceptedRelationalAction system Relation)
    (source : List system.State) :
    (normalizeAcceptedFrontier search action source).retained.length ≤ source.length := by
  induction source with
  | nil => exact Nat.le_refl _
  | cons state tail previous =>
      exact Nat.le_trans (insertion_length search action state _ _)
        (Nat.succ_le_succ previous)

theorem retained_length {context cursor sources contract demand left right}
    (stage : @Master.Stage context cursor sources contract demand left right) :
    stage.reduction.retained.length ≤ 2 := by
  have openingLength : stage.opening.frontier.length = 2 := by
    rw [stage.openingExact]
    rfl
  rw [stage.reductionExact]
  exact Nat.le_trans (normalization_length
    (generatedStructuralFlipAtSearch stage.formula (VariableMaster.selected stage.head))
    (generatedStructuralFlipAtAction stage.formula (VariableMaster.selected stage.head)) stage.opening.frontier)
    (Nat.le_of_eq openingLength)

theorem assignment_le_frontier {formula : Cnf} {frontier : List (GeneratedStructuralBranchContext formula)}
    (continuation : FrontierContinuation (generatedStructuralBranchSystem formula) frontier) :
    assignmentBound continuation ≤ frontier.length := by
  induction continuation with
  | head received => exact Nat.succ_le_succ (Nat.zero_le _)
  | tail rest previous => exact Nat.succ_le_succ previous

theorem checked_origin {context sources contract demand origin}
    (checked : @Checked context sources contract demand origin) (accepted : checked.flag = true) :
    (checked.candidate accepted).origin = origin := by
  cases checked with
  | permitted permission meets => rfl
  | rejected absent => cases accepted

theorem candidateFromBit_origin {context cursor sources contract demand left right}
    (stage : @Master.Stage context cursor sources contract demand left right)
    (assignment : Assignment) (accepted : Satisfies assignment stage.formula)
    (bit : Bool) (actual : bit = assignment (VariableMaster.selected stage.head)) :
    (stage.candidateFromBit assignment accepted ⟨bit, actual⟩).origin = left ∨
      (stage.candidateFromBit assignment accepted ⟨bit, actual⟩).origin = right := by
  unfold Master.Stage.candidateFromBit
  dsimp only
  cases bit
  · exact Or.inl (checked_origin _ _)
  · exact Or.inr (checked_origin _ _)

theorem candidate_origin {context cursor sources contract demand left right}
    (stage : @Master.Stage context cursor sources contract demand left right)
    (assignment : Assignment) (accepted : Satisfies assignment stage.formula) :
    (stage.candidate assignment accepted).origin = left ∨
      (stage.candidate assignment accepted).origin = right := by
  have origin := candidateFromBit_origin stage assignment accepted
    (assignment (VariableMaster.selected stage.head)) rfl
  rw [stage.candidateFromBit_actual] at origin
  exact origin

def sourceWorkBound {context} (origin : Location context) : Nat :=
  ((origin.2.position + 1 + 4) + 1) + (ControlReference.positionBound origin.2 + 2)

/-- A conservative envelope from both received references, without seed, routing,
candidate, extraction or whole search evaluation. Its bootstrap is still D3. -/
def pairBound {context} (left right : Location context) : Nat :=
  sourceWorkBound left + sourceWorkBound right + 12

theorem complete_cost_le {context cursor sources contract demand left right}
    (stage : @Master.Stage context cursor sources contract demand left right) (memory : Memory sources contract)
    (continuation : FrontierContinuation (generatedStructuralBranchSystem stage.formula) stage.reduction.retained)
    (accepted : FrontierAccept (generatedStructuralBranchSystem stage.formula) stage.reduction.retained continuation) :
    completeBound stage memory continuation accepted + 5 ≤ pairBound left right := by
  have pathBound := Nat.le_trans (assignment_le_frontier continuation) (retained_length stage)
  have originBound : sourceWorkBound (stage.candidate (frontierAssignment continuation)
      (frontier_root_accept continuation accepted)).origin ≤ sourceWorkBound left + sourceWorkBound right := by
    cases candidate_origin stage (frontierAssignment continuation) (frontier_root_accept continuation accepted) with
    | inl actual => rw [actual]; exact Nat.le_add_right _ _
    | inr actual => rw [actual]; exact Nat.le_add_left _ _
  calc
    completeBound stage memory continuation accepted + 5 = assignmentBound continuation +
        sourceWorkBound (stage.candidate (frontierAssignment continuation)
          (frontier_root_accept continuation accepted)).origin + 10 := by
      dsimp only [completeBound, ControlCitation.extractBound, ControlCitation.readoutBound, sourceWorkBound]
      repeat rw [Nat.add_assoc]
    _ ≤ 2 + (sourceWorkBound left + sourceWorkBound right) + 10 :=
      Nat.add_le_add_right (Nat.add_le_add pathBound originBound) 10
    _ = pairBound left right := by
      unfold pairBound
      rw [Nat.add_comm 2 (sourceWorkBound left + sourceWorkBound right), Nat.add_assoc]

theorem decide_cost_le {context cursor sources contract demand left right}
    (stage : @Master.Stage context cursor sources contract demand left right) (memory : Memory sources contract) :
    decideBound stage memory ≤ pairBound left right := by
  unfold decideBound
  split
  · exact Nat.le_trans (by decide : 2 ≤ 12)
      (Nat.le_add_left 12 (sourceWorkBound left + sourceWorkBound right))
  · rename_i assignment accepted found
    let input : FrontierContinuation (generatedStructuralBranchSystem stage.formula)
        [GeneratedStructuralBranchContext.root stage.formula] := .head ⟨assignment, True.intro⟩
    have bound := complete_cost_le stage memory (stage.preservation.forward.map input)
      (stage.preservation.forward.preservesAccept input accepted)
    dsimp only [input] at bound
    exact bound

theorem pair_bounded {context cursor sources contract demand left right}
    (stage : @Master.Stage context cursor sources contract demand left right) (memory : Memory sources contract) :
    Within (decideCode stage memory) (pairBound left right) :=
  within_weaken (decide_bounded stage memory) (decide_cost_le stage memory)

end ConstitutiveSearch.Agent.Local.Documentary.ControlCompletion

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlCompletion.AssignmentRead
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlCompletion.assignmentCode
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlCompletion.assignmentBound
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlCompletion.assignment_bounded
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlCompletion.Completion
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlCompletion.completeCode
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlCompletion.completeBound
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlCompletion.complete_bounded
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlCompletion.Decision
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlCompletion.decideCode
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlCompletion.decideBound
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlCompletion.decide_bounded
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlCompletion.insertion_length
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlCompletion.normalization_length
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlCompletion.retained_length
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlCompletion.assignment_le_frontier
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlCompletion.checked_origin
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlCompletion.candidateFromBit_origin
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlCompletion.candidate_origin
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlCompletion.sourceWorkBound
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlCompletion.pairBound
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlCompletion.complete_cost_le
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlCompletion.decide_cost_le
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlCompletion.pair_bounded
/- AXIOM_AUDIT_END -/
