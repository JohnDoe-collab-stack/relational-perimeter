import Tests.LocalAlignment.DocumentaryControlFrontierCeilingApplication

/-! Concrete leaves form the original complete preservation, transport and
executor together with their realized ceilings. No arbitrary Formed is enriched
by assuming that its metadata are the identity or a flip. The same actual
preservation/transport/children supply both payloads; no engine is replayed. -/
set_option genInjectivity false
set_option backward.match.sparseCases false
set_option maxHeartbeats 16000000
namespace ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierCeilingApplication
open SAT Selection Control ControlBindings ControlMasterData ControlAssignmentApplication

def swapCode (formula : Cnf) (selected : Var) {first second : GeneratedStructuralBranchContext formula}
    {rest : List (GeneratedStructuralBranchContext formula)} :
    Code Label (Formed selected (AcceptedFrontierPreservation.swapFirstTwo
      (system := generatedStructuralBranchSystem formula) (first := first) (second := second) (rest := rest))) :=
  ControlFrontierEvaluation.swapCode.bind (fun actual =>
    .step .executionPayload (fun _ => .step .controlClosure (fun _ =>
      let forward := ControlFrontierApplication.swapApplication selected
        ⟨actual.1.forward, congrArg AcceptedFrontierPreservation.forward actual.2⟩
      .step .controlClosure (fun _ =>
        let backward := ControlFrontierApplication.swapApplication selected
          ⟨actual.1.backward, congrArg AcceptedFrontierPreservation.backward actual.2⟩
        .step .formationResources (fun _ =>
          let original : ControlFrontierApplication.ExecutablePreservation formula selected
              (first :: second :: rest) (second :: first :: rest) :=
            ControlFrontierCeilingOriginal.assembled
            (actual.1)
            (fun _ => 3)
            (fun _ => 3)
            (id)
            (id)
            (forward)
            (backward)
            (ControlFrontierApplication.swap_application_bounded selected _)
            (ControlFrontierApplication.swap_application_bounded selected _)
          let receivedWhole : Actual (ControlFrontierCeilingOriginal.swap formula selected actual) := ⟨original, rfl⟩
          returnLeafCode receivedWhole.1 .identity .identity (actual.2))))))

theorem swap_finite (formula : Cnf) (selected : Var) {first second : GeneratedStructuralBranchContext formula}
    {rest : List (GeneratedStructuralBranchContext formula)} :
    Finite (swapCode formula selected (first := first) (second := second) (rest := rest)) := by
  apply finite_bind (finite_of_within ControlFrontierEvaluation.swap_bounded); intro actual
  repeat apply finite_step
  exact return_leaf_finite _ _ _ _

def absorbFirstCode {formula : Cnf} (selected : Var)
    {first second : GeneratedStructuralBranchContext formula} {rest : List (GeneratedStructuralBranchContext formula)}
    (relation : GeneratedStructuralFlipAtRelation selected first second) :
    Code Label (Formed selected (AcceptedFrontierPreservation.absorbFirstIntoSecond (rest := rest) relation.toAcceptingTransport)) :=
  (ControlFrontierEvaluation.transportCode selected relation).bind (fun transport =>
    (ControlFrontierEvaluation.absorbFirstCode (rest := rest) transport.1).bind (fun actual =>
      .step .executionPayload (fun _ => .step .controlClosure (fun _ =>
        let forward := ControlFrontierApplication.absorbFirstForward selected relation transport actual
        .step .controlClosure (fun _ =>
          let backward := ControlFrontierApplication.absorbFirstBackward selected transport.1 actual
          .step .formationResources (fun _ =>
          let original : ControlFrontierApplication.ExecutablePreservation formula selected
              (first :: second :: rest) (second :: rest) :=
            ControlFrontierCeilingOriginal.assembled
            (actual.1)
            (fun _ => 7)
            (fun _ => 2)
            (flipEnvelope selected)
            (id)
            (forward)
            (backward)
            (ControlFrontierApplication.absorb_first_forward_bounded selected relation transport actual)
            (ControlFrontierApplication.absorb_first_backward_bounded selected transport.1 actual)
          let receivedWhole : Actual (ControlFrontierCeilingOriginal.absorbFirst selected relation transport actual) := ⟨original, rfl⟩
          returnLeafCode receivedWhole.1 (.flip selected) .identity (by
                change actual.1 = _
                exact actual.2.trans (congrArg (AcceptedFrontierPreservation.absorbFirstIntoSecond (rest := rest)) transport.2))))))))

theorem absorb_first_finite {formula : Cnf} (selected : Var)
    {first second : GeneratedStructuralBranchContext formula} {rest : List (GeneratedStructuralBranchContext formula)}
    (relation : GeneratedStructuralFlipAtRelation selected first second) :
    Finite (absorbFirstCode selected (rest := rest) relation) := by
  apply finite_bind (finite_of_within (ControlFrontierEvaluation.transport_bounded selected relation)); intro transport
  apply finite_bind (finite_of_within (ControlFrontierEvaluation.absorb_first_bounded transport.1)); intro actual
  repeat apply finite_step
  exact return_leaf_finite _ _ _ _

def absorbSecondCode {formula : Cnf} (selected : Var)
    {first second : GeneratedStructuralBranchContext formula} {rest : List (GeneratedStructuralBranchContext formula)}
    (relation : GeneratedStructuralFlipAtRelation selected second first) :
    Code Label (Formed selected (AcceptedFrontierPreservation.absorbSecondIntoFirst (rest := rest) relation.toAcceptingTransport)) :=
  (ControlFrontierEvaluation.transportCode selected relation).bind (fun transport =>
    (ControlFrontierEvaluation.absorbSecondCode (rest := rest) transport.1).bind (fun actual =>
      .step .executionPayload (fun _ => .step .controlClosure (fun _ =>
        let forward := ControlFrontierApplication.absorbSecondForward selected relation transport actual
        .step .controlClosure (fun _ =>
          let backward := ControlFrontierApplication.absorbSecondBackward selected transport.1 actual
          .step .formationResources (fun _ =>
          let original : ControlFrontierApplication.ExecutablePreservation formula selected
              (first :: second :: rest) (first :: rest) :=
            ControlFrontierCeilingOriginal.assembled
            (actual.1)
            (fun _ => 8)
            (fun _ => 2)
            (flipEnvelope selected)
            (id)
            (forward)
            (backward)
            (ControlFrontierApplication.absorb_second_forward_bounded selected relation transport actual)
            (ControlFrontierApplication.absorb_second_backward_bounded selected transport.1 actual)
          let receivedWhole : Actual (ControlFrontierCeilingOriginal.absorbSecond selected relation transport actual) := ⟨original, rfl⟩
          returnLeafCode receivedWhole.1 (.flip selected) .identity (by
                change actual.1 = _
                exact actual.2.trans (congrArg (AcceptedFrontierPreservation.absorbSecondIntoFirst (rest := rest)) transport.2))))))))

theorem absorb_second_finite {formula : Cnf} (selected : Var)
    {first second : GeneratedStructuralBranchContext formula} {rest : List (GeneratedStructuralBranchContext formula)}
    (relation : GeneratedStructuralFlipAtRelation selected second first) :
    Finite (absorbSecondCode selected (rest := rest) relation) := by
  apply finite_bind (finite_of_within (ControlFrontierEvaluation.transport_bounded selected relation)); intro transport
  apply finite_bind (finite_of_within (ControlFrontierEvaluation.absorb_second_bounded transport.1)); intro actual
  repeat apply finite_step
  exact return_leaf_finite _ _ _ _

def expandCode {formula : Cnf} (selected : Var) (parent : GeneratedStructuralBranchContext formula)
    (fresh : StructuralDecisionsAvoid selected parent.context.decisions)
    (left : Actual (parent.child selected false fresh)) (right : Actual (parent.child selected true fresh))
    (splitter : ControlFrontierOpening.Split parent selected fresh left right)
    {rest : List (GeneratedStructuralBranchContext formula)} :
    Code Label (Formed selected (AcceptedFrontierPreservation.expandHead (rest := rest) splitter.1)) :=
  (ControlFrontierOpening.expandCode (rest := rest) splitter.1).bind (fun actual =>
    .step .executionPayload (fun _ => .step .controlClosure (fun _ =>
      let forward := ControlFrontierApplication.expandForward selected parent fresh left right splitter actual
      .step .controlClosure (fun _ =>
        let backward := ControlFrontierApplication.expandBackward selected parent fresh left right splitter actual
        .step .formationResources (fun _ =>
          let original : ControlFrontierApplication.ExecutablePreservation formula selected
              (parent :: rest) (left.1 :: right.1 :: rest) :=
            ControlFrontierCeilingOriginal.assembled
            (actual.1)
            (fun budget => (budget + 3) + 1)
            (fun _ => 4)
            (id)
            (id)
            (forward)
            (backward)
            (ControlFrontierApplication.expand_forward_bounded selected parent fresh left right splitter actual)
            (ControlFrontierApplication.expand_backward_bounded selected parent fresh left right splitter actual)
          let receivedWhole : Actual (ControlFrontierCeilingOriginal.expand selected parent fresh left right splitter actual) := ⟨original, rfl⟩
          returnLeafCode receivedWhole.1 .identity .identity (actual.2))))))

theorem expand_finite {formula : Cnf} (selected : Var) (parent : GeneratedStructuralBranchContext formula)
    (fresh : StructuralDecisionsAvoid selected parent.context.decisions)
    (left : Actual (parent.child selected false fresh)) (right : Actual (parent.child selected true fresh))
    (splitter : ControlFrontierOpening.Split parent selected fresh left right)
    {rest : List (GeneratedStructuralBranchContext formula)} :
    Finite (expandCode selected parent fresh left right splitter (rest := rest)) := by
  apply finite_bind (finite_of_within (ControlFrontierOpening.expand_bounded splitter.1)); intro actual
  repeat apply finite_step
  exact return_leaf_finite _ _ _ _

end ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierCeilingApplication

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierCeilingApplication.swapCode
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierCeilingApplication.swap_finite
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierCeilingApplication.absorbFirstCode
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierCeilingApplication.absorb_first_finite
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierCeilingApplication.absorbSecondCode
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierCeilingApplication.absorb_second_finite
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierCeilingApplication.expandCode
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrontierCeilingApplication.expand_finite
/- AXIOM_AUDIT_END -/
