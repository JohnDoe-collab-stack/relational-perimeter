import RelationalPerimeter.Computation.ConstitutiveSearch.EndogenousDecomposition.RoleIndexedProgram

/-! Local feasibility construction. Fresh variables are computed from the
actual formula and decision history. Accepted payloads are transformed by the
compiled role action; no policy or signature is supplied to this construction.
This module alone does not certify the composed continuation family. -/

set_option genInjectivity false
namespace ConstitutiveSearch.ContinuationSignatures
open SAT EndogenousDecomposition

def literalVariable : Literal → Var
  | .positive v => v
  | .negative v => v

def formulaVariables : Cnf → List Var
  | [] => []
  | clause :: rest => clause.map literalVariable ++ formulaVariables rest

theorem mapped_member {α β : Type} (f : α → β) {x : α} {xs : List α}
    (member : x ∈ xs) : f x ∈ xs.map f := by
  induction xs with
  | nil => cases member
  | cons _ rest ih =>
      cases member with
      | head => exact .head _
      | tail _ member => exact .tail _ (ih member)

theorem append_left_member {α : Type} {x : α} {xs : List α}
    (ys : List α) (member : x ∈ xs) : x ∈ xs ++ ys := by
  induction xs with
  | nil => cases member
  | cons _ rest ih =>
      cases member with
      | head => exact .head _
      | tail _ member => exact .tail _ (ih member)

theorem append_right_member {α : Type} (xs : List α) {x : α} {ys : List α}
    (member : x ∈ ys) : x ∈ xs ++ ys := by
  induction xs with
  | nil => exact member
  | cons _ _ ih => exact .tail _ ih

def variableBound : List Var → Nat
  | [] => 0
  | v :: rest => v + 1 + variableBound rest

theorem variable_lt_bound {v : Var} {variables : List Var}
    (present : v ∈ variables) : v < variableBound variables := by
  induction variables with
  | nil => cases present
  | cons head rest ih =>
      cases present with
      | head => exact Nat.lt_of_lt_of_le (Nat.lt_succ_self v) (Nat.le_add_right _ _)
      | tail _ tail =>
          exact Nat.lt_of_lt_of_le (ih tail) (Nat.le_add_left _ _)

theorem flip_literal_unchanged (assignment : Assignment) (query : Var)
    (literal : Literal) (absent : literalVariable literal ≠ query) :
    literal.eval (Assignment.flipAt query assignment) = literal.eval assignment := by
  cases literal with
  | positive v => exact Assignment.flipAt_other _ _ _ absent
  | negative v => exact congrArg Bool.not (Assignment.flipAt_other _ _ _ absent)

theorem flip_clause_unchanged (assignment : Assignment) (query : Var)
    (clause : Clause) (absent : ∀ literal ∈ clause, literalVariable literal ≠ query) :
    Clause.eval (Assignment.flipAt query assignment) clause = Clause.eval assignment clause := by
  induction clause with
  | nil => rfl
  | cons literal rest ih =>
      change (_ || _) = (_ || _)
      rw [flip_literal_unchanged assignment query literal (absent _ (List.mem_cons_self))]
      rw [ih (fun l member => absent l (List.mem_cons_of_mem _ member))]

theorem flip_satisfies_unchanged {assignment : Assignment} {formula : Cnf}
    (accepted : Satisfies assignment formula) (query : Var)
    (absent : query ∉ formulaVariables formula) :
    Satisfies (Assignment.flipAt query assignment) formula := by
  induction accepted with
  | nil => exact .nil
  | @cons clause rest head tail ih =>
      have localAbsent : ∀ literal ∈ clause, literalVariable literal ≠ query := by
        intro literal member same
        apply absent
        rw [← same]
        exact append_left_member _ (mapped_member literalVariable member)
      refine .cons ?_ (ih ?_)
      · rw [flip_clause_unchanged assignment query clause localAbsent]
        exact head
      · intro present
        apply absent
        exact append_right_member _ present

theorem flip_decisions_unchanged {assignment : Assignment}
    {decisions : List StructuralBranchDecision}
    (holds : StructuralDecisionsHold assignment decisions) (query : Var)
    (absent : query ∉ decisions.map StructuralBranchDecision.var) :
    StructuralDecisionsHold (Assignment.flipAt query assignment) decisions := by
  induction decisions with
  | nil => exact True.intro
  | cons decision rest ih =>
      refine ⟨?_, ih holds.2 ?_⟩
      · rw [Assignment.flipAt_other]
        · exact holds.1
        · intro same
          exact absent (same ▸ mapped_member StructuralBranchDecision.var (.head _))
      · intro present
        exact absent (List.mem_cons_of_mem _ present)

variable {state : CausalConstitutiveState} {run : CausalConstitutiveStageExecution state}

def freeVariable (run : CausalConstitutiveStageExecution state) : Var :=
  variableBound (run.selected ::
    formulaVariables (causalOpeningLeft state run.selected run.fresh).context.formula ++
    (causalOpeningLeft state run.selected run.fresh).context.decisions.map
      StructuralBranchDecision.var)

theorem freeVariable_selected_ne (run : CausalConstitutiveStageExecution state) :
    freeVariable run ≠ run.selected := by
  have less := variable_lt_bound (v := run.selected)
    (variables := run.selected ::
      formulaVariables (causalOpeningLeft state run.selected run.fresh).context.formula ++
      (causalOpeningLeft state run.selected run.fresh).context.decisions.map
        StructuralBranchDecision.var) List.mem_cons_self
  change run.selected < freeVariable run at less
  exact (Nat.ne_of_lt less).symm

theorem freeVariable_formula_absent (run : CausalConstitutiveStageExecution state) :
    freeVariable run ∉
      formulaVariables (causalOpeningLeft state run.selected run.fresh).context.formula := by
  intro present
  have less : freeVariable run < freeVariable run := variable_lt_bound (List.mem_cons_of_mem run.selected
    (append_left_member _ present))
  exact (Nat.lt_irrefl (freeVariable run)) less

theorem freeVariable_decisions_absent (run : CausalConstitutiveStageExecution state) :
    freeVariable run ∉
      (causalOpeningLeft state run.selected run.fresh).context.decisions.map
        StructuralBranchDecision.var := by
  intro present
  have less : freeVariable run < freeVariable run := variable_lt_bound (List.mem_cons_of_mem run.selected
    (append_right_member _ present))
  exact (Nat.lt_irrefl (freeVariable run)) less

def variedInput (run : CausalConstitutiveStageExecution state) :
    GeneratedStructuralBranchContinuation (causalOpeningLeft state run.selected run.fresh) :=
  ⟨Assignment.flipAt (freeVariable run) run.sourceContinuation.1,
    flip_decisions_unchanged run.sourceContinuation.2 _ (freeVariable_decisions_absent run)⟩

theorem variedInput_accepted (run : CausalConstitutiveStageExecution state) :
    GeneratedStructuralBranchAccept (causalOpeningLeft state run.selected run.fresh)
      (variedInput run) :=
  flip_satisfies_unchanged run.sourceAccepted _ (freeVariable_formula_absent run)

def variedOutput (role : RelationalConstitutiveRoleStage run) :
    GeneratedStructuralBranchContinuation (causalOpeningRight state run.selected run.fresh) :=
  (compileRoleStageAtom role).action (variedInput run)

theorem variedOutput_accepted (role : RelationalConstitutiveRoleStage run) :
    GeneratedStructuralBranchAccept (causalOpeningRight state run.selected run.fresh)
      (variedOutput role) :=
  (compileRoleStageAtom role).preservesAccepted _ (variedInput_accepted run)

theorem variedOutput_distinguished (role : RelationalConstitutiveRoleStage run) :
    (variedOutput role).1 (freeVariable run) ≠
      ((compileRoleStageAtom role).action run.sourceContinuation).1 (freeVariable run) := by
  change Assignment.flipAt run.selected (Assignment.flipAt (freeVariable run)
    run.sourceContinuation.1) (freeVariable run) ≠
      Assignment.flipAt run.selected run.sourceContinuation.1 (freeVariable run)
  rw [Assignment.flipAt_other _ _ _ (freeVariable_selected_ne run),
    Assignment.flipAt_other _ _ _ (freeVariable_selected_ne run), Assignment.flipAt_selected]
  cases run.sourceContinuation.1 (freeVariable run) <;> decide

/-- The source retains its formed occurrence and accepted payload. -/
structure AcceptedRoleSource (role : RelationalConstitutiveRoleStage run) where
  occurrence : RoleConstitutedOccurrence role
  payload : RoleOpeningPayload occurrence
  accepted : RoleSemantics.LocalAccept occurrence payload

def leftSource (role : RelationalConstitutiveRoleStage run) : AcceptedRoleSource role :=
  ⟨roleConstitutedOccurrenceAt role .left, run.sourceContinuation, run.sourceAccepted⟩

def pairedRightSource (role : RelationalConstitutiveRoleStage run) : AcceptedRoleSource role :=
  ⟨roleConstitutedOccurrenceAt role .right,
    (compileRoleStageAtom role).action run.sourceContinuation,
    (compileRoleStageAtom role).preservesAccepted _ run.sourceAccepted⟩

def variedLeftSource (role : RelationalConstitutiveRoleStage run) : AcceptedRoleSource role :=
  ⟨roleConstitutedOccurrenceAt role .left, variedInput run, variedInput_accepted run⟩

def producedOutput (role : RelationalConstitutiveRoleStage run) (source : AcceptedRoleSource role) :
    GeneratedStructuralBranchContinuation (causalOpeningRight state run.selected run.fresh) :=
  interpretRoleStageAtom (compileRoleStageAtom role) source.occurrence
    (roleConstitutionEvidence role source.occurrence) source.payload

theorem paired_sources_same_output (role : RelationalConstitutiveRoleStage run) :
    producedOutput role (leftSource role) = producedOutput role (pairedRightSource role) := rfl

theorem paired_sources_distinct (role : RelationalConstitutiveRoleStage run) :
    leftSource role ≠ pairedRightSource role := by
  intro same
  have positions := congrArg (fun source => source.occurrence.position) same
  cases positions

theorem varied_source_separated (role : RelationalConstitutiveRoleStage run) :
    (producedOutput role (variedLeftSource role)).1 (freeVariable run) ≠
      (producedOutput role (leftSource role)).1 (freeVariable run) :=
  variedOutput_distinguished role

end ConstitutiveSearch.ContinuationSignatures

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.ContinuationSignatures.variable_lt_bound
#print axioms ConstitutiveSearch.ContinuationSignatures.flip_literal_unchanged
#print axioms ConstitutiveSearch.ContinuationSignatures.flip_clause_unchanged
#print axioms ConstitutiveSearch.ContinuationSignatures.flip_satisfies_unchanged
#print axioms ConstitutiveSearch.ContinuationSignatures.flip_decisions_unchanged
#print axioms ConstitutiveSearch.ContinuationSignatures.freeVariable_formula_absent
#print axioms ConstitutiveSearch.ContinuationSignatures.freeVariable_decisions_absent
#print axioms ConstitutiveSearch.ContinuationSignatures.variedInput
#print axioms ConstitutiveSearch.ContinuationSignatures.variedInput_accepted
#print axioms ConstitutiveSearch.ContinuationSignatures.variedOutput_accepted
#print axioms ConstitutiveSearch.ContinuationSignatures.producedOutput
#print axioms ConstitutiveSearch.ContinuationSignatures.paired_sources_same_output
#print axioms ConstitutiveSearch.ContinuationSignatures.paired_sources_distinct
#print axioms ConstitutiveSearch.ContinuationSignatures.varied_source_separated
/- AXIOM_AUDIT_END -/
