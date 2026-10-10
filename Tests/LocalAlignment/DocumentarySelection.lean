import Tests.LocalAlignment.DocumentaryContract
import RelationalPerimeter.Computation.ConstitutiveSearch.SAT.StructuralGlobalContextRelation

/-! Executable two-source documentary encoding. The received goal and contract
determine acceptance. Structural continuation formation is separate. -/
set_option genInjectivity false
namespace ConstitutiveSearch.Agent.Local.Documentary.Selection
open Resources SAT

inductive Checked {context} (sources : Support SourceValue context) (contract : Contract)
    (demand : Demand) (origin : Location context) where
  | permitted (permission : Ref contract.allowed origin.2.position)
      (meets : Meets demand (sourceCitation sources origin))
  | rejected (absent : Ref contract.allowed origin.2.position →
      Meets demand (sourceCitation sources origin) → False)

def check {context} (sources : Support SourceValue context) (contract : Contract)
    (demand : Demand) (origin : Location context) : Checked sources contract demand origin :=
  match found : resolvePermission contract.allowed origin.2.position with
  | none => .rejected (fun permission _ =>
      resolvePermission_none contract.allowed origin.2.position found permission)
  | some permission =>
      match meetsDecision demand (sourceCitation sources origin) with
      | .isTrue meets => .permitted permission meets
      | .isFalse wrong => .rejected (fun _ meets => wrong meets)

def Checked.flag {context} {sources : Support SourceValue context} {contract demand origin} :
    Checked sources contract demand origin → Bool
  | .permitted _ _ => true
  | .rejected _ => false

def Checked.candidate {context} {sources : Support SourceValue context} {contract demand origin}
    (checked : Checked sources contract demand origin) (accepted : checked.flag = true) :
    Candidate sources contract demand := by
  cases checked with
  | permitted permission meets => exact ⟨origin, permission, meets⟩
  | rejected absent => cases accepted

theorem Checked.complete {context} {sources : Support SourceValue context} {contract demand origin}
    (checked : Checked sources contract demand origin)
    (permission : Ref contract.allowed origin.2.position)
    (meets : Meets demand (sourceCitation sources origin)) : checked.flag = true := by
  cases checked with
  | permitted _ _ => rfl
  | rejected absent => exact False.elim (absent permission meets)

/-- The selected bit denotes a received location, never an interchangeable value. -/
def originFor {context} (left right : Location context) : Bool → Location context
  | false => left
  | true => right

def choiceFormula (var : Var) : Bool → Bool → Cnf
  | false, false => [[]]
  | false, true => [[.positive var]]
  | true, false => [[.negative var]]
  | true, true => []

/-- Exact semantic law: satisfying assignments choose precisely eligible sources. -/
theorem choiceFormula_exact (var : Var) (left right : Bool) (assignment : Assignment) :
    Satisfies assignment (choiceFormula var left right) ↔
      (if assignment var then right else left) = true := by
  cases left <;> cases right <;> cases value : assignment var
  all_goals constructor
  all_goals intro witness
  all_goals first
    | exact rfl
    | exact .nil
    | exact .cons (by change (assignment var || false) = true; rw [value]; rfl) .nil
    | exact .cons (by change (!assignment var || false) = true; rw [value]; rfl) .nil
    | (have impossible : false = true := witness; cases impossible)
    | (cases witness with
        | cons head _ =>
            have impossible : false = true := head
            cases impossible)
    | (cases witness with
        | cons head _ =>
            change (assignment var || false) = true at head
            rw [value] at head
            cases head)
    | (cases witness with
        | cons head _ =>
            change (!assignment var || false) = true at head
            rw [value] at head
            cases head)

inductive Seed (var : Var) (left right : Bool) where
  | viable (assignment : Assignment)
      (accepted : Satisfies assignment (choiceFormula var left right))
  | blocked (impossible : (value : Bool) → (if value then right else left) = true → False)

def seed (var : Var) : (left right : Bool) → Seed var left right
  | false, false => .blocked (fun value accepted => by cases value <;> cases accepted)
  | false, true => .viable (fun _ => true)
      ((choiceFormula_exact var false true _).2 rfl)
  | true, false => .viable (fun _ => false)
      ((choiceFormula_exact var true false _).2 rfl)
  | true, true => .viable (fun _ => false)
      ((choiceFormula_exact var true true _).2 rfl)

/-- Acceptance at a generated descendant reflects to its actual received root. -/
theorem generated_root_accept {formula : Cnf} {state : StructuralBranchContext}
    (generated : StructuralGeneratedFrom formula state)
    (continuation : StructuralBranchContinuation state)
    (accepted : StructuralBranchAccept state continuation) :
    Satisfies continuation.1 formula := by
  induction generated with
  | root => exact accepted
  | child parentGenerated var value fresh ih =>
      exact ih ⟨continuation.1, continuation.2.2⟩
        (restoreSatisfaction _ continuation.1 var value continuation.2.1 accepted)

def frontierAssignment {formula : Cnf} :
    {frontier : List (GeneratedStructuralBranchContext formula)} →
      FrontierContinuation (generatedStructuralBranchSystem formula) frontier → Assignment
  | _ :: _, .head continuation => continuation.1
  | _ :: _, .tail continuation => frontierAssignment continuation

theorem frontier_root_accept {formula : Cnf}
    {frontier : List (GeneratedStructuralBranchContext formula)}
    (continuation : FrontierContinuation (generatedStructuralBranchSystem formula) frontier)
    (accepted : FrontierAccept (generatedStructuralBranchSystem formula) frontier continuation) :
    Satisfies (frontierAssignment continuation) formula := by
  induction continuation with
  | @head state _ continuation =>
      exact generated_root_accept state.generated continuation accepted
  | tail continuation ih => exact ih accepted

end ConstitutiveSearch.Agent.Local.Documentary.Selection
/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Selection.Checked
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Selection.check
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Selection.Checked.flag
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Selection.Checked.candidate
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Selection.Checked.complete
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Selection.originFor
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Selection.choiceFormula
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Selection.choiceFormula_exact
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Selection.Seed
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Selection.seed
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Selection.generated_root_accept
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Selection.frontierAssignment
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Selection.frontier_root_accept
/- AXIOM_AUDIT_END -/
