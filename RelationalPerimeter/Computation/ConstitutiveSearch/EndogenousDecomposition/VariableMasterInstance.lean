import RelationalPerimeter.Computation.ConstitutiveSearch.EndogenousDecomposition.VariableMasterExecution
import RelationalPerimeter.Computation.ConstitutiveSearch.EndogenousDecomposition.ProducedProfileContinuation

/-!
# Two data-dependent decompositions of one master head

One received formula, one master origin, one selected transformation and one
SAT criterion. Only the constituted incoming decision differs. All four
opened branches are viable. The search actually retains one or two states.
Neither the expected width nor a partition is supplied to the executor.
-/
set_option genInjectivity false
set_option autoImplicit false
set_option maxHeartbeats 400000
namespace ConstitutiveSearch.EndogenousDecomposition.VariableMaster.Example
open SAT

def origin := ProducedContinuation.publicOrigin 0
def formula : Cnf := [[.positive 10, .positive 1, .positive 2]]
def root := GeneratedStructuralBranchContext.root formula
def parent (previous : Bool) := root.child 1 previous True.intro
def incoming (previous : Bool) : States formula := [parent previous]

theorem selected_exact : selected (masterHead origin) = 10 := by
  let stage := (masterHead origin).head.stage
  calc
    stage.discovery.var = stage.schedule.entry.var :=
      (congrArg (fun schedule => schedule.entry.var) stage.scheduleExact).symm
    _ = stageSelectedVar (origin.depth + 1) := sequentialStage_selected_exact stage
    _ = 10 := rfl

theorem fresh (previous : Bool) : StructuralDecisionsAvoid 10 (parent previous).context.decisions :=
  ⟨by change (1 : Nat) ≠ 10; decide, True.intro⟩

def child (previous choice : Bool) := (parent previous).child 10 choice (fresh previous)

def assignment (previous choice : Bool) : Assignment := fun var =>
  if var = 10 then choice else if var = 1 then previous else true

def continuation (previous choice : Bool) : GeneratedStructuralBranchContinuation (child previous choice) :=
  ⟨assignment previous choice, ⟨by rfl, ⟨by rfl, True.intro⟩⟩⟩

theorem each_child_accepted (previous choice : Bool) :
    GeneratedStructuralBranchAccept (child previous choice) (continuation previous choice) := by
  cases previous <;> cases choice
  · exact Satisfies.cons rfl Satisfies.nil
  · exact Satisfies.nil
  · exact Satisfies.nil
  · exact Satisfies.nil

theorem same_incoming_depth : (parent false).depth = (parent true).depth := rfl
theorem same_opened_depth : (child false false).depth = (child true false).depth := rfl

theorem opened_exact (previous : Bool) :
    (openFrontier formula 10 (incoming previous)).frontier =
      [child previous false, child previous true] := by
  cases previous <;> rfl

theorem grouped_width : (step origin formula (incoming true)).frontier.length = 1 := by
  rw [step_frontier_exact, selected_exact, opened_exact]
  decide

theorem unresolved_width : (step origin formula (incoming false)).frontier.length = 2 := by
  rw [step_frontier_exact, selected_exact, opened_exact]
  decide

/-- Both directions fail on the unresolved pair, for the very same finder. -/
theorem unresolved_search :
    (generatedStructuralFlipAtSearch formula 10).find (child false false) (child false true) = none ∧
    (generatedStructuralFlipAtSearch formula 10).find (child false true) (child false false) = none := by
  constructor <;> rfl

def discoveredRelation : GeneratedStructuralFlipAtRelation 10 (child true false) (child true true) :=
  ⟨rfl, rfl⟩

theorem grouped_search :
    (generatedStructuralFlipAtSearch formula 10).find (child true false) (child true true) =
      some discoveredRelation := rfl

theorem action_is_used :
    (discoveredRelation.mapContinuation (continuation true false)).1 10 = true := rfl

theorem preserved_after_action : GeneratedStructuralBranchAccept (child true true)
    (discoveredRelation.mapContinuation (continuation true false)) :=
  discoveredRelation.mapContinuation_accept _ (each_child_accepted true false)

theorem outputs_differ :
    (step origin formula (incoming true)).frontier.length ≠
      (step origin formula (incoming false)).frontier.length := by
  rw [grouped_width, unresolved_width]
  decide

theorem one_stage_finish (previous : Bool) :
    (execute 1 origin formula (incoming previous)).finish =
      (step origin formula (incoming previous)).frontier := rfl

theorem master_unchanged (count : Nat) (previous : Bool) :
    (execute count origin formula (incoming previous)).erasure = MasterResources.execute count origin :=
  execute_erases count origin formula (incoming previous)

def widths (count : Nat) : Nat × Nat :=
  ((execute count origin formula (incoming true)).finish.length,
    (execute count origin formula (incoming false)).finish.length)

end ConstitutiveSearch.EndogenousDecomposition.VariableMaster.Example
/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableMaster.Example.selected_exact
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableMaster.Example.each_child_accepted
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableMaster.Example.same_incoming_depth
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableMaster.Example.same_opened_depth
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableMaster.Example.opened_exact
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableMaster.Example.grouped_width
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableMaster.Example.unresolved_width
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableMaster.Example.unresolved_search
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableMaster.Example.grouped_search
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableMaster.Example.action_is_used
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableMaster.Example.preserved_after_action
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableMaster.Example.outputs_differ
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableMaster.Example.one_stage_finish
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableMaster.Example.master_unchanged
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableMaster.Example.widths
/- AXIOM_AUDIT_END -/
