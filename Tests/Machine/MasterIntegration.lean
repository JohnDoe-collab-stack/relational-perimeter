import RelationalPerimeter.Computation.Machine.MasterContract
import RelationalPerimeter.Computation.ConstitutiveSearch.EndogenousDecomposition.VariableMasterInstance

/-! Same public master, formula, depth, scope and finder. Received constitutive
decisions change the actually retained frontier and the configured packet action.
These are semantic regression proofs, not time or allocation measurements. -/
set_option genInjectivity false
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace ConstitutiveSearch.MasterMachine.Checks
open SAT EndogenousDecomposition ConnectedFabric
open ReconfigurableMachine.LiveReduction

def scope : Scope := [Channel.singleton 12]
def formula : Cnf := [[.positive 12, .positive 1, .positive 2]]
def root := GeneratedStructuralBranchContext.root formula
def parent (previous : Bool) := root.child 1 previous True.intro
def incoming (previous : Bool) : VariableMaster.States formula := [parent previous]
def master := UnifiedMaster.publicInstance 0
def rich (previous : Bool) := fromMaster scope master formula (incoming previous)
def received (previous : Bool) := project scope (rich previous)

theorem initialization_is_existing_master (previous : Bool) :
    received previous = receive 0 scope formula (incoming previous) := rfl

theorem initialization_all_inputs (input : Nat) (permissions : Scope) (problem : Cnf)
    (source : VariableMaster.States problem) :
    receive input permissions problem source =
      project permissions (fromMaster permissions (UnifiedMaster.publicInstance input) problem source) :=
  receive_exact input permissions problem source

theorem initialization_core_all_inputs (input : Nat) (permissions : Scope) (problem : Cnf)
    (source : VariableMaster.States problem) :
    (receive input permissions problem source).core =
      projectMemory permissions (fromMaster permissions (UnifiedMaster.publicInstance input) problem source).core :=
  receive_core_exact input permissions problem source

theorem initialization_problem_all_inputs (input : Nat) (permissions : Scope) (problem : Cnf)
    (source : VariableMaster.States problem) :
    (receive input permissions problem source).problem = initialProblem problem source :=
  receive_problem_exact input permissions problem source

theorem same_live (one two : Bool) : (received one).core = (received two).core := rfl
theorem same_depth : (parent false).depth = (parent true).depth := rfl
theorem selector (previous : Bool) :
    (ConstitutiveExecution.produce (received previous).core.live).action.selected = 12 := by
  calc
    _ = stageSelectedVar ((received previous).core.live.front.depth + 1) :=
      LocalAction.selected_exact _
    _ = 12 := rfl

theorem fresh (previous : Bool) : StructuralDecisionsAvoid 12 (parent previous).context.decisions :=
  ⟨by change (1 : Nat) ≠ 12; decide, True.intro⟩
def child (previous choice : Bool) := (parent previous).child 12 choice (fresh previous)
def assignment (previous choice : Bool) : Assignment := fun var =>
  if var = 12 then choice else if var = 1 then previous else true
def continuation (previous choice : Bool) : GeneratedStructuralBranchContinuation (child previous choice) :=
  ⟨assignment previous choice, ⟨by rfl, ⟨by rfl, True.intro⟩⟩⟩

theorem every_child_viable (previous choice : Bool) :
    GeneratedStructuralBranchAccept (child previous choice) (continuation previous choice) := by
  cases previous <;> cases choice
  · exact Satisfies.cons rfl Satisfies.nil
  · exact Satisfies.nil
  · exact Satisfies.nil
  · exact Satisfies.nil

theorem source_distinct (previous : Bool) : child previous false ≠ child previous true := by
  intro equal
  have decisions := congrArg (fun context => context.context.decisions) equal
  have choice := congrArg (fun decisions => (decisions.headD ⟨0, false⟩).value) decisions
  exact Bool.noConfusion choice

theorem grouped_width : (advance (received true)).problem.frontier.length = 1 := by
  rw [advance_frontier_is_produced, selector]
  decide
theorem unresolved_width : (advance (received false)).problem.frontier.length = 2 := by
  rw [advance_frontier_is_produced, selector]
  decide

theorem grouped_routing :
    (produceProblem scope formula 12 (incoming true)).configured.fire ⟨0, [false]⟩ =
      ⟨0, [true]⟩ := rfl
theorem unresolved_routing :
    (produceProblem scope formula 12 (incoming false)).configured.fire ⟨0, [false]⟩ =
      ⟨1, [false]⟩ := rfl
theorem same_finder_fails_both_ways :
    (generatedStructuralFlipAtSearch formula 12).find (child false false) (child false true) = none ∧
    (generatedStructuralFlipAtSearch formula 12).find (child false true) (child false false) = none := ⟨rfl, rfl⟩

theorem next_problem_exact (previous : Bool) :
    (advance (received previous)).problem =
      (produceProblem scope formula 12 (incoming previous)).next := by
  change (produceProblem scope formula
    (ConstitutiveExecution.produce (received previous).core.live).action.selected
    (incoming previous)).next = _
  rw [selector]

theorem grouped_packet_after_advance :
    ((perform (advance (received true)) (.route 0 [false])).1).problem.routed = some (0, [true]) := by
  change (routeProblem scope (advance (received true)).problem 0 [false]).1.routed = _
  rw [next_problem_exact]
  rfl
theorem unresolved_packet_after_advance :
    ((perform (advance (received false)) (.route 0 [false])).1).problem.routed = some (1, [false]) := by
  change (routeProblem scope (advance (received false)).problem 0 [false]).1.routed = _
  rw [next_problem_exact]
  rfl

theorem all_interleavings_exact (previous : Bool) (requests : List (ULift.{3} Request)) :
    (richContract scope formula).outcome (rich previous) requests =
      run (received previous) requests := all_futures_exact scope (rich previous) requests

theorem old_exponential_result : master.carrier.frontier.length = 2 ^ (0 + 1) := master.source_width
theorem old_grouped_result : master.regime.frontier.length = 1 := master.executed_width

end ConstitutiveSearch.MasterMachine.Checks
/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.MasterMachine.Checks.initialization_is_existing_master
#print axioms ConstitutiveSearch.MasterMachine.Checks.initialization_all_inputs
#print axioms ConstitutiveSearch.MasterMachine.Checks.initialization_core_all_inputs
#print axioms ConstitutiveSearch.MasterMachine.Checks.initialization_problem_all_inputs
#print axioms ConstitutiveSearch.MasterMachine.Checks.same_live
#print axioms ConstitutiveSearch.MasterMachine.Checks.selector
#print axioms ConstitutiveSearch.MasterMachine.Checks.every_child_viable
#print axioms ConstitutiveSearch.MasterMachine.Checks.source_distinct
#print axioms ConstitutiveSearch.MasterMachine.Checks.grouped_width
#print axioms ConstitutiveSearch.MasterMachine.Checks.unresolved_width
#print axioms ConstitutiveSearch.MasterMachine.Checks.grouped_routing
#print axioms ConstitutiveSearch.MasterMachine.Checks.unresolved_routing
#print axioms ConstitutiveSearch.MasterMachine.Checks.same_finder_fails_both_ways
#print axioms ConstitutiveSearch.MasterMachine.Checks.next_problem_exact
#print axioms ConstitutiveSearch.MasterMachine.Checks.grouped_packet_after_advance
#print axioms ConstitutiveSearch.MasterMachine.Checks.unresolved_packet_after_advance
#print axioms ConstitutiveSearch.MasterMachine.Checks.all_interleavings_exact
#print axioms ConstitutiveSearch.MasterMachine.Checks.old_exponential_result
#print axioms ConstitutiveSearch.MasterMachine.Checks.old_grouped_result
/- AXIOM_AUDIT_END -/
