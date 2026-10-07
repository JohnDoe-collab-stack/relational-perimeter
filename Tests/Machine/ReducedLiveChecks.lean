import RelationalPerimeter.Computation.Machine.ReducedLiveMinimality

/-! Closed boundaries of the reduction: diagnostics really disappear, empty
and repeated interfaces remain valid, and returned instructions act on inputs. -/
set_option genInjectivity false
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace ConstitutiveSearch.ReconfigurableMachine.LiveReduction
open SAT EndogenousDecomposition ConnectedFabric ContinuationSignatures

/-- Change a genuine source reader's instrumentation, not its assignment. -/
def additionalDiagnostic (live : LiveContinuation.Memory) : LiveContinuation.Memory :=
  let assignment : SequentialAssignment live.depth :=
    { assignment := live.assignment.assignment
      reader := fun query =>
        let previous := live.assignment.reader query
        ⟨previous.value, previous.valueExact, previous.work.visit⟩
      zeroTrue := live.assignment.zeroTrue
      futureSelectedFalse := live.assignment.futureSelectedFalse
      futureAnchorTrue := live.assignment.futureAnchorTrue }
  let state : ThreadedConstitutiveState live.depth assignment :=
    { threadedAssignment := assignment
      threadedAssignmentExact := rfl
      generation := live.state.generation
      searchSeed := live.state.searchSeed
      searchSeedExact := live.state.searchSeedExact
      decisions := live.state.decisions
      provenance := live.state.provenance
      provenanceExact := live.state.provenanceExact
      decisionsHold := live.state.decisionsHold }
  ⟨live.depth, assignment, state, live.fresh⟩

theorem diagnostics_are_distinct (live : LiveContinuation.Memory) : additionalDiagnostic live ≠ live := by
  intro same
  have observed := congrArg (fun memory : LiveContinuation.Memory =>
    (memory.assignment.reader 0).work.nodes) same
  change (live.assignment.reader 0).work.nodes + 1 = (live.assignment.reader 0).work.nodes at observed
  exact (Nat.ne_of_gt (Nat.lt_succ_self _)) observed

theorem diagnostics_projection_equal (scope : Scope) (live : LiveContinuation.Memory) :
    projectLive scope (additionalDiagnostic live) = projectLive scope live := rfl

theorem diagnostics_same_futures (scope : Scope) (memory : Memory) :
    FutureEquivalent (runtimeContract scope)
      { memory with live := additionalDiagnostic memory.live } memory :=
  (liveReduction scope).equal_memory_same_futures rfl

theorem empty_scope_exact (memory : Memory) (requests : List (ULift.{3} Request)) :
    (runtimeContract []).outcome memory requests =
      (contract []).outcome (projectMemory [] memory) requests :=
  all_futures_exact [] memory requests

theorem repeated_scope_exact (query : Var) (memory : Memory) (requests : List (ULift.{3} Request)) :
    (runtimeContract [Channel.singleton query, Channel.singleton query]).outcome memory requests =
      (contract [Channel.singleton query, Channel.singleton query]).outcome
        (projectMemory [Channel.singleton query, Channel.singleton query] memory) requests :=
  all_futures_exact _ memory requests

/-- Equal query addresses do not identify independent pulse positions. -/
theorem repeated_positions_not_identified (query : Var) :
    fire (configure [Channel.singleton query, Channel.singleton query] query) [false, true] =
      [true, false] := by
  change (configureGate query query).fire false :: (configureGate query query).fire true :: [] = _
  rw [configureGate, if_pos rfl]
  rfl

theorem selected_internal_input_exact (live : LiveContinuation.Memory)
    (action : LocalAction (projectFront live)) :
    (codeGate action.selected action.selected action.execution.code).fire
      (live.assignment.assignment action.selected) = action.internalOutput := by
  have source : live.assignment.assignment action.selected = false := by
    rw [action.selected_exact]
    exact live.assignment.futureSelectedFalse _ (Nat.le_refl _)
  rw [source]
  rfl

theorem empty_scope_keeps_internal_action (front : Frontier) (action : LocalAction front) :
    action.gates [] = [] ∧ action.internalOutput = true :=
  ⟨rfl, action.internalOutput_exact⟩

/-- The lowering distinguishes identity and a real flip instruction. -/
theorem identity_and_atom_act_differently {root : Cnf} (selected : Var)
    {source target : GeneratedStructuralBranchContext root}
    (relation : GeneratedStructuralFlipAtRelation selected source target) :
    (codeGate selected selected (.identity source)).fire false = false ∧
      (codeGate selected selected (.atom relation)).fire false = true := by
  constructor
  · rfl
  · change (configureGate selected selected).fire false = true
    rw [configureGate, if_pos rfl]
    rfl

/-- An explicit finite distinguishing request, not an existential appeal to
some unspecified future. Equal fronts install the same actual gates. -/
theorem one_advance_distinguishes_live_values (scope : Scope)
    (one two : LiveContinuation.Memory) (sameFront : projectFront one = projectFront two)
    (different : sense scope one.assignment.assignment ≠ sense scope two.assignment.assignment) :
    (advance scope one).1.bank.read .retained ≠ (advance scope two).1.bank.read .retained := by
  have lowered : (produceReduced (projectLive scope one)).connections =
      (produceReduced (projectLive scope two)).connections := by
    change (buildAction (projectFront one)).gates scope = (buildAction (projectFront two)).gates scope
    rw [sameFront]
  have gates : compile scope (LiveContinuation.produce one) = compile scope (LiveContinuation.produce two) :=
    (produced_connections_exact scope one).symm.trans (lowered.trans (produced_connections_exact scope two))
  intro equal
  have acted := (advance_values scope one).trans (equal.trans (advance_values scope two).symm)
  change fire (compile scope (LiveContinuation.produce one)) _ =
    fire (compile scope (LiveContinuation.produce two)) _ at acted
  rw [← gates] at acted
  have inverted := congrArg (fire (compile scope (LiveContinuation.produce one))) acted
  rw [fire_involutive _ _ ((compile_length scope _).trans (sensed_length scope one.assignment.assignment).symm),
    fire_involutive _ _ ((compile_length scope _).trans (sensed_length scope two.assignment.assignment).symm)] at inverted
  exact different inverted

end ConstitutiveSearch.ReconfigurableMachine.LiveReduction
/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.ReconfigurableMachine.LiveReduction.additionalDiagnostic
#print axioms ConstitutiveSearch.ReconfigurableMachine.LiveReduction.diagnostics_are_distinct
#print axioms ConstitutiveSearch.ReconfigurableMachine.LiveReduction.diagnostics_projection_equal
#print axioms ConstitutiveSearch.ReconfigurableMachine.LiveReduction.diagnostics_same_futures
#print axioms ConstitutiveSearch.ReconfigurableMachine.LiveReduction.empty_scope_exact
#print axioms ConstitutiveSearch.ReconfigurableMachine.LiveReduction.repeated_scope_exact
#print axioms ConstitutiveSearch.ReconfigurableMachine.LiveReduction.repeated_positions_not_identified
#print axioms ConstitutiveSearch.ReconfigurableMachine.LiveReduction.selected_internal_input_exact
#print axioms ConstitutiveSearch.ReconfigurableMachine.LiveReduction.empty_scope_keeps_internal_action
#print axioms ConstitutiveSearch.ReconfigurableMachine.LiveReduction.identity_and_atom_act_differently
#print axioms ConstitutiveSearch.ReconfigurableMachine.LiveReduction.one_advance_distinguishes_live_values
/- AXIOM_AUDIT_END -/
