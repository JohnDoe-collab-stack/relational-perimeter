import Tests.Machine.ReducedLiveChecks
import RelationalPerimeter.Computation.ConstitutiveSearch.EndogenousDecomposition.UnifiedPublicCertificate

/-! Two valid received lives differ in an actual assignment bit, not in reader
instrumentation. The fixed future contract can forget that bit under one
permission and must retain it under another. These are constructed valid
states; no claim that both are prefixes of the canonical public run is made. -/
set_option genInjectivity false
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace ConstitutiveSearch.ReconfigurableMachine.LiveReduction.AssignmentForgetting
open SAT EndogenousDecomposition ConnectedFabric ContinuationSignatures

theorem selected_above_low_bits (depth : Nat) : 8 ≤ stageSelectedVar depth := by
  induction depth with
  | zero => exact Nat.le_refl 8
  | succ depth ih => rw [stageSelectedVar_succ]; exact Nat.le_trans ih (Nat.le_add_right _ _)

theorem flip_preserves_decisions (assignment : Assignment) (query : Var)
    (decisions : List StructuralBranchDecision)
    (avoids : ∀ decision, decision ∈ decisions → decision.var ≠ query)
    (holds : StructuralDecisionsHold assignment decisions) :
    StructuralDecisionsHold (Assignment.flipAt query assignment) decisions := by
  induction decisions with
  | nil => exact True.intro
  | cons decision rest ih =>
      exact ⟨(Assignment.flipAt_other query decision.var assignment
        (avoids decision (List.Mem.head rest))).trans holds.1,
        ih (fun prior member => avoids prior (List.Mem.tail decision member)) holds.2⟩

/-- A positive executable reconstruction, with all source invariants retained. -/
def flipLowBit (live : LiveContinuation.Memory) (query : Var)
    (low : query < 8) (notZero : query ≠ 0)
    (avoids : ∀ decision, decision ∈ live.state.decisions → decision.var ≠ query) :
    LiveContinuation.Memory :=
  let assignment : SequentialAssignment live.depth :=
    { assignment := Assignment.flipAt query live.assignment.assignment
      reader := readFlippedAssignment query live.assignment.reader
      zeroTrue := (Assignment.flipAt_other query 0 live.assignment.assignment
        (Ne.symm notZero)).trans live.assignment.zeroTrue
      futureSelectedFalse := fun depth after =>
        (Assignment.flipAt_other query _ live.assignment.assignment
          (Nat.ne_of_gt (Nat.lt_of_lt_of_le low (selected_above_low_bits depth)))).trans
            (live.assignment.futureSelectedFalse depth after)
      futureAnchorTrue := fun depth after => by
        have bound : 8 ≤ stageAnchorVar depth := by
          rw [stageAnchorVar_eq_selected_succ]
          exact Nat.le_trans (selected_above_low_bits depth) (Nat.le_add_right _ _)
        exact (Assignment.flipAt_other query _ live.assignment.assignment
          (Nat.ne_of_gt (Nat.lt_of_lt_of_le low bound))).trans
            (live.assignment.futureAnchorTrue depth after) }
  let state : ThreadedConstitutiveState live.depth assignment :=
    { threadedAssignment := assignment
      threadedAssignmentExact := rfl
      generation := live.state.generation
      searchSeed := live.state.searchSeed
      searchSeedExact := live.state.searchSeedExact
      decisions := live.state.decisions
      provenance := live.state.provenance
      provenanceExact := live.state.provenanceExact
      decisionsHold := flip_preserves_decisions _ query _ avoids live.state.decisionsHold }
  ⟨live.depth, assignment, state, live.fresh⟩

def original : LiveContinuation.Memory :=
  LiveContinuation.project (UnifiedMaster.publicInstance 0).cursor

theorem original_avoids_one :
    ∀ decision, decision ∈ original.state.decisions → decision.var ≠ 1 := by
  intro decision member
  have mapped : decision.var ∈ original.state.decisions.map (fun item => item.var) := by
    have mapMember (decisions : List StructuralBranchDecision)
        (member : decision ∈ decisions) : decision.var ∈ decisions.map (fun item => item.var) := by
      induction decisions with
      | nil => cases member
      | cons head rest ih =>
          cases member with
          | head => exact List.Mem.head _
          | tail _ prior => exact List.Mem.tail _ (ih prior)
    exact mapMember _ member
  rw [← original.state.provenanceExact] at mapped
  have provenance : original.state.provenance = [10] := by decide
  rw [provenance] at mapped
  have onlyTen (var : Var) (member : var ∈ [10]) : var = 10 := by
    cases member with
    | head => rfl
    | tail _ impossible => cases impossible
  have sameVar := onlyTen decision.var mapped
  rw [sameVar]
  decide

def changed : LiveContinuation.Memory :=
  flipLowBit original 1 (by decide) (by decide) original_avoids_one

theorem assignment_values_differ :
    original.assignment.assignment 1 ≠ changed.assignment.assignment 1 := by
  change original.assignment.assignment 1 ≠ Assignment.flipAt 1 original.assignment.assignment 1
  rw [Assignment.flipAt_selected]
  cases original.assignment.assignment 1 <;> decide

theorem lives_distinct : original ≠ changed := by
  intro same
  exact assignment_values_differ (congrArg (fun live : LiveContinuation.Memory =>
    live.assignment.assignment 1) same)

/-- The present bank is fixed; coherence only requires its interface length. -/
def received (live : LiveContinuation.Memory) : Memory :=
  ⟨live, [⟨false⟩], .shared [original.assignment.assignment 2]⟩

theorem received_coherent (query : Var) (live : LiveContinuation.Memory) :
    Coherent [Channel.singleton query] (received live) := ⟨rfl, rfl, rfl⟩

theorem received_distinct : received original ≠ received changed := by
  intro same
  exact lives_distinct (congrArg Memory.live same)

theorem same_present_view : (received original).view = (received changed).view := rfl

theorem outside_permission_projection_equal :
    projectMemory [Channel.singleton 2] (received original) =
      projectMemory [Channel.singleton 2] (received changed) := by
  apply runtime_ext
  · apply live_ext
    · rfl
    · change [original.assignment.assignment 2] =
        [Assignment.flipAt 1 original.assignment.assignment 2]
      rw [Assignment.flipAt_other 1 2 _ (by decide)]
  · rfl
  · rfl

theorem outside_permission_all_futures :
    FutureEquivalent (runtimeContract [Channel.singleton 2])
      (received original) (received changed) :=
  (minimal_projection_iff_futures _ (received_coherent 2 original)
    (received_coherent 2 changed)).mp outside_permission_projection_equal

theorem inside_permission_values_differ :
    sense [Channel.singleton 1] original.assignment.assignment ≠
      sense [Channel.singleton 1] changed.assignment.assignment := by
  intro same
  exact assignment_values_differ (List.cons.inj same).1

theorem advance_separates :
    (advance [Channel.singleton 1] original).1.bank.read .retained ≠
      (advance [Channel.singleton 1] changed).1.bank.read .retained :=
  one_advance_distinguishes_live_values _ original changed rfl inside_permission_values_differ

def separatingRequests : List (ULift.{3} Request) := [⟨.advance⟩]

theorem separating_future :
    (runtimeContract [Channel.singleton 1]).outcome (received original) separatingRequests ≠
      (runtimeContract [Channel.singleton 1]).outcome (received changed) separatingRequests := by
  intro same
  injection same with _ _ _ tailSame
  injection tailSame with finalView
  exact advance_separates (congrArg (fun view : View => view.2.2) finalView)

theorem inside_permission_not_equivalent :
    ¬ FutureEquivalent (runtimeContract [Channel.singleton 1])
      (received original) (received changed) := fun same => separating_future (same separatingRequests)

end ConstitutiveSearch.ReconfigurableMachine.LiveReduction.AssignmentForgetting
/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.ReconfigurableMachine.LiveReduction.AssignmentForgetting.flipLowBit
#print axioms ConstitutiveSearch.ReconfigurableMachine.LiveReduction.AssignmentForgetting.changed
#print axioms ConstitutiveSearch.ReconfigurableMachine.LiveReduction.AssignmentForgetting.assignment_values_differ
#print axioms ConstitutiveSearch.ReconfigurableMachine.LiveReduction.AssignmentForgetting.received_coherent
#print axioms ConstitutiveSearch.ReconfigurableMachine.LiveReduction.AssignmentForgetting.received_distinct
#print axioms ConstitutiveSearch.ReconfigurableMachine.LiveReduction.AssignmentForgetting.same_present_view
#print axioms ConstitutiveSearch.ReconfigurableMachine.LiveReduction.AssignmentForgetting.outside_permission_projection_equal
#print axioms ConstitutiveSearch.ReconfigurableMachine.LiveReduction.AssignmentForgetting.outside_permission_all_futures
#print axioms ConstitutiveSearch.ReconfigurableMachine.LiveReduction.AssignmentForgetting.separating_future
#print axioms ConstitutiveSearch.ReconfigurableMachine.LiveReduction.AssignmentForgetting.inside_permission_not_equivalent
/- AXIOM_AUDIT_END -/
