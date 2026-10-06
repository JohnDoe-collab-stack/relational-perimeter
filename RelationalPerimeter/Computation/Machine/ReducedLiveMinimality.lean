import RelationalPerimeter.Computation.Machine.ReducedLiveContract

/-! Minimal distinctions for the fixed contract, with no equality assumption
on the original live engines and no simulation of futures in the projection. -/
set_option genInjectivity false
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace ConstitutiveSearch.ReconfigurableMachine.LiveReduction
open SAT EndogenousDecomposition ConnectedFabric ContinuationSignatures StrongPerimetralTurning

theorem free_layer_unique {P : CircularPresentation} {cursor : PerimeterCursor P}
    {previous : FreeConstitution P cursor} {difference : BoundaryDifference P previous}
    (one two : FreeK P previous difference) : one = two := by
  cases one with | mk one =>
    cases two with | mk two =>
      cases one with | mk term termExact obstruction obstructionExact provenance provenanceExact =>
        cases two with | mk otherTerm otherTermExact otherObstruction otherObstructionExact otherProvenance otherProvenanceExact =>
          cases termExact; cases otherTermExact
          cases obstructionExact; cases otherObstructionExact
          cases provenanceExact; cases otherProvenanceExact
          rfl

theorem integration_unique {P : CircularPresentation} (source : PositiveConstitution P)
    (one two : Integrates source) : one = two := by
  cases one with | mk layer exactLayer =>
    cases two with | mk otherLayer otherExact =>
      have same := free_layer_unique layer otherLayer
      cases same
      rfl

theorem provenance_unique {P : CircularPresentation} (source : PositiveConstitution P)
    (one two : PreservesProvenance source (canonicalTarget source)) : one = two := by
  cases one with | mk exactTarget integration =>
    cases two with | mk otherExact otherIntegration =>
      have same := integration_unique source integration otherIntegration
      cases same
      rfl

theorem fresh_difference_unique {P : CircularPresentation} (source : PositiveConstitution P)
    (one two : FreshBoundaryDifference source) : one = two := by
  cases one with | mk continuation record recordExact notOld =>
    cases two with | mk otherContinuation otherRecord otherRecordExact otherNotOld =>
      cases continuation; cases otherContinuation
      cases recordExact; cases otherRecordExact
      rfl

theorem generated_laws_unique {P : CircularPresentation} (source : PositiveConstitution P)
    (one two : CanonicalGeneratedLaws source) : one = two := by
  cases one with | mk compatible compatibleExact provenance obstruction difference fresh =>
    cases two with | mk otherCompatible otherCompatibleExact otherProvenance otherObstruction otherDifference otherFresh =>
      cases compatibleExact; cases otherCompatibleExact
      have sameProvenance := provenance_unique source provenance otherProvenance
      have sameFresh := fresh_difference_unique source fresh otherFresh
      cases sameProvenance; cases sameFresh
      cases obstruction; cases otherObstruction
      cases difference; cases otherDifference
      rfl

theorem generated_step_unique {P : CircularPresentation} {source target : PositiveConstitution P}
    (one two : GeneratedStep source target) : one = two := by
  cases one with | mk exactTarget laws =>
    cases two with | mk otherExact otherLaws =>
      have same := generated_laws_unique source laws otherLaws
      cases same
      rfl

theorem generation_unique {depth : Nat} (one two : Generation depth) : one = two := by
  cases one with | mk target targetExact generated =>
    cases two with | mk otherTarget otherExact otherGenerated =>
      cases targetExact; cases otherExact
      have same := generated_step_unique generated otherGenerated
      cases same
      rfl

theorem frontier_read_complete (one two : Frontier)
    (same : (one.depth, one.provenance, one.searchSeed) = (two.depth, two.provenance, two.searchSeed)) :
    one = two := by
  have depth := congrArg Prod.fst same
  have provenance := congrArg (fun view : Nat × List Var × Nat => view.2.1) same
  have seed := congrArg (fun view : Nat × List Var × Nat => view.2.2) same
  apply frontier_ext one two depth _ seed provenance
  cases one; cases two
  cases depth
  exact heq_of_eq (generation_unique _ _)

theorem advance_values (scope : Scope) (live : LiveContinuation.Memory) :
    fire (advance scope live).1.gates (sense scope live.assignment.assignment) =
      (advance scope live).1.bank.read .retained := by
  change fire (compile scope (LiveContinuation.produce live)) _ =
    (drive _ _ _).read .retained
  rw [drive, route_reads_retained]
  have convergence := canonical_targets_converge scope (LiveContinuation.produce live)
  rw [(LiveContinuation.produce live).decomposition.role.executedInputExact] at convergence
  change fire (compile scope (LiveContinuation.produce live))
    (sense scope (LiveContinuation.produce live).built.stage.sourceContinuation.1) = _ at convergence
  rw [(LiveContinuation.produce live).built.stage.sourceAssignmentExact] at convergence
  exact convergence

theorem future_determines_live_values (scope : Scope) {one two : Memory}
    (same : FutureEquivalent (runtimeContract scope) one two) :
    sense scope one.live.assignment.assignment = sense scope two.live.assignment.assignment := by
  have future := same.next ⟨.advance⟩
  have gates := futures_determine_connections scope
    (install_coherent scope (LiveContinuation.produce one.live))
    (install_coherent scope (LiveContinuation.produce two.live)) future
  have outputs := congrArg (fun view : View => view.2.2) future.read
  change (advance scope one.live).1.bank.read .retained =
    (advance scope two.live).1.bank.read .retained at outputs
  have acted : fire (advance scope one.live).1.gates (sense scope one.live.assignment.assignment) =
      fire (advance scope two.live).1.gates (sense scope two.live.assignment.assignment) :=
    (advance_values scope one.live).trans (outputs.trans (advance_values scope two.live).symm)
  change (advance scope one.live).1.gates = (advance scope two.live).1.gates at gates
  rw [← gates] at acted
  have firstLength := (compile_length scope (LiveContinuation.produce one.live)).trans
    (sensed_length scope one.live.assignment.assignment).symm
  have secondLength := (compile_length scope (LiveContinuation.produce one.live)).trans
    (sensed_length scope two.live.assignment.assignment).symm
  have inverted := congrArg (fire (advance scope one.live).1.gates) acted
  change fire (compile scope (LiveContinuation.produce one.live))
      (fire (compile scope (LiveContinuation.produce one.live)) (sense scope one.live.assignment.assignment)) =
    fire (compile scope (LiveContinuation.produce one.live))
      (fire (compile scope (LiveContinuation.produce one.live)) (sense scope two.live.assignment.assignment)) at inverted
  rw [fire_involutive _ _ firstLength, fire_involutive _ _ secondLength] at inverted
  exact inverted

theorem future_determines_projection (scope : Scope) {one two : Memory}
    (first : Coherent scope one) (second : Coherent scope two)
    (same : FutureEquivalent (runtimeContract scope) one two) :
    projectMemory scope one = projectMemory scope two := by
  apply runtime_ext
  · apply live_ext
    · apply frontier_read_complete
      exact congrArg Prod.fst same.read
    · exact future_determines_live_values scope same
  · exact futures_determine_connections scope first second same
  · exact (normalize_bank_exact_iff one.bank two.bank).mpr
      ⟨congrArg (fun view : View => view.2.1) same.read,
        congrArg (fun view : View => view.2.2) same.read⟩

theorem minimal_projection_iff_futures (scope : Scope) {one two : Memory}
    (first : Coherent scope one) (second : Coherent scope two) :
    projectMemory scope one = projectMemory scope two ↔ FutureEquivalent (runtimeContract scope) one two :=
  ⟨(liveReduction scope).equal_memory_same_futures, future_determines_projection scope first second⟩

/-- Any exact implementation must retain the distinguishability of this finite
projection, without being required to use its fields or encoding. -/
theorem any_exact_realization_retains_projection (scope : Scope) {Other : Type 3}
    (realization : ExactRealization (runtimeContract scope) Other) {one two : Memory}
    (first : Coherent scope one) (second : Coherent scope two)
    (same : realization.project one = realization.project two) :
    projectMemory scope one = projectMemory scope two :=
  future_determines_projection scope first second (realization.equal_memory_same_futures same)

end ConstitutiveSearch.ReconfigurableMachine.LiveReduction
/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.ReconfigurableMachine.LiveReduction.free_layer_unique
#print axioms ConstitutiveSearch.ReconfigurableMachine.LiveReduction.integration_unique
#print axioms ConstitutiveSearch.ReconfigurableMachine.LiveReduction.provenance_unique
#print axioms ConstitutiveSearch.ReconfigurableMachine.LiveReduction.fresh_difference_unique
#print axioms ConstitutiveSearch.ReconfigurableMachine.LiveReduction.generated_laws_unique
#print axioms ConstitutiveSearch.ReconfigurableMachine.LiveReduction.generated_step_unique
#print axioms ConstitutiveSearch.ReconfigurableMachine.LiveReduction.generation_unique
#print axioms ConstitutiveSearch.ReconfigurableMachine.LiveReduction.frontier_read_complete
#print axioms ConstitutiveSearch.ReconfigurableMachine.LiveReduction.advance_values
#print axioms ConstitutiveSearch.ReconfigurableMachine.LiveReduction.future_determines_live_values
#print axioms ConstitutiveSearch.ReconfigurableMachine.LiveReduction.future_determines_projection
#print axioms ConstitutiveSearch.ReconfigurableMachine.LiveReduction.minimal_projection_iff_futures
#print axioms ConstitutiveSearch.ReconfigurableMachine.LiveReduction.any_exact_realization_retains_projection
/- AXIOM_AUDIT_END -/
