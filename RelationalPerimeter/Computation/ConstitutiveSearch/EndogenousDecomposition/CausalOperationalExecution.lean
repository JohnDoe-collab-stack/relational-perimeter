import RelationalPerimeter.Computation.ConstitutiveSearch.EndogenousDecomposition.InstrumentedExecutionRealization
import RelationalPerimeter.Computation.ConstitutiveSearch.EndogenousDecomposition.PrefixLocalOperationalProduction
import RelationalPerimeter.Computation.ConstitutiveSearch.EndogenousDecomposition.ExecutedRoleIndexedReduction

/-!
# Execution that produces its operational decomposition stage by stage

This is the causal object used by the final certificate.  It does not receive a
completed execution history.  Its executor performs the authoritative stage
construction and, at that same recursive step, forms the local relational
decomposition before recursing from the state just produced.

The older instrumented and causal histories are downstream erasures of this
single object.  They are not inputs from which the operational decomposition is
reconstructed afterwards.
-/

namespace ConstitutiveSearch
namespace EndogenousDecomposition

/--
One execution whose head stage and head decomposition are formed before its
dependent tail.  The type of the head decomposition mentions only the current
executed stage; no completed future is an argument or an index of that head.
-/
inductive CausalOperationalExecutionHistory :
    {depth _count : Nat} → {assignment : SequentialAssignment depth} →
      (state : ThreadedConstitutiveState depth assignment) → Type 2 where
  | nil {depth : Nat} {assignment : SequentialAssignment depth}
      (state : ThreadedConstitutiveState depth assignment) :
      CausalOperationalExecutionHistory (_count := 0) state
  | step {depth count : Nat} {assignment : SequentialAssignment depth}
      {state : ThreadedConstitutiveState depth assignment}
      (head : SequentialStageRun depth assignment)
      (headRun : ThreadedConstitutiveStageRun state head)
      (headProduction : ExecutedStageOperationalProduction
        (causalStageOfThreadedStage headRun))
      (tail : CausalOperationalExecutionHistory
        (_count := count) headRun.nextRun.next) :
      CausalOperationalExecutionHistory (_count := count + 1) state

/--
The authoritative recursion produces the stage, its local decomposition and
the next state in one step, then continues from that next state.
-/
def executeCausalOperationalExecutionHistory
    (count : Nat) : {depth : Nat} → {assignment : SequentialAssignment depth} →
      (state : ThreadedConstitutiveState depth assignment) →
      ThreadedStateFreshForNext state →
      CausalOperationalExecutionHistory (_count := count) state
  | _, _, state, fresh => match count with
    | 0 => .nil state
    | count + 1 =>
        let discoveryRun := runThreadedNextDiscovery state
        match found : discoveryRun.outcome.discovered? with
        | none => False.elim ((runThreadedNextDiscovery_found state fresh) found)
        | some discovery =>
            let built := buildThreadedConstitutiveStage state discoveryRun rfl
              discovery found
              (by
                rw [← runThreadedNextDiscovery_discovered_exact state fresh]
                exact found)
              (runThreadedNextDiscovery_work_le_canonical state fresh)
              (state.decisionsAvoidNext fresh)
            let causalStage := causalStageOfThreadedStage built.run
            let localProduction := prefixLocalOperationalProducer causalStage
            .step built.stage built.run localProduction
              (executeCausalOperationalExecutionHistory count
                built.run.nextRun.next (built.run.nextRun.fresh fresh))

/-- Erase only the operational decomposition, retaining the executed history. -/
def CausalOperationalExecutionHistory.instrumented :
    {depth count : Nat} → {assignment : SequentialAssignment depth} →
      {state : ThreadedConstitutiveState depth assignment} →
      CausalOperationalExecutionHistory (_count := count) state →
      ConstitutiveExecutionHistory (count := count) state
  | _, _, _, _, .nil state => .nil state
  | _, _, _, _, .step head headRun _ tail =>
      .step head headRun tail.instrumented

/-- Erase instrumentation while retaining the causal stages produced in place. -/
def CausalOperationalExecutionHistory.causalRun :
    {depth count : Nat} → {assignment : SequentialAssignment depth} →
      {state : ThreadedConstitutiveState depth assignment} →
      (history : CausalOperationalExecutionHistory (_count := count) state) →
      CausalConstitutiveExecutionHistory count
        (causalStateOfThreadedState state)
  | _, _, _, _, .nil state =>
      CausalConstitutiveExecutionHistory.nil (causalStateOfThreadedState state)
  | _, _, _, _, .step _ headRun _ tail =>
      CausalConstitutiveExecutionHistory.step
        (causalStageOfThreadedStage headRun) tail.causalRun

/-- Read the decomposition produced at each recursive execution step. -/
def CausalOperationalExecutionHistory.stagewiseDecomposition :
    {depth count : Nat} → {assignment : SequentialAssignment depth} →
      {state : ThreadedConstitutiveState depth assignment} →
      (history : CausalOperationalExecutionHistory (_count := count) state) →
      StagewiseExecutedDecompositionHistory history.causalRun
  | _, _, _, _, .nil _ => .nil
  | _, _, _, _, .step _ _ headProduction tail =>
      .step headProduction.decomposition tail.stagewiseDecomposition

/-- Every stored head is the canonical function of its current stage alone. -/
theorem CausalOperationalExecutionHistory.headsArePrefixLocal :
    {depth count : Nat} → {assignment : SequentialAssignment depth} →
      {state : ThreadedConstitutiveState depth assignment} →
      (history : CausalOperationalExecutionHistory (_count := count) state) →
      history.stagewiseDecomposition =
        buildStagewiseExecutedDecompositionHistory history.causalRun
  | _, _, _, _, .nil _ => rfl
  | _, _, _, _, .step _ _ headProduction tail => by
      change StagewiseExecutedDecompositionHistory.step
          headProduction.decomposition tail.stagewiseDecomposition =
        StagewiseExecutedDecompositionHistory.step
          (executedStageDecomposition _) _
      rw [headProduction.decompositionExact, tail.headsArePrefixLocal]
      rfl

/-- The fused executor erases to the pre-existing authoritative executor. -/
theorem executeCausalOperationalExecutionHistory_instrumented_exact
    (count : Nat) {depth : Nat}
    {assignment : SequentialAssignment depth}
    (state : ThreadedConstitutiveState depth assignment)
    (fresh : ThreadedStateFreshForNext state) :
    (executeCausalOperationalExecutionHistory count state fresh).instrumented =
      executeConstitutiveExecutionHistory count state fresh := by
  induction count generalizing depth assignment state with
  | zero => rfl
  | succ count inductionHypothesis =>
      simp only [executeCausalOperationalExecutionHistory,
        executeConstitutiveExecutionHistory]
      split
      case h_1 =>
        rename_i notFound
        exact False.elim
          ((runThreadedNextDiscovery_found state fresh) notFound)
      case h_2 =>
        rename_i leftDiscovery leftFound
        split
        case h_1 =>
          rename_i rightNotFound
          exact False.elim
            ((runThreadedNextDiscovery_found state fresh) rightNotFound)
        case h_2 =>
          rename_i rightDiscovery rightFound
          have sameDiscovery : leftDiscovery = rightDiscovery :=
            Option.some.inj (Eq.trans leftFound.symm rightFound)
          cases sameDiscovery
          simp only [CausalOperationalExecutionHistory.instrumented]
          exact congrArg
            (fun tail => ConstitutiveExecutionHistory.step _ _ tail)
            (inductionHypothesis _ _)

/-- The public fused run starts from the measured public initialization. -/
def publicCausalOperationalExecution (input : Nat) :
    CausalOperationalExecutionHistory
      (_count := resolutionLength input)
      (initialThreadedConstitutiveStateFromInitialization
        (initializeConstitutiveHistory input)) :=
  executeCausalOperationalExecutionHistory
    (resolutionLength input)
    (initialThreadedConstitutiveStateFromInitialization
      (initializeConstitutiveHistory input))
    (initialThreadedConstitutiveStateFromInitialization_fresh
      (initializeConstitutiveHistory input))

/-- Its instrumented erasure is exactly the history exposed by the public run. -/
theorem publicCausalOperationalExecution_instrumented_exact (input : Nat) :
    (publicCausalOperationalExecution input).instrumented =
      (executeConstitutiveResolution input).constitutiveFeedbackHistory := by
  exact executeCausalOperationalExecutionHistory_instrumented_exact
    (resolutionLength input)
    (initialThreadedConstitutiveStateFromInitialization
      (initializeConstitutiveHistory input))
    (initialThreadedConstitutiveStateFromInitialization_fresh
      (initializeConstitutiveHistory input))

end EndogenousDecomposition
end ConstitutiveSearch

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.EndogenousDecomposition.CausalOperationalExecutionHistory
#print axioms ConstitutiveSearch.EndogenousDecomposition.executeCausalOperationalExecutionHistory
#print axioms ConstitutiveSearch.EndogenousDecomposition.CausalOperationalExecutionHistory.instrumented
#print axioms ConstitutiveSearch.EndogenousDecomposition.CausalOperationalExecutionHistory.causalRun
#print axioms ConstitutiveSearch.EndogenousDecomposition.CausalOperationalExecutionHistory.stagewiseDecomposition
#print axioms ConstitutiveSearch.EndogenousDecomposition.CausalOperationalExecutionHistory.headsArePrefixLocal
#print axioms ConstitutiveSearch.EndogenousDecomposition.executeCausalOperationalExecutionHistory_instrumented_exact
#print axioms ConstitutiveSearch.EndogenousDecomposition.publicCausalOperationalExecution
#print axioms ConstitutiveSearch.EndogenousDecomposition.publicCausalOperationalExecution_instrumented_exact
/- AXIOM_AUDIT_END -/
