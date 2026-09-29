import RelationalPerimeter.Computation.ConstitutiveSearch.EndogenousDecomposition.InstrumentedExecutionRealization
import RelationalPerimeter.Computation.ConstitutiveSearch.EndogenousDecomposition.PrefixLocalOperationalProduction
import RelationalPerimeter.Computation.ConstitutiveSearch.EndogenousDecomposition.ExecutedRoleIndexedReduction

/-!
# Execution that produces its operational decomposition stage by stage

This is the causal object used by the final certificate.  It does not receive a
completed execution history.  Its executor performs the authoritative stage
construction and, at that same recursive step, forms the local relational
decomposition before recursing from the state just produced.

The instrumented and causal histories are downstream erasures of this single
object. They are not inputs from which the operational decomposition is
reconstructed afterwards.
-/

namespace ConstitutiveSearch
namespace EndogenousDecomposition

/-- The root prefix before the first operational production. -/
abbrev InitialOperationalPrefix : Type 2 := ULift.{2, 0} Unit

/-- Canonical empty root prefix. -/
def initialOperationalPrefix : InitialOperationalPrefix :=
  ULift.up ()

/--
One execution whose head stage and head decomposition are formed before its
dependent tail.  The type of the head decomposition mentions only the current
executed stage; no completed future is an argument or an index of that head.
-/
inductive CausalOperationalExecutionHistory :
    {Context : Type 2} → (context : Context) →
      {depth _count : Nat} → {assignment : SequentialAssignment depth} →
      (state : ThreadedConstitutiveState depth assignment) → Type 3 where
  | nil {Context : Type 2} (context : Context)
      {depth : Nat} {assignment : SequentialAssignment depth}
      (state : ThreadedConstitutiveState depth assignment) :
      CausalOperationalExecutionHistory context (_count := 0) state
  | step {Context : Type 2} {context : Context}
      {depth count : Nat} {assignment : SequentialAssignment depth}
      {state : ThreadedConstitutiveState depth assignment}
      (head : SequentialStageRun depth assignment)
      (headRun : ThreadedConstitutiveStageRun state head)
      (headProduction : ExecutedStageOperationalProduction
        context (causalStageOfThreadedStage headRun))
      (tail : CausalOperationalExecutionHistory
        headProduction (_count := count) headRun.nextRun.next) :
      CausalOperationalExecutionHistory context (_count := count + 1) state

/--
The authoritative recursion produces the stage, its local decomposition and
the next state in one step, then continues from that next state.
-/
def executeCausalOperationalExecutionHistory
    (count : Nat) : {Context : Type 2} → (context : Context) →
      {depth : Nat} → {assignment : SequentialAssignment depth} →
      (state : ThreadedConstitutiveState depth assignment) →
      ThreadedStateFreshForNext state →
      CausalOperationalExecutionHistory context (_count := count) state
  | _, context, _, _, state, fresh => match count with
    | 0 => .nil context state
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
            let localProduction :=
              prefixLocalOperationalProducer context causalStage
            .step built.stage built.run localProduction
              (executeCausalOperationalExecutionHistory count
                localProduction built.run.nextRun.next
                (built.run.nextRun.fresh fresh))

/-- Erase only the operational decomposition, retaining the executed history. -/
def CausalOperationalExecutionHistory.instrumented :
    {Context : Type 2} → {context : Context} →
      {depth count : Nat} → {assignment : SequentialAssignment depth} →
      {state : ThreadedConstitutiveState depth assignment} →
      CausalOperationalExecutionHistory context (_count := count) state →
      ConstitutiveExecutionHistory (count := count) state
  | _, _, _, _, _, _, .nil _ state => .nil state
  | _, _, _, _, _, _, .step head headRun _ tail =>
      .step head headRun tail.instrumented

/-- Erase instrumentation while retaining the causal stages produced in place. -/
def CausalOperationalExecutionHistory.causalRun :
    {Context : Type 2} → {context : Context} →
      {depth count : Nat} → {assignment : SequentialAssignment depth} →
      {state : ThreadedConstitutiveState depth assignment} →
      (history : CausalOperationalExecutionHistory context (_count := count) state) →
      CausalConstitutiveExecutionHistory count
        (causalStateOfThreadedState state)
  | _, _, _, _, _, _, .nil _ state =>
      CausalConstitutiveExecutionHistory.nil (causalStateOfThreadedState state)
  | _, _, _, _, _, _, .step _ headRun _ tail =>
      CausalConstitutiveExecutionHistory.step
        (causalStageOfThreadedStage headRun) tail.causalRun

/--
The causal run stored by the fused recursion is exactly the structural erasure
of its authoritative instrumented execution; this is proved for every fused
history, not only for the public instance.
-/
theorem CausalOperationalExecutionHistory.causalRun_exact :
    {Context : Type 2} → {context : Context} →
      {depth count : Nat} → {assignment : SequentialAssignment depth} →
      {state : ThreadedConstitutiveState depth assignment} →
      (history : CausalOperationalExecutionHistory context (_count := count) state) →
      history.causalRun =
        causalHistoryOfInstrumentedHistory history.instrumented
  | _, _, _, _, _, _, .nil _ _ => rfl
  | _, _, _, _, _, _, .step _ _ _ tail => by
      simp only [CausalOperationalExecutionHistory.causalRun,
        CausalOperationalExecutionHistory.instrumented,
        causalHistoryOfInstrumentedHistory]
      rw [tail.causalRun_exact]

/-- Read the decomposition produced at each recursive execution step. -/
def CausalOperationalExecutionHistory.stagewiseDecomposition :
    {Context : Type 2} → {context : Context} →
      {depth count : Nat} → {assignment : SequentialAssignment depth} →
      {state : ThreadedConstitutiveState depth assignment} →
      (history : CausalOperationalExecutionHistory context (_count := count) state) →
      StagewiseExecutedDecompositionHistory history.causalRun
  | _, _, _, _, _, _, .nil _ _ => .nil
  | _, _, _, _, _, _, .step _ _ headProduction tail =>
      .step headProduction.decomposition tail.stagewiseDecomposition

/-- Every stored head is the canonical function of its current stage alone. -/
theorem CausalOperationalExecutionHistory.headsArePrefixLocal :
    {Context : Type 2} → {context : Context} →
      {depth count : Nat} → {assignment : SequentialAssignment depth} →
      {state : ThreadedConstitutiveState depth assignment} →
      (history : CausalOperationalExecutionHistory context (_count := count) state) →
      history.stagewiseDecomposition =
        buildStagewiseExecutedDecompositionHistory history.causalRun
  | _, _, _, _, _, _, .nil _ _ => rfl
  | _, _, _, _, _, _, .step _ _ headProduction tail => by
      change StagewiseExecutedDecompositionHistory.step
          headProduction.decomposition tail.stagewiseDecomposition =
        StagewiseExecutedDecompositionHistory.step
          (executedStageDecomposition _) _
      rw [headProduction.decompositionExact, tail.headsArePrefixLocal]
      rfl

/-- The fused executor erases to the pre-existing authoritative executor. -/
theorem executeCausalOperationalExecutionHistory_instrumented_exact
    (count : Nat) {Context : Type 2} (context : Context) {depth : Nat}
    {assignment : SequentialAssignment depth}
    (state : ThreadedConstitutiveState depth assignment)
    (fresh : ThreadedStateFreshForNext state) :
    (executeCausalOperationalExecutionHistory count context state fresh).instrumented =
      executeConstitutiveExecutionHistory count state fresh := by
  induction count generalizing Context context depth assignment state with
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
            (inductionHypothesis _ _ _)

/-- The public fused run starts from the measured public initialization. -/
def publicCausalOperationalExecution (input : Nat) :
    CausalOperationalExecutionHistory
      initialOperationalPrefix
      (_count := resolutionLength input)
      (initialThreadedConstitutiveStateFromInitialization
        (initializeConstitutiveHistory input)) :=
  executeCausalOperationalExecutionHistory
    (resolutionLength input)
    initialOperationalPrefix
    (initialThreadedConstitutiveStateFromInitialization
      (initializeConstitutiveHistory input))
    (initialThreadedConstitutiveStateFromInitialization_fresh
      (initializeConstitutiveHistory input))

/--
The authoritative public roles are constituted directly from the sole fused
execution.  No projected history defines a parallel scientific carrier.
-/
def publicRelationalConstitutiveRoles (input : Nat) :=
  (publicCausalOperationalExecution input).stagewiseDecomposition.roles

/-- The unique public source carrier, read from the fused constitutive roles. -/
def publicRoleProfileFiniteCarrier (input : Nat) : Extensive.FiniteCarrier :=
  roleProfileFiniteCarrier (publicRelationalConstitutiveRoles input)

theorem publicRoleProfileFiniteCarrier_width (input : Nat) :
    (publicRoleProfileFiniteCarrier input).frontier.length =
      2 ^ (input + 1) :=
  roleProfileFiniteCarrier_width (publicRelationalConstitutiveRoles input)

/-- Public role-carrier form of the exact exponential-width equivalence. -/
theorem public_exponentialWidth_iff_distinctSeparateConservation
    (input : Nat)
    (regime : Extensive.ObligationRegime
      (publicRoleProfileFiniteCarrier input)) :
    regime.frontier.length = 2 ^ (input + 1) ↔
      ConservesRoleIdentitiesAsDistinctSeparatelyAddressable regime :=
  roleConstituted_exponentialWidth_iff_distinctSeparateConservation
    (publicRelationalConstitutiveRoles input) regime

/-- Public factorized-addressing form of the same exact equivalence. -/
theorem public_exponentialWidth_iff_exactRegimeCapacity
    (input : Nat)
    (regime : Extensive.ObligationRegime
      (publicRoleProfileFiniteCarrier input)) :
    regime.frontier.length = 2 ^ (input + 1) ↔
      Nonempty
        (Extensive.ExactRegimeSeparateCapacity regime
          (publicRoleProfileFiniteCarrier input).frontier.length) :=
  roleConstituted_exponentialWidth_iff_exactRegimeCapacity
    (publicRelationalConstitutiveRoles input) regime

/-- Its instrumented erasure is exactly the history exposed by the public run. -/
theorem publicCausalOperationalExecution_instrumented_exact (input : Nat) :
    (publicCausalOperationalExecution input).instrumented =
      (executeConstitutiveResolution input).constitutiveFeedbackHistory := by
  exact executeCausalOperationalExecutionHistory_instrumented_exact
    (resolutionLength input)
    initialOperationalPrefix
    (initialThreadedConstitutiveStateFromInitialization
      (initializeConstitutiveHistory input))
    (initialThreadedConstitutiveStateFromInitialization_fresh
      (initializeConstitutiveHistory input))

/-- The fused public causal run is the causal run of the authoritative public realization. -/
theorem publicCausalOperationalExecution_causalRun_exact (input : Nat) :
    (publicCausalOperationalExecution input).causalRun =
      (publicInstrumentedExecutionRealization input).causalRun := by
  exact Eq.trans
    (publicCausalOperationalExecution input).causalRun_exact
    (congrArg causalHistoryOfInstrumentedHistory
      (publicCausalOperationalExecution_instrumented_exact input))

/-- The roles constituted from the fused run are definitionally the public roles. -/
theorem publicCausalOperationalExecution_roles_exact (input : Nat) :
    (publicCausalOperationalExecution input).stagewiseDecomposition.roles =
      publicRelationalConstitutiveRoles input :=
  rfl

end EndogenousDecomposition
end ConstitutiveSearch

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.EndogenousDecomposition.InitialOperationalPrefix
#print axioms ConstitutiveSearch.EndogenousDecomposition.initialOperationalPrefix
#print axioms ConstitutiveSearch.EndogenousDecomposition.CausalOperationalExecutionHistory
#print axioms ConstitutiveSearch.EndogenousDecomposition.executeCausalOperationalExecutionHistory
#print axioms ConstitutiveSearch.EndogenousDecomposition.CausalOperationalExecutionHistory.instrumented
#print axioms ConstitutiveSearch.EndogenousDecomposition.CausalOperationalExecutionHistory.causalRun
#print axioms ConstitutiveSearch.EndogenousDecomposition.CausalOperationalExecutionHistory.causalRun_exact
#print axioms ConstitutiveSearch.EndogenousDecomposition.CausalOperationalExecutionHistory.stagewiseDecomposition
#print axioms ConstitutiveSearch.EndogenousDecomposition.CausalOperationalExecutionHistory.headsArePrefixLocal
#print axioms ConstitutiveSearch.EndogenousDecomposition.executeCausalOperationalExecutionHistory_instrumented_exact
#print axioms ConstitutiveSearch.EndogenousDecomposition.publicCausalOperationalExecution
#print axioms ConstitutiveSearch.EndogenousDecomposition.publicRelationalConstitutiveRoles
#print axioms ConstitutiveSearch.EndogenousDecomposition.publicRoleProfileFiniteCarrier
#print axioms ConstitutiveSearch.EndogenousDecomposition.publicRoleProfileFiniteCarrier_width
#print axioms ConstitutiveSearch.EndogenousDecomposition.public_exponentialWidth_iff_distinctSeparateConservation
#print axioms ConstitutiveSearch.EndogenousDecomposition.public_exponentialWidth_iff_exactRegimeCapacity
#print axioms ConstitutiveSearch.EndogenousDecomposition.publicCausalOperationalExecution_instrumented_exact
#print axioms ConstitutiveSearch.EndogenousDecomposition.publicCausalOperationalExecution_causalRun_exact
#print axioms ConstitutiveSearch.EndogenousDecomposition.publicCausalOperationalExecution_roles_exact
/- AXIOM_AUDIT_END -/
