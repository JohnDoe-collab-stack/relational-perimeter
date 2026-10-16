import RelationalPerimeter.Constitution.Reals.RelationalEquivalence
import RelationalPerimeter.Constitution.Reals.FiniteGroupingProduction

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Executed diagonal production of a relational-real limit response

The numerical diagonal formula is not enough for the constitutive target.  A
limit production first executes the canonical source selected by the Cauchy
modulus, passes that owned execution through the proof-relevant grouping
action, and uses the action's actual output as the payload of the subsequent
limit response.  One package retains this whole chain.
-/

namespace RelationalPerimeter.Constitution.Reals

open StrongPerimetralTurning
open StrongPerimetralTurning.GodelGroupingTower

namespace ExecutedCauchyFamily

/-- Canonical source selected by the modulus for the diagonal response. -/
def diagonalSourceAt
    {P : CircularPresentation}
    (family : ExecutedCauchyFamily P)
    (precision : Nat) : family.SourceAt precision where
  index := family.modulus precision
  readoutPrecision := precision
  indexBeyondModulus := PrecisionExtension.refl (family.modulus precision)
  readoutRefines := PrecisionExtension.refl precision

end ExecutedCauchyFamily

/--
One master package for source execution, grouping, and limit execution at a
single requested precision.
-/
structure ExecutedLimitProduction
    {P : CircularPresentation}
    (family : ExecutedCauchyFamily P)
    (journal : OperationJournal ApproximationPayload)
    (precision : Nat) where
  source : family.ProducedSourceAt precision
  sourceJournalExact : source.journal = journal
  sourceIndexExact : source.source.index = family.modulus precision
  sourcePrecisionExact : source.source.readoutPrecision = precision
  limitExecution :
    ExecutedApproximation P source.afterExecutionState.journal
      (limitPayload precision
        (effectiveLimitGroupedCode family precision source))

namespace ExecutedLimitProduction

/-- The unique grouping output determined by the owned executed source. -/
def groupedCharge
    {P : CircularPresentation}
    {family : ExecutedCauchyFamily P}
    {journal : OperationJournal ApproximationPayload}
    {precision : Nat}
    (production : ExecutedLimitProduction family journal precision) :
    LocalGrouping.GroupedCharge precision
      (family.limitApproximation precision) :=
  effectiveLimitGroupedCharge family precision production.source

/-- Readout projected only after the source, action, and limit response ran. -/
def readout
    {P : CircularPresentation}
    {family : ExecutedCauchyFamily P}
    {journal : OperationJournal ApproximationPayload}
    {precision : Nat}
    (production : ExecutedLimitProduction family journal precision) :
    SignedDyadicCode :=
  production.limitExecution.readout

/-- The executed limit response reads the exact output of the grouping action. -/
theorem readout_is_groupedOutput
    {P : CircularPresentation}
    {family : ExecutedCauchyFamily P}
    {journal : OperationJournal ApproximationPayload}
    {precision : Nat}
    (production : ExecutedLimitProduction family journal precision) :
    production.readout = production.groupedCharge.outputCode :=
  rfl

/-- The master package consumes the readout of its owned source execution. -/
theorem groupedCharge_consumesSourceReadout
    {P : CircularPresentation}
    {family : ExecutedCauchyFamily P}
    {journal : OperationJournal ApproximationPayload}
    {precision : Nat}
    (production : ExecutedLimitProduction family journal precision) :
    production.groupedCharge.consumedCode = production.source.code := by
  exact effectiveLimitGroupedCharge_consumesSourceCode
    family precision production.source

/-- Its grouping action consumes the convergence witness of that same source. -/
theorem groupedCharge_consumesSourceNear
    {P : CircularPresentation}
    {family : ExecutedCauchyFamily P}
    {journal : OperationJournal ApproximationPayload}
    {precision : Nat}
    (production : ExecutedLimitProduction family journal precision) :
    production.groupedCharge.consumedNearTarget =
      production.source.nearLimit :=
  effectiveLimitGroupedCharge_consumesNear
    family precision production.source

/-- The terminal readout is the constructed diagonal limit approximation. -/
theorem readout_is_limitApproximation
    {P : CircularPresentation}
    {family : ExecutedCauchyFamily P}
    {journal : OperationJournal ApproximationPayload}
    {precision : Nat}
    (production : ExecutedLimitProduction family journal precision) :
    production.readout = family.limitApproximation precision := by
  calc
    production.readout = production.groupedCharge.outputCode :=
      production.readout_is_groupedOutput
    _ = family.limitApproximation precision :=
      effectiveLimitGroupedCode_exact family precision production.source

/-- Final journal after the source request and the grouped limit request. -/
def completedJournal
    {P : CircularPresentation}
    {family : ExecutedCauchyFamily P}
    {journal : OperationJournal ApproximationPayload}
    {precision : Nat}
    (production : ExecutedLimitProduction family journal precision) :
    OperationJournal ApproximationPayload :=
  ExecutedApproximation.completedJournal
    production.source.afterExecutionState.journal
    (limitPayload precision production.groupedCharge.outputCode)

/-- The two executed requests add exactly twelve constitutive operations. -/
theorem completedJournal_depth
    {P : CircularPresentation}
    {family : ExecutedCauchyFamily P}
    {journal : OperationJournal ApproximationPayload}
    {precision : Nat}
    (production : ExecutedLimitProduction family journal precision) :
    production.completedJournal.depth = journal.depth + 12 := by
  calc
    production.completedJournal.depth =
        production.source.afterExecutionState.journal.depth + 6 :=
      ExecutedApproximation.completedJournal_depth
        production.source.afterExecutionState.journal
        (limitPayload precision production.groupedCharge.outputCode)
    _ = (production.source.journal.depth + 6) + 6 := by
      rw [ExecutedCauchyFamily.ProducedSourceAt.afterExecutionState_depth]
    _ = (journal.depth + 6) + 6 := by rw [production.sourceJournalExact]
    _ = journal.depth + (6 + 6) :=
      Nat.add_assoc journal.depth 6 6
    _ = journal.depth + 12 := rfl

end ExecutedLimitProduction

/-- Execute the complete diagonal source–grouping–limit chain. -/
def executeLimitProduction
    {P : CircularPresentation}
    (family : ExecutedCauchyFamily P)
    (journal : OperationJournal ApproximationPayload)
    (precision : Nat) :
    ExecutedLimitProduction family journal precision := by
  let source := family.produceSourceAt journal
    (family.diagonalSourceAt precision)
  exact
  { source := source
    sourceJournalExact := rfl
    sourceIndexExact := rfl
    sourcePrecisionExact := rfl
    limitExecution :=
      executeApproximation P source.afterExecutionState.journal
        (limitPayload precision
          (effectiveLimitGroupedCode family precision source)) }

/-!
## One typed master for every finite future

The low-level response continuation can execute an already formed payload.
That is useful as an exact journal bridge, but it does not by itself establish
that a public limit request ran the source search and grouping action from
which its payload must come.  The family-specific master below closes that
gap: a source request owns its source execution, while a limit request owns the
complete `ExecutedLimitProduction` package above.
-/

namespace MasterContinuation

open ConstitutiveSearch.Grouping

/--
The proof-relevant response owned by one typed family request.  The request
index fixes which complete execution must be retained.
-/
structure ExecutedResponse
    {P : CircularPresentation}
    (family : ExecutedCauchyFamily P)
    (state : ResponseContinuation.RichState P)
    (request : family.Request) where
  execution :
    match request with
    | .source _ source =>
        ExecutedApproximation P state.journal
          (sourcePayload source.index source.readoutPrecision
            (ExecutedCauchyFamily.sourceCode source))
    | .limit precision =>
        ExecutedLimitProduction family state.journal precision

/-- The single executable producer used by both state and event projections. -/
def execute
    {P : CircularPresentation}
    (family : ExecutedCauchyFamily P)
    (state : ResponseContinuation.RichState P)
    (request : family.Request) :
    ExecutedResponse family state request := by
  cases request with
  | source precision source =>
      exact
      { execution :=
          family.executeSource state.journal source.index
            source.readoutPrecision }
  | limit precision =>
      exact { execution := executeLimitProduction family state.journal precision }

/-- A retained master may be projected repeatedly, but is supplied only once. -/
abbrev Executor
    {P : CircularPresentation}
    (family : ExecutedCauchyFamily P) : Type _ :=
  (state : ResponseContinuation.RichState P) ->
    (request : family.Request) -> ExecutedResponse family state request

/-- The exact public payload denoted by a typed family request. -/
def requestPayload
    {P : CircularPresentation}
    {family : ExecutedCauchyFamily P}
    (request : family.Request) : ApproximationPayload :=
  request.payload

/-- Journal produced by the execution actually retained in the response. -/
def ExecutedResponse.completedJournal
    {P : CircularPresentation}
    {family : ExecutedCauchyFamily P}
    {state : ResponseContinuation.RichState P}
    {request : family.Request}
    (response : ExecutedResponse family state request) :
    OperationJournal ApproximationPayload := by
  cases request with
  | source precision source =>
      exact ExecutedApproximation.completedJournal state.journal
        (sourcePayload source.index source.readoutPrecision
          (ExecutedCauchyFamily.sourceCode source))
  | limit precision =>
      exact response.execution.completedJournal

/-- Readout projected after the retained source or complete limit execution. -/
def ExecutedResponse.readout
    {P : CircularPresentation}
    {family : ExecutedCauchyFamily P}
    {state : ResponseContinuation.RichState P}
    {request : family.Request}
    (response : ExecutedResponse family state request) : SignedDyadicCode := by
  cases request with
  | source precision source => exact response.execution.readout
  | limit precision => exact response.execution.readout

/-- Every retained response reads exactly the code fixed by its typed request. -/
theorem ExecutedResponse.readout_exact
    {P : CircularPresentation}
    {family : ExecutedCauchyFamily P}
    {state : ResponseContinuation.RichState P}
    {request : family.Request}
    (response : ExecutedResponse family state request) :
    response.readout = (requestPayload request).code := by
  cases request with
  | source precision source => rfl
  | limit precision =>
      exact response.execution.readout_is_limitApproximation

/-- Source requests add six operations; complete limit requests add twelve. -/
def requestOperationCount
    {P : CircularPresentation}
    {family : ExecutedCauchyFamily P} : family.Request -> Nat
  | .source _ _ => 6
  | .limit _ => 12

/-- The completed depth is computed from the owned execution, not assumed. -/
theorem ExecutedResponse.completedJournal_depth
    {P : CircularPresentation}
    {family : ExecutedCauchyFamily P}
    {state : ResponseContinuation.RichState P}
    {request : family.Request}
    (response : ExecutedResponse family state request) :
    response.completedJournal.depth =
      state.journal.depth + requestOperationCount request := by
  cases request with
  | source precision source =>
      exact ExecutedApproximation.completedJournal_depth state.journal
        (sourcePayload source.index source.readoutPrecision
          (ExecutedCauchyFamily.sourceCode source))
  | limit precision => exact response.execution.completedJournal_depth

/-- The rich successor is a projection of the retained master response. -/
def ExecutedResponse.next
    {P : CircularPresentation}
    {family : ExecutedCauchyFamily P}
    {state : ResponseContinuation.RichState P}
    {request : family.Request}
    (response : ExecutedResponse family state request) :
    ResponseContinuation.RichState P :=
  { journal := response.completedJournal
    memory := response.readout }

/-- The normalized event is a second projection of that same response. -/
def ExecutedResponse.event
    {P : CircularPresentation}
    {family : ExecutedCauchyFamily P}
    {state : ResponseContinuation.RichState P}
    {request : family.Request}
    (response : ExecutedResponse family state request) :
    ResponseContinuation.NormalizedEvent :=
  { request := (requestPayload request).request
    startDepth := state.journal.depth
    endDepth := response.completedJournal.depth
    code := response.readout }

/-- Rich next-state projection of the one retained family master. -/
def sourceNext
    {P : CircularPresentation}
    {family : ExecutedCauchyFamily P}
    (executor : Executor family)
    (state : ResponseContinuation.RichState P)
    (request : family.Request) : ResponseContinuation.RichState P :=
  (executor state request).next

/-- Rich event projection of the same retained family master. -/
def sourceEvent
    {P : CircularPresentation}
    {family : ExecutedCauchyFamily P}
    (executor : Executor family)
    (state : ResponseContinuation.RichState P)
    (request : family.Request) : ResponseContinuation.NormalizedEvent :=
  (executor state request).event

/-- Every typed source or limit request has executable positive data. -/
def sourceAllow
    {P : CircularPresentation}
    {family : ExecutedCauchyFamily P}
    (state : ResponseContinuation.RichState P)
    (request : family.Request) : Type :=
  Unit

/-- Reduced transition after the rich master has been constituted. -/
def reducedNext
    {P : CircularPresentation}
    {family : ExecutedCauchyFamily P}
    (state : ResponseContinuation.ReducedState)
    (request : family.Request) : ResponseContinuation.ReducedState :=
  { depth := state.depth + requestOperationCount request
    memory := (requestPayload request).code }

/-- Fixed public event corresponding to the family master. -/
def reducedEvent
    {P : CircularPresentation}
    {family : ExecutedCauchyFamily P}
    (state : ResponseContinuation.ReducedState)
    (request : family.Request) : ResponseContinuation.NormalizedEvent :=
  { request := (requestPayload request).request
    startDepth := state.depth
    endDepth := state.depth + requestOperationCount request
    code := (requestPayload request).code }

def reducedAllow
    {P : CircularPresentation}
    {family : ExecutedCauchyFamily P}
    (state : ResponseContinuation.ReducedState)
    (request : family.Request) : Type :=
  Unit

/--
Exact bridge for typed family requests.  Both operational projections consume
the same `executor`; a limit transition therefore cannot be replaced by an
independent six-phase payload response.
-/
def bridge
    {P : CircularPresentation}
    (family : ExecutedCauchyFamily P)
    (executor : Executor family) :
    Continuation.Exact
      (ResponseContinuation.RichState P)
      ResponseContinuation.ReducedState family.Request
      ResponseContinuation.NormalizedEvent SignedDyadicCode where
  project := ResponseContinuation.project
  sourceNext := sourceNext executor
  reducedNext := reducedNext
  sourceAllow := sourceAllow
  reducedAllow := reducedAllow
  toReduced := fun _ _ _ => Unit.unit
  toSource := fun _ _ _ => Unit.unit
  sourceEvent := sourceEvent executor
  reducedEvent := reducedEvent
  sourceRead := ResponseContinuation.RichState.memory
  reducedRead := ResponseContinuation.ReducedState.memory
  nextLaw := by
    intro state request
    exact ResponseContinuation.ReducedState.equal
      (executor state request).completedJournal_depth
      (executor state request).readout_exact
  eventLaw := by
    intro state request
    exact ResponseContinuation.NormalizedEvent.equal rfl rfl
      (executor state request).completedJournal_depth
      (executor state request).readout_exact
  readLaw := fun _ => rfl

/-- Positive admission of every finite typed family future. -/
def admitAll
    {P : CircularPresentation}
    (family : ExecutedCauchyFamily P)
    (executor : Executor family)
    (state : ResponseContinuation.RichState P) :
    (requests : List family.Request) ->
      Continuation.Admitted
        (bridge family executor).sourceNext
        (bridge family executor).sourceAllow state requests
  | [] => .nil state
  | request :: rest =>
      .cons Unit.unit
        (admitAll family executor
          ((bridge family executor).sourceNext state request) rest)

/-- Exact normalized future under one retained family executor. -/
structure SameNormalizedFuture
    {P : CircularPresentation}
    (family : ExecutedCauchyFamily P)
    (executor : Executor family)
    (first second : ResponseContinuation.RichState P) where
  admittedForward :
    (requests : List family.Request) ->
      Continuation.Admitted
          (bridge family executor).sourceNext
          (bridge family executor).sourceAllow first requests ->
        Continuation.Admitted
          (bridge family executor).sourceNext
          (bridge family executor).sourceAllow second requests
  admittedBackward :
    (requests : List family.Request) ->
      Continuation.Admitted
          (bridge family executor).sourceNext
          (bridge family executor).sourceAllow second requests ->
        Continuation.Admitted
          (bridge family executor).sourceNext
          (bridge family executor).sourceAllow first requests
  next :
    (requests : List family.Request) ->
      (bridge family executor).project
          (Continuation.run
            (bridge family executor).sourceNext first requests) =
        (bridge family executor).project
          (Continuation.run
            (bridge family executor).sourceNext second requests)
  events :
    (requests : List family.Request) ->
      Continuation.events
          (bridge family executor).sourceNext
          (bridge family executor).sourceEvent first requests =
        Continuation.events
          (bridge family executor).sourceNext
          (bridge family executor).sourceEvent second requests
  observations :
    (requests : List family.Request) ->
      Continuation.observations
          (bridge family executor).sourceNext
          (bridge family executor).sourceRead first requests =
        Continuation.observations
          (bridge family executor).sourceNext
          (bridge family executor).sourceRead second requests

/-- Equal public states have identical futures under the same retained master. -/
def sameNormalizedFuture
    {P : CircularPresentation}
    (family : ExecutedCauchyFamily P)
    (executor : Executor family)
    {first second : ResponseContinuation.RichState P}
    (same : (bridge family executor).project first =
      (bridge family executor).project second) :
    SameNormalizedFuture family executor first second where
  admittedForward := by
    intro requests admitted
    apply (bridge family executor).admittedSource
    exact same ▸ (bridge family executor).admitted admitted
  admittedBackward := by
    intro requests admitted
    apply (bridge family executor).admittedSource
    exact same.symm ▸ (bridge family executor).admitted admitted
  next := by
    intro requests
    rw [(bridge family executor).run_exact,
      (bridge family executor).run_exact, same]
  events := by
    intro requests
    rw [(bridge family executor).events_exact,
      (bridge family executor).events_exact, same]
  observations := by
    intro requests
    rw [(bridge family executor).observations_exact,
      (bridge family executor).observations_exact, same]

end MasterContinuation

/--
Sequential completeness together with the executable master production at
every starting journal and every requested precision.  The equality field
prevents this constitutive producer from being paired with a different
logical completeness result.
-/
structure FullyExecutedSequentialCompleteness
    {P : CircularPresentation}
    (family : ExecutedCauchyFamily P) where
  sequential : SequentialCompletenessResult family
  sequentialExact : sequential = effectiveSequentialCompleteness family
  master : MasterContinuation.Executor family
  masterCanonical :
    (state : ResponseContinuation.RichState P) ->
      (request : family.Request) ->
      master state request = MasterContinuation.execute family state request
  produceFiniteGrouping :
    {precision : Nat} ->
      {initial final : OperationJournal ApproximationPayload} ->
      {size : Nat} ->
      (chain :
        ExecutedSourceChain family precision initial final size) ->
      ExecutedFiniteGrouping chain

/--
Construct the universal source–grouping–limit producer from the same family
that constructs the relational limit and its convergence witnesses.
-/
def fullyExecutedSequentialCompleteness
    {P : CircularPresentation}
    (family : ExecutedCauchyFamily P) :
    FullyExecutedSequentialCompleteness family where
  sequential := effectiveSequentialCompleteness family
  sequentialExact := rfl
  master := MasterContinuation.execute family
  masterCanonical := fun _ _ => rfl
  produceFiniteGrouping := executeFiniteGrouping

namespace FullyExecutedSequentialCompleteness

/--
The limit producer is a projection of the retained universal master, not a
second execution installed beside it.
-/
def produceLimit
    {P : CircularPresentation}
    {family : ExecutedCauchyFamily P}
    (completeness : FullyExecutedSequentialCompleteness family)
    (journal : OperationJournal ApproximationPayload)
    (precision : Nat) : ExecutedLimitProduction family journal precision :=
  (completeness.master
    { journal := journal, memory := family.limitApproximation precision }
    (.limit precision)).execution

/-- The retained master projection is exactly the canonical complete producer. -/
theorem produceLimitCanonical
    {P : CircularPresentation}
    {family : ExecutedCauchyFamily P}
    (completeness : FullyExecutedSequentialCompleteness family)
    (journal : OperationJournal ApproximationPayload)
    (precision : Nat) :
    completeness.produceLimit journal precision =
      executeLimitProduction family journal precision := by
  exact congrArg
    (fun response => response.execution)
    (completeness.masterCanonical
      { journal := journal, memory := family.limitApproximation precision }
      (.limit precision))

/-- Every finite typed request list is admitted by the retained master. -/
def allTypedRequestsAdmitted
    {P : CircularPresentation}
    {family : ExecutedCauchyFamily P}
    (completeness : FullyExecutedSequentialCompleteness family)
    (state : ResponseContinuation.RichState P)
    (requests : List family.Request) :
    ConstitutiveSearch.Grouping.Continuation.Admitted
      (MasterContinuation.bridge family completeness.master).sourceNext
      (MasterContinuation.bridge family completeness.master).sourceAllow
      state requests :=
  MasterContinuation.admitAll family completeness.master state requests

/-- Exact state projection for every finite typed future of the master. -/
theorem finiteRunExact
    {P : CircularPresentation}
    {family : ExecutedCauchyFamily P}
    (completeness : FullyExecutedSequentialCompleteness family)
    (state : ResponseContinuation.RichState P)
    (requests : List family.Request) :
    (MasterContinuation.bridge family completeness.master).project
        (ConstitutiveSearch.Grouping.Continuation.run
          (MasterContinuation.bridge family completeness.master).sourceNext
          state requests) =
      ConstitutiveSearch.Grouping.Continuation.run
        (MasterContinuation.bridge family completeness.master).reducedNext
        ((MasterContinuation.bridge family completeness.master).project state)
        requests :=
  (MasterContinuation.bridge family completeness.master).run_exact state requests

/-- Exact normalized events for every finite typed future of the master. -/
theorem finiteEventsExact
    {P : CircularPresentation}
    {family : ExecutedCauchyFamily P}
    (completeness : FullyExecutedSequentialCompleteness family)
    (state : ResponseContinuation.RichState P)
    (requests : List family.Request) :
    ConstitutiveSearch.Grouping.Continuation.events
        (MasterContinuation.bridge family completeness.master).sourceNext
        (MasterContinuation.bridge family completeness.master).sourceEvent
        state requests =
      ConstitutiveSearch.Grouping.Continuation.events
        (MasterContinuation.bridge family completeness.master).reducedNext
        (MasterContinuation.bridge family completeness.master).reducedEvent
        ((MasterContinuation.bridge family completeness.master).project state)
        requests :=
  (MasterContinuation.bridge family completeness.master).events_exact state requests

/-- Exact readouts for every finite typed future of the master. -/
theorem finiteObservationsExact
    {P : CircularPresentation}
    {family : ExecutedCauchyFamily P}
    (completeness : FullyExecutedSequentialCompleteness family)
    (state : ResponseContinuation.RichState P)
    (requests : List family.Request) :
    ConstitutiveSearch.Grouping.Continuation.observations
        (MasterContinuation.bridge family completeness.master).sourceNext
        (MasterContinuation.bridge family completeness.master).sourceRead
        state requests =
      ConstitutiveSearch.Grouping.Continuation.observations
        (MasterContinuation.bridge family completeness.master).reducedNext
        (MasterContinuation.bridge family completeness.master).reducedRead
        ((MasterContinuation.bridge family completeness.master).project state)
        requests :=
  (MasterContinuation.bridge family completeness.master).observations_exact
    state requests

/-- Equal grouped public states share every future of the retained master. -/
def sameNormalizedFuture
    {P : CircularPresentation}
    {family : ExecutedCauchyFamily P}
    (completeness : FullyExecutedSequentialCompleteness family)
    {first second : ResponseContinuation.RichState P}
    (same :
      (MasterContinuation.bridge family completeness.master).project first =
        (MasterContinuation.bridge family completeness.master).project second) :
    MasterContinuation.SameNormalizedFuture family completeness.master
      first second :=
  MasterContinuation.sameNormalizedFuture family completeness.master same

/--
Two actually grouped sources at the same starting depth share every later
typed source/limit future of the retained master.  Their rich journals and
source identities remain distinct.
-/
def groupedSourcesSameMasterFuture
    {P : CircularPresentation}
    {family : ExecutedCauchyFamily P}
    (completeness : FullyExecutedSequentialCompleteness family)
    (precision : Nat)
    (first second : family.ProducedSourceAt precision)
    (sameStartDepth : first.journal.depth = second.journal.depth) :
    MasterContinuation.SameNormalizedFuture family completeness.master
      (groupedFutureState family precision first)
      (groupedFutureState family precision second) :=
  completeness.sameNormalizedFuture
    (groupedSources_project_eq family precision first second sameStartDepth)

/-- Every produced response reads the diagonal limit of the retained family. -/
theorem producedReadoutExact
    {P : CircularPresentation}
    {family : ExecutedCauchyFamily P}
    (completeness : FullyExecutedSequentialCompleteness family)
    (journal : OperationJournal ApproximationPayload)
    (precision : Nat) :
    (completeness.produceLimit journal precision).readout =
      family.limitApproximation precision :=
  (completeness.produceLimit journal precision).readout_is_limitApproximation

/-- The retained logical limit is definitionally the family's construction. -/
theorem sequentialLimitExact
    {P : CircularPresentation}
    {family : ExecutedCauchyFamily P}
    (completeness : FullyExecutedSequentialCompleteness family) :
    completeness.sequential.limit = family.limit := by
  rw [completeness.sequentialExact]
  rfl

/-- Every chronological finite batch is consumed in full by the master. -/
theorem finiteGroupingConsumesEverySource
    {P : CircularPresentation}
    {family : ExecutedCauchyFamily P}
    (completeness : FullyExecutedSequentialCompleteness family)
    {precision : Nat}
    {initial final : OperationJournal ApproximationPayload}
    {size : Nat}
    (chain : ExecutedSourceChain family precision initial final size) :
    (completeness.produceFiniteGrouping chain).grouped.consumed.length = size :=
  (completeness.produceFiniteGrouping chain).consumesEverySource

/-- Every produced finite batch exposes its exact oldest-first evidence list. -/
theorem finiteGroupingConsumesExactChronology
    {P : CircularPresentation}
    {family : ExecutedCauchyFamily P}
    (completeness : FullyExecutedSequentialCompleteness family)
    {precision : Nat}
    {initial final : OperationJournal ApproximationPayload}
    {size : Nat}
    (chain : ExecutedSourceChain family precision initial final size) :
    (completeness.produceFiniteGrouping chain).grouped.consumed =
      HistoricalGrouping.chargesForIndices chain.selection
        (HistoricalGrouping.initialBatchCharge chain.selection).available
        (HistoricalGrouping.allIndices size) :=
  (completeness.produceFiniteGrouping chain).consumedExact

/-- Every finite batch produced by the master returns the same limit target. -/
def finiteGroupingOutputExact
    {P : CircularPresentation}
    {family : ExecutedCauchyFamily P}
    (completeness : FullyExecutedSequentialCompleteness family)
    {precision : Nat}
    {initial final : OperationJournal ApproximationPayload}
    {size : Nat}
    (chain : ExecutedSourceChain family precision initial final size) :
    SameValue
      (completeness.produceFiniteGrouping chain).grouped.outputCode
      (family.limitApproximation precision) :=
  (completeness.produceFiniteGrouping chain).outputExact

end FullyExecutedSequentialCompleteness

end RelationalPerimeter.Constitution.Reals

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Constitution.Reals.ExecutedCauchyFamily.diagonalSourceAt
#print axioms RelationalPerimeter.Constitution.Reals.ExecutedLimitProduction
#print axioms RelationalPerimeter.Constitution.Reals.ExecutedLimitProduction.groupedCharge
#print axioms RelationalPerimeter.Constitution.Reals.ExecutedLimitProduction.readout
#print axioms RelationalPerimeter.Constitution.Reals.ExecutedLimitProduction.readout_is_groupedOutput
#print axioms RelationalPerimeter.Constitution.Reals.ExecutedLimitProduction.groupedCharge_consumesSourceReadout
#print axioms RelationalPerimeter.Constitution.Reals.ExecutedLimitProduction.groupedCharge_consumesSourceNear
#print axioms RelationalPerimeter.Constitution.Reals.ExecutedLimitProduction.readout_is_limitApproximation
#print axioms RelationalPerimeter.Constitution.Reals.ExecutedLimitProduction.completedJournal
#print axioms RelationalPerimeter.Constitution.Reals.ExecutedLimitProduction.completedJournal_depth
#print axioms RelationalPerimeter.Constitution.Reals.executeLimitProduction
#print axioms RelationalPerimeter.Constitution.Reals.MasterContinuation.ExecutedResponse
#print axioms RelationalPerimeter.Constitution.Reals.MasterContinuation.execute
#print axioms RelationalPerimeter.Constitution.Reals.MasterContinuation.Executor
#print axioms RelationalPerimeter.Constitution.Reals.MasterContinuation.requestPayload
#print axioms RelationalPerimeter.Constitution.Reals.MasterContinuation.ExecutedResponse.completedJournal
#print axioms RelationalPerimeter.Constitution.Reals.MasterContinuation.ExecutedResponse.readout
#print axioms RelationalPerimeter.Constitution.Reals.MasterContinuation.ExecutedResponse.readout_exact
#print axioms RelationalPerimeter.Constitution.Reals.MasterContinuation.requestOperationCount
#print axioms RelationalPerimeter.Constitution.Reals.MasterContinuation.ExecutedResponse.completedJournal_depth
#print axioms RelationalPerimeter.Constitution.Reals.MasterContinuation.ExecutedResponse.next
#print axioms RelationalPerimeter.Constitution.Reals.MasterContinuation.ExecutedResponse.event
#print axioms RelationalPerimeter.Constitution.Reals.MasterContinuation.sourceNext
#print axioms RelationalPerimeter.Constitution.Reals.MasterContinuation.sourceEvent
#print axioms RelationalPerimeter.Constitution.Reals.MasterContinuation.sourceAllow
#print axioms RelationalPerimeter.Constitution.Reals.MasterContinuation.reducedNext
#print axioms RelationalPerimeter.Constitution.Reals.MasterContinuation.reducedEvent
#print axioms RelationalPerimeter.Constitution.Reals.MasterContinuation.reducedAllow
#print axioms RelationalPerimeter.Constitution.Reals.MasterContinuation.bridge
#print axioms RelationalPerimeter.Constitution.Reals.MasterContinuation.admitAll
#print axioms RelationalPerimeter.Constitution.Reals.MasterContinuation.SameNormalizedFuture
#print axioms RelationalPerimeter.Constitution.Reals.MasterContinuation.sameNormalizedFuture
#print axioms RelationalPerimeter.Constitution.Reals.FullyExecutedSequentialCompleteness
#print axioms RelationalPerimeter.Constitution.Reals.fullyExecutedSequentialCompleteness
#print axioms RelationalPerimeter.Constitution.Reals.FullyExecutedSequentialCompleteness.produceLimit
#print axioms RelationalPerimeter.Constitution.Reals.FullyExecutedSequentialCompleteness.produceLimitCanonical
#print axioms RelationalPerimeter.Constitution.Reals.FullyExecutedSequentialCompleteness.allTypedRequestsAdmitted
#print axioms RelationalPerimeter.Constitution.Reals.FullyExecutedSequentialCompleteness.finiteRunExact
#print axioms RelationalPerimeter.Constitution.Reals.FullyExecutedSequentialCompleteness.finiteEventsExact
#print axioms RelationalPerimeter.Constitution.Reals.FullyExecutedSequentialCompleteness.finiteObservationsExact
#print axioms RelationalPerimeter.Constitution.Reals.FullyExecutedSequentialCompleteness.sameNormalizedFuture
#print axioms RelationalPerimeter.Constitution.Reals.FullyExecutedSequentialCompleteness.groupedSourcesSameMasterFuture
#print axioms RelationalPerimeter.Constitution.Reals.FullyExecutedSequentialCompleteness.producedReadoutExact
#print axioms RelationalPerimeter.Constitution.Reals.FullyExecutedSequentialCompleteness.sequentialLimitExact
#print axioms RelationalPerimeter.Constitution.Reals.FullyExecutedSequentialCompleteness.finiteGroupingConsumesEverySource
#print axioms RelationalPerimeter.Constitution.Reals.FullyExecutedSequentialCompleteness.finiteGroupingConsumesExactChronology
#print axioms RelationalPerimeter.Constitution.Reals.FullyExecutedSequentialCompleteness.finiteGroupingOutputExact
/- AXIOM_AUDIT_END -/
