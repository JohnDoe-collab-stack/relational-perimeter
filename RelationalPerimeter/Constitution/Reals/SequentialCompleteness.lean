import RelationalPerimeter.Constitution.Reals.HistoricalGrouping
import RelationalPerimeter.Constitution.Reals.ResponseContinuation

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Effective sequential completeness of relational reals

A relational real is an effective precision-indexed response module on one
fixed circular presentation.  Every response is executed through the shared
six-phase journal before its dyadic readout is available.  Coherence is
positive `Near` data, not equality of source codes.

An executed Cauchy family supplies an explicit modulus and its monotonicity.
The limit is constructed by the diagonal response
`family (modulus p)` at precision `p`.  Cauchy data proves both coherence of
that response and convergence.  Local grouping specifications then make the
same convergence witnesses operational: finite source views normalize to the
limit target, extend historically, and preserve source identities.
-/

namespace RelationalPerimeter.Constitution.Reals

open StrongPerimetralTurning
open StrongPerimetralTurning.GodelGroupingTower

/-- One effective relational real over a fixed constitutive perimeter. -/
structure RelationalReal (P : CircularPresentation) where
  approximation : Nat -> SignedDyadicCode
  coherent :
    (coarse leftPrecision rightPrecision : Nat) ->
      PrecisionExtension coarse leftPrecision ->
      PrecisionExtension coarse rightPrecision ->
      Near coarse
        (approximation leftPrecision)
        (approximation rightPrecision)
  respond :
    (journal : OperationJournal ApproximationPayload) ->
      (precision : Nat) ->
      ExecutedApproximation P journal
        (limitPayload precision (approximation precision))

namespace RelationalReal

/-- Every real readout is projected from its executed response package. -/
def executedReadout
    {P : CircularPresentation}
    (real : RelationalReal P)
    (journal : OperationJournal ApproximationPayload)
    (precision : Nat) : SignedDyadicCode :=
  (real.respond journal precision).readout

theorem executedReadout_exact
    {P : CircularPresentation}
    (real : RelationalReal P)
    (journal : OperationJournal ApproximationPayload)
    (precision : Nat) :
    real.executedReadout journal precision = real.approximation precision :=
  rfl

/-- A signed dyadic generates a constant relational real at every scale. -/
def constant
    (P : CircularPresentation)
    (code : SignedDyadicCode) : RelationalReal P where
  approximation := fun precision => code.raise precision
  coherent := by
    intro coarse leftPrecision rightPrecision leftExtension rightExtension
    exact
      ((SameValue.raiseExact code leftPrecision).symm.trans
        (SameValue.raiseExact code rightPrecision)).toNear coarse
  respond := fun journal precision =>
    executeApproximation P journal
      (limitPayload precision (code.raise precision))

end RelationalReal

/--
An effective Cauchy family.  Indices and readout precisions are independently
extended from the requested coarse precision; they are not conflated with
journal depth.
-/
structure ExecutedCauchyFamily (P : CircularPresentation) where
  term : Nat -> RelationalReal P
  modulus : Nat -> Nat
  modulusMonotone :
    {coarse fine : Nat} ->
      PrecisionExtension coarse fine ->
      PrecisionExtension (modulus coarse) (modulus fine)
  cauchy :
    {precision firstIndex secondIndex firstReadout secondReadout : Nat} ->
      PrecisionExtension (modulus precision) firstIndex ->
      PrecisionExtension (modulus precision) secondIndex ->
      PrecisionExtension precision firstReadout ->
      PrecisionExtension precision secondReadout ->
      Near precision
        ((term firstIndex).approximation firstReadout)
        ((term secondIndex).approximation secondReadout)

namespace ExecutedCauchyFamily

/-- Execute one source-family request in the shared constitutive history. -/
def executeSource
    {P : CircularPresentation}
    (family : ExecutedCauchyFamily P)
    (journal : OperationJournal ApproximationPayload)
    (index precision : Nat) :
    ExecutedApproximation P journal
      (sourcePayload index precision
        ((family.term index).approximation precision)) :=
  executeApproximation P journal
    (sourcePayload index precision
      ((family.term index).approximation precision))

/-- The diagonal code selected constructively for the limit response. -/
def limitApproximation
    {P : CircularPresentation}
    (family : ExecutedCauchyFamily P)
    (precision : Nat) : SignedDyadicCode :=
  (family.term (family.modulus precision)).approximation precision

/-- The Cauchy witnesses construct the effective limit response module. -/
def limit
    {P : CircularPresentation}
    (family : ExecutedCauchyFamily P) : RelationalReal P where
  approximation := family.limitApproximation
  coherent := by
    intro coarse leftPrecision rightPrecision leftExtension rightExtension
    exact family.cauchy
      (family.modulusMonotone leftExtension)
      (family.modulusMonotone rightExtension)
      leftExtension
      rightExtension
  respond := fun journal precision =>
    executeApproximation P journal
      (limitPayload precision (family.limitApproximation precision))

/-- One source admitted by the modulus at one requested precision. -/
structure SourceAt
    {P : CircularPresentation}
    (family : ExecutedCauchyFamily P)
    (precision : Nat) where
  index : Nat
  readoutPrecision : Nat
  indexBeyondModulus :
    PrecisionExtension (family.modulus precision) index
  readoutRefines : PrecisionExtension precision readoutPrecision

def sourceCode
    {P : CircularPresentation}
    {family : ExecutedCauchyFamily P}
    {precision : Nat}
    (source : family.SourceAt precision) : SignedDyadicCode :=
  (family.term source.index).approximation source.readoutPrecision

/-- Every admitted source is near the diagonal limit response. -/
def sourceNearLimit
    {P : CircularPresentation}
    {family : ExecutedCauchyFamily P}
    {precision : Nat}
    (source : family.SourceAt precision) :
    Near precision (sourceCode source) (family.limitApproximation precision) :=
  family.cauchy
    source.indexBeyondModulus
    (PrecisionExtension.refl (family.modulus precision))
    source.readoutRefines
    (PrecisionExtension.refl precision)

/--
A source made available to grouping is not a bare index: it owns the actual
executed approximation package from which its code and provenance are read.
-/
structure ProducedSourceAt
    {P : CircularPresentation}
    (family : ExecutedCauchyFamily P)
    (precision : Nat) where
  journal : OperationJournal ApproximationPayload
  source : family.SourceAt precision
  execution :
    ExecutedApproximation P journal
      (sourcePayload source.index source.readoutPrecision
        (sourceCode source))

/-- Execute and package one admitted source for use by the grouping rules. -/
def produceSourceAt
    {P : CircularPresentation}
    (family : ExecutedCauchyFamily P)
    (journal : OperationJournal ApproximationPayload)
    {precision : Nat}
    (source : family.SourceAt precision) :
    family.ProducedSourceAt precision :=
  { journal := journal
    source := source
    execution := family.executeSource journal source.index source.readoutPrecision }

/-- The source code is projected from the owned execution. -/
def ProducedSourceAt.code
    {P : CircularPresentation}
    {family : ExecutedCauchyFamily P}
    {precision : Nat}
    (source : family.ProducedSourceAt precision) : SignedDyadicCode :=
  source.execution.readout

theorem ProducedSourceAt.code_exact
    {P : CircularPresentation}
    {family : ExecutedCauchyFamily P}
    {precision : Nat}
    (source : family.ProducedSourceAt precision) :
    source.code = sourceCode source.source :=
  rfl

/-- Proximity is consumed for the code read from the actual source execution. -/
def ProducedSourceAt.nearLimit
    {P : CircularPresentation}
    {family : ExecutedCauchyFamily P}
    {precision : Nat}
    (source : family.ProducedSourceAt precision) :
    Near precision source.code (family.limitApproximation precision) :=
  family.sourceNearLimit source.source

/-- Fixed global grouping envelope at a requested precision. -/
def groupingEnvelope
    {P : CircularPresentation}
    (family : ExecutedCauchyFamily P)
    (precision : Nat) : LocalGrouping.Specification where
  Source := family.ProducedSourceAt precision
  precision := precision
  sourceCode := ProducedSourceAt.code
  targetCode := family.limitApproximation precision
  sourceNearTarget := ProducedSourceAt.nearLimit

/-- Every finite future is governed by the fixed envelope at that precision. -/
def groupingFutureContract
    {P : CircularPresentation}
    (family : ExecutedCauchyFamily P)
    (precision : Nat) :
    HistoricalGrouping.FutureContract (family.groupingEnvelope precision) :=
  HistoricalGrouping.futureContract _

/-- Public family request: a certified source or a constructed limit response. -/
inductive Request
    {P : CircularPresentation}
    (family : ExecutedCauchyFamily P) : Type
  | source (precision : Nat) (source : family.SourceAt precision)
  | limit (precision : Nat)

/-- Translate a typed family request to the unique executable payload. -/
def Request.payload
    {P : CircularPresentation}
    {family : ExecutedCauchyFamily P}
    (request : family.Request) : ApproximationPayload := by
  cases request with
  | source precision source =>
      exact sourcePayload source.index source.readoutPrecision (sourceCode source)
  | limit precision =>
      exact limitPayload precision (family.limitApproximation precision)

/-- Translate a finite typed future without changing its order. -/
def requestPayloads
    {P : CircularPresentation}
    (family : ExecutedCauchyFamily P)
    (requests : List family.Request) : List ApproximationPayload :=
  requests.map Request.payload

end ExecutedCauchyFamily

/--
Convergence contains both its numerical witness and the executions from which
the source and limit readouts are projected.
-/
structure ExecutedConvergence
    {P : CircularPresentation}
    (family : ExecutedCauchyFamily P)
    (limit : RelationalReal P) where
  response : Nat -> Nat
  responseExact : response = family.modulus
  near :
    (precision : Nat) ->
      (source : family.SourceAt precision) ->
      Near precision (ExecutedCauchyFamily.sourceCode source)
        (limit.approximation precision)
  executeSource :
    (journal : OperationJournal ApproximationPayload) ->
      (precision : Nat) ->
      (source : family.SourceAt precision) ->
      ExecutedApproximation P journal
        (sourcePayload source.index source.readoutPrecision
          (ExecutedCauchyFamily.sourceCode source))
  executeLimit :
    (journal : OperationJournal ApproximationPayload) ->
      (precision : Nat) ->
      ExecutedApproximation P journal
        (limitPayload precision (limit.approximation precision))
  envelope :
    (precision : Nat) -> LocalGrouping.Specification
  envelopeExact :
    (precision : Nat) ->
      envelope precision = family.groupingEnvelope precision
  future :
    (precision : Nat) ->
      HistoricalGrouping.FutureContract (envelope precision)

namespace ExecutedConvergence

/-- The source readout in convergence comes from the source execution. -/
theorem sourceReadout_exact
    {P : CircularPresentation}
    {family : ExecutedCauchyFamily P}
    {limit : RelationalReal P}
    (convergence : ExecutedConvergence family limit)
    (journal : OperationJournal ApproximationPayload)
    (precision : Nat)
    (source : family.SourceAt precision) :
    (convergence.executeSource journal precision source).readout =
      ExecutedCauchyFamily.sourceCode source :=
  rfl

/-- The limit readout in convergence comes from the limit execution. -/
theorem limitReadout_exact
    {P : CircularPresentation}
    {family : ExecutedCauchyFamily P}
    {limit : RelationalReal P}
    (convergence : ExecutedConvergence family limit)
    (journal : OperationJournal ApproximationPayload)
    (precision : Nat) :
    (convergence.executeLimit journal precision).readout =
      limit.approximation precision :=
  rfl

end ExecutedConvergence

/-- The effective limit together with executed convergence at every precision. -/
structure SequentialCompletenessResult
    {P : CircularPresentation}
    (family : ExecutedCauchyFamily P) where
  limit : RelationalReal P
  convergence : ExecutedConvergence family limit
  allFiniteRequestsAdmitted :
    (state : ResponseContinuation.RichState P) ->
      (inputs : List ApproximationPayload) ->
      ConstitutiveSearch.Grouping.Continuation.Admitted
        (ResponseContinuation.bridge P).sourceNext
        (ResponseContinuation.bridge P).sourceAllow state inputs
  allTypedRequestsAdmitted :
    (state : ResponseContinuation.RichState P) ->
      (requests : List family.Request) ->
      ConstitutiveSearch.Grouping.Continuation.Admitted
        (ResponseContinuation.bridge P).sourceNext
        (ResponseContinuation.bridge P).sourceAllow state
        (family.requestPayloads requests)
  finiteRunExact :
    (state : ResponseContinuation.RichState P) ->
      (inputs : List ApproximationPayload) ->
      (ResponseContinuation.bridge P).project
          (ConstitutiveSearch.Grouping.Continuation.run
            (ResponseContinuation.bridge P).sourceNext state inputs) =
        ConstitutiveSearch.Grouping.Continuation.run
          (ResponseContinuation.bridge P).reducedNext
          ((ResponseContinuation.bridge P).project state) inputs
  finiteEventsExact :
    (state : ResponseContinuation.RichState P) ->
      (inputs : List ApproximationPayload) ->
      ConstitutiveSearch.Grouping.Continuation.events
          (ResponseContinuation.bridge P).sourceNext
          (ResponseContinuation.bridge P).sourceEvent state inputs =
        ConstitutiveSearch.Grouping.Continuation.events
          (ResponseContinuation.bridge P).reducedNext
          (ResponseContinuation.bridge P).reducedEvent
          ((ResponseContinuation.bridge P).project state) inputs
  finiteObservationsExact :
    (state : ResponseContinuation.RichState P) ->
      (inputs : List ApproximationPayload) ->
      ConstitutiveSearch.Grouping.Continuation.observations
          (ResponseContinuation.bridge P).sourceNext
          (ResponseContinuation.bridge P).sourceRead state inputs =
        ConstitutiveSearch.Grouping.Continuation.observations
          (ResponseContinuation.bridge P).reducedNext
          (ResponseContinuation.bridge P).reducedRead
          ((ResponseContinuation.bridge P).project state) inputs
  sameNormalizedFuture :
    {first second : ResponseContinuation.RichState P} ->
      (ResponseContinuation.bridge P).project first =
        (ResponseContinuation.bridge P).project second ->
      ResponseContinuation.SameNormalizedFuture P first second

/--
Effective sequential completeness: no limit is assumed.  It is produced from
the family and its explicit Cauchy modulus.
-/
def effectiveSequentialCompleteness
    {P : CircularPresentation}
    (family : ExecutedCauchyFamily P) :
    SequentialCompletenessResult family := by
  let producedLimit := family.limit
  exact
  { limit := producedLimit
    convergence :=
    { response := family.modulus
      responseExact := rfl
      near := fun precision source => family.sourceNearLimit source
      executeSource := fun journal precision source =>
        family.executeSource journal source.index source.readoutPrecision
      executeLimit := fun journal precision =>
        producedLimit.respond journal precision
      envelope := family.groupingEnvelope
      envelopeExact := fun _ => rfl
      future := fun precision => family.groupingFutureContract precision }
    allFiniteRequestsAdmitted := ResponseContinuation.admitAll P
    allTypedRequestsAdmitted := fun state requests =>
      ResponseContinuation.admitAll P state (family.requestPayloads requests)
    finiteRunExact := ResponseContinuation.finiteRun_exact P
    finiteEventsExact := ResponseContinuation.finiteEvents_exact P
    finiteObservationsExact := ResponseContinuation.finiteObservations_exact P
    sameNormalizedFuture := ResponseContinuation.sameNormalizedFuture P }

/-- Every constructed limit request is admitted from every rich state. -/
def limitRequestAdmitted
    {P : CircularPresentation}
    (family : ExecutedCauchyFamily P)
    (state : ResponseContinuation.RichState P)
    (precision : Nat) :
    ConstitutiveSearch.Grouping.Continuation.Admitted
      (ResponseContinuation.bridge P).sourceNext
      (ResponseContinuation.bridge P).sourceAllow state
      (family.requestPayloads [ExecutedCauchyFamily.Request.limit precision]) :=
  (effectiveSequentialCompleteness family).allTypedRequestsAdmitted state
    [ExecutedCauchyFamily.Request.limit precision]

/-- Proof-relevant resource returned by grouping one actually executed source. -/
def effectiveLimitGroupedCharge
    {P : CircularPresentation}
    (family : ExecutedCauchyFamily P)
    (precision : Nat)
    (source : family.ProducedSourceAt precision) :
    LocalGrouping.GroupedCharge precision
      (family.limitApproximation precision) :=
  (LocalGrouping.acceptanceAction
    (family.groupingEnvelope precision)).transport
      (ConstitutiveSearch.Grouping.Trace.one
        (LocalGrouping.Step.group
          (specification := family.groupingEnvelope precision)
          (show (family.groupingEnvelope precision).Source from source)))
      (LocalGrouping.sourceCharge
        (family.groupingEnvelope precision) source)

/-- Code projected from the proof-relevant output of the grouping action. -/
def effectiveLimitGroupedCode
    {P : CircularPresentation}
    (family : ExecutedCauchyFamily P)
    (precision : Nat)
    (source : family.ProducedSourceAt precision) : SignedDyadicCode :=
  (effectiveLimitGroupedCharge family precision source).outputCode

/-- The grouping action returns exactly the constructed limit code. -/
theorem effectiveLimitGroupedCode_exact
    {P : CircularPresentation}
    (family : ExecutedCauchyFamily P)
    (precision : Nat)
    (source : family.ProducedSourceAt precision) :
    effectiveLimitGroupedCode family precision source =
      family.limitApproximation precision :=
  LocalGrouping.sourceTransport_exact
    (family.groupingEnvelope precision) source
    (LocalGrouping.sourceCharge
      (family.groupingEnvelope precision) source)

/-- Grouping retains the exact readout of the owned source execution. -/
theorem effectiveLimitGroupedCharge_consumesSourceCode
    {P : CircularPresentation}
    (family : ExecutedCauchyFamily P)
    (precision : Nat)
    (source : family.ProducedSourceAt precision) :
    (effectiveLimitGroupedCharge family precision source).consumedCode =
      source.code :=
  LocalGrouping.sourceTransport_consumedCode
    (family.groupingEnvelope precision) source
    (LocalGrouping.sourceCharge
      (family.groupingEnvelope precision) source)

/-- Grouping retains the exact positive proximity witness it consumed. -/
theorem effectiveLimitGroupedCharge_consumesNear
    {P : CircularPresentation}
    (family : ExecutedCauchyFamily P)
    (precision : Nat)
    (source : family.ProducedSourceAt precision) :
    (effectiveLimitGroupedCharge family precision source).consumedNearTarget =
      source.nearLimit :=
  rfl

/--
The rich state immediately after the owned source execution.  No source
response is reconstructed: both the journal and the memory are projected from
the execution already stored by `ProducedSourceAt`.
-/
def ExecutedCauchyFamily.ProducedSourceAt.afterExecutionState
    {P : CircularPresentation}
    {family : ExecutedCauchyFamily P}
    {precision : Nat}
    (source : family.ProducedSourceAt precision) :
    ResponseContinuation.RichState P :=
  { journal :=
      ExecutedApproximation.completedJournal source.journal
        (sourcePayload source.source.index source.source.readoutPrecision
          (ExecutedCauchyFamily.sourceCode source.source))
    memory := source.execution.readout }

theorem ExecutedCauchyFamily.ProducedSourceAt.afterExecutionState_depth
    {P : CircularPresentation}
    {family : ExecutedCauchyFamily P}
    {precision : Nat}
    (source : family.ProducedSourceAt precision) :
    source.afterExecutionState.journal.depth = source.journal.depth + 6 :=
  ExecutedApproximation.completedJournal_depth source.journal
    (sourcePayload source.source.index source.source.readoutPrecision
      (ExecutedCauchyFamily.sourceCode source.source))

/--
Execute the grouped output as the next response after the owned source
execution.  Thus the future state consumes the actual output of the grouping
action rather than rebuilding the limit code independently.
-/
def groupedFutureState
    {P : CircularPresentation}
    (family : ExecutedCauchyFamily P)
    (precision : Nat)
    (source : family.ProducedSourceAt precision) :
    ResponseContinuation.RichState P :=
  ResponseContinuation.sourceNext P source.afterExecutionState
    (limitPayload precision
      (effectiveLimitGroupedCode family precision source))

/-- The grouped future memory is exactly the output consumed by its response. -/
theorem groupedFutureState_memory_exact
    {P : CircularPresentation}
    (family : ExecutedCauchyFamily P)
    (precision : Nat)
    (source : family.ProducedSourceAt precision) :
    (groupedFutureState family precision source).memory =
      effectiveLimitGroupedCode family precision source :=
  rfl

/--
Two sources constituted at histories of equal depth have the same public
state after grouping: their occurrence-bearing journals remain distinct, but
the projection keeps the common depth and the common grouped output.
-/
theorem groupedSources_project_eq
    {P : CircularPresentation}
    (family : ExecutedCauchyFamily P)
    (precision : Nat)
    (first second : family.ProducedSourceAt precision)
    (sameStartDepth : first.journal.depth = second.journal.depth) :
    (ResponseContinuation.bridge P).project
        (groupedFutureState family precision first) =
      (ResponseContinuation.bridge P).project
        (groupedFutureState family precision second) := by
  apply ResponseContinuation.ReducedState.equal
  · calc
      (groupedFutureState family precision first).journal.depth =
          first.afterExecutionState.journal.depth + 6 :=
        ExecutedApproximation.completedJournal_depth
          first.afterExecutionState.journal
          (limitPayload precision
            (effectiveLimitGroupedCode family precision first))
      _ = (first.journal.depth + 6) + 6 := by
        rw [ExecutedCauchyFamily.ProducedSourceAt.afterExecutionState_depth]
      _ = (second.journal.depth + 6) + 6 := by rw [sameStartDepth]
      _ = second.afterExecutionState.journal.depth + 6 := by
        rw [ExecutedCauchyFamily.ProducedSourceAt.afterExecutionState_depth]
      _ = (groupedFutureState family precision second).journal.depth :=
        (ExecutedApproximation.completedJournal_depth
          second.afterExecutionState.journal
          (limitPayload precision
            (effectiveLimitGroupedCode family precision second))).symm
  · exact
      (effectiveLimitGroupedCode_exact family precision first).trans
        (effectiveLimitGroupedCode_exact family precision second).symm

/--
The local grouping equality is therefore sufficient for every finite public
future: equal-depth grouped sources have identical normalized runs, events and
readouts for all later request lists.
-/
def groupedSourcesSameNormalizedFuture
    {P : CircularPresentation}
    (family : ExecutedCauchyFamily P)
    (precision : Nat)
    (first second : family.ProducedSourceAt precision)
    (sameStartDepth : first.journal.depth = second.journal.depth) :
    ResponseContinuation.SameNormalizedFuture P
      (groupedFutureState family precision first)
      (groupedFutureState family precision second) :=
  ResponseContinuation.sameNormalizedFuture P
    (groupedSources_project_eq family precision first second sameStartDepth)

/--
The readout of the executed limit response is the exact output of the grouping
action, not an independently reconstructed code.
-/
theorem effectiveLimitReadout_is_groupedCode
    {P : CircularPresentation}
    (family : ExecutedCauchyFamily P)
    (journal : OperationJournal ApproximationPayload)
    (precision : Nat)
    (source : family.ProducedSourceAt precision) :
    ((effectiveSequentialCompleteness family).convergence.executeLimit
      journal precision).readout =
        effectiveLimitGroupedCode family precision source := by
  exact (effectiveLimitGroupedCode_exact family precision source).symm

/--
The local grouping action consumes the convergence witness and preserves the
source charge at the common target.
-/
theorem effectiveLimit_groupedSourceAccepted
    {P : CircularPresentation}
    (family : ExecutedCauchyFamily P)
    (precision : Nat)
    (source : family.ProducedSourceAt precision) :
    (LocalGrouping.acceptanceAction (family.groupingEnvelope precision)).Accept
      LocalGrouping.State.target
      (effectiveLimitGroupedCharge family precision source) :=
  LocalGrouping.groupedSourceAccepted
    (family.groupingEnvelope precision) source

end RelationalPerimeter.Constitution.Reals

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Constitution.Reals.RelationalReal
#print axioms RelationalPerimeter.Constitution.Reals.RelationalReal.executedReadout
#print axioms RelationalPerimeter.Constitution.Reals.RelationalReal.executedReadout_exact
#print axioms RelationalPerimeter.Constitution.Reals.RelationalReal.constant
#print axioms RelationalPerimeter.Constitution.Reals.ExecutedCauchyFamily
#print axioms RelationalPerimeter.Constitution.Reals.ExecutedCauchyFamily.executeSource
#print axioms RelationalPerimeter.Constitution.Reals.ExecutedCauchyFamily.limitApproximation
#print axioms RelationalPerimeter.Constitution.Reals.ExecutedCauchyFamily.limit
#print axioms RelationalPerimeter.Constitution.Reals.ExecutedCauchyFamily.SourceAt
#print axioms RelationalPerimeter.Constitution.Reals.ExecutedCauchyFamily.sourceCode
#print axioms RelationalPerimeter.Constitution.Reals.ExecutedCauchyFamily.sourceNearLimit
#print axioms RelationalPerimeter.Constitution.Reals.ExecutedCauchyFamily.ProducedSourceAt
#print axioms RelationalPerimeter.Constitution.Reals.ExecutedCauchyFamily.produceSourceAt
#print axioms RelationalPerimeter.Constitution.Reals.ExecutedCauchyFamily.ProducedSourceAt.code
#print axioms RelationalPerimeter.Constitution.Reals.ExecutedCauchyFamily.ProducedSourceAt.code_exact
#print axioms RelationalPerimeter.Constitution.Reals.ExecutedCauchyFamily.ProducedSourceAt.nearLimit
#print axioms RelationalPerimeter.Constitution.Reals.ExecutedCauchyFamily.groupingEnvelope
#print axioms RelationalPerimeter.Constitution.Reals.ExecutedCauchyFamily.groupingFutureContract
#print axioms RelationalPerimeter.Constitution.Reals.ExecutedCauchyFamily.Request
#print axioms RelationalPerimeter.Constitution.Reals.ExecutedCauchyFamily.Request.payload
#print axioms RelationalPerimeter.Constitution.Reals.ExecutedCauchyFamily.requestPayloads
#print axioms RelationalPerimeter.Constitution.Reals.ExecutedConvergence
#print axioms RelationalPerimeter.Constitution.Reals.ExecutedConvergence.sourceReadout_exact
#print axioms RelationalPerimeter.Constitution.Reals.ExecutedConvergence.limitReadout_exact
#print axioms RelationalPerimeter.Constitution.Reals.SequentialCompletenessResult
#print axioms RelationalPerimeter.Constitution.Reals.effectiveSequentialCompleteness
#print axioms RelationalPerimeter.Constitution.Reals.limitRequestAdmitted
#print axioms RelationalPerimeter.Constitution.Reals.effectiveLimitGroupedCharge
#print axioms RelationalPerimeter.Constitution.Reals.effectiveLimitGroupedCode
#print axioms RelationalPerimeter.Constitution.Reals.effectiveLimitGroupedCode_exact
#print axioms RelationalPerimeter.Constitution.Reals.effectiveLimitGroupedCharge_consumesSourceCode
#print axioms RelationalPerimeter.Constitution.Reals.effectiveLimitGroupedCharge_consumesNear
#print axioms RelationalPerimeter.Constitution.Reals.ExecutedCauchyFamily.ProducedSourceAt.afterExecutionState
#print axioms RelationalPerimeter.Constitution.Reals.ExecutedCauchyFamily.ProducedSourceAt.afterExecutionState_depth
#print axioms RelationalPerimeter.Constitution.Reals.groupedFutureState
#print axioms RelationalPerimeter.Constitution.Reals.groupedFutureState_memory_exact
#print axioms RelationalPerimeter.Constitution.Reals.groupedSources_project_eq
#print axioms RelationalPerimeter.Constitution.Reals.groupedSourcesSameNormalizedFuture
#print axioms RelationalPerimeter.Constitution.Reals.effectiveLimitReadout_is_groupedCode
#print axioms RelationalPerimeter.Constitution.Reals.effectiveLimit_groupedSourceAccepted
/- AXIOM_AUDIT_END -/
