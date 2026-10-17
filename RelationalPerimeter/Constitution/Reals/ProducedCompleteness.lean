import RelationalPerimeter.Constitution.Reals.ConstitutiveRuntime
import RelationalPerimeter.Constitution.Reals.HistoricalGrouping

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Producer-first sequential completeness

This module reverses the former approximation-first construction.  Requests
contain indices only.  A source program computes a code during search, carries
that exact resource through action and continuation, stores it, and exposes it
only through the memory readout.  A limit request first executes a diagonal
source and then executes a grouping program whose action consumes that source;
the limit code is definitionally the action output, never an input target.

Finite grouping is indexed by an executed chronological source chain.  Its
batch action consumes that dependent chain constructor by constructor and
exposes only a unary chronological shape, then groups it around the target
produced by an executed limit action.
-/

namespace RelationalPerimeter.Constitution.Reals.ProducedCompleteness

open StrongPerimetralTurning
open ConstitutiveRuntime

universe uResource

/-! ## Source requests and their executable program -/

/-- A source request carries indices and precision, never a result code. -/
structure SourceRequest where
  term : Nat
  precision : Nat
deriving DecidableEq

/-- The received source context supplies an executable code producer. -/
structure SourceProducer where
  calculate : SourceRequest -> SignedDyadicCode

/-- The received context carries the exact producer used by source search. -/
structure SourceContext (producer : SourceProducer) (_request : SourceRequest) where
  private mk ::
  receivedProducer : SourceProducer
  producerExact : receivedProducer = producer

/-- Search computes the code from the producer and retains its exact origin. -/
structure SourceSearch (producer : SourceProducer) (request : SourceRequest) where
  private mk ::
  code : SignedDyadicCode
  codeExact : code = producer.calculate request

/-- Action consumes the exact search resource. -/
structure SourceAction
    (producer : SourceProducer)
    (request : SourceRequest)
    (searched : SourceSearch producer request) where
  private mk ::
  search : SourceSearch producer request
  searchExact : search = searched

structure SourceAccepted
    (producer : SourceProducer)
    (request : SourceRequest)
    (searched : SourceSearch producer request)
    (acted : SourceAction producer request searched) where
  private mk ::
  token : Unit

structure SourceAuthorization
    (producer : SourceProducer)
    (request : SourceRequest)
    (searched : SourceSearch producer request)
    (acted : SourceAction producer request searched)
    (accepted : SourceAccepted producer request searched acted) where
  private mk ::
  token : Unit

structure SourceDecomposition
    (producer : SourceProducer)
    (request : SourceRequest)
    (searched : SourceSearch producer request)
    (acted : SourceAction producer request searched)
    (accepted : SourceAccepted producer request searched acted)
    (authorized : SourceAuthorization producer request searched acted accepted) where
  private mk ::
  token : Unit

structure SourceContinuation
    (producer : SourceProducer)
    (request : SourceRequest)
    (searched : SourceSearch producer request)
    (acted : SourceAction producer request searched)
    (accepted : SourceAccepted producer request searched acted)
    (authorized : SourceAuthorization producer request searched acted accepted)
    (decomposed :
      SourceDecomposition producer request searched acted accepted authorized) where
  private mk ::
  token : Unit

/-- Memory stores the action itself, rather than a reconstructed code. -/
structure SourceStored
    (producer : SourceProducer)
    (request : SourceRequest)
    (searched : SourceSearch producer request)
    (acted : SourceAction producer request searched) where
  private mk ::
  action : SourceAction producer request searched
  actionExact : action = acted

/-- The executable six-phase source program. -/
def sourceProgram (producer : SourceProducer) : Program SourceRequest where
  ReceivedContext := SourceContext producer
  SearchResult := SourceSearch producer
  ActionResult := SourceAction producer
  Accepted := SourceAccepted producer
  Authorization := SourceAuthorization producer
  Decomposition := SourceDecomposition producer
  Continuation := SourceContinuation producer
  Stored := SourceStored producer
  stamp := fun request => .source request.term request.precision
  receive := fun _request =>
    { receivedProducer := producer, producerExact := rfl }
  search := fun request context =>
    { code := context.receivedProducer.calculate request
      codeExact := by rw [context.producerExact] }
  act := fun _request searched =>
    { search := searched, searchExact := rfl }
  preserves := fun _request _searched _acted => { token := () }
  authorize := fun _request _searched _acted _accepted => { token := () }
  decompose := fun _request _searched _acted _accepted _authorized =>
    { token := () }
  resume := fun _request _searched _acted _accepted _authorized _decomposed =>
    { token := () }
  store := fun _request _searched acted _accepted _authorized _decomposed
      _continued =>
    { action := acted, actionExact := rfl }
  actionCode := fun acted => acted.search.code
  read := fun stored => stored.action.search.code
  readStoredExact := fun stored => by rw [stored.actionExact]

theorem sourceProgram_actionCode_exact
    (producer : SourceProducer)
    (request : SourceRequest)
    (searched : (sourceProgram producer).SearchResult request)
    (acted : (sourceProgram producer).ActionResult request searched) :
    (sourceProgram producer).actionCode acted = producer.calculate request := by
  change acted.search.code = producer.calculate request
  exact acted.search.codeExact

/-! ## Executed Cauchy families -/

/--
The Cauchy law consumes two actual source executions and compares their memory
readouts.  It cannot be discharged by codes stored independently in requests.
-/
structure ExecutedCauchyFamily
    (P : CircularPresentation)
    (baseDepth : Nat) where
  producer : SourceProducer
  termCoherent :
    (term coarse leftPrecision rightPrecision : Nat) ->
    PrecisionExtension coarse leftPrecision ->
    PrecisionExtension coarse rightPrecision ->
      Near coarse
        (producer.calculate { term := term, precision := leftPrecision })
        (producer.calculate { term := term, precision := rightPrecision })
  modulus : Nat -> Nat
  modulusMonotone : {coarse fine : Nat} ->
    PrecisionExtension coarse fine ->
      PrecisionExtension (modulus coarse) (modulus fine)
  cauchy :
    (precision : Nat) ->
    {firstJournal secondJournal : Journal P baseDepth} ->
    (firstRequest secondRequest : SourceRequest) ->
    PrecisionExtension (modulus precision) firstRequest.term ->
    PrecisionExtension (modulus precision) secondRequest.term ->
    PrecisionExtension precision firstRequest.precision ->
    PrecisionExtension precision secondRequest.precision ->
    (first : ExecutedRequest (sourceProgram producer) P
      firstJournal firstRequest) ->
    (second : ExecutedRequest (sourceProgram producer) P
      secondJournal secondRequest) ->
      Near precision first.readout second.readout

namespace ExecutedCauchyFamily

variable {P : CircularPresentation} {baseDepth : Nat}
variable (family : ExecutedCauchyFamily P baseDepth)

/-- A source certificate at a requested external precision. -/
structure SourceAt (precision : Nat) where
  request : SourceRequest
  indexBeyondModulus :
    PrecisionExtension (family.modulus precision) request.term
  readoutRefines : PrecisionExtension precision request.precision

/-- The canonical diagonal source used to produce the limit at a precision. -/
def diagonalSourceAt (precision : Nat) : family.SourceAt precision where
  request := { term := family.modulus precision, precision := precision }
  indexBeyondModulus := PrecisionExtension.refl _
  readoutRefines := PrecisionExtension.refl _

/-- A source resource executed at one exact journal. -/
structure ProducedSourceAt
    {precision : Nat}
    (journal : Journal P baseDepth)
    (source : family.SourceAt precision) where
  execution : ExecutedRequest (sourceProgram family.producer) P
    journal source.request

/-- Execute a certified source from the supplied exact journal. -/
def produceSourceAt
    {precision : Nat}
    (journal : Journal P baseDepth)
    (source : family.SourceAt precision) :
    family.ProducedSourceAt journal source :=
  { execution := execute (sourceProgram family.producer) P journal source.request }

namespace ProducedSourceAt

def completedJournal
    {family : ExecutedCauchyFamily P baseDepth}
    {precision : Nat}
    {journal : Journal P baseDepth}
    {source : family.SourceAt precision}
    (produced : family.ProducedSourceAt journal source) :
    Journal P baseDepth :=
  produced.execution.completedJournal

def readout
    {family : ExecutedCauchyFamily P baseDepth}
    {precision : Nat}
    {journal : Journal P baseDepth}
    {source : family.SourceAt precision}
    (produced : family.ProducedSourceAt journal source) : SignedDyadicCode :=
  produced.execution.readout

theorem readout_is_storedAction
    {family : ExecutedCauchyFamily P baseDepth}
    {precision : Nat}
    {journal : Journal P baseDepth}
    {source : family.SourceAt precision}
    (produced : family.ProducedSourceAt journal source) :
    produced.readout =
      (sourceProgram family.producer).actionCode produced.execution.action :=
  produced.execution.readout_is_storedAction

theorem readout_is_calculated
    {family : ExecutedCauchyFamily P baseDepth}
    {precision : Nat}
    {journal : Journal P baseDepth}
    {source : family.SourceAt precision}
    (produced : family.ProducedSourceAt journal source) :
    produced.readout = family.producer.calculate source.request := by
  rw [produced.readout_is_storedAction]
  exact sourceProgram_actionCode_exact family.producer source.request
    produced.execution.memory.continued.authorized.acted.searched.result
    produced.execution.action

/-- Every individual family term remains coherent at arbitrary refinements. -/
def sameTermExecutedNear
    {family : ExecutedCauchyFamily P baseDepth}
    {leftJournal rightJournal : Journal P baseDepth}
    (term coarse leftPrecision rightPrecision : Nat)
    (leftBeyond : PrecisionExtension coarse leftPrecision)
    (rightBeyond : PrecisionExtension coarse rightPrecision)
    (left : ExecutedRequest (sourceProgram family.producer) P leftJournal
      { term := term, precision := leftPrecision })
    (right : ExecutedRequest (sourceProgram family.producer) P rightJournal
      { term := term, precision := rightPrecision }) :
    Near coarse left.readout right.readout := by
  have leftExact : left.readout =
      family.producer.calculate { term := term, precision := leftPrecision } := by
    rw [left.readout_is_storedAction]
    exact sourceProgram_actionCode_exact family.producer _
      left.memory.continued.authorized.acted.searched.result left.action
  have rightExact : right.readout =
      family.producer.calculate { term := term, precision := rightPrecision } := by
    rw [right.readout_is_storedAction]
    exact sourceProgram_actionCode_exact family.producer _
      right.memory.continued.authorized.acted.searched.result right.action
  rw [leftExact, rightExact]
  exact family.termCoherent term coarse leftPrecision rightPrecision
    leftBeyond rightBeyond

theorem completedDepth
    {family : ExecutedCauchyFamily P baseDepth}
    {precision : Nat}
    {journal : Journal P baseDepth}
    {source : family.SourceAt precision}
    (produced : family.ProducedSourceAt journal source) :
    produced.completedJournal.absoluteDepth = journal.absoluteDepth + 6 :=
  produced.execution.completed_absoluteDepth

end ProducedSourceAt


/-- A coherent real term executed by the same source program and shared journal. -/
structure TermModel (term : Nat) where
  respond : (journal : Journal P baseDepth) -> (precision : Nat) ->
    ExecutedRequest (sourceProgram family.producer) P journal
      { term := term, precision := precision }
  canonical : (journal : Journal P baseDepth) -> (precision : Nat) ->
    respond journal precision =
      execute (sourceProgram family.producer) P journal
        { term := term, precision := precision }
  coherent :
    {leftJournal rightJournal : Journal P baseDepth} ->
    (coarse leftPrecision rightPrecision : Nat) ->
    PrecisionExtension coarse leftPrecision -> PrecisionExtension coarse rightPrecision ->
    (left : ExecutedRequest (sourceProgram family.producer) P leftJournal
      { term := term, precision := leftPrecision }) ->
    (right : ExecutedRequest (sourceProgram family.producer) P rightJournal
      { term := term, precision := rightPrecision }) ->
      Near coarse left.readout right.readout

def termModel (term : Nat) : family.TermModel term where
  respond := fun journal precision =>
    execute (sourceProgram family.producer) P journal { term := term, precision := precision }
  canonical := fun _journal _precision => rfl
  coherent := fun coarse leftPrecision rightPrecision leftBeyond rightBeyond left right =>
    ProducedSourceAt.sameTermExecutedNear term coarse leftPrecision rightPrecision
      leftBeyond rightBeyond left right


end ExecutedCauchyFamily

/-! ## Limit grouping consumes an executed source -/

namespace LimitGrouping

variable {P : CircularPresentation} {baseDepth : Nat}
variable {family : ExecutedCauchyFamily P baseDepth}
variable {precision : Nat}
variable {journal : Journal P baseDepth}
variable {source : family.SourceAt precision}

/-- Context reception retains the exact source package to be grouped. -/
structure Context
    (produced : family.ProducedSourceAt journal source)
    (_request : Unit) where
  private mk ::
  retained : family.ProducedSourceAt journal source
  retainedExact : retained = produced

structure Search
    (produced : family.ProducedSourceAt journal source)
    (_request : Unit) where
  private mk ::
  retained : family.ProducedSourceAt journal source
  retainedExact : retained = produced


/-- Cauchy data on the exact owned execution, not a reflexive Near constructor. -/
def receivedNear
    (produced : family.ProducedSourceAt journal source) :
    Near precision produced.readout produced.readout :=
  family.cauchy precision source.request source.request
    source.indexBeyondModulus source.indexBeyondModulus
    source.readoutRefines source.readoutRefines
    produced.execution produced.execution

def specification (produced : family.ProducedSourceAt journal source) :
    LocalGrouping.Specification where
  Source := Unit
  precision := precision
  sourceCode := fun _ => produced.readout
  targetCode := produced.readout
  sourceNearTarget := fun _ => receivedNear produced

/-- The local normalizer executes its rank/choices/decrease rules. -/
def normalizationTrace (produced : family.ProducedSourceAt journal source) :
    ConstitutiveSearch.Grouping.Trace
      (LocalGrouping.Step (specification produced))
      (.source ()) .target := by
  rw [← LocalGrouping.normal_source (specification produced) ()]
  exact ((LocalGrouping.rules (specification produced)).normalize (.source ())).trace

def normalizedCharge (produced : family.ProducedSourceAt journal source) :
    LocalGrouping.GroupedCharge precision produced.readout :=
  (LocalGrouping.acceptanceAction (specification produced)).transport
    (normalizationTrace produced)
    (LocalGrouping.sourceCharge (specification produced) ())

/-- Coherence identifies the executed normalizer with the canonical local trace. -/
theorem normalizedCharge_exact (produced : family.ProducedSourceAt journal source) :
    normalizedCharge produced =
      (LocalGrouping.acceptanceAction (specification produced)).transport
        (ConstitutiveSearch.Grouping.Trace.one
          (LocalGrouping.Step.group (specification := specification produced) ()))
        (LocalGrouping.sourceCharge (specification produced) ()) :=
  LocalGrouping.action_coherent (specification produced)
    (normalizationTrace produced)
    (ConstitutiveSearch.Grouping.Trace.one
      (LocalGrouping.Step.group (specification := specification produced) ())) _

theorem normalizedCharge_code (produced : family.ProducedSourceAt journal source) :
    (normalizedCharge produced).outputCode = produced.readout := by
  rw [normalizedCharge_exact]
  rfl


/--
Target resource produced by the grouping action.  Its numerical code may
represent the same dyadic value as the source, but the target is a distinct
proof-relevant resource owned by the later action phase.
-/
structure ProducedTarget
    (produced : family.ProducedSourceAt journal source) where
  private mk ::
  normalized : LocalGrouping.GroupedCharge precision produced.readout
  normalizedExact : normalized = normalizedCharge produced
  code : SignedDyadicCode
  codeIsNormalized : code = normalized.outputCode
  codeExact : code = produced.readout
  sourceNearTarget : Near precision produced.readout code

/--
The grouping action consumes the searched source and its positive proximity to
the target it produces.  Its code is a projection of that consumed source.
-/
structure Action (produced : family.ProducedSourceAt journal source) (_request : Unit)
    (searched : Search produced ()) where
  private mk ::
  search : Search produced ()
  searchExact : search = searched
  target : ProducedTarget search.retained
  consumedNearProduced :
    Near precision search.retained.readout target.code
  consumedNearExact : consumedNearProduced = target.sourceNearTarget

def Action.code
    {produced : family.ProducedSourceAt journal source}
    {searched : Search produced ()}
    (acted : Action produced () searched) : SignedDyadicCode :=
  acted.target.code

structure Accepted (produced : family.ProducedSourceAt journal source) (_request : Unit)
    (searched : Search produced ()) (acted : Action produced () searched) where
  private mk ::
  preservation : Near precision acted.search.retained.readout acted.target.code
  preservationExact : preservation = acted.consumedNearProduced

structure Authorization (produced : family.ProducedSourceAt journal source) (_request : Unit)
    (searched : Search produced ()) (acted : Action produced () searched)
    (accepted : Accepted produced () searched acted) where
  private mk ::
  token : Unit

structure Decomposition (produced : family.ProducedSourceAt journal source) (_request : Unit)
    (searched : Search produced ()) (acted : Action produced () searched)
    (accepted : Accepted produced () searched acted)
    (authorized : Authorization produced () searched acted accepted) where
  private mk ::
  source : family.ProducedSourceAt journal source
  sourceExact : source = acted.search.retained
  target : ProducedTarget source
  targetExact : target.code = acted.target.code

structure Continuation (produced : family.ProducedSourceAt journal source) (_request : Unit)
    (searched : Search produced ()) (acted : Action produced () searched)
    (accepted : Accepted produced () searched acted)
    (authorized : Authorization produced () searched acted accepted)
    (decomposed : Decomposition produced () searched acted accepted authorized) where
  private mk ::
  source : family.ProducedSourceAt journal source
  sourceExact : source = decomposed.source
  target : ProducedTarget source
  targetCodeExact : target.code = decomposed.target.code

structure Stored (produced : family.ProducedSourceAt journal source) (_request : Unit)
    (searched : Search produced ()) (acted : Action produced () searched) where
  private mk ::
  action : Action produced () searched
  actionExact : action = acted

def program (produced : family.ProducedSourceAt journal source) : Program Unit where
  ReceivedContext := Context produced
  SearchResult := Search produced
  ActionResult := Action produced
  Accepted := Accepted produced
  Authorization := Authorization produced
  Decomposition := Decomposition produced
  Continuation := Continuation produced
  Stored := Stored produced
  stamp := fun _request => .limit precision
  receive := fun _request => { retained := produced, retainedExact := rfl }
  search := fun _request context =>
    { retained := context.retained, retainedExact := context.retainedExact }
  act := fun _request searched =>
    let target : ProducedTarget searched.retained :=
      { normalized := normalizedCharge searched.retained
        normalizedExact := rfl
        code := (normalizedCharge searched.retained).outputCode
        codeIsNormalized := rfl
        codeExact := normalizedCharge_code searched.retained
        sourceNearTarget := by
          rw [normalizedCharge_code]
          exact receivedNear searched.retained }
    { search := searched
      searchExact := rfl
      target := target
      consumedNearProduced := target.sourceNearTarget
      consumedNearExact := rfl }
  preserves := fun _request _searched acted =>
    { preservation := acted.consumedNearProduced
      preservationExact := rfl }
  authorize := fun _request _searched _acted _accepted => { token := () }
  decompose := fun _request _searched acted _accepted _authorized =>
    { source := acted.search.retained
      sourceExact := rfl
      target := acted.target
      targetExact := rfl }
  resume := fun _request _searched _acted _accepted _authorized decomposed =>
    { source := decomposed.source
      sourceExact := rfl
      target := decomposed.target
      targetCodeExact := rfl }
  store := fun _request _searched acted _accepted _authorized _decomposed
      _continued =>
    { action := acted, actionExact := rfl }
  actionCode := Action.code
  read := fun stored => stored.action.code
  readStoredExact := fun stored => by rw [stored.actionExact]

theorem program_actionCode_exact
    (produced : family.ProducedSourceAt journal source)
    (searched : (program produced).SearchResult ())
    (acted : (program produced).ActionResult () searched) :
    (program produced).actionCode acted = produced.readout := by
  change acted.target.code = produced.readout
  rw [acted.target.codeExact, acted.search.retainedExact]

end LimitGrouping

/-- Complete source--grouping--memory production at one precision. -/
structure ExecutedLimitProduction
    {P : CircularPresentation}
    {baseDepth : Nat}
    (family : ExecutedCauchyFamily P baseDepth)
    (journal : Journal P baseDepth)
    (precision : Nat) where
  private mk ::
  sourceAt : family.SourceAt precision
  sourceAtExact : sourceAt = family.diagonalSourceAt precision
  source : family.ProducedSourceAt journal sourceAt
  execution : ExecutedRequest (LimitGrouping.program source) P
    source.completedJournal ()

/-- Execute the diagonal source, then consume it in the limit grouping action. -/
def executeLimitProduction
    {P : CircularPresentation}
    {baseDepth : Nat}
    (family : ExecutedCauchyFamily P baseDepth)
    (journal : Journal P baseDepth)
    (precision : Nat) :
    ExecutedLimitProduction family journal precision := by
  let sourceAt := family.diagonalSourceAt precision
  let source := family.produceSourceAt journal sourceAt
  exact
  { sourceAt := sourceAt
    sourceAtExact := rfl
    source := source
    execution := execute (LimitGrouping.program source) P
      source.completedJournal () }

namespace ExecutedLimitProduction

variable {P : CircularPresentation} {baseDepth : Nat}
variable {family : ExecutedCauchyFamily P baseDepth}
variable {journal : Journal P baseDepth}
variable {precision : Nat}

def completedJournal
    (produced : ExecutedLimitProduction family journal precision) :
    Journal P baseDepth :=
  produced.execution.completedJournal

/-- The limit readout is the memory projection of the grouping action. -/
def readout
    (produced : ExecutedLimitProduction family journal precision) :
    SignedDyadicCode :=
  produced.execution.readout

theorem readout_is_groupingAction
    (produced : ExecutedLimitProduction family journal precision) :
    produced.readout =
      (LimitGrouping.program produced.source).actionCode
        produced.execution.action :=
  produced.execution.readout_is_storedAction

/-- Code owned by the target resource produced inside the grouping action. -/
def targetCode
    (produced : ExecutedLimitProduction family journal precision) :
    SignedDyadicCode :=
  produced.execution.action.target.code

theorem readout_is_targetCode
    (produced : ExecutedLimitProduction family journal precision) :
    produced.readout = produced.targetCode := by
  exact produced.readout_is_groupingAction

/--
The positive source--target witness is the one retained by the executed action;
it is not reconstructed from the final readout.
-/
def sourceNearTarget
    (produced : ExecutedLimitProduction family journal precision) :
    Near precision produced.source.readout produced.targetCode := by
  rw [← produced.execution.action.search.retainedExact]
  exact produced.execution.action.consumedNearProduced

def sourceNearReadout
    (produced : ExecutedLimitProduction family journal precision) :
    Near precision produced.source.readout produced.readout := by
  rw [produced.readout_is_targetCode]
  exact produced.sourceNearTarget

/-- The action output is exactly the readout of the source it consumed. -/
theorem readout_is_source
    (produced : ExecutedLimitProduction family journal precision) :
    produced.readout = produced.source.readout := by
  rw [produced.readout_is_groupingAction]
  exact LimitGrouping.program_actionCode_exact produced.source
    produced.execution.memory.continued.authorized.acted.searched.result
    produced.execution.action

theorem sourceCompletedDepth
    (produced : ExecutedLimitProduction family journal precision) :
    produced.source.completedJournal.absoluteDepth =
      journal.absoluteDepth + 6 :=
  produced.source.completedDepth

/-- A limit production executes one six-phase source and one six-phase grouping. -/
theorem completedDepth
    (produced : ExecutedLimitProduction family journal precision) :
    produced.completedJournal.absoluteDepth = journal.absoluteDepth + 12 := by
  calc
    produced.completedJournal.absoluteDepth =
        produced.source.completedJournal.absoluteDepth + 6 :=
      produced.execution.completed_absoluteDepth
    _ = (journal.absoluteDepth + 6) + 6 := by
      rw [produced.sourceCompletedDepth]
    _ = journal.absoluteDepth + 12 := rfl

end ExecutedLimitProduction

/-! ## Chronological finite grouping with exact structural consumption -/

/--
This unary enumeration records only the chronological shape indexed by the
exact chain length.  Exhaustive, non-duplicating source consumption is carried
separately by `ExactConsumption`, whose constructors mirror the source chain.
-/
inductive ExactIndexEnumeration : Nat -> Type
  | empty : ExactIndexEnumeration 0
  | snoc {size : Nat} :
      ExactIndexEnumeration size -> ExactIndexEnumeration (Nat.succ size)

/-- Canonical exhaustive chronological enumeration. -/
def allIndices : (size : Nat) -> ExactIndexEnumeration size
  | 0 => .empty
  | Nat.succ size => .snoc (allIndices size)

/-- Executable count readout of the dependent enumeration. -/
def ExactIndexEnumeration.count :
    {size : Nat} -> ExactIndexEnumeration size -> Nat
  | size, _enumeration => size

theorem allIndices_length (size : Nat) : (allIndices size).count = size := by
  rfl

theorem ExactIndexEnumeration.unique
    {size : Nat}
    (enumeration : ExactIndexEnumeration size) :
    enumeration = allIndices size := by
  induction enumeration with
  | empty => rfl
  | snoc prior inductionHypothesis =>
      exact congrArg ExactIndexEnumeration.snoc inductionHypothesis

namespace ExecutedCauchyFamily

variable {P : CircularPresentation} {baseDepth : Nat}
variable (family : ExecutedCauchyFamily P baseDepth)


/-- An executed diagonal SOURCE, never an already produced grouping target. -/
structure DiagonalAnchor
    (family : ExecutedCauchyFamily P baseDepth)
    (journal : Journal P baseDepth) (precision : Nat) where
  private mk ::
  source : family.ProducedSourceAt journal (family.diagonalSourceAt precision)

def executeAnchor (family : ExecutedCauchyFamily P baseDepth)
    (journal : Journal P baseDepth) (precision : Nat) :
    DiagonalAnchor family journal precision :=
  { source := family.produceSourceAt journal (family.diagonalSourceAt precision) }

namespace DiagonalAnchor
variable {family : ExecutedCauchyFamily P baseDepth}
variable {journal : Journal P baseDepth} {precision : Nat}
def sourceAt (_anchor : DiagonalAnchor family journal precision) :
    family.SourceAt precision := family.diagonalSourceAt precision
theorem sourceAtExact (anchor : DiagonalAnchor family journal precision) :
    anchor.sourceAt = family.diagonalSourceAt precision := rfl
def readout (anchor : DiagonalAnchor family journal precision) : SignedDyadicCode :=
  anchor.source.readout
def completedJournal (anchor : DiagonalAnchor family journal precision) :
    Journal P baseDepth := anchor.source.completedJournal
end DiagonalAnchor

/-- Compatibility only: forget the target and retain its already owned source. -/
def ExecutedLimitProduction.toAnchor
    {family : ExecutedCauchyFamily P baseDepth}
    {journal : Journal P baseDepth} {precision : Nat}
    (produced : ExecutedLimitProduction family journal precision) :
    DiagonalAnchor family journal precision where
  source := by
    rw [← produced.sourceAtExact]
    exact produced.source

instance limitToSourceAnchor
    {family : ExecutedCauchyFamily P baseDepth}
    {journal : Journal P baseDepth} {precision : Nat} :
    Coe (ExecutedLimitProduction family journal precision)
      (DiagonalAnchor family journal precision) :=
  ⟨ExecutedLimitProduction.toAnchor⟩


/-- One existentially journal-indexed produced source. -/
structure SourceRecord (precision : Nat) where
  journal : Journal P baseDepth
  sourceAt : family.SourceAt precision
  produced : family.ProducedSourceAt journal sourceAt

/-- A chronological chain; each next source starts at the prior completed journal. -/
inductive ExecutedSourceChain (precision : Nat) :
    Journal P baseDepth -> Journal P baseDepth ->
      Nat -> Type _
  | empty (journal : Journal P baseDepth) :
      ExecutedSourceChain precision journal journal 0
  | snoc
      {start current : Journal P baseDepth}
      {size : Nat}
      (prior : ExecutedSourceChain precision start current size)
      (sourceAt : family.SourceAt precision)
      (produced : family.ProducedSourceAt current sourceAt) :
      ExecutedSourceChain precision start produced.completedJournal
        (Nat.succ size)

namespace ExecutedSourceChain

def append
    {precision : Nat}
    {start current : Journal P baseDepth}
    {size : Nat}
    (chain : family.ExecutedSourceChain precision start current size)
    (sourceAt : family.SourceAt precision) :
    family.ExecutedSourceChain precision start
      (family.produceSourceAt current sourceAt).completedJournal
      (Nat.succ size) :=
  .snoc chain sourceAt (family.produceSourceAt current sourceAt)

/-- Number of constitutive phases executed by a chronological source chain. -/
def operationCount : Nat -> Nat
  | 0 => 0
  | Nat.succ size => operationCount size + 6

/--
Oldest-first view of the exact productions owned by the chain.  This is a
projection of the dependent constructors; it never re-executes a source.
-/
def records
    {precision : Nat} {start current : Journal P baseDepth} {size : Nat} :
    family.ExecutedSourceChain precision start current size ->
      List (family.SourceRecord precision)
  | .empty _ => []
  | .snoc prior sourceAt produced =>
      records prior ++
        [{ journal := _, sourceAt := sourceAt, produced := produced }]

/-- The terminal depth is the initial depth plus exactly six phases per source. -/
theorem finalDepth_exact
    {precision : Nat} {start current : Journal P baseDepth} {size : Nat}
    (chain : family.ExecutedSourceChain precision start current size) :
    current.absoluteDepth = start.absoluteDepth + operationCount size := by
  induction chain with
  | empty => rfl
  | snoc prior sourceAt produced inductionHypothesis =>
      rw [produced.completedDepth, inductionHypothesis]
      exact Nat.add_assoc start.absoluteDepth (operationCount _) 6

end ExecutedSourceChain


namespace ExecutedSourceChain

universe uList

theorem listAppendNil {A : Type uList} (values : List A) : values ++ [] = values := by
  induction values with
  | nil => rfl
  | cons first remaining ih => exact congrArg (List.cons first) ih

theorem listAppendAssoc {A : Type uList} (first second third : List A) :
    (first ++ second) ++ third = first ++ (second ++ third) := by
  induction first with
  | nil => rfl
  | cons head tail ih => exact congrArg (List.cons head) ih


/-- Concatenate exact chronological chains at their shared journal. -/
def concatenate
    {precision : Nat} {first middle last : Journal P baseDepth}
    {leftSize rightSize : Nat}
    (left : family.ExecutedSourceChain precision first middle leftSize) :
    family.ExecutedSourceChain precision middle last rightSize ->
      family.ExecutedSourceChain precision first last (leftSize + rightSize)
  | .empty _ => left
  | .snoc prior source produced => .snoc (concatenate left prior) source produced

theorem concatenate_records
    {precision : Nat} {first middle last : Journal P baseDepth}
    {leftSize rightSize : Nat}
    (left : family.ExecutedSourceChain precision first middle leftSize)
    (right : family.ExecutedSourceChain precision middle last rightSize) :
    (concatenate family left right).records = left.records ++ right.records := by
  induction right with
  | empty => exact (listAppendNil _).symm
  | snoc prior source produced ih =>
      change (concatenate family left prior).records ++ [_] =
        left.records ++ (prior.records ++ [_])
      rw [ih, listAppendAssoc]
end ExecutedSourceChain


/-- One exact journal-indexed source charge consumed by finite grouping. -/
structure ConsumedSource
    {precision : Nat}
    {targetJournal : Journal P baseDepth}
    (target : DiagonalAnchor family targetJournal precision)
    (record : family.SourceRecord precision) where
  nearTarget : Near precision record.produced.readout target.readout

/-- Consume one exact source record against an action-produced target. -/
def consumeSource
    {precision : Nat}
    {targetJournal : Journal P baseDepth}
    (target : DiagonalAnchor family targetJournal precision)
    (record : family.SourceRecord precision) :
    family.ConsumedSource target record := by
  exact
  { nearTarget := by
      exact family.cauchy precision
        record.sourceAt.request target.sourceAt.request
        record.sourceAt.indexBeyondModulus
        (by rw [target.sourceAtExact]; exact PrecisionExtension.refl _)
        record.sourceAt.readoutRefines
        (by rw [target.sourceAtExact]; exact PrecisionExtension.refl _)
        record.produced.execution target.source.execution }


/-- The source identity and the exact positive witness consumed from that identity. -/
structure ChargedRecord
    {precision : Nat} {targetJournal : Journal P baseDepth}
    (anchor : DiagonalAnchor family targetJournal precision) where
  record : family.SourceRecord precision
  charge : family.ConsumedSource anchor record


/-- Local finite-image specification derived from an executed source anchor. -/
def groupingSpecification
    {precision : Nat}
    {targetJournal : Journal P baseDepth}
    (target : DiagonalAnchor family targetJournal precision) :
    LocalGrouping.Specification where
  Source := family.ChargedRecord target
  precision := precision
  sourceCode := fun charged => charged.record.produced.readout
  targetCode := target.readout
  sourceNearTarget := fun charged => charged.charge.nearTarget

/--
Indexable oldest-first selection projected from the exact chronological chain.
Every selected identity contains the production already owned by that chain.
-/
def ExecutedSourceChain.selection
    {precision : Nat}
    {start current targetJournal : Journal P baseDepth}
    {size : Nat}
    (chain : family.ExecutedSourceChain precision start current size)
    (target : DiagonalAnchor family targetJournal precision) :
    HistoricalGrouping.FiniteSelection
      (family.groupingSpecification target) size :=
  match chain with
  | .empty _ => HistoricalGrouping.emptySelection _
  | .snoc prior sourceAt produced =>
      HistoricalGrouping.FiniteSelection.snoc (prior.selection target)
        { record := { journal := _, sourceAt := sourceAt, produced := produced }
          charge := family.consumeSource target
            { journal := _, sourceAt := sourceAt, produced := produced } }

/-
Exact exhaustive consumption mirrors the source chain constructor for
constructor.  The successor consumes the exact fresh production and retains an
exact recursive consumption of the exact prior chain.
-/
inductive ExactConsumption
    {precision : Nat}
    {targetJournal : Journal P baseDepth}
    (target : DiagonalAnchor family targetJournal precision) :
    {start current : Journal P baseDepth} -> {size : Nat} ->
    family.ExecutedSourceChain precision start current size -> Type _
  | empty (journal : Journal P baseDepth) :
      ExactConsumption target (.empty journal)
  | snoc
      {start current : Journal P baseDepth}
      {size : Nat}
      (prior : family.ExecutedSourceChain precision start current size)
      (sourceAt : family.SourceAt precision)
      (produced : family.ProducedSourceAt current sourceAt)
      (previous : ExactConsumption target prior)
      (fresh : family.ConsumedSource target
        { journal := current, sourceAt := sourceAt, produced := produced }) :
      ExactConsumption target (.snoc prior sourceAt produced)

def consumeAll
    {precision : Nat}
    {targetJournal : Journal P baseDepth}
    (target : DiagonalAnchor family targetJournal precision) :
    {start current : Journal P baseDepth} -> {size : Nat} ->
    (chain : family.ExecutedSourceChain precision start current size) ->
      family.ExactConsumption target chain
  | _, _, _, .empty journal => .empty journal
  | _, _, _, .snoc prior sourceAt produced =>
      .snoc prior sourceAt produced
        (consumeAll target prior)
        (family.consumeSource target
          { journal := _, sourceAt := sourceAt, produced := produced })

namespace ExactConsumption

/-- Oldest-first records projected from exact structural consumption. -/
def records
    {family : ExecutedCauchyFamily P baseDepth}
    {precision : Nat}
    {targetJournal : Journal P baseDepth}
    {target : DiagonalAnchor family targetJournal precision}
    {start current : Journal P baseDepth}
    {size : Nat}
    {chain : family.ExecutedSourceChain precision start current size} :
    family.ExactConsumption target chain ->
      List (family.SourceRecord precision)
  | .empty _ => []
  | .snoc _ sourceAt produced previous _ =>
      previous.records ++
        [{ journal := _, sourceAt := sourceAt, produced := produced }]

/-- Structural consumption and the chain expose the same exact productions. -/
theorem records_exact
    {family : ExecutedCauchyFamily P baseDepth}
    {precision : Nat}
    {targetJournal : Journal P baseDepth}
    {target : DiagonalAnchor family targetJournal precision}
    {start current : Journal P baseDepth}
    {size : Nat}
    {chain : family.ExecutedSourceChain precision start current size}
    (consumption : family.ExactConsumption target chain) :
    consumption.records = chain.records := by
  induction consumption with
  | empty => rfl
  | snoc prior sourceAt produced previous fresh inductionHypothesis =>
      rw [records, ExecutedSourceChain.records, inductionHypothesis]

/--
Historical indexing projected from the exact consumption itself.  Batch
normalization therefore consumes the same master resource as the structural
exhaustivity proof; no parallel selection is reconstructed from the chain.
-/
def indexedSelection
    {family : ExecutedCauchyFamily P baseDepth}
    {precision : Nat}
    {targetJournal : Journal P baseDepth}
    {target : DiagonalAnchor family targetJournal precision}
    {start current : Journal P baseDepth}
    {size : Nat}
    {chain : family.ExecutedSourceChain precision start current size} :
    family.ExactConsumption target chain ->
      HistoricalGrouping.FiniteSelection
        (family.groupingSpecification target) size
  | .empty _ => HistoricalGrouping.emptySelection _
  | .snoc _ sourceAt produced previous fresh =>
      HistoricalGrouping.FiniteSelection.snoc previous.indexedSelection
        { record := { journal := _, sourceAt := sourceAt, produced := produced }
          charge := fresh }

def indexing
    {family : ExecutedCauchyFamily P baseDepth}
    {precision : Nat}
    {targetJournal : Journal P baseDepth}
    {target : DiagonalAnchor family targetJournal precision}
    {start current : Journal P baseDepth}
    {size : Nat}
    {chain : family.ExecutedSourceChain precision start current size} :
    family.ExactConsumption target chain -> ExactIndexEnumeration size
  | .empty _ => .empty
  | .snoc _ _ _ previous _ => .snoc previous.indexing

def count
    {family : ExecutedCauchyFamily P baseDepth}
    {precision : Nat}
    {targetJournal : Journal P baseDepth}
    {target : DiagonalAnchor family targetJournal precision}
    {start current : Journal P baseDepth}
    {size : Nat}
    {chain : family.ExecutedSourceChain precision start current size}
    (consumption : family.ExactConsumption target chain) : Nat :=
  consumption.indexing.count

theorem count_exact
    {family : ExecutedCauchyFamily P baseDepth}
    {precision : Nat}
    {targetJournal : Journal P baseDepth}
    {target : DiagonalAnchor family targetJournal precision}
    {start current : Journal P baseDepth}
    {size : Nat}
    {chain : family.ExecutedSourceChain precision start current size}
    (consumption : family.ExactConsumption target chain) :
    consumption.count = size := by
  induction consumption with
  | empty => rfl
  | snoc prior sourceAt produced previous fresh inductionHypothesis =>
      exact congrArg Nat.succ inductionHypothesis

end ExactConsumption


/-- A transported historical payload, retaining its actual selection and charge. -/
structure HistoricalBatchResource
    {precision : Nat} {targetJournal : Journal P baseDepth}
    (anchor : DiagonalAnchor family targetJournal precision) where
  size : Nat
  selection : HistoricalGrouping.FiniteSelection (family.groupingSpecification anchor) size
  charge : HistoricalGrouping.BatchCharge selection

/-- A typed execution chain: every append consumes the complete previously
normalized batch through `advanceBatch`, never a code-only replacement. -/
inductive HistoricalNormalization
    {precision : Nat} {targetJournal : Journal P baseDepth}
    (anchor : DiagonalAnchor family targetJournal precision) :
    {start current : Journal P baseDepth} -> {size : Nat} ->
    {chain : family.ExecutedSourceChain precision start current size} ->
    (consumption : family.ExactConsumption anchor chain) ->
    HistoricalGrouping.BatchCharge consumption.indexedSelection -> Type _
  | empty (journal : Journal P baseDepth) :
      HistoricalNormalization anchor (.empty journal) (HistoricalGrouping.initialBatchCharge _)
  | snoc
      {start current : Journal P baseDepth} {size : Nat}
      (prior : family.ExecutedSourceChain precision start current size)
      (sourceAt : family.SourceAt precision)
      (produced : family.ProducedSourceAt current sourceAt)
      (previous : family.ExactConsumption anchor prior)
      (fresh : family.ConsumedSource anchor
        { journal := current, sourceAt := sourceAt, produced := produced })
      (before : HistoricalGrouping.BatchCharge previous.indexedSelection)
      (execution : HistoricalNormalization anchor previous before)
      (oldTraceCompatible :
        HistoricalGrouping.transportBatch
          (previous.indexedSelection.snoc
            { record := { journal := current, sourceAt := sourceAt, produced := produced }, charge := fresh })
          (((HistoricalGrouping.futureContract (family.groupingSpecification anchor)).extendBatch
            previous.indexedSelection
            { record := { journal := current, sourceAt := sourceAt, produced := produced }, charge := fresh }).trace
              (HistoricalGrouping.normalizationTrace previous.indexedSelection))
          (HistoricalGrouping.liftBatchCharge previous.indexedSelection
            { record := { journal := current, sourceAt := sourceAt, produced := produced }, charge := fresh }
            (HistoricalGrouping.initialBatchCharge previous.indexedSelection)) =
        HistoricalGrouping.liftBatchCharge previous.indexedSelection
          { record := { journal := current, sourceAt := sourceAt, produced := produced }, charge := fresh } before) :
      HistoricalNormalization anchor (.snoc prior sourceAt produced previous fresh)
        (HistoricalGrouping.advanceBatch previous.indexedSelection
          { record := { journal := current, sourceAt := sourceAt, produced := produced }, charge := fresh }
          before).result

/-- The seed is already normalized, with a resource-indexed execution chain.
The old consumed evidence and each old SourceCharge/Near are retained exactly. -/
structure HistoricalSeed
    {precision : Nat} {targetJournal : Journal P baseDepth}
    {anchor : DiagonalAnchor family targetJournal precision}
    {start current : Journal P baseDepth} {size : Nat}
    {chain : family.ExecutedSourceChain precision start current size}
    (consumption : family.ExactConsumption anchor chain) where
  seed : HistoricalGrouping.BatchCharge consumption.indexedSelection
  seedExact : seed = HistoricalGrouping.executeBatch consumption.indexedSelection
  normalization : family.HistoricalNormalization anchor consumption seed
  resources : List (family.HistoricalBatchResource anchor)
  localCharges : List (LocalGrouping.GroupedCharge precision anchor.readout)

/--
Each snoc transports the entire already normalized batch and executes the
fresh rule obligation on THAT resource. Its consumed prefix is neither reset
nor consumed twice; only the genuinely fresh charge is appended. The
resource-indexed normalization records this chain, independently of code equality.
-/
def historicalSeed
    {precision : Nat} {targetJournal : Journal P baseDepth}
    {anchor : DiagonalAnchor family targetJournal precision} :
    {start current : Journal P baseDepth} -> {size : Nat} ->
    {chain : family.ExecutedSourceChain precision start current size} ->
    (consumption : family.ExactConsumption anchor chain) ->
      family.HistoricalSeed consumption
  | _, _, _, _, .empty journal =>
      { seed := HistoricalGrouping.initialBatchCharge _, seedExact := rfl,
        normalization := .empty journal,
        resources := [], localCharges := [] }
  | _, _, _, _, .snoc prior sourceAt produced previous fresh => by
      let before := historicalSeed previous
      let selection := previous.indexedSelection
      let added : family.ChargedRecord anchor :=
        { record := { journal := _, sourceAt := sourceAt, produced := produced }, charge := fresh }
      let future := HistoricalGrouping.futureContract (family.groupingSpecification anchor)
      let advanced := HistoricalGrouping.advanceBatch selection added before.seed
      let locals : List (LocalGrouping.GroupedCharge precision anchor.readout) :=
        (HistoricalGrouping.allIndices _).map (fun index =>
        (LocalGrouping.acceptanceAction
          (HistoricalGrouping.finiteSpecification (selection.snoc added))).transport
          ((future.extend selection added).lift (LocalGrouping.Step.group index))
          (HistoricalGrouping.liftSourceCharge selection added index
            (before.seed.available index)))
      exact
      { seed := advanced.result
        seedExact := by
          change (HistoricalGrouping.advanceBatch selection added before.seed).result = _
          rw [before.seedExact]
          exact HistoricalGrouping.advanceBatch_executeBatch selection added
        normalization := .snoc prior sourceAt produced previous fresh before.seed before.normalization
          ((HistoricalGrouping.transportBatch_extension selection added
            (HistoricalGrouping.normalizationTrace selection)
            (HistoricalGrouping.initialBatchCharge selection)).trans
              (congrArg (HistoricalGrouping.liftBatchCharge selection added)
                ((HistoricalGrouping.normalizedBatch_exact selection).trans before.seedExact.symm)))
        resources := before.resources ++
          [{ size := _, selection := selection.snoc added, charge := advanced.transported }]
        localCharges := before.localCharges ++ locals }

/-- Read the normalized resource of the typed historical execution itself.
No second normalization, charge reconstruction, or consumed-prefix reset occurs. -/
def normalizeHistorical
    {precision : Nat} {targetJournal : Journal P baseDepth}
    {anchor : DiagonalAnchor family targetJournal precision}
    {start current : Journal P baseDepth} {size : Nat}
    {chain : family.ExecutedSourceChain precision start current size}
    (consumption : family.ExactConsumption anchor chain)
    (history : family.HistoricalSeed consumption) :
    HistoricalGrouping.BatchCharge consumption.indexedSelection :=
  history.seed

theorem normalizeHistorical_exact
    {precision : Nat} {targetJournal : Journal P baseDepth}
    {anchor : DiagonalAnchor family targetJournal precision}
    {start current : Journal P baseDepth} {size : Nat}
    {chain : family.ExecutedSourceChain precision start current size}
    (consumption : family.ExactConsumption anchor chain)
    (history : family.HistoricalSeed consumption) :
    family.normalizeHistorical consumption history =
      HistoricalGrouping.executeBatch consumption.indexedSelection :=
  history.seedExact

namespace BatchGrouping

variable {family : ExecutedCauchyFamily P baseDepth}
variable {precision : Nat}
variable {start current : Journal P baseDepth}
variable {size : Nat}
variable (chain : family.ExecutedSourceChain precision start current size)
variable (anchor : DiagonalAnchor family current precision)

/-- The target exists only as the result of normalizing these exact charges. -/
structure ProducedTarget (selection : family.ExactConsumption anchor chain) where
  private mk ::
  history : family.HistoricalSeed selection
  normalized : HistoricalGrouping.BatchCharge selection.indexedSelection
  normalizedFromHistory : normalized = family.normalizeHistorical selection history
  localGrouped : (index : HistoricalGrouping.PrefixIndex size) ->
    LocalGrouping.GroupedCharge precision anchor.readout
  localGroupedExact : (index : HistoricalGrouping.PrefixIndex size) ->
    localGrouped index = HistoricalGrouping.normalizeSourceCharge selection.indexedSelection
      index (normalized.available index)
  normalizedExact :
    normalized = HistoricalGrouping.executeBatch selection.indexedSelection

def ProducedTarget.readout
    {selection : family.ExactConsumption anchor chain}
    (produced : ProducedTarget chain anchor selection) : SignedDyadicCode :=
  produced.normalized.outputCode


theorem ProducedTarget.localGrouped_consumedCode
    {selection : family.ExactConsumption anchor chain}
    (produced : ProducedTarget chain anchor selection) (index : HistoricalGrouping.PrefixIndex size) :
    (produced.localGrouped index).consumedCode = (produced.normalized.available index).receivedCode := by
  rw [produced.localGroupedExact, HistoricalGrouping.normalizeSourceCharge_exact]
  rfl

theorem ProducedTarget.localGrouped_consumedNear
    {selection : family.ExactConsumption anchor chain}
    (produced : ProducedTarget chain anchor selection) (index : HistoricalGrouping.PrefixIndex size) :
    HEq (produced.localGrouped index).consumedNearTarget
      (produced.normalized.available index).receivedNearTarget := by
  rw [produced.localGroupedExact]
  exact HistoricalGrouping.normalizeSourceCharge_consumedNear _ _ _

theorem ProducedTarget.localGrouped_accepted
    {selection : family.ExactConsumption anchor chain}
    (produced : ProducedTarget chain anchor selection) (index : HistoricalGrouping.PrefixIndex size) :
    LocalGrouping.AcceptedCharge
      (specification := HistoricalGrouping.finiteSpecification selection.indexedSelection)
      LocalGrouping.State.target (produced.localGrouped index) := by
  rw [produced.localGroupedExact]
  exact (LocalGrouping.acceptanceAction
    (HistoricalGrouping.finiteSpecification selection.indexedSelection)).transport_preserves
      (HistoricalGrouping.normalizeSourceTrace selection.indexedSelection index)
      (produced.normalized.available index)
      (Nonempty.intro (produced.normalized.available index).receivedCodeExact)

/-- Context reception owns the exact structural consumption of the batch. -/
structure Context (_request : Unit) where
  private mk ::
  selection : family.ExactConsumption anchor chain

structure Search (_request : Unit) where
  private mk ::
  selection : family.ExactConsumption anchor chain

structure Action (_request : Unit) (searched : Search chain anchor ()) where
  private mk ::
  consumed : family.ExactConsumption anchor chain
  consumedExact : consumed = searched.selection
  target : ProducedTarget chain anchor searched.selection

def Action.code
    {searched : Search chain anchor ()}
    (acted : Action chain anchor () searched) : SignedDyadicCode :=
  acted.target.readout

def Action.normalized
    {searched : Search chain anchor ()}
    (acted : Action chain anchor () searched) :
    HistoricalGrouping.BatchCharge searched.selection.indexedSelection :=
  acted.target.normalized

theorem Action.normalizedExact
    {searched : Search chain anchor ()}
    (acted : Action chain anchor () searched) :
    acted.normalized = HistoricalGrouping.executeBatch searched.selection.indexedSelection :=
  acted.target.normalizedExact

structure Accepted (_request : Unit) (searched : Search chain anchor ())
    (acted : Action chain anchor () searched) where
  private mk ::
  exactEnumeration : ExactIndexEnumeration size
  exactEnumerationIsConsumption :
    exactEnumeration = acted.consumed.indexing
  groupingAccepted : HistoricalGrouping.BatchAccepted
    (.target : HistoricalGrouping.BatchState size) acted.normalized
  normalTarget :
    (HistoricalGrouping.batchRules searched.selection.indexedSelection).normal
      (HistoricalGrouping.initialBatchState searched.selection.indexedSelection) = .target
  token : Unit

structure Authorization (_request : Unit) (searched : Search chain anchor ())
    (acted : Action chain anchor () searched)
    (accepted : Accepted chain anchor () searched acted) where
  private mk ::
  token : Unit

structure Decomposition (_request : Unit) (searched : Search chain anchor ())
    (acted : Action chain anchor () searched)
    (accepted : Accepted chain anchor () searched acted)
    (authorized : Authorization chain anchor () searched acted accepted) where
  private mk ::
  consumed : family.ExactConsumption anchor chain
  consumedExact : consumed = acted.consumed

structure Continuation (_request : Unit) (searched : Search chain anchor ())
    (acted : Action chain anchor () searched)
    (accepted : Accepted chain anchor () searched acted)
    (authorized : Authorization chain anchor () searched acted accepted)
    (decomposed : Decomposition chain anchor () searched acted accepted authorized) where
  private mk ::
  consumed : family.ExactConsumption anchor chain
  consumedExact : consumed = decomposed.consumed

structure Stored (_request : Unit) (searched : Search chain anchor ())
    (acted : Action chain anchor () searched) where
  private mk ::
  action : Action chain anchor () searched
  actionExact : action = acted

def program : Program Unit where
  ReceivedContext := Context chain anchor
  SearchResult := Search chain anchor
  ActionResult := Action chain anchor
  Accepted := Accepted chain anchor
  Authorization := Authorization chain anchor
  Decomposition := Decomposition chain anchor
  Continuation := Continuation chain anchor
  Stored := Stored chain anchor
  stamp := fun _request => .finiteGrouping precision size
  receive := fun _request =>
    { selection := consumeAll (family := family) anchor chain }
  search := fun _request context =>
    { selection := context.selection }
  act := fun _request searched =>
    { consumed := searched.selection
      consumedExact := rfl
      target :=
        let history := family.historicalSeed searched.selection
        let normalized := family.normalizeHistorical searched.selection history
        { history := history
          normalized := normalized
          normalizedFromHistory := rfl
          localGrouped := fun index => HistoricalGrouping.normalizeSourceCharge
            searched.selection.indexedSelection index (normalized.available index)
          localGroupedExact := fun _ => rfl
          normalizedExact := family.normalizeHistorical_exact _ history } }
  preserves := fun _request _searched acted =>
    { exactEnumeration := acted.consumed.indexing
      exactEnumerationIsConsumption := rfl
      groupingAccepted := by
        rw [acted.normalizedExact]
        exact HistoricalGrouping.executeBatchAccepted _
      normalTarget := HistoricalGrouping.normal_initialBatchState _
      token := () }
  authorize := fun _request _searched _acted _accepted => { token := () }
  decompose := fun _request _searched acted _accepted _authorized =>
    { consumed := acted.consumed, consumedExact := rfl }
  resume := fun _request _searched _acted _accepted _authorized decomposed =>
    { consumed := decomposed.consumed, consumedExact := rfl }
  store := fun _request _searched acted _accepted _authorized _decomposed
      _continued =>
    { action := acted, actionExact := rfl }
  actionCode := fun acted => acted.code
  read := fun stored => stored.action.code
  readStoredExact := fun stored => by rw [stored.actionExact]

theorem program_actionCode_exact
    (searched : (program chain anchor).SearchResult ())
    (acted : (program chain anchor).ActionResult () searched) :
    (program chain anchor).actionCode acted = anchor.readout := by
  change acted.normalized.outputCode = anchor.readout
  rw [acted.normalizedExact]
  exact HistoricalGrouping.executeBatch_outputCode _

end BatchGrouping

/-- Finite grouping built only from a chronological chain and produced target. -/
structure ExecutedFiniteGrouping
    {precision : Nat}
    {start current : Journal P baseDepth}
    {size : Nat}
    (chain : family.ExecutedSourceChain precision start current size) where
  private mk ::
  anchor : DiagonalAnchor family current precision
  execution : ExecutedRequest (BatchGrouping.program chain anchor) P
    anchor.completedJournal ()

def executeFiniteGrouping
    {precision : Nat}
    {start current : Journal P baseDepth}
    {size : Nat}
    (chain : family.ExecutedSourceChain precision start current size) :
    family.ExecutedFiniteGrouping chain := by
  let anchor := family.executeAnchor current precision
  exact
  { anchor := anchor
    execution := execute (BatchGrouping.program chain anchor) P
      anchor.completedJournal () }

namespace ExecutedFiniteGrouping

/-- The resource created by this batch action, not the source anchor. -/
def target
    {precision : Nat} {start current : Journal P baseDepth} {size : Nat}
    {chain : family.ExecutedSourceChain precision start current size}
    (grouping : family.ExecutedFiniteGrouping chain) :=
  grouping.execution.action.target

def consumption
    {family : ExecutedCauchyFamily P baseDepth}
    {precision : Nat}
    {start current : Journal P baseDepth}
    {size : Nat}
    {chain : family.ExecutedSourceChain precision start current size}
    (grouped : family.ExecutedFiniteGrouping chain) :
    family.ExactConsumption grouped.anchor chain :=
  grouped.execution.action.consumed

/-- Historical normalization actually executed by the retained batch action. -/
def normalizedBatch
    {family : ExecutedCauchyFamily P baseDepth}
    {precision : Nat}
    {start current : Journal P baseDepth}
    {size : Nat}
    {chain : family.ExecutedSourceChain precision start current size}
    (grouped : family.ExecutedFiniteGrouping chain) :
    HistoricalGrouping.BatchCharge
      grouped.execution.memory.continued.authorized.acted.searched.result.selection.indexedSelection :=
  grouped.execution.action.normalized

theorem normalizedBatch_exact
    {family : ExecutedCauchyFamily P baseDepth}
    {precision : Nat}
    {start current : Journal P baseDepth}
    {size : Nat}
    {chain : family.ExecutedSourceChain precision start current size}
    (grouped : family.ExecutedFiniteGrouping chain) :
    grouped.normalizedBatch = HistoricalGrouping.executeBatch
      grouped.execution.memory.continued.authorized.acted.searched.result.selection.indexedSelection :=
  grouped.execution.action.normalizedExact

/-- The historical action retained by the exact batch is admitted. -/
theorem normalizedBatch_accepted
    {family : ExecutedCauchyFamily P baseDepth}
    {precision : Nat}
    {start current : Journal P baseDepth}
    {size : Nat}
    {chain : family.ExecutedSourceChain precision start current size}
    (grouped : family.ExecutedFiniteGrouping chain) :
    HistoricalGrouping.BatchAccepted
      (.target : HistoricalGrouping.BatchState size)
      grouped.normalizedBatch :=
  grouped.execution.memory.continued.authorized.accepted.groupingAccepted

/-- The executed historical batch consumes exactly `size` sources. -/
theorem normalizedBatch_consumed_length
    {family : ExecutedCauchyFamily P baseDepth}
    {precision : Nat}
    {start current : Journal P baseDepth}
    {size : Nat}
    {chain : family.ExecutedSourceChain precision start current size}
    (grouped : family.ExecutedFiniteGrouping chain) :
    grouped.normalizedBatch.consumed.length = size := by
  rw [grouped.normalizedBatch_exact]
  exact HistoricalGrouping.executeBatch_consumed_length _

/-- The exact oldest-first consumed charges are those of the chain selection. -/
theorem normalizedBatch_consumed_exact
    {family : ExecutedCauchyFamily P baseDepth}
    {precision : Nat}
    {start current : Journal P baseDepth}
    {size : Nat}
    {chain : family.ExecutedSourceChain precision start current size}
    (grouped : family.ExecutedFiniteGrouping chain) :
    grouped.normalizedBatch.consumed =
      HistoricalGrouping.chargesForIndices
        grouped.execution.memory.continued.authorized.acted.searched.result.selection.indexedSelection
        (HistoricalGrouping.initialBatchCharge
          grouped.execution.memory.continued.authorized.acted.searched.result.selection.indexedSelection).available
        (HistoricalGrouping.allIndices size) := by
  rw [grouped.normalizedBatch_exact]
  exact HistoricalGrouping.executeBatch_consumed_exact _

def consumesEverySource
    {family : ExecutedCauchyFamily P baseDepth}
    {precision : Nat}
    {start current : Journal P baseDepth}
    {size : Nat}
    {chain : family.ExecutedSourceChain precision start current size}
    (grouped : family.ExecutedFiniteGrouping chain) :
    family.ExactConsumption grouped.anchor chain :=
  grouped.consumption

/-- Unary chronological shape projected from the exact structural consumption. -/
def consumptionShape
    {family : ExecutedCauchyFamily P baseDepth}
    {precision : Nat}
    {start current : Journal P baseDepth}
    {size : Nat}
    {chain : family.ExecutedSourceChain precision start current size}
    (grouped : family.ExecutedFiniteGrouping chain) :
    ExactIndexEnumeration size :=
  grouped.consumption.indexing

theorem consumptionShape_exact
    {family : ExecutedCauchyFamily P baseDepth}
    {precision : Nat}
    {start current : Journal P baseDepth}
    {size : Nat}
    {chain : family.ExecutedSourceChain precision start current size}
    (grouped : family.ExecutedFiniteGrouping chain) :
    grouped.consumption.indexing = allIndices size :=
  grouped.consumption.indexing.unique

def readout
    {family : ExecutedCauchyFamily P baseDepth}
    {precision : Nat}
    {start current : Journal P baseDepth}
    {size : Nat}
    {chain : family.ExecutedSourceChain precision start current size}
    (grouped : family.ExecutedFiniteGrouping chain) : SignedDyadicCode :=
  grouped.execution.readout

theorem readout_is_producedTarget
    {family : ExecutedCauchyFamily P baseDepth}
    {precision : Nat}
    {start current : Journal P baseDepth}
    {size : Nat}
    {chain : family.ExecutedSourceChain precision start current size}
    (grouped : family.ExecutedFiniteGrouping chain) :
    grouped.readout = grouped.target.readout :=
  grouped.execution.readout_is_storedAction

end ExecutedFiniteGrouping


/-- Code and occurrence are projections of the same completed grouping action. -/
def targetOccurrence
    {family : ExecutedCauchyFamily P baseDepth}
    {precision : Nat} {start current : Journal P baseDepth} {size : Nat}
    {chain : family.ExecutedSourceChain precision start current size}
    (grouped : family.ExecutedFiniteGrouping chain) :=
  grouped.execution.memory.continued.authorized.acted.phase.occurrence

theorem readout_is_anchor
    {family : ExecutedCauchyFamily P baseDepth}
    {precision : Nat} {start current : Journal P baseDepth} {size : Nat}
    {chain : family.ExecutedSourceChain precision start current size}
    (grouped : family.ExecutedFiniteGrouping chain) :
    grouped.readout = grouped.anchor.readout :=
  grouped.execution.readout_is_storedAction.trans
    (BatchGrouping.program_actionCode_exact chain grouped.anchor _ _)

theorem completedDepth
    {family : ExecutedCauchyFamily P baseDepth}
    {precision : Nat} {start current : Journal P baseDepth} {size : Nat}
    {chain : family.ExecutedSourceChain precision start current size}
    (grouped : family.ExecutedFiniteGrouping chain) :
    grouped.execution.completedJournal.absoluteDepth = current.absoluteDepth + 12 := by
  rw [grouped.execution.completed_absoluteDepth]
  change grouped.anchor.source.completedJournal.absoluteDepth + 6 = _
  rw [grouped.anchor.source.completedDepth]


end ExecutedCauchyFamily

end RelationalPerimeter.Constitution.Reals.ProducedCompleteness

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Constitution.Reals.ProducedCompleteness.SourceRequest
#print axioms RelationalPerimeter.Constitution.Reals.ProducedCompleteness.SourceProducer
#print axioms RelationalPerimeter.Constitution.Reals.ProducedCompleteness.SourceContext
#print axioms RelationalPerimeter.Constitution.Reals.ProducedCompleteness.sourceProgram
#print axioms RelationalPerimeter.Constitution.Reals.ProducedCompleteness.sourceProgram_actionCode_exact
#print axioms RelationalPerimeter.Constitution.Reals.ProducedCompleteness.ExecutedCauchyFamily
#print axioms RelationalPerimeter.Constitution.Reals.ProducedCompleteness.ExecutedCauchyFamily.SourceAt
#print axioms RelationalPerimeter.Constitution.Reals.ProducedCompleteness.ExecutedCauchyFamily.diagonalSourceAt
#print axioms RelationalPerimeter.Constitution.Reals.ProducedCompleteness.ExecutedCauchyFamily.ProducedSourceAt
#print axioms RelationalPerimeter.Constitution.Reals.ProducedCompleteness.ExecutedCauchyFamily.produceSourceAt
#print axioms RelationalPerimeter.Constitution.Reals.ProducedCompleteness.ExecutedCauchyFamily.ProducedSourceAt.readout_is_calculated
#print axioms RelationalPerimeter.Constitution.Reals.ProducedCompleteness.ExecutedCauchyFamily.ProducedSourceAt.sameTermExecutedNear
#print axioms RelationalPerimeter.Constitution.Reals.ProducedCompleteness.LimitGrouping.Context
#print axioms RelationalPerimeter.Constitution.Reals.ProducedCompleteness.LimitGrouping.ProducedTarget
#print axioms RelationalPerimeter.Constitution.Reals.ProducedCompleteness.LimitGrouping.Action
#print axioms RelationalPerimeter.Constitution.Reals.ProducedCompleteness.LimitGrouping.program
#print axioms RelationalPerimeter.Constitution.Reals.ProducedCompleteness.LimitGrouping.program_actionCode_exact
#print axioms RelationalPerimeter.Constitution.Reals.ProducedCompleteness.ExecutedLimitProduction
#print axioms RelationalPerimeter.Constitution.Reals.ProducedCompleteness.executeLimitProduction
#print axioms RelationalPerimeter.Constitution.Reals.ProducedCompleteness.ExecutedLimitProduction.targetCode
#print axioms RelationalPerimeter.Constitution.Reals.ProducedCompleteness.ExecutedLimitProduction.readout_is_targetCode
#print axioms RelationalPerimeter.Constitution.Reals.ProducedCompleteness.ExecutedLimitProduction.sourceNearTarget
#print axioms RelationalPerimeter.Constitution.Reals.ProducedCompleteness.ExecutedLimitProduction.sourceNearReadout
#print axioms RelationalPerimeter.Constitution.Reals.ProducedCompleteness.ExecutedLimitProduction.readout_is_source
#print axioms RelationalPerimeter.Constitution.Reals.ProducedCompleteness.ExecutedLimitProduction.completedDepth
#print axioms RelationalPerimeter.Constitution.Reals.ProducedCompleteness.ExactIndexEnumeration
#print axioms RelationalPerimeter.Constitution.Reals.ProducedCompleteness.allIndices
#print axioms RelationalPerimeter.Constitution.Reals.ProducedCompleteness.allIndices_length
#print axioms RelationalPerimeter.Constitution.Reals.ProducedCompleteness.ExecutedCauchyFamily.SourceRecord
#print axioms RelationalPerimeter.Constitution.Reals.ProducedCompleteness.ExecutedCauchyFamily.ExecutedSourceChain
#print axioms RelationalPerimeter.Constitution.Reals.ProducedCompleteness.ExecutedCauchyFamily.ExecutedSourceChain.append
#print axioms RelationalPerimeter.Constitution.Reals.ProducedCompleteness.ExecutedCauchyFamily.ExecutedSourceChain.operationCount
#print axioms RelationalPerimeter.Constitution.Reals.ProducedCompleteness.ExecutedCauchyFamily.ExecutedSourceChain.records
#print axioms RelationalPerimeter.Constitution.Reals.ProducedCompleteness.ExecutedCauchyFamily.ExecutedSourceChain.finalDepth_exact
#print axioms RelationalPerimeter.Constitution.Reals.ProducedCompleteness.ExecutedCauchyFamily.ConsumedSource
#print axioms RelationalPerimeter.Constitution.Reals.ProducedCompleteness.ExecutedCauchyFamily.consumeSource
#print axioms RelationalPerimeter.Constitution.Reals.ProducedCompleteness.ExecutedCauchyFamily.groupingSpecification
#print axioms RelationalPerimeter.Constitution.Reals.ProducedCompleteness.ExecutedCauchyFamily.ExecutedSourceChain.selection
#print axioms RelationalPerimeter.Constitution.Reals.ProducedCompleteness.ExecutedCauchyFamily.ExactConsumption
#print axioms RelationalPerimeter.Constitution.Reals.ProducedCompleteness.ExecutedCauchyFamily.consumeAll
#print axioms RelationalPerimeter.Constitution.Reals.ProducedCompleteness.ExecutedCauchyFamily.ExactConsumption.records
#print axioms RelationalPerimeter.Constitution.Reals.ProducedCompleteness.ExecutedCauchyFamily.ExactConsumption.records_exact
#print axioms RelationalPerimeter.Constitution.Reals.ProducedCompleteness.ExecutedCauchyFamily.ExactConsumption.indexedSelection
#print axioms RelationalPerimeter.Constitution.Reals.ProducedCompleteness.ExecutedCauchyFamily.BatchGrouping.Context
#print axioms RelationalPerimeter.Constitution.Reals.ProducedCompleteness.ExecutedCauchyFamily.BatchGrouping.Action
#print axioms RelationalPerimeter.Constitution.Reals.ProducedCompleteness.ExecutedCauchyFamily.BatchGrouping.program
#print axioms RelationalPerimeter.Constitution.Reals.ProducedCompleteness.ExecutedCauchyFamily.ExecutedFiniteGrouping
#print axioms RelationalPerimeter.Constitution.Reals.ProducedCompleteness.ExecutedCauchyFamily.executeFiniteGrouping
#print axioms RelationalPerimeter.Constitution.Reals.ProducedCompleteness.ExecutedCauchyFamily.ExecutedFiniteGrouping.normalizedBatch
#print axioms RelationalPerimeter.Constitution.Reals.ProducedCompleteness.ExecutedCauchyFamily.ExecutedFiniteGrouping.normalizedBatch_exact
#print axioms RelationalPerimeter.Constitution.Reals.ProducedCompleteness.ExecutedCauchyFamily.ExecutedFiniteGrouping.normalizedBatch_accepted
#print axioms RelationalPerimeter.Constitution.Reals.ProducedCompleteness.ExecutedCauchyFamily.ExecutedFiniteGrouping.normalizedBatch_consumed_length
#print axioms RelationalPerimeter.Constitution.Reals.ProducedCompleteness.ExecutedCauchyFamily.ExecutedFiniteGrouping.normalizedBatch_consumed_exact
#print axioms RelationalPerimeter.Constitution.Reals.ProducedCompleteness.ExecutedCauchyFamily.ExecutedFiniteGrouping.consumesEverySource
#print axioms RelationalPerimeter.Constitution.Reals.ProducedCompleteness.ExecutedCauchyFamily.ExecutedFiniteGrouping.consumptionShape
#print axioms RelationalPerimeter.Constitution.Reals.ProducedCompleteness.ExecutedCauchyFamily.ExecutedFiniteGrouping.consumptionShape_exact
#print axioms RelationalPerimeter.Constitution.Reals.ProducedCompleteness.ExecutedCauchyFamily.ExecutedFiniteGrouping.readout_is_producedTarget
#print axioms RelationalPerimeter.Constitution.Reals.ProducedCompleteness.LimitGrouping.receivedNear
#print axioms RelationalPerimeter.Constitution.Reals.ProducedCompleteness.LimitGrouping.specification
#print axioms RelationalPerimeter.Constitution.Reals.ProducedCompleteness.LimitGrouping.normalizationTrace
#print axioms RelationalPerimeter.Constitution.Reals.ProducedCompleteness.LimitGrouping.normalizedCharge
#print axioms RelationalPerimeter.Constitution.Reals.ProducedCompleteness.LimitGrouping.normalizedCharge_exact
#print axioms RelationalPerimeter.Constitution.Reals.ProducedCompleteness.LimitGrouping.normalizedCharge_code
#print axioms RelationalPerimeter.Constitution.Reals.ProducedCompleteness.ExecutedCauchyFamily.DiagonalAnchor
#print axioms RelationalPerimeter.Constitution.Reals.ProducedCompleteness.ExecutedCauchyFamily.executeAnchor
#print axioms RelationalPerimeter.Constitution.Reals.ProducedCompleteness.ExecutedCauchyFamily.DiagonalAnchor.sourceAt
#print axioms RelationalPerimeter.Constitution.Reals.ProducedCompleteness.ExecutedCauchyFamily.DiagonalAnchor.sourceAtExact
#print axioms RelationalPerimeter.Constitution.Reals.ProducedCompleteness.ExecutedCauchyFamily.DiagonalAnchor.readout
#print axioms RelationalPerimeter.Constitution.Reals.ProducedCompleteness.ExecutedCauchyFamily.DiagonalAnchor.completedJournal
#print axioms RelationalPerimeter.Constitution.Reals.ProducedCompleteness.ExecutedCauchyFamily.ExecutedLimitProduction.toAnchor
#print axioms RelationalPerimeter.Constitution.Reals.ProducedCompleteness.ExecutedCauchyFamily.limitToSourceAnchor
#print axioms RelationalPerimeter.Constitution.Reals.ProducedCompleteness.ExecutedCauchyFamily.BatchGrouping.ProducedTarget
#print axioms RelationalPerimeter.Constitution.Reals.ProducedCompleteness.ExecutedCauchyFamily.BatchGrouping.ProducedTarget.readout
#print axioms RelationalPerimeter.Constitution.Reals.ProducedCompleteness.ExecutedCauchyFamily.BatchGrouping.Action.normalized
#print axioms RelationalPerimeter.Constitution.Reals.ProducedCompleteness.ExecutedCauchyFamily.BatchGrouping.Action.normalizedExact
#print axioms RelationalPerimeter.Constitution.Reals.ProducedCompleteness.ExecutedCauchyFamily.ExecutedFiniteGrouping.target
#print axioms RelationalPerimeter.Constitution.Reals.ProducedCompleteness.ExecutedCauchyFamily.TermModel
#print axioms RelationalPerimeter.Constitution.Reals.ProducedCompleteness.ExecutedCauchyFamily.termModel
#print axioms RelationalPerimeter.Constitution.Reals.ProducedCompleteness.ExecutedCauchyFamily.targetOccurrence
#print axioms RelationalPerimeter.Constitution.Reals.ProducedCompleteness.ExecutedCauchyFamily.readout_is_anchor
#print axioms RelationalPerimeter.Constitution.Reals.ProducedCompleteness.ExecutedCauchyFamily.completedDepth
#print axioms RelationalPerimeter.Constitution.Reals.ProducedCompleteness.ExecutedCauchyFamily.ExecutedSourceChain.concatenate
#print axioms RelationalPerimeter.Constitution.Reals.ProducedCompleteness.ExecutedCauchyFamily.ExecutedSourceChain.concatenate_records
#print axioms RelationalPerimeter.Constitution.Reals.ProducedCompleteness.ExecutedCauchyFamily.ExecutedSourceChain.listAppendNil
#print axioms RelationalPerimeter.Constitution.Reals.ProducedCompleteness.ExecutedCauchyFamily.ExecutedSourceChain.listAppendAssoc
#print axioms RelationalPerimeter.Constitution.Reals.ProducedCompleteness.ExecutedCauchyFamily.ChargedRecord
#print axioms RelationalPerimeter.Constitution.Reals.ProducedCompleteness.ExecutedCauchyFamily.HistoricalBatchResource
#print axioms RelationalPerimeter.Constitution.Reals.ProducedCompleteness.ExecutedCauchyFamily.HistoricalSeed
#print axioms RelationalPerimeter.Constitution.Reals.ProducedCompleteness.ExecutedCauchyFamily.historicalSeed
#print axioms RelationalPerimeter.Constitution.Reals.ProducedCompleteness.ExecutedCauchyFamily.normalizeHistorical
#print axioms RelationalPerimeter.Constitution.Reals.ProducedCompleteness.ExecutedCauchyFamily.normalizeHistorical_exact
#print axioms RelationalPerimeter.Constitution.Reals.ProducedCompleteness.ExecutedCauchyFamily.BatchGrouping.ProducedTarget.localGrouped_consumedCode
#print axioms RelationalPerimeter.Constitution.Reals.ProducedCompleteness.ExecutedCauchyFamily.BatchGrouping.ProducedTarget.localGrouped_consumedNear
#print axioms RelationalPerimeter.Constitution.Reals.ProducedCompleteness.ExecutedCauchyFamily.BatchGrouping.ProducedTarget.localGrouped_accepted
#print axioms RelationalPerimeter.Constitution.Reals.ProducedCompleteness.ExecutedCauchyFamily.HistoricalNormalization
/- AXIOM_AUDIT_END -/
