import RelationalPerimeter.Constitution.Reals.ProducedCompleteness
import RelationalPerimeter.Constitution.Continuation.Minimality

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Authoritative runtime for produced relational reals

This runtime is the authoritative route used by the terminal raccord from a
public request to an observation.  Its state starts over an already constituted base history,
executes the producer and grouping programs, stores their exact dependent
resources, advances the same journal, and exposes only the memory readout.

The reduced transition below is a specification of that execution.  It does
not produce rich states and is not used to build the terminal raccord.
-/

namespace RelationalPerimeter.Constitution.Reals.AuthoritativeRuntime

open StrongPerimetralTurning
open ConstitutiveRuntime
open ProducedCompleteness
open ConstitutiveSearch.ContinuationSignatures

variable {P : CircularPresentation} {baseDepth : Nat}

/-- Public requests contain indices and certificates, never proposed outputs. -/
inductive RuntimeRequest (family : ExecutedCauchyFamily P baseDepth) : Type
  | source (precision : Nat) (sourceAt : family.SourceAt precision)
  | limit (precision : Nat)

/-- The last observation identifies its request and its memory-derived code. -/
structure Observation where
  stamp : RequestStamp
  code : SignedDyadicCode

theorem Observation.extensionality
    (first second : Observation)
    (stampExact : first.stamp = second.stamp)
    (codeExact : first.code = second.code) : first = second := by
  cases first
  cases second
  cases stampExact
  cases codeExact
  rfl

/-- A completed transition event records the exact journal endpoints. -/
structure RuntimeEvent where
  startDepth : Nat
  endDepth : Nat
  stamp : RequestStamp
  readout : SignedDyadicCode

theorem RuntimeEvent.extensionality
    (first second : RuntimeEvent)
    (startExact : first.startDepth = second.startDepth)
    (endExact : first.endDepth = second.endDepth)
    (stampExact : first.stamp = second.stamp)
    (readoutExact : first.readout = second.readout) : first = second := by
  cases first
  cases second
  cases startExact
  cases endExact
  cases stampExact
  cases readoutExact
  rfl


/-- An owned grouping target; rescaling preserves its original occurrence. -/
inductive OwnedTarget (family : ExecutedCauchyFamily P baseDepth) where
  | limit {journal : Journal P baseDepth} {precision : Nat}
      (produced : ExecutedLimitProduction family journal precision)
  | batch {precision : Nat} {start current : Journal P baseDepth} {size : Nat}
      {chain : family.ExecutedSourceChain precision start current size}
      (produced : family.ExecutedFiniteGrouping chain)
  | rescaled (prior : OwnedTarget family) (extra : Nat)

namespace OwnedTarget
def readout {family : ExecutedCauchyFamily P baseDepth} : OwnedTarget family -> SignedDyadicCode
  | .limit produced => produced.readout
  | .batch produced => produced.readout
  | .rescaled prior extra => prior.readout.raise extra
def stamp {family : ExecutedCauchyFamily P baseDepth} : OwnedTarget family -> RequestStamp
  | .limit (precision := precision) _ => .limit precision
  | .batch (precision := precision) (size := size) _ => .finiteGrouping precision size
  | .rescaled prior _ => prior.stamp
end OwnedTarget

structure RetainedTarget {family : ExecutedCauchyFamily P baseDepth} (target : OwnedTarget family) where
  private mk ::
  value : OwnedTarget family
  exact : value = target

structure TargetContinuationAction {family : ExecutedCauchyFamily P baseDepth}
    (target : OwnedTarget family) (extra : Nat) (searched : RetainedTarget target) where
  private mk ::
  retained : RetainedTarget target
  retainedExact : retained = searched
  code : SignedDyadicCode
  codeExact : code = retained.value.readout.raise extra

structure TargetContinuationAccepted {family : ExecutedCauchyFamily P baseDepth}
    {target : OwnedTarget family} {extra : Nat} {searched : RetainedTarget target}
    (acted : TargetContinuationAction target extra searched) where
  private mk ::
  sameValue : SameValue acted.code target.readout

structure TargetContinuationStored {family : ExecutedCauchyFamily P baseDepth}
    {target : OwnedTarget family} {extra : Nat} {searched : RetainedTarget target}
    (acted : TargetContinuationAction target extra searched) where
  private mk ::
  action : TargetContinuationAction target extra searched
  actionExact : action = acted

/-- Re-read the retained resource itself, not a recalculated producer output. -/
def targetContinuationProgram {family : ExecutedCauchyFamily P baseDepth}
    (target : OwnedTarget family) (extra : Nat) : Program Unit where
  ReceivedContext := fun _ => RetainedTarget target
  SearchResult := fun _ => RetainedTarget target
  ActionResult := fun _ searched => TargetContinuationAction target extra searched
  Accepted := fun _ _ acted => TargetContinuationAccepted acted
  Authorization := fun _ _ _ _ => Unit
  Decomposition := fun _ _ _ _ _ => RetainedTarget target
  Continuation := fun _ _ _ _ _ _ => RetainedTarget target
  Stored := fun _ _ acted => TargetContinuationStored acted
  stamp := fun _ => target.stamp
  receive := fun _ => { value := target, exact := rfl }
  search := fun _ received => received
  act := fun _ searched =>
    { retained := searched, retainedExact := rfl,
      code := searched.value.readout.raise extra, codeExact := rfl }
  preserves := fun _ _ acted =>
    { sameValue := by
        rw [acted.codeExact, acted.retained.exact]
        exact (SameValue.raiseExact target.readout extra).symm }
  authorize := fun _ _ _ _ => ()
  decompose := fun _ _ acted _ _ => acted.retained
  resume := fun _ _ _ _ _ decomposed => decomposed
  store := fun _ _ acted _ _ _ _ => { action := acted, actionExact := rfl }
  actionCode := fun acted => acted.code
  read := fun stored => stored.action.code
  readStoredExact := fun stored => by rw [stored.actionExact]

theorem targetContinuation_readout
    {family : ExecutedCauchyFamily P baseDepth} {journal : Journal P baseDepth}
    (target : OwnedTarget family) (extra : Nat)
    (executed : ExecutedRequest (targetContinuationProgram target extra) P journal ()) :
    executed.readout = target.readout.raise extra := by
  rw [executed.readout_is_storedAction]
  change executed.action.code = _
  rw [executed.action.codeExact, executed.action.retained.exact]


/-- Resources retained by memory are the actual dependent execution packages. -/
inductive StoredResource (family : ExecutedCauchyFamily P baseDepth) : Type
  | rawSource {journal : Journal P baseDepth} {request : SourceRequest}
      (produced : ExecutedRequest (sourceProgram family.producer) P journal request)
  | batch {precision : Nat} {start current : Journal P baseDepth} {size : Nat}
      {chain : family.ExecutedSourceChain precision start current size}
      (produced : family.ExecutedFiniteGrouping chain)
  | continued {journal : Journal P baseDepth} (target : OwnedTarget family) (extra : Nat)
      (produced : ExecutedRequest (targetContinuationProgram target extra) P journal ())
  | source
      {journal : Journal P baseDepth}
      {precision : Nat}
      {sourceAt : family.SourceAt precision}
      (produced : family.ProducedSourceAt journal sourceAt)
  | limit
      {journal : Journal P baseDepth}
      {precision : Nat}
      (produced : ExecutedLimitProduction family journal precision)


def OwnedTarget.observation {family : ExecutedCauchyFamily P baseDepth}
    (target : OwnedTarget family) : Observation :=
  { stamp := target.stamp, code := target.readout }

def installedObservation : Option Observation -> Option Observation
  | none => none
  | some observed =>
      match observed.stamp with
      | .source _ _ => none
      | .limit _ | .finiteGrouping _ _ => some observed


/-- Rich state.  Its private constructor prevents arbitrary journal updates. -/
structure Runtime (family : ExecutedCauchyFamily P baseDepth) where
  private mk ::
  journal : Journal P baseDepth
  memory : List (StoredResource family)
  last : Option Observation
  target : Option (OwnedTarget family)
  targetReadExact : target.map OwnedTarget.observation = installedObservation last

/-- Initialize over the supplied constitutive base; no artificial seed is added. -/
def initialState (family : ExecutedCauchyFamily P baseDepth) : Runtime family :=
  .mk (Journal.root P baseDepth) [] none none rfl

/-- Public runtime read; it reveals only the last memory-derived observation. -/
def read
    {family : ExecutedCauchyFamily P baseDepth}
    (state : Runtime family) : Option Observation :=
  state.last

private inductive ResponseResource
    (family : ExecutedCauchyFamily P baseDepth)
    (state : Runtime family) : RuntimeRequest family -> Type
  | source
      {precision : Nat}
      {sourceAt : family.SourceAt precision}
      (produced : family.ProducedSourceAt state.journal sourceAt) :
      ResponseResource family state (.source precision sourceAt)
  | limit
      (precision : Nat)
      (produced : ExecutedLimitProduction family state.journal precision) :
      ResponseResource family state (.limit precision)

/-- One response, constructible only by executing the requested producer. -/
structure ExecutedResponse
    (family : ExecutedCauchyFamily P baseDepth)
    (state : Runtime family)
    (request : RuntimeRequest family) where
  private mk ::
  private resource : ResponseResource family state request

/-- Execute the producer selected by the public request exactly once. -/
def executeResponse
    (family : ExecutedCauchyFamily P baseDepth)
    (state : Runtime family)
    (request : RuntimeRequest family) :
    ExecutedResponse family state request :=
  match request with
  | .source precision sourceAt =>
      .mk (.source (family.produceSourceAt state.journal sourceAt))
  | .limit precision =>
      .mk (.limit precision
        (executeLimitProduction family state.journal precision))

namespace ExecutedResponse

def completedJournal
    {family : ExecutedCauchyFamily P baseDepth}
    {state : Runtime family}
    {request : RuntimeRequest family}
    (response : ExecutedResponse family state request) : Journal P baseDepth :=
  match response.resource with
  | .source produced => produced.completedJournal
  | .limit _ produced => produced.completedJournal

def storedResource
    {family : ExecutedCauchyFamily P baseDepth}
    {state : Runtime family}
    {request : RuntimeRequest family}
    (response : ExecutedResponse family state request) : StoredResource family :=
  match response.resource with
  | .source produced => .source produced
  | .limit _ produced => .limit produced

def stamp
    {family : ExecutedCauchyFamily P baseDepth}
    {state : Runtime family}
    {request : RuntimeRequest family}
    (response : ExecutedResponse family state request) : RequestStamp :=
  match response.resource with
  | .source (sourceAt := sourceAt) _ =>
      .source sourceAt.request.term sourceAt.request.precision
  | .limit precision _ => .limit precision

/-- A limit response exposes exactly the stamp fixed by its request index. -/
theorem limit_stamp
    {family : ExecutedCauchyFamily P baseDepth}
    {state : Runtime family}
    {precision : Nat}
    (response : ExecutedResponse family state (.limit precision)) :
    response.stamp = .limit precision := by
  rcases response with ⟨resource⟩
  cases resource
  rfl

/-- The response readout is exclusively the readout of its retained memory resource. -/
def readout
    {family : ExecutedCauchyFamily P baseDepth}
    {state : Runtime family}
    {request : RuntimeRequest family}
    (response : ExecutedResponse family state request) : SignedDyadicCode :=
  match response.resource with
  | .source produced => produced.readout
  | .limit _ produced => produced.readout

def observation
    {family : ExecutedCauchyFamily P baseDepth}
    {state : Runtime family}
    {request : RuntimeRequest family}
    (response : ExecutedResponse family state request) : Observation :=
  { stamp := response.stamp, code := response.readout }

def event
    {family : ExecutedCauchyFamily P baseDepth}
    {state : Runtime family}
    {request : RuntimeRequest family}
    (response : ExecutedResponse family state request) : RuntimeEvent :=
  { startDepth := state.journal.absoluteDepth
    endDepth := response.completedJournal.absoluteDepth
    stamp := response.stamp
    readout := response.readout }

def sourceProduction
    {family : ExecutedCauchyFamily P baseDepth}
    {state : Runtime family}
    {precision : Nat}
    {sourceAt : family.SourceAt precision}
    (response : ExecutedResponse family state (.source precision sourceAt)) :
    family.ProducedSourceAt state.journal sourceAt :=
  match response.resource with
  | .source produced => produced

def limitProduction
    {family : ExecutedCauchyFamily P baseDepth}
    {state : Runtime family}
    {precision : Nat}
    (response : ExecutedResponse family state (.limit precision)) :
    ExecutedLimitProduction family state.journal precision :=
  match response.resource with
  | .limit _ produced => produced

/-- A source response completes at the journal owned by its source execution. -/
theorem source_completedJournal
    {family : ExecutedCauchyFamily P baseDepth}
    {state : Runtime family}
    {precision : Nat}
    {sourceAt : family.SourceAt precision}
    (response : ExecutedResponse family state (.source precision sourceAt)) :
    response.completedJournal =
      response.sourceProduction.execution.completedJournal := by
  rcases response with ⟨resource⟩
  cases resource
  rfl

/-- A limit response completes at the journal owned by its grouping execution. -/
theorem limit_completedJournal
    {family : ExecutedCauchyFamily P baseDepth}
    {state : Runtime family}
    {precision : Nat}
    (response : ExecutedResponse family state (.limit precision)) :
    response.completedJournal =
      response.limitProduction.execution.completedJournal := by
  rcases response with ⟨resource⟩
  cases resource
  rfl

theorem source_readout_is_calculated
    {family : ExecutedCauchyFamily P baseDepth}
    {state : Runtime family}
    {precision : Nat}
    {sourceAt : family.SourceAt precision}
    (response : ExecutedResponse family state (.source precision sourceAt)) :
    response.readout = family.producer.calculate sourceAt.request := by
  rcases response with ⟨resource⟩
  cases resource with
  | source produced => exact produced.readout_is_calculated

theorem limit_readout_is_calculated
    {family : ExecutedCauchyFamily P baseDepth}
    {state : Runtime family}
    {precision : Nat}
    (response : ExecutedResponse family state (.limit precision)) :
    response.readout =
      family.producer.calculate (family.diagonalSourceAt precision).request := by
  rcases response with ⟨resource⟩
  cases resource with
  | limit _ produced =>
      change produced.readout = _
      rw [produced.readout_is_source]
      rw [produced.source.readout_is_calculated]
      rw [produced.sourceAtExact]

theorem source_depth
    {family : ExecutedCauchyFamily P baseDepth}
    {state : Runtime family}
    {precision : Nat}
    {sourceAt : family.SourceAt precision}
    (response : ExecutedResponse family state (.source precision sourceAt)) :
    response.completedJournal.absoluteDepth =
      state.journal.absoluteDepth + 6 :=
  by
    rcases response with ⟨resource⟩
    cases resource with
    | source produced => exact produced.completedDepth

theorem limit_depth
    {family : ExecutedCauchyFamily P baseDepth}
    {state : Runtime family}
    {precision : Nat}
    (response : ExecutedResponse family state (.limit precision)) :
    response.completedJournal.absoluteDepth =
      state.journal.absoluteDepth + 12 :=
  by
    rcases response with ⟨resource⟩
    cases resource with
    | limit _ produced => exact produced.completedDepth

def target
    {family : ExecutedCauchyFamily P baseDepth}
    {state : Runtime family} {request : RuntimeRequest family}
    (response : ExecutedResponse family state request) : Option (OwnedTarget family) :=
  match response.resource with
  | .source _ => none
  | .limit _ produced => some (.limit produced)

theorem target_read_exact
    {family : ExecutedCauchyFamily P baseDepth}
    {state : Runtime family} {request : RuntimeRequest family}
    (response : ExecutedResponse family state request) :
    response.target.map OwnedTarget.observation = installedObservation (some response.observation) := by
  rcases response with ⟨resource⟩
  cases resource <;> rfl

end ExecutedResponse

/-- The authoritative state update consumes the exact executed response. -/
private def update
    {family : ExecutedCauchyFamily P baseDepth}
    {state : Runtime family}
    {request : RuntimeRequest family}
    (response : ExecutedResponse family state request) : Runtime family :=
  .mk response.completedJournal
    (state.memory ++ [response.storedResource])
    (some response.observation)
    response.target response.target_read_exact

/-- One authoritative transition retains the response it actually executed. -/
structure ExecutedStep
    (family : ExecutedCauchyFamily P baseDepth)
    (state : Runtime family)
    (request : RuntimeRequest family) where
  private mk ::
  response : ExecutedResponse family state request

namespace ExecutedStep

def next
    {family : ExecutedCauchyFamily P baseDepth}
    {state : Runtime family}
    {request : RuntimeRequest family}
    (step : ExecutedStep family state request) : Runtime family :=
  update step.response

/-- The next state carries the completed journal of the exact retained response. -/
theorem next_journal
    {family : ExecutedCauchyFamily P baseDepth}
    {state : Runtime family}
    {request : RuntimeRequest family}
    (step : ExecutedStep family state request) :
    step.next.journal = step.response.completedJournal :=
  rfl

def event
    {family : ExecutedCauchyFamily P baseDepth}
    {state : Runtime family}
    {request : RuntimeRequest family}
    (step : ExecutedStep family state request) : RuntimeEvent :=
  step.response.event

theorem next_last
    {family : ExecutedCauchyFamily P baseDepth}
    {state : Runtime family}
    {request : RuntimeRequest family}
    (step : ExecutedStep family state request) :
    step.next.last = some step.response.observation :=
  rfl

theorem next_read
    {family : ExecutedCauchyFamily P baseDepth}
    {state : Runtime family}
    {request : RuntimeRequest family}
    (step : ExecutedStep family state request) :
    read step.next = some step.response.observation :=
  rfl

end ExecutedStep

/-- Perform one request once and derive the state update from that same response. -/
def perform
    (family : ExecutedCauchyFamily P baseDepth)
    (state : Runtime family)
    (request : RuntimeRequest family) : ExecutedStep family state request :=
  let response := executeResponse family state request
  .mk response


theorem OwnedTarget.installed
    {family : ExecutedCauchyFamily P baseDepth} :
    (target : OwnedTarget family) -> (code : SignedDyadicCode) ->
      installedObservation (some { stamp := target.stamp, code := code }) =
        some { stamp := target.stamp, code := code }
  | .limit _, _ => rfl
  | .batch _, _ => rfl
  | .rescaled prior _, code => prior.installed code

structure RawSourceStep (family : ExecutedCauchyFamily P baseDepth)
    (state : Runtime family) (request : SourceRequest) where
  private mk ::
  execution : ExecutedRequest (sourceProgram family.producer) P state.journal request

namespace RawSourceStep
def next {family : ExecutedCauchyFamily P baseDepth} {state : Runtime family}
    {request : SourceRequest} (step : RawSourceStep family state request) : Runtime family :=
  .mk step.execution.completedJournal (state.memory ++ [.rawSource step.execution])
    (some { stamp := .source request.term request.precision, code := step.execution.readout })
    none rfl
def event {family : ExecutedCauchyFamily P baseDepth} {state : Runtime family}
    {request : SourceRequest} (step : RawSourceStep family state request) : RuntimeEvent :=
  { startDepth := state.journal.absoluteDepth,
    endDepth := step.execution.completedJournal.absoluteDepth,
    stamp := .source request.term request.precision, readout := step.execution.readout }
theorem readoutExact {family : ExecutedCauchyFamily P baseDepth} {state : Runtime family}
    {request : SourceRequest} (step : RawSourceStep family state request) :
    step.execution.readout = family.producer.calculate request :=
  step.execution.readout_is_storedAction.trans
    (sourceProgram_actionCode_exact family.producer request _ _)
end RawSourceStep

def performRawSource (family : ExecutedCauchyFamily P baseDepth)
    (state : Runtime family) (request : SourceRequest) : RawSourceStep family state request :=
  { execution := execute (sourceProgram family.producer) P state.journal request }

structure GroupingStep (family : ExecutedCauchyFamily P baseDepth)
    (state : Runtime family) (precision : Nat) where
  private mk ::
  size : Nat
  current : Journal P baseDepth
  chain : family.ExecutedSourceChain precision state.journal current size
  grouped : family.ExecutedFiniteGrouping chain

namespace GroupingStep
def next {family : ExecutedCauchyFamily P baseDepth} {state : Runtime family}
    {precision : Nat} (step : GroupingStep family state precision) : Runtime family :=
  let target : OwnedTarget family := .batch step.grouped
  .mk step.grouped.execution.completedJournal (state.memory ++ [.batch step.grouped])
    (some target.observation) (some target) (target.installed target.readout).symm
def event {family : ExecutedCauchyFamily P baseDepth} {state : Runtime family}
    {precision : Nat} (step : GroupingStep family state precision) : RuntimeEvent :=
  { startDepth := state.journal.absoluteDepth,
    endDepth := step.grouped.execution.completedJournal.absoluteDepth,
    stamp := .finiteGrouping precision step.size, readout := step.grouped.readout }
end GroupingStep

/-- The caller supplies only the exact source chain, never a target. -/
def performGrouping (family : ExecutedCauchyFamily P baseDepth)
    (state : Runtime family) {precision : Nat}
    {current : Journal P baseDepth} {size : Nat}
    (chain : family.ExecutedSourceChain precision state.journal current size) :
    GroupingStep family state precision :=
  { size := size, current := current, chain := chain,
    grouped := family.executeFiniteGrouping chain }

structure ContinuedStep (family : ExecutedCauchyFamily P baseDepth)
    (state : Runtime family) (extra : Nat) where
  private mk ::
  target : OwnedTarget family
  installedExact : state.target = some target
  execution : ExecutedRequest (targetContinuationProgram target extra) P state.journal ()

namespace ContinuedStep
def next {family : ExecutedCauchyFamily P baseDepth} {state : Runtime family}
    {extra : Nat} (step : ContinuedStep family state extra) : Runtime family :=
  .mk step.execution.completedJournal
    (state.memory ++ [.continued step.target extra step.execution])
    (some { stamp := step.target.stamp, code := step.execution.readout })
    (some (.rescaled step.target extra)) (by
      rw [targetContinuation_readout]
      exact (step.target.installed (step.target.readout.raise extra)).symm)
def event {family : ExecutedCauchyFamily P baseDepth} {state : Runtime family}
    {extra : Nat} (step : ContinuedStep family state extra) : RuntimeEvent :=
  { startDepth := state.journal.absoluteDepth,
    endDepth := step.execution.completedJournal.absoluteDepth,
    stamp := step.target.stamp, readout := step.execution.readout }
end ContinuedStep

def continueInstalled (family : ExecutedCauchyFamily P baseDepth)
    (state : Runtime family) (extra : Nat) : Option (ContinuedStep family state extra) :=
  match installed : state.target with
  | none => none
  | some target =>
      some {
        target := target
        installedExact := installed
        execution := execute (targetContinuationProgram target extra) P state.journal ()
      }




theorem continueInstalled_none
    (family : ExecutedCauchyFamily P baseDepth) (state : Runtime family) (extra : Nat)
    (empty : continueInstalled family state extra = none) : state.target = none := by
  rcases state with ⟨journal, memory, last, target, targetReadExact⟩
  cases target with
  | none => rfl
  | some target => cases empty


universe uListA uListB

theorem listMapAppend {A : Type uListA} {B : Type uListB} (f : A -> B) (left right : List A) :
    (left ++ right).map f = left.map f ++ right.map f := by
  induction left with
  | nil => rfl
  | cons first remaining ih => exact congrArg (List.cons (f first)) ih

/-- One source plan owns its exact productions; requests are not output codes. -/
structure SourceListExecution (family : ExecutedCauchyFamily P baseDepth)
    {precision : Nat} (start : Journal P baseDepth)
    (sources : List (family.SourceAt precision)) where
  private mk ::
  size : Nat
  current : Journal P baseDepth
  chain : family.ExecutedSourceChain precision start current size
  sizeExact : size = sources.length
  requestsExact :
    chain.records.map (fun record => record.sourceAt.request) =
      sources.map (fun source => source.request)

def executeSourceList (family : ExecutedCauchyFamily P baseDepth)
    {precision : Nat} :
    (start : Journal P baseDepth) -> (sources : List (family.SourceAt precision)) ->
      SourceListExecution family start sources
  | start, [] =>
      { size := 0, current := start, chain := .empty start,
        sizeExact := rfl, requestsExact := rfl }
  | start, source :: remaining =>
      let produced := family.produceSourceAt start source
      let first : family.ExecutedSourceChain precision start produced.completedJournal 1 :=
        .snoc (.empty start) source produced
      let later := executeSourceList family produced.completedJournal remaining
      { size := 1 + later.size
        current := later.current
        chain := ExecutedCauchyFamily.ExecutedSourceChain.concatenate family first later.chain
        sizeExact := by rw [later.sizeExact]; exact Nat.add_comm 1 remaining.length
        requestsExact := by
          rw [ExecutedCauchyFamily.ExecutedSourceChain.concatenate_records]
          rw [listMapAppend, later.requestsExact]
          rfl }

def performSourceListGrouping (family : ExecutedCauchyFamily P baseDepth)
    (state : Runtime family) {precision : Nat}
    (sources : List (family.SourceAt precision)) : GroupingStep family state precision :=
  let built : SourceListExecution family state.journal sources :=
    executeSourceList family state.journal sources
  performGrouping family state (precision := precision)
    (current := built.current) (size := built.size) built.chain


set_option genInjectivity false in
set_option maxHeartbeats 2000000 in
/-- Reachability is generated only by initialization and authoritative steps. -/
inductive Reachable
    (family : ExecutedCauchyFamily P baseDepth) : Runtime family -> Type
  | initial : Reachable family (initialState family)
  | performed
      {state : Runtime family}
      (reachable : Reachable family state)
      {request : RuntimeRequest family}
      (step : ExecutedStep family state request) :
      Reachable family step.next
  | rawSource {state : Runtime family} (reachable : Reachable family state)
      {request : SourceRequest} (step : RawSourceStep family state request) :
      Reachable family step.next
  | grouped {state : Runtime family} (reachable : Reachable family state)
      {precision : Nat} (step : GroupingStep family state precision) :
      Reachable family step.next
  | continued {state : Runtime family} (reachable : Reachable family state)
      {extra : Nat} (step : ContinuedStep family state extra) :
      Reachable family step.next

/--
A relational real whose primitive productions are authoritative runtime steps
from reachable rich states.  The coherence and convergence fields consume the
responses owned by those steps; no journal-only producer can inhabit this
terminal interface.
-/
structure RuntimeProducedRelationalReal
    (family : ExecutedCauchyFamily P baseDepth) where
  produce : (state : Runtime family) -> Reachable family state ->
    (precision : Nat) -> ExecutedStep family state (.limit precision)
  produceCanonical : (state : Runtime family) ->
    (reachable : Reachable family state) -> (precision : Nat) ->
      produce state reachable precision = perform family state (.limit precision)
  coherent :
    (precision : Nat) ->
    (firstState secondState : Runtime family) ->
    (firstReachable : Reachable family firstState) ->
    (secondReachable : Reachable family secondState) ->
      Near precision
        (produce firstState firstReachable precision).response.readout
        (produce secondState secondReachable (Nat.succ precision)).response.readout
  sourceNear :
    (precision : Nat) ->
    {sourceState limitState : Runtime family} ->
    (sourceReachable : Reachable family sourceState) ->
    (sourceAt : family.SourceAt precision) ->
    (sourceStep : ExecutedStep family sourceState (.source precision sourceAt)) ->
    (limitReachable : Reachable family limitState) ->
      Near precision sourceStep.response.readout
        (produce limitState limitReachable precision).response.readout

namespace ExecutedCauchyFamily

private def precisionSuccExtension (precision : Nat) :
    PrecisionExtension precision (Nat.succ precision) :=
  { extra := 1, exact := rfl }

/-- Sequential completeness produced only through authoritative runtime steps. -/
def completeViaRuntime
    (family : ExecutedCauchyFamily P baseDepth) :
    RuntimeProducedRelationalReal family where
  produce := fun state _reachable precision =>
    perform family state (.limit precision)
  produceCanonical := fun _state _reachable _precision => rfl
  coherent := by
    intro precision firstState secondState firstReachable secondReachable
    let first := perform family firstState (.limit precision)
    let second := perform family secondState (.limit (Nat.succ precision))
    let firstProduction := first.response.limitProduction
    let secondProduction := second.response.limitProduction
    change Near precision firstProduction.readout secondProduction.readout
    rw [firstProduction.readout_is_source, secondProduction.readout_is_source]
    exact family.cauchy precision
      firstProduction.sourceAt.request secondProduction.sourceAt.request
      (by rw [firstProduction.sourceAtExact]; exact PrecisionExtension.refl _)
      (by
        rw [secondProduction.sourceAtExact]
        exact family.modulusMonotone (precisionSuccExtension precision))
      (by rw [firstProduction.sourceAtExact]; exact PrecisionExtension.refl _)
      (by
        rw [secondProduction.sourceAtExact]
        exact precisionSuccExtension precision)
      firstProduction.source.execution secondProduction.source.execution
  sourceNear := by
    intro precision sourceState limitState sourceReachable sourceAt sourceStep
      limitReachable
    rcases sourceStep with ⟨sourceResponse⟩
    rcases sourceResponse with ⟨sourceResource⟩
    cases sourceResource with
    | source source =>
        let limit :=
          (perform family limitState (.limit precision)).response.limitProduction
        change Near precision source.readout limit.readout
        rw [limit.readout_is_source]
        exact family.cauchy precision
          sourceAt.request limit.sourceAt.request
          sourceAt.indexBeyondModulus
          (by rw [limit.sourceAtExact]; exact PrecisionExtension.refl _)
          sourceAt.readoutRefines
          (by rw [limit.sourceAtExact]; exact PrecisionExtension.refl _)
          source.execution limit.source.execution

end ExecutedCauchyFamily

inductive RunTrace
    (family : ExecutedCauchyFamily P baseDepth) :
    (state : Runtime family) -> List (RuntimeRequest family) ->
      Runtime family -> Type
  | done (state : Runtime family) : RunTrace family state [] state
  | step
      {state finalState : Runtime family}
      {request : RuntimeRequest family}
      {remaining : List (RuntimeRequest family)}
      (executed : ExecutedStep family state request)
      (later : RunTrace family executed.next remaining finalState) :
      RunTrace family state (request :: remaining) finalState

/-- Transport reachability through the exact stored trace. -/
private def RunTrace.finalReachable
    {family : ExecutedCauchyFamily P baseDepth} :
    {state : Runtime family} ->
    {requests : List (RuntimeRequest family)} ->
    {finalState : Runtime family} ->
    RunTrace family state requests finalState ->
    Reachable family state -> Reachable family finalState
  | _, [], _, trace, reachable => by
      cases trace
      exact reachable
  | _, _ :: _, _, trace, reachable => by
      cases trace with
      | step executed later =>
          exact later.finalReachable (.performed reachable executed)

/-- A run retains every exact step and its exact final state. -/
structure ExecutedRun
    (family : ExecutedCauchyFamily P baseDepth)
    (state : Runtime family)
    (requests : List (RuntimeRequest family)) where
  private mk ::
  finalState : Runtime family
  private trace : RunTrace family state requests finalState

/-- Execute a list by reusing each step's actual next state. -/
def run
    (family : ExecutedCauchyFamily P baseDepth) :
    (state : Runtime family) ->
    (requests : List (RuntimeRequest family)) ->
      ExecutedRun family state requests
  | state, [] => .mk state (.done state)
  | state, request :: remaining =>
      let executed := perform family state request
      let later := run family executed.next remaining
      .mk later.finalState (.step executed later.trace)

namespace ExecutedRun

/-- Exact public trace evidence; the run constructor itself remains private. -/
def traceEvidence
    {family : ExecutedCauchyFamily P baseDepth}
    {state : Runtime family}
    {requests : List (RuntimeRequest family)}
    (executed : ExecutedRun family state requests) :
    RunTrace family state requests executed.finalState :=
  executed.trace

def firstStep
    {family : ExecutedCauchyFamily P baseDepth}
    {state : Runtime family}
    {request : RuntimeRequest family}
    {remaining : List (RuntimeRequest family)}
    (executed : ExecutedRun family state (request :: remaining)) :
    ExecutedStep family state request :=
  match executed.trace with
  | .step step _ => step

/-- A singleton run built from the already executed authoritative step. -/
def singleton
    {family : ExecutedCauchyFamily P baseDepth}
    {state : Runtime family}
    {request : RuntimeRequest family}
    (step : ExecutedStep family state request) :
    ExecutedRun family state [request] :=
  .mk step.next (.step step (.done step.next))

/-- Reachability transported through the exact retained trace, without replay. -/
def finalReachable
    {family : ExecutedCauchyFamily P baseDepth}
    {state : Runtime family}
    {requests : List (RuntimeRequest family)}
    (executed : ExecutedRun family state requests)
    (reachable : Reachable family state) :
    Reachable family executed.finalState :=
  executed.trace.finalReachable reachable

end ExecutedRun

/-! ## Reduced specification and exact refinement -/

structure ReducedState where
  depth : Nat
  last : Option Observation

theorem ReducedState.extensionality
    (first second : ReducedState)
    (depthExact : first.depth = second.depth)
    (lastExact : first.last = second.last) : first = second := by
  cases first
  cases second
  cases depthExact
  cases lastExact
  rfl

def project
    {family : ExecutedCauchyFamily P baseDepth}
    (state : Runtime family) : ReducedState :=
  { depth := state.journal.absoluteDepth, last := state.last }

def expectedStamp
    {family : ExecutedCauchyFamily P baseDepth} :
    RuntimeRequest family -> RequestStamp
  | .source _ sourceAt =>
      .source sourceAt.request.term sourceAt.request.precision
  | .limit precision => .limit precision

def expectedCode
    {family : ExecutedCauchyFamily P baseDepth} :
    RuntimeRequest family -> SignedDyadicCode
  | .source _ sourceAt => family.producer.calculate sourceAt.request
  | .limit precision =>
      family.producer.calculate (family.diagonalSourceAt precision).request

def requestCost
    {family : ExecutedCauchyFamily P baseDepth} :
    RuntimeRequest family -> Nat
  | .source _ _ => 6
  | .limit _ => 12

/-- Contract-level transition; it specifies but never constructs rich resources. -/
def reducedNext
    {family : ExecutedCauchyFamily P baseDepth}
    (state : ReducedState)
    (request : RuntimeRequest family) : ReducedState :=
  { depth := state.depth + requestCost request
    last := some { stamp := expectedStamp request, code := expectedCode request } }

def reducedRun
    {family : ExecutedCauchyFamily P baseDepth} :
    ReducedState -> List (RuntimeRequest family) -> ReducedState
  | state, [] => state
  | state, request :: remaining =>
      reducedRun (reducedNext state request) remaining

theorem perform_projects
    (family : ExecutedCauchyFamily P baseDepth)
    (state : Runtime family)
    (request : RuntimeRequest family) :
    project (perform family state request).next =
      reducedNext (project state) request := by
  cases request with
  | source precision sourceAt =>
      apply ReducedState.extensionality
      · exact (perform family state (.source precision sourceAt)).response.source_depth
      · apply congrArg some
        apply Observation.extensionality
        · rfl
        · exact (perform family state (.source precision sourceAt)).response.source_readout_is_calculated
  | limit precision =>
      apply ReducedState.extensionality
      · exact (perform family state (.limit precision)).response.limit_depth
      · apply congrArg some
        apply Observation.extensionality
        · rfl
        · exact (perform family state (.limit precision)).response.limit_readout_is_calculated

theorem run_projects
    (family : ExecutedCauchyFamily P baseDepth)
    (state : Runtime family)
    (requests : List (RuntimeRequest family)) :
    project (run family state requests).finalState =
      reducedRun (project state) requests := by
  induction requests generalizing state with
  | nil => rfl
  | cons request remaining inductionHypothesis =>
      change project (run family (perform family state request).next remaining).finalState = _
      rw [inductionHypothesis]
      rw [perform_projects]
      rfl

/--
The reduced future forgets rich resources only under its explicit projection:
two reachable rich states with the same reduced state have the same projected
future for the same request list.  Their journals and stored resources are not
identified.
-/
theorem run_projects_of_project_eq
    (family : ExecutedCauchyFamily P baseDepth)
    (first second : Runtime family)
    (_firstReachable : Reachable family first)
    (_secondReachable : Reachable family second)
    (projectExact : project first = project second)
    (requests : List (RuntimeRequest family)) :
    project (run family first requests).finalState =
      project (run family second requests).finalState := by
  rw [run_projects, run_projects, projectExact]

/-! ## Common public language and the exact live-memory contract -/

/--
One request language shared by all runtime reals.  A source request selects the
canonical executed source of the received family; no family-indexed certificate
or proposed output appears in the public input.
-/
inductive CommonRequest : Type
  | source (precision : Nat)
  | limit (precision : Nat)
  | unsupported (stamp : RequestStamp)

/-- Events expose execution or an explicit refusal without forging a resource. -/
inductive CommonEvent : Type
  | executed (event : RuntimeEvent)
  | refused (depth : Nat) (stamp : RequestStamp)

def CommonAllow : CommonRequest -> Type
  | .source _ => Unit
  | .limit _ => Unit
  | .unsupported _ => Empty

def commonDecision (request : CommonRequest) :
    PSum (CommonAllow request) (CommonAllow request -> False) :=
  match request with
  | .source _ => .inl ()
  | .limit _ => .inl ()
  | .unsupported _ => .inr (fun impossible => nomatch impossible)

/-- Interpret a common request inside one received family. -/
def interpret
    (family : ExecutedCauchyFamily P baseDepth) :
    CommonRequest -> Option (RuntimeRequest family)
  | .source precision =>
      some (.source precision (family.diagonalSourceAt precision))
  | .limit precision => some (.limit precision)
  | .unsupported _ => none

/--
Execute a common request once.  Refusal preserves the exact state, so the next
request is still executed from the same memory.
-/
def performCommon
    (family : ExecutedCauchyFamily P baseDepth)
    (state : Runtime family) :
    CommonRequest -> Runtime family × CommonEvent
  | .source precision =>
      let step := perform family state
        (.source precision (family.diagonalSourceAt precision))
      (step.next, .executed step.event)
  | .limit precision =>
      let step := perform family state (.limit precision)
      (step.next, .executed step.event)
  | .unsupported stamp =>
      (state, .refused state.journal.absoluteDepth stamp)

/-- Complete future contract: admission, event, observation and continuation. -/
def futureContract
    (family : ExecutedCauchyFamily P baseDepth) :
    FutureContract (Runtime family) CommonRequest CommonEvent
      (Option Observation) where
  next state request := (performCommon family state request).1
  event state request := (performCommon family state request).2
  read := read
  Allow _state request := CommonAllow request
  decision _state request := commonDecision request

/-- Executable future path sharing the single transition returned at each step. -/
def runCommon
    (family : ExecutedCauchyFamily P baseDepth) :
    Runtime family -> List CommonRequest -> Outcome CommonEvent (Option Observation)
  | state, [] => .stop (read state)
  | state, request :: remaining =>
      let transition := performCommon family state request
      .step (read state) ((futureContract family).enabled state request)
        transition.2 (runCommon family transition.1 remaining)

theorem runCommon_contract_exact
    (family : ExecutedCauchyFamily P baseDepth)
    (state : Runtime family)
    (requests : List CommonRequest) :
    runCommon family state requests =
      (futureContract family).outcome state requests := by
  induction requests generalizing state with
  | nil => rfl
  | cons request remaining inductionHypothesis =>
      change Outcome.step _ _ _ (runCommon family _ remaining) =
        Outcome.step _ _ _ ((futureContract family).outcome _ remaining)
      rw [inductionHypothesis]
      rfl

def reducedCommonNext
    (family : ExecutedCauchyFamily P baseDepth)
    (state : ReducedState) : CommonRequest -> ReducedState
  | .source precision =>
      reducedNext (family := family) state
        (.source precision (family.diagonalSourceAt precision))
  | .limit precision =>
      reducedNext (family := family) state (.limit precision)
  | .unsupported _ => state

def reducedCommonEvent
    (family : ExecutedCauchyFamily P baseDepth)
    (state : ReducedState) : CommonRequest -> CommonEvent
  | .source precision =>
      let request : RuntimeRequest family :=
        .source precision (family.diagonalSourceAt precision)
      .executed
        { startDepth := state.depth
          endDepth := state.depth + requestCost request
          stamp := expectedStamp request
          readout := expectedCode request }
  | .limit precision =>
      let request : RuntimeRequest family := .limit precision
      .executed
        { startDepth := state.depth
          endDepth := state.depth + requestCost request
          stamp := expectedStamp request
          readout := expectedCode request }
  | .unsupported stamp => .refused state.depth stamp

/-- The directly executed memory, distinct from the rich execution archive. -/
abbrev LiveRuntime := ReducedState

def initializeLive
    (family : ExecutedCauchyFamily P baseDepth) : LiveRuntime :=
  project (initialState family)

def readLive (state : LiveRuntime) : Option Observation :=
  state.last

/--
One live transition computes exactly the next memory and event.  The caller
binds this pair once; no source archive is replayed and refusal preserves the
same memory.
-/
def performLive
    (family : ExecutedCauchyFamily P baseDepth)
    (state : LiveRuntime) : CommonRequest -> LiveRuntime × CommonEvent
  | .source precision =>
      let request : RuntimeRequest family :=
        .source precision (family.diagonalSourceAt precision)
      let observation : Observation :=
        { stamp := expectedStamp request, code := expectedCode request }
      let event : RuntimeEvent :=
        { startDepth := state.depth
          endDepth := state.depth + requestCost request
          stamp := observation.stamp
          readout := observation.code }
      ({ depth := event.endDepth, last := some observation }, .executed event)
  | .limit precision =>
      let request : RuntimeRequest family := .limit precision
      let observation : Observation :=
        { stamp := expectedStamp request, code := expectedCode request }
      let event : RuntimeEvent :=
        { startDepth := state.depth
          endDepth := state.depth + requestCost request
          stamp := observation.stamp
          readout := observation.code }
      ({ depth := event.endDepth, last := some observation }, .executed event)
  | .unsupported stamp =>
      (state, .refused state.depth stamp)

theorem performLive_next_exact
    (family : ExecutedCauchyFamily P baseDepth)
    (state : LiveRuntime)
    (request : CommonRequest) :
    (performLive family state request).1 =
      reducedCommonNext family state request := by
  cases request <;> rfl

theorem performLive_event_exact
    (family : ExecutedCauchyFamily P baseDepth)
    (state : LiveRuntime)
    (request : CommonRequest) :
    (performLive family state request).2 =
      reducedCommonEvent family state request := by
  cases request <;> rfl

/-- The live runtime contains exactly the state read by the public contract. -/
def liveContract
    (family : ExecutedCauchyFamily P baseDepth) :
    FutureContract LiveRuntime CommonRequest CommonEvent
      (Option Observation) where
  next state request := (performLive family state request).1
  event state request := (performLive family state request).2
  read := readLive
  Allow _state request := CommonAllow request
  decision _state request := commonDecision request

/-- Backward-compatible name for the public live-memory contract. -/
def reducedFutureContract
    (family : ExecutedCauchyFamily P baseDepth) :
    FutureContract LiveRuntime CommonRequest CommonEvent
      (Option Observation) :=
  liveContract family

/-- Direct finite execution over exactly the live memory. -/
def runLive
    (family : ExecutedCauchyFamily P baseDepth) :
    LiveRuntime -> List CommonRequest -> Outcome CommonEvent (Option Observation)
  | state, [] => .stop (readLive state)
  | state, request :: remaining =>
      let transition := performLive family state request
      .step (readLive state) ((liveContract family).enabled state request)
        transition.2 (runLive family transition.1 remaining)

theorem runLive_contract_exact
    (family : ExecutedCauchyFamily P baseDepth)
    (state : LiveRuntime)
    (requests : List CommonRequest) :
    runLive family state requests =
      (liveContract family).outcome state requests := by
  induction requests generalizing state with
  | nil => rfl
  | cons request remaining inductionHypothesis =>
      change Outcome.step _ _ _ (runLive family _ remaining) =
        Outcome.step _ _ _ ((liveContract family).outcome _ remaining)
      rw [inductionHypothesis]
      rfl

theorem performCommon_projects
    (family : ExecutedCauchyFamily P baseDepth)
    (state : Runtime family)
    (request : CommonRequest) :
    project (performCommon family state request).1 =
      (performLive family (project state) request).1 := by
  rw [performLive_next_exact]
  cases request with
  | source precision =>
      change project
          (perform family state
            (.source precision (family.diagonalSourceAt precision))).next =
        reducedNext (family := family) (project state)
          (.source precision (family.diagonalSourceAt precision))
      exact perform_projects family state
        (.source precision (family.diagonalSourceAt precision))
  | limit precision =>
      change project (perform family state (.limit precision)).next =
        reducedNext (family := family) (project state) (.limit precision)
      exact perform_projects family state (.limit precision)
  | unsupported stamp =>
      change project state = project state
      rfl

theorem performCommon_event_projects
    (family : ExecutedCauchyFamily P baseDepth)
    (state : Runtime family)
    (request : CommonRequest) :
    (performCommon family state request).2 =
      (performLive family (project state) request).2 := by
  rw [performLive_event_exact]
  cases request with
  | source precision =>
      apply congrArg CommonEvent.executed
      apply RuntimeEvent.extensionality
      · rfl
      · exact (perform family state
          (.source precision (family.diagonalSourceAt precision))).response.source_depth
      · rfl
      · exact (perform family state
          (.source precision (family.diagonalSourceAt precision))).response.source_readout_is_calculated
  | limit precision =>
      apply congrArg CommonEvent.executed
      apply RuntimeEvent.extensionality
      · rfl
      · exact (perform family state (.limit precision)).response.limit_depth
      · rfl
      · exact (perform family state (.limit precision)).response.limit_readout_is_calculated
  | unsupported stamp => rfl

/-- Exact realization of the rich history by the directly executed live state. -/
def runtimeRealization
    (family : ExecutedCauchyFamily P baseDepth) :
    ExactRealization (futureContract family) ReducedState where
  reduced := liveContract family
  project := project
  forward := by
    intro _state request witness
    cases request <;> exact witness
  backward := by
    intro _state request witness
    cases request <;> exact witness
  backward_forward := by
    intro _state request witness
    cases request <;> cases witness <;> rfl
  forward_backward := by
    intro _state request witness
    cases request <;> cases witness <;> rfl
  next_exact := performCommon_projects family
  event_exact := performCommon_event_projects family
  read_exact := fun _state => rfl

private def outcomeStartDepth :
    Outcome CommonEvent (Option Observation) -> Nat
  | .stop _ => 0
  | .step _ _ (.executed event) _ => event.startDepth
  | .step _ _ (.refused depth _) _ => depth

/--
SAT-style bilateral characterization: equal live memory is equivalent to equal
behavior for every finite future of the complete contract.
-/
theorem minimality
    (family : ExecutedCauchyFamily P baseDepth)
    {first second : Runtime family} :
    project first = project second ↔
      FutureEquivalent (futureContract family) first second := by
  constructor
  · intro same
    exact (runtimeRealization family).equal_memory_same_futures same
  · intro same
    apply ReducedState.extensionality
    · have depthExact := congrArg outcomeStartDepth
        (same [CommonRequest.limit 0])
      exact depthExact
    · exact same.read

/-- Equality of live memory is exactly equality of all of its finite futures. -/
theorem liveMinimality
    (family : ExecutedCauchyFamily P baseDepth)
    {first second : LiveRuntime} :
    first = second ↔ FutureEquivalent (liveContract family) first second := by
  constructor
  · intro same requests
    exact congrArg (fun state => (liveContract family).outcome state requests) same
  · intro same
    apply ReducedState.extensionality
    · have depthExact := congrArg outcomeStartDepth
        (same [CommonRequest.limit 0])
      exact depthExact
    · exact same.read

/-- Any exact implementation of the live contract must retain its distinctions. -/
theorem any_live_realization
    (family : ExecutedCauchyFamily P baseDepth)
    {Other : Type}
    (other : ExactRealization (liveContract family) Other)
    {first second : LiveRuntime}
    (same : other.project first = other.project second) :
    first = second :=
  (liveMinimality family).2 (other.equal_memory_same_futures same)

/-- Every exact realization of the same futures must retain live distinctions. -/
theorem any_realization
    (family : ExecutedCauchyFamily P baseDepth)
    {Other : Type}
    (other : ExactRealization (futureContract family) Other)
    {first second : Runtime family}
    (same : other.project first = other.project second) :
    project first = project second :=
  (minimality family).2 (other.equal_memory_same_futures same)

theorem refusal_continues
    (family : ExecutedCauchyFamily P baseDepth)
    (state : Runtime family)
    (stamp : RequestStamp)
    (remaining : List CommonRequest) :
    runCommon family state (.unsupported stamp :: remaining) =
      .step (read state) false
        (.refused state.journal.absoluteDepth stamp)
        (runCommon family state remaining) := by
  change Outcome.step (read state) false
      (.refused state.journal.absoluteDepth stamp)
      (runCommon family state remaining) = _
  rfl

/-! ## One common carrier for comparing runtime-real behaviors -/

structure RuntimeCarrier (P : CircularPresentation) (baseDepth : Nat) where
  family : ExecutedCauchyFamily P baseDepth
  state : Runtime family

def RuntimeCarrier.initial
    (family : ExecutedCauchyFamily P baseDepth) : RuntimeCarrier P baseDepth :=
  { family := family, state := initialState family }

def performCarrier
    (carrier : RuntimeCarrier P baseDepth)
    (request : CommonRequest) : RuntimeCarrier P baseDepth × CommonEvent :=
  let transition := performCommon carrier.family carrier.state request
  ({ family := carrier.family, state := transition.1 }, transition.2)

def carrierContract (P : CircularPresentation) (baseDepth : Nat) :
    FutureContract (RuntimeCarrier P baseDepth) CommonRequest CommonEvent
      (Option Observation) where
  next carrier request := (performCarrier carrier request).1
  event carrier request := (performCarrier carrier request).2
  read carrier := read carrier.state
  Allow _carrier request := CommonAllow request
  decision _carrier request := commonDecision request


/-! ## Full typed futures: no restriction to diagonal source requests -/

def typedContract (family : ExecutedCauchyFamily P baseDepth) :
    FutureContract (Runtime family) (RuntimeRequest family) RuntimeEvent
      (Option Observation) where
  next state request := (perform family state request).next
  event state request := (perform family state request).event
  read := read
  Allow _state _request := Unit
  decision _state _request := .inl ()

def typedReducedEvent
    (family : ExecutedCauchyFamily P baseDepth)
    (state : ReducedState) (request : RuntimeRequest family) : RuntimeEvent where
  startDepth := state.depth
  endDepth := state.depth + requestCost request
  stamp := expectedStamp request
  readout := expectedCode request

def typedReducedContract (family : ExecutedCauchyFamily P baseDepth) :
    FutureContract ReducedState (RuntimeRequest family) RuntimeEvent
      (Option Observation) where
  next := reducedNext
  event := typedReducedEvent family
  read := fun state => state.last
  Allow _state _request := Unit
  decision _state _request := .inl ()

theorem perform_event_projects
    (family : ExecutedCauchyFamily P baseDepth)
    (state : Runtime family) (request : RuntimeRequest family) :
    (perform family state request).event =
      typedReducedEvent family (project state) request := by
  cases request with
  | source precision sourceAt =>
      apply RuntimeEvent.extensionality
      · rfl
      · exact (perform family state (.source precision sourceAt)).response.source_depth
      · rfl
      · exact (perform family state (.source precision sourceAt)).response.source_readout_is_calculated
  | limit precision =>
      apply RuntimeEvent.extensionality
      · rfl
      · exact (perform family state (.limit precision)).response.limit_depth
      · rfl
      · exact (perform family state (.limit precision)).response.limit_readout_is_calculated

/-- All typed source/limit requests, including non-diagonal sources. -/
def typedRealization (family : ExecutedCauchyFamily P baseDepth) :
    ExactRealization (typedContract family) ReducedState where
  reduced := typedReducedContract family
  project := project
  forward := fun _state _request witness => witness
  backward := fun _state _request witness => witness
  backward_forward := fun _state _request _witness => rfl
  forward_backward := fun _state _request _witness => rfl
  next_exact := perform_projects family
  event_exact := perform_event_projects family
  read_exact := fun _state => rfl

/-- Full event and observation laws use the same retained authoritative steps. -/
def typedBridge (family : ExecutedCauchyFamily P baseDepth) :=
  (typedRealization family).continuationBridge

def admitAllTyped (family : ExecutedCauchyFamily P baseDepth) :
    (state : Runtime family) -> (requests : List (RuntimeRequest family)) ->
      ConstitutiveSearch.Grouping.Continuation.Admitted
        (typedContract family).next (typedContract family).Allow state requests
  | state, [] => .nil state
  | state, request :: remaining =>
      .cons () (admitAllTyped family (perform family state request).next remaining)

theorem typedOutcomes_exact (family : ExecutedCauchyFamily P baseDepth)
    (state : Runtime family) (requests : List (RuntimeRequest family)) :
    (typedContract family).outcome state requests =
      (typedReducedContract family).outcome (project state) requests :=
  (typedRealization family).outcome_exact state requests

theorem typedEvents_exact (family : ExecutedCauchyFamily P baseDepth)
    (state : Runtime family) (requests : List (RuntimeRequest family)) :
    ConstitutiveSearch.Grouping.Continuation.events
        (typedContract family).next (typedContract family).event state requests =
      ConstitutiveSearch.Grouping.Continuation.events
        (typedReducedContract family).next (typedReducedContract family).event
        (project state) requests :=
  (typedBridge family).events_exact state requests

theorem typedObservations_exact (family : ExecutedCauchyFamily P baseDepth)
    (state : Runtime family) (requests : List (RuntimeRequest family)) :
    ConstitutiveSearch.Grouping.Continuation.observations
        (typedContract family).next (typedContract family).read state requests =
      ConstitutiveSearch.Grouping.Continuation.observations
        (typedReducedContract family).next (typedReducedContract family).read
        (project state) requests :=
  (typedBridge family).observations_exact state requests

theorem sameTypedFuture (family : ExecutedCauchyFamily P baseDepth)
    {first second : Runtime family} (same : project first = project second) :
    FutureEquivalent (typedContract family) first second :=
  (typedRealization family).equal_memory_same_futures same

/-- One generic completeness master, independent of a Gödel-specific Result. -/
structure GenericCompleteness (family : ExecutedCauchyFamily P baseDepth) where
  terms : (term : Nat) -> family.TermModel term
  termsExact : (term : Nat) -> terms term = family.termModel term
  produced : RuntimeProducedRelationalReal family
  producedExact : produced = ExecutedCauchyFamily.completeViaRuntime family
  realization : ExactRealization (typedContract family) ReducedState
  realizationExact : realization = typedRealization family
  groupFinite :
    {precision : Nat} -> {start current : Journal P baseDepth} -> {size : Nat} ->
      (chain : family.ExecutedSourceChain precision start current size) ->
        family.ExecutedFiniteGrouping chain
  groupFiniteExact :
    {precision : Nat} -> {start current : Journal P baseDepth} -> {size : Nat} ->
      (chain : family.ExecutedSourceChain precision start current size) ->
        groupFinite chain = family.executeFiniteGrouping chain

def completeGeneric (family : ExecutedCauchyFamily P baseDepth) :
    GenericCompleteness family where
  terms := family.termModel
  termsExact := fun _term => rfl
  produced := ExecutedCauchyFamily.completeViaRuntime family
  producedExact := rfl
  realization := typedRealization family
  realizationExact := rfl
  groupFinite := family.executeFiniteGrouping
  groupFiniteExact := fun _chain => rfl


end RelationalPerimeter.Constitution.Reals.AuthoritativeRuntime

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Constitution.Reals.AuthoritativeRuntime.RuntimeRequest
#print axioms RelationalPerimeter.Constitution.Reals.AuthoritativeRuntime.Observation
#print axioms RelationalPerimeter.Constitution.Reals.AuthoritativeRuntime.RuntimeEvent
#print axioms RelationalPerimeter.Constitution.Reals.AuthoritativeRuntime.RuntimeEvent.extensionality
#print axioms RelationalPerimeter.Constitution.Reals.AuthoritativeRuntime.StoredResource
#print axioms RelationalPerimeter.Constitution.Reals.AuthoritativeRuntime.Runtime
#print axioms RelationalPerimeter.Constitution.Reals.AuthoritativeRuntime.initialState
#print axioms RelationalPerimeter.Constitution.Reals.AuthoritativeRuntime.read
#print axioms RelationalPerimeter.Constitution.Reals.AuthoritativeRuntime.ExecutedResponse
#print axioms RelationalPerimeter.Constitution.Reals.AuthoritativeRuntime.executeResponse
#print axioms RelationalPerimeter.Constitution.Reals.AuthoritativeRuntime.ExecutedResponse.readout
#print axioms RelationalPerimeter.Constitution.Reals.AuthoritativeRuntime.ExecutedResponse.limit_stamp
#print axioms RelationalPerimeter.Constitution.Reals.AuthoritativeRuntime.ExecutedResponse.source_readout_is_calculated
#print axioms RelationalPerimeter.Constitution.Reals.AuthoritativeRuntime.ExecutedResponse.limit_readout_is_calculated
#print axioms RelationalPerimeter.Constitution.Reals.AuthoritativeRuntime.ExecutedResponse.source_completedJournal
#print axioms RelationalPerimeter.Constitution.Reals.AuthoritativeRuntime.ExecutedResponse.limit_completedJournal
#print axioms RelationalPerimeter.Constitution.Reals.AuthoritativeRuntime.ExecutedStep
#print axioms RelationalPerimeter.Constitution.Reals.AuthoritativeRuntime.perform
#print axioms RelationalPerimeter.Constitution.Reals.AuthoritativeRuntime.ExecutedStep.next_journal
#print axioms RelationalPerimeter.Constitution.Reals.AuthoritativeRuntime.ExecutedStep.next_read
#print axioms RelationalPerimeter.Constitution.Reals.AuthoritativeRuntime.Reachable
#print axioms RelationalPerimeter.Constitution.Reals.AuthoritativeRuntime.RuntimeProducedRelationalReal
#print axioms RelationalPerimeter.Constitution.Reals.AuthoritativeRuntime.ExecutedCauchyFamily.completeViaRuntime
#print axioms RelationalPerimeter.Constitution.Reals.AuthoritativeRuntime.ExecutedRun
#print axioms RelationalPerimeter.Constitution.Reals.AuthoritativeRuntime.RunTrace
#print axioms RelationalPerimeter.Constitution.Reals.AuthoritativeRuntime.run
#print axioms RelationalPerimeter.Constitution.Reals.AuthoritativeRuntime.ExecutedRun.traceEvidence
#print axioms RelationalPerimeter.Constitution.Reals.AuthoritativeRuntime.ExecutedRun.singleton
#print axioms RelationalPerimeter.Constitution.Reals.AuthoritativeRuntime.ExecutedRun.finalReachable
#print axioms RelationalPerimeter.Constitution.Reals.AuthoritativeRuntime.ReducedState
#print axioms RelationalPerimeter.Constitution.Reals.AuthoritativeRuntime.reducedNext
#print axioms RelationalPerimeter.Constitution.Reals.AuthoritativeRuntime.perform_projects
#print axioms RelationalPerimeter.Constitution.Reals.AuthoritativeRuntime.run_projects
#print axioms RelationalPerimeter.Constitution.Reals.AuthoritativeRuntime.run_projects_of_project_eq
#print axioms RelationalPerimeter.Constitution.Reals.AuthoritativeRuntime.CommonRequest
#print axioms RelationalPerimeter.Constitution.Reals.AuthoritativeRuntime.CommonEvent
#print axioms RelationalPerimeter.Constitution.Reals.AuthoritativeRuntime.CommonAllow
#print axioms RelationalPerimeter.Constitution.Reals.AuthoritativeRuntime.commonDecision
#print axioms RelationalPerimeter.Constitution.Reals.AuthoritativeRuntime.interpret
#print axioms RelationalPerimeter.Constitution.Reals.AuthoritativeRuntime.performCommon
#print axioms RelationalPerimeter.Constitution.Reals.AuthoritativeRuntime.futureContract
#print axioms RelationalPerimeter.Constitution.Reals.AuthoritativeRuntime.runCommon
#print axioms RelationalPerimeter.Constitution.Reals.AuthoritativeRuntime.runCommon_contract_exact
#print axioms RelationalPerimeter.Constitution.Reals.AuthoritativeRuntime.reducedCommonNext
#print axioms RelationalPerimeter.Constitution.Reals.AuthoritativeRuntime.reducedCommonEvent
#print axioms RelationalPerimeter.Constitution.Reals.AuthoritativeRuntime.LiveRuntime
#print axioms RelationalPerimeter.Constitution.Reals.AuthoritativeRuntime.initializeLive
#print axioms RelationalPerimeter.Constitution.Reals.AuthoritativeRuntime.readLive
#print axioms RelationalPerimeter.Constitution.Reals.AuthoritativeRuntime.performLive
#print axioms RelationalPerimeter.Constitution.Reals.AuthoritativeRuntime.performLive_next_exact
#print axioms RelationalPerimeter.Constitution.Reals.AuthoritativeRuntime.performLive_event_exact
#print axioms RelationalPerimeter.Constitution.Reals.AuthoritativeRuntime.liveContract
#print axioms RelationalPerimeter.Constitution.Reals.AuthoritativeRuntime.reducedFutureContract
#print axioms RelationalPerimeter.Constitution.Reals.AuthoritativeRuntime.runLive
#print axioms RelationalPerimeter.Constitution.Reals.AuthoritativeRuntime.runLive_contract_exact
#print axioms RelationalPerimeter.Constitution.Reals.AuthoritativeRuntime.performCommon_projects
#print axioms RelationalPerimeter.Constitution.Reals.AuthoritativeRuntime.performCommon_event_projects
#print axioms RelationalPerimeter.Constitution.Reals.AuthoritativeRuntime.runtimeRealization
#print axioms RelationalPerimeter.Constitution.Reals.AuthoritativeRuntime.minimality
#print axioms RelationalPerimeter.Constitution.Reals.AuthoritativeRuntime.liveMinimality
#print axioms RelationalPerimeter.Constitution.Reals.AuthoritativeRuntime.any_realization
#print axioms RelationalPerimeter.Constitution.Reals.AuthoritativeRuntime.any_live_realization
#print axioms RelationalPerimeter.Constitution.Reals.AuthoritativeRuntime.refusal_continues
#print axioms RelationalPerimeter.Constitution.Reals.AuthoritativeRuntime.RuntimeCarrier
#print axioms RelationalPerimeter.Constitution.Reals.AuthoritativeRuntime.RuntimeCarrier.initial
#print axioms RelationalPerimeter.Constitution.Reals.AuthoritativeRuntime.performCarrier
#print axioms RelationalPerimeter.Constitution.Reals.AuthoritativeRuntime.carrierContract
#print axioms RelationalPerimeter.Constitution.Reals.AuthoritativeRuntime.typedContract
#print axioms RelationalPerimeter.Constitution.Reals.AuthoritativeRuntime.typedReducedEvent
#print axioms RelationalPerimeter.Constitution.Reals.AuthoritativeRuntime.typedReducedContract
#print axioms RelationalPerimeter.Constitution.Reals.AuthoritativeRuntime.perform_event_projects
#print axioms RelationalPerimeter.Constitution.Reals.AuthoritativeRuntime.typedRealization
#print axioms RelationalPerimeter.Constitution.Reals.AuthoritativeRuntime.typedBridge
#print axioms RelationalPerimeter.Constitution.Reals.AuthoritativeRuntime.admitAllTyped
#print axioms RelationalPerimeter.Constitution.Reals.AuthoritativeRuntime.typedOutcomes_exact
#print axioms RelationalPerimeter.Constitution.Reals.AuthoritativeRuntime.typedEvents_exact
#print axioms RelationalPerimeter.Constitution.Reals.AuthoritativeRuntime.typedObservations_exact
#print axioms RelationalPerimeter.Constitution.Reals.AuthoritativeRuntime.sameTypedFuture
#print axioms RelationalPerimeter.Constitution.Reals.AuthoritativeRuntime.GenericCompleteness
#print axioms RelationalPerimeter.Constitution.Reals.AuthoritativeRuntime.completeGeneric
#print axioms RelationalPerimeter.Constitution.Reals.AuthoritativeRuntime.OwnedTarget
#print axioms RelationalPerimeter.Constitution.Reals.AuthoritativeRuntime.OwnedTarget.readout
#print axioms RelationalPerimeter.Constitution.Reals.AuthoritativeRuntime.OwnedTarget.stamp
#print axioms RelationalPerimeter.Constitution.Reals.AuthoritativeRuntime.RetainedTarget
#print axioms RelationalPerimeter.Constitution.Reals.AuthoritativeRuntime.TargetContinuationAction
#print axioms RelationalPerimeter.Constitution.Reals.AuthoritativeRuntime.TargetContinuationAccepted
#print axioms RelationalPerimeter.Constitution.Reals.AuthoritativeRuntime.TargetContinuationStored
#print axioms RelationalPerimeter.Constitution.Reals.AuthoritativeRuntime.targetContinuationProgram
#print axioms RelationalPerimeter.Constitution.Reals.AuthoritativeRuntime.targetContinuation_readout
#print axioms RelationalPerimeter.Constitution.Reals.AuthoritativeRuntime.OwnedTarget.observation
#print axioms RelationalPerimeter.Constitution.Reals.AuthoritativeRuntime.installedObservation
#print axioms RelationalPerimeter.Constitution.Reals.AuthoritativeRuntime.ExecutedResponse.target
#print axioms RelationalPerimeter.Constitution.Reals.AuthoritativeRuntime.ExecutedResponse.target_read_exact
#print axioms RelationalPerimeter.Constitution.Reals.AuthoritativeRuntime.OwnedTarget.installed
#print axioms RelationalPerimeter.Constitution.Reals.AuthoritativeRuntime.RawSourceStep
#print axioms RelationalPerimeter.Constitution.Reals.AuthoritativeRuntime.RawSourceStep.next
#print axioms RelationalPerimeter.Constitution.Reals.AuthoritativeRuntime.RawSourceStep.event
#print axioms RelationalPerimeter.Constitution.Reals.AuthoritativeRuntime.RawSourceStep.readoutExact
#print axioms RelationalPerimeter.Constitution.Reals.AuthoritativeRuntime.performRawSource
#print axioms RelationalPerimeter.Constitution.Reals.AuthoritativeRuntime.GroupingStep
#print axioms RelationalPerimeter.Constitution.Reals.AuthoritativeRuntime.GroupingStep.next
#print axioms RelationalPerimeter.Constitution.Reals.AuthoritativeRuntime.GroupingStep.event
#print axioms RelationalPerimeter.Constitution.Reals.AuthoritativeRuntime.performGrouping
#print axioms RelationalPerimeter.Constitution.Reals.AuthoritativeRuntime.ContinuedStep
#print axioms RelationalPerimeter.Constitution.Reals.AuthoritativeRuntime.ContinuedStep.next
#print axioms RelationalPerimeter.Constitution.Reals.AuthoritativeRuntime.ContinuedStep.event
#print axioms RelationalPerimeter.Constitution.Reals.AuthoritativeRuntime.continueInstalled
#print axioms RelationalPerimeter.Constitution.Reals.AuthoritativeRuntime.SourceListExecution
#print axioms RelationalPerimeter.Constitution.Reals.AuthoritativeRuntime.executeSourceList
#print axioms RelationalPerimeter.Constitution.Reals.AuthoritativeRuntime.performSourceListGrouping
#print axioms RelationalPerimeter.Constitution.Reals.AuthoritativeRuntime.listMapAppend
#print axioms RelationalPerimeter.Constitution.Reals.AuthoritativeRuntime.continueInstalled_none
/- AXIOM_AUDIT_END -/
