import RelationalPerimeter.Constitution.Grouping.ContinuationContract
import RelationalPerimeter.Constitution.Reals.ExecutedApproximations

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Exact continuation contract for approximation requests

The rich state retains the actual operation journal.  The reduced public
state retains only its depth and the last constituted dyadic code.  Each rich
transition is one `ExecutedResponse`: its next state, normalized event and
readout are projections of the same executed approximation package.

`bridge` proves that this reduction commutes with every finite run, event list
and observation list through the generic `Continuation.Exact` theorems.
-/

namespace RelationalPerimeter.Constitution.Reals
namespace ResponseContinuation

open StrongPerimetralTurning
open StrongPerimetralTurning.GodelGroupingTower
open ConstitutiveSearch.Grouping

/-- Rich continuation state: actual journal plus its current memory readout. -/
structure RichState (P : CircularPresentation) where
  journal : OperationJournal ApproximationPayload
  memory : SignedDyadicCode

/-- Public state after forgetting the journal contents but not its depth. -/
structure ReducedState where
  depth : Nat
  memory : SignedDyadicCode

theorem ReducedState.equal
    {first second : ReducedState}
    (depthExact : first.depth = second.depth)
    (memoryExact : first.memory = second.memory) : first = second := by
  cases first with
  | mk firstDepth firstMemory =>
      cases second with
      | mk secondDepth secondMemory =>
          cases depthExact
          cases memoryExact
          rfl

/-- Fixed normalized event type used by the exact continuation bridge. -/
structure NormalizedEvent where
  request : ApproximationRequest
  startDepth : Nat
  endDepth : Nat
  code : SignedDyadicCode

theorem NormalizedEvent.equal
    {first second : NormalizedEvent}
    (requestExact : first.request = second.request)
    (startExact : first.startDepth = second.startDepth)
    (endExact : first.endDepth = second.endDepth)
    (codeExact : first.code = second.code) : first = second := by
  cases first with
  | mk firstRequest firstStart firstEnd firstCode =>
      cases second with
      | mk secondRequest secondStart secondEnd secondCode =>
          cases requestExact
          cases startExact
          cases endExact
          cases codeExact
          rfl

/--
The unique master response for one transition.  Its approximation field owns
the executed schedule and therefore its two occurrences and provenance.
-/
structure ExecutedResponse
    (P : CircularPresentation)
    (state : RichState P)
    (input : ApproximationPayload) where
  approximation : ExecutedApproximation P state.journal input

/-- Execute one request exactly once at the level of the master package. -/
def executeResponse
    (P : CircularPresentation)
    (state : RichState P)
    (input : ApproximationPayload) : ExecutedResponse P state input :=
  { approximation := executeApproximation P state.journal input }

namespace ExecutedResponse

/-- The next rich state is projected from the master response. -/
def next
    {P : CircularPresentation}
    {state : RichState P}
    {input : ApproximationPayload}
    (response : ExecutedResponse P state input) : RichState P :=
  { journal := ExecutedApproximation.completedJournal state.journal input
    memory := response.approximation.readout }

/-- The normalized event is projected from the same master response. -/
def event
    {P : CircularPresentation}
    {state : RichState P}
    {input : ApproximationPayload}
    (response : ExecutedResponse P state input) : NormalizedEvent :=
  { request := response.approximation.provenance.request
    startDepth := state.journal.depth
    endDepth :=
      (ExecutedApproximation.completedJournal state.journal input).depth
    code := response.approximation.readout }

/-- The full occurrence-bearing provenance remains available before reduction. -/
def provenance
    {P : CircularPresentation}
    {state : RichState P}
    {input : ApproximationPayload}
    (response : ExecutedResponse P state input) :
    ExecutedApproximation.Provenance response.approximation :=
  response.approximation.provenance

theorem next_memory_exact
    {P : CircularPresentation}
    {state : RichState P}
    {input : ApproximationPayload}
    (response : ExecutedResponse P state input) :
    response.next.memory = input.code :=
  rfl

theorem event_request_exact
    {P : CircularPresentation}
    {state : RichState P}
    {input : ApproximationPayload}
    (response : ExecutedResponse P state input) :
    response.event.request = input.request :=
  rfl

theorem event_endDepth_exact
    {P : CircularPresentation}
    {state : RichState P}
    {input : ApproximationPayload}
    (response : ExecutedResponse P state input) :
    response.event.endDepth = state.journal.depth + 6 :=
  ExecutedApproximation.completedJournal_depth state.journal input

end ExecutedResponse

/-- Forget journal contents only after the rich state has been constituted. -/
def project
    {P : CircularPresentation}
    (state : RichState P) : ReducedState :=
  { depth := state.journal.depth, memory := state.memory }

/-- Rich next-state projection of the one master execution. -/
def sourceNext
    (P : CircularPresentation)
    (state : RichState P)
    (input : ApproximationPayload) : RichState P :=
  (executeResponse P state input).next

/-- Rich normalized event projection of the same master execution. -/
def sourceEvent
    (P : CircularPresentation)
    (state : RichState P)
    (input : ApproximationPayload) : NormalizedEvent :=
  (executeResponse P state input).event

/-- Every finite approximation request is positively admitted. -/
def sourceAllow
    (P : CircularPresentation)
    (state : RichState P)
    (input : ApproximationPayload) : Type :=
  Unit

/-- Reduced transition matching the projection of the rich execution. -/
def reducedNext
    (state : ReducedState)
    (input : ApproximationPayload) : ReducedState :=
  { depth := state.depth + 6, memory := input.code }

/-- Reduced event matching the normalized rich event. -/
def reducedEvent
    (state : ReducedState)
    (input : ApproximationPayload) : NormalizedEvent :=
  { request := input.request
    startDepth := state.depth
    endDepth := state.depth + 6
    code := input.code }

def reducedAllow
    (state : ReducedState)
    (input : ApproximationPayload) : Type :=
  Unit

/-- Exact bridge from occurrence-bearing journals to the fixed public state. -/
def bridge
    (P : CircularPresentation) :
    Continuation.Exact
      (RichState P) ReducedState ApproximationPayload
      NormalizedEvent SignedDyadicCode where
  project := project
  sourceNext := sourceNext P
  reducedNext := reducedNext
  sourceAllow := sourceAllow P
  reducedAllow := reducedAllow
  toReduced := fun _ _ _ => Unit.unit
  toSource := fun _ _ _ => Unit.unit
  sourceEvent := sourceEvent P
  reducedEvent := reducedEvent
  sourceRead := RichState.memory
  reducedRead := ReducedState.memory
  nextLaw := by
    intro state input
    exact ReducedState.equal
      (ExecutedApproximation.completedJournal_depth state.journal input) rfl
  eventLaw := by
    intro state input
    exact NormalizedEvent.equal rfl rfl
      (ExecutedApproximation.completedJournal_depth state.journal input) rfl
  readLaw := fun _ => rfl

/-- Positive admission of every finite request list. -/
def admitAll
    (P : CircularPresentation)
    (state : RichState P) :
    (inputs : List ApproximationPayload) ->
      Continuation.Admitted
        (bridge P).sourceNext (bridge P).sourceAllow state inputs
  | [] => .nil state
  | input :: rest =>
      .cons Unit.unit (admitAll P ((bridge P).sourceNext state input) rest)

theorem finiteRun_exact
    (P : CircularPresentation)
    (state : RichState P)
    (inputs : List ApproximationPayload) :
    (bridge P).project
        (Continuation.run (bridge P).sourceNext state inputs) =
      Continuation.run (bridge P).reducedNext
        ((bridge P).project state) inputs :=
  (bridge P).run_exact state inputs

theorem finiteEvents_exact
    (P : CircularPresentation)
    (state : RichState P)
    (inputs : List ApproximationPayload) :
    Continuation.events (bridge P).sourceNext (bridge P).sourceEvent
        state inputs =
      Continuation.events (bridge P).reducedNext (bridge P).reducedEvent
        ((bridge P).project state) inputs :=
  (bridge P).events_exact state inputs

theorem finiteObservations_exact
    (P : CircularPresentation)
    (state : RichState P)
    (inputs : List ApproximationPayload) :
    Continuation.observations (bridge P).sourceNext (bridge P).sourceRead
        state inputs =
      Continuation.observations (bridge P).reducedNext (bridge P).reducedRead
        ((bridge P).project state) inputs :=
  (bridge P).observations_exact state inputs

/--
Exact normalized future shared by two rich states with one projection,
including proof-relevant admission transport in both directions.
-/
structure SameNormalizedFuture
    (P : CircularPresentation)
    (first second : RichState P) where
  admittedForward :
    (inputs : List ApproximationPayload) ->
      Continuation.Admitted
          (bridge P).sourceNext (bridge P).sourceAllow first inputs ->
        Continuation.Admitted
          (bridge P).sourceNext (bridge P).sourceAllow second inputs
  admittedBackward :
    (inputs : List ApproximationPayload) ->
      Continuation.Admitted
          (bridge P).sourceNext (bridge P).sourceAllow second inputs ->
        Continuation.Admitted
          (bridge P).sourceNext (bridge P).sourceAllow first inputs
  next :
    (inputs : List ApproximationPayload) ->
      (bridge P).project
          (Continuation.run (bridge P).sourceNext first inputs) =
        (bridge P).project
          (Continuation.run (bridge P).sourceNext second inputs)
  events :
    (inputs : List ApproximationPayload) ->
      Continuation.events (bridge P).sourceNext (bridge P).sourceEvent
          first inputs =
        Continuation.events (bridge P).sourceNext (bridge P).sourceEvent
          second inputs
  observations :
    (inputs : List ApproximationPayload) ->
      Continuation.observations (bridge P).sourceNext (bridge P).sourceRead
          first inputs =
        Continuation.observations (bridge P).sourceNext (bridge P).sourceRead
          second inputs

/-- Equal public states have the same admitted and normalized finite behavior. -/
def sameNormalizedFuture
    (P : CircularPresentation)
    {first second : RichState P}
    (same : (bridge P).project first = (bridge P).project second) :
    SameNormalizedFuture P first second where
  admittedForward := by
    intro inputs admitted
    apply (bridge P).admittedSource
    exact same ▸ (bridge P).admitted admitted
  admittedBackward := by
    intro inputs admitted
    apply (bridge P).admittedSource
    exact same.symm ▸ (bridge P).admitted admitted
  next := by
    intro inputs
    rw [finiteRun_exact, finiteRun_exact, same]
  events := by
    intro inputs
    rw [finiteEvents_exact, finiteEvents_exact, same]
  observations := by
    intro inputs
    rw [finiteObservations_exact, finiteObservations_exact, same]

end ResponseContinuation
end RelationalPerimeter.Constitution.Reals

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Constitution.Reals.ResponseContinuation.RichState
#print axioms RelationalPerimeter.Constitution.Reals.ResponseContinuation.ReducedState
#print axioms RelationalPerimeter.Constitution.Reals.ResponseContinuation.ReducedState.equal
#print axioms RelationalPerimeter.Constitution.Reals.ResponseContinuation.NormalizedEvent
#print axioms RelationalPerimeter.Constitution.Reals.ResponseContinuation.NormalizedEvent.equal
#print axioms RelationalPerimeter.Constitution.Reals.ResponseContinuation.ExecutedResponse
#print axioms RelationalPerimeter.Constitution.Reals.ResponseContinuation.executeResponse
#print axioms RelationalPerimeter.Constitution.Reals.ResponseContinuation.ExecutedResponse.next
#print axioms RelationalPerimeter.Constitution.Reals.ResponseContinuation.ExecutedResponse.event
#print axioms RelationalPerimeter.Constitution.Reals.ResponseContinuation.ExecutedResponse.provenance
#print axioms RelationalPerimeter.Constitution.Reals.ResponseContinuation.ExecutedResponse.next_memory_exact
#print axioms RelationalPerimeter.Constitution.Reals.ResponseContinuation.ExecutedResponse.event_request_exact
#print axioms RelationalPerimeter.Constitution.Reals.ResponseContinuation.ExecutedResponse.event_endDepth_exact
#print axioms RelationalPerimeter.Constitution.Reals.ResponseContinuation.project
#print axioms RelationalPerimeter.Constitution.Reals.ResponseContinuation.sourceNext
#print axioms RelationalPerimeter.Constitution.Reals.ResponseContinuation.sourceEvent
#print axioms RelationalPerimeter.Constitution.Reals.ResponseContinuation.sourceAllow
#print axioms RelationalPerimeter.Constitution.Reals.ResponseContinuation.reducedNext
#print axioms RelationalPerimeter.Constitution.Reals.ResponseContinuation.reducedEvent
#print axioms RelationalPerimeter.Constitution.Reals.ResponseContinuation.reducedAllow
#print axioms RelationalPerimeter.Constitution.Reals.ResponseContinuation.bridge
#print axioms RelationalPerimeter.Constitution.Reals.ResponseContinuation.admitAll
#print axioms RelationalPerimeter.Constitution.Reals.ResponseContinuation.finiteRun_exact
#print axioms RelationalPerimeter.Constitution.Reals.ResponseContinuation.finiteEvents_exact
#print axioms RelationalPerimeter.Constitution.Reals.ResponseContinuation.finiteObservations_exact
#print axioms RelationalPerimeter.Constitution.Reals.ResponseContinuation.SameNormalizedFuture
#print axioms RelationalPerimeter.Constitution.Reals.ResponseContinuation.sameNormalizedFuture
/- AXIOM_AUDIT_END -/
