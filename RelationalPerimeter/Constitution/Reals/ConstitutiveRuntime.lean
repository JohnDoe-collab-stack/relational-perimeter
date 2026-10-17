import RelationalPerimeter.Constitution.Godel.GroupingTower
import RelationalPerimeter.Constitution.Reals.Precision

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Constitutive runtime for produced approximations

This module provides the non-forgeable historical and operational core used by
the corrected Gödel--grouping--real raccord.  A journal is rooted at an already
constituted history depth; in the terminal construction that root is exactly
the Gödel continuation `H1`.  Public execution appends six semantic phases.

The phase packages are nested: search owns reception, action owns search,
authorization/decomposition owns the action and its separate preservation
witness, continuation owns the decomposition, and memory owns that
continuation together with the stored action output.  Consequently a list of
phase names cannot inhabit an executed request.  The numerical readout is a
projection of the stored resource and is unavailable before memory.
-/

namespace RelationalPerimeter.Constitution.Reals.ConstitutiveRuntime

open StrongPerimetralTurning
open StrongPerimetralTurning.GodelGroupingTower
open ConstitutiveSearch.OccurrencePersistence
open ConstitutiveSearch.PerimeterPersistence.Iterated

universe uRequest uSearch uAction uAccepted uAuthorization uDecomposition
  uContinuation uStored uResource

/-- The semantic phases of one public request, in constitutive order. -/
inductive Phase : Type
  | receivedContext
  | executedSearch
  | relationalAction
  | authorizationDecomposition
  | effectiveContinuation
  | contractMemory
deriving DecidableEq

/-- A calculable public identity shared by heterogeneous runtime requests. -/
inductive RequestStamp : Type
  | source (term precision : Nat)
  | limit (precision : Nat)
  | finiteGrouping (precision size : Nat)
deriving DecidableEq

/-- A journal entry identifies both the request and the semantic phase. -/
structure Entry where
  request : RequestStamp
  phase : Phase

/--
A proof-relevant journal rooted at an already constituted finite depth.  Its
constructor is private: only the execution functions below may append entries.
-/
structure Journal (P : CircularPresentation) (baseDepth : Nat) where
  private mk ::
  relativeDepth : Nat
  entries : List Entry

namespace Journal

/-- The empty operational journal over an already constituted base. -/
def root (P : CircularPresentation) (baseDepth : Nat) : Journal P baseDepth :=
  .mk 0 []

/-- Absolute generated-history depth represented by this journal. -/
def absoluteDepth {P : CircularPresentation} {baseDepth : Nat}
    (journal : Journal P baseDepth) : Nat :=
  baseDepth + journal.relativeDepth

/-- The exact generated history indexed by the base and journal. -/
def history {P : CircularPresentation} {baseDepth : Nat}
    (journal : Journal P baseDepth) :
    RootedGeneratedHistory P :=
  iteratedHistory P journal.absoluteDepth

/-- Internal chronological append.  It is intentionally not public. -/
private def append {P : CircularPresentation} {baseDepth : Nat}
    (journal : Journal P baseDepth) (entry : Entry) :
    Journal P baseDepth :=
  .mk (journal.relativeDepth + 1) (journal.entries ++ [entry])

theorem root_relativeDepth (P : CircularPresentation) (baseDepth : Nat) :
    (root P baseDepth).relativeDepth = 0 :=
  rfl

theorem root_absoluteDepth (P : CircularPresentation) (baseDepth : Nat) :
    (root P baseDepth).absoluteDepth = baseDepth :=
  rfl

private theorem append_relativeDepth
    {P : CircularPresentation} {baseDepth : Nat}
    (journal : Journal P baseDepth) (entry : Entry) :
    (append journal entry).relativeDepth = journal.relativeDepth + 1 :=
  rfl

private theorem append_absoluteDepth
    {P : CircularPresentation} {baseDepth : Nat}
    (journal : Journal P baseDepth) (entry : Entry) :
    (append journal entry).absoluteDepth = journal.absoluteDepth + 1 := by
  exact (Nat.add_assoc baseDepth journal.relativeDepth 1).symm

/--
The fresh occurrence of an append is the actual last occurrence of the next
generated history.  The equality cast only reconciles the list-length
calculation with the successor presentation; it does not reconstruct data.
-/
private def freshOccurrence
    {P : CircularPresentation} {baseDepth : Nat}
    (journal : Journal P baseDepth)
    (entry : Entry) :
    History.Occurrence (history (append journal entry)).history :=
  History.Occurrence.last

end Journal

/--
One phase actually appended to the shared journal.  Its constructor is private,
so phase names alone cannot manufacture execution evidence.
-/
structure ExecutedPhase
    (P : CircularPresentation)
    {baseDepth : Nat}
    (before : Journal P baseDepth)
    (request : RequestStamp)
    (phase : Phase) where
  private mk ::
  occurrence :
    History.Occurrence
      (Journal.history
        (Journal.append before { request := request, phase := phase })).history
  occurrenceExact :
    occurrence =
      Journal.freshOccurrence before { request := request, phase := phase }

namespace ExecutedPhase

/-- The next journal is fixed by the phase index, not supplied by a caller. -/
def after
    {P : CircularPresentation}
    {baseDepth : Nat}
    {before : Journal P baseDepth}
    {request : RequestStamp}
    {phase : Phase}
    (_executed : ExecutedPhase P before request phase) :
    Journal P baseDepth :=
  Journal.append before { request := request, phase := phase }

end ExecutedPhase

/-- Execute exactly one semantic phase. -/
def executePhase
    (P : CircularPresentation)
    {baseDepth : Nat}
    (before : Journal P baseDepth)
    (request : RequestStamp)
    (phase : Phase) : ExecutedPhase P before request phase :=
  { occurrence := Journal.freshOccurrence before
      { request := request, phase := phase }
    occurrenceExact := rfl }

namespace ExecutedPhase

theorem relativeDepth_succ
    {P : CircularPresentation}
    {baseDepth : Nat}
    {before : Journal P baseDepth}
    {request : RequestStamp}
    {phase : Phase}
    (executed : ExecutedPhase P before request phase) :
    executed.after.relativeDepth = before.relativeDepth + 1 := by
  exact Journal.append_relativeDepth before _

theorem absoluteDepth_succ
    {P : CircularPresentation}
    {baseDepth : Nat}
    {before : Journal P baseDepth}
    {request : RequestStamp}
    {phase : Phase}
    (executed : ExecutedPhase P before request phase) :
    executed.after.absoluteDepth = before.absoluteDepth + 1 := by
  exact Journal.append_absoluteDepth before _

/-- Transport a prior occurrence through this exact executed phase. -/
def transportPrior
    {P : CircularPresentation}
    {baseDepth : Nat}
    {before : Journal P baseDepth}
    {request : RequestStamp}
    {phase : Phase}
    (executed : ExecutedPhase P before request phase)
    (occurrence : History.Occurrence (Journal.history before).history) :
    History.Occurrence (Journal.history executed.after).history :=
  History.Occurrence.earlier occurrence

/-- Transport through an executed phase preserves the identity of prior occurrences. -/
theorem transportPrior_injective
    {P : CircularPresentation}
    {baseDepth : Nat}
    {before : Journal P baseDepth}
    {request : RequestStamp}
    {phase : Phase}
    (executed : ExecutedPhase P before request phase) :
    Function.Injective executed.transportPrior := by
  intro first second equality
  cases equality
  rfl

/-- Every transported prior occurrence is distinct from the fresh occurrence. -/
theorem transportPrior_ne_fresh
    {P : CircularPresentation}
    {baseDepth : Nat}
    {before : Journal P baseDepth}
    {request : RequestStamp}
    {phase : Phase}
    (executed : ExecutedPhase P before request phase)
    (occurrence : History.Occurrence (Journal.history before).history) :
    executed.transportPrior occurrence ≠ executed.occurrence := by
  rw [executed.occurrenceExact]
  intro equality
  cases equality

end ExecutedPhase

/-! ## Semantic program and nested execution packages -/

/--
A semantic request program separates production, action and preservation.  All
resource families live in `Type`.  The store consumes both the continuation and
the exact action result, and the readout law identifies its observation with
that same action rather than with the request.
-/
structure Program (Request : Type uRequest) where
  ReceivedContext : Request -> Type uResource
  SearchResult : Request -> Type uResource
  ActionResult : (request : Request) -> SearchResult request -> Type uResource
  Accepted : (request : Request) ->
    (searched : SearchResult request) -> ActionResult request searched ->
      Type uResource
  Authorization : (request : Request) ->
    (searched : SearchResult request) ->
    (acted : ActionResult request searched) ->
    Accepted request searched acted -> Type uResource
  Decomposition : (request : Request) ->
    (searched : SearchResult request) ->
    (acted : ActionResult request searched) ->
    (accepted : Accepted request searched acted) ->
    Authorization request searched acted accepted -> Type uResource
  Continuation : (request : Request) ->
    (searched : SearchResult request) ->
    (acted : ActionResult request searched) ->
    (accepted : Accepted request searched acted) ->
    (authorized : Authorization request searched acted accepted) ->
    Decomposition request searched acted accepted authorized -> Type uResource
  Stored : (request : Request) ->
    (searched : SearchResult request) ->
    (acted : ActionResult request searched) -> Type uResource
  stamp : Request -> RequestStamp
  receive : (request : Request) -> ReceivedContext request
  search : (request : Request) -> ReceivedContext request -> SearchResult request
  act : (request : Request) -> (searched : SearchResult request) ->
    ActionResult request searched
  preserves : (request : Request) -> (searched : SearchResult request) ->
    (acted : ActionResult request searched) -> Accepted request searched acted
  authorize : (request : Request) -> (searched : SearchResult request) ->
    (acted : ActionResult request searched) ->
    (accepted : Accepted request searched acted) ->
      Authorization request searched acted accepted
  decompose : (request : Request) -> (searched : SearchResult request) ->
    (acted : ActionResult request searched) ->
    (accepted : Accepted request searched acted) ->
    (authorized : Authorization request searched acted accepted) ->
      Decomposition request searched acted accepted authorized
  resume : (request : Request) -> (searched : SearchResult request) ->
    (acted : ActionResult request searched) ->
    (accepted : Accepted request searched acted) ->
    (authorized : Authorization request searched acted accepted) ->
    (decomposed : Decomposition request searched acted accepted authorized) ->
      Continuation request searched acted accepted authorized decomposed
  store : (request : Request) -> (searched : SearchResult request) ->
    (acted : ActionResult request searched) ->
    (accepted : Accepted request searched acted) ->
    (authorized : Authorization request searched acted accepted) ->
    (decomposed : Decomposition request searched acted accepted authorized) ->
    Continuation request searched acted accepted authorized decomposed ->
      Stored request searched acted
  actionCode : {request : Request} -> {searched : SearchResult request} ->
    ActionResult request searched -> SignedDyadicCode
  read : {request : Request} -> {searched : SearchResult request} ->
    {acted : ActionResult request searched} ->
      Stored request searched acted -> SignedDyadicCode
  readStoredExact :
    {request : Request} -> {searched : SearchResult request} ->
    {acted : ActionResult request searched} ->
    (stored : Stored request searched acted) ->
      read stored = actionCode acted

section ProgramExecution

variable {Request : Type uRequest}

/-- Context reception owns the first executed phase. -/
structure Received
    (program : Program.{uRequest, uResource} Request)
    (P : CircularPresentation)
    {baseDepth : Nat}
    (journal : Journal P baseDepth)
    (request : Request) where
  private mk ::
  context : program.ReceivedContext request
  contextExact : context = program.receive request
  phase : ExecutedPhase P journal (program.stamp request) .receivedContext

/-- Search owns reception and the result computed from the received request. -/
structure Searched
    (program : Program.{uRequest, uResource} Request)
    (P : CircularPresentation)
    {baseDepth : Nat}
    {journal : Journal P baseDepth}
    {request : Request} where
  private mk ::
  received : Received program P journal request
  result : program.SearchResult request
  resultExact : result = program.search request received.context
  phase : ExecutedPhase P received.phase.after
    (program.stamp request) .executedSearch

/-- Relational action owns the exact search result it consumes. -/
structure Acted
    (program : Program.{uRequest, uResource} Request)
    (P : CircularPresentation)
    {baseDepth : Nat}
    {journal : Journal P baseDepth}
    {request : Request} where
  private mk ::
  searched : Searched program P (journal := journal) (request := request)
  result : program.ActionResult request searched.result
  resultExact : result = program.act request searched.result
  phase : ExecutedPhase P searched.phase.after
    (program.stamp request) .relationalAction

/-- Authorization/decomposition owns the action and separate preservation. -/
structure Authorized
    (program : Program.{uRequest, uResource} Request)
    (P : CircularPresentation)
    {baseDepth : Nat}
    {journal : Journal P baseDepth}
    {request : Request} where
  private mk ::
  acted : Acted program P (journal := journal) (request := request)
  accepted : program.Accepted request acted.searched.result acted.result
  acceptedExact :
    accepted = program.preserves request acted.searched.result acted.result
  authorization :
    program.Authorization request acted.searched.result acted.result accepted
  authorizationExact :
    authorization = program.authorize request acted.searched.result acted.result accepted
  decomposition :
    program.Decomposition request acted.searched.result acted.result accepted authorization
  decompositionExact :
    decomposition = program.decompose request acted.searched.result acted.result
      accepted authorization
  phase : ExecutedPhase P acted.phase.after
    (program.stamp request) .authorizationDecomposition

/-- Effective continuation owns the exact authorized decomposition. -/
structure Continued
    (program : Program.{uRequest, uResource} Request)
    (P : CircularPresentation)
    {baseDepth : Nat}
    {journal : Journal P baseDepth}
    {request : Request} where
  private mk ::
  authorized : Authorized program P (journal := journal) (request := request)
  result :
    program.Continuation request
      authorized.acted.searched.result authorized.acted.result
      authorized.accepted authorized.authorization authorized.decomposition
  resultExact :
    result = program.resume request
      authorized.acted.searched.result authorized.acted.result
      authorized.accepted authorized.authorization authorized.decomposition
  phase : ExecutedPhase P authorized.phase.after
    (program.stamp request) .effectiveContinuation

/-- Contract memory owns the continuation and stores that same action output. -/
structure Memorized
    (program : Program.{uRequest, uResource} Request)
    (P : CircularPresentation)
    {baseDepth : Nat}
    {journal : Journal P baseDepth}
    {request : Request} where
  private mk ::
  continued : Continued program P (journal := journal) (request := request)
  stored : program.Stored request
    continued.authorized.acted.searched.result
    continued.authorized.acted.result
  storedExact :
    stored = program.store request
      continued.authorized.acted.searched.result
      continued.authorized.acted.result
      continued.authorized.accepted
      continued.authorized.authorization
      continued.authorized.decomposition
      continued.result
  phase : ExecutedPhase P continued.phase.after
    (program.stamp request) .contractMemory

/-- The only public evidence for a completely executed request. -/
structure ExecutedRequest
    (program : Program.{uRequest, uResource} Request)
    (P : CircularPresentation)
    {baseDepth : Nat}
    (journal : Journal P baseDepth)
    (request : Request) where
  private mk ::
  memory : Memorized program P (journal := journal) (request := request)

/-- Execute every semantic phase once and retain the nested dependency chain. -/
def execute
    (program : Program.{uRequest, uResource} Request)
    (P : CircularPresentation)
    {baseDepth : Nat}
    (journal : Journal P baseDepth)
    (request : Request) : ExecutedRequest program P journal request := by
  let received : Received program P journal request :=
    { context := program.receive request
      contextExact := rfl
      phase := executePhase P journal (program.stamp request) .receivedContext }
  let searched : Searched program P (journal := journal) (request := request) :=
    { received := received
      result := program.search request received.context
      resultExact := rfl
      phase := executePhase P received.phase.after
        (program.stamp request) .executedSearch }
  let acted : Acted program P (journal := journal) (request := request) :=
    { searched := searched
      result := program.act request searched.result
      resultExact := rfl
      phase := executePhase P searched.phase.after
        (program.stamp request) .relationalAction }
  let accepted := program.preserves request acted.searched.result acted.result
  let authorization :=
    program.authorize request acted.searched.result acted.result accepted
  let decomposition :=
    program.decompose request acted.searched.result acted.result
      accepted authorization
  let authorized :
      Authorized program P (journal := journal) (request := request) :=
    { acted := acted
      accepted := accepted
      acceptedExact := rfl
      authorization := authorization
      authorizationExact := rfl
      decomposition := decomposition
      decompositionExact := rfl
      phase := executePhase P acted.phase.after (program.stamp request)
        .authorizationDecomposition }
  let continued :
      Continued program P (journal := journal) (request := request) :=
    { authorized := authorized
      result := program.resume request
        authorized.acted.searched.result authorized.acted.result
        authorized.accepted authorized.authorization authorized.decomposition
      resultExact := rfl
      phase := executePhase P authorized.phase.after (program.stamp request)
        .effectiveContinuation }
  let memorized :
      Memorized program P (journal := journal) (request := request) :=
    { continued := continued
      stored := program.store request
        continued.authorized.acted.searched.result
        continued.authorized.acted.result
        continued.authorized.accepted
        continued.authorized.authorization
        continued.authorized.decomposition
        continued.result
      storedExact := rfl
      phase := executePhase P continued.phase.after
        (program.stamp request) .contractMemory }
  exact { memory := memorized }

namespace ExecutedRequest

/-- The received context retained by this execution is the program's produced context. -/
theorem receivedContext_is_produced
    {program : Program.{uRequest, uResource} Request}
    {P : CircularPresentation}
    {baseDepth : Nat}
    {journal : Journal P baseDepth}
    {request : Request}
    (executed : ExecutedRequest program P journal request) :
    executed.memory.continued.authorized.acted.searched.received.context =
      program.receive request :=
  executed.memory.continued.authorized.acted.searched.received.contextExact

/-- Search consumes that exact retained context rather than recomputing beside it. -/
theorem searchResult_is_receivedContextOutput
    {program : Program.{uRequest, uResource} Request}
    {P : CircularPresentation}
    {baseDepth : Nat}
    {journal : Journal P baseDepth}
    {request : Request}
    (executed : ExecutedRequest program P journal request) :
    executed.memory.continued.authorized.acted.searched.result =
      program.search request
        executed.memory.continued.authorized.acted.searched.received.context :=
  executed.memory.continued.authorized.acted.searched.resultExact

/-- Journal reached only after contract memory has executed. -/
def completedJournal
    {program : Program.{uRequest, uResource} Request}
    {P : CircularPresentation}
    {baseDepth : Nat}
    {journal : Journal P baseDepth}
    {request : Request}
    (executed : ExecutedRequest program P journal request) :
    Journal P baseDepth :=
  executed.memory.phase.after


/-- The exact occurrence received by this execution, before search. -/
def receivedOccurrence
    {program : Program.{uRequest, uResource} Request}
    {P : CircularPresentation} {baseDepth : Nat}
    {journal : Journal P baseDepth} {request : Request}
    (executed : ExecutedRequest program P journal request) :
    History.Occurrence
      (Journal.history
        executed.memory.continued.authorized.acted.searched.received.phase.after).history :=
  executed.memory.continued.authorized.acted.searched.received.phase.occurrence

/-- The output occurrence belongs to the actual memory phase. -/
def producedOccurrence
    {program : Program.{uRequest, uResource} Request}
    {P : CircularPresentation} {baseDepth : Nat}
    {journal : Journal P baseDepth} {request : Request}
    (executed : ExecutedRequest program P journal request) :
    History.Occurrence (Journal.history executed.completedJournal).history :=
  executed.memory.phase.occurrence

/-- Public directed provenance; every field is tied to this same execution. -/
structure Provenance
    {program : Program.{uRequest, uResource} Request}
    {P : CircularPresentation} {baseDepth : Nat}
    {journal : Journal P baseDepth} {request : Request}
    (executed : ExecutedRequest program P journal request) where
  stamp : RequestStamp
  stampExact : stamp = program.stamp request
  receivedAt : History.Occurrence
    (Journal.history
      executed.memory.continued.authorized.acted.searched.received.phase.after).history
  receivedExact : receivedAt = executed.receivedOccurrence
  producedAt : History.Occurrence (Journal.history executed.completedJournal).history
  producedExact : producedAt = executed.producedOccurrence
  constitutiveTrace : Memorized program P (journal := journal) (request := request)
  traceExact : constitutiveTrace = executed.memory

def provenance
    {program : Program.{uRequest, uResource} Request}
    {P : CircularPresentation} {baseDepth : Nat}
    {journal : Journal P baseDepth} {request : Request}
    (executed : ExecutedRequest program P journal request) : Provenance executed where
  stamp := program.stamp request
  stampExact := rfl
  receivedAt := executed.receivedOccurrence
  receivedExact := rfl
  producedAt := executed.producedOccurrence
  producedExact := rfl
  constitutiveTrace := executed.memory
  traceExact := rfl


/-- Action resource actually retained inside the execution. -/
def action
    {program : Program.{uRequest, uResource} Request}
    {P : CircularPresentation}
    {baseDepth : Nat}
    {journal : Journal P baseDepth}
    {request : Request}
    (executed : ExecutedRequest program P journal request) :
    program.ActionResult request
      executed.memory.continued.authorized.acted.searched.result :=
  executed.memory.continued.authorized.acted.result

/-- Stored resource from which the observation is read. -/
def stored
    {program : Program.{uRequest, uResource} Request}
    {P : CircularPresentation}
    {baseDepth : Nat}
    {journal : Journal P baseDepth}
    {request : Request}
    (executed : ExecutedRequest program P journal request) :
    program.Stored request
      executed.memory.continued.authorized.acted.searched.result
      executed.memory.continued.authorized.acted.result :=
  executed.provenance.constitutiveTrace.stored

/-- Readout is exclusively a projection of the stored resource. -/
def readout
    {program : Program.{uRequest, uResource} Request}
    {P : CircularPresentation}
    {baseDepth : Nat}
    {journal : Journal P baseDepth}
    {request : Request}
    (executed : ExecutedRequest program P journal request) : SignedDyadicCode :=
  program.read executed.stored

theorem readout_is_storedAction
    {program : Program.{uRequest, uResource} Request}
    {P : CircularPresentation}
    {baseDepth : Nat}
    {journal : Journal P baseDepth}
    {request : Request}
    (executed : ExecutedRequest program P journal request) :
    executed.readout = program.actionCode executed.action :=
  program.readStoredExact executed.stored

theorem completed_relativeDepth
    {program : Program.{uRequest, uResource} Request}
    {P : CircularPresentation}
    {baseDepth : Nat}
    {journal : Journal P baseDepth}
    {request : Request}
    (executed : ExecutedRequest program P journal request) :
    executed.completedJournal.relativeDepth = journal.relativeDepth + 6 := by
  change executed.memory.phase.after.relativeDepth = journal.relativeDepth + 6
  rw [executed.memory.phase.relativeDepth_succ]
  rw [executed.memory.continued.phase.relativeDepth_succ]
  rw [executed.memory.continued.authorized.phase.relativeDepth_succ]
  rw [executed.memory.continued.authorized.acted.phase.relativeDepth_succ]
  rw [executed.memory.continued.authorized.acted.searched.phase.relativeDepth_succ]
  rw [executed.memory.continued.authorized.acted.searched.received.phase.relativeDepth_succ]

theorem completed_absoluteDepth
    {program : Program.{uRequest, uResource} Request}
    {P : CircularPresentation}
    {baseDepth : Nat}
    {journal : Journal P baseDepth}
    {request : Request}
    (executed : ExecutedRequest program P journal request) :
    executed.completedJournal.absoluteDepth = journal.absoluteDepth + 6 := by
  change executed.memory.phase.after.absoluteDepth = journal.absoluteDepth + 6
  rw [executed.memory.phase.absoluteDepth_succ]
  rw [executed.memory.continued.phase.absoluteDepth_succ]
  rw [executed.memory.continued.authorized.phase.absoluteDepth_succ]
  rw [executed.memory.continued.authorized.acted.phase.absoluteDepth_succ]
  rw [executed.memory.continued.authorized.acted.searched.phase.absoluteDepth_succ]
  rw [executed.memory.continued.authorized.acted.searched.received.phase.absoluteDepth_succ]

end ExecutedRequest

end ProgramExecution

end RelationalPerimeter.Constitution.Reals.ConstitutiveRuntime

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Constitution.Reals.ConstitutiveRuntime.Phase
#print axioms RelationalPerimeter.Constitution.Reals.ConstitutiveRuntime.RequestStamp
#print axioms RelationalPerimeter.Constitution.Reals.ConstitutiveRuntime.Entry
#print axioms RelationalPerimeter.Constitution.Reals.ConstitutiveRuntime.Journal
#print axioms RelationalPerimeter.Constitution.Reals.ConstitutiveRuntime.Journal.root
#print axioms RelationalPerimeter.Constitution.Reals.ConstitutiveRuntime.Journal.relativeDepth
#print axioms RelationalPerimeter.Constitution.Reals.ConstitutiveRuntime.Journal.absoluteDepth
#print axioms RelationalPerimeter.Constitution.Reals.ConstitutiveRuntime.Journal.root_absoluteDepth
#print axioms RelationalPerimeter.Constitution.Reals.ConstitutiveRuntime.Journal.history
#print axioms RelationalPerimeter.Constitution.Reals.ConstitutiveRuntime.ExecutedPhase
#print axioms RelationalPerimeter.Constitution.Reals.ConstitutiveRuntime.executePhase
#print axioms RelationalPerimeter.Constitution.Reals.ConstitutiveRuntime.ExecutedPhase.relativeDepth_succ
#print axioms RelationalPerimeter.Constitution.Reals.ConstitutiveRuntime.ExecutedPhase.absoluteDepth_succ
#print axioms RelationalPerimeter.Constitution.Reals.ConstitutiveRuntime.ExecutedPhase.transportPrior
#print axioms RelationalPerimeter.Constitution.Reals.ConstitutiveRuntime.ExecutedPhase.transportPrior_injective
#print axioms RelationalPerimeter.Constitution.Reals.ConstitutiveRuntime.ExecutedPhase.transportPrior_ne_fresh
#print axioms RelationalPerimeter.Constitution.Reals.ConstitutiveRuntime.Program
#print axioms RelationalPerimeter.Constitution.Reals.ConstitutiveRuntime.Received
#print axioms RelationalPerimeter.Constitution.Reals.ConstitutiveRuntime.Searched
#print axioms RelationalPerimeter.Constitution.Reals.ConstitutiveRuntime.Acted
#print axioms RelationalPerimeter.Constitution.Reals.ConstitutiveRuntime.Authorized
#print axioms RelationalPerimeter.Constitution.Reals.ConstitutiveRuntime.Continued
#print axioms RelationalPerimeter.Constitution.Reals.ConstitutiveRuntime.Memorized
#print axioms RelationalPerimeter.Constitution.Reals.ConstitutiveRuntime.ExecutedRequest
#print axioms RelationalPerimeter.Constitution.Reals.ConstitutiveRuntime.execute
#print axioms RelationalPerimeter.Constitution.Reals.ConstitutiveRuntime.ExecutedRequest.receivedContext_is_produced
#print axioms RelationalPerimeter.Constitution.Reals.ConstitutiveRuntime.ExecutedRequest.searchResult_is_receivedContextOutput
#print axioms RelationalPerimeter.Constitution.Reals.ConstitutiveRuntime.ExecutedRequest.completedJournal
#print axioms RelationalPerimeter.Constitution.Reals.ConstitutiveRuntime.ExecutedRequest.action
#print axioms RelationalPerimeter.Constitution.Reals.ConstitutiveRuntime.ExecutedRequest.stored
#print axioms RelationalPerimeter.Constitution.Reals.ConstitutiveRuntime.ExecutedRequest.readout
#print axioms RelationalPerimeter.Constitution.Reals.ConstitutiveRuntime.ExecutedRequest.readout_is_storedAction
#print axioms RelationalPerimeter.Constitution.Reals.ConstitutiveRuntime.ExecutedRequest.completed_relativeDepth
#print axioms RelationalPerimeter.Constitution.Reals.ConstitutiveRuntime.ExecutedRequest.completed_absoluteDepth
#print axioms RelationalPerimeter.Constitution.Reals.ConstitutiveRuntime.ExecutedRequest.receivedOccurrence
#print axioms RelationalPerimeter.Constitution.Reals.ConstitutiveRuntime.ExecutedRequest.producedOccurrence
#print axioms RelationalPerimeter.Constitution.Reals.ConstitutiveRuntime.ExecutedRequest.Provenance
#print axioms RelationalPerimeter.Constitution.Reals.ConstitutiveRuntime.ExecutedRequest.provenance
/- AXIOM_AUDIT_END -/
