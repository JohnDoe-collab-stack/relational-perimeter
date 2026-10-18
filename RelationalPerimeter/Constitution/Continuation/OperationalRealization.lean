import RelationalPerimeter.Constitution.Continuation.Execution
import RelationalPerimeter.Constitution.Continuation.Minimality

/-! A readout-free operational realization.  The reduced memory retains only
the transition, emitted event and admission contract.  Readout correspondence
is deliberately factored into a separate layer. -/
set_option genInjectivity false
namespace ConstitutiveSearch.ContinuationSignatures
universe u v
variable {S I M : Type u} {E O : Type v}

structure OperationalContract (Memory Input : Type u) (Event : Type v) where
  next : Memory → Input → Memory
  event : Memory → Input → Event
  Allow : Memory → Input → Type u
  decision : ∀ memory input, PSum (Allow memory input) (Allow memory input → False)

structure OperationalRealization (contract : FutureContract S I E O) (Memory : Type u) where
  reduced : OperationalContract Memory I E
  project : S → Memory
  forward : ∀ source input, contract.Allow source input → reduced.Allow (project source) input
  backward : ∀ source input, reduced.Allow (project source) input → contract.Allow source input
  backward_forward : ∀ source input witness,
    backward source input (forward source input witness) = witness
  forward_backward : ∀ source input witness,
    forward source input (backward source input witness) = witness
  next_exact : ∀ source input,
    project (contract.next source input) = reduced.next (project source) input
  event_exact : ∀ source input,
    contract.event source input = reduced.event (project source) input

variable {contract : FutureContract S I E O}

theorem OperationalRealization.enabled_exact
    (realization : OperationalRealization contract M) (source : S) (input : I) :
    contract.enabled source input =
      (match realization.reduced.decision (realization.project source) input with
       | .inl _ => true
       | .inr _ => false) := by
  unfold FutureContract.enabled
  cases contract.decision source input with
  | inl admitted =>
      cases realization.reduced.decision (realization.project source) input with
      | inl _ => rfl
      | inr impossible => exact False.elim (impossible (realization.forward source input admitted))
  | inr impossible =>
      cases realization.reduced.decision (realization.project source) input with
      | inl admitted => exact False.elim (impossible (realization.backward source input admitted))
      | inr _ => rfl

theorem OperationalRealization.run_exact (realization : OperationalRealization contract M)
    (source : S) (requests : List I) :
    realization.project (Grouping.Continuation.run contract.next source requests) =
      Grouping.Continuation.run realization.reduced.next (realization.project source) requests := by
  induction requests generalizing source with
  | nil => rfl
  | cons input rest ih =>
      exact (ih _).trans (congrArg
        (fun memory => Grouping.Continuation.run realization.reduced.next memory rest)
        (realization.next_exact source input))

theorem OperationalRealization.events_exact (realization : OperationalRealization contract M)
    (source : S) (requests : List I) :
    Grouping.Continuation.events contract.next contract.event source requests =
      Grouping.Continuation.events realization.reduced.next realization.reduced.event
        (realization.project source) requests := by
  induction requests generalizing source with
  | nil => rfl
  | cons input rest ih =>
      change contract.event source input :: _ = realization.reduced.event
        (realization.project source) input :: _
      rw [realization.event_exact source input]
      exact congrArg (List.cons _)
        ((ih _).trans (congrArg
          (fun memory => Grouping.Continuation.events realization.reduced.next
            realization.reduced.event memory rest)
          (realization.next_exact source input)))

def OperationalRealization.admitted (realization : OperationalRealization contract M)
    {source : S} {requests : List I} :
    Grouping.Continuation.Admitted contract.next contract.Allow source requests →
      Grouping.Continuation.Admitted realization.reduced.next realization.reduced.Allow
        (realization.project source) requests
  | .nil _ => .nil _
  | .cons witness tail => .cons (realization.forward _ _ witness)
      ((realization.next_exact _ _) ▸ realization.admitted tail)

def OperationalRealization.admittedSource (realization : OperationalRealization contract M)
    {source : S} {requests : List I} :
    Grouping.Continuation.Admitted realization.reduced.next realization.reduced.Allow
        (realization.project source) requests →
      Grouping.Continuation.Admitted contract.next contract.Allow source requests :=
  match requests with
  | [] => fun _ => .nil _
  | input :: _rest => fun trace =>
      match trace with
      | .cons witness tail => .cons (realization.backward source input witness)
          (realization.admittedSource ((realization.next_exact source input).symm ▸ tail))
termination_by structural requests

def ExactRealization.toOperational (realization : ExactRealization contract M) :
    OperationalRealization contract M where
  reduced :=
    { next := realization.reduced.next
      event := realization.reduced.event
      Allow := realization.reduced.Allow
      decision := realization.reduced.decision }
  project := realization.project
  forward := realization.forward
  backward := realization.backward
  backward_forward := realization.backward_forward
  forward_backward := realization.forward_backward
  next_exact := realization.next_exact
  event_exact := realization.event_exact

structure OperationalNonemptyRequestTrace (Request : Type u) where
  head : Request
  tail : List Request

def OperationalNonemptyRequestTrace.toList
    (trace : OperationalNonemptyRequestTrace I) : List I := trace.head :: trace.tail

structure ExecutedOperationalGrouping (realization : OperationalRealization contract M)
    (left right leftTerminal rightTerminal : S) where
  trace : OperationalNonemptyRequestTrace I
  leftEvents : List E
  leftRun : ExecutedRun contract left trace.toList leftTerminal leftEvents
  rightEvents : List E
  rightRun : ExecutedRun contract right trace.toList rightTerminal rightEvents
  terminalCollision :
    Grouping.Continuation.run realization.reduced.next (realization.project left) trace.toList =
      Grouping.Continuation.run realization.reduced.next (realization.project right) trace.toList

namespace ExecutedOperationalGrouping
variable {realization : OperationalRealization contract M}
  {left right leftTerminal rightTerminal : S}

def requests (grouping :
    ExecutedOperationalGrouping realization left right leftTerminal rightTerminal) : List I :=
  grouping.trace.toList

theorem nonempty (grouping :
    ExecutedOperationalGrouping realization left right leftTerminal rightTerminal) :
    grouping.requests ≠ [] := by
  intro impossible
  cases impossible

def producedMemory (grouping :
    ExecutedOperationalGrouping realization left right leftTerminal rightTerminal) : M :=
  Grouping.Continuation.run realization.reduced.next (realization.project left) grouping.requests

theorem rightProducesMemory (grouping :
    ExecutedOperationalGrouping realization left right leftTerminal rightTerminal) :
    Grouping.Continuation.run realization.reduced.next (realization.project right) grouping.requests =
      grouping.producedMemory := grouping.terminalCollision.symm

def leftReducedAdmitted (grouping :
    ExecutedOperationalGrouping realization left right leftTerminal rightTerminal) :=
  realization.admitted grouping.leftRun.toAdmitted

def rightReducedAdmitted (grouping :
    ExecutedOperationalGrouping realization left right leftTerminal rightTerminal) :=
  realization.admitted grouping.rightRun.toAdmitted

theorem leftTerminalExact (grouping :
    ExecutedOperationalGrouping realization left right leftTerminal rightTerminal) :
    realization.project leftTerminal = grouping.producedMemory :=
  (congrArg realization.project grouping.leftRun.terminal_eq_run).trans
    (realization.run_exact left grouping.requests)

theorem rightTerminalExact (grouping :
    ExecutedOperationalGrouping realization left right leftTerminal rightTerminal) :
    realization.project rightTerminal =
      Grouping.Continuation.run realization.reduced.next (realization.project right)
        grouping.requests :=
  (congrArg realization.project grouping.rightRun.terminal_eq_run).trans
    (realization.run_exact right grouping.requests)

theorem leftEventsExact (grouping :
    ExecutedOperationalGrouping realization left right leftTerminal rightTerminal) :
    grouping.leftEvents = Grouping.Continuation.events realization.reduced.next
      realization.reduced.event (realization.project left) grouping.requests :=
  grouping.leftRun.events_eq_events.trans (realization.events_exact left grouping.requests)

theorem rightEventsExact (grouping :
    ExecutedOperationalGrouping realization left right leftTerminal rightTerminal) :
    grouping.rightEvents = Grouping.Continuation.events realization.reduced.next
      realization.reduced.event (realization.project right) grouping.requests :=
  grouping.rightRun.events_eq_events.trans (realization.events_exact right grouping.requests)

theorem projectedTerminalsEqual (grouping :
    ExecutedOperationalGrouping realization left right leftTerminal rightTerminal) :
    realization.project leftTerminal = realization.project rightTerminal :=
  grouping.leftTerminalExact.trans
    (grouping.terminalCollision.trans grouping.rightTerminalExact.symm)

end ExecutedOperationalGrouping
end ConstitutiveSearch.ContinuationSignatures
/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.ContinuationSignatures.OperationalContract
#print axioms ConstitutiveSearch.ContinuationSignatures.OperationalRealization
#print axioms ConstitutiveSearch.ContinuationSignatures.OperationalRealization.enabled_exact
#print axioms ConstitutiveSearch.ContinuationSignatures.OperationalRealization.run_exact
#print axioms ConstitutiveSearch.ContinuationSignatures.OperationalRealization.events_exact
#print axioms ConstitutiveSearch.ContinuationSignatures.OperationalRealization.admitted
#print axioms ConstitutiveSearch.ContinuationSignatures.OperationalRealization.admittedSource
#print axioms ConstitutiveSearch.ContinuationSignatures.ExactRealization.toOperational
#print axioms ConstitutiveSearch.ContinuationSignatures.OperationalNonemptyRequestTrace
#print axioms ConstitutiveSearch.ContinuationSignatures.OperationalNonemptyRequestTrace.toList
#print axioms ConstitutiveSearch.ContinuationSignatures.ExecutedOperationalGrouping
#print axioms ConstitutiveSearch.ContinuationSignatures.ExecutedOperationalGrouping.requests
#print axioms ConstitutiveSearch.ContinuationSignatures.ExecutedOperationalGrouping.nonempty
#print axioms ConstitutiveSearch.ContinuationSignatures.ExecutedOperationalGrouping.producedMemory
#print axioms ConstitutiveSearch.ContinuationSignatures.ExecutedOperationalGrouping.rightProducesMemory
#print axioms ConstitutiveSearch.ContinuationSignatures.ExecutedOperationalGrouping.leftReducedAdmitted
#print axioms ConstitutiveSearch.ContinuationSignatures.ExecutedOperationalGrouping.rightReducedAdmitted
#print axioms ConstitutiveSearch.ContinuationSignatures.ExecutedOperationalGrouping.leftTerminalExact
#print axioms ConstitutiveSearch.ContinuationSignatures.ExecutedOperationalGrouping.rightTerminalExact
#print axioms ConstitutiveSearch.ContinuationSignatures.ExecutedOperationalGrouping.leftEventsExact
#print axioms ConstitutiveSearch.ContinuationSignatures.ExecutedOperationalGrouping.rightEventsExact
#print axioms ConstitutiveSearch.ContinuationSignatures.ExecutedOperationalGrouping.projectedTerminalsEqual
/- AXIOM_AUDIT_END -/
