import RelationalPerimeter.Constitution.Continuation.Execution
import RelationalPerimeter.Constitution.Continuation.Minimality

/-! Executed grouping under a fixed exact realization. The common memory is
the computed left output, not an additional supplied object. -/
set_option genInjectivity false
namespace ConstitutiveSearch.ContinuationSignatures
universe u v
variable {S I M : Type u} {E O : Type v}

def identityRealization (contract : FutureContract S I E O) : ExactRealization contract S where
  reduced := contract
  project := id
  forward := fun _ _ witness => witness
  backward := fun _ _ witness => witness
  backward_forward := fun _ _ _ => rfl
  forward_backward := fun _ _ _ => rfl
  next_exact := fun _ _ => rfl
  event_exact := fun _ _ => rfl
  read_exact := fun _ => rfl

structure NonemptyRequestTrace (Request : Type u) where
  head : Request
  tail : List Request

def NonemptyRequestTrace.toList (trace : NonemptyRequestTrace I) : List I :=
  trace.head :: trace.tail

structure ExecutedCommonMemoryGrouping {contract : FutureContract S I E O}
    (realization : ExactRealization contract M) (left right : S) where
  trace : NonemptyRequestTrace I
  leftTerminal : S
  leftEvents : List E
  leftRun : ExecutedRun contract left trace.toList leftTerminal leftEvents
  rightTerminal : S
  rightEvents : List E
  rightRun : ExecutedRun contract right trace.toList rightTerminal rightEvents
  terminalCollision :
    Grouping.Continuation.run realization.reduced.next (realization.project left) trace.toList =
      Grouping.Continuation.run realization.reduced.next (realization.project right) trace.toList

namespace ExecutedCommonMemoryGrouping
variable {contract : FutureContract S I E O} {realization : ExactRealization contract M}
  {left right : S}

def requests (grouping : ExecutedCommonMemoryGrouping realization left right) : List I :=
  grouping.trace.toList

theorem nonempty (grouping : ExecutedCommonMemoryGrouping realization left right) :
    grouping.requests ≠ [] := by
  intro impossible
  cases impossible

def producedMemory (grouping : ExecutedCommonMemoryGrouping realization left right) : M :=
  Grouping.Continuation.run realization.reduced.next (realization.project left) grouping.requests

theorem rightProducesMemory (grouping : ExecutedCommonMemoryGrouping realization left right) :
    Grouping.Continuation.run realization.reduced.next (realization.project right) grouping.requests =
      grouping.producedMemory := grouping.terminalCollision.symm

def leftReducedAdmitted (grouping : ExecutedCommonMemoryGrouping realization left right) :=
  realization.continuationBridge.admitted grouping.leftRun.toAdmitted

def rightReducedAdmitted (grouping : ExecutedCommonMemoryGrouping realization left right) :=
  realization.continuationBridge.admitted grouping.rightRun.toAdmitted

theorem leftTerminalExact (grouping : ExecutedCommonMemoryGrouping realization left right) :
    realization.project grouping.leftTerminal = grouping.producedMemory :=
  (congrArg realization.project grouping.leftRun.terminal_eq_run).trans
    (realization.continuationBridge.run_exact left grouping.requests)

theorem rightTerminalExact (grouping : ExecutedCommonMemoryGrouping realization left right) :
    realization.project grouping.rightTerminal =
      Grouping.Continuation.run realization.reduced.next (realization.project right) grouping.requests :=
  (congrArg realization.project grouping.rightRun.terminal_eq_run).trans
    (realization.continuationBridge.run_exact right grouping.requests)

theorem leftEventsExact (grouping : ExecutedCommonMemoryGrouping realization left right) :
    grouping.leftEvents = Grouping.Continuation.events realization.reduced.next
      realization.reduced.event (realization.project left) grouping.requests :=
  grouping.leftRun.events_eq_events.trans
    (realization.continuationBridge.events_exact left grouping.requests)

theorem rightEventsExact (grouping : ExecutedCommonMemoryGrouping realization left right) :
    grouping.rightEvents = Grouping.Continuation.events realization.reduced.next
      realization.reduced.event (realization.project right) grouping.requests :=
  grouping.rightRun.events_eq_events.trans
    (realization.continuationBridge.events_exact right grouping.requests)

theorem projectedTerminalsEqual (grouping : ExecutedCommonMemoryGrouping realization left right) :
    realization.project grouping.leftTerminal = realization.project grouping.rightTerminal :=
  grouping.leftTerminalExact.trans
    (grouping.terminalCollision.trans grouping.rightTerminalExact.symm)

theorem terminalReadEqual (grouping : ExecutedCommonMemoryGrouping realization left right) :
    contract.read grouping.leftTerminal = contract.read grouping.rightTerminal :=
  (realization.read_exact grouping.leftTerminal).trans
    ((congrArg realization.reduced.read grouping.projectedTerminalsEqual).trans
      (realization.read_exact grouping.rightTerminal).symm)

theorem terminalFutureEquivalent (grouping : ExecutedCommonMemoryGrouping realization left right) :
    FutureEquivalent contract grouping.leftTerminal grouping.rightTerminal :=
  realization.equal_memory_same_futures grouping.projectedTerminalsEqual
end ExecutedCommonMemoryGrouping

end ConstitutiveSearch.ContinuationSignatures
/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.ContinuationSignatures.identityRealization
#print axioms ConstitutiveSearch.ContinuationSignatures.NonemptyRequestTrace
#print axioms ConstitutiveSearch.ContinuationSignatures.NonemptyRequestTrace.toList
#print axioms ConstitutiveSearch.ContinuationSignatures.ExecutedCommonMemoryGrouping
#print axioms ConstitutiveSearch.ContinuationSignatures.ExecutedCommonMemoryGrouping.requests
#print axioms ConstitutiveSearch.ContinuationSignatures.ExecutedCommonMemoryGrouping.nonempty
#print axioms ConstitutiveSearch.ContinuationSignatures.ExecutedCommonMemoryGrouping.producedMemory
#print axioms ConstitutiveSearch.ContinuationSignatures.ExecutedCommonMemoryGrouping.rightProducesMemory
#print axioms ConstitutiveSearch.ContinuationSignatures.ExecutedCommonMemoryGrouping.leftReducedAdmitted
#print axioms ConstitutiveSearch.ContinuationSignatures.ExecutedCommonMemoryGrouping.rightReducedAdmitted
#print axioms ConstitutiveSearch.ContinuationSignatures.ExecutedCommonMemoryGrouping.leftTerminalExact
#print axioms ConstitutiveSearch.ContinuationSignatures.ExecutedCommonMemoryGrouping.rightTerminalExact
#print axioms ConstitutiveSearch.ContinuationSignatures.ExecutedCommonMemoryGrouping.leftEventsExact
#print axioms ConstitutiveSearch.ContinuationSignatures.ExecutedCommonMemoryGrouping.rightEventsExact
#print axioms ConstitutiveSearch.ContinuationSignatures.ExecutedCommonMemoryGrouping.projectedTerminalsEqual
#print axioms ConstitutiveSearch.ContinuationSignatures.ExecutedCommonMemoryGrouping.terminalReadEqual
#print axioms ConstitutiveSearch.ContinuationSignatures.ExecutedCommonMemoryGrouping.terminalFutureEquivalent
/- AXIOM_AUDIT_END -/
