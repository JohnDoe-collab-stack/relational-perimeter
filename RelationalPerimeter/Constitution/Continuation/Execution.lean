import RelationalPerimeter.Constitution.Continuation.Behavior

/-! Authorized execution of the independently fixed continuation contract.
Targets and events are computed, never received as step fields. -/
set_option genInjectivity false
namespace ConstitutiveSearch.ContinuationSignatures
universe u v
variable {S I : Type u} {E O : Type v}

structure ExecutedStep (contract : FutureContract S I E O) (source : S) (input : I) where
  authorized : contract.Allow source input

def ExecutedStep.target {contract : FutureContract S I E O} {source : S} {input : I}
    (_step : ExecutedStep contract source input) : S := contract.next source input

def ExecutedStep.producedEvent {contract : FutureContract S I E O} {source : S} {input : I}
    (_step : ExecutedStep contract source input) : E := contract.event source input

def perform (contract : FutureContract S I E O) (source : S) (input : I)
    (authorized : contract.Allow source input) : ExecutedStep contract source input :=
  ⟨authorized⟩

inductive ExecutedRun (contract : FutureContract S I E O) :
    S → List I → S → List E → Type (max u v) where
  | nil (source : S) : ExecutedRun contract source [] source []
  | cons {source : S} {input : I} {rest : List I} {terminal : S} {events : List E}
      (step : ExecutedStep contract source input)
      (tail : ExecutedRun contract step.target rest terminal events) :
      ExecutedRun contract source (input :: rest) terminal (step.producedEvent :: events)

namespace ExecutedRun
variable {contract : FutureContract S I E O} {source terminal : S}
  {requests : List I} {events : List E}

theorem terminal_eq_run (execution : ExecutedRun contract source requests terminal events) :
    terminal = Grouping.Continuation.run contract.next source requests := by
  induction execution with
  | nil => rfl
  | cons step tail ih => exact ih

theorem events_eq_events (execution : ExecutedRun contract source requests terminal events) :
    events = Grouping.Continuation.events contract.next contract.event source requests := by
  induction execution with
  | nil => rfl
  | cons step tail ih => exact congrArg (List.cons step.producedEvent) ih

def toAdmitted {source terminal : S} {requests : List I} {events : List E}
    (execution : ExecutedRun contract source requests terminal events) :
    Grouping.Continuation.Admitted contract.next contract.Allow source requests :=
  match execution with
  | .nil source => .nil source
  | .cons step tail => .cons step.authorized (toAdmitted tail)
termination_by structural execution
end ExecutedRun

/-- An accessible state retains the complete authorized run as its index. -/
structure ReachableRuntime (contract : FutureContract S I E O) (initial : S) where
  requests : List I
  terminal : S
  events : List E
  execution : ExecutedRun contract initial requests terminal events

end ConstitutiveSearch.ContinuationSignatures
/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.ContinuationSignatures.ExecutedStep
#print axioms ConstitutiveSearch.ContinuationSignatures.ExecutedStep.target
#print axioms ConstitutiveSearch.ContinuationSignatures.ExecutedStep.producedEvent
#print axioms ConstitutiveSearch.ContinuationSignatures.perform
#print axioms ConstitutiveSearch.ContinuationSignatures.ExecutedRun
#print axioms ConstitutiveSearch.ContinuationSignatures.ExecutedRun.terminal_eq_run
#print axioms ConstitutiveSearch.ContinuationSignatures.ExecutedRun.events_eq_events
#print axioms ConstitutiveSearch.ContinuationSignatures.ExecutedRun.toAdmitted
#print axioms ConstitutiveSearch.ContinuationSignatures.ReachableRuntime
/- AXIOM_AUDIT_END -/
