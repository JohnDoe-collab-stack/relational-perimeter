import RelationalPerimeter.Computation.ProducedState

/-!
# Feedback through the exact produced state

One feedback step reconstructs from its current state and then produces the
state supplied to the next step.  Iteration is structural recursion on the
number of steps; its recursive call receives the exact output of the head.
-/

namespace RelationalPerimeter.Computation

universe u

/-- One reconstruction-and-production step on a state carrier. -/
structure FeedbackStep (State : Type u) where
  Reconstruction : State → Type u
  reconstruct : (state : State) → Reconstruction state
  produceNext : (state : State) → Reconstruction state → State

namespace FeedbackStep

/-- State produced by one complete feedback step. -/
def next
    {State : Type u}
    (step : FeedbackStep State)
    (state : State) : State :=
  step.produceNext state (step.reconstruct state)

/-- Iterate by feeding each produced state to the next reconstruction. -/
def iterate
    {State : Type u}
    (step : FeedbackStep State) : Nat → State → State
  | 0, state => state
  | count + 1, state => step.iterate count (step.next state)

/-- The successor equation exposes the exact feedback dependency. -/
theorem iterate_succ
    {State : Type u}
    (step : FeedbackStep State)
    (count : Nat)
    (state : State) :
    step.iterate (count + 1) state =
      step.iterate count (step.next state) :=
  rfl

/-- Two steps reconstruct the second step from the state produced by the first. -/
theorem iterate_two
    {State : Type u}
    (step : FeedbackStep State)
    (state : State) :
    step.iterate 2 state = step.next (step.next state) :=
  rfl

end FeedbackStep
end RelationalPerimeter.Computation

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Computation.FeedbackStep
#print axioms RelationalPerimeter.Computation.FeedbackStep.next
#print axioms RelationalPerimeter.Computation.FeedbackStep.iterate
#print axioms RelationalPerimeter.Computation.FeedbackStep.iterate_succ
#print axioms RelationalPerimeter.Computation.FeedbackStep.iterate_two
/- AXIOM_AUDIT_END -/
