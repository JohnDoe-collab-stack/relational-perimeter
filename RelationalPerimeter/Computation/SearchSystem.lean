import Init

/-!
# Structural continuations and an explicit criterion

This module separates the type of structurally available continuations from
the proposition used to evaluate them.  No decidability, viability, relation
between states, or search procedure is included in the primitive interface.
-/

namespace RelationalPerimeter.Computation

universe u

/--
A search system keeps structural continuations distinct from the criterion
that some of those continuations satisfy.
-/
structure SearchSystem where
  State : Type u
  Continuation : State → Type u
  Criterion : (state : State) → Continuation state → Prop

namespace SearchSystem

/-- A state is viable when it has a continuation satisfying the criterion. -/
def Viable
    (system : SearchSystem)
    (state : system.State) : Prop :=
  ∃ continuation : system.Continuation state,
    system.Criterion state continuation

/--
The proof-relevant type of criterion-satisfying continuations.  It is derived
from the structural continuation type and is not the primitive carrier.
-/
def AcceptedContinuation
    (system : SearchSystem)
    (state : system.State) : Type u :=
  { continuation : system.Continuation state //
      system.Criterion state continuation }

/-- Viability is precisely inhabitation of the derived accepted carrier. -/
theorem viable_iff_nonempty_accepted
    (system : SearchSystem)
    (state : system.State) :
    system.Viable state ↔
      Nonempty (system.AcceptedContinuation state) := by
  constructor
  · intro viable
    rcases viable with ⟨continuation, accepted⟩
    exact ⟨⟨continuation, accepted⟩⟩
  · intro inhabited
    rcases inhabited with ⟨accepted⟩
    exact ⟨accepted.1, accepted.2⟩

end SearchSystem
end RelationalPerimeter.Computation

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Computation.SearchSystem
#print axioms RelationalPerimeter.Computation.SearchSystem.Viable
#print axioms RelationalPerimeter.Computation.SearchSystem.AcceptedContinuation
#print axioms RelationalPerimeter.Computation.SearchSystem.viable_iff_nonempty_accepted
/- AXIOM_AUDIT_END -/
