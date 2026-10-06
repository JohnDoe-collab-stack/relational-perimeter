import RelationalPerimeter.Constitution.Continuation.Behavior

/-! A generic finite-basis interface is conditional. Concrete instances must
construct its completeness proof against the independent future contract. -/
set_option genInjectivity false
namespace ConstitutiveSearch.ContinuationSignatures
universe u v
variable {S I : Type u} {E O : Type v}

def TestAgreement (contract : FutureContract S I E O) (tests : List (List I))
    (left right : S) : Prop :=
  ∀ requests, requests ∈ tests → contract.outcome left requests = contract.outcome right requests

structure FiniteFutureBasis (contract : FutureContract S I E O) where
  tests : List (List I)
  complete : ∀ left right, TestAgreement contract tests left right → FutureEquivalent contract left right

def evaluateTests (contract : FutureContract S I E O) (tests : List (List I))
    (source : S) : List (Outcome E O) := tests.map (contract.outcome source)

theorem evaluateTests_eq (contract : FutureContract S I E O) (tests : List (List I))
    {left right : S} (agree : TestAgreement contract tests left right) :
    evaluateTests contract tests left = evaluateTests contract tests right := by
  induction tests with
  | nil => rfl
  | cons request rest ih =>
      change _ :: _ = _ :: _
      rw [agree request (.head _)]
      exact congrArg (List.cons _) (ih (fun q member => agree q (.tail _ member)))

theorem evaluateTests_at (contract : FutureContract S I E O) (tests : List (List I))
    {left right : S} (same : evaluateTests contract tests left = evaluateTests contract tests right) :
    TestAgreement contract tests left right := by
  induction tests with
  | nil => intro _ impossible; cases impossible
  | cons request rest ih =>
      intro q member
      cases member with
      | head =>
          exact Option.some.inj (congrArg List.head? same)
      | tail _ member => exact ih (congrArg List.tail same) q member

structure FutureSeparator (contract : FutureContract S I E O) (left right : S) where
  requests : List I
  different : contract.outcome left requests ≠ contract.outcome right requests

/-- Structural search; the returned witness is a real request of the contract. -/
def separateTests [DecidableEq E] [DecidableEq O]
    (contract : FutureContract S I E O) (left right : S) :
    (tests : List (List I)) →
    evaluateTests contract tests left ≠ evaluateTests contract tests right →
    FutureSeparator contract left right
  | [], impossible => False.elim (impossible rfl)
  | requests :: rest, different =>
      if same : contract.outcome left requests = contract.outcome right requests then
        separateTests contract left right rest (fun tailSame => different
          ((congrArg (fun head => head :: evaluateTests contract rest left) same).trans
            (congrArg (List.cons (contract.outcome right requests)) tailSame)))
      else ⟨requests, same⟩

theorem FutureSeparator.not_equivalent {contract : FutureContract S I E O} {left right : S}
    (separator : FutureSeparator contract left right) : ¬ FutureEquivalent contract left right :=
  fun same => separator.different (same separator.requests)

end ConstitutiveSearch.ContinuationSignatures
/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.ContinuationSignatures.evaluateTests
#print axioms ConstitutiveSearch.ContinuationSignatures.evaluateTests_eq
#print axioms ConstitutiveSearch.ContinuationSignatures.evaluateTests_at
#print axioms ConstitutiveSearch.ContinuationSignatures.separateTests
#print axioms ConstitutiveSearch.ContinuationSignatures.FutureSeparator.not_equivalent
/- AXIOM_AUDIT_END -/
