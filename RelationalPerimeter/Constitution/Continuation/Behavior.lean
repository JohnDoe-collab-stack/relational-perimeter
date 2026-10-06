import RelationalPerimeter.Constitution.Grouping.ContinuationContract

/-! Independent rich contract: total responses include refused requests and
the final read. Admission evidence remains separate from observations. -/
set_option genInjectivity false
namespace ConstitutiveSearch.ContinuationSignatures
universe u v

structure FutureContract (Source Input : Type u) (Event Observation : Type v) where
  next : Source → Input → Source
  event : Source → Input → Event
  read : Source → Observation
  Allow : Source → Input → Type u
  decision : ∀ source input, PSum (Allow source input) (Allow source input → False)

inductive Outcome (Event Observation : Type v) where
  | stop (read : Observation)
  | step (read : Observation) (allowed : Bool) (event : Event)
      (tail : Outcome Event Observation)
  deriving DecidableEq

variable {S I : Type u} {E O : Type v}

def FutureContract.enabled (contract : FutureContract S I E O) (source : S) (input : I) : Bool :=
  match contract.decision source input with
  | .inl _ => true
  | .inr _ => false

theorem FutureContract.enabled_of_admitted (contract : FutureContract S I E O)
    (source : S) (input : I) (witness : contract.Allow source input) :
    contract.enabled source input = true := by
  unfold enabled
  cases contract.decision source input with
  | inl _ => rfl
  | inr impossible => exact False.elim (impossible witness)

def FutureContract.admissionOfEnabled (contract : FutureContract S I E O)
    (source : S) (input : I) (yes : contract.enabled source input = true) :
    contract.Allow source input := by
  cases chosen : contract.decision source input with
  | inl witness => exact witness
  | inr _ =>
      unfold enabled at yes
      rw [chosen] at yes
      cases yes

def FutureContract.outcome (contract : FutureContract S I E O) : S → List I → Outcome E O
  | source, [] => .stop (contract.read source)
  | source, input :: rest => .step (contract.read source)
      (contract.enabled source input) (contract.event source input)
      (contract.outcome (contract.next source input) rest)

def FutureEquivalent (contract : FutureContract S I E O) (left right : S) : Prop :=
  ∀ requests, contract.outcome left requests = contract.outcome right requests

theorem FutureEquivalent.refl (contract : FutureContract S I E O) (source : S) :
    FutureEquivalent contract source source := fun _ => rfl

theorem FutureEquivalent.symm {contract : FutureContract S I E O} {left right : S}
    (same : FutureEquivalent contract left right) : FutureEquivalent contract right left :=
  fun requests => (same requests).symm

theorem FutureEquivalent.trans {contract : FutureContract S I E O} {left middle right : S}
    (first : FutureEquivalent contract left middle) (second : FutureEquivalent contract middle right) :
    FutureEquivalent contract left right := fun requests => (first requests).trans (second requests)

def Outcome.read : Outcome E O → O
  | .stop value => value
  | .step value _ _ _ => value

def Outcome.tail : Outcome E O → Outcome E O
  | .stop value => .stop value
  | .step _ _ _ rest => rest

def Outcome.right : Outcome E O → Bool
  | .stop _ => false
  | .step _ allowed _ _ => allowed

theorem FutureEquivalent.read {contract : FutureContract S I E O} {left right : S}
    (same : FutureEquivalent contract left right) : contract.read left = contract.read right :=
  congrArg Outcome.read (same [])

theorem FutureEquivalent.enabled {contract : FutureContract S I E O} {left right : S}
    (same : FutureEquivalent contract left right) (input : I) :
    contract.enabled left input = contract.enabled right input :=
  congrArg Outcome.right (same [input])

def FutureEquivalent.admission {contract : FutureContract S I E O} {left right : S}
    (same : FutureEquivalent contract left right) (input : I) (witness : contract.Allow left input) :
    contract.Allow right input :=
  contract.admissionOfEnabled right input
    ((same.enabled input).symm.trans (contract.enabled_of_admitted left input witness))

theorem FutureEquivalent.next {contract : FutureContract S I E O} {left right : S}
    (same : FutureEquivalent contract left right) (input : I) :
    FutureEquivalent contract (contract.next left input) (contract.next right input) :=
  fun requests => congrArg Outcome.tail (same (input :: requests))

end ConstitutiveSearch.ContinuationSignatures
/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.ContinuationSignatures.FutureContract.outcome
#print axioms ConstitutiveSearch.ContinuationSignatures.FutureContract.admissionOfEnabled
#print axioms ConstitutiveSearch.ContinuationSignatures.FutureEquivalent.admission
#print axioms ConstitutiveSearch.ContinuationSignatures.FutureEquivalent.next
/- AXIOM_AUDIT_END -/
