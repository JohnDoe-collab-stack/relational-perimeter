import RelationalPerimeter.Constitution.Continuation.Signature

/-! Minimality is relative to the independently fixed future contract.
The positive coverage used for factorization is not a runtime source archive. -/
set_option genInjectivity false
namespace ConstitutiveSearch.ContinuationSignatures
universe u v
variable {S M I : Type u} {E O : Type v}

structure ExactRealization (contract : FutureContract S I E O) (Memory : Type u) where
  reduced : FutureContract Memory I E O
  project : S → Memory
  forward : ∀ source input, contract.Allow source input → reduced.Allow (project source) input
  backward : ∀ source input, reduced.Allow (project source) input → contract.Allow source input
  backward_forward : ∀ source input witness,
    backward source input (forward source input witness) = witness
  forward_backward : ∀ source input witness,
    forward source input (backward source input witness) = witness
  next_exact : ∀ source input, project (contract.next source input) = reduced.next (project source) input
  event_exact : ∀ source input, contract.event source input = reduced.event (project source) input
  read_exact : ∀ source, contract.read source = reduced.read (project source)

variable {contract : FutureContract S I E O}

def ExactRealization.continuationBridge (realization : ExactRealization contract M) :
    Grouping.Continuation.Exact S M I E O where
  project := realization.project
  sourceNext := contract.next
  reducedNext := realization.reduced.next
  sourceAllow := contract.Allow
  reducedAllow := realization.reduced.Allow
  toReduced := realization.forward
  toSource := realization.backward
  sourceEvent := contract.event
  reducedEvent := realization.reduced.event
  sourceRead := contract.read
  reducedRead := realization.reduced.read
  nextLaw := realization.next_exact
  eventLaw := realization.event_exact
  readLaw := realization.read_exact

theorem ExactRealization.enabled_exact (realization : ExactRealization contract M)
    (source : S) (input : I) :
    contract.enabled source input = realization.reduced.enabled (realization.project source) input := by
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

theorem ExactRealization.outcome_exact (realization : ExactRealization contract M)
    (source : S) (requests : List I) :
    contract.outcome source requests = realization.reduced.outcome (realization.project source) requests := by
  induction requests generalizing source with
  | nil => exact congrArg Outcome.stop (realization.read_exact source)
  | cons input rest ih =>
      change Outcome.step _ _ _ _ = Outcome.step _ _ _ _
      rw [realization.read_exact, realization.enabled_exact, realization.event_exact]
      apply congrArg (Outcome.step _ _ _)
      exact (ih _).trans (congrArg (fun memory => realization.reduced.outcome memory rest)
        (realization.next_exact source input))

theorem ExactRealization.equal_memory_same_futures (realization : ExactRealization contract M)
    {left right : S} (same : realization.project left = realization.project right) :
    FutureEquivalent contract left right := fun requests =>
  (realization.outcome_exact left requests).trans
    ((congrArg (fun memory => realization.reduced.outcome memory requests) same).trans
      (realization.outcome_exact right requests).symm)

theorem minimal_distinctions (basis : FiniteFutureBasis contract)
    (realization : ExactRealization contract M) {left right : S}
    (same : realization.project left = realization.project right) :
    producedSignature basis left = producedSignature basis right :=
  signature_complete basis (realization.equal_memory_same_futures same)

/-- A representative is positively provided only on the covered memory domain. -/
structure PositiveCoverage (realization : ExactRealization contract M) where
  representative : (memory : M) → { source : S // realization.project source = memory }

def recoverSignature (basis : FiniteFutureBasis contract)
    (realization : ExactRealization contract M) (cover : PositiveCoverage realization)
    (memory : M) : List (Outcome E O) := producedSignature basis (cover.representative memory).1

theorem recoverSignature_exact (basis : FiniteFutureBasis contract)
    (realization : ExactRealization contract M) (cover : PositiveCoverage realization) (source : S) :
    recoverSignature basis realization cover (realization.project source) = producedSignature basis source :=
  minimal_distinctions basis realization (cover.representative (realization.project source)).2

end ConstitutiveSearch.ContinuationSignatures
/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.ContinuationSignatures.ExactRealization.continuationBridge
#print axioms ConstitutiveSearch.ContinuationSignatures.ExactRealization.enabled_exact
#print axioms ConstitutiveSearch.ContinuationSignatures.ExactRealization.outcome_exact
#print axioms ConstitutiveSearch.ContinuationSignatures.ExactRealization.equal_memory_same_futures
#print axioms ConstitutiveSearch.ContinuationSignatures.minimal_distinctions
#print axioms ConstitutiveSearch.ContinuationSignatures.recoverSignature
#print axioms ConstitutiveSearch.ContinuationSignatures.recoverSignature_exact
/- AXIOM_AUDIT_END -/
