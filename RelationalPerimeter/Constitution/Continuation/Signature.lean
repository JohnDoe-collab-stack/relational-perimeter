import RelationalPerimeter.Constitution.Continuation.FiniteBasis

set_option genInjectivity false
namespace ConstitutiveSearch.ContinuationSignatures
universe u v
variable {S I : Type u} {E O : Type v} {contract : FutureContract S I E O}

/-- Comparable data contains only evaluated outcomes, not its formation proof. -/
def producedSignature (basis : FiniteFutureBasis contract) (source : S) : List (Outcome E O) :=
  evaluateTests contract basis.tests source

theorem signature_sound (basis : FiniteFutureBasis contract) {left right : S}
    (same : producedSignature basis left = producedSignature basis right) :
    FutureEquivalent contract left right :=
  basis.complete left right (evaluateTests_at contract basis.tests same)

theorem signature_complete (basis : FiniteFutureBasis contract) {left right : S}
    (same : FutureEquivalent contract left right) :
    producedSignature basis left = producedSignature basis right :=
  evaluateTests_eq contract basis.tests (fun requests _ => same requests)

theorem signature_exact (basis : FiniteFutureBasis contract) (left right : S) :
    producedSignature basis left = producedSignature basis right ↔ FutureEquivalent contract left right :=
  ⟨signature_sound basis, signature_complete basis⟩

def separate [DecidableEq E] [DecidableEq O] (basis : FiniteFutureBasis contract)
    (left right : S) (different : producedSignature basis left ≠ producedSignature basis right) :
    FutureSeparator contract left right := separateTests contract left right basis.tests different

theorem signature_stable (basis : FiniteFutureBasis contract) {left right : S}
    (same : producedSignature basis left = producedSignature basis right) (request : I) :
    producedSignature basis (contract.next left request) =
      producedSignature basis (contract.next right request) :=
  signature_complete basis ((signature_sound basis same).next request)

end ConstitutiveSearch.ContinuationSignatures
/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.ContinuationSignatures.producedSignature
#print axioms ConstitutiveSearch.ContinuationSignatures.signature_sound
#print axioms ConstitutiveSearch.ContinuationSignatures.signature_complete
#print axioms ConstitutiveSearch.ContinuationSignatures.signature_exact
#print axioms ConstitutiveSearch.ContinuationSignatures.separate
#print axioms ConstitutiveSearch.ContinuationSignatures.signature_stable
/- AXIOM_AUDIT_END -/
