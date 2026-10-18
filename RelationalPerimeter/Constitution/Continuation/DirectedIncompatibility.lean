import Init

/-! Constructive endpoint incompatibilities.  This logical layer knows
nothing about executions, memories or diagonal applications. -/
set_option autoImplicit false
set_option genInjectivity false
namespace ConstitutiveSearch.ContinuationSignatures

universe uP uQ

structure BilateralNegationCertificate (P : Type uP) (Q : Type uQ) where
  forward : P → Q → Empty
  backward : (Q → Empty) → P

def rejectDirectedTransport
    {P : Type uP} {Q : Type uQ}
    (transport : P → Q)
    (sourceWitness : P)
    (rejectTarget : Q → Empty) : Empty :=
  rejectTarget (transport sourceWitness)

def rejectBilateralTransport
    {P : Type uP} {Q : Type uQ}
    (leftToRight : P → Q)
    (rightToLeft : Q → P)
    (certificate : BilateralNegationCertificate P Q) : Empty := by
  let rejectRight : Q → Empty := fun right =>
    certificate.forward (rightToLeft right) right
  let left : P := certificate.backward rejectRight
  exact rejectRight (leftToRight left)

end ConstitutiveSearch.ContinuationSignatures
/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.ContinuationSignatures.BilateralNegationCertificate
#print axioms ConstitutiveSearch.ContinuationSignatures.rejectDirectedTransport
#print axioms ConstitutiveSearch.ContinuationSignatures.rejectBilateralTransport
/- AXIOM_AUDIT_END -/
