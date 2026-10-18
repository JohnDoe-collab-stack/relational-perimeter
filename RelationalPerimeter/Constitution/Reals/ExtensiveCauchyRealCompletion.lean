import RelationalPerimeter.Constitution.Reals.ExtensiveCauchyReal
import RelationalPerimeter.Constitution.Reals.RegularDyadicCompletion

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace RelationalPerimeter.Constitution.Reals.ExtensiveCauchyReal
open PresentedDyadicCompletion RegularDyadicCompletion

structure ExternalPresentedFamily where
  terms : Nat → Value
  name : (n : Nat) → RegularDyadicName
  member : (n : Nat) → (terms n).Contains (name n)
  modulus : Nat → Nat
  modulusMonotone : {p q : Nat} → PrecisionExtension p q → PrecisionExtension (modulus p) (modulus q)
  cauchy : (p n m r s : Nat) → PrecisionExtension (modulus p) n → PrecisionExtension (modulus p) m →
    PrecisionExtension p r → PrecisionExtension p s →
    Near p ((name n).approximation r) ((name m).approximation s)

structure ExternalConverges (family : ExternalPresentedFamily) (value : Value) where
  candidateName : RegularDyadicName
  candidateMember : value.Contains candidateName
  threshold : Nat → Nat
  near : (p n r s : Nat) → PrecisionExtension (family.modulus p) n → PrecisionExtension p r →
    PrecisionExtension (threshold p) s →
    Near p ((family.name n).approximation r) (candidateName.approximation s)

structure ExternalLimitResult (family : ExternalPresentedFamily) where
  value : Value
  convergence : ExternalConverges family value
  unique : {other : Value} → ExternalConverges family other → ExternalEquivalent value other

/-- Exact structural copy into the identity-modulus reference contract. -/
def referenceFamily (family : ExternalPresentedFamily) : PresentedFamily regularPresentedCore where
  terms := family.name
  modulus := family.modulus
  modulusMonotone := family.modulusMonotone
  cauchy p n m r s hn hm hr hs := family.cauchy p n m r s hn hm hr hs

def externalConvergenceFromReference (family : ExternalPresentedFamily)
    (produced : LimitResult regularPresentedCore (referenceFamily family)) :
    ExternalConverges family (classOf produced.value) where
  candidateName := produced.value
  candidateMember := classOfContains produced.value
  threshold := produced.convergence.threshold
  near := produced.convergence.near

def externalUniquenessFromReference (family : ExternalPresentedFamily)
    (produced : LimitResult regularPresentedCore (referenceFamily family)) {other : Value}
    (convergence : ExternalConverges family other) : ExternalEquivalent (classOf produced.value) other :=
  (classOfPreserves (produced.unique convergence.candidateName
    ⟨convergence.threshold, convergence.near⟩)).trans
    (memberClassEquivalent other convergence.candidateName convergence.candidateMember)

/-- One reference completion production supplies the class and all its laws. -/
def externalComplete (family : ExternalPresentedFamily) : ExternalLimitResult family :=
  let produced := regularPresentedCompletion.complete (referenceFamily family)
  { value := classOf produced.value
    convergence := externalConvergenceFromReference family produced
    unique := externalUniquenessFromReference family produced }

theorem referenceFamilyNamesExact (family : ExternalPresentedFamily) (n : Nat) :
    (referenceFamily family).terms n = family.name n := rfl
theorem referenceFamilyModulusExact (family : ExternalPresentedFamily) (p : Nat) :
    (referenceFamily family).modulus p = family.modulus p := rfl
theorem externalCompleteExact (family : ExternalPresentedFamily) :
    (externalComplete family).value =
      classOf ((regularPresentedCompletion.complete (referenceFamily family)).value) := rfl
theorem externalCandidateExact (family : ExternalPresentedFamily) :
    (externalComplete family).convergence.candidateName =
      (regularPresentedCompletion.complete (referenceFamily family)).value := rfl

end RelationalPerimeter.Constitution.Reals.ExtensiveCauchyReal

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Constitution.Reals.ExtensiveCauchyReal.ExternalPresentedFamily
#print axioms RelationalPerimeter.Constitution.Reals.ExtensiveCauchyReal.ExternalConverges
#print axioms RelationalPerimeter.Constitution.Reals.ExtensiveCauchyReal.ExternalLimitResult
#print axioms RelationalPerimeter.Constitution.Reals.ExtensiveCauchyReal.referenceFamily
#print axioms RelationalPerimeter.Constitution.Reals.ExtensiveCauchyReal.externalConvergenceFromReference
#print axioms RelationalPerimeter.Constitution.Reals.ExtensiveCauchyReal.externalUniquenessFromReference
#print axioms RelationalPerimeter.Constitution.Reals.ExtensiveCauchyReal.externalComplete
#print axioms RelationalPerimeter.Constitution.Reals.ExtensiveCauchyReal.referenceFamilyNamesExact
#print axioms RelationalPerimeter.Constitution.Reals.ExtensiveCauchyReal.referenceFamilyModulusExact
#print axioms RelationalPerimeter.Constitution.Reals.ExtensiveCauchyReal.externalCompleteExact
#print axioms RelationalPerimeter.Constitution.Reals.ExtensiveCauchyReal.externalCandidateExact
/- AXIOM_AUDIT_END -/
