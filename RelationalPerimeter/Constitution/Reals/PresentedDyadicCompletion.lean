import RelationalPerimeter.Constitution.Reals.RelationalRealCarrierCompleteness
import RelationalPerimeter.Constitution.Reals.RelationalRealMultiplicativeLaws

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# A non-circular contract for presented dyadic completion

The core receives codes, moduli and positive laws. No terminal comparison map
is received. Numerical carriers and all presentation families are derived.
-/
namespace RelationalPerimeter.Constitution.Reals.PresentedDyadicCompletion
open StrongPerimetralTurning ProducedCompleteness RuntimeCorrespondence
open RelationalRealCarrierCompleteness RelationalRealFamilyTransport

structure PresentedDyadicData where
  Carrier : Type
  approximation : Carrier → Nat → SignedDyadicCode
  modulus : Carrier → Nat → Nat
  modulusMonotone : (x : Carrier) → {p q : Nat} → PrecisionExtension p q →
    PrecisionExtension (modulus x p) (modulus x q)
  coherent : (x : Carrier) → (p r s : Nat) →
    PrecisionExtension (modulus x p) r → PrecisionExtension (modulus x p) s →
    Near p (approximation x r) (approximation x s)
  dyadic : SignedDyadicCode → Carrier
  dyadicExact : (code : SignedDyadicCode) → (r : Nat) →
    SameValue (approximation (dyadic code) r) code

structure ApproxEquivalent (D : PresentedDyadicData) (x y : D.Carrier) where
  firstThreshold : Nat → Nat
  secondThreshold : Nat → Nat
  near : (p r s : Nat) → PrecisionExtension (firstThreshold p) r →
    PrecisionExtension (secondThreshold p) s →
    Near p (D.approximation x r) (D.approximation y s)

structure PresentedDyadicStructure extends PresentedDyadicData where
  Equivalent : Carrier → Carrier → Type
  equivalentRefl : (x : Carrier) → Equivalent x x
  equivalentSymm : {x y : Carrier} → Equivalent x y → Equivalent y x
  equivalentTrans : {x y z : Carrier} → Equivalent x y → Equivalent y z → Equivalent x z
  toApprox : {x y : Carrier} → Equivalent x y → ApproxEquivalent toPresentedDyadicData x y
  fromApprox : {x y : Carrier} → ApproxEquivalent toPresentedDyadicData x y → Equivalent x y

structure PresentedFamily (C : PresentedDyadicStructure) where
  terms : Nat → C.Carrier
  modulus : Nat → Nat
  modulusMonotone : {p q : Nat} → PrecisionExtension p q →
    PrecisionExtension (modulus p) (modulus q)
  cauchy : (p n m r s : Nat) →
    PrecisionExtension (modulus p) n → PrecisionExtension (modulus p) m →
    PrecisionExtension (C.modulus (terms n) p) r → PrecisionExtension (C.modulus (terms m) p) s →
    Near p (C.approximation (terms n) r) (C.approximation (terms m) s)

structure Converges (C : PresentedDyadicStructure) (family : PresentedFamily C) (value : C.Carrier) where
  threshold : Nat → Nat
  near : (p n r s : Nat) →
    PrecisionExtension (family.modulus p) n → PrecisionExtension p r →
    PrecisionExtension (threshold p) s →
    Near p (C.approximation (family.terms n) (C.modulus (family.terms n) r))
      (C.approximation value (C.modulus value s))

structure LimitResult (C : PresentedDyadicStructure) (family : PresentedFamily C) where
  value : C.Carrier
  convergence : Converges C family value
  unique : (other : C.Carrier) → Converges C family other → C.Equivalent value other

structure PresentedDyadicCompletion (C : PresentedDyadicStructure) where
  complete : (family : PresentedFamily C) → LimitResult C family

structure PresentedDyadicCompletionObject where
  core : PresentedDyadicStructure
  completion : PresentedDyadicCompletion core

/-- Only the four received numerical fields constitute this derived carrier. -/
def numericalCarrier (C : PresentedDyadicData) (x : C.Carrier) : EffectiveCauchyReal.Carrier where
  approximation := C.approximation x
  modulus := C.modulus x
  modulusMonotone := C.modulusMonotone x
  cauchy := C.coherent x

def approxToCarrier {C : PresentedDyadicData} {x y : C.Carrier} (same : ApproxEquivalent C x y) :
    EffectiveCauchyReal.Equivalent (numericalCarrier C x) (numericalCarrier C y) :=
  ⟨same.firstThreshold, same.secondThreshold, same.near⟩

def carrierToApprox {C : PresentedDyadicData} {x y : C.Carrier}
    (same : EffectiveCauchyReal.Equivalent (numericalCarrier C x) (numericalCarrier C y)) :
    ApproxEquivalent C x y := ⟨same.firstThreshold, same.secondThreshold, same.near⟩

def equivalentToCarrier {C : PresentedDyadicStructure} {x y : C.Carrier} (same : C.Equivalent x y) :
    EffectiveCauchyReal.Equivalent (numericalCarrier C.toPresentedDyadicData x)
      (numericalCarrier C.toPresentedDyadicData y) := approxToCarrier (C.toApprox same)

def carrierToEquivalent {C : PresentedDyadicStructure} {x y : C.Carrier}
    (same : EffectiveCauchyReal.Equivalent (numericalCarrier C.toPresentedDyadicData x)
      (numericalCarrier C.toPresentedDyadicData y)) : C.Equivalent x y :=
  C.fromApprox (carrierToApprox same)

def presentCarrierFamily (C : PresentedDyadicStructure) (x : EffectiveCauchyReal.Carrier) :
    PresentedFamily C where
  terms n := C.dyadic (x.approximation n)
  modulus := x.modulus
  modulusMonotone := x.modulusMonotone
  cauchy p n m r s hn hm hr hs :=
    Near.ofSameLeft (C.dyadicExact _ _)
      (Near.ofSameRight (x.cauchy p n m hn hm) (C.dyadicExact _ _).symm)

def ownFamily (C : PresentedDyadicStructure) (x : C.Carrier) : PresentedFamily C :=
  presentCarrierFamily C (numericalCarrier C.toPresentedDyadicData x)

def selfConvergence (C : PresentedDyadicStructure) (x : C.Carrier) : Converges C (ownFamily C x) x where
  threshold p := p
  near p n r s hn hr hs :=
    Near.ofSameLeft (C.dyadicExact _ _)
      (C.coherent x p n (C.modulus x s) hn (C.modulusMonotone x hs))

/-- The extra bit pays for the coherent comparison of the intermediate
normalized value with the arbitrary raw value reply. Both thresholds matter. -/
def presentedCarrierEquivalent (C : PresentedDyadicStructure)
    (x : EffectiveCauchyReal.Carrier) (y : C.Carrier)
    (convergence : Converges C (presentCarrierFamily C x) y) :
    EffectiveCauchyReal.Equivalent (numericalCarrier C.toPresentedDyadicData y) x where
  firstThreshold p := C.modulus y (p + 1)
  secondThreshold p := x.modulus (p + 1)
  near := by
    intro p r s hr hs
    let response := (p + 1) + convergence.threshold (p + 1)
    have close := convergence.near (p + 1) s (p + 1) response hs (.refl _)
      (PrecisionExtension.second _ _)
    have exactClose := Near.ofSameLeft (C.dyadicExact _ _).symm close
    have coherent := C.coherent y (p + 1) r (C.modulus y response) hr
      (C.modulusMonotone y (PrecisionExtension.first _ _))
    exact Near.compose coherent exactClose.symm

def diagonalTransportFamily (Source Target : PresentedDyadicStructure)
    (family : PresentedFamily Source) : PresentedFamily Target where
  terms n := Target.dyadic
    (Source.approximation (family.terms n) (Source.modulus (family.terms n) n))
  modulus p := Nat.succ p + family.modulus (Nat.succ p)
  modulusMonotone extension := extension.succ.add (family.modulusMonotone extension.succ)
  cauchy := by
    intro p n m r s hn hm hr hs
    have hnFine := (PrecisionExtension.first _ _).trans hn
    have hmFine := (PrecisionExtension.first _ _).trans hm
    have hnFamily := (PrecisionExtension.second _ _).trans hn
    have hmFamily := (PrecisionExtension.second _ _).trans hm
    have close := family.cauchy (Nat.succ p) n m
      (Source.modulus (family.terms n) n) (Source.modulus (family.terms m) m)
      hnFamily hmFamily (Source.modulusMonotone _ hnFine) (Source.modulusMonotone _ hmFine)
    exact Near.ofSameLeft (Target.dyadicExact _ _)
      (Near.ofSameRight (close.weaken (PrecisionExtension.next p)) (Target.dyadicExact _ _).symm)

def dyadicCarrier (code : SignedDyadicCode) : EffectiveCauchyReal.Carrier :=
  EffectiveCauchyReal.ofPresentation (EffectiveDyadicPresentation.constant code)

def carrierPresentedCore : PresentedDyadicStructure where
  Carrier := EffectiveCauchyReal.Carrier
  approximation := EffectiveCauchyReal.Carrier.approximation
  modulus := EffectiveCauchyReal.Carrier.modulus
  modulusMonotone := EffectiveCauchyReal.Carrier.modulusMonotone
  coherent := EffectiveCauchyReal.Carrier.cauchy
  dyadic := dyadicCarrier
  dyadicExact := EffectiveDyadicPresentation.constantApproximationSameValue
  Equivalent := EffectiveCauchyReal.Equivalent
  equivalentRefl := EffectiveCauchyReal.Equivalent.refl
  equivalentSymm := EffectiveCauchyReal.Equivalent.symm
  equivalentTrans := EffectiveCauchyReal.Equivalent.trans
  toApprox same := ⟨same.firstThreshold, same.secondThreshold, same.near⟩
  fromApprox same := ⟨same.firstThreshold, same.secondThreshold, same.near⟩

def asCarrierFamily (family : PresentedFamily carrierPresentedCore) : CarrierFamily :=
  ⟨family.terms, family.modulus, family.modulusMonotone, family.cauchy⟩

def carrierCompletionStructure (P : CircularPresentation) (baseDepth : Nat) :
    PresentedDyadicCompletion carrierPresentedCore where
  complete family :=
    let produced := carrierCompletion P baseDepth (asCarrierFamily family)
    { value := produced.limit
      convergence := ⟨produced.convergence.threshold, produced.convergence.converges⟩
      unique := fun other convergence =>
        produced.uniqueness other ⟨convergence.threshold, convergence.near⟩ }

/- These families specify the numerical behaviour of operations only. They
never define an operation on a presented structure or a runtime producer. -/
def canonicalAdditiveFamily (C : PresentedDyadicStructure) (x y : C.Carrier) : PresentedFamily C :=
  presentCarrierFamily C (RelationalRealAddition.addCarrier
    (numericalCarrier C.toPresentedDyadicData x) (numericalCarrier C.toPresentedDyadicData y))

def canonicalNegativeFamily (C : PresentedDyadicStructure) (x : C.Carrier) : PresentedFamily C :=
  presentCarrierFamily C (RelationalRealAddition.negCarrier (numericalCarrier C.toPresentedDyadicData x))

def canonicalMultiplicativeFamily (C : PresentedDyadicStructure) (x y : C.Carrier) : PresentedFamily C :=
  presentCarrierFamily C (RelationalRealAddition.mulCarrier
    (numericalCarrier C.toPresentedDyadicData x) (numericalCarrier C.toPresentedDyadicData y))

end RelationalPerimeter.Constitution.Reals.PresentedDyadicCompletion

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Constitution.Reals.PresentedDyadicCompletion.PresentedDyadicData
#print axioms RelationalPerimeter.Constitution.Reals.PresentedDyadicCompletion.ApproxEquivalent
#print axioms RelationalPerimeter.Constitution.Reals.PresentedDyadicCompletion.PresentedDyadicStructure
#print axioms RelationalPerimeter.Constitution.Reals.PresentedDyadicCompletion.PresentedFamily
#print axioms RelationalPerimeter.Constitution.Reals.PresentedDyadicCompletion.Converges
#print axioms RelationalPerimeter.Constitution.Reals.PresentedDyadicCompletion.LimitResult
#print axioms RelationalPerimeter.Constitution.Reals.PresentedDyadicCompletion.PresentedDyadicCompletion
#print axioms RelationalPerimeter.Constitution.Reals.PresentedDyadicCompletion.PresentedDyadicCompletionObject
#print axioms RelationalPerimeter.Constitution.Reals.PresentedDyadicCompletion.numericalCarrier
#print axioms RelationalPerimeter.Constitution.Reals.PresentedDyadicCompletion.approxToCarrier
#print axioms RelationalPerimeter.Constitution.Reals.PresentedDyadicCompletion.carrierToApprox
#print axioms RelationalPerimeter.Constitution.Reals.PresentedDyadicCompletion.equivalentToCarrier
#print axioms RelationalPerimeter.Constitution.Reals.PresentedDyadicCompletion.carrierToEquivalent
#print axioms RelationalPerimeter.Constitution.Reals.PresentedDyadicCompletion.presentCarrierFamily
#print axioms RelationalPerimeter.Constitution.Reals.PresentedDyadicCompletion.ownFamily
#print axioms RelationalPerimeter.Constitution.Reals.PresentedDyadicCompletion.selfConvergence
#print axioms RelationalPerimeter.Constitution.Reals.PresentedDyadicCompletion.presentedCarrierEquivalent
#print axioms RelationalPerimeter.Constitution.Reals.PresentedDyadicCompletion.diagonalTransportFamily
#print axioms RelationalPerimeter.Constitution.Reals.PresentedDyadicCompletion.dyadicCarrier
#print axioms RelationalPerimeter.Constitution.Reals.PresentedDyadicCompletion.carrierPresentedCore
#print axioms RelationalPerimeter.Constitution.Reals.PresentedDyadicCompletion.asCarrierFamily
#print axioms RelationalPerimeter.Constitution.Reals.PresentedDyadicCompletion.carrierCompletionStructure
#print axioms RelationalPerimeter.Constitution.Reals.PresentedDyadicCompletion.canonicalAdditiveFamily
#print axioms RelationalPerimeter.Constitution.Reals.PresentedDyadicCompletion.canonicalNegativeFamily
#print axioms RelationalPerimeter.Constitution.Reals.PresentedDyadicCompletion.canonicalMultiplicativeFamily
/- AXIOM_AUDIT_END -/
