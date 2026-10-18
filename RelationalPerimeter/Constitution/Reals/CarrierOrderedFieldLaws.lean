import RelationalPerimeter.Constitution.Reals.PresentedDyadicOrderedField
import RelationalPerimeter.Constitution.Reals.RelationalRealDensity
import RelationalPerimeter.Constitution.Reals.RelationalRealInverseCorrespondence

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace RelationalPerimeter.Constitution.Reals.CarrierOrderedField
open StrongPerimetralTurning RuntimeCorrespondence HeterogeneousRealRuntime
open RelationalRealAddition RelationalRealOrder RelationalRealInverse PresentedDyadicCompletion

variable {P : CircularPresentation} {baseDepth : Nat}

def canonicalZeroCarrier : EffectiveCauchyReal.Carrier := dyadicCarrier SignedDyadicCode.zero
def canonicalOneCarrier : EffectiveCauchyReal.Carrier := dyadicCarrier SignedDyadicCode.one
def CanonicalCarrierDomain (x : EffectiveCauchyReal.Carrier) : Type := CarrierApartness x canonicalZeroCarrier

def carrierReadoutConstant (P : CircularPresentation) (baseDepth : Nat) (code : SignedDyadicCode) :
    EffectiveCauchyReal.Equivalent (toCarrier (.leaf (constantRuntime P baseDepth code))) (dyadicCarrier code) where
  firstThreshold p := p
  secondThreshold p := p
  near p r s hr hs := Near.ofSameLeft (constant_readout (P := P) (baseDepth := baseDepth) code r)
    ((EffectiveDyadicPresentation.constantApproximationSameValue code s).symm.toNear p)

def runtimeZeroEquivalent (P : CircularPresentation) (baseDepth : Nat) :
    EffectiveCauchyReal.Equivalent canonicalZeroCarrier (toCarrier (zero P baseDepth)) :=
  (carrierReadoutConstant P baseDepth SignedDyadicCode.zero).symm

def runtimeCarrierDomain (P : CircularPresentation) (baseDepth : Nat) (x : EffectiveCauchyReal.Carrier)
    (w : CanonicalCarrierDomain x) : CarrierDomain P baseDepth x :=
  transportCarrierApartness w (.refl x) (runtimeZeroEquivalent P baseDepth)

def carrierInverse (P : CircularPresentation) (baseDepth : Nat) (x : EffectiveCauchyReal.Carrier)
    (w : CanonicalCarrierDomain x) : EffectiveCauchyReal.Carrier :=
  inverseCarrier x (runtimeCarrierDomain P baseDepth x w)

def carrierReadoutAdd {a b : Real P baseDepth} {x y : EffectiveCauchyReal.Carrier}
    (left : EffectiveCauchyReal.Equivalent (toCarrier a) x)
    (right : EffectiveCauchyReal.Equivalent (toCarrier b) y) :
    EffectiveCauchyReal.Equivalent (toCarrier (.add a b)) (addCarrier x y) :=
  (toCarrier_add a b).trans (addCarrierCongr left right)

def carrierReadoutNeg {a : Real P baseDepth} {x : EffectiveCauchyReal.Carrier}
    (same : EffectiveCauchyReal.Equivalent (toCarrier a) x) :
    EffectiveCauchyReal.Equivalent (toCarrier (.neg a)) (negCarrier x) :=
  (toCarrier_neg a).trans (negCarrierCongr same)

def carrierReadoutMul {a b : Real P baseDepth} {x y : EffectiveCauchyReal.Carrier}
    (left : EffectiveCauchyReal.Equivalent (toCarrier a) x)
    (right : EffectiveCauchyReal.Equivalent (toCarrier b) y) :
    EffectiveCauchyReal.Equivalent (toCarrier (.mul a b)) (mulCarrier x y) :=
  (toCarrier_mul a b).trans (mulCarrierCongr left right)

def carrierReadoutLaw {a b : Real P baseDepth} {x y : EffectiveCauchyReal.Carrier}
    (law : Equivalent a b) (left : EffectiveCauchyReal.Equivalent (toCarrier a) x)
    (right : EffectiveCauchyReal.Equivalent (toCarrier b) y) : EffectiveCauchyReal.Equivalent x y :=
  left.symm.trans (((equivalentCarrier a b).1 law).trans right)

def carrierAdditiveLaws (P : CircularPresentation) (baseDepth : Nat) :
    PresentedAdditiveGroupLaws carrierPresentedCore canonicalZeroCarrier addCarrier negCarrier := by
  let f := ofCarrier P baseDepth
  let rt := fun x => carrier_roundtrip (P := P) (baseDepth := baseDepth) x
  let z := carrierReadoutConstant P baseDepth SignedDyadicCode.zero
  exact {
    addCongr := addCarrierCongr
    addComm := fun a b => carrierReadoutLaw (add_comm (f a) (f b))
      (carrierReadoutAdd (rt a) (rt b)) (carrierReadoutAdd (rt b) (rt a))
    addAssoc := fun a b c => carrierReadoutLaw (add_assoc (f a) (f b) (f c))
      (carrierReadoutAdd (carrierReadoutAdd (rt a) (rt b)) (rt c))
      (carrierReadoutAdd (rt a) (carrierReadoutAdd (rt b) (rt c)))
    zeroLeft := fun a => carrierReadoutLaw (zero_add (f a)) (carrierReadoutAdd z (rt a)) (rt a)
    zeroRight := fun a => carrierReadoutLaw (add_zero (f a)) (carrierReadoutAdd (rt a) z) (rt a)
    negCongr := negCarrierCongr
    negInvolutive := fun a => carrierReadoutLaw (neg_neg (f a)) (carrierReadoutNeg (carrierReadoutNeg (rt a))) (rt a)
    inverseLeft := fun a => carrierReadoutLaw (neg_add (f a)) (carrierReadoutAdd (carrierReadoutNeg (rt a)) (rt a)) z
    inverseRight := fun a => carrierReadoutLaw (add_neg (f a)) (carrierReadoutAdd (rt a) (carrierReadoutNeg (rt a))) z
    negSum := fun a b => carrierReadoutLaw (neg_sum (f a) (f b))
      (carrierReadoutNeg (carrierReadoutAdd (rt a) (rt b)))
      (carrierReadoutAdd (carrierReadoutNeg (rt a)) (carrierReadoutNeg (rt b))) }

def carrierMultiplicativeLaws (P : CircularPresentation) (baseDepth : Nat) :
    PresentedMultiplicativeLaws carrierPresentedCore canonicalZeroCarrier canonicalOneCarrier
      addCarrier negCarrier mulCarrier := by
  let f := ofCarrier P baseDepth
  let rt := fun x => carrier_roundtrip (P := P) (baseDepth := baseDepth) x
  let z := carrierReadoutConstant P baseDepth SignedDyadicCode.zero
  let u := carrierReadoutConstant P baseDepth SignedDyadicCode.one
  exact {
    mulCongr := mulCarrierCongr
    mulComm := fun a b => carrierReadoutLaw (mul_comm (f a) (f b))
      (carrierReadoutMul (rt a) (rt b)) (carrierReadoutMul (rt b) (rt a))
    mulAssoc := fun a b c => carrierReadoutLaw (mul_assoc (f a) (f b) (f c))
      (carrierReadoutMul (carrierReadoutMul (rt a) (rt b)) (rt c))
      (carrierReadoutMul (rt a) (carrierReadoutMul (rt b) (rt c)))
    oneLeft := fun a => carrierReadoutLaw (one_mul (f a)) (carrierReadoutMul u (rt a)) (rt a)
    oneRight := fun a => carrierReadoutLaw (mul_one (f a)) (carrierReadoutMul (rt a) u) (rt a)
    zeroLeft := fun a => carrierReadoutLaw (zero_mul (f a)) (carrierReadoutMul z (rt a)) z
    zeroRight := fun a => carrierReadoutLaw (mul_zero (f a)) (carrierReadoutMul (rt a) z) z
    distributeLeft := fun a b c => carrierReadoutLaw (mul_add (f a) (f b) (f c))
      (carrierReadoutMul (rt a) (carrierReadoutAdd (rt b) (rt c)))
      (carrierReadoutAdd (carrierReadoutMul (rt a) (rt b)) (carrierReadoutMul (rt a) (rt c)))
    distributeRight := fun a b c => carrierReadoutLaw (add_mul (f a) (f b) (f c))
      (carrierReadoutMul (carrierReadoutAdd (rt a) (rt b)) (rt c))
      (carrierReadoutAdd (carrierReadoutMul (rt a) (rt c)) (carrierReadoutMul (rt b) (rt c)))
    negLeft := fun a b => carrierReadoutLaw (neg_mul (f a) (f b))
      (carrierReadoutMul (carrierReadoutNeg (rt a)) (rt b)) (carrierReadoutNeg (carrierReadoutMul (rt a) (rt b)))
    negRight := fun a b => carrierReadoutLaw (mul_neg (f a) (f b))
      (carrierReadoutMul (rt a) (carrierReadoutNeg (rt b))) (carrierReadoutNeg (carrierReadoutMul (rt a) (rt b))) }

/-- This algebraic uniqueness consumes two actual unit laws. -/
def carrierInverseUnique (P : CircularPresentation) (baseDepth : Nat)
    {x b c : EffectiveCauchyReal.Carrier}
    (rightUnit : EffectiveCauchyReal.Equivalent (mulCarrier x b) canonicalOneCarrier)
    (leftUnit : EffectiveCauchyReal.Equivalent (mulCarrier c x) canonicalOneCarrier) :
    EffectiveCauchyReal.Equivalent b c :=
  let laws := carrierMultiplicativeLaws P baseDepth
  (laws.oneLeft b).symm.trans
    ((mulCarrierCongr leftUnit.symm (.refl b)).trans
      ((laws.mulAssoc c x b).trans
        ((mulCarrierCongr (.refl c) rightUnit).trans (laws.oneRight c))))

def carrierInverseUnitRight (P : CircularPresentation) (baseDepth : Nat)
    (x : EffectiveCauchyReal.Carrier) (w : CanonicalCarrierDomain x) :
    EffectiveCauchyReal.Equivalent (mulCarrier x (carrierInverse P baseDepth x w)) canonicalOneCarrier :=
  let runtimeWitness := realizeCarrierDomain x (runtimeCarrierDomain P baseDepth x w)
    (environment (ofCarrier P baseDepth x)).initialArchive (environment (zero P baseDepth)).initialArchive
  carrierReadoutLaw (mul_inverse (ofCarrier P baseDepth x) runtimeWitness)
    (carrierReadoutMul (carrier_roundtrip x) (.refl _))
    (carrierReadoutConstant P baseDepth SignedDyadicCode.one)

def carrierInverseUnitLeft (P : CircularPresentation) (baseDepth : Nat)
    (x : EffectiveCauchyReal.Carrier) (w : CanonicalCarrierDomain x) :
    EffectiveCauchyReal.Equivalent (mulCarrier (carrierInverse P baseDepth x w) x) canonicalOneCarrier :=
  ((carrierMultiplicativeLaws P baseDepth).mulComm _ _).trans (carrierInverseUnitRight P baseDepth x w)

def carrierInverseCongr (P : CircularPresentation) (baseDepth : Nat) {x y : EffectiveCauchyReal.Carrier}
    (same : EffectiveCauchyReal.Equivalent x y) (first : CanonicalCarrierDomain x) (second : CanonicalCarrierDomain y) :
    EffectiveCauchyReal.Equivalent (carrierInverse P baseDepth x first) (carrierInverse P baseDepth y second) :=
  carrierInverseUnique P baseDepth (carrierInverseUnitRight P baseDepth x first)
    ((mulCarrierCongr (.refl _) same).trans (carrierInverseUnitLeft P baseDepth y second))

def carrierInverse_perimeterIndependent (P Q : CircularPresentation) (baseDepth otherDepth : Nat)
    (x : EffectiveCauchyReal.Carrier) (w : CanonicalCarrierDomain x) :
    EffectiveCauchyReal.Equivalent (carrierInverse P baseDepth x w) (carrierInverse Q otherDepth x w) :=
  carrierInverseUnique P baseDepth (carrierInverseUnitRight P baseDepth x w) (carrierInverseUnitLeft Q otherDepth x w)

def projectCarrierOrder {a b : Real P baseDepth} {x y : EffectiveCauchyReal.Carrier}
    (order : StrictOrder a b) (left : EffectiveCauchyReal.Equivalent (toCarrier a) x)
    (right : EffectiveCauchyReal.Equivalent (toCarrier b) y) : CarrierOrder x y :=
  transportCarrierOrder order.toCarrier left right

def realizeCarrierOrderOn {a b : Real P baseDepth} {x y : EffectiveCauchyReal.Carrier}
    (order : CarrierOrder x y) (left : EffectiveCauchyReal.Equivalent (toCarrier a) x)
    (right : EffectiveCauchyReal.Equivalent (toCarrier b) y) : StrictOrder a b :=
  reflectCarrierOrder (transportCarrierOrder order left.symm right.symm)
    (environment a).initialArchive (environment b).initialArchive

def carrierOrderLaws (P : CircularPresentation) (baseDepth : Nat) :
    PresentedConstructiveOrderLaws carrierPresentedCore canonicalZeroCarrier canonicalOneCarrier
      addCarrier negCarrier mulCarrier CarrierOrder CarrierApartness (carrierInverse P baseDepth) := by
  let f := ofCarrier P baseDepth
  let rt := fun x => carrier_roundtrip (P := P) (baseDepth := baseDepth) x
  let z := carrierReadoutConstant P baseDepth SignedDyadicCode.zero
  let u := carrierReadoutConstant P baseDepth SignedDyadicCode.one
  let laws := RelationalRealOrderedField.orderedFieldLaws P baseDepth
  exact {
    unitPositive := projectCarrierOrder laws.unitPositive z u
    irreflexive := fun order => (realizeCarrierOrderOn order (rt _) (rt _)).irreflexive
    asymmetric := fun first second =>
      (realizeCarrierOrderOn first (rt _) (rt _)).asymmetric (realizeCarrierOrderOn second (rt _) (rt _))
    transitive := fun first second => projectCarrierOrder
      ((realizeCarrierOrderOn first (rt _) (rt _)).transitive (realizeCarrierOrderOn second (rt _) (rt _))) (rt _) (rt _)
    cotransitive := fun order middle =>
      match laws.cotransitive (realizeCarrierOrderOn order (rt _) (rt _)) (f middle) (environment (f middle)).initialArchive with
      | .inl first => .inl (projectCarrierOrder first (rt _) (rt _))
      | .inr second => .inr (projectCarrierOrder second (rt _) (rt _))
    transportOrder := transportCarrierOrder
    transportApartness := transportCarrierApartness
    translateRight := fun order shift => projectCarrierOrder
      (laws.translateRight (realizeCarrierOrderOn order (rt _) (rt _)) (f shift))
      (carrierReadoutAdd (rt _) (rt _)) (carrierReadoutAdd (rt _) (rt _))
    translateLeft := fun order shift => projectCarrierOrder
      (laws.translateLeft (realizeCarrierOrderOn order (rt _) (rt _)) (f shift))
      (carrierReadoutAdd (rt _) (rt _)) (carrierReadoutAdd (rt _) (rt _))
    reflectTranslationRight := fun order => projectCarrierOrder
      (laws.reflectTranslation (realizeCarrierOrderOn order
        (carrierReadoutAdd (rt _) (rt _)) (carrierReadoutAdd (rt _) (rt _)))) (rt _) (rt _)
    positiveProduct := fun first second => projectCarrierOrder
      (laws.positiveProduct (realizeCarrierOrderOn first z (rt _)) (realizeCarrierOrderOn second z (rt _)))
      z (carrierReadoutMul (rt _) (rt _))
    multiplyPositiveRight := fun order positive => projectCarrierOrder
      (laws.multiplyPositiveRight (realizeCarrierOrderOn order (rt _) (rt _)) (realizeCarrierOrderOn positive z (rt _)))
      (carrierReadoutMul (rt _) (rt _)) (carrierReadoutMul (rt _) (rt _))
    multiplyPositiveLeft := fun order positive => projectCarrierOrder
      (laws.multiplyPositiveLeft (realizeCarrierOrderOn order (rt _) (rt _)) (realizeCarrierOrderOn positive z (rt _)))
      (carrierReadoutMul (rt _) (rt _)) (carrierReadoutMul (rt _) (rt _))
    inverseUnitRight := carrierInverseUnitRight P baseDepth _
    inverseUnitLeft := carrierInverseUnitLeft P baseDepth _
    inverseWitnessIndependent := fun first second => carrierInverseCongr P baseDepth (.refl _) first second
    inverseCongr := carrierInverseCongr P baseDepth }

structure CarrierOrderedFieldLaws (P : CircularPresentation) (baseDepth : Nat) where
  additive : PresentedAdditiveGroupLaws carrierPresentedCore canonicalZeroCarrier addCarrier negCarrier
  multiplicative : PresentedMultiplicativeLaws carrierPresentedCore canonicalZeroCarrier canonicalOneCarrier addCarrier negCarrier mulCarrier
  ordered : PresentedConstructiveOrderLaws carrierPresentedCore canonicalZeroCarrier canonicalOneCarrier
    addCarrier negCarrier mulCarrier CarrierOrder CarrierApartness (carrierInverse P baseDepth)

def carrierOrderedFieldLaws (P : CircularPresentation) (baseDepth : Nat) : CarrierOrderedFieldLaws P baseDepth :=
  ⟨carrierAdditiveLaws P baseDepth, carrierMultiplicativeLaws P baseDepth, carrierOrderLaws P baseDepth⟩

end RelationalPerimeter.Constitution.Reals.CarrierOrderedField

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Constitution.Reals.CarrierOrderedField.canonicalZeroCarrier
#print axioms RelationalPerimeter.Constitution.Reals.CarrierOrderedField.canonicalOneCarrier
#print axioms RelationalPerimeter.Constitution.Reals.CarrierOrderedField.CanonicalCarrierDomain
#print axioms RelationalPerimeter.Constitution.Reals.CarrierOrderedField.carrierReadoutConstant
#print axioms RelationalPerimeter.Constitution.Reals.CarrierOrderedField.runtimeZeroEquivalent
#print axioms RelationalPerimeter.Constitution.Reals.CarrierOrderedField.runtimeCarrierDomain
#print axioms RelationalPerimeter.Constitution.Reals.CarrierOrderedField.carrierInverse
#print axioms RelationalPerimeter.Constitution.Reals.CarrierOrderedField.carrierReadoutAdd
#print axioms RelationalPerimeter.Constitution.Reals.CarrierOrderedField.carrierReadoutNeg
#print axioms RelationalPerimeter.Constitution.Reals.CarrierOrderedField.carrierReadoutMul
#print axioms RelationalPerimeter.Constitution.Reals.CarrierOrderedField.carrierReadoutLaw
#print axioms RelationalPerimeter.Constitution.Reals.CarrierOrderedField.carrierAdditiveLaws
#print axioms RelationalPerimeter.Constitution.Reals.CarrierOrderedField.carrierMultiplicativeLaws
#print axioms RelationalPerimeter.Constitution.Reals.CarrierOrderedField.carrierInverseUnique
#print axioms RelationalPerimeter.Constitution.Reals.CarrierOrderedField.carrierInverseUnitRight
#print axioms RelationalPerimeter.Constitution.Reals.CarrierOrderedField.carrierInverseUnitLeft
#print axioms RelationalPerimeter.Constitution.Reals.CarrierOrderedField.carrierInverseCongr
#print axioms RelationalPerimeter.Constitution.Reals.CarrierOrderedField.carrierInverse_perimeterIndependent
#print axioms RelationalPerimeter.Constitution.Reals.CarrierOrderedField.projectCarrierOrder
#print axioms RelationalPerimeter.Constitution.Reals.CarrierOrderedField.realizeCarrierOrderOn
#print axioms RelationalPerimeter.Constitution.Reals.CarrierOrderedField.carrierOrderLaws
#print axioms RelationalPerimeter.Constitution.Reals.CarrierOrderedField.CarrierOrderedFieldLaws
#print axioms RelationalPerimeter.Constitution.Reals.CarrierOrderedField.carrierOrderedFieldLaws
/- AXIOM_AUDIT_END -/
