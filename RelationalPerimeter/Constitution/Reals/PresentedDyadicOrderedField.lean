import RelationalPerimeter.Constitution.Reals.CarrierQuantitativeTransport
import RelationalPerimeter.Constitution.Reals.DyadicDensity

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace RelationalPerimeter.Constitution.Reals.PresentedDyadicCompletion
open DyadicDensity

structure StrictSeparationWitness (C : PresentedDyadicStructure) (x y : C.Carrier) where
  accuracy : Nat
  response : Nat
  beyond : PrecisionExtension (accuracy + 3) response
  separation : StrictSeparation accuracy (C.approximation x (C.modulus x response))
    (C.approximation y (C.modulus y response))

def PresentedDensityWitness (C : PresentedDyadicStructure) (Order : C.Carrier → C.Carrier → Type)
    (x y : C.Carrier) : Type :=
  (code : SignedDyadicCode) × (Order x (C.dyadic code) × Order (C.dyadic code) y)

def PresentedNaturalBoundsWitness (C : PresentedDyadicStructure) (Order : C.Carrier → C.Carrier → Type)
    (x : C.Carrier) : Type :=
  (lower : Nat) × (upper : Nat) ×
    (Order (C.dyadic (negativeNaturalCode lower)) x × Order x (C.dyadic (naturalCode upper)))

structure PresentedAdditiveGroupLaws (C : PresentedDyadicStructure) (zero : C.Carrier)
    (add : C.Carrier → C.Carrier → C.Carrier) (neg : C.Carrier → C.Carrier) where
  addCongr : {a b c d : C.Carrier} → C.Equivalent a c → C.Equivalent b d → C.Equivalent (add a b) (add c d)
  addComm : (a b : C.Carrier) → C.Equivalent (add a b) (add b a)
  addAssoc : (a b c : C.Carrier) → C.Equivalent (add (add a b) c) (add a (add b c))
  zeroLeft : (a : C.Carrier) → C.Equivalent (add zero a) a
  zeroRight : (a : C.Carrier) → C.Equivalent (add a zero) a
  negCongr : {a b : C.Carrier} → C.Equivalent a b → C.Equivalent (neg a) (neg b)
  negInvolutive : (a : C.Carrier) → C.Equivalent (neg (neg a)) a
  inverseLeft : (a : C.Carrier) → C.Equivalent (add (neg a) a) zero
  inverseRight : (a : C.Carrier) → C.Equivalent (add a (neg a)) zero
  negSum : (a b : C.Carrier) → C.Equivalent (neg (add a b)) (add (neg a) (neg b))

structure PresentedMultiplicativeLaws (C : PresentedDyadicStructure) (zero one : C.Carrier)
    (add : C.Carrier → C.Carrier → C.Carrier) (neg : C.Carrier → C.Carrier)
    (mul : C.Carrier → C.Carrier → C.Carrier) where
  mulCongr : {a b c d : C.Carrier} → C.Equivalent a c → C.Equivalent b d → C.Equivalent (mul a b) (mul c d)
  mulComm : (a b : C.Carrier) → C.Equivalent (mul a b) (mul b a)
  mulAssoc : (a b c : C.Carrier) → C.Equivalent (mul (mul a b) c) (mul a (mul b c))
  oneLeft : (a : C.Carrier) → C.Equivalent (mul one a) a
  oneRight : (a : C.Carrier) → C.Equivalent (mul a one) a
  zeroLeft : (a : C.Carrier) → C.Equivalent (mul zero a) zero
  zeroRight : (a : C.Carrier) → C.Equivalent (mul a zero) zero
  distributeLeft : (a b c : C.Carrier) → C.Equivalent (mul a (add b c)) (add (mul a b) (mul a c))
  distributeRight : (a b c : C.Carrier) → C.Equivalent (mul (add a b) c) (add (mul a c) (mul b c))
  negLeft : (a b : C.Carrier) → C.Equivalent (mul (neg a) b) (neg (mul a b))
  negRight : (a b : C.Carrier) → C.Equivalent (mul a (neg b)) (neg (mul a b))

structure PresentedConstructiveOrderLaws (C : PresentedDyadicStructure) (zero one : C.Carrier)
    (add : C.Carrier → C.Carrier → C.Carrier) (neg : C.Carrier → C.Carrier)
    (mul : C.Carrier → C.Carrier → C.Carrier) (Order Apartness : C.Carrier → C.Carrier → Type)
    (inverse : (x : C.Carrier) → Apartness x zero → C.Carrier) where
  unitPositive : Order zero one
  irreflexive : {a : C.Carrier} → Order a a → Empty
  asymmetric : {a b : C.Carrier} → Order a b → Order b a → Empty
  transitive : {a b c : C.Carrier} → Order a b → Order b c → Order a c
  cotransitive : {a b : C.Carrier} → Order a b → (middle : C.Carrier) → Order a middle ⊕ Order middle b
  transportOrder : {a b c d : C.Carrier} → Order a b → C.Equivalent a c → C.Equivalent b d → Order c d
  transportApartness : {a b c d : C.Carrier} → Apartness a b → C.Equivalent a c → C.Equivalent b d → Apartness c d
  translateRight : {a b : C.Carrier} → Order a b → (shift : C.Carrier) → Order (add a shift) (add b shift)
  translateLeft : {a b : C.Carrier} → Order a b → (shift : C.Carrier) → Order (add shift a) (add shift b)
  reflectTranslationRight : {a b shift : C.Carrier} → Order (add a shift) (add b shift) → Order a b
  positiveProduct : {a b : C.Carrier} → Order zero a → Order zero b → Order zero (mul a b)
  multiplyPositiveRight : {a b c : C.Carrier} → Order a b → Order zero c → Order (mul a c) (mul b c)
  multiplyPositiveLeft : {a b c : C.Carrier} → Order a b → Order zero c → Order (mul c a) (mul c b)
  inverseUnitRight : {a : C.Carrier} → (w : Apartness a zero) → C.Equivalent (mul a (inverse a w)) one
  inverseUnitLeft : {a : C.Carrier} → (w : Apartness a zero) → C.Equivalent (mul (inverse a w) a) one
  inverseWitnessIndependent : {a : C.Carrier} → (first second : Apartness a zero) →
    C.Equivalent (inverse a first) (inverse a second)
  inverseCongr : {a b : C.Carrier} → C.Equivalent a b → (first : Apartness a zero) →
    (second : Apartness b zero) → C.Equivalent (inverse a first) (inverse b second)

structure PresentedDyadicOrderedFieldData (C : PresentedDyadicStructure) where
  zero : C.Carrier
  one : C.Carrier
  zeroExact : C.Equivalent zero (C.dyadic SignedDyadicCode.zero)
  oneExact : C.Equivalent one (C.dyadic SignedDyadicCode.one)
  add : C.Carrier → C.Carrier → C.Carrier
  mul : C.Carrier → C.Carrier → C.Carrier
  neg : C.Carrier → C.Carrier
  Order : C.Carrier → C.Carrier → Type
  Apartness : C.Carrier → C.Carrier → Type
  inverse : (x : C.Carrier) → Apartness x zero → C.Carrier
  additiveConverges : (x y : C.Carrier) → Converges C (canonicalAdditiveFamily C x y) (add x y)
  negativeConverges : (x : C.Carrier) → Converges C (canonicalNegativeFamily C x) (neg x)
  multiplicativeConverges : (x y : C.Carrier) → Converges C (canonicalMultiplicativeFamily C x y) (mul x y)
  additiveLaws : PresentedAdditiveGroupLaws C zero add neg
  multiplicativeLaws : PresentedMultiplicativeLaws C zero one add neg mul
  orderedLaws : PresentedConstructiveOrderLaws C zero one add neg mul Order Apartness inverse
  orderToSeparation : {x y : C.Carrier} → Order x y → StrictSeparationWitness C x y
  separationToOrder : {x y : C.Carrier} → StrictSeparationWitness C x y → Order x y
  apartnessToOrder : {x y : C.Carrier} → Apartness x y → Order x y ⊕ Order y x
  orderToApartness : {x y : C.Carrier} → Order x y ⊕ Order y x → Apartness x y
  density : {x y : C.Carrier} → Order x y → PresentedDensityWitness C Order x y
  naturalBounds : (x : C.Carrier) → PresentedNaturalBoundsWitness C Order x

structure PresentedDyadicOrderedFieldCompletion where
  core : PresentedDyadicStructure
  completion : PresentedDyadicCompletion core
  ordered : PresentedDyadicOrderedFieldData core

def densityCode {C : PresentedDyadicStructure} {Order : C.Carrier → C.Carrier → Type} {x y : C.Carrier}
    (w : PresentedDensityWitness C Order x y) : SignedDyadicCode := w.1
def lowerNatural {C : PresentedDyadicStructure} {Order : C.Carrier → C.Carrier → Type} {x : C.Carrier}
    (w : PresentedNaturalBoundsWitness C Order x) : Nat := w.1
def upperNatural {C : PresentedDyadicStructure} {Order : C.Carrier → C.Carrier → Type} {x : C.Carrier}
    (w : PresentedNaturalBoundsWitness C Order x) : Nat := w.2.1

structure OrderedCompletionPointwiseEquivalent (C : PresentedDyadicStructure)
    (KA KB : PresentedDyadicCompletion C) (A B : PresentedDyadicOrderedFieldData C) where
  zeroEquivalent : C.Equivalent A.zero B.zero
  oneEquivalent : C.Equivalent A.one B.one
  addEquivalent : (x y : C.Carrier) → C.Equivalent (A.add x y) (B.add x y)
  negEquivalent : (x : C.Carrier) → C.Equivalent (A.neg x) (B.neg x)
  mulEquivalent : (x y : C.Carrier) → C.Equivalent (A.mul x y) (B.mul x y)
  completeEquivalent : (family : PresentedFamily C) → C.Equivalent (KA.complete family).value (KB.complete family).value
  preserveApartness : {x y : C.Carrier} → A.Apartness x y → B.Apartness x y
  reflectApartness : {x y : C.Carrier} → B.Apartness x y → A.Apartness x y
  transportInverseDomain : {x : C.Carrier} → A.Apartness x A.zero → B.Apartness x B.zero
  reflectInverseDomain : {x : C.Carrier} → B.Apartness x B.zero → A.Apartness x A.zero
  inverse : (x : C.Carrier) → (w : A.Apartness x A.zero) →
    C.Equivalent (A.inverse x w) (B.inverse x (transportInverseDomain w))
  preserveOrder : {x y : C.Carrier} → A.Order x y → B.Order x y
  reflectOrder : {x y : C.Carrier} → B.Order x y → A.Order x y
  preserveDensity : {x y : C.Carrier} → PresentedDensityWitness C A.Order x y → PresentedDensityWitness C B.Order x y
  reflectDensity : {x y : C.Carrier} → PresentedDensityWitness C B.Order x y → PresentedDensityWitness C A.Order x y
  preserveBounds : {x : C.Carrier} → PresentedNaturalBoundsWitness C A.Order x → PresentedNaturalBoundsWitness C B.Order x
  reflectBounds : {x : C.Carrier} → PresentedNaturalBoundsWitness C B.Order x → PresentedNaturalBoundsWitness C A.Order x
  densityReadoutExact : {x y : C.Carrier} → (origin : A.Order x y) →
    densityCode (A.density origin) = densityCode (B.density (preserveOrder origin))
  lowerBoundReadoutExact : (x : C.Carrier) → lowerNatural (A.naturalBounds x) = lowerNatural (B.naturalBounds x)
  upperBoundReadoutExact : (x : C.Carrier) → upperNatural (A.naturalBounds x) = upperNatural (B.naturalBounds x)

end RelationalPerimeter.Constitution.Reals.PresentedDyadicCompletion

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Constitution.Reals.PresentedDyadicCompletion.StrictSeparationWitness
#print axioms RelationalPerimeter.Constitution.Reals.PresentedDyadicCompletion.PresentedDensityWitness
#print axioms RelationalPerimeter.Constitution.Reals.PresentedDyadicCompletion.PresentedNaturalBoundsWitness
#print axioms RelationalPerimeter.Constitution.Reals.PresentedDyadicCompletion.PresentedAdditiveGroupLaws
#print axioms RelationalPerimeter.Constitution.Reals.PresentedDyadicCompletion.PresentedMultiplicativeLaws
#print axioms RelationalPerimeter.Constitution.Reals.PresentedDyadicCompletion.PresentedConstructiveOrderLaws
#print axioms RelationalPerimeter.Constitution.Reals.PresentedDyadicCompletion.PresentedDyadicOrderedFieldData
#print axioms RelationalPerimeter.Constitution.Reals.PresentedDyadicCompletion.PresentedDyadicOrderedFieldCompletion
#print axioms RelationalPerimeter.Constitution.Reals.PresentedDyadicCompletion.densityCode
#print axioms RelationalPerimeter.Constitution.Reals.PresentedDyadicCompletion.lowerNatural
#print axioms RelationalPerimeter.Constitution.Reals.PresentedDyadicCompletion.upperNatural
#print axioms RelationalPerimeter.Constitution.Reals.PresentedDyadicCompletion.OrderedCompletionPointwiseEquivalent
/- AXIOM_AUDIT_END -/
