import RelationalPerimeter.Constitution.Reals.DyadicCompletionCharacterization

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace RelationalPerimeter.Constitution.Reals.DyadicCompletionCharacterization
open StrongPerimetralTurning PresentedDyadicCompletion RelationalRealAddition RelationalRealOrder CarrierOrderedField
open DyadicDensity

def orderedObject (C : PresentedDyadicOrderedFieldCompletion) : PresentedDyadicCompletionObject := ⟨C.core, C.completion⟩

def additiveNumerical (C : PresentedDyadicStructure) (A : PresentedDyadicOrderedFieldData C) (x y : C.Carrier) :
    EffectiveCauchyReal.Equivalent (fromTarget C (A.add x y)) (addCarrier (fromTarget C x) (fromTarget C y)) :=
  presentedCarrierEquivalent C _ _ (A.additiveConverges x y)
def negativeNumerical (C : PresentedDyadicStructure) (A : PresentedDyadicOrderedFieldData C) (x : C.Carrier) :
    EffectiveCauchyReal.Equivalent (fromTarget C (A.neg x)) (negCarrier (fromTarget C x)) :=
  presentedCarrierEquivalent C _ _ (A.negativeConverges x)
def multiplicativeNumerical (C : PresentedDyadicStructure) (A : PresentedDyadicOrderedFieldData C) (x y : C.Carrier) :
    EffectiveCauchyReal.Equivalent (fromTarget C (A.mul x y)) (mulCarrier (fromTarget C x) (fromTarget C y)) :=
  presentedCarrierEquivalent C _ _ (A.multiplicativeConverges x y)

variable {Source Target : PresentedDyadicOrderedFieldCompletion}
  (f : CompletionMorphism (orderedObject Source) (orderedObject Target))

def preserveZero : Target.core.Equivalent (f.map Source.ordered.zero) Target.ordered.zero :=
  Target.core.equivalentTrans (f.mapEquivalent Source.ordered.zeroExact)
    (Target.core.equivalentTrans (f.mapDyadic SignedDyadicCode.zero) (Target.core.equivalentSymm Target.ordered.zeroExact))

def preserveOne : Target.core.Equivalent (f.map Source.ordered.one) Target.ordered.one :=
  Target.core.equivalentTrans (f.mapEquivalent Source.ordered.oneExact)
    (Target.core.equivalentTrans (f.mapDyadic SignedDyadicCode.one) (Target.core.equivalentSymm Target.ordered.oneExact))

def preserveAdd (x y : Source.core.Carrier) :
    Target.core.Equivalent (f.map (Source.ordered.add x y)) (Target.ordered.add (f.map x) (f.map y)) :=
  equivalentByLimitUniqueness (orderedObject Target)
    ((morphismNumerical f _).trans ((additiveNumerical Source.core Source.ordered x y).trans
      ((addCarrierCongr (morphismNumerical f x).symm (morphismNumerical f y).symm).trans
        (additiveNumerical Target.core Target.ordered (f.map x) (f.map y)).symm)))

def preserveNeg (x : Source.core.Carrier) :
    Target.core.Equivalent (f.map (Source.ordered.neg x)) (Target.ordered.neg (f.map x)) :=
  equivalentByLimitUniqueness (orderedObject Target)
    ((morphismNumerical f _).trans ((negativeNumerical Source.core Source.ordered x).trans
      ((negCarrierCongr (morphismNumerical f x).symm).trans
        (negativeNumerical Target.core Target.ordered (f.map x)).symm)))

/-- The only numerical congruence here is the quantified crossed-amplitude
lemma. Both canonical multiplication families retain their own schedules. -/
def preserveMul (x y : Source.core.Carrier) :
    Target.core.Equivalent (f.map (Source.ordered.mul x y)) (Target.ordered.mul (f.map x) (f.map y)) :=
  equivalentByLimitUniqueness (orderedObject Target)
    ((morphismNumerical f _).trans ((multiplicativeNumerical Source.core Source.ordered x y).trans
      ((mulCarrierCongr (morphismNumerical f x).symm (morphismNumerical f y).symm).trans
        (multiplicativeNumerical Target.core Target.ordered (f.map x) (f.map y)).symm)))

def reflectEquivalent {x y : Source.core.Carrier}
    (same : Target.core.Equivalent (f.map x) (f.map y)) : Source.core.Equivalent x y :=
  equivalentByLimitUniqueness (orderedObject Source)
    ((morphismNumerical f x).symm.trans ((equivalentToCarrier same).trans (morphismNumerical f y)))

def orderToNumerical (C : PresentedDyadicOrderedFieldCompletion) {x y : C.core.Carrier} (order : C.ordered.Order x y) :
    CarrierOrder (fromTarget C.core x) (fromTarget C.core y) :=
  let witness := C.ordered.orderToSeparation order
  ⟨witness.accuracy, witness.response, witness.beyond, witness.separation⟩

def numericalToOrder (C : PresentedDyadicOrderedFieldCompletion) {x y : C.core.Carrier}
    (order : CarrierOrder (fromTarget C.core x) (fromTarget C.core y)) : C.ordered.Order x y :=
  C.ordered.separationToOrder ⟨order.accuracy, order.response, order.beyond, order.separation⟩

def preserveOrder {x y : Source.core.Carrier} (order : Source.ordered.Order x y) : Target.ordered.Order (f.map x) (f.map y) :=
  numericalToOrder Target (transportCarrierOrder (orderToNumerical Source order)
    (morphismNumerical f x).symm (morphismNumerical f y).symm)

def reflectOrder {x y : Source.core.Carrier} (order : Target.ordered.Order (f.map x) (f.map y)) : Source.ordered.Order x y :=
  numericalToOrder Source (transportCarrierOrder (orderToNumerical Target order) (morphismNumerical f x) (morphismNumerical f y))

def preserveApartness {x y : Source.core.Carrier} (apartness : Source.ordered.Apartness x y) :
    Target.ordered.Apartness (f.map x) (f.map y) :=
  Target.ordered.orderToApartness (match Source.ordered.apartnessToOrder apartness with
    | .inl first => .inl (preserveOrder f first)
    | .inr second => .inr (preserveOrder f second))

def reflectApartness {x y : Source.core.Carrier} (apartness : Target.ordered.Apartness (f.map x) (f.map y)) :
    Source.ordered.Apartness x y :=
  Source.ordered.orderToApartness (match Target.ordered.apartnessToOrder apartness with
    | .inl first => .inl (reflectOrder f first)
    | .inr second => .inr (reflectOrder f second))

def transportInverseDomain {x : Source.core.Carrier} (domain : Source.ordered.Apartness x Source.ordered.zero) :
    Target.ordered.Apartness (f.map x) Target.ordered.zero :=
  Target.ordered.orderedLaws.transportApartness (preserveApartness f domain)
    (Target.core.equivalentRefl _) (preserveZero f)

def presentedInverseUnique (C : PresentedDyadicOrderedFieldCompletion) {x b c : C.core.Carrier}
    (rightUnit : C.core.Equivalent (C.ordered.mul x b) C.ordered.one)
    (leftUnit : C.core.Equivalent (C.ordered.mul c x) C.ordered.one) : C.core.Equivalent b c :=
  let laws := C.ordered.multiplicativeLaws
  C.core.equivalentTrans (C.core.equivalentSymm (laws.oneLeft b))
    (C.core.equivalentTrans (laws.mulCongr (C.core.equivalentSymm leftUnit) (C.core.equivalentRefl b))
      (C.core.equivalentTrans (laws.mulAssoc c x b)
        (C.core.equivalentTrans (laws.mulCongr (C.core.equivalentRefl c) rightUnit) (laws.oneRight c))))

def preserveInverse (x : Source.core.Carrier) (domain : Source.ordered.Apartness x Source.ordered.zero) :
    Target.core.Equivalent (f.map (Source.ordered.inverse x domain))
      (Target.ordered.inverse (f.map x) (transportInverseDomain f domain)) :=
  presentedInverseUnique Target
    (Target.core.equivalentTrans (Target.core.equivalentSymm (preserveMul f x (Source.ordered.inverse x domain)))
      (Target.core.equivalentTrans (f.mapEquivalent (Source.ordered.orderedLaws.inverseUnitRight domain)) (preserveOne f)))
    (Target.ordered.orderedLaws.inverseUnitLeft (transportInverseDomain f domain))

/-- Transport the received witness and its code; do not run the target selector. -/
def preserveDensity {x y : Source.core.Carrier} (w : PresentedDensityWitness Source.core Source.ordered.Order x y) :
    PresentedDensityWitness Target.core Target.ordered.Order (f.map x) (f.map y) :=
  ⟨w.1, Target.ordered.orderedLaws.transportOrder (preserveOrder f w.2.1) (Target.core.equivalentRefl _) (f.mapDyadic w.1),
    Target.ordered.orderedLaws.transportOrder (preserveOrder f w.2.2) (f.mapDyadic w.1) (Target.core.equivalentRefl _)⟩

def reflectDensity {x y : Source.core.Carrier}
    (w : PresentedDensityWitness Target.core Target.ordered.Order (f.map x) (f.map y)) :
    PresentedDensityWitness Source.core Source.ordered.Order x y :=
  ⟨w.1, reflectOrder f (Target.ordered.orderedLaws.transportOrder w.2.1 (Target.core.equivalentRefl _)
      (Target.core.equivalentSymm (f.mapDyadic w.1))),
    reflectOrder f (Target.ordered.orderedLaws.transportOrder w.2.2 (Target.core.equivalentSymm (f.mapDyadic w.1))
      (Target.core.equivalentRefl _))⟩

def preserveBounds {x : Source.core.Carrier} (w : PresentedNaturalBoundsWitness Source.core Source.ordered.Order x) :
    PresentedNaturalBoundsWitness Target.core Target.ordered.Order (f.map x) :=
  ⟨w.1, w.2.1,
    Target.ordered.orderedLaws.transportOrder (preserveOrder f w.2.2.1) (f.mapDyadic _) (Target.core.equivalentRefl _),
    Target.ordered.orderedLaws.transportOrder (preserveOrder f w.2.2.2) (Target.core.equivalentRefl _) (f.mapDyadic _)⟩

def reflectBounds {x : Source.core.Carrier} (w : PresentedNaturalBoundsWitness Target.core Target.ordered.Order (f.map x)) :
    PresentedNaturalBoundsWitness Source.core Source.ordered.Order x :=
  ⟨w.1, w.2.1,
    reflectOrder f (Target.ordered.orderedLaws.transportOrder w.2.2.1 (Target.core.equivalentSymm (f.mapDyadic _))
      (Target.core.equivalentRefl _)),
    reflectOrder f (Target.ordered.orderedLaws.transportOrder w.2.2.2 (Target.core.equivalentRefl _)
      (Target.core.equivalentSymm (f.mapDyadic _)))⟩

theorem densityTransportCode {x y : Source.core.Carrier} (w : PresentedDensityWitness Source.core Source.ordered.Order x y) :
    densityCode (preserveDensity f w) = densityCode w := rfl
theorem boundsTransportLower {x : Source.core.Carrier} (w : PresentedNaturalBoundsWitness Source.core Source.ordered.Order x) :
    lowerNatural (preserveBounds f w) = lowerNatural w := rfl
theorem boundsTransportUpper {x : Source.core.Carrier} (w : PresentedNaturalBoundsWitness Source.core Source.ordered.Order x) :
    upperNatural (preserveBounds f w) = upperNatural w := rfl

def orderedComparisonRoundtrip (x : Source.core.Carrier) :
    Source.core.Equivalent ((comparisonMorphism (orderedObject Target) (orderedObject Source)).map (f.map x)) x :=
  equivalentByLimitUniqueness (orderedObject Source)
    ((morphismNumerical (comparisonMorphism (orderedObject Target) (orderedObject Source)) (f.map x)).trans (morphismNumerical f x))

structure OrderedMorphismTransports (Source Target : PresentedDyadicOrderedFieldCompletion)
    (f : CompletionMorphism (orderedObject Source) (orderedObject Target)) where
  zero : Target.core.Equivalent (f.map Source.ordered.zero) Target.ordered.zero
  one : Target.core.Equivalent (f.map Source.ordered.one) Target.ordered.one
  add : (x y : Source.core.Carrier) → Target.core.Equivalent (f.map (Source.ordered.add x y)) (Target.ordered.add (f.map x) (f.map y))
  neg : (x : Source.core.Carrier) → Target.core.Equivalent (f.map (Source.ordered.neg x)) (Target.ordered.neg (f.map x))
  mul : (x y : Source.core.Carrier) → Target.core.Equivalent (f.map (Source.ordered.mul x y)) (Target.ordered.mul (f.map x) (f.map y))
  equivalentReflection : {x y : Source.core.Carrier} → Target.core.Equivalent (f.map x) (f.map y) → Source.core.Equivalent x y
  orderPreservation : {x y : Source.core.Carrier} → Source.ordered.Order x y → Target.ordered.Order (f.map x) (f.map y)
  orderReflection : {x y : Source.core.Carrier} → Target.ordered.Order (f.map x) (f.map y) → Source.ordered.Order x y
  apartnessPreservation : {x y : Source.core.Carrier} → Source.ordered.Apartness x y → Target.ordered.Apartness (f.map x) (f.map y)
  apartnessReflection : {x y : Source.core.Carrier} → Target.ordered.Apartness (f.map x) (f.map y) → Source.ordered.Apartness x y
  inverseDomain : {x : Source.core.Carrier} → Source.ordered.Apartness x Source.ordered.zero → Target.ordered.Apartness (f.map x) Target.ordered.zero
  inverse : (x : Source.core.Carrier) → (w : Source.ordered.Apartness x Source.ordered.zero) →
    Target.core.Equivalent (f.map (Source.ordered.inverse x w)) (Target.ordered.inverse (f.map x) (inverseDomain w))
  density : {x y : Source.core.Carrier} → PresentedDensityWitness Source.core Source.ordered.Order x y →
    PresentedDensityWitness Target.core Target.ordered.Order (f.map x) (f.map y)
  densityReflection : {x y : Source.core.Carrier} → PresentedDensityWitness Target.core Target.ordered.Order (f.map x) (f.map y) →
    PresentedDensityWitness Source.core Source.ordered.Order x y
  bounds : {x : Source.core.Carrier} → PresentedNaturalBoundsWitness Source.core Source.ordered.Order x →
    PresentedNaturalBoundsWitness Target.core Target.ordered.Order (f.map x)
  boundsReflection : {x : Source.core.Carrier} → PresentedNaturalBoundsWitness Target.core Target.ordered.Order (f.map x) →
    PresentedNaturalBoundsWitness Source.core Source.ordered.Order x

def orderedMorphismTransports : OrderedMorphismTransports Source Target f :=
  ⟨preserveZero f, preserveOne f, preserveAdd f, preserveNeg f, preserveMul f, reflectEquivalent f,
    preserveOrder f, reflectOrder f, preserveApartness f, reflectApartness f, transportInverseDomain f, preserveInverse f,
    preserveDensity f, reflectDensity f, preserveBounds f, reflectBounds f⟩

structure RelativeOrderedCharacterization (Source Target : PresentedDyadicOrderedFieldCompletion) where
  forward : CompletionMorphism (orderedObject Source) (orderedObject Target)
  backward : CompletionMorphism (orderedObject Target) (orderedObject Source)
  carrierReturn : (x : Source.core.Carrier) → Source.core.Equivalent (backward.map (forward.map x)) x
  targetReturn : (y : Target.core.Carrier) → Target.core.Equivalent (forward.map (backward.map y)) y
  forwardTransports : OrderedMorphismTransports Source Target forward
  backwardTransports : OrderedMorphismTransports Target Source backward
  forwardLimit : (family : PresentedFamily Source.core) → Target.core.Equivalent
    (forward.map (Source.completion.complete family).value)
    (Target.completion.complete (diagonalTransportFamily Source.core Target.core family)).value
  backwardLimit : (family : PresentedFamily Target.core) → Source.core.Equivalent
    (backward.map (Target.completion.complete family).value)
    (Source.completion.complete (diagonalTransportFamily Target.core Source.core family)).value
  comparisonUniqueness : (other : CompletionMorphism (orderedObject Source) (orderedObject Target)) →
    PointwiseEquivalent other forward

def relativeOrderedCharacterization (P : CircularPresentation) (baseDepth : Nat)
    (Target : PresentedDyadicOrderedFieldCompletion) :
    RelativeOrderedCharacterization (carrierOrderedCompletion P baseDepth) Target where
  forward := comparisonMorphism (carrierCompletionObject P baseDepth) (orderedObject Target)
  backward := reverseMorphism (orderedObject Target) P baseDepth
  carrierReturn := fromToTarget (orderedObject Target)
  targetReturn := toFromTarget (orderedObject Target)
  forwardTransports := orderedMorphismTransports _
  backwardTransports := orderedMorphismTransports _
  forwardLimit := mapProducedLimit (comparisonMorphism (carrierCompletionObject P baseDepth) (orderedObject Target))
  backwardLimit := mapProducedLimit (reverseMorphism (orderedObject Target) P baseDepth)
  comparisonUniqueness := comparisonUnique

theorem relativeForwardExact (P : CircularPresentation) (baseDepth : Nat)
    (Target : PresentedDyadicOrderedFieldCompletion) (x : EffectiveCauchyReal.Carrier) :
    (relativeOrderedCharacterization P baseDepth Target).forward.map x = toTarget (orderedObject Target) x := rfl

theorem relativeBackwardExact (P : CircularPresentation) (baseDepth : Nat)
    (Target : PresentedDyadicOrderedFieldCompletion) (y : Target.core.Carrier) :
    (relativeOrderedCharacterization P baseDepth Target).backward.map y = fromTarget Target.core y := rfl

end RelationalPerimeter.Constitution.Reals.DyadicCompletionCharacterization

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Constitution.Reals.DyadicCompletionCharacterization.orderedObject
#print axioms RelationalPerimeter.Constitution.Reals.DyadicCompletionCharacterization.additiveNumerical
#print axioms RelationalPerimeter.Constitution.Reals.DyadicCompletionCharacterization.negativeNumerical
#print axioms RelationalPerimeter.Constitution.Reals.DyadicCompletionCharacterization.multiplicativeNumerical
#print axioms RelationalPerimeter.Constitution.Reals.DyadicCompletionCharacterization.preserveZero
#print axioms RelationalPerimeter.Constitution.Reals.DyadicCompletionCharacterization.preserveOne
#print axioms RelationalPerimeter.Constitution.Reals.DyadicCompletionCharacterization.preserveAdd
#print axioms RelationalPerimeter.Constitution.Reals.DyadicCompletionCharacterization.preserveNeg
#print axioms RelationalPerimeter.Constitution.Reals.DyadicCompletionCharacterization.preserveMul
#print axioms RelationalPerimeter.Constitution.Reals.DyadicCompletionCharacterization.reflectEquivalent
#print axioms RelationalPerimeter.Constitution.Reals.DyadicCompletionCharacterization.orderToNumerical
#print axioms RelationalPerimeter.Constitution.Reals.DyadicCompletionCharacterization.numericalToOrder
#print axioms RelationalPerimeter.Constitution.Reals.DyadicCompletionCharacterization.preserveOrder
#print axioms RelationalPerimeter.Constitution.Reals.DyadicCompletionCharacterization.reflectOrder
#print axioms RelationalPerimeter.Constitution.Reals.DyadicCompletionCharacterization.preserveApartness
#print axioms RelationalPerimeter.Constitution.Reals.DyadicCompletionCharacterization.reflectApartness
#print axioms RelationalPerimeter.Constitution.Reals.DyadicCompletionCharacterization.transportInverseDomain
#print axioms RelationalPerimeter.Constitution.Reals.DyadicCompletionCharacterization.presentedInverseUnique
#print axioms RelationalPerimeter.Constitution.Reals.DyadicCompletionCharacterization.preserveInverse
#print axioms RelationalPerimeter.Constitution.Reals.DyadicCompletionCharacterization.preserveDensity
#print axioms RelationalPerimeter.Constitution.Reals.DyadicCompletionCharacterization.reflectDensity
#print axioms RelationalPerimeter.Constitution.Reals.DyadicCompletionCharacterization.preserveBounds
#print axioms RelationalPerimeter.Constitution.Reals.DyadicCompletionCharacterization.reflectBounds
#print axioms RelationalPerimeter.Constitution.Reals.DyadicCompletionCharacterization.densityTransportCode
#print axioms RelationalPerimeter.Constitution.Reals.DyadicCompletionCharacterization.boundsTransportLower
#print axioms RelationalPerimeter.Constitution.Reals.DyadicCompletionCharacterization.boundsTransportUpper
#print axioms RelationalPerimeter.Constitution.Reals.DyadicCompletionCharacterization.orderedComparisonRoundtrip
#print axioms RelationalPerimeter.Constitution.Reals.DyadicCompletionCharacterization.OrderedMorphismTransports
#print axioms RelationalPerimeter.Constitution.Reals.DyadicCompletionCharacterization.orderedMorphismTransports
#print axioms RelationalPerimeter.Constitution.Reals.DyadicCompletionCharacterization.RelativeOrderedCharacterization
#print axioms RelationalPerimeter.Constitution.Reals.DyadicCompletionCharacterization.relativeOrderedCharacterization
#print axioms RelationalPerimeter.Constitution.Reals.DyadicCompletionCharacterization.relativeForwardExact
#print axioms RelationalPerimeter.Constitution.Reals.DyadicCompletionCharacterization.relativeBackwardExact
/- AXIOM_AUDIT_END -/
