import RelationalPerimeter.Constitution.Reals.RegularDyadicNameOrderedField

set_option autoImplicit false
set_option linter.unusedVariables false

namespace RelationalPerimeter.Tests.RegularDyadicNameOrderedField
open RelationalPerimeter.Constitution.Reals RegularDyadicName DyadicReciprocal DyadicDensity

def alternateZero : RegularDyadicName := constantName ⟨1, 1, 0⟩
def alternateOne : RegularDyadicName := constantName ⟨2, 1, 0⟩

def alternateZeroSame : NameEquivalent alternateZero zeroName :=
  NameEquivalent.ofPointwiseSame (fun p =>
    (constantNameSameValue _ p).trans
      ((⟨⟨0, 0, 0, rfl, rfl⟩, rfl⟩ : SameValue ⟨1, 1, 0⟩ SignedDyadicCode.zero).trans
        (constantNameSameValue _ p).symm))

def alternateOneSame : NameEquivalent alternateOne oneName :=
  NameEquivalent.ofPointwiseSame (fun p =>
    (constantNameSameValue _ p).trans
      ((⟨⟨0, 0, 0, rfl, rfl⟩, rfl⟩ : SameValue ⟨2, 1, 0⟩ SignedDyadicCode.one).trans
        (constantNameSameValue _ p).symm))

def alternateZeroDistinct (same : alternateZero = zeroName) : Empty := by
  have components := congrArg (fun name : RegularDyadicName => (name.approximation 0).positive) same
  cases components

def alternateOrder : NameOrder alternateZero alternateOne :=
  transportNameOrder NameOrder.unitPositive alternateZeroSame.symm alternateOneSame.symm

def orderOnReceivedMiddle (middle : RegularDyadicName) := alternateOrder.cotransitive middle

def firstInverseWitness : NameApartness oneName zeroName := .inr NameOrder.unitPositive
def secondInverseWitness : NameApartness oneName zeroName :=
  .inr (NameOrder.unitPositive.refine 6 (.refl _))

theorem witnessAccuracyDistinct :
    (inverseNameDomain oneName firstInverseWitness).away = 3 ∧
    (inverseNameDomain oneName secondInverseWitness).away = 5 := ⟨rfl, rfl⟩

def twoWitnessesSameInverse := inverseNameWitnessIndependent oneName firstInverseWitness secondInverseWitness
def receivedInverseUnits (name : RegularDyadicName) (w : NameApartness name zeroName) :=
  (inverseNameUnitRight name w, inverseNameUnitLeft name w)

theorem inverseSchedule (name : RegularDyadicName) (w : NameApartness name zeroName) (p : Nat) :
    (inverseName name w).approximation p =
      (computeReciprocal (inverseNameDomain name w).direction
        (name.approximation (sourcePrecision (inverseNameDomain name w).away p))
        (roundingPrecision p) ((inverseNameDomain name w).nonzero p).positive).code := rfl

def producedDensity := nameDensity alternateOrder
theorem densityCodeExact : producedDensity.code = (bisect alternateOrder.separation).code := rfl
theorem densityAccuracyExact :
    producedDensity.left.accuracy = alternateOrder.accuracy + 3 ∧
    producedDensity.right.accuracy = alternateOrder.accuracy + 3 := ⟨rfl, rfl⟩
theorem densityResponseExact :
    producedDensity.left.response = alternateOrder.accuracy + 6 ∧
    producedDensity.right.response = alternateOrder.accuracy + 6 := ⟨rfl, rfl⟩

def producedBounds := nameNaturalBounds alternateOne
theorem lowerBoundExact : producedBounds.lower = (naturalBounds (alternateOne.approximation 2)).lower := rfl
theorem upperBoundExact : producedBounds.upper = (naturalBounds (alternateOne.approximation 2)).upper := rfl
theorem boundsScheduleExact : producedBounds.lowerOrder.accuracy = 2 ∧
    producedBounds.upperOrder.accuracy = 2 ∧ producedBounds.lowerOrder.response = 5 ∧
    producedBounds.upperOrder.response = 5 := ⟨rfl, rfl, rfl, rfl⟩

def receivedOrderMultiply {a b c : RegularDyadicName} (order : NameOrder a b) (positive : NameOrder zeroName c) :=
  (NameOrder.multiplyPositiveRight order positive, NameOrder.multiplyPositiveLeft order positive)

def receivedOrderCancellation {a b shift : RegularDyadicName}
    (order : NameOrder (addName a shift) (addName b shift)) := NameOrder.reflectTranslationRight order

def receivedCrossedMultiplication {a b c d : RegularDyadicName}
    (first : NameEquivalent a c) (second : NameEquivalent b d) := mulNameCongr first second

def shiftedReceivedFamily (name : RegularDyadicName) : RegularPresentedFamily where
  name n := constantName (name.approximation n)
  modulus p := p + 2
  modulusMonotone extension := extension.add (.refl 2)
  cauchy p n m r s hn hm hr hs :=
    Near.ofSameRight (Near.ofSameLeft (constantNameSameValue _ r)
      (name.coherent p n m ((PrecisionExtension.first p 2).trans hn)
        ((PrecisionExtension.first p 2).trans hm))) (constantNameSameValue _ s).symm

def shiftedReceivedLimit (name : RegularDyadicName) := regularLimitResult (shiftedReceivedFamily name)
theorem shiftedModuleExact (name : RegularDyadicName) (p : Nat) :
    (shiftedReceivedFamily name).modulus p = p + 2 := rfl
theorem shiftedDiagonalExact (name : RegularDyadicName) (p : Nat) :
    (shiftedReceivedLimit name).value.approximation p = (name.approximation (p + 2)).raise p := rfl

/-- A numerically varying regular name, with all error data constructed finitely. -/
def decayName : RegularDyadicName where
  approximation p := ⟨1, 0, p⟩
  coherent p r s hr hs := by
    have precision : p + (s + hr.extra) = r + s :=
      (Nat.add_assoc _ _ _).symm.trans
        ((addSwapMiddle _ _ _).trans (congrArg (fun n => n + s) hr.exact))
    have other : p + (r + hs.extra) = r + s :=
      (Nat.add_assoc _ _ _).symm.trans
        ((addSwapMiddle _ _ _).trans ((congrArg (fun n => n + r) hs.exact).trans (Nat.add_comm _ _)))
    have tolerance : s + hr.extra = r + hs.extra := addLeftCancel (precision.trans other.symm)
    refine ⟨⟨r + s, s, r, rfl, Nat.add_comm _ _⟩, s + hr.extra, precision, ?_, ?_⟩
    · change powerOfTwo s + scaleNat 0 r ≤ powerOfTwo r + scaleNat 0 s + powerOfTwo (s + hr.extra)
      rw [SignedDyadicCode.scaleNat_zero, SignedDyadicCode.scaleNat_zero, Nat.add_zero, Nat.add_zero]
      exact Nat.le_trans (powerOfTwo_extension s hr.extra) (Nat.le_add_left _ _)
    · change powerOfTwo r + scaleNat 0 s ≤ powerOfTwo s + scaleNat 0 r + powerOfTwo (s + hr.extra)
      rw [SignedDyadicCode.scaleNat_zero, SignedDyadicCode.scaleNat_zero, Nat.add_zero, Nat.add_zero, tolerance]
      exact Nat.le_trans (powerOfTwo_extension r hs.extra) (Nat.le_add_left _ _)

def nonconstantFamilyStrictDrop :
    NameOrder ((shiftedReceivedFamily decayName).name 1) ((shiftedReceivedFamily decayName).name 0) := by
  have margin : StrictSeparation 2 (decayName.approximation 1) (decayName.approximation 0) :=
    ⟨⟨2, 1, 2, rfl, rfl⟩, 0, rfl, by decide⟩
  exact ⟨2, 5, .refl _,
    (margin.ofSameRight (constantNameSameValue _ 5).symm).ofSameLeft (constantNameSameValue _ 5)⟩

def nonconstantFamilyCompletion := shiftedReceivedLimit decayName

end RelationalPerimeter.Tests.RegularDyadicNameOrderedField

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Tests.RegularDyadicNameOrderedField.alternateZero
#print axioms RelationalPerimeter.Tests.RegularDyadicNameOrderedField.alternateOne
#print axioms RelationalPerimeter.Tests.RegularDyadicNameOrderedField.alternateZeroSame
#print axioms RelationalPerimeter.Tests.RegularDyadicNameOrderedField.alternateOneSame
#print axioms RelationalPerimeter.Tests.RegularDyadicNameOrderedField.alternateZeroDistinct
#print axioms RelationalPerimeter.Tests.RegularDyadicNameOrderedField.alternateOrder
#print axioms RelationalPerimeter.Tests.RegularDyadicNameOrderedField.orderOnReceivedMiddle
#print axioms RelationalPerimeter.Tests.RegularDyadicNameOrderedField.firstInverseWitness
#print axioms RelationalPerimeter.Tests.RegularDyadicNameOrderedField.secondInverseWitness
#print axioms RelationalPerimeter.Tests.RegularDyadicNameOrderedField.witnessAccuracyDistinct
#print axioms RelationalPerimeter.Tests.RegularDyadicNameOrderedField.twoWitnessesSameInverse
#print axioms RelationalPerimeter.Tests.RegularDyadicNameOrderedField.receivedInverseUnits
#print axioms RelationalPerimeter.Tests.RegularDyadicNameOrderedField.inverseSchedule
#print axioms RelationalPerimeter.Tests.RegularDyadicNameOrderedField.producedDensity
#print axioms RelationalPerimeter.Tests.RegularDyadicNameOrderedField.densityCodeExact
#print axioms RelationalPerimeter.Tests.RegularDyadicNameOrderedField.densityAccuracyExact
#print axioms RelationalPerimeter.Tests.RegularDyadicNameOrderedField.densityResponseExact
#print axioms RelationalPerimeter.Tests.RegularDyadicNameOrderedField.producedBounds
#print axioms RelationalPerimeter.Tests.RegularDyadicNameOrderedField.lowerBoundExact
#print axioms RelationalPerimeter.Tests.RegularDyadicNameOrderedField.upperBoundExact
#print axioms RelationalPerimeter.Tests.RegularDyadicNameOrderedField.boundsScheduleExact
#print axioms RelationalPerimeter.Tests.RegularDyadicNameOrderedField.receivedOrderMultiply
#print axioms RelationalPerimeter.Tests.RegularDyadicNameOrderedField.receivedOrderCancellation
#print axioms RelationalPerimeter.Tests.RegularDyadicNameOrderedField.receivedCrossedMultiplication
#print axioms RelationalPerimeter.Tests.RegularDyadicNameOrderedField.shiftedReceivedFamily
#print axioms RelationalPerimeter.Tests.RegularDyadicNameOrderedField.shiftedReceivedLimit
#print axioms RelationalPerimeter.Tests.RegularDyadicNameOrderedField.shiftedModuleExact
#print axioms RelationalPerimeter.Tests.RegularDyadicNameOrderedField.shiftedDiagonalExact
#print axioms RelationalPerimeter.Tests.RegularDyadicNameOrderedField.decayName
#print axioms RelationalPerimeter.Tests.RegularDyadicNameOrderedField.nonconstantFamilyStrictDrop
#print axioms RelationalPerimeter.Tests.RegularDyadicNameOrderedField.nonconstantFamilyCompletion
/- AXIOM_AUDIT_END -/
