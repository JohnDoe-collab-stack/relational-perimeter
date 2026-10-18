import Tests.RegularDyadicName
import RelationalPerimeter.Constitution.Reals.ExtensiveCauchyRealCompletion

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace RelationalPerimeter.Tests.ExtensiveCauchyReal
open RelationalPerimeter.Constitution.Reals
open RelationalPerimeter.Constitution.Reals.RegularDyadicName
open RelationalPerimeter.Constitution.Reals.ExtensiveCauchyReal
open RelationalPerimeter.Constitution.Reals.RegularDyadicCompletion

/-- The received approximation function is unrestricted. -/
def receivedReferenceCoverage (name : RegularDyadicName) :
    ReferenceRealizes name (referenceCoverage name).1 := (referenceCoverage name).2

theorem referenceCarrierExact : ConventionalRegularCauchyReference.Carrier = RegularDyadicName := rfl

def receivedTailMember (name : RegularDyadicName) :
    ReferenceRealizes (RegularDyadicName.tailName name 1) (classOf name) :=
  RegularDyadicName.tailEquivalent name 1

/-- This class has a different membership type, retaining an extra positive tag. -/
def taggedClass (name : RegularDyadicName) : Value where
  Contains other := NameEquivalent name other × Unit
  inhabited := ⟨⟨name, ⟨.refl name, ()⟩⟩⟩
  saturated same member := ⟨member.1.trans same, member.2⟩
  coherent first second := first.1.symm.trans second.1

def taggedClassEquivalent (name : RegularDyadicName) : ExternalEquivalent (classOf name) (taggedClass name) :=
  ⟨fun _ same => ⟨same, ()⟩, fun _ member => member.1⟩

def taggedFirstMember (name : RegularDyadicName) : (taggedClass name).Contains name := ⟨.refl name, ()⟩
def taggedSecondMember (name : RegularDyadicName) :
    (taggedClass name).Contains (RegularDyadicName.tailName name 1) :=
  ⟨RegularDyadicName.tailEquivalent name 1, ()⟩

theorem taggedValueReferenceCoverage (name : RegularDyadicName) :
    Nonempty (Σ member, ReferenceRealizes member (taggedClass name)) := valueReferenceCoverage _

theorem twoMembersDiffer :
    zeroName.approximation 0 ≠ (RegularDyadicName.tailName zeroName 1).approximation 0 :=
  RegularDyadicName.distinctZeroReplies

def receivedReferenceCorrect {a b : RegularDyadicName} (same : NameEquivalent a b) :
    ExternalEquivalent (taggedClass a) (classOf b) :=
  referenceCorrect same (taggedFirstMember a) (classOfContains b)

def receivedReferenceFaithful {a b : RegularDyadicName}
    (same : ExternalEquivalent (taggedClass a) (classOf b)) : NameEquivalent a b :=
  referenceFaithful same (taggedFirstMember a) (classOfContains b)

def identityNameMap (name : RegularDyadicName) : ConventionalRegularCauchyReference.Carrier := name
def identityNameRespect : RespectsNameEquivalent identityNameMap := fun same => same

def firstDescent (name : RegularDyadicName) : ClassDescent identityNameMap (classOf name) name :=
  ⟨name, classOfContains name, .refl name⟩

def secondDescent {a b : RegularDyadicName} (same : NameEquivalent a b) :
    ClassDescent identityNameMap (classOf a) b := ⟨b, same, .refl b⟩

def twoDescentOutputs {a b : RegularDyadicName} (same : NameEquivalent a b) : NameEquivalent a b :=
  (classDescent identityNameMap identityNameRespect).singleValued (firstDescent a) (secondDescent same)

def identityExtendsClassMap : ExtendsNameMap classOf (RelationalMorphism.identity ValuePositiveSetoid) :=
  fun name => .refl _

def universalIdentity : RelationalMorphism.PointwiseEquivalent
    (classDescent classOf (fun same => classOfPreserves same)) (RelationalMorphism.identity ValuePositiveSetoid) :=
  classDescentUnique (fun same => classOfPreserves same) _ identityExtendsClassMap

universe u v w z g
def morphismIdentityLeft {X : PositiveSetoid.{u,v}} {Y : PositiveSetoid.{w,z}}
    (F : RelationalMorphism.{u,v,w,z,g} X Y) :
    RelationalMorphism.PointwiseEquivalent (RelationalMorphism.compose (RelationalMorphism.identity X) F) F :=
  RelationalMorphism.identityLeft F

def morphismIdentityRight {X : PositiveSetoid.{u,v}} {Y : PositiveSetoid.{w,z}}
    (F : RelationalMorphism.{u,v,w,z,g} X Y) :
    RelationalMorphism.PointwiseEquivalent (RelationalMorphism.compose F (RelationalMorphism.identity Y)) F :=
  RelationalMorphism.identityRight F

def compositeDescent (name : RegularDyadicName) :
    (RelationalMorphism.compose (classDescent identityNameMap identityNameRespect)
      (RelationalMorphism.identity ConventionalRegularCauchyReference)).Graph (classOf name) name :=
  ⟨name, firstDescent name, .refl name⟩

/-- The carrier, equivalence and graph occupy three different universes. -/
def raisedReference : PositiveSetoid.{1,2} where
  Carrier := ULift.{1} RegularDyadicName
  Equivalent a b := ULift.{2} (NameEquivalent a.down b.down)
  equivalentRefl a := ⟨.refl a.down⟩
  equivalentSymm same := ⟨same.down.symm⟩
  equivalentTrans first second := ⟨first.down.trans second.down⟩

def raisedGraph : RelationalMorphism.{1,2,1,2,3} raisedReference raisedReference where
  Graph a b := ULift.{3} (NameEquivalent a.down b.down)
  total a := ⟨⟨a, ⟨.refl a.down⟩⟩⟩
  stableSource same graph := ⟨same.down.symm.trans graph.down⟩
  stableTarget graph same := ⟨graph.down.trans same.down⟩
  singleValued first second := ⟨first.down.symm.trans second.down⟩

def raisedGraphIdentity : RelationalMorphism.PointwiseEquivalent
    (RelationalMorphism.compose raisedGraph (RelationalMorphism.identity raisedReference)) raisedGraph :=
  RelationalMorphism.identityRight raisedGraph

def receivedOperationComparisons (a b : RegularDyadicName) :=
  (classOfAdd a b, classOfNeg a, classOfMul a b)

theorem densityFiniteReadoutExact {a b : RegularDyadicName} (origin : NameOrder a b) :
    (externalDensity (nameOrderToExternal origin)).code = (nameDensity origin).code := densityCodeExact origin

theorem boundsFiniteReadoutExact (name : RegularDyadicName) :
    (externalNaturalBoundsFromMember (classOf name) name (classOfContains name)).lower =
      (nameNaturalBounds name).lower ∧
    (externalNaturalBoundsFromMember (classOf name) name (classOfContains name)).upper =
      (nameNaturalBounds name).upper := ⟨lowerBoundExact name, upperBoundExact name⟩

def shiftedZero : RegularDyadicName := RegularDyadicName.tailName zeroName 1
def shiftedZeroMember : zero.Contains shiftedZero := RegularDyadicName.tailEquivalent zeroName 1

def canonicalUnitOrder : ExternalOrder zero one := nameOrderToExternal unitNamePositive

/-- Its zero member has a different dyadic scale already at response zero. -/
def shiftedUnitOrder : ExternalOrder zero one :=
  externalOrderFromMembers shiftedZeroMember (classOfContains oneName)
    (transportNameOrder unitNamePositive (RegularDyadicName.tailEquivalent zeroName 1) (.refl oneName))

theorem shiftedZeroNotCanonical : zeroName.approximation 0 ≠ shiftedUnitOrder.leftName.approximation 0 :=
  RegularDyadicName.distinctZeroReplies

def firstApartness : ExternalApartness one zero := .inr canonicalUnitOrder
def secondApartness : ExternalApartness one zero := .inr shiftedUnitOrder

theorem distinctWitnessAccuracies : canonicalUnitOrder.accuracy ≠ shiftedUnitOrder.accuracy := by decide

def shiftedZeroThreeLinks := zeroMemberNear shiftedUnitOrder.leftName shiftedUnitOrder.leftMember
  (shiftedUnitOrder.accuracy + 3) shiftedUnitOrder.response shiftedUnitOrder.beyond

theorem zeroAuxiliaryExact : shiftedZeroThreeLinks.1 =
    (shiftedUnitOrder.accuracy + 3) +
      shiftedUnitOrder.leftMember.symm.responseThreshold (shiftedUnitOrder.accuracy + 3) := rfl

def zeroFirstLink : Near (shiftedUnitOrder.accuracy + 3)
    (shiftedUnitOrder.leftName.approximation shiftedUnitOrder.response)
    (shiftedUnitOrder.leftName.approximation shiftedZeroThreeLinks.1) := shiftedZeroThreeLinks.2.1
def zeroSecondLink : Near (shiftedUnitOrder.accuracy + 3)
    (shiftedUnitOrder.leftName.approximation shiftedZeroThreeLinks.1)
    (zeroName.approximation shiftedZeroThreeLinks.1) := shiftedZeroThreeLinks.2.2.1
def zeroThirdLink : Near (shiftedUnitOrder.accuracy + 3)
    (zeroName.approximation shiftedZeroThreeLinks.1) SignedDyadicCode.zero := shiftedZeroThreeLinks.2.2.2

theorem inverseAwayExact : (externalPositiveDomain shiftedUnitOrder).away = shiftedUnitOrder.accuracy + 2 := rfl
def inverseSourceBeyondExact (p : Nat) : PrecisionExtension (shiftedUnitOrder.accuracy + 3)
    (DyadicReciprocal.sourcePrecision (shiftedUnitOrder.accuracy + 2) p) :=
  inverseSourceBeyond shiftedUnitOrder.accuracy p

def inverseNormalizedNonzero (p : Nat) := (externalPositiveDomain shiftedUnitOrder).nonzero p

theorem inverseRoundingSchedule (p : Nat) :
    (reciprocalName shiftedUnitOrder.rightName (externalPositiveDomain shiftedUnitOrder)).approximation p =
    (DyadicReciprocal.computeReciprocal .positive
      (shiftedUnitOrder.rightName.approximation
        (DyadicReciprocal.sourcePrecision (shiftedUnitOrder.accuracy + 2) p))
      (DyadicReciprocal.roundingPrecision p) (inverseNormalizedNonzero p).positive).code := rfl

def inverseTwoWitnesses : ExternalEquivalent (externalInverse one firstApartness) (externalInverse one secondApartness) :=
  externalInverseWitnessIndependent one firstApartness secondApartness

def exactClassInverse {name : RegularDyadicName} (apart : NameApartness name zeroName) :
    ExternalEquivalent (classOf (inverseName name apart))
      (externalInverse (classOf name) (nameApartnessToExternal apart)) := classOfInverse apart

theorem allReadoutLaws : SetoidOrderedArchimedeanReadout := setoidOrderedArchimedeanReadout

theorem inverseReadoutTwoWitnesses :
    SetoidEquivalent (externalInverse one firstApartness) (externalInverse one secondApartness) :=
  allReadoutLaws.inverseWitnessIndependent firstApartness secondApartness

theorem inverseReadoutUnit :
    SetoidEquivalent (mulValue one (externalInverse one secondApartness)) one :=
  allReadoutLaws.inverseUnitRight (allReadoutLaws.inverseFromWitness secondApartness)

def receivedExternalFamily (name : RegularDyadicName) : ExternalPresentedFamily where
  terms n := classOf ((RegularDyadicName.nonidentityFamily name).name n)
  name := (RegularDyadicName.nonidentityFamily name).name
  member n := classOfContains _
  modulus := (RegularDyadicName.nonidentityFamily name).modulus
  modulusMonotone := (RegularDyadicName.nonidentityFamily name).modulusMonotone
  cauchy := (RegularDyadicName.nonidentityFamily name).cauchy

theorem nonidentityExternalModule (name : RegularDyadicName) (p : Nat) :
    (receivedExternalFamily name).modulus p = p + 2 := rfl

theorem externalFamilyNamesExact (name : RegularDyadicName) (n : Nat) :
    (referenceFamily (receivedExternalFamily name)).terms n = constantName (name.approximation n) := rfl

theorem completionUsesSingleReferenceProduction (name : RegularDyadicName) :
    (externalComplete (receivedExternalFamily name)).value =
      classOf ((regularPresentedCompletion.complete (referenceFamily (receivedExternalFamily name))).value) :=
  externalCompleteExact _

theorem completedCandidateExact (name : RegularDyadicName) :
    (externalComplete (receivedExternalFamily name)).convergence.candidateName =
      (regularPresentedCompletion.complete (referenceFamily (receivedExternalFamily name))).value :=
  externalCandidateExact _

/-- Test-only varying rational values; no second production master is introduced. -/
def decayingCode (n : Nat) : SignedDyadicCode := ⟨1, 0, n⟩

def decayingNearZero (p n : Nat) (beyond : PrecisionExtension p n) :
    Near p (decayingCode n) SignedDyadicCode.zero where
  scale := ⟨n, 0, n, rfl, Nat.zero_add _⟩
  precisionExtra := beyond.extra
  precisionExact := beyond.exact
  leftBound := by
    change 1 + scaleNat 0 n ≤ scaleNat 0 n + 0 + powerOfTwo beyond.extra
    rw [SignedDyadicCode.scaleNat_zero, Nat.add_zero, Nat.zero_add]
    have bound := powerOfTwo_extension 0 beyond.extra
    rw [Nat.zero_add] at bound
    exact bound
  rightBound := by
    change scaleNat 0 n + 0 ≤ 1 + scaleNat 0 n + powerOfTwo beyond.extra
    rw [SignedDyadicCode.scaleNat_zero, Nat.add_zero]
    exact Nat.zero_le _

def decayingExternalFamily : ExternalPresentedFamily where
  terms n := classOf (constantName (decayingCode n))
  name n := constantName (decayingCode n)
  member n := classOfContains _
  modulus p := p + 1
  modulusMonotone extension := extension.succ
  cauchy p n m r s hn hm hr hs := Near.ofSameLeft (constantNameSameValue _ r)
    (Near.ofSameRight
      (Near.compose (decayingNearZero (p + 1) n hn) (decayingNearZero (p + 1) m hm).symm)
      (constantNameSameValue _ s).symm)

def decayingTermsOrdered : NameOrder (decayingExternalFamily.name 1) (decayingExternalFamily.name 0) := by
  have gap : StrictSeparation 2 (decayingCode 1) (decayingCode 0) :=
    ⟨⟨2, 1, 2, rfl, rfl⟩, 0, rfl, by decide⟩
  exact ⟨2, 5, .refl _,
    (gap.ofSameRight (constantNameSameValue (decayingCode 0) 5).symm).ofSameLeft
      (constantNameSameValue (decayingCode 1) 5)⟩

theorem decayingValuesDistinct :
    SetoidEquivalent (decayingExternalFamily.terms 1) (decayingExternalFamily.terms 0) → False := by
  intro same
  obtain ⟨same⟩ := same
  exact (decayingTermsOrdered.refutesEquivalent (classOfReflects same)).elim

theorem decayingModulusNonidentity (p : Nat) : decayingExternalFamily.modulus p ≠ p := by
  intro same
  exact Nat.noConfusion (addLeftCancel (same.trans (Nat.add_zero p).symm))

def decayingConvergesZero : ExternalConverges decayingExternalFamily zero where
  candidateName := zeroName
  candidateMember := classOfContains _
  threshold p := p
  near p n r s hn hr hs := Near.ofSameLeft (constantNameSameValue _ r)
    (Near.ofSameRight (decayingNearZero p n ((PrecisionExtension.next p).trans hn))
      (constantNameSameValue SignedDyadicCode.zero s).symm)

def decayingProducedValueIsZero : ExternalEquivalent (externalComplete decayingExternalFamily).value zero :=
  (externalComplete decayingExternalFamily).unique decayingConvergesZero

theorem decayingCompleteExact : (externalComplete decayingExternalFamily).value =
    classOf ((regularPresentedCompletion.complete (referenceFamily decayingExternalFamily)).value) :=
  externalCompleteExact _

end RelationalPerimeter.Tests.ExtensiveCauchyReal

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Tests.ExtensiveCauchyReal.receivedReferenceCoverage
#print axioms RelationalPerimeter.Tests.ExtensiveCauchyReal.referenceCarrierExact
#print axioms RelationalPerimeter.Tests.ExtensiveCauchyReal.receivedTailMember
#print axioms RelationalPerimeter.Tests.ExtensiveCauchyReal.taggedClass
#print axioms RelationalPerimeter.Tests.ExtensiveCauchyReal.taggedClassEquivalent
#print axioms RelationalPerimeter.Tests.ExtensiveCauchyReal.taggedFirstMember
#print axioms RelationalPerimeter.Tests.ExtensiveCauchyReal.taggedSecondMember
#print axioms RelationalPerimeter.Tests.ExtensiveCauchyReal.taggedValueReferenceCoverage
#print axioms RelationalPerimeter.Tests.ExtensiveCauchyReal.twoMembersDiffer
#print axioms RelationalPerimeter.Tests.ExtensiveCauchyReal.receivedReferenceCorrect
#print axioms RelationalPerimeter.Tests.ExtensiveCauchyReal.receivedReferenceFaithful
#print axioms RelationalPerimeter.Tests.ExtensiveCauchyReal.identityNameMap
#print axioms RelationalPerimeter.Tests.ExtensiveCauchyReal.identityNameRespect
#print axioms RelationalPerimeter.Tests.ExtensiveCauchyReal.firstDescent
#print axioms RelationalPerimeter.Tests.ExtensiveCauchyReal.secondDescent
#print axioms RelationalPerimeter.Tests.ExtensiveCauchyReal.twoDescentOutputs
#print axioms RelationalPerimeter.Tests.ExtensiveCauchyReal.identityExtendsClassMap
#print axioms RelationalPerimeter.Tests.ExtensiveCauchyReal.universalIdentity
#print axioms RelationalPerimeter.Tests.ExtensiveCauchyReal.morphismIdentityLeft
#print axioms RelationalPerimeter.Tests.ExtensiveCauchyReal.morphismIdentityRight
#print axioms RelationalPerimeter.Tests.ExtensiveCauchyReal.compositeDescent
#print axioms RelationalPerimeter.Tests.ExtensiveCauchyReal.raisedReference
#print axioms RelationalPerimeter.Tests.ExtensiveCauchyReal.raisedGraph
#print axioms RelationalPerimeter.Tests.ExtensiveCauchyReal.raisedGraphIdentity
#print axioms RelationalPerimeter.Tests.ExtensiveCauchyReal.receivedOperationComparisons
#print axioms RelationalPerimeter.Tests.ExtensiveCauchyReal.densityFiniteReadoutExact
#print axioms RelationalPerimeter.Tests.ExtensiveCauchyReal.boundsFiniteReadoutExact
#print axioms RelationalPerimeter.Tests.ExtensiveCauchyReal.shiftedZero
#print axioms RelationalPerimeter.Tests.ExtensiveCauchyReal.shiftedZeroMember
#print axioms RelationalPerimeter.Tests.ExtensiveCauchyReal.canonicalUnitOrder
#print axioms RelationalPerimeter.Tests.ExtensiveCauchyReal.shiftedUnitOrder
#print axioms RelationalPerimeter.Tests.ExtensiveCauchyReal.shiftedZeroNotCanonical
#print axioms RelationalPerimeter.Tests.ExtensiveCauchyReal.firstApartness
#print axioms RelationalPerimeter.Tests.ExtensiveCauchyReal.secondApartness
#print axioms RelationalPerimeter.Tests.ExtensiveCauchyReal.distinctWitnessAccuracies
#print axioms RelationalPerimeter.Tests.ExtensiveCauchyReal.shiftedZeroThreeLinks
#print axioms RelationalPerimeter.Tests.ExtensiveCauchyReal.zeroAuxiliaryExact
#print axioms RelationalPerimeter.Tests.ExtensiveCauchyReal.zeroFirstLink
#print axioms RelationalPerimeter.Tests.ExtensiveCauchyReal.zeroSecondLink
#print axioms RelationalPerimeter.Tests.ExtensiveCauchyReal.zeroThirdLink
#print axioms RelationalPerimeter.Tests.ExtensiveCauchyReal.inverseAwayExact
#print axioms RelationalPerimeter.Tests.ExtensiveCauchyReal.inverseSourceBeyondExact
#print axioms RelationalPerimeter.Tests.ExtensiveCauchyReal.inverseNormalizedNonzero
#print axioms RelationalPerimeter.Tests.ExtensiveCauchyReal.inverseRoundingSchedule
#print axioms RelationalPerimeter.Tests.ExtensiveCauchyReal.inverseTwoWitnesses
#print axioms RelationalPerimeter.Tests.ExtensiveCauchyReal.exactClassInverse
#print axioms RelationalPerimeter.Tests.ExtensiveCauchyReal.allReadoutLaws
#print axioms RelationalPerimeter.Tests.ExtensiveCauchyReal.inverseReadoutTwoWitnesses
#print axioms RelationalPerimeter.Tests.ExtensiveCauchyReal.inverseReadoutUnit
#print axioms RelationalPerimeter.Tests.ExtensiveCauchyReal.receivedExternalFamily
#print axioms RelationalPerimeter.Tests.ExtensiveCauchyReal.nonidentityExternalModule
#print axioms RelationalPerimeter.Tests.ExtensiveCauchyReal.externalFamilyNamesExact
#print axioms RelationalPerimeter.Tests.ExtensiveCauchyReal.completionUsesSingleReferenceProduction
#print axioms RelationalPerimeter.Tests.ExtensiveCauchyReal.completedCandidateExact
#print axioms RelationalPerimeter.Tests.ExtensiveCauchyReal.decayingCode
#print axioms RelationalPerimeter.Tests.ExtensiveCauchyReal.decayingNearZero
#print axioms RelationalPerimeter.Tests.ExtensiveCauchyReal.decayingExternalFamily
#print axioms RelationalPerimeter.Tests.ExtensiveCauchyReal.decayingTermsOrdered
#print axioms RelationalPerimeter.Tests.ExtensiveCauchyReal.decayingValuesDistinct
#print axioms RelationalPerimeter.Tests.ExtensiveCauchyReal.decayingModulusNonidentity
#print axioms RelationalPerimeter.Tests.ExtensiveCauchyReal.decayingConvergesZero
#print axioms RelationalPerimeter.Tests.ExtensiveCauchyReal.decayingProducedValueIsZero
#print axioms RelationalPerimeter.Tests.ExtensiveCauchyReal.decayingCompleteExact
/- AXIOM_AUDIT_END -/
