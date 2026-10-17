import RelationalPerimeter.Constitution.Reals.RelationalRealEffectiveCorrespondence
import Tests.RelationalRealNativeCauchy

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace RelationalPerimeter.Tests.RelationalRealEffectiveCorrespondence
open StrongPerimetralTurning
open RelationalPerimeter.Constitution.Reals
open ProducedCompleteness RuntimeCorrespondence HeterogeneousRealRuntime ConstitutiveRuntime
open RelationalRealAddition RelationalRealOrder RelationalRealCauchy
open RelationalPerimeter.Constitution.Reals.RelationalRealFamilyTransport
open RelationalPerimeter.Constitution.Reals.RelationalRealLimitUniqueness
open RelationalPerimeter.Constitution.Reals.RelationalRealEffectiveCorrespondence
variable {P : CircularPresentation} {d : Nat}

def terminal (P : CircularPresentation) (d : Nat) := effectiveCorrespondence P d

theorem exportedTo (a : Real P d) : (terminal P d).applications.toEffective a = toPresentation a := rfl

theorem exportedFrom (a : EffectiveDyadicPresentation) : (terminal P d).applications.fromEffective a = ofPresentation P d a := rfl

def realRoundtrip (a : Real P d) := (terminal P d).applications.realReturn a

def realFutureRoundtrip (a : Real P d) := (terminal P d).applications.realFutureReturn a

def presentationRoundtrip (a : EffectiveDyadicPresentation) := (terminal P d).applications.effectiveReturn a

def carrierRoundtrip (a : EffectiveCauchyReal.Carrier) := (terminal P d).applications.carrierReturn a

def realCarrierRoundtrip (a : Real P d) := (terminal P d).applications.realCarrierFutureReturn a

def numericEquivalent {a b : Real P d} (same : Equivalent a b) := (terminal P d).applications.preserveEquivalent same

def equivalenceReflected {a b : Real P d} (same : EffectiveDyadicPresentation.Equivalent (toPresentation a) (toPresentation b)) := (terminal P d).applications.reflectEquivalent same

def zeroPreserved (P : CircularPresentation) (d : Nat) := (terminal P d).operations.zero

def onePreserved (P : CircularPresentation) (d : Nat) := (terminal P d).operations.one

def constantRealized (code : SignedDyadicCode) := (terminal P d).operations.realizeConstants code

def addPreserved (a b : Real P d) := (terminal P d).operations.add a b

def negPreserved (a : Real P d) := (terminal P d).operations.neg a

def mulPreserved (a b : Real P d) := (terminal P d).operations.mul a b

def addRealized (a b : EffectiveDyadicPresentation) := (terminal P d).operations.realizeAdd a b

def negRealized (a : EffectiveDyadicPresentation) := (terminal P d).operations.realizeNeg a

def mulRealized (a b : EffectiveDyadicPresentation) := (terminal P d).operations.realizeMul a b

def carrierAdd (a b : Real P d) := (terminal P d).operations.carrierAdd a b

def carrierNeg (a : Real P d) := (terminal P d).operations.carrierNeg a

def carrierMul (a b : Real P d) := (terminal P d).operations.carrierMul a b

def carrierAddRealized (a b : EffectiveCauchyReal.Carrier) := (terminal P d).operations.realizeCarrierAdd a b

def carrierNegRealized (a : EffectiveCauchyReal.Carrier) := (terminal P d).operations.realizeCarrierNeg a

def carrierMulRealized (a b : EffectiveCauchyReal.Carrier) := (terminal P d).operations.realizeCarrierMul a b

def inversePreserved (a : Real P d) (w : Apartness a (zero P d)) := (terminal P d).operations.inverse a w

def inverseRealized (a : EffectiveDyadicPresentation) (w : RelationalRealInverse.PresentationDomain P d a) := (terminal P d).operations.realizeInverse a w

def carrierInverse (a : Real P d) (w : Apartness a (zero P d)) := (terminal P d).operations.carrierInverse a w

def carrierInverseRealized (a : EffectiveCauchyReal.Carrier) (w : RelationalRealInverse.CarrierDomain P d a) := (terminal P d).operations.realizeCarrierInverse a w

def orderPreserved {a b : Real P d} (order : StrictOrder a b) := (terminal P d).relations.order order

def apartnessPreserved {a b : Real P d} (apart : Apartness a b) := (terminal P d).relations.apartness apart

def orderReflected {a b : Real P d} (order : PresentationOrder (toPresentation a) (toPresentation b)) (aa : (environment a).Archive) (ba : (environment b).Archive) := (terminal P d).relations.reflectOrder order aa ba

def apartnessRealized (a b : EffectiveDyadicPresentation) (apart : PresentationApartness a b) (aa : (environment (ofPresentation P d a)).Archive) (ba : (environment (ofPresentation P d b)).Archive) := (terminal P d).relations.realizeApartness a b apart aa ba

def carrierApartnessRealized (a b : EffectiveCauchyReal.Carrier) (apart : CarrierApartness a b) (aa : (environment (ofCarrier P d a)).Archive) (ba : (environment (ofCarrier P d b)).Archive) := (terminal P d).relations.realizeCarrierApartness a b apart aa ba

def presentedAddCommutative (a b : Real P d) :
    EffectiveDyadicPresentation.Equivalent (addPresentation (toPresentation a) (toPresentation b))
      (addPresentation (toPresentation b) (toPresentation a)) :=
  ((terminal P d).operations.add a b).symm.trans
    (((terminal P d).applications.preserveEquivalent ((terminal P d).ordered.laws.additive.additive.commutative a b)).trans
      ((terminal P d).operations.add b a))

def presentedMulCommutative (a b : Real P d) :
    EffectiveDyadicPresentation.Equivalent (mulPresentation (toPresentation a) (toPresentation b))
      (mulPresentation (toPresentation b) (toPresentation a)) :=
  ((terminal P d).operations.mul a b).symm.trans
    (((terminal P d).applications.preserveEquivalent ((terminal P d).ordered.laws.multiplicative.commutative a b)).trans
      ((terminal P d).operations.mul b a))

def unitTransported (a : Real P d) (w : Apartness a (zero P d)) := (terminal P d).applications.preserveEquivalent ((terminal P d).ordered.laws.inverseUnitRight a w)

def positiveProductTransported {a b : Real P d} (pa : Positive a) (pb : Positive b) := (terminal P d).relations.order ((terminal P d).ordered.laws.positiveProduct pa pb)

def densityPacket {a b : Real P d} (order : StrictOrder a b) (journal : Journal P d) := (terminal P d).ordered.density order journal

def densityProjected {a b : Real P d} {order : StrictOrder a b} {journal : Journal P d} (packet : RelationalRealDensity.Density order journal) := (terminal P d).ordered.densityProjection packet

def boundsPacket (a : Real P d) (archive : (environment a).Archive) (journal : Journal P d) := (terminal P d).ordered.bounds a archive journal

def boundsProjected {a : Real P d} {archive : (environment a).Archive} {journal : Journal P d} (packet : RelationalRealDensity.NaturalBound a archive journal) := (terminal P d).ordered.boundProjection packet

def sourceComplete (family : ExecutedCauchyFamily P d) := (terminal P d).families.sourceCompleteness family

def effectiveComplete (numeric : EffectiveFamily) := (terminal P d).families.sourceCompleteness ((terminal P d).families.fromEffective numeric)

def effectiveReturned (numeric : EffectiveFamily) := (terminal P d).families.effectiveReturn numeric

def sourceReturned (family : ExecutedCauchyFamily P d) := (terminal P d).families.sourceReturn family

def nativeComplete (family : RelationalRealNativeCauchy.NativeCauchyFamily P d) := (terminal P d).families.nativeCompleteness family

def composedNativeComplete (family : ExecutedCauchyFamily P d) := nativeComplete (RelationalRealNativeCauchy.composedFamily family)

theorem nativeLimitProduced (family : ExecutedCauchyFamily P d) : (composedNativeComplete family).limit = RelationalPerimeter.Constitution.Reals.RelationalRealNativeCauchy.nativeLimit (RelationalRealNativeCauchy.composedFamily family) := (composedNativeComplete family).limitExact

def nativeCurrentConvergence (family : ExecutedCauchyFamily P d) := RelationalRealNativeCauchy.firstObservation family

def nativeHigherConvergence (family : ExecutedCauchyFamily P d) := RelationalRealNativeCauchy.higherObservation family

def twoNativeCandidates (family : ExecutedCauchyFamily P d) := (terminal P d).families.nativeUniqueness (RelationalRealNativeCauchy.nativeCandidate family) (RelationalRealNativeCauchy.certifiedCandidate family)

def currentLimitPreservation (family : ExecutedCauchyFamily P d) := RelationalRealFamilyTransport.observed family

def routeA (family : ExecutedCauchyFamily P d) := (terminal P d).limits.routeA family

def routeARoundtrip (family : ExecutedCauchyFamily P d) := (terminal P d).limits.sourceLimitReturn family

theorem threeSuccessors (family : ExecutedCauchyFamily P d) : (RelationalRealFamilyTransport.tail family).archives = ⟨(RelationalRealFamilyTransport.head family).termStep.next, (RelationalRealFamilyTransport.head family).firstStep.next, (RelationalRealFamilyTransport.head family).secondStep.next⟩ := RelationalRealFamilyTransport.continuesThree family

def futureProjection (family : ExecutedCauchyFamily P d) := (terminal P d).limits.projectUniqueness (RelationalRealFamilyTransport.rich family)

def richCauchyLoss (P : CircularPresentation) (d : Nat) := RelationalRealFamilyTransport.cauchyDataNotRecovered P d

theorem directSix (P : CircularPresentation) (d : Nat) : (RelationalRealFamilyTransport.directData P d).scale.common = 6 := rfl

theorem reconstructedZero (P : CircularPresentation) (d : Nat) : (RelationalRealFamilyTransport.reconstructedData P d).scale.common = 0 := rfl

def boundedCarrier (P : CircularPresentation) (d : Nat) := (terminal P d).families.fromCarriers RelationalRealFamilyTransport.boundedFamily

def boundedNotCofinal (p : Nat) (h : PrecisionExtension 1 (RelationalRealFamilyTransport.boundedCarrier.modulus p)) : Empty := RelationalRealFamilyTransport.boundedNotCofinal p h

def boundedLimitRealized (P : CircularPresentation) (d : Nat) := (terminal P d).limits.carrierRealize RelationalRealFamilyTransport.boundedFamily RelationalRealFamilyTransport.boundedCarrier RelationalRealFamilyTransport.boundedLimit

end RelationalPerimeter.Tests.RelationalRealEffectiveCorrespondence

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Tests.RelationalRealEffectiveCorrespondence.terminal
#print axioms RelationalPerimeter.Tests.RelationalRealEffectiveCorrespondence.exportedTo
#print axioms RelationalPerimeter.Tests.RelationalRealEffectiveCorrespondence.exportedFrom
#print axioms RelationalPerimeter.Tests.RelationalRealEffectiveCorrespondence.realRoundtrip
#print axioms RelationalPerimeter.Tests.RelationalRealEffectiveCorrespondence.realFutureRoundtrip
#print axioms RelationalPerimeter.Tests.RelationalRealEffectiveCorrespondence.presentationRoundtrip
#print axioms RelationalPerimeter.Tests.RelationalRealEffectiveCorrespondence.carrierRoundtrip
#print axioms RelationalPerimeter.Tests.RelationalRealEffectiveCorrespondence.realCarrierRoundtrip
#print axioms RelationalPerimeter.Tests.RelationalRealEffectiveCorrespondence.numericEquivalent
#print axioms RelationalPerimeter.Tests.RelationalRealEffectiveCorrespondence.equivalenceReflected
#print axioms RelationalPerimeter.Tests.RelationalRealEffectiveCorrespondence.zeroPreserved
#print axioms RelationalPerimeter.Tests.RelationalRealEffectiveCorrespondence.onePreserved
#print axioms RelationalPerimeter.Tests.RelationalRealEffectiveCorrespondence.constantRealized
#print axioms RelationalPerimeter.Tests.RelationalRealEffectiveCorrespondence.addPreserved
#print axioms RelationalPerimeter.Tests.RelationalRealEffectiveCorrespondence.negPreserved
#print axioms RelationalPerimeter.Tests.RelationalRealEffectiveCorrespondence.mulPreserved
#print axioms RelationalPerimeter.Tests.RelationalRealEffectiveCorrespondence.addRealized
#print axioms RelationalPerimeter.Tests.RelationalRealEffectiveCorrespondence.negRealized
#print axioms RelationalPerimeter.Tests.RelationalRealEffectiveCorrespondence.mulRealized
#print axioms RelationalPerimeter.Tests.RelationalRealEffectiveCorrespondence.carrierAdd
#print axioms RelationalPerimeter.Tests.RelationalRealEffectiveCorrespondence.carrierNeg
#print axioms RelationalPerimeter.Tests.RelationalRealEffectiveCorrespondence.carrierMul
#print axioms RelationalPerimeter.Tests.RelationalRealEffectiveCorrespondence.carrierAddRealized
#print axioms RelationalPerimeter.Tests.RelationalRealEffectiveCorrespondence.carrierNegRealized
#print axioms RelationalPerimeter.Tests.RelationalRealEffectiveCorrespondence.carrierMulRealized
#print axioms RelationalPerimeter.Tests.RelationalRealEffectiveCorrespondence.inversePreserved
#print axioms RelationalPerimeter.Tests.RelationalRealEffectiveCorrespondence.inverseRealized
#print axioms RelationalPerimeter.Tests.RelationalRealEffectiveCorrespondence.carrierInverse
#print axioms RelationalPerimeter.Tests.RelationalRealEffectiveCorrespondence.carrierInverseRealized
#print axioms RelationalPerimeter.Tests.RelationalRealEffectiveCorrespondence.orderPreserved
#print axioms RelationalPerimeter.Tests.RelationalRealEffectiveCorrespondence.apartnessPreserved
#print axioms RelationalPerimeter.Tests.RelationalRealEffectiveCorrespondence.orderReflected
#print axioms RelationalPerimeter.Tests.RelationalRealEffectiveCorrespondence.apartnessRealized
#print axioms RelationalPerimeter.Tests.RelationalRealEffectiveCorrespondence.carrierApartnessRealized
#print axioms RelationalPerimeter.Tests.RelationalRealEffectiveCorrespondence.presentedAddCommutative
#print axioms RelationalPerimeter.Tests.RelationalRealEffectiveCorrespondence.presentedMulCommutative
#print axioms RelationalPerimeter.Tests.RelationalRealEffectiveCorrespondence.unitTransported
#print axioms RelationalPerimeter.Tests.RelationalRealEffectiveCorrespondence.positiveProductTransported
#print axioms RelationalPerimeter.Tests.RelationalRealEffectiveCorrespondence.densityPacket
#print axioms RelationalPerimeter.Tests.RelationalRealEffectiveCorrespondence.densityProjected
#print axioms RelationalPerimeter.Tests.RelationalRealEffectiveCorrespondence.boundsPacket
#print axioms RelationalPerimeter.Tests.RelationalRealEffectiveCorrespondence.boundsProjected
#print axioms RelationalPerimeter.Tests.RelationalRealEffectiveCorrespondence.sourceComplete
#print axioms RelationalPerimeter.Tests.RelationalRealEffectiveCorrespondence.effectiveComplete
#print axioms RelationalPerimeter.Tests.RelationalRealEffectiveCorrespondence.effectiveReturned
#print axioms RelationalPerimeter.Tests.RelationalRealEffectiveCorrespondence.sourceReturned
#print axioms RelationalPerimeter.Tests.RelationalRealEffectiveCorrespondence.nativeComplete
#print axioms RelationalPerimeter.Tests.RelationalRealEffectiveCorrespondence.composedNativeComplete
#print axioms RelationalPerimeter.Tests.RelationalRealEffectiveCorrespondence.nativeLimitProduced
#print axioms RelationalPerimeter.Tests.RelationalRealEffectiveCorrespondence.nativeCurrentConvergence
#print axioms RelationalPerimeter.Tests.RelationalRealEffectiveCorrespondence.nativeHigherConvergence
#print axioms RelationalPerimeter.Tests.RelationalRealEffectiveCorrespondence.twoNativeCandidates
#print axioms RelationalPerimeter.Tests.RelationalRealEffectiveCorrespondence.currentLimitPreservation
#print axioms RelationalPerimeter.Tests.RelationalRealEffectiveCorrespondence.routeA
#print axioms RelationalPerimeter.Tests.RelationalRealEffectiveCorrespondence.routeARoundtrip
#print axioms RelationalPerimeter.Tests.RelationalRealEffectiveCorrespondence.threeSuccessors
#print axioms RelationalPerimeter.Tests.RelationalRealEffectiveCorrespondence.futureProjection
#print axioms RelationalPerimeter.Tests.RelationalRealEffectiveCorrespondence.richCauchyLoss
#print axioms RelationalPerimeter.Tests.RelationalRealEffectiveCorrespondence.directSix
#print axioms RelationalPerimeter.Tests.RelationalRealEffectiveCorrespondence.reconstructedZero
#print axioms RelationalPerimeter.Tests.RelationalRealEffectiveCorrespondence.boundedCarrier
#print axioms RelationalPerimeter.Tests.RelationalRealEffectiveCorrespondence.boundedNotCofinal
#print axioms RelationalPerimeter.Tests.RelationalRealEffectiveCorrespondence.boundedLimitRealized
/- AXIOM_AUDIT_END -/
