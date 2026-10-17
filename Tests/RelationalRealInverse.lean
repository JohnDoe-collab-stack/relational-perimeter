import Tests.RelationalRealInverseRaccord
import RelationalPerimeter.Constitution.Reals.RelationalRealInverseCorrespondence

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace RelationalPerimeter.Tests.RelationalRealInverse
open StrongPerimetralTurning
open RelationalPerimeter.Constitution.Reals
open RuntimeCorrespondence HeterogeneousRealRuntime RelationalRealAddition RelationalRealOrder
open RelationalPerimeter.Constitution.Reals.RelationalRealInverse DyadicReciprocal
variable (P : CircularPresentation) (depth : Nat)

def domain := RelationalRealInverseRaccord.positiveDomain P depth
def inv := inverse (one P depth) (domain P depth)
def product : Real P depth := .mul (one P depth) (inv P depth)
def firstProduct := executeReal (product P depth) 0
def currentProduct (p : Nat) := executeAt (product P depth) (firstProduct P depth).next
  (p + 1 + probeAmplitude (readout (inv P depth) 0))

def unitFromCurrentPacket (p : Nat) : Near p (currentProduct P depth p).code SignedDyadicCode.one := by
  dsimp only [currentProduct, firstProduct, product, inv]
  apply mul_inverse_step (currentProduct P depth p)
  dsimp only [currentProduct, firstProduct, product, inv]
  rw [currentReadout _ _ _]
  exact PrecisionExtension.refl _

theorem currentProductArchives : (currentProduct P depth 0).resource.leftProbe =
    executeAt (one P depth) (firstProduct P depth).next.left 0 ∧
    (currentProduct P depth 0).resource.rightProbe = executeAt (inv P depth) (firstProduct P depth).next.right 0 :=
  ⟨rfl, rfl⟩

def rightUnit := mul_inverse (one P depth) (domain P depth)
def leftUnit := inverse_mul (one P depth) (domain P depth)
def rightFutureUnit := mul_inverse_futures (one P depth) (domain P depth)
def leftFutureUnit := inverse_mul_futures (one P depth) (domain P depth)

def newDomain : Apartness (one P depth) (zero P depth) :=
  reflectPresentationApartness (domain P depth).toPresentation
    (RelationalRealInverseRaccord.first P depth 0).next.source
    (environment (zero P depth)).initialArchive

def witnessIndependent := witness_independent (one P depth) (domain P depth) (newDomain P depth)
def witnessIndependentFutures := witness_independent_futures (one P depth) (domain P depth) (newDomain P depth)

def negativeRightUnit := mul_inverse (.neg (RelationalRealRuntime.sum P depth))
  (RelationalRealInverseRaccord.negativeDomain P depth)
def negativeLeftUnit := inverse_mul (.neg (RelationalRealRuntime.sum P depth))
  (RelationalRealInverseRaccord.negativeDomain P depth)
def negativeFutureUnit := inverse_mul_futures (.neg (RelationalRealRuntime.sum P depth))
  (RelationalRealInverseRaccord.negativeDomain P depth)

def cancelled : Real P depth := .leaf (constantRuntime P depth ⟨10001, 10000, 0⟩)
def cancelledEquivalent : Equivalent (one P depth) (cancelled P depth) := Equivalent.ofExact (fun p =>
  (constant_readout SignedDyadicCode.one p).trans
    ((⟨⟨0, 0, 0, rfl, rfl⟩, by decide⟩ : SameValue SignedDyadicCode.one ⟨10001, 10000, 0⟩).trans
      (constant_readout (⟨10001, 10000, 0⟩ : SignedDyadicCode) p).symm))

def cancelledDomain : Apartness (cancelled P depth) (zero P depth) :=
  transportApartness (domain P depth) (cancelledEquivalent P depth) (Equivalent.refl _)
    (environment (cancelled P depth)).initialArchive (environment (zero P depth)).initialArchive
def cancelledUnit := mul_inverse (cancelled P depth) (cancelledDomain P depth)
def occurrenceIndependent := inverse_congr (cancelledEquivalent P depth) (domain P depth) (cancelledDomain P depth)
def occurrenceIndependentFutures := inverse_congr_futures (cancelledEquivalent P depth).toFutures
  (domain P depth) (cancelledDomain P depth)

def presentationTransport := toPresentation_inverse (one P depth) (domain P depth)
def presentationRealization := realization_inverse (toPresentation (one P depth)) (domain P depth).toPresentation
def carrierTransport := toCarrier_inverse (one P depth) (domain P depth)
def carrierRealization := realization_carrier_inverse (toCarrier (one P depth)) (domain P depth).toCarrier

def futureQuery (p : Nat) : LimitQuery (rightFutureUnit P depth).threshold :=
  ⟨p, (rightFutureUnit P depth).threshold p, (rightFutureUnit P depth).threshold p,
    PrecisionExtension.refl _, PrecisionExtension.refl _⟩
def currentFutureTrace := (rightFutureUnit P depth).traces (firstProduct P depth).next
  (executeReal (one P depth) 0).next [futureQuery P depth 0, futureQuery P depth 1]

theorem zeroFallback : ReciprocalRuntime.liveCode .positive SignedDyadicCode.zero 2 = ⟨0, 0, 4⟩ := rfl

end RelationalPerimeter.Tests.RelationalRealInverse

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Tests.RelationalRealInverse.domain
#print axioms RelationalPerimeter.Tests.RelationalRealInverse.inv
#print axioms RelationalPerimeter.Tests.RelationalRealInverse.product
#print axioms RelationalPerimeter.Tests.RelationalRealInverse.firstProduct
#print axioms RelationalPerimeter.Tests.RelationalRealInverse.currentProduct
#print axioms RelationalPerimeter.Tests.RelationalRealInverse.unitFromCurrentPacket
#print axioms RelationalPerimeter.Tests.RelationalRealInverse.currentProductArchives
#print axioms RelationalPerimeter.Tests.RelationalRealInverse.rightUnit
#print axioms RelationalPerimeter.Tests.RelationalRealInverse.leftUnit
#print axioms RelationalPerimeter.Tests.RelationalRealInverse.rightFutureUnit
#print axioms RelationalPerimeter.Tests.RelationalRealInverse.leftFutureUnit
#print axioms RelationalPerimeter.Tests.RelationalRealInverse.newDomain
#print axioms RelationalPerimeter.Tests.RelationalRealInverse.witnessIndependent
#print axioms RelationalPerimeter.Tests.RelationalRealInverse.witnessIndependentFutures
#print axioms RelationalPerimeter.Tests.RelationalRealInverse.negativeRightUnit
#print axioms RelationalPerimeter.Tests.RelationalRealInverse.negativeLeftUnit
#print axioms RelationalPerimeter.Tests.RelationalRealInverse.negativeFutureUnit
#print axioms RelationalPerimeter.Tests.RelationalRealInverse.cancelled
#print axioms RelationalPerimeter.Tests.RelationalRealInverse.cancelledEquivalent
#print axioms RelationalPerimeter.Tests.RelationalRealInverse.cancelledDomain
#print axioms RelationalPerimeter.Tests.RelationalRealInverse.cancelledUnit
#print axioms RelationalPerimeter.Tests.RelationalRealInverse.occurrenceIndependent
#print axioms RelationalPerimeter.Tests.RelationalRealInverse.occurrenceIndependentFutures
#print axioms RelationalPerimeter.Tests.RelationalRealInverse.presentationTransport
#print axioms RelationalPerimeter.Tests.RelationalRealInverse.presentationRealization
#print axioms RelationalPerimeter.Tests.RelationalRealInverse.carrierTransport
#print axioms RelationalPerimeter.Tests.RelationalRealInverse.carrierRealization
#print axioms RelationalPerimeter.Tests.RelationalRealInverse.futureQuery
#print axioms RelationalPerimeter.Tests.RelationalRealInverse.currentFutureTrace
#print axioms RelationalPerimeter.Tests.RelationalRealInverse.zeroFallback
/- AXIOM_AUDIT_END -/
