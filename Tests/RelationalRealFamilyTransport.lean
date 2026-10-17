import RelationalPerimeter.Constitution.Reals.RelationalRealFamilyTransport
import Tests.RelationalRealLimitUniqueness
import Tests.RelationalRealDensity

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace RelationalPerimeter.Tests.RelationalRealFamilyTransport
open StrongPerimetralTurning
open RelationalPerimeter.Constitution.Reals
open ConstitutiveRuntime ProducedCompleteness RuntimeCorrespondence
open HeterogeneousRealRuntime RelationalRealAddition RelationalRealCauchy RelationalRealLimitUniqueness
open RelationalPerimeter.Constitution.Reals.RelationalRealFamilyTransport

variable {P : CircularPresentation} {d : Nat} (family : ExecutedCauchyFamily P d)

def previousTerm := executeReal (termReal (returnedFamily family) 0) 2
def previousFirst := executeReal (limitReal (returnedFamily family)) 3
def previousSecond := executeReal (limitReal family) 4
def queryOne : LimitQuery (uniquenessThreshold (returnedAuthoritative family) (returnedCandidate family)) :=
  ⟨0, 2, 3, .refl _, ⟨1, rfl⟩⟩
def queryTwo : LimitQuery (uniquenessThreshold (returnedAuthoritative family) (returnedCandidate family)) :=
  ⟨2, 7, 8, ⟨1, rfl⟩, ⟨2, rfl⟩⟩
def head := mediate (returnedAuthoritative family) (returnedCandidate family)
  (previousTerm family).next (previousFirst family).next (previousSecond family).next (queryOne family)
def tail := mediate (returnedAuthoritative family) (returnedCandidate family)
  (head family).termStep.next (head family).firstStep.next (head family).secondStep.next (queryTwo family)
def rich := produceTrace (returnedAuthoritative family) (returnedCandidate family)
  (previousTerm family).next (previousFirst family).next (previousSecond family).next
  [queryOne family, queryTwo family]
theorem continuesThree : (tail family).archives =
    ⟨(head family).termStep.next, (head family).firstStep.next, (head family).secondStep.next⟩ :=
  (tail family).archivesExact
theorem termIndexChanges : (tail family).termStep = executeAt
    (termReal (returnedFamily family) (family.modulus 3)) (head family).termStep.next 3 :=
  (tail family).termExact
theorem wholeTrace : rich family = .step (head family)
    (.step (tail family) (.done (tail family).termStep.next (tail family).firstStep.next (tail family).secondStep.next)) := rfl
theorem projectionShared : (rich family).toNumerical =
    .step (head family).firstStep (head family).secondStep (head family).firstExact (head family).secondExact (head family).near
      (.step (tail family).firstStep (tail family).secondStep (tail family).firstExact (tail family).secondExact
        (tail family).near (.done (tail family).firstStep.next (tail family).secondStep.next)) := rfl
def roundtrip := relationalLimitRoundtrip family
def futureFromCurrent := (roundtrip family).2.traces
  (previousFirst family).next (previousSecond family).next [queryOne family, queryTwo family]
theorem uniformThreshold : (relationalTermRoundtrip family 0).threshold 2 = 2 := rfl
theorem restoredProducer : (returnedFamily family).producer = family.producer := returnedProducer family
theorem restoredModulus : (returnedFamily family).modulus = family.modulus := returnedModulus family
def termFuture := (relationalTermFutures family 0).traces
  (previousTerm family).next (executeReal (termReal family 0) 1).next
  [⟨0, 1, 2, ⟨1, rfl⟩, ⟨2, rfl⟩⟩, ⟨2, 3, 4, ⟨1, rfl⟩, ⟨2, rfl⟩⟩]
def observed := observeLimit (returnedCandidate family) 0 (family.modulus 0) 2 3
  (previousTerm family).next (previousSecond family).next
  (.refl _) ⟨2, rfl⟩ ⟨3, rfl⟩


theorem observedCurrentTerm : (observed family).termStep = executeAt
    (termReal (returnedFamily family) (family.modulus 0)) (previousTerm family).next 2 :=
  (observed family).termExact
theorem observedCurrentCandidate : (observed family).candidateStep = executeAt
    (limitReal family) (previousSecond family).next 3 := (observed family).candidateExact
theorem observedNearShared : (observed family).numerical =
    projectLimitNear (returnedCandidate family) 0 (family.modulus 0) 2 3
      (observed family).termStep (observed family).candidateStep (observed family).near :=
  (observed family).numericalExact
theorem observedNearNotReconstructed : HEq (observed family).numerical (observed family).near := by
  rw [(observed family).numericalExact]
  exact projectLimitNear_heq _ _ _ _ _ _ _ _
def globalLimit := preserveLimit (authoritative family)
def reflectedLimit := reflectLimit (limitReal family) (globalLimit family)
def reflectedUnique := authoritativeUnique (reflectedLimit family)
def realizedNumericLimit := realizeLimit (P := P) (baseDepth := d)
  (readoutFamily family) (toPresentation (limitReal family)) (globalLimit family)
def realizedNumericUnique := realizedLimitEquivalence (P := P) (baseDepth := d)
  (readoutFamily family) (toPresentation (limitReal family)) (globalLimit family)
theorem effectiveCodes (n p : Nat) :
    ((readoutFamily (realizeFamily P d (readoutFamily family))).terms n).approximation p =
      ((readoutFamily family).terms n).approximation p := effectiveReturnAt _ _ _
def effectiveBehaviour := effectiveRoundtrip (P := P) (baseDepth := d) (readoutFamily family)

/-- Test-only family: positive Cauchy data records the actual first journal.
It is a counterexample to rich-data preservation, not another production master. -/
def taggedFamily (P : CircularPresentation) (d : Nat) : ExecutedCauchyFamily P d where
  producer := ⟨fun _ => SignedDyadicCode.zero⟩
  termCoherent _ p _ _ _ _ := Near.refl p _
  modulus _ := 0
  modulusMonotone _ := .refl 0
  cauchy := by
    intro p fj sj fr sr fn sn fp sp first second
    have fe : first.readout = SignedDyadicCode.zero := by
      rw [first.readout_is_storedAction, sourceProgram_actionCode_exact]
    have se : second.readout = SignedDyadicCode.zero := by
      rw [second.readout_is_storedAction, sourceProgram_actionCode_exact]
    rw [fe, se]
    exact (Near.refl p SignedDyadicCode.zero).liftCommon fj.relativeDepth

def taggedTerm (P : CircularPresentation) (d : Nat) :=
  executeAt (termReal (returnedFamily (taggedFamily P d)) 0) (previousTerm (taggedFamily P d)).next 3
def taggedOldLimit (P : CircularPresentation) (d : Nat) :=
  executeAt (limitReal (taggedFamily P d)) (previousSecond (taggedFamily P d)).next 3
def taggedNewLimit (P : CircularPresentation) (d : Nat) :=
  executeAt (limitReal (returnedFamily (taggedFamily P d))) (previousFirst (taggedFamily P d)).next 3
def directData (P : CircularPresentation) (d : Nat) :=
  (returnedCandidate (taggedFamily P d)).converges 0 0 3 3
    (taggedTerm P d) (taggedOldLimit P d) (.refl _) ⟨3, rfl⟩ ⟨3, rfl⟩
def reconstructedData (P : CircularPresentation) (d : Nat) :=
  (returnedAuthoritative (taggedFamily P d)).converges 0 0 3 3
    (taggedTerm P d) (taggedNewLimit P d) (.refl _) ⟨3, rfl⟩ ⟨3, rfl⟩
theorem directScale (P : CircularPresentation) (d : Nat) : (directData P d).scale.common = 6 := rfl
theorem reconstructedScale (P : CircularPresentation) (d : Nat) : (reconstructedData P d).scale.common = 0 := rfl
def cauchyDataNotRecovered (P : CircularPresentation) (d : Nat)
    (same : (directData P d).scale.common = (reconstructedData P d).scale.common) : Empty := by
  change (6 : Nat) = 0 at same
  cases same

def boundedCarrier : EffectiveCauchyReal.Carrier where
  approximation _ := SignedDyadicCode.zero
  modulus _ := 0
  modulusMonotone _ := .refl 0
  cauchy p _ _ _ _ := Near.refl p _
def boundedFamily : CarrierFamily where
  terms _ := boundedCarrier
  modulus _ := 0
  modulusMonotone _ := .refl 0
  cauchy p _ _ _ _ _ _ _ _ := Near.refl p _
def boundedNotCofinal (p : Nat) (extension : PrecisionExtension 1 (boundedCarrier.modulus p)) : Empty := by
  have impossible : Nat.succ extension.extra = 0 := by
    rw [← Nat.one_add]
    exact extension.exact
  cases impossible
def boundedLimit : CarrierLimit boundedFamily boundedCarrier where
  threshold := fun p => p
  converges p _ _ _ _ _ _ := Near.refl p _
def boundedRealization (P : CircularPresentation) (d : Nat) :=
  realizeCarrierLimit (P := P) (baseDepth := d) boundedFamily boundedCarrier boundedLimit
def boundedUnique (P : CircularPresentation) (d : Nat) := authoritativeUnique (boundedRealization P d)
def carrierReturn := carrierTermRoundtrip boundedFamily 3
theorem normalizedCodes (p : Nat) :
    ((normalizeCarrierFamily (carrierFamily (normalizeCarrierFamily boundedFamily))).terms 2).approximation p =
      SignedDyadicCode.zero := rfl
def carrierPreserved := preserveCarrierLimit (authoritative family)

/-- Canonical formation in currentReadout is checked on all five constructors
and recursively composed zero behaviours. The runtime is already native. -/
def zeroNumeric (P : CircularPresentation) (d : Nat) (real : Real P d)
    (exact : (p : Nat) → readout real p = SignedDyadicCode.zero) :
    PresentationLimit (readoutFamily (taggedFamily P d)) (toPresentation real) where
  threshold := fun p => p
  converges p _ _ s _ _ _ := by
    change Near p SignedDyadicCode.zero (readout real s)
    rw [exact s]
    exact Near.refl p _
def leafZero (P : CircularPresentation) (d : Nat) := limitReal (taggedFamily P d)
def certifiedZero (P : CircularPresentation) (d : Nat) := termReal (taggedFamily P d) 0
def addZero (P : CircularPresentation) (d : Nat) := Real.add (leafZero P d) (certifiedZero P d)
def negZero (P : CircularPresentation) (d : Nat) := Real.neg (addZero P d)
def mulZero (P : CircularPresentation) (d : Nat) := Real.mul (negZero P d) (addZero P d)
def recursiveZero (P : CircularPresentation) (d : Nat) := Real.add (mulZero P d) (.neg (mulZero P d))
def reflectedLeaf (P : CircularPresentation) (d : Nat) :=
  reflectLimit (leafZero P d) (zeroNumeric P d (leafZero P d) (fun _ => rfl))
def reflectedCertified (P : CircularPresentation) (d : Nat) :=
  reflectLimit (certifiedZero P d) (zeroNumeric P d (certifiedZero P d) (fun _ => rfl))
def reflectedAdd (P : CircularPresentation) (d : Nat) :=
  reflectLimit (addZero P d) (zeroNumeric P d (addZero P d) (fun _ => rfl))
def reflectedNeg (P : CircularPresentation) (d : Nat) :=
  reflectLimit (negZero P d) (zeroNumeric P d (negZero P d) (fun _ => rfl))
def reflectedMul (P : CircularPresentation) (d : Nat) :=
  reflectLimit (mulZero P d) (zeroNumeric P d (mulZero P d) (fun _ => rfl))
def reflectedRecursive (P : CircularPresentation) (d : Nat) :=
  reflectLimit (recursiveZero P d) (zeroNumeric P d (recursiveZero P d) (fun _ => rfl))
def reflectedAt (P : CircularPresentation) (d : Nat) (candidate : LimitCandidate (taggedFamily P d))
    (ta : TermArchive (taggedFamily P d)) (a : (environment candidate.real).Archive) :=
  observeLimit candidate 0 0 2 (candidate.threshold 0) ta a (.refl _) ⟨2, rfl⟩ (.refl _)
def fiveConstructorRuns (P : CircularPresentation) (d : Nat) :=
  let termArchive := (executeReal (termReal (taggedFamily P d) 0) 1).next
  (reflectedAt P d (reflectedLeaf P d) termArchive (executeReal (leafZero P d) 1).next,
   reflectedAt P d (reflectedCertified P d) termArchive (executeReal (certifiedZero P d) 1).next,
   reflectedAt P d (reflectedAdd P d) termArchive (executeReal (addZero P d) 1).next,
   reflectedAt P d (reflectedNeg P d) termArchive (executeReal (negZero P d) 1).next,
   reflectedAt P d (reflectedMul P d) termArchive (executeReal (mulZero P d) 1).next,
   reflectedAt P d (reflectedRecursive P d) termArchive (executeReal (recursiveZero P d) 1).next)


/-- The output certificate coordinates really read the two owned action codes;
the common scale is not padded to manufacture a history dependency. -/
def currentAlignmentLeft := executeAt (termReal (returnedFamily family) (family.modulus 0))
  (previousTerm family).next 2
def currentAlignmentRight := executeAt (termReal (returnedFamily family) (family.modulus 0))
  (currentAlignmentLeft family).next 3
def currentAlignment := (returnedFamily family).cauchy 0
  { term := family.modulus 0, precision := 2 } { term := family.modulus 0, precision := 3 }
  (.refl _) (.refl _) ⟨2, rfl⟩ ⟨3, rfl⟩
  (currentAlignmentLeft family).resource.execution (currentAlignmentRight family).resource.execution
theorem alignmentReadsLeft : (currentAlignment family).scale.leftExtra =
    (currentAlignment family).scale.common - (currentAlignmentLeft family).code.scale := rfl
theorem alignmentReadsRight : (currentAlignment family).scale.rightExtra =
    (currentAlignment family).scale.common - (currentAlignmentRight family).code.scale := rfl

end RelationalPerimeter.Tests.RelationalRealFamilyTransport

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Tests.RelationalRealFamilyTransport.previousTerm
#print axioms RelationalPerimeter.Tests.RelationalRealFamilyTransport.previousFirst
#print axioms RelationalPerimeter.Tests.RelationalRealFamilyTransport.previousSecond
#print axioms RelationalPerimeter.Tests.RelationalRealFamilyTransport.queryOne
#print axioms RelationalPerimeter.Tests.RelationalRealFamilyTransport.queryTwo
#print axioms RelationalPerimeter.Tests.RelationalRealFamilyTransport.head
#print axioms RelationalPerimeter.Tests.RelationalRealFamilyTransport.tail
#print axioms RelationalPerimeter.Tests.RelationalRealFamilyTransport.rich
#print axioms RelationalPerimeter.Tests.RelationalRealFamilyTransport.continuesThree
#print axioms RelationalPerimeter.Tests.RelationalRealFamilyTransport.termIndexChanges
#print axioms RelationalPerimeter.Tests.RelationalRealFamilyTransport.wholeTrace
#print axioms RelationalPerimeter.Tests.RelationalRealFamilyTransport.projectionShared
#print axioms RelationalPerimeter.Tests.RelationalRealFamilyTransport.roundtrip
#print axioms RelationalPerimeter.Tests.RelationalRealFamilyTransport.futureFromCurrent
#print axioms RelationalPerimeter.Tests.RelationalRealFamilyTransport.uniformThreshold
#print axioms RelationalPerimeter.Tests.RelationalRealFamilyTransport.restoredProducer
#print axioms RelationalPerimeter.Tests.RelationalRealFamilyTransport.restoredModulus
#print axioms RelationalPerimeter.Tests.RelationalRealFamilyTransport.termFuture
#print axioms RelationalPerimeter.Tests.RelationalRealFamilyTransport.observed
#print axioms RelationalPerimeter.Tests.RelationalRealFamilyTransport.observedCurrentTerm
#print axioms RelationalPerimeter.Tests.RelationalRealFamilyTransport.observedCurrentCandidate
#print axioms RelationalPerimeter.Tests.RelationalRealFamilyTransport.observedNearShared
#print axioms RelationalPerimeter.Tests.RelationalRealFamilyTransport.observedNearNotReconstructed
#print axioms RelationalPerimeter.Tests.RelationalRealFamilyTransport.globalLimit
#print axioms RelationalPerimeter.Tests.RelationalRealFamilyTransport.reflectedLimit
#print axioms RelationalPerimeter.Tests.RelationalRealFamilyTransport.reflectedUnique
#print axioms RelationalPerimeter.Tests.RelationalRealFamilyTransport.realizedNumericLimit
#print axioms RelationalPerimeter.Tests.RelationalRealFamilyTransport.realizedNumericUnique
#print axioms RelationalPerimeter.Tests.RelationalRealFamilyTransport.effectiveCodes
#print axioms RelationalPerimeter.Tests.RelationalRealFamilyTransport.effectiveBehaviour
#print axioms RelationalPerimeter.Tests.RelationalRealFamilyTransport.taggedFamily
#print axioms RelationalPerimeter.Tests.RelationalRealFamilyTransport.taggedTerm
#print axioms RelationalPerimeter.Tests.RelationalRealFamilyTransport.taggedOldLimit
#print axioms RelationalPerimeter.Tests.RelationalRealFamilyTransport.taggedNewLimit
#print axioms RelationalPerimeter.Tests.RelationalRealFamilyTransport.directData
#print axioms RelationalPerimeter.Tests.RelationalRealFamilyTransport.reconstructedData
#print axioms RelationalPerimeter.Tests.RelationalRealFamilyTransport.directScale
#print axioms RelationalPerimeter.Tests.RelationalRealFamilyTransport.reconstructedScale
#print axioms RelationalPerimeter.Tests.RelationalRealFamilyTransport.cauchyDataNotRecovered
#print axioms RelationalPerimeter.Tests.RelationalRealFamilyTransport.boundedCarrier
#print axioms RelationalPerimeter.Tests.RelationalRealFamilyTransport.boundedFamily
#print axioms RelationalPerimeter.Tests.RelationalRealFamilyTransport.boundedNotCofinal
#print axioms RelationalPerimeter.Tests.RelationalRealFamilyTransport.boundedLimit
#print axioms RelationalPerimeter.Tests.RelationalRealFamilyTransport.boundedRealization
#print axioms RelationalPerimeter.Tests.RelationalRealFamilyTransport.boundedUnique
#print axioms RelationalPerimeter.Tests.RelationalRealFamilyTransport.carrierReturn
#print axioms RelationalPerimeter.Tests.RelationalRealFamilyTransport.normalizedCodes
#print axioms RelationalPerimeter.Tests.RelationalRealFamilyTransport.carrierPreserved
#print axioms RelationalPerimeter.Tests.RelationalRealFamilyTransport.zeroNumeric
#print axioms RelationalPerimeter.Tests.RelationalRealFamilyTransport.leafZero
#print axioms RelationalPerimeter.Tests.RelationalRealFamilyTransport.certifiedZero
#print axioms RelationalPerimeter.Tests.RelationalRealFamilyTransport.addZero
#print axioms RelationalPerimeter.Tests.RelationalRealFamilyTransport.negZero
#print axioms RelationalPerimeter.Tests.RelationalRealFamilyTransport.mulZero
#print axioms RelationalPerimeter.Tests.RelationalRealFamilyTransport.recursiveZero
#print axioms RelationalPerimeter.Tests.RelationalRealFamilyTransport.reflectedLeaf
#print axioms RelationalPerimeter.Tests.RelationalRealFamilyTransport.reflectedCertified
#print axioms RelationalPerimeter.Tests.RelationalRealFamilyTransport.reflectedAdd
#print axioms RelationalPerimeter.Tests.RelationalRealFamilyTransport.reflectedNeg
#print axioms RelationalPerimeter.Tests.RelationalRealFamilyTransport.reflectedMul
#print axioms RelationalPerimeter.Tests.RelationalRealFamilyTransport.reflectedRecursive
#print axioms RelationalPerimeter.Tests.RelationalRealFamilyTransport.reflectedAt
#print axioms RelationalPerimeter.Tests.RelationalRealFamilyTransport.fiveConstructorRuns
#print axioms RelationalPerimeter.Tests.RelationalRealFamilyTransport.currentAlignmentLeft
#print axioms RelationalPerimeter.Tests.RelationalRealFamilyTransport.currentAlignmentRight
#print axioms RelationalPerimeter.Tests.RelationalRealFamilyTransport.currentAlignment
#print axioms RelationalPerimeter.Tests.RelationalRealFamilyTransport.alignmentReadsLeft
#print axioms RelationalPerimeter.Tests.RelationalRealFamilyTransport.alignmentReadsRight
/- AXIOM_AUDIT_END -/
