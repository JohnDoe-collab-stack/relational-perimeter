import RelationalPerimeter.Constitution.Reals.CarrierOrderedCompletion
import Tests.RelationalRealFamilyTransport

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace RelationalPerimeter.Tests.RelationalRealCarrierCompleteness
open StrongPerimetralTurning
open RelationalPerimeter.Constitution.Reals
open RuntimeCorrespondence HeterogeneousRealRuntime RelationalRealAddition RelationalRealFamilyTransport
open RelationalRealOrder
open RelationalPerimeter.Constitution.Reals.RelationalRealCarrierCompleteness RelationalRealNativeCauchy
open PresentedDyadicCompletion CarrierOrderedField

def decayCode (n : Nat) : SignedDyadicCode := ⟨1, 0, n⟩
def decayNearZero (p n : Nat) (beyond : PrecisionExtension p n) : Near p (decayCode n) SignedDyadicCode.zero where
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

/-- Test-only family with genuinely varying values, shifted inner modules,
and a nontrivial outer modulus. It is not another production master. -/
def decayTerm (n : Nat) : EffectiveCauchyReal.Carrier where
  approximation r := (decayCode n).raise r
  modulus p := p + 2
  modulusMonotone extension := extension.add (.refl 2)
  cauchy p r s hr hs := ((SameValue.raiseExact (decayCode n) r).symm.trans (SameValue.raiseExact (decayCode n) s)).toNear p
def decayFamily : CarrierFamily where
  terms := decayTerm
  modulus p := p + 1
  modulusMonotone := PrecisionExtension.succ
  cauchy p n m r s hn hm hr hs := Near.ofSameLeft (SameValue.raiseExact (decayCode n) r).symm
    (Near.ofSameRight (Near.compose (decayNearZero (p + 1) n hn) (decayNearZero (p + 1) m hm).symm)
      (SameValue.raiseExact (decayCode m) s))
theorem outerModule : decayFamily.modulus 2 = 3 := rfl
theorem innerModule : (decayFamily.terms 3).modulus 2 = 4 := rfl
def termsVary (same : (decayFamily.terms 0).approximation 0 = (decayFamily.terms 1).approximation 0) : Empty := by
  have scales := congrArg SignedDyadicCode.scale same
  change (0 : Nat) = 1 at scales
  cases scales

def firstZero : EffectiveCauchyReal.Carrier := dyadicCarrier SignedDyadicCode.zero
def secondZero : EffectiveCauchyReal.Carrier where
  approximation _ := ⟨1, 1, 0⟩
  modulus _ := 0
  modulusMonotone _ := .refl 0
  cauchy p _ _ _ _ := Near.refl p _
def secondZeroSame : SameValue SignedDyadicCode.zero (secondZero.approximation 0) :=
  ⟨⟨0, 0, 0, rfl, rfl⟩, rfl⟩
def firstZeroLimit : CarrierLimit decayFamily firstZero where
  threshold p := p
  converges p n r s hn hr hs := Near.ofSameLeft (SameValue.raiseExact (decayCode n) (r + 2)).symm
    (Near.ofSameRight (decayNearZero p n ((PrecisionExtension.next p).trans hn)) (SameValue.raiseExact SignedDyadicCode.zero s))
def secondZeroLimit : CarrierLimit decayFamily secondZero where
  threshold p := p
  converges p n r s hn hr hs := Near.ofSameLeft (SameValue.raiseExact (decayCode n) (r + 2)).symm
    (Near.ofSameRight (decayNearZero p n ((PrecisionExtension.next p).trans hn)) secondZeroSame)
def candidatesDistinct (same : firstZero = secondZero) : Empty := by
  have different := congrArg (fun x : EffectiveCauchyReal.Carrier => (x.approximation 0).positive) same
  change (0 : Nat) = 1 at different
  cases different
def candidateAgreement (P : CircularPresentation) (d : Nat) : EffectiveCauchyReal.Equivalent firstZero secondZero :=
  ((carrierCompletion P d decayFamily).uniqueness firstZero firstZeroLimit).symm.trans
    ((carrierCompletion P d decayFamily).uniqueness secondZero secondZeroLimit)
def completed (P : CircularPresentation) (d : Nat) := carrierCompletion P d decayFamily
theorem productionOrigin (P : CircularPresentation) (d : Nat) :
    (completed P d).limit = toCarrier (completed P d).native.limit := (completed P d).limitExact
def bothBridges (P : CircularPresentation) (d : Nat) : CarrierLimit decayFamily firstZero :=
  returnedCarrierLimitToOriginal (originalCarrierLimitToReturned (P := P) (baseDepth := d) firstZeroLimit)
def boundedCompletion (P : CircularPresentation) (d : Nat) := carrierCompletion P d RelationalRealFamilyTransport.boundedFamily

def previousTerm (P : CircularPresentation) (d : Nat) := executeReal (ofCarrier P d (decayFamily.terms 3)) 0
def currentTerm (P : CircularPresentation) (d : Nat) := executeAt (ofCarrier P d (decayFamily.terms 3)) (previousTerm P d).next 2
def previousLimit (P : CircularPresentation) (d : Nat) := executeReal (nativeLimit (carrierNativeFamily P d decayFamily)) 0
def currentLimit (P : CircularPresentation) (d : Nat) :=
  executeAt (nativeLimit (carrierNativeFamily P d decayFamily)) (previousLimit P d).next 2
def currentObservation (P : CircularPresentation) (d : Nat) :=
  (completed P d).native.convergence 2 3 2 2 (currentTerm P d) (currentLimit P d) (.refl _) (.refl _) (.refl _)
theorem currentDiagonalOwned (P : CircularPresentation) (d : Nat) :
    (currentObservation P d).diagonal = (currentLimit P d).resource.diagonal := (currentObservation P d).diagonalExact
theorem currentArchiveOwned (P : CircularPresentation) (d : Nat) :
    (currentObservation P d).diagonalArchive = (previousLimit P d).next.bank 3 := (currentObservation P d).archiveExact
theorem nextInstalled (P : CircularPresentation) (d : Nat) :
    (currentLimit P d).next.installed = some ⟨(previousLimit P d).next.bank,
      (previousLimit P d).next.journal, 2, (currentLimit P d).resource⟩ := rfl

def firstPerimeter : CircularPresentation := Example.examplePresentation
def secondPerimeter : CircularPresentation := { Example.examplePresentation with perimeterPositive := Example.exampleP2 }
def perimeterHead (p : CircularPresentation) : Bool :=
  match p.perimeter, p.perimeterPositive with
  | .advance _ _, .here => true
  | .advance _ _, .later _ => false
def perimeterDistinct (same : firstPerimeter = secondPerimeter) : Empty := by
  have positions := congrArg perimeterHead same
  change true = false at positions
  cases positions
def twoPerimeterCompletion := carrierCompletion_perimeterIndependent firstPerimeter secondPerimeter 1 4 decayFamily
def twoPerimeterInverse (x : EffectiveCauchyReal.Carrier) (w : CanonicalCarrierDomain x) :=
  carrierInverse_perimeterIndependent firstPerimeter secondPerimeter 1 4 x w
theorem twoPerimeterDensity {x y : EffectiveCauchyReal.Carrier} (origin : CarrierOrder x y) :
    (produceCarrierDensity firstPerimeter 1 origin).code = (produceCarrierDensity secondPerimeter 4 origin).code :=
  carrierDensityReadout_perimeterIndependent firstPerimeter secondPerimeter 1 4 origin
theorem twoPerimeterBounds (x : EffectiveCauchyReal.Carrier) :
    (produceCarrierNaturalBounds firstPerimeter 1 x).lower = (produceCarrierNaturalBounds secondPerimeter 4 x).lower ∧
    (produceCarrierNaturalBounds firstPerimeter 1 x).upper = (produceCarrierNaturalBounds secondPerimeter 4 x).upper :=
  carrierNaturalBoundsReadout_perimeterIndependent firstPerimeter secondPerimeter 1 4 x

end RelationalPerimeter.Tests.RelationalRealCarrierCompleteness

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Tests.RelationalRealCarrierCompleteness.decayCode
#print axioms RelationalPerimeter.Tests.RelationalRealCarrierCompleteness.decayNearZero
#print axioms RelationalPerimeter.Tests.RelationalRealCarrierCompleteness.decayTerm
#print axioms RelationalPerimeter.Tests.RelationalRealCarrierCompleteness.decayFamily
#print axioms RelationalPerimeter.Tests.RelationalRealCarrierCompleteness.outerModule
#print axioms RelationalPerimeter.Tests.RelationalRealCarrierCompleteness.innerModule
#print axioms RelationalPerimeter.Tests.RelationalRealCarrierCompleteness.termsVary
#print axioms RelationalPerimeter.Tests.RelationalRealCarrierCompleteness.firstZero
#print axioms RelationalPerimeter.Tests.RelationalRealCarrierCompleteness.secondZero
#print axioms RelationalPerimeter.Tests.RelationalRealCarrierCompleteness.secondZeroSame
#print axioms RelationalPerimeter.Tests.RelationalRealCarrierCompleteness.firstZeroLimit
#print axioms RelationalPerimeter.Tests.RelationalRealCarrierCompleteness.secondZeroLimit
#print axioms RelationalPerimeter.Tests.RelationalRealCarrierCompleteness.candidatesDistinct
#print axioms RelationalPerimeter.Tests.RelationalRealCarrierCompleteness.candidateAgreement
#print axioms RelationalPerimeter.Tests.RelationalRealCarrierCompleteness.completed
#print axioms RelationalPerimeter.Tests.RelationalRealCarrierCompleteness.productionOrigin
#print axioms RelationalPerimeter.Tests.RelationalRealCarrierCompleteness.bothBridges
#print axioms RelationalPerimeter.Tests.RelationalRealCarrierCompleteness.boundedCompletion
#print axioms RelationalPerimeter.Tests.RelationalRealCarrierCompleteness.previousTerm
#print axioms RelationalPerimeter.Tests.RelationalRealCarrierCompleteness.currentTerm
#print axioms RelationalPerimeter.Tests.RelationalRealCarrierCompleteness.previousLimit
#print axioms RelationalPerimeter.Tests.RelationalRealCarrierCompleteness.currentLimit
#print axioms RelationalPerimeter.Tests.RelationalRealCarrierCompleteness.currentObservation
#print axioms RelationalPerimeter.Tests.RelationalRealCarrierCompleteness.currentDiagonalOwned
#print axioms RelationalPerimeter.Tests.RelationalRealCarrierCompleteness.currentArchiveOwned
#print axioms RelationalPerimeter.Tests.RelationalRealCarrierCompleteness.nextInstalled
#print axioms RelationalPerimeter.Tests.RelationalRealCarrierCompleteness.firstPerimeter
#print axioms RelationalPerimeter.Tests.RelationalRealCarrierCompleteness.secondPerimeter
#print axioms RelationalPerimeter.Tests.RelationalRealCarrierCompleteness.perimeterHead
#print axioms RelationalPerimeter.Tests.RelationalRealCarrierCompleteness.perimeterDistinct
#print axioms RelationalPerimeter.Tests.RelationalRealCarrierCompleteness.twoPerimeterCompletion
#print axioms RelationalPerimeter.Tests.RelationalRealCarrierCompleteness.twoPerimeterInverse
#print axioms RelationalPerimeter.Tests.RelationalRealCarrierCompleteness.twoPerimeterDensity
#print axioms RelationalPerimeter.Tests.RelationalRealCarrierCompleteness.twoPerimeterBounds
/- AXIOM_AUDIT_END -/
