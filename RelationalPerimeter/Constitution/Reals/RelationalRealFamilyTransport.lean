import RelationalPerimeter.Constitution.Reals.RelationalRealLimitUniqueness

set_option autoImplicit false
set_option linter.unusedVariables false

/-!
# Effective family transport downstream of executed reals

The received producer and the authoritative grouping remain primitive.
Round trips below are numerical, not identities of families, Cauchy data,
archives or occurrences. A numerical Cauchy callback may form canonical
executions; this is different from consuming arbitrary current executions.
-/
namespace RelationalPerimeter.Constitution.Reals.RelationalRealFamilyTransport
open StrongPerimetralTurning ProducedCompleteness RuntimeCorrespondence
open HeterogeneousRealRuntime RelationalRealAddition RelationalRealCauchy
open RelationalRealLimitUniqueness

variable {P : CircularPresentation} {baseDepth : Nat}

/-- Executable coherent terms and a uniform positive Cauchy law. No limit is input. -/
structure EffectiveFamily where
  terms : Nat → EffectiveDyadicPresentation
  modulus : Nat → Nat
  modulusMonotone : {p q : Nat} → PrecisionExtension p q →
    PrecisionExtension (modulus p) (modulus q)
  cauchy : (p n m r s : Nat) →
    PrecisionExtension (modulus p) n → PrecisionExtension (modulus p) m →
    PrecisionExtension p r → PrecisionExtension p s →
    Near p ((terms n).approximation r) ((terms m).approximation s)

/-- Uniform term behaviour only: this is not an identity of rich family data. -/
structure TermwiseUniformEquivalent (first second : EffectiveFamily) where
  threshold : Nat → Nat
  near : (p n r s : Nat) →
    PrecisionExtension (threshold p) r → PrecisionExtension (threshold p) s →
    Near p ((first.terms n).approximation r) ((second.terms n).approximation s)

/-- The numerical view uses canonical term executions, not arbitrary current histories. -/
def readoutFamily (family : ExecutedCauchyFamily P baseDepth) : EffectiveFamily where
  terms n := toPresentation (termReal family n)
  modulus := family.modulus
  modulusMonotone := family.modulusMonotone
  cauchy p n m r s hn hm hr hs :=
    termsCauchy family p n m r s
      (executeReal (termReal family n) r) (executeReal (termReal family m) s) hn hm hr hs

/-- Subtraction cancellation with a constructive proof, independent of library simplification. -/
theorem subtractOwnedScale (a b : Nat) : (a + b) - a = b := by
  induction a with
  | zero => rw [Nat.zero_add]; rfl
  | succ a ih =>
    rw [Nat.succ_add, Nat.succ_sub_succ_eq_sub]
    exact ih
def alignOwnedNear {p : Nat} {left right : SignedDyadicCode}
    (ownedLeft ownedRight : SignedDyadicCode) (leftExact : left = ownedLeft) (rightExact : right = ownedRight)
    (near : Near p left right) : Near p ownedLeft ownedRight := by
  let transported := LimitGrouping.transportNear leftExact rightExact near
  let common := transported.scale.common
  have le : common - ownedLeft.scale = transported.scale.leftExtra := by
    rw [show common = ownedLeft.scale + transported.scale.leftExtra from transported.scale.leftExact.symm]
    exact subtractOwnedScale _ _
  have re : common - ownedRight.scale = transported.scale.rightExtra := by
    rw [show common = ownedRight.scale + transported.scale.rightExtra from transported.scale.rightExact.symm]
    exact subtractOwnedScale _ _
  exact {
    scale := {
      common := common
      leftExtra := common - ownedLeft.scale
      rightExtra := common - ownedRight.scale
      leftExact := by rw [le]; exact transported.scale.leftExact
      rightExact := by rw [re]; exact transported.scale.rightExact }
    precisionExtra := transported.precisionExtra
    precisionExact := transported.precisionExact
    leftBound := by
      change liftedPositive ownedLeft (common - ownedLeft.scale) +
          liftedNegative ownedRight (common - ownedRight.scale) ≤
        liftedPositive ownedRight (common - ownedRight.scale) +
          liftedNegative ownedLeft (common - ownedLeft.scale) + powerOfTwo transported.precisionExtra
      rw [le, re]
      exact transported.leftBound
    rightBound := by
      change liftedPositive ownedRight (common - ownedRight.scale) +
          liftedNegative ownedLeft (common - ownedLeft.scale) ≤
        liftedPositive ownedLeft (common - ownedLeft.scale) +
          liftedNegative ownedRight (common - ownedRight.scale) + powerOfTwo transported.precisionExtra
      rw [le, re]
      exact transported.rightBound }

theorem ownedLeftExtra {p : Nat} {left right : SignedDyadicCode}
    (ownedLeft ownedRight : SignedDyadicCode) (le : left = ownedLeft) (re : right = ownedRight)
    (near : Near p left right) :
    (alignOwnedNear ownedLeft ownedRight le re near).scale.leftExtra =
      (LimitGrouping.transportNear le re near).scale.leftExtra := by
  change (LimitGrouping.transportNear le re near).scale.common - ownedLeft.scale = _
  rw [← (LimitGrouping.transportNear le re near).scale.leftExact]
  exact subtractOwnedScale _ _

theorem ownedRightExtra {p : Nat} {left right : SignedDyadicCode}
    (ownedLeft ownedRight : SignedDyadicCode) (le : left = ownedLeft) (re : right = ownedRight)
    (near : Near p left right) :
    (alignOwnedNear ownedLeft ownedRight le re near).scale.rightExtra =
      (LimitGrouping.transportNear le re near).scale.rightExtra := by
  change (LimitGrouping.transportNear le re near).scale.common - ownedRight.scale = _
  rw [← (LimitGrouping.transportNear le re near).scale.rightExact]
  exact subtractOwnedScale _ _

theorem commonScaleExtensionality {left right : SignedDyadicCode} (first second : CommonScale left right)
    (sameCommon : first.common = second.common) (sameLeft : first.leftExtra = second.leftExtra)
    (sameRight : first.rightExtra = second.rightExtra) : first = second := by
  cases first; cases second; cases sameCommon; cases sameLeft; cases sameRight; rfl

theorem nearCoordinateExtensionality {p : Nat} {left right : SignedDyadicCode} (first second : Near p left right)
    (sameScale : first.scale = second.scale) (samePrecision : first.precisionExtra = second.precisionExtra) :
    first = second := by
  cases first; cases second; cases sameScale; cases samePrecision; rfl

/-- No padding or new numerical witness: the exact same common scale, lifts,
precision slack and directed bounds are retained at the owned endpoint codes. -/
theorem alignOwnedNear_exact {p : Nat} {left right : SignedDyadicCode}
    (ownedLeft ownedRight : SignedDyadicCode) (le : left = ownedLeft) (re : right = ownedRight)
    (near : Near p left right) :
    alignOwnedNear ownedLeft ownedRight le re near = LimitGrouping.transportNear le re near :=
  nearCoordinateExtensionality _ _
    (commonScaleExtensionality _ _ rfl (ownedLeftExtra _ _ _ _ _) (ownedRightExtra _ _ _ _ _)) rfl

/-- Realization executes the requested term/precision. Its law projects the two
owned actions before using the received numerical law; it does not recover an
earlier rich Cauchy witness. -/
def realizeFamily (P : CircularPresentation) (baseDepth : Nat)
    (numeric : EffectiveFamily) : ExecutedCauchyFamily P baseDepth where
  producer := ⟨fun request => (numeric.terms request.term).approximation request.precision⟩
  termCoherent n p r s hr hs := (numeric.terms n).coherent p r s hr hs
  modulus := numeric.modulus
  modulusMonotone := numeric.modulusMonotone
  cauchy := by
    intro p fj sj fr sr fn sn fp sp first second
    let firstCode := first.readout
    let secondCode := second.readout
    have firstExact : first.readout = (numeric.terms fr.term).approximation fr.precision := by
      rw [first.readout_is_storedAction, sourceProgram_actionCode_exact]
    have secondExact : second.readout = (numeric.terms sr.term).approximation sr.precision := by
      rw [second.readout_is_storedAction, sourceProgram_actionCode_exact]
    let near := numeric.cauchy p fr.term sr.term fr.precision sr.precision fn sn fp sp
    exact alignOwnedNear firstCode secondCode firstExact.symm secondExact.symm near

theorem realizedProducerAt (numeric : EffectiveFamily) (request : SourceRequest) :
    (realizeFamily P baseDepth numeric).producer.calculate request =
      (numeric.terms request.term).approximation request.precision := rfl

theorem realizedModulus (numeric : EffectiveFamily) :
    (realizeFamily P baseDepth numeric).modulus = numeric.modulus := rfl

/-- Exact code of this current raw execution, without another source production. -/
theorem realizedTermAt (numeric : EffectiveFamily) (n p : Nat)
    {archive : (environment (termReal (realizeFamily P baseDepth numeric) n)).Archive}
    (step : Step (environment (termReal (realizeFamily P baseDepth numeric) n)) archive p) :
    step.code = (numeric.terms n).approximation p := step.resource.readoutExact

theorem effectiveReturnAt (numeric : EffectiveFamily) (n p : Nat) :
    ((readoutFamily (realizeFamily P baseDepth numeric)).terms n).approximation p =
      (numeric.terms n).approximation p := rfl

def effectiveRoundtrip (numeric : EffectiveFamily) :
    TermwiseUniformEquivalent (readoutFamily (realizeFamily P baseDepth numeric)) numeric where
  threshold := fun p => p
  near p n r s hr hs := (numeric.terms n).coherent p r s hr hs

def realizedTermEquivalent (numeric : EffectiveFamily) (n : Nat) :
    Equivalent (termReal (realizeFamily P baseDepth numeric) n)
      (ofPresentation P baseDepth (numeric.terms n)) :=
  Equivalent.ofExact (fun p => by rw [ofPresentation_readout]; exact SameValue.refl _)

def realizedTermFutures (numeric : EffectiveFamily) (n : Nat) :
    NumericalFutureEquivalent (termReal (realizeFamily P baseDepth numeric) n)
      (ofPresentation P baseDepth (numeric.terms n)) :=
  (realizedTermEquivalent numeric n).toFutures

abbrev returnedFamily (family : ExecutedCauchyFamily P baseDepth) :=
  realizeFamily P baseDepth (readoutFamily family)

theorem returnedProducer (family : ExecutedCauchyFamily P baseDepth) :
    (returnedFamily family).producer = family.producer := rfl

theorem returnedModulus (family : ExecutedCauchyFamily P baseDepth) :
    (returnedFamily family).modulus = family.modulus := rfl

theorem relationalReturnAt (family : ExecutedCauchyFamily P baseDepth) (request : SourceRequest) :
    (returnedFamily family).producer.calculate request = family.producer.calculate request := rfl

def relationalTermRoundtrip (family : ExecutedCauchyFamily P baseDepth) (n : Nat) :
    Equivalent (termReal (returnedFamily family) n) (termReal family n) :=
  Equivalent.ofExact (fun _ => SameValue.refl _)

def relationalTermFutures (family : ExecutedCauchyFamily P baseDepth) (n : Nat) :
    NumericalFutureEquivalent (termReal (returnedFamily family) n) (termReal family n) :=
  (relationalTermRoundtrip family n).toFutures

def relationalRoundtrip (family : ExecutedCauchyFamily P baseDepth) :
    TermwiseUniformEquivalent (readoutFamily (returnedFamily family)) (readoutFamily family) where
  threshold := fun p => p
  near p n r s hr hs := (readoutFamily family).terms n |>.coherent p r s hr hs


/-- The positive numerical domain is exactly the existing candidate domain. -/
structure PresentationLimit (family : EffectiveFamily) (value : EffectiveDyadicPresentation) where
  threshold : Nat → Nat
  converges : (p n r s : Nat) →
    PrecisionExtension (family.modulus p) n → PrecisionExtension p r →
    PrecisionExtension (threshold p) s →
    Near p ((family.terms n).approximation r) (value.approximation s)

variable {family : ExecutedCauchyFamily P baseDepth}

/-- Endpoint transport of the received witness. currentReadout is a Prop
raccord; its canonical formations are not extra current Steps. -/
def projectLimitNear (candidate : LimitCandidate family) (p n r s : Nat)
    {ta : TermArchive family} {a : (environment candidate.real).Archive}
    (termStep : Step (environment (termReal family n)) ta r)
    (candidateStep : Step (environment candidate.real) a s)
    (near : Near p termStep.code candidateStep.code) :
    Near p (((readoutFamily family).terms n).approximation r)
      ((toPresentation candidate.real).approximation s) :=
  LimitGrouping.transportNear (currentReadout _ _ _ termStep) (currentReadout _ _ _ candidateStep) near

theorem projectLimitNear_heq (candidate : LimitCandidate family) (p n r s : Nat)
    {ta : TermArchive family} {a : (environment candidate.real).Archive}
    (termStep : Step (environment (termReal family n)) ta r)
    (candidateStep : Step (environment candidate.real) a s)
    (near : Near p termStep.code candidateStep.code) :
    HEq (projectLimitNear candidate p n r s termStep candidateStep near) near :=
  LimitGrouping.transportNear_heq _ _ near

def preserveLimitAt (candidate : LimitCandidate family) (p n r s : Nat)
    {ta : TermArchive family} {a : (environment candidate.real).Archive}
    (termStep : Step (environment (termReal family n)) ta r)
    (candidateStep : Step (environment candidate.real) a s)
    (indexBeyond : PrecisionExtension (family.modulus p) n)
    (termBeyond : PrecisionExtension p r)
    (candidateBeyond : PrecisionExtension (candidate.threshold p) s) :
    Near p (((readoutFamily family).terms n).approximation r)
      ((toPresentation candidate.real).approximation s) :=
  let near := candidate.converges p n r s termStep candidateStep indexBeyond termBeyond candidateBeyond
  projectLimitNear candidate p n r s termStep candidateStep near

/-- A global numerical observation first owns two newly executed current Steps.
Its numerical field is projected from the one received convergence result. -/
structure LimitObservation (candidate : LimitCandidate family) (p n r s : Nat)
    (ta : TermArchive family) (a : (environment candidate.real).Archive)
    (indexBeyond : PrecisionExtension (family.modulus p) n)
    (termBeyond : PrecisionExtension p r)
    (candidateBeyond : PrecisionExtension (candidate.threshold p) s) where
  private mk ::
  archives : TermArchive family × (environment candidate.real).Archive
  archivesExact : archives = ⟨ta, a⟩
  termStep : Step (environment (termReal family n)) ta r
  candidateStep : Step (environment candidate.real) a s
  termExact : termStep = executeAt (termReal family n) ta r
  candidateExact : candidateStep = executeAt candidate.real a s
  near : Near p termStep.code candidateStep.code
  nearExact : near = candidate.converges p n r s termStep candidateStep indexBeyond termBeyond candidateBeyond
  numerical : Near p (((readoutFamily family).terms n).approximation r)
    ((toPresentation candidate.real).approximation s)
  numericalExact : numerical = projectLimitNear candidate p n r s termStep candidateStep near

def observeLimit (candidate : LimitCandidate family) (p n r s : Nat)
    (ta : TermArchive family) (a : (environment candidate.real).Archive)
    (indexBeyond : PrecisionExtension (family.modulus p) n)
    (termBeyond : PrecisionExtension p r)
    (candidateBeyond : PrecisionExtension (candidate.threshold p) s) :
    LimitObservation candidate p n r s ta a indexBeyond termBeyond candidateBeyond :=
  let termStep := executeAt (termReal family n) ta r
  let candidateStep := executeAt candidate.real a s
  let near := candidate.converges p n r s termStep candidateStep indexBeyond termBeyond candidateBeyond
  let numerical := projectLimitNear candidate p n r s termStep candidateStep near
  ⟨⟨ta, a⟩, rfl, termStep, candidateStep, rfl, rfl, near, rfl, numerical, rfl⟩

/-- Convenience projection: fresh Steps at declared initial archives, not a
claim that arbitrary earlier rich occurrences were recovered. -/
def preserveLimit (candidate : LimitCandidate family) :
    PresentationLimit (readoutFamily family) (toPresentation candidate.real) where
  threshold := candidate.threshold
  converges p n r s hn hr hs :=
    let observed := observeLimit candidate p n r s (termEnvironment family 0).initialArchive
      (environment candidate.real).initialArchive hn hr hs
    observed.numerical

def reflectLimit (real : Real P baseDepth)
    (numeric : PresentationLimit (readoutFamily family) (toPresentation real)) :
    LimitCandidate family where
  real := real
  threshold := numeric.threshold
  converges := by
    intro p n r s ta a termStep candidateStep indexBeyond termBeyond candidateBeyond
    have near := numeric.converges p n r s indexBeyond termBeyond candidateBeyond
    change Near p (readout (termReal family n) r) (readout real s) at near
    rw [← currentReadout _ _ _ termStep, ← currentReadout _ _ _ candidateStep] at near
    exact near

/-- A received numerical limit is only a candidate. The authoritative limit
is still produced by grouping in limitReal (realizeFamily ...). -/
def realizeLimit (numeric : EffectiveFamily) (value : EffectiveDyadicPresentation)
    (convergence : PresentationLimit numeric value) :
    LimitCandidate (realizeFamily P baseDepth numeric) where
  real := ofPresentation P baseDepth value
  threshold := convergence.threshold
  converges := by
    intro p n r s ta a termStep candidateStep indexBeyond termBeyond candidateBeyond
    have near := convergence.converges p n r s indexBeyond termBeyond candidateBeyond
    have termExact := realizedTermAt numeric n r termStep
    have candidateExact : candidateStep.code = value.approximation s := by
      rw [currentReadout _ _ _ candidateStep, ofPresentation_readout]
    rw [← termExact, ← candidateExact] at near
    exact near

/-- Route A: old authoritative real, current returned term, old current limit.
Both source executions are passed directly to the OLD family Cauchy law. -/
def returnedCandidate (original : ExecutedCauchyFamily P baseDepth) :
    LimitCandidate (returnedFamily original) where
  real := limitReal original
  threshold := fun p => p
  converges := by
    intro p n r s ta a termStep limitStep indexBeyond termBeyond limitBeyond
    let production := limitStep.resource.response.limitProduction
    rw [limitStepReadout limitStep]
    change Near p termStep.code production.readout
    rw [production.readout_is_source]
    exact original.cauchy p { term := n, precision := r } production.sourceAt.request
      indexBeyond
      (by rw [production.sourceAtExact]; exact original.modulusMonotone limitBeyond)
      termBeyond (by rw [production.sourceAtExact]; exact limitBeyond)
      termStep.resource.execution production.source.execution

/-- The OTHER convergence goes through the RECONSTRUCTED Cauchy law. -/
def returnedAuthoritative (original : ExecutedCauchyFamily P baseDepth) :
    LimitCandidate (returnedFamily original) := authoritative (returnedFamily original)

def relationalLimitRoundtrip (original : ExecutedCauchyFamily P baseDepth) :
    Equivalent (limitReal (returnedFamily original)) (limitReal original) ×
      NumericalFutureEquivalent (limitReal (returnedFamily original)) (limitReal original) :=
  authoritativeUnique (returnedCandidate original)

def realizedLimitEquivalence (numeric : EffectiveFamily) (value : EffectiveDyadicPresentation)
    (convergence : PresentationLimit numeric value) :
    Equivalent (limitReal (realizeFamily P baseDepth numeric)) (ofPresentation P baseDepth value) ×
      NumericalFutureEquivalent (limitReal (realizeFamily P baseDepth numeric)) (ofPresentation P baseDepth value) :=
  authoritativeUnique (realizeLimit numeric value convergence)

/-- Raw carrier replies have their OWN term moduli; none must be cofinal. -/
structure CarrierFamily where
  terms : Nat → EffectiveCauchyReal.Carrier
  modulus : Nat → Nat
  modulusMonotone : {p q : Nat} → PrecisionExtension p q →
    PrecisionExtension (modulus p) (modulus q)
  cauchy : (p n m r s : Nat) →
    PrecisionExtension (modulus p) n → PrecisionExtension (modulus p) m →
    PrecisionExtension ((terms n).modulus p) r → PrecisionExtension ((terms m).modulus p) s →
    Near p ((terms n).approximation r) ((terms m).approximation s)

def normalizeCarrierFamily (numeric : CarrierFamily) : EffectiveFamily where
  terms n := EffectiveCauchyReal.toPresentation (numeric.terms n)
  modulus := numeric.modulus
  modulusMonotone := numeric.modulusMonotone
  cauchy p n m r s hn hm hr hs :=
    numeric.cauchy p n m ((numeric.terms n).modulus r) ((numeric.terms m).modulus s) hn hm
      ((numeric.terms n).modulusMonotone hr) ((numeric.terms m).modulusMonotone hs)

def carrierFamily (numeric : EffectiveFamily) : CarrierFamily where
  terms n := EffectiveCauchyReal.ofPresentation (numeric.terms n)
  modulus := numeric.modulus
  modulusMonotone := numeric.modulusMonotone
  cauchy := numeric.cauchy

theorem normalizedReturnAt (numeric : EffectiveFamily) (n p : Nat) :
    ((normalizeCarrierFamily (carrierFamily numeric)).terms n).approximation p =
      (numeric.terms n).approximation p := rfl

def carrierTermRoundtrip (numeric : CarrierFamily) (n : Nat) :
    EffectiveCauchyReal.Equivalent ((carrierFamily (normalizeCarrierFamily numeric)).terms n) (numeric.terms n) :=
  EffectiveCauchyReal.carrier_roundtrip_equivalent (numeric.terms n)

def readoutCarrierFamily (family : ExecutedCauchyFamily P baseDepth) : CarrierFamily :=
  carrierFamily (readoutFamily family)

def realizeCarrierFamily (P : CircularPresentation) (baseDepth : Nat) (numeric : CarrierFamily) :
    ExecutedCauchyFamily P baseDepth := realizeFamily P baseDepth (normalizeCarrierFamily numeric)

/-- Limits of carriers here concern their normalized presentations. This does
not invert a term modulus or assert a cofinal raw-index round trip. -/
def CarrierLimit (family : CarrierFamily) (value : EffectiveCauchyReal.Carrier) : Type :=
  PresentationLimit (normalizeCarrierFamily family) (EffectiveCauchyReal.toPresentation value)

def realizeCarrierLimit (numeric : CarrierFamily) (value : EffectiveCauchyReal.Carrier)
    (convergence : CarrierLimit numeric value) :
    LimitCandidate (realizeCarrierFamily P baseDepth numeric) :=
  realizeLimit (normalizeCarrierFamily numeric) (EffectiveCauchyReal.toPresentation value) convergence

def preserveCarrierLimit (candidate : LimitCandidate family) :
    CarrierLimit (readoutCarrierFamily family) (toCarrier candidate.real) :=
  preserveLimit candidate

end RelationalPerimeter.Constitution.Reals.RelationalRealFamilyTransport

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealFamilyTransport.EffectiveFamily
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealFamilyTransport.TermwiseUniformEquivalent
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealFamilyTransport.readoutFamily
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealFamilyTransport.realizeFamily
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealFamilyTransport.realizedProducerAt
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealFamilyTransport.realizedModulus
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealFamilyTransport.realizedTermAt
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealFamilyTransport.effectiveReturnAt
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealFamilyTransport.effectiveRoundtrip
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealFamilyTransport.realizedTermEquivalent
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealFamilyTransport.realizedTermFutures
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealFamilyTransport.returnedFamily
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealFamilyTransport.returnedProducer
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealFamilyTransport.returnedModulus
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealFamilyTransport.relationalReturnAt
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealFamilyTransport.relationalTermRoundtrip
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealFamilyTransport.relationalTermFutures
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealFamilyTransport.relationalRoundtrip
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealFamilyTransport.PresentationLimit
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealFamilyTransport.projectLimitNear
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealFamilyTransport.projectLimitNear_heq
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealFamilyTransport.preserveLimitAt
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealFamilyTransport.LimitObservation
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealFamilyTransport.observeLimit
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealFamilyTransport.preserveLimit
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealFamilyTransport.reflectLimit
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealFamilyTransport.realizeLimit
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealFamilyTransport.returnedCandidate
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealFamilyTransport.returnedAuthoritative
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealFamilyTransport.relationalLimitRoundtrip
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealFamilyTransport.realizedLimitEquivalence
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealFamilyTransport.CarrierFamily
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealFamilyTransport.normalizeCarrierFamily
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealFamilyTransport.carrierFamily
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealFamilyTransport.normalizedReturnAt
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealFamilyTransport.carrierTermRoundtrip
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealFamilyTransport.readoutCarrierFamily
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealFamilyTransport.realizeCarrierFamily
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealFamilyTransport.CarrierLimit
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealFamilyTransport.realizeCarrierLimit
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealFamilyTransport.preserveCarrierLimit
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealFamilyTransport.subtractOwnedScale
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealFamilyTransport.alignOwnedNear
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealFamilyTransport.ownedLeftExtra
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealFamilyTransport.ownedRightExtra
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealFamilyTransport.commonScaleExtensionality
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealFamilyTransport.nearCoordinateExtensionality
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealFamilyTransport.alignOwnedNear_exact
/- AXIOM_AUDIT_END -/
