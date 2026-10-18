import RelationalPerimeter.Constitution.Reals.CarrierOrderedFieldLaws

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace RelationalPerimeter.Constitution.Reals.CarrierOrderedField
open StrongPerimetralTurning RuntimeCorrespondence HeterogeneousRealRuntime ConstitutiveRuntime
open RelationalRealAddition RelationalRealOrder RelationalRealDensity DyadicDensity
open PresentedDyadicCompletion RelationalRealCarrierCompleteness

variable {P : CircularPresentation} {baseDepth : Nat}

/-- A numerical readout of finite classification, never another producer. -/
def inspectedDensityCode (p : Nat) (a b : SignedDyadicCode) : SignedDyadicCode :=
  match classifyFinite p a b with
  | .forward gap => midpointCode gap
  | .backward _ => SignedDyadicCode.zero
  | .inconclusive _ _ => SignedDyadicCode.zero

theorem forwardMidpointCode {a b : Real P baseDepth}
    {aa : (environment a).Archive} {ba : (environment b).Archive} {p r : Nat}
    (attempt : ComparisonAttempt (environment a) (environment b) aa ba p r)
    (expected : StrictSeparation p attempt.pair.left.code attempt.pair.right.code) :
    midpointCode (attempt.forward expected).separation =
      inspectedDensityCode p (attempt.forward expected).pair.left.code (attempt.forward expected).pair.right.code := by
  cases h : attempt.direction with
  | forward gap =>
      unfold ComparisonAttempt.forward
      rw [h]
      unfold inspectedDensityCode
      rw [← attempt.classified, h]
  | backward gap => exact (expected.refuteUpper (gap.forwardUpper p)).elim
  | inconclusive upper reverse => exact (expected.refuteUpper upper).elim

theorem forwardResponse {a b : Real P baseDepth}
    {aa : (environment a).Archive} {ba : (environment b).Archive} {p r : Nat}
    (attempt : ComparisonAttempt (environment a) (environment b) aa ba p r)
    (expected : StrictSeparation p attempt.pair.left.code attempt.pair.right.code) :
    (attempt.forward expected).response = r := by
  cases h : attempt.direction with
  | forward gap => unfold ComparisonAttempt.forward; rw [h]
  | backward gap => exact (expected.refuteUpper (gap.forwardUpper p)).elim
  | inconclusive upper reverse => exact (expected.refuteUpper upper).elim

structure CarrierDensityResult (P : CircularPresentation) (baseDepth : Nat)
    (x y : EffectiveCauchyReal.Carrier) (origin : CarrierOrder x y) where
  realizedOrigin : StrictOrder (ofCarrier P baseDepth x) (ofCarrier P baseDepth y)
  realizedOriginExact : realizedOrigin = realizeCarrierOrder x y origin
    (environment (ofCarrier P baseDepth x)).initialArchive (environment (ofCarrier P baseDepth y)).initialArchive
  responseExact : realizedOrigin.response = origin.response
  selectionExact : midpointCode realizedOrigin.separation =
    inspectedDensityCode origin.accuracy realizedOrigin.pair.left.code realizedOrigin.pair.right.code
  packet : Density realizedOrigin (Journal.root P baseDepth)
  code : SignedDyadicCode
  codeExact : code = packet.action.readout
  target : EffectiveCauchyReal.Carrier
  targetExact : target = toCarrier packet.target
  targetDyadic : EffectiveCauchyReal.Equivalent target (dyadicCarrier code)
  left : CarrierOrder x (dyadicCarrier code)
  right : CarrierOrder (dyadicCarrier code) y

def produceCarrierDensity (P : CircularPresentation) (baseDepth : Nat)
    {x y : EffectiveCauchyReal.Carrier} (origin : CarrierOrder x y) :
    CarrierDensityResult P baseDepth x y origin := by
  let realizedOrigin := realizeCarrierOrder x y origin
    (environment (ofCarrier P baseDepth x)).initialArchive (environment (ofCarrier P baseDepth y)).initialArchive
  have responseExact : realizedOrigin.response = origin.response := by
    unfold realizedOrigin realizeCarrierOrder realizePresentationOrder
    exact forwardResponse _ _
  have selectionExact : midpointCode realizedOrigin.separation =
      inspectedDensityCode origin.accuracy realizedOrigin.pair.left.code realizedOrigin.pair.right.code := by
    unfold realizedOrigin realizeCarrierOrder realizePresentationOrder
    exact forwardMidpointCode _ _
  let packet := produceDensity realizedOrigin (Journal.root P baseDepth)
  let code := packet.action.readout
  let target := toCarrier packet.target
  have targetDyadic : EffectiveCauchyReal.Equivalent target (dyadicCarrier code) := by
    change EffectiveCauchyReal.Equivalent (toCarrier packet.target) _
    rw [packet.targetExact]
    exact carrierReadoutConstant P baseDepth code
  let orders := packet.orders
  exact ⟨realizedOrigin, rfl, responseExact, selectionExact, packet, code, rfl, target, rfl, targetDyadic,
    transportCarrierOrder orders.1.toCarrier (carrier_roundtrip x) targetDyadic,
    transportCarrierOrder orders.2.toCarrier targetDyadic (carrier_roundtrip y)⟩

structure CarrierNaturalBoundResult (P : CircularPresentation) (baseDepth : Nat) (x : EffectiveCauchyReal.Carrier) where
  realized : Real P baseDepth
  realizedExact : realized = ofCarrier P baseDepth x
  packet : NaturalBound realized (environment realized).initialArchive (Journal.root P baseDepth)
  lower : Nat
  upper : Nat
  lowerExact : lower = packet.action.stored.value.lower
  upperExact : upper = packet.action.stored.value.upper
  lowerOrder : CarrierOrder (dyadicCarrier (negativeNaturalCode lower)) x
  upperOrder : CarrierOrder x (dyadicCarrier (naturalCode upper))

def produceCarrierNaturalBounds (P : CircularPresentation) (baseDepth : Nat) (x : EffectiveCauchyReal.Carrier) :
    CarrierNaturalBoundResult P baseDepth x := by
  let realized := ofCarrier P baseDepth x
  let packet := produceNaturalBound realized (environment realized).initialArchive (Journal.root P baseDepth)
  let lower := packet.action.stored.value.lower
  let upper := packet.action.stored.value.upper
  have lowerDyadic : EffectiveCauchyReal.Equivalent (toCarrier packet.lowerTarget)
      (dyadicCarrier (negativeNaturalCode lower)) := by
    rw [packet.lowerExact]
    exact carrierReadoutConstant P baseDepth _
  have upperDyadic : EffectiveCauchyReal.Equivalent (toCarrier packet.upperTarget)
      (dyadicCarrier (naturalCode upper)) := by
    rw [packet.upperExact]
    exact carrierReadoutConstant P baseDepth _
  let orders := packet.orders
  exact ⟨realized, rfl, packet, lower, upper, rfl, rfl,
    transportCarrierOrder orders.1.toCarrier lowerDyadic (carrier_roundtrip x),
    transportCarrierOrder orders.2.toCarrier (carrier_roundtrip x) upperDyadic⟩

theorem carrierNaturalBoundsReadout_perimeterIndependent (P Q : CircularPresentation) (baseDepth otherDepth : Nat)
    (x : EffectiveCauchyReal.Carrier) :
    (produceCarrierNaturalBounds P baseDepth x).lower = (produceCarrierNaturalBounds Q otherDepth x).lower ∧
    (produceCarrierNaturalBounds P baseDepth x).upper = (produceCarrierNaturalBounds Q otherDepth x).upper := by
  let first := produceCarrierNaturalBounds P baseDepth x
  let second := produceCarrierNaturalBounds Q otherDepth x
  have firstProbe : first.packet.probe.code = (EffectiveCauchyReal.toPresentation x).approximation 2 := by
    rw [currentReadout _ _ _ first.packet.probe]
    rw [first.realizedExact]
    exact ofPresentation_readout _ _
  have secondProbe : second.packet.probe.code = (EffectiveCauchyReal.toPresentation x).approximation 2 := by
    rw [currentReadout _ _ _ second.packet.probe]
    rw [second.realizedExact]
    exact ofPresentation_readout _ _
  constructor
  · change first.lower = second.lower
    rw [first.lowerExact, second.lowerExact, first.packet.action.stored.exact, second.packet.action.stored.exact]
    change first.packet.action.action.lower = second.packet.action.action.lower
    rw [first.packet.action.action.lowerExact, second.packet.action.action.lowerExact, firstProbe, secondProbe]
  · change first.upper = second.upper
    rw [first.upperExact, second.upperExact, first.packet.action.stored.exact, second.packet.action.stored.exact]
    change first.packet.action.action.upper = second.packet.action.action.upper
    rw [first.packet.action.action.upperExact, second.packet.action.action.upperExact, firstProbe, secondProbe]

theorem carrierDensityReadoutExact (P : CircularPresentation) (baseDepth : Nat)
    {x y : EffectiveCauchyReal.Carrier} (origin : CarrierOrder x y) :
    (produceCarrierDensity P baseDepth origin).code = inspectedDensityCode origin.accuracy
      ((EffectiveCauchyReal.toPresentation x).approximation origin.response)
      ((EffectiveCauchyReal.toPresentation y).approximation origin.response) := by
  let produced := produceCarrierDensity P baseDepth origin
  change produced.code = _
  rw [produced.codeExact, produced.packet.action.readout_is_storedAction]
  change produced.packet.action.action.code = _
  rw [produced.packet.action.action.codeExact, produced.selectionExact]
  rw [currentReadout _ _ _ produced.realizedOrigin.pair.left, currentReadout _ _ _ produced.realizedOrigin.pair.right]
  rw [produced.responseExact]
  unfold ofCarrier
  rw [ofPresentation_readout, ofPresentation_readout]

theorem carrierDensityReadout_perimeterIndependent (P Q : CircularPresentation) (baseDepth otherDepth : Nat)
    {x y : EffectiveCauchyReal.Carrier} (origin : CarrierOrder x y) :
    (produceCarrierDensity P baseDepth origin).code = (produceCarrierDensity Q otherDepth origin).code :=
  (carrierDensityReadoutExact P baseDepth origin).trans (carrierDensityReadoutExact Q otherDepth origin).symm

/-- The convergence law is read from an already constituted native operation.
Its exact readout theorem is stronger than merely choosing an equivalent
value; no numerical operation is used to constitute this native real. -/
def nativeOperationConvergence (presentation : EffectiveDyadicPresentation) (real : Real P baseDepth)
    (exactReadout : (r : Nat) → readout real r = presentation.approximation r) :
    Converges carrierPresentedCore (presentCarrierFamily carrierPresentedCore
      (EffectiveCauchyReal.ofPresentation presentation)) (EffectiveCauchyReal.ofPresentation presentation) where
  threshold p := p
  near p n r s hn hr hs := Near.ofSameLeft (carrierPresentedCore.dyadicExact _ _)
    (ProducedCompleteness.LimitGrouping.transportNear (exactReadout n) (exactReadout s)
      (readoutsNear real p n s hn hs))

def carrierAddConvergence (P : CircularPresentation) (baseDepth : Nat) (x y : EffectiveCauchyReal.Carrier) :
    Converges carrierPresentedCore (canonicalAdditiveFamily carrierPresentedCore x y) (addCarrier x y) :=
  nativeOperationConvergence _ (.add (ofCarrier P baseDepth x) (ofCarrier P baseDepth y)) (by
    intro r
    rw [add_readout_exact]
    unfold ofCarrier
    rw [ofPresentation_readout, ofPresentation_readout]
    rfl)

def carrierNegConvergence (P : CircularPresentation) (baseDepth : Nat) (x : EffectiveCauchyReal.Carrier) :
    Converges carrierPresentedCore (canonicalNegativeFamily carrierPresentedCore x) (negCarrier x) :=
  nativeOperationConvergence _ (.neg (ofCarrier P baseDepth x)) (by
    intro r
    rw [neg_readout_exact]
    unfold ofCarrier
    rw [ofPresentation_readout]
    rfl)

def carrierMulConvergence (P : CircularPresentation) (baseDepth : Nat) (x y : EffectiveCauchyReal.Carrier) :
    Converges carrierPresentedCore (canonicalMultiplicativeFamily carrierPresentedCore x y) (mulCarrier x y) :=
  nativeOperationConvergence _ (.mul (ofCarrier P baseDepth x) (ofCarrier P baseDepth y)) (by
    intro r
    rw [mul_readout_exact]
    unfold ofCarrier
    rw [ofPresentation_readout, ofPresentation_readout, ofPresentation_readout, ofPresentation_readout]
    rfl)

def carrierOrderedData (P : CircularPresentation) (baseDepth : Nat) :
    PresentedDyadicOrderedFieldData carrierPresentedCore where
  zero := canonicalZeroCarrier
  one := canonicalOneCarrier
  zeroExact := .refl _
  oneExact := .refl _
  add := addCarrier
  mul := mulCarrier
  neg := negCarrier
  Order := CarrierOrder
  Apartness := CarrierApartness
  inverse := carrierInverse P baseDepth
  additiveConverges := carrierAddConvergence P baseDepth
  negativeConverges := carrierNegConvergence P baseDepth
  multiplicativeConverges := carrierMulConvergence P baseDepth
  additiveLaws := (carrierOrderedFieldLaws P baseDepth).additive
  multiplicativeLaws := (carrierOrderedFieldLaws P baseDepth).multiplicative
  orderedLaws := (carrierOrderedFieldLaws P baseDepth).ordered
  orderToSeparation order := ⟨order.accuracy, order.response, order.beyond, order.separation⟩
  separationToOrder gap := ⟨gap.accuracy, gap.response, gap.beyond, gap.separation⟩
  apartnessToOrder apartness := apartness
  orderToApartness order := order
  density origin :=
    let produced := produceCarrierDensity P baseDepth origin
    ⟨produced.code, produced.left, produced.right⟩
  naturalBounds x :=
    let produced := produceCarrierNaturalBounds P baseDepth x
    ⟨produced.lower, produced.upper, produced.lowerOrder, produced.upperOrder⟩

def carrierOrderedCompletion (P : CircularPresentation) (baseDepth : Nat) : PresentedDyadicOrderedFieldCompletion :=
  ⟨carrierPresentedCore, carrierCompletionStructure P baseDepth, carrierOrderedData P baseDepth⟩

def carrierOrderedCompletionIndependent (P Q : CircularPresentation) (baseDepth otherDepth : Nat) :
    OrderedCompletionPointwiseEquivalent carrierPresentedCore
      (carrierCompletionStructure P baseDepth) (carrierCompletionStructure Q otherDepth)
      (carrierOrderedData P baseDepth) (carrierOrderedData Q otherDepth) where
  zeroEquivalent := .refl _
  oneEquivalent := .refl _
  addEquivalent _ _ := .refl _
  negEquivalent _ := .refl _
  mulEquivalent _ _ := .refl _
  completeEquivalent family := carrierCompletion_perimeterIndependent P Q baseDepth otherDepth (asCarrierFamily family)
  preserveApartness apartness := apartness
  reflectApartness apartness := apartness
  transportInverseDomain domain := domain
  reflectInverseDomain domain := domain
  inverse := carrierInverse_perimeterIndependent P Q baseDepth otherDepth
  preserveOrder order := order
  reflectOrder order := order
  preserveDensity witness := witness
  reflectDensity witness := witness
  preserveBounds witness := witness
  reflectBounds witness := witness
  densityReadoutExact := carrierDensityReadout_perimeterIndependent P Q baseDepth otherDepth
  lowerBoundReadoutExact x := (carrierNaturalBoundsReadout_perimeterIndependent P Q baseDepth otherDepth x).1
  upperBoundReadoutExact x := (carrierNaturalBoundsReadout_perimeterIndependent P Q baseDepth otherDepth x).2

end RelationalPerimeter.Constitution.Reals.CarrierOrderedField

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Constitution.Reals.CarrierOrderedField.CarrierDensityResult
#print axioms RelationalPerimeter.Constitution.Reals.CarrierOrderedField.produceCarrierDensity
#print axioms RelationalPerimeter.Constitution.Reals.CarrierOrderedField.CarrierNaturalBoundResult
#print axioms RelationalPerimeter.Constitution.Reals.CarrierOrderedField.produceCarrierNaturalBounds
#print axioms RelationalPerimeter.Constitution.Reals.CarrierOrderedField.carrierNaturalBoundsReadout_perimeterIndependent
#print axioms RelationalPerimeter.Constitution.Reals.CarrierOrderedField.inspectedDensityCode
#print axioms RelationalPerimeter.Constitution.Reals.CarrierOrderedField.forwardMidpointCode
#print axioms RelationalPerimeter.Constitution.Reals.CarrierOrderedField.forwardResponse
#print axioms RelationalPerimeter.Constitution.Reals.CarrierOrderedField.carrierDensityReadoutExact
#print axioms RelationalPerimeter.Constitution.Reals.CarrierOrderedField.carrierDensityReadout_perimeterIndependent
#print axioms RelationalPerimeter.Constitution.Reals.CarrierOrderedField.nativeOperationConvergence
#print axioms RelationalPerimeter.Constitution.Reals.CarrierOrderedField.carrierAddConvergence
#print axioms RelationalPerimeter.Constitution.Reals.CarrierOrderedField.carrierNegConvergence
#print axioms RelationalPerimeter.Constitution.Reals.CarrierOrderedField.carrierMulConvergence
#print axioms RelationalPerimeter.Constitution.Reals.CarrierOrderedField.carrierOrderedData
#print axioms RelationalPerimeter.Constitution.Reals.CarrierOrderedField.carrierOrderedCompletion
#print axioms RelationalPerimeter.Constitution.Reals.CarrierOrderedField.carrierOrderedCompletionIndependent
/- AXIOM_AUDIT_END -/
