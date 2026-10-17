import RelationalPerimeter.Constitution.Reals.RelationalRealNativeCauchy
import RelationalPerimeter.Constitution.Reals.RelationalRealDensity
import RelationalPerimeter.Constitution.Reals.RelationalRealInverseCorrespondence

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Concrete effective behavioural correspondence (gate 6 only)

The class is Real P baseDepth and executable coherent dyadic presentations
(or effective carriers with their own monotone response moduli). Native
Cauchy families additionally receive a positive law on current Steps.
No quotient, equality of occurrences or coverage of unrestricted reals is
claimed. Realization is a declared relational input; readout is downstream.

ApplicationMaps ties its exported functions pointwise to the fixed application
names used by the transport blocks. This avoids function extensionality and
does not let an unrelated implementation silently satisfy a transport.
All blocks below have concrete inhabitants derived from existing producers
and proofs; none is an assumption of the final constructor.
-/
namespace RelationalPerimeter.Constitution.Reals.RelationalRealEffectiveCorrespondence
open StrongPerimetralTurning ProducedCompleteness RuntimeCorrespondence
open HeterogeneousRealRuntime RelationalRealAddition RelationalRealOrder
open RelationalRealOrderedField RelationalRealDensity RelationalRealCauchy
open RelationalRealFamilyTransport RelationalRealLimitUniqueness
open ConstitutiveRuntime
variable {P : CircularPresentation} {baseDepth : Nat}

def presentationRoundtrip (value : EffectiveDyadicPresentation) :
    EffectiveDyadicPresentation.Equivalent (toPresentation (ofPresentation P baseDepth value)) value where
  responseThreshold := fun p => p
  near := by
    intro p l r hl hr
    change Near p (readout (ofPresentation P baseDepth value) l) (value.approximation r)
    rw [ofPresentation_readout]
    exact value.coherent p l r hl hr

def constantPreservation (code : SignedDyadicCode) :
    EffectiveDyadicPresentation.Equivalent (toPresentation (dyadic P baseDepth code))
      (EffectiveDyadicPresentation.constant code) where
  responseThreshold := fun p => p
  near := by
    intro p l r hl hr
    change Near p (executeReal (dyadic P baseDepth code) l).code (code.raise r)
    exact ((dyadicStepSame (executeReal (dyadic P baseDepth code) l)).trans
      (SameValue.raiseExact code r)).toNear p

def constantRealization (code : SignedDyadicCode) :
    Equivalent (dyadic P baseDepth code)
      (ofPresentation P baseDepth (EffectiveDyadicPresentation.constant code)) :=
  Equivalent.ofExact (fun p => by
    rw [ofPresentation_readout]
    exact (dyadicStepSame (executeReal (dyadic P baseDepth code) p)).trans (SameValue.raiseExact code p))

def realizeApartness (left right : EffectiveDyadicPresentation) (numeric : PresentationApartness left right)
    (aa : (environment (ofPresentation P baseDepth left)).Archive)
    (ba : (environment (ofPresentation P baseDepth right)).Archive) :
    Apartness (ofPresentation P baseDepth left) (ofPresentation P baseDepth right) :=
  match numeric with
  | .inl order => .forward (realizePresentationOrder left right order aa ba)
  | .inr order => .backward (realizePresentationOrder right left order ba aa)

def projectDensity {a b : Real P baseDepth} {origin : StrictOrder a b}
    {journal : Journal P baseDepth} (packet : Density origin journal) :
    (PresentationOrder (toPresentation a) (toPresentation packet.target) ×
      PresentationOrder (toPresentation packet.target) (toPresentation b)) ×
    (CarrierOrder (toCarrier a) (toCarrier packet.target) × CarrierOrder (toCarrier packet.target) (toCarrier b)) :=
  ⟨⟨packet.orders.1.toPresentation, packet.orders.2.toPresentation⟩,
    ⟨packet.orders.1.toCarrier, packet.orders.2.toCarrier⟩⟩

def projectBounds {source : Real P baseDepth} {archive : (environment source).Archive}
    {journal : Journal P baseDepth} (packet : NaturalBound source archive journal) :
    (PresentationOrder (toPresentation packet.lowerTarget) (toPresentation source) ×
      PresentationOrder (toPresentation source) (toPresentation packet.upperTarget)) ×
    (CarrierOrder (toCarrier packet.lowerTarget) (toCarrier source) ×
      CarrierOrder (toCarrier source) (toCarrier packet.upperTarget)) :=
  ⟨⟨packet.orders.1.toPresentation, packet.orders.2.toPresentation⟩,
    ⟨packet.orders.1.toCarrier, packet.orders.2.toCarrier⟩⟩

structure ApplicationMaps (P : CircularPresentation) (baseDepth : Nat) where
  toEffective : Real P baseDepth → EffectiveDyadicPresentation
  fromEffective : EffectiveDyadicPresentation → Real P baseDepth
  toCarrierEffective : Real P baseDepth → EffectiveCauchyReal.Carrier
  fromCarrierEffective : EffectiveCauchyReal.Carrier → Real P baseDepth
  toEffectiveExact : (x : Real P baseDepth) → toEffective x = toPresentation x
  fromEffectiveExact : (x : EffectiveDyadicPresentation) → fromEffective x = ofPresentation P baseDepth x
  toCarrierExact : (x : Real P baseDepth) → toCarrierEffective x = toCarrier x
  fromCarrierExact : (x : EffectiveCauchyReal.Carrier) → fromCarrierEffective x = ofCarrier P baseDepth x
  realReturn : (x : Real P baseDepth) → Equivalent (fromEffective (toEffective x)) x
  realFutureReturn : (x : Real P baseDepth) → NumericalFutureEquivalent (fromEffective (toEffective x)) x
  effectiveReturn : (x : EffectiveDyadicPresentation) → EffectiveDyadicPresentation.Equivalent (toEffective (fromEffective x)) x
  realCarrierReturn : (x : Real P baseDepth) → Equivalent (fromCarrierEffective (toCarrierEffective x)) x
  realCarrierFutureReturn : (x : Real P baseDepth) → NumericalFutureEquivalent (fromCarrierEffective (toCarrierEffective x)) x
  carrierReturn : (x : EffectiveCauchyReal.Carrier) → EffectiveCauchyReal.Equivalent (toCarrierEffective (fromCarrierEffective x)) x
  preserveEquivalent : {a b : Real P baseDepth} → Equivalent a b → EffectiveDyadicPresentation.Equivalent (toEffective a) (toEffective b)
  reflectEquivalent : {a b : Real P baseDepth} → EffectiveDyadicPresentation.Equivalent (toEffective a) (toEffective b) → Equivalent a b
  preserveCarrierEquivalent : {a b : Real P baseDepth} → Equivalent a b → EffectiveCauchyReal.Equivalent (toCarrierEffective a) (toCarrierEffective b)
  reflectCarrierEquivalent : {a b : Real P baseDepth} → EffectiveCauchyReal.Equivalent (toCarrierEffective a) (toCarrierEffective b) → Equivalent a b
  equivalentFutures : (a b : Real P baseDepth) → (Equivalent a b → NumericalFutureEquivalent a b) × (NumericalFutureEquivalent a b → Equivalent a b)

def applicationMaps (P : CircularPresentation) (baseDepth : Nat) : ApplicationMaps P baseDepth where
  toEffective := toPresentation
  fromEffective := ofPresentation P baseDepth
  toCarrierEffective := toCarrier
  fromCarrierEffective := ofCarrier P baseDepth
  toEffectiveExact := fun _ => rfl
  fromEffectiveExact := fun _ => rfl
  toCarrierExact := fun _ => rfl
  fromCarrierExact := fun _ => rfl
  realReturn := real_roundtrip
  realFutureReturn := fun x => (real_roundtrip x).toFutures
  effectiveReturn := presentationRoundtrip
  realCarrierReturn := real_roundtrip
  realCarrierFutureReturn := fun x => (real_roundtrip x).toFutures
  carrierReturn := carrier_roundtrip
  preserveEquivalent := fun same => (equivalentPresentation _ _).1 same
  reflectEquivalent := fun same => (equivalentPresentation _ _).2 same
  preserveCarrierEquivalent := fun same => (equivalentCarrier _ _).1 same
  reflectCarrierEquivalent := fun same => (equivalentCarrier _ _).2 same
  equivalentFutures := numericalFutureCorrespondence

structure OperationTransports (P : CircularPresentation) (baseDepth : Nat) where
  constants : (code : SignedDyadicCode) → EffectiveDyadicPresentation.Equivalent (toPresentation (dyadic P baseDepth code)) (EffectiveDyadicPresentation.constant code)
  realizeConstants : (code : SignedDyadicCode) → Equivalent (dyadic P baseDepth code) (ofPresentation P baseDepth (EffectiveDyadicPresentation.constant code))
  zero : EffectiveDyadicPresentation.Equivalent (toPresentation (zero P baseDepth)) (EffectiveDyadicPresentation.constant SignedDyadicCode.zero)
  one : EffectiveDyadicPresentation.Equivalent (toPresentation (one P baseDepth)) (EffectiveDyadicPresentation.constant SignedDyadicCode.one)
  add : (a b : Real P baseDepth) → EffectiveDyadicPresentation.Equivalent (toPresentation (.add a b)) (addPresentation (toPresentation a) (toPresentation b))
  realizeAdd : (a b : EffectiveDyadicPresentation) → Equivalent (.add (ofPresentation P baseDepth a) (ofPresentation P baseDepth b)) (ofPresentation P baseDepth (addPresentation a b))
  neg : (a : Real P baseDepth) → EffectiveDyadicPresentation.Equivalent (toPresentation (.neg a)) (negPresentation (toPresentation a))
  realizeNeg : (a : EffectiveDyadicPresentation) → Equivalent (.neg (ofPresentation P baseDepth a)) (ofPresentation P baseDepth (negPresentation a))
  mul : (a b : Real P baseDepth) → EffectiveDyadicPresentation.Equivalent (toPresentation (.mul a b)) (mulPresentation (toPresentation a) (toPresentation b))
  realizeMul : (a b : EffectiveDyadicPresentation) → Equivalent (.mul (ofPresentation P baseDepth a) (ofPresentation P baseDepth b)) (ofPresentation P baseDepth (mulPresentation a b))
  carrierAdd : (a b : Real P baseDepth) → EffectiveCauchyReal.Equivalent (toCarrier (.add a b)) (addCarrier (toCarrier a) (toCarrier b))
  realizeCarrierAdd : (a b : EffectiveCauchyReal.Carrier) → Equivalent (.add (ofCarrier P baseDepth a) (ofCarrier P baseDepth b)) (ofCarrier P baseDepth (addCarrier a b))
  carrierNeg : (a : Real P baseDepth) → EffectiveCauchyReal.Equivalent (toCarrier (.neg a)) (negCarrier (toCarrier a))
  realizeCarrierNeg : (a : EffectiveCauchyReal.Carrier) → Equivalent (.neg (ofCarrier P baseDepth a)) (ofCarrier P baseDepth (negCarrier a))
  carrierMul : (a b : Real P baseDepth) → EffectiveCauchyReal.Equivalent (toCarrier (.mul a b)) (mulCarrier (toCarrier a) (toCarrier b))
  realizeCarrierMul : (a b : EffectiveCauchyReal.Carrier) → Equivalent (.mul (ofCarrier P baseDepth a) (ofCarrier P baseDepth b)) (ofCarrier P baseDepth (mulCarrier a b))
  inverse : (a : Real P baseDepth) → (w : Apartness a (RelationalRealAddition.zero P baseDepth)) → EffectiveDyadicPresentation.Equivalent (toPresentation (RelationalRealInverse.inverse a w)) (RelationalRealInverse.inversePresentation (toPresentation a) w.toPresentation)
  realizeInverse : (a : EffectiveDyadicPresentation) → (w : RelationalRealInverse.PresentationDomain P baseDepth a) → Equivalent (RelationalRealInverse.inverse (ofPresentation P baseDepth a) (RelationalRealInverse.realizePresentationDomain a w (environment (ofPresentation P baseDepth a)).initialArchive (environment (RelationalRealAddition.zero P baseDepth)).initialArchive)) (ofPresentation P baseDepth (RelationalRealInverse.inversePresentation a w))
  carrierInverse : (a : Real P baseDepth) → (w : Apartness a (RelationalRealAddition.zero P baseDepth)) → EffectiveCauchyReal.Equivalent (toCarrier (RelationalRealInverse.inverse a w)) (RelationalRealInverse.inverseCarrier (toCarrier a) w.toCarrier)
  realizeCarrierInverse : (a : EffectiveCauchyReal.Carrier) → (w : RelationalRealInverse.CarrierDomain P baseDepth a) → Equivalent (RelationalRealInverse.inverse (ofCarrier P baseDepth a) (RelationalRealInverse.realizeCarrierDomain a w (environment (ofCarrier P baseDepth a)).initialArchive (environment (RelationalRealAddition.zero P baseDepth)).initialArchive)) (ofCarrier P baseDepth (RelationalRealInverse.inverseCarrier a w))

def operationTransports (P : CircularPresentation) (baseDepth : Nat) : OperationTransports P baseDepth where
  constants := constantPreservation
  realizeConstants := constantRealization
  zero := constantPreservation _
  one := constantPreservation _
  add := toPresentation_add
  realizeAdd := realization_add
  neg := toPresentation_neg
  realizeNeg := realization_neg
  mul := toPresentation_mul
  realizeMul := realization_mul
  carrierAdd := toCarrier_add
  realizeCarrierAdd := realization_carrier_add
  carrierNeg := toCarrier_neg
  realizeCarrierNeg := realization_carrier_neg
  carrierMul := toCarrier_mul
  realizeCarrierMul := realization_carrier_mul
  inverse := RelationalRealInverse.toPresentation_inverse
  realizeInverse := RelationalRealInverse.realization_inverse
  carrierInverse := RelationalRealInverse.toCarrier_inverse
  realizeCarrierInverse := RelationalRealInverse.realization_carrier_inverse

structure RelationTransports (P : CircularPresentation) (baseDepth : Nat) where
  order : {a b : Real P baseDepth} → StrictOrder a b → PresentationOrder (toPresentation a) (toPresentation b)
  reflectOrder : {a b : Real P baseDepth} → PresentationOrder (toPresentation a) (toPresentation b) → (environment a).Archive → (environment b).Archive → StrictOrder a b
  realizeOrder : (a b : EffectiveDyadicPresentation) → PresentationOrder a b → (environment (ofPresentation P baseDepth a)).Archive → (environment (ofPresentation P baseDepth b)).Archive → StrictOrder (ofPresentation P baseDepth a) (ofPresentation P baseDepth b)
  apartness : {a b : Real P baseDepth} → Apartness a b → PresentationApartness (toPresentation a) (toPresentation b)
  reflectApartness : {a b : Real P baseDepth} → PresentationApartness (toPresentation a) (toPresentation b) → (environment a).Archive → (environment b).Archive → Apartness a b
  realizeApartness : (a b : EffectiveDyadicPresentation) → PresentationApartness a b → (environment (ofPresentation P baseDepth a)).Archive → (environment (ofPresentation P baseDepth b)).Archive → Apartness (ofPresentation P baseDepth a) (ofPresentation P baseDepth b)
  carrierOrder : {a b : Real P baseDepth} → StrictOrder a b → CarrierOrder (toCarrier a) (toCarrier b)
  reflectCarrierOrder : {a b : Real P baseDepth} → CarrierOrder (toCarrier a) (toCarrier b) → (environment a).Archive → (environment b).Archive → StrictOrder a b
  realizeCarrierOrder : (a b : EffectiveCauchyReal.Carrier) → CarrierOrder a b → (environment (ofCarrier P baseDepth a)).Archive → (environment (ofCarrier P baseDepth b)).Archive → StrictOrder (ofCarrier P baseDepth a) (ofCarrier P baseDepth b)
  carrierApartness : {a b : Real P baseDepth} → Apartness a b → CarrierApartness (toCarrier a) (toCarrier b)
  reflectCarrierApartness : {a b : Real P baseDepth} → CarrierApartness (toCarrier a) (toCarrier b) → (environment a).Archive → (environment b).Archive → Apartness a b
  realizeCarrierApartness : (a b : EffectiveCauchyReal.Carrier) → CarrierApartness a b → (environment (ofCarrier P baseDepth a)).Archive → (environment (ofCarrier P baseDepth b)).Archive → Apartness (ofCarrier P baseDepth a) (ofCarrier P baseDepth b)
  inverseDomain : (a : EffectiveDyadicPresentation) → RelationalRealInverse.PresentationDomain P baseDepth a → (environment (ofPresentation P baseDepth a)).Archive → (environment (RelationalRealAddition.zero P baseDepth)).Archive → Apartness (ofPresentation P baseDepth a) (RelationalRealAddition.zero P baseDepth)
  carrierInverseDomain : (a : EffectiveCauchyReal.Carrier) → RelationalRealInverse.CarrierDomain P baseDepth a → (environment (ofCarrier P baseDepth a)).Archive → (environment (RelationalRealAddition.zero P baseDepth)).Archive → Apartness (ofCarrier P baseDepth a) (RelationalRealAddition.zero P baseDepth)

def relationTransports (P : CircularPresentation) (baseDepth : Nat) : RelationTransports P baseDepth where
  order := StrictOrder.toPresentation
  reflectOrder := reflectPresentationOrder
  realizeOrder := realizePresentationOrder
  apartness := Apartness.toPresentation
  reflectApartness := reflectPresentationApartness
  realizeApartness := RelationalRealEffectiveCorrespondence.realizeApartness
  carrierOrder := StrictOrder.toCarrier
  reflectCarrierOrder := RelationalRealOrder.reflectCarrierOrder
  realizeCarrierOrder := RelationalRealOrder.realizeCarrierOrder
  carrierApartness := Apartness.toCarrier
  reflectCarrierApartness := RelationalRealOrder.reflectCarrierApartness
  realizeCarrierApartness := fun a b => RelationalRealEffectiveCorrespondence.realizeApartness (EffectiveCauchyReal.toPresentation a) (EffectiveCauchyReal.toPresentation b)
  inverseDomain := RelationalRealInverse.realizePresentationDomain
  carrierInverseDomain := RelationalRealInverse.realizeCarrierDomain

structure OrderAndFiniteWitnesses (P : CircularPresentation) (baseDepth : Nat) where
  laws : ConstructiveOrderedFieldLaws P baseDepth
  futureLaws : ConstructiveOrderedFieldFutureLaws P baseDepth
  density : {a b : Real P baseDepth} → (origin : StrictOrder a b) → (journal : Journal P baseDepth) → Density origin journal
  densityProjection : {a b : Real P baseDepth} → {origin : StrictOrder a b} → {journal : Journal P baseDepth} → (packet : Density origin journal) → (PresentationOrder (toPresentation a) (toPresentation packet.target) × PresentationOrder (toPresentation packet.target) (toPresentation b)) × (CarrierOrder (toCarrier a) (toCarrier packet.target) × CarrierOrder (toCarrier packet.target) (toCarrier b))
  bounds : (a : Real P baseDepth) → (archive : (environment a).Archive) → (journal : Journal P baseDepth) → NaturalBound a archive journal
  boundProjection : {a : Real P baseDepth} → {archive : (environment a).Archive} → {journal : Journal P baseDepth} → (packet : NaturalBound a archive journal) → (PresentationOrder (toPresentation packet.lowerTarget) (toPresentation a) × PresentationOrder (toPresentation a) (toPresentation packet.upperTarget)) × (CarrierOrder (toCarrier packet.lowerTarget) (toCarrier a) × CarrierOrder (toCarrier a) (toCarrier packet.upperTarget))

def orderAndFiniteWitnesses (P : CircularPresentation) (baseDepth : Nat) : OrderAndFiniteWitnesses P baseDepth where
  laws := orderedFieldLaws P baseDepth
  futureLaws := orderedFieldFutureLaws P baseDepth
  density := produceDensity
  densityProjection := projectDensity
  bounds := produceNaturalBound
  boundProjection := projectBounds

structure FamilyCorrespondence (P : CircularPresentation) (baseDepth : Nat) where
  toEffective : ExecutedCauchyFamily P baseDepth → EffectiveFamily
  fromEffective : EffectiveFamily → ExecutedCauchyFamily P baseDepth
  toEffectiveExact : (family : ExecutedCauchyFamily P baseDepth) → toEffective family = readoutFamily family
  fromEffectiveExact : (numeric : EffectiveFamily) → fromEffective numeric = realizeFamily P baseDepth numeric
  producerAt : (numeric : EffectiveFamily) → (request : SourceRequest) → (fromEffective numeric).producer.calculate request = (numeric.terms request.term).approximation request.precision
  modulus : (numeric : EffectiveFamily) → (fromEffective numeric).modulus = numeric.modulus
  effectiveReturn : (numeric : EffectiveFamily) → TermwiseUniformEquivalent (readoutFamily (realizeFamily P baseDepth numeric)) numeric
  effectiveReturnAt : (numeric : EffectiveFamily) → (n p : Nat) → ((readoutFamily (realizeFamily P baseDepth numeric)).terms n).approximation p = (numeric.terms n).approximation p
  realizedTerm : (numeric : EffectiveFamily) → (n : Nat) → Equivalent (termReal (realizeFamily P baseDepth numeric) n) (ofPresentation P baseDepth (numeric.terms n))
  realizedTermFuture : (numeric : EffectiveFamily) → (n : Nat) → NumericalFutureEquivalent (termReal (realizeFamily P baseDepth numeric) n) (ofPresentation P baseDepth (numeric.terms n))
  restoredProducer : (family : ExecutedCauchyFamily P baseDepth) → (returnedFamily family).producer = family.producer
  restoredModulus : (family : ExecutedCauchyFamily P baseDepth) → (returnedFamily family).modulus = family.modulus
  sourceReturn : (family : ExecutedCauchyFamily P baseDepth) → TermwiseUniformEquivalent (readoutFamily (returnedFamily family)) (readoutFamily family)
  sourceTermReturn : (family : ExecutedCauchyFamily P baseDepth) → (n : Nat) → Equivalent (termReal (returnedFamily family) n) (termReal family n)
  sourceTermFuture : (family : ExecutedCauchyFamily P baseDepth) → (n : Nat) → NumericalFutureEquivalent (termReal (returnedFamily family) n) (termReal family n)
  sourceCompleteness : (family : ExecutedCauchyFamily P baseDepth) → InternalCompleteness family
  nativeReadout : RelationalRealNativeCauchy.NativeCauchyFamily P baseDepth → EffectiveFamily
  nativeReadoutExact : (family : RelationalRealNativeCauchy.NativeCauchyFamily P baseDepth) → nativeReadout family = RelationalRealNativeCauchy.toEffectiveFamily family
  nativeCompleteness : (family : RelationalRealNativeCauchy.NativeCauchyFamily P baseDepth) → RelationalRealNativeCauchy.NativeCompleteness family
  nativeUniqueness : {family : RelationalRealNativeCauchy.NativeCauchyFamily P baseDepth} → (first second : RelationalRealNativeCauchy.NativeCandidate family) → Equivalent first.real second.real × NumericalFutureEquivalent first.real second.real
  toCarriers : ExecutedCauchyFamily P baseDepth → CarrierFamily
  fromCarriers : CarrierFamily → ExecutedCauchyFamily P baseDepth
  normalizeCarriers : CarrierFamily → EffectiveFamily
  normalizedCodes : (numeric : EffectiveFamily) → (n p : Nat) → ((normalizeCarrierFamily (carrierFamily numeric)).terms n).approximation p = (numeric.terms n).approximation p
  carrierReturn : (numeric : CarrierFamily) → (n : Nat) → EffectiveCauchyReal.Equivalent ((carrierFamily (normalizeCarrierFamily numeric)).terms n) (numeric.terms n)

def familyCorrespondence (P : CircularPresentation) (baseDepth : Nat) : FamilyCorrespondence P baseDepth where
  toEffective := readoutFamily
  fromEffective := realizeFamily P baseDepth
  toEffectiveExact := fun _ => rfl
  fromEffectiveExact := fun _ => rfl
  producerAt := realizedProducerAt
  modulus := realizedModulus
  effectiveReturn := effectiveRoundtrip
  effectiveReturnAt := effectiveReturnAt
  realizedTerm := RelationalRealFamilyTransport.realizedTermEquivalent
  realizedTermFuture := RelationalRealFamilyTransport.realizedTermFutures
  restoredProducer := returnedProducer
  restoredModulus := returnedModulus
  sourceReturn := relationalRoundtrip
  sourceTermReturn := relationalTermRoundtrip
  sourceTermFuture := relationalTermFutures
  sourceCompleteness := internalCompleteness
  nativeReadout := RelationalRealNativeCauchy.toEffectiveFamily
  nativeReadoutExact := fun _ => rfl
  nativeCompleteness := RelationalRealNativeCauchy.nativeCompleteness
  nativeUniqueness := RelationalRealNativeCauchy.nativeUnique
  toCarriers := readoutCarrierFamily
  fromCarriers := realizeCarrierFamily P baseDepth
  normalizeCarriers := normalizeCarrierFamily
  normalizedCodes := normalizedReturnAt
  carrierReturn := carrierTermRoundtrip

structure LimitCorrespondence (P : CircularPresentation) (baseDepth : Nat) where
  nativeCandidate : (family : RelationalRealNativeCauchy.NativeCauchyFamily P baseDepth) → RelationalRealNativeCauchy.NativeCandidate family
  nativeCandidateReal : (family : RelationalRealNativeCauchy.NativeCauchyFamily P baseDepth) → (nativeCandidate family).real = RelationalRealNativeCauchy.nativeLimit family
  nativeProducedProjection : (family : RelationalRealNativeCauchy.NativeCauchyFamily P baseDepth) →
    Equivalent (limitReal (RelationalRealNativeCauchy.realizedFamily family)) (RelationalRealNativeCauchy.nativeLimit family) ×
      NumericalFutureEquivalent (limitReal (RelationalRealNativeCauchy.realizedFamily family)) (RelationalRealNativeCauchy.nativeLimit family)
  preserveAt : {family : ExecutedCauchyFamily P baseDepth} → (candidate : LimitCandidate family) → (p n r s : Nat) →
  {ta : TermArchive family} → {a : (environment candidate.real).Archive} →
  (term : Step (environment (termReal family n)) ta r) → (response : Step (environment candidate.real) a s) →
  PrecisionExtension (family.modulus p) n → PrecisionExtension p r → PrecisionExtension (candidate.threshold p) s →
  Near p (((readoutFamily family).terms n).approximation r) ((toPresentation candidate.real).approximation s)
  observe : {family : ExecutedCauchyFamily P baseDepth} → (candidate : LimitCandidate family) → (p n r s : Nat) →
  (ta : TermArchive family) → (a : (environment candidate.real).Archive) →
  (hn : PrecisionExtension (family.modulus p) n) → (hr : PrecisionExtension p r) → (hs : PrecisionExtension (candidate.threshold p) s) →
  RelationalRealFamilyTransport.LimitObservation candidate p n r s ta a hn hr hs
  preserve : {family : ExecutedCauchyFamily P baseDepth} → (candidate : LimitCandidate family) → PresentationLimit (readoutFamily family) (toPresentation candidate.real)
  reflect : {family : ExecutedCauchyFamily P baseDepth} → (real : Real P baseDepth) → PresentationLimit (readoutFamily family) (toPresentation real) → LimitCandidate family
  realize : (numeric : EffectiveFamily) → (value : EffectiveDyadicPresentation) → PresentationLimit numeric value → LimitCandidate (realizeFamily P baseDepth numeric)
  routeA : (family : ExecutedCauchyFamily P baseDepth) → LimitCandidate (returnedFamily family)
  routeAExact : (family : ExecutedCauchyFamily P baseDepth) → (routeA family).real = limitReal family
  routeAThreshold : (family : ExecutedCauchyFamily P baseDepth) → (p : Nat) → (routeA family).threshold p = p
  rebuiltAuthoritative : (family : ExecutedCauchyFamily P baseDepth) → LimitCandidate (returnedFamily family)
  sourceLimitReturn : (family : ExecutedCauchyFamily P baseDepth) → Equivalent (limitReal (returnedFamily family)) (limitReal family) × NumericalFutureEquivalent (limitReal (returnedFamily family)) (limitReal family)
  realizedLimit : (numeric : EffectiveFamily) → (value : EffectiveDyadicPresentation) → PresentationLimit numeric value → Equivalent (limitReal (realizeFamily P baseDepth numeric)) (ofPresentation P baseDepth value) × NumericalFutureEquivalent (limitReal (realizeFamily P baseDepth numeric)) (ofPresentation P baseDepth value)
  carrierRealize : (numeric : CarrierFamily) → (value : EffectiveCauchyReal.Carrier) → CarrierLimit numeric value → LimitCandidate (realizeCarrierFamily P baseDepth numeric)
  carrierPreserve : {family : ExecutedCauchyFamily P baseDepth} → (candidate : LimitCandidate family) → CarrierLimit (readoutCarrierFamily family) (toCarrier candidate.real)
  uniqueness : {family : ExecutedCauchyFamily P baseDepth} → (first second : LimitCandidate family) → Equivalent first.real second.real × NumericalFutureEquivalent first.real second.real
  authoritativeUniqueness : {family : ExecutedCauchyFamily P baseDepth} → (candidate : LimitCandidate family) → Equivalent (limitReal family) candidate.real × NumericalFutureEquivalent (limitReal family) candidate.real
  richUniqueness : {family : ExecutedCauchyFamily P baseDepth} → (first second : LimitCandidate family) → (ta : TermArchive family) → (aa : (environment first.real).Archive) → (ba : (environment second.real).Archive) → (queries : List (LimitQuery (uniquenessThreshold first second))) → UniquenessTrace first second ta aa ba queries
  projectUniqueness : {family : ExecutedCauchyFamily P baseDepth} → {first second : LimitCandidate family} → {ta : TermArchive family} → {aa : (environment first.real).Archive} → {ba : (environment second.real).Archive} → {queries : List (LimitQuery (uniquenessThreshold first second))} → UniquenessTrace first second ta aa ba queries → NumericalTrace first.real second.real (uniquenessThreshold first second) aa ba queries

def limitCorrespondence (P : CircularPresentation) (baseDepth : Nat) : LimitCorrespondence P baseDepth where
  nativeCandidate := RelationalRealNativeCauchy.nativeAuthoritative
  nativeCandidateReal := fun _ => rfl
  nativeProducedProjection := RelationalRealNativeCauchy.nativeProducedLimitCorrespondence
  preserveAt := preserveLimitAt
  observe := RelationalRealFamilyTransport.observeLimit
  preserve := preserveLimit
  reflect := reflectLimit
  realize := realizeLimit
  routeA := returnedCandidate
  routeAExact := fun _ => rfl
  routeAThreshold := fun _ _ => rfl
  rebuiltAuthoritative := returnedAuthoritative
  sourceLimitReturn := relationalLimitRoundtrip
  realizedLimit := realizedLimitEquivalence
  carrierRealize := realizeCarrierLimit
  carrierPreserve := preserveCarrierLimit
  uniqueness := unique
  authoritativeUniqueness := authoritativeUnique
  richUniqueness := produceTrace
  projectUniqueness := UniquenessTrace.toNumerical

/-! No field below asks for a missing theorem. The concrete constructor closes
every block. Native completeness includes composed term families, not merely
the term-source service of an already received ExecutedCauchyFamily. -/
structure EffectiveCorrespondence (P : CircularPresentation) (baseDepth : Nat) where
  applications : ApplicationMaps P baseDepth
  operations : OperationTransports P baseDepth
  relations : RelationTransports P baseDepth
  ordered : OrderAndFiniteWitnesses P baseDepth
  families : FamilyCorrespondence P baseDepth
  limits : LimitCorrespondence P baseDepth

def effectiveCorrespondence (P : CircularPresentation) (baseDepth : Nat) : EffectiveCorrespondence P baseDepth where
  applications := applicationMaps P baseDepth
  operations := operationTransports P baseDepth
  relations := relationTransports P baseDepth
  ordered := orderAndFiniteWitnesses P baseDepth
  families := familyCorrespondence P baseDepth
  limits := limitCorrespondence P baseDepth

end RelationalPerimeter.Constitution.Reals.RelationalRealEffectiveCorrespondence

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealEffectiveCorrespondence.presentationRoundtrip
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealEffectiveCorrespondence.constantPreservation
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealEffectiveCorrespondence.constantRealization
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealEffectiveCorrespondence.realizeApartness
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealEffectiveCorrespondence.projectDensity
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealEffectiveCorrespondence.projectBounds
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealEffectiveCorrespondence.ApplicationMaps
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealEffectiveCorrespondence.applicationMaps
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealEffectiveCorrespondence.OperationTransports
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealEffectiveCorrespondence.operationTransports
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealEffectiveCorrespondence.RelationTransports
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealEffectiveCorrespondence.relationTransports
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealEffectiveCorrespondence.OrderAndFiniteWitnesses
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealEffectiveCorrespondence.orderAndFiniteWitnesses
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealEffectiveCorrespondence.FamilyCorrespondence
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealEffectiveCorrespondence.familyCorrespondence
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealEffectiveCorrespondence.LimitCorrespondence
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealEffectiveCorrespondence.limitCorrespondence
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealEffectiveCorrespondence.EffectiveCorrespondence
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealEffectiveCorrespondence.effectiveCorrespondence
/- AXIOM_AUDIT_END -/
