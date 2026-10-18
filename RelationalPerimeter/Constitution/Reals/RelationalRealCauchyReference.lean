import RelationalPerimeter.Constitution.Reals.ExtensiveCauchyRealCompletion
import RelationalPerimeter.Constitution.Reals.DyadicCompletionOrderedCharacterization

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace RelationalPerimeter.Constitution.Reals.RelationalRealCauchyReference
open StrongPerimetralTurning PresentedDyadicCompletion DyadicCompletionCharacterization
open RegularDyadicCompletion ExtensiveCauchyReal
open RelationalRealAddition RelationalRealOrder CarrierOrderedField
open RelationalRealFamilyTransport RelationalRealCarrierCompleteness RegularDyadicName

def regularCharacterization (P : CircularPresentation) (baseDepth : Nat) :=
  relativeOrderedCharacterization P baseDepth regularOrderedCompletion

def carrierToReferenceName (P : CircularPresentation) (baseDepth : Nat)
    (carrier : EffectiveCauchyReal.Carrier) : RegularDyadicName :=
  (regularCharacterization P baseDepth).forward.map carrier

def referenceNameToCarrier (P : CircularPresentation) (baseDepth : Nat)
    (name : RegularDyadicName) : EffectiveCauchyReal.Carrier :=
  (regularCharacterization P baseDepth).backward.map name

def targetPositiveSetoid (Target : PresentedDyadicCompletionObject) : PositiveSetoid where
  Carrier := Target.core.Carrier
  Equivalent := Target.core.Equivalent
  equivalentRefl := Target.core.equivalentRefl
  equivalentSymm := Target.core.equivalentSymm
  equivalentTrans := Target.core.equivalentTrans

def DescendedComparison {Y : PositiveSetoid} (f : RegularDyadicName → Y.Carrier)
    (value : Value) (y : Y.Carrier) : Type _ := ClassDescent f value y

/-- The entire completion structure is carried by the sole pullback field. -/
structure RelationalCompletionMorphism (Target : PresentedDyadicCompletionObject) where
  pullback : CompletionMorphism conventionalCompletionObject Target

namespace RelationalCompletionMorphism

def Graph {Target : PresentedDyadicCompletionObject} (M : RelationalCompletionMorphism Target)
    (value : Value) (y : Target.core.Carrier) : Type :=
  DescendedComparison (Y := targetPositiveSetoid Target) M.pullback.map value y

def underlying {Target : PresentedDyadicCompletionObject} (M : RelationalCompletionMorphism Target) :
    RelationalMorphism ValuePositiveSetoid (targetPositiveSetoid Target) :=
  classDescent M.pullback.map M.pullback.mapEquivalent

def unique {Target : PresentedDyadicCompletionObject} (F G : RelationalCompletionMorphism Target) :
    RelationalMorphism.PointwiseEquivalent F.underlying G.underlying :=
  fun value y z first second =>
    Target.core.equivalentTrans (Target.core.equivalentSymm first.agrees)
      (Target.core.equivalentTrans (F.pullback.mapEquivalent (value.coherent first.member second.member))
        (Target.core.equivalentTrans (morphismsPointwiseEquivalent F.pullback G.pullback second.name) second.agrees))

def onClass {Target : PresentedDyadicCompletionObject} (M : RelationalCompletionMorphism Target)
    {name : RegularDyadicName} {y : Target.core.Carrier} (graph : M.Graph (classOf name) y) :
    Target.core.Equivalent (M.pullback.map name) y :=
  classDescentOnClass (Y := targetPositiveSetoid Target) M.pullback.mapEquivalent graph

def onClassBack {Target : PresentedDyadicCompletionObject} (M : RelationalCompletionMorphism Target)
    {name : RegularDyadicName} {y : Target.core.Carrier}
    (same : Target.core.Equivalent (M.pullback.map name) y) : M.Graph (classOf name) y :=
  classDescentOnClassBack same

def dyadic {Target : PresentedDyadicCompletionObject} (M : RelationalCompletionMorphism Target)
    (code : SignedDyadicCode) : M.Graph (dyadicValue code) (Target.core.dyadic code) :=
  ⟨RegularDyadicName.constantName code, classOfContains _, M.pullback.mapDyadic code⟩

def producedLimit {Target : PresentedDyadicCompletionObject} (M : RelationalCompletionMorphism Target)
    (family : PresentedFamily regularPresentedCore) :
    M.Graph (classOf (regularPresentedCompletion.complete family).value)
      (Target.completion.complete (diagonalTransportFamily regularPresentedCore Target.core family)).value :=
  ⟨(regularPresentedCompletion.complete family).value, classOfContains _, mapProducedLimit M.pullback family⟩

end RelationalCompletionMorphism

def relationalCompletionComparison (Target : PresentedDyadicCompletionObject) : RelationalCompletionMorphism Target :=
  ⟨comparisonMorphism conventionalCompletionObject Target⟩

def carrierPositiveSetoid (P : CircularPresentation) (baseDepth : Nat) : PositiveSetoid :=
  targetPositiveSetoid (carrierCompletionObject P baseDepth)

def Realizes (P : CircularPresentation) (baseDepth : Nat)
    (carrier : EffectiveCauchyReal.Carrier) (value : Value) : Type :=
  DescendedComparison (Y := carrierPositiveSetoid P baseDepth)
    (referenceNameToCarrier P baseDepth) value carrier

variable {P : CircularPresentation} {baseDepth : Nat}

def realizationMorphism (P : CircularPresentation) (baseDepth : Nat) :
    RelationalMorphism ValuePositiveSetoid (carrierPositiveSetoid P baseDepth) :=
  classDescent (referenceNameToCarrier P baseDepth) (regularCharacterization P baseDepth).backward.mapEquivalent

def carrierCoverage (P : CircularPresentation) (baseDepth : Nat) (carrier : EffectiveCauchyReal.Carrier) :
    Σ value : Value, Realizes P baseDepth carrier value :=
  let name := carrierToReferenceName P baseDepth carrier
  ⟨classOf name, ⟨name, classOfContains name, (regularCharacterization P baseDepth).carrierReturn carrier⟩⟩

theorem relationalCoverage (P : CircularPresentation) (baseDepth : Nat) (value : Value) :
    Nonempty (Σ carrier : EffectiveCauchyReal.Carrier, Realizes P baseDepth carrier value) :=
  (realizationMorphism P baseDepth).total value

def realizesStableValue {carrier : EffectiveCauchyReal.Carrier} {x y : Value}
    (same : ExternalEquivalent x y) (realized : Realizes P baseDepth carrier x) : Realizes P baseDepth carrier y :=
  ⟨realized.name, same.forward _ realized.member, realized.agrees⟩

def realizesStableCarrier {first second : EffectiveCauchyReal.Carrier} {value : Value}
    (same : EffectiveCauchyReal.Equivalent first second) (realized : Realizes P baseDepth first value) :
    Realizes P baseDepth second value :=
  ⟨realized.name, realized.member, realized.agrees.trans same⟩

def realizesCorrect {first second : EffectiveCauchyReal.Carrier} {x y : Value}
    (same : EffectiveCauchyReal.Equivalent first second)
    (left : Realizes P baseDepth first x) (right : Realizes P baseDepth second y) : ExternalEquivalent x y :=
  referenceCorrect ((regularCharacterization P baseDepth).backwardTransports.equivalentReflection
    (left.agrees.trans (same.trans right.agrees.symm))) left.member right.member

def realizesFaithful {first second : EffectiveCauchyReal.Carrier} {x y : Value}
    (same : ExternalEquivalent x y)
    (left : Realizes P baseDepth first x) (right : Realizes P baseDepth second y) :
    EffectiveCauchyReal.Equivalent first second :=
  left.agrees.symm.trans (((regularCharacterization P baseDepth).backward.mapEquivalent
    (y.coherent (same.forward _ left.member) right.member)).trans right.agrees)

def realizesDyadic (P : CircularPresentation) (baseDepth : Nat) (code : SignedDyadicCode) :
    Realizes P baseDepth (dyadicCarrier code) (dyadicValue code) :=
  ⟨RegularDyadicName.constantName code, classOfContains _,
    (regularCharacterization P baseDepth).backward.mapDyadic code⟩

def realizesZero (P : CircularPresentation) (baseDepth : Nat) :
    Realizes P baseDepth canonicalZeroCarrier ExtensiveCauchyReal.zero := realizesDyadic P baseDepth _
def realizesOne (P : CircularPresentation) (baseDepth : Nat) :
    Realizes P baseDepth canonicalOneCarrier ExtensiveCauchyReal.one := realizesDyadic P baseDepth _

def realizesAdd {a b : EffectiveCauchyReal.Carrier} {x y : Value}
    (left : Realizes P baseDepth a x) (right : Realizes P baseDepth b y) :
    Realizes P baseDepth (addCarrier a b) (addValue x y) :=
  ⟨RegularDyadicName.addName left.name right.name, addMember left.member right.member,
    ((regularCharacterization P baseDepth).backwardTransports.add left.name right.name).trans
      (addCarrierCongr left.agrees right.agrees)⟩

def realizesNeg {a : EffectiveCauchyReal.Carrier} {x : Value} (source : Realizes P baseDepth a x) :
    Realizes P baseDepth (negCarrier a) (negValue x) :=
  ⟨RegularDyadicName.negName source.name, negMember source.member,
    ((regularCharacterization P baseDepth).backwardTransports.neg source.name).trans
      (negCarrierCongr source.agrees)⟩

def realizesMul {a b : EffectiveCauchyReal.Carrier} {x y : Value}
    (left : Realizes P baseDepth a x) (right : Realizes P baseDepth b y) :
    Realizes P baseDepth (mulCarrier a b) (mulValue x y) :=
  ⟨RegularDyadicName.mulName left.name right.name, mulMember left.member right.member,
    ((regularCharacterization P baseDepth).backwardTransports.mul left.name right.name).trans
      (mulCarrierCongr left.agrees right.agrees)⟩

def realizesOrder {a b : EffectiveCauchyReal.Carrier} {x y : Value}
    (left : Realizes P baseDepth a x) (right : Realizes P baseDepth b y) (order : CarrierOrder a b) :
    ExternalOrder x y :=
  externalOrderFromMembers left.member right.member
    ((regularCharacterization P baseDepth).backwardTransports.orderReflection
      (transportCarrierOrder order left.agrees.symm right.agrees.symm))

def realizesOrderReflect {a b : EffectiveCauchyReal.Carrier} {x y : Value}
    (left : Realizes P baseDepth a x) (right : Realizes P baseDepth b y) (order : ExternalOrder x y) :
    CarrierOrder a b :=
  transportCarrierOrder ((regularCharacterization P baseDepth).backwardTransports.orderPreservation
    (externalOrderToNames order left.member right.member)) left.agrees right.agrees

def realizesApartness {a b : EffectiveCauchyReal.Carrier} {x y : Value}
    (left : Realizes P baseDepth a x) (right : Realizes P baseDepth b y) (apart : CarrierApartness a b) :
    ExternalApartness x y :=
  match apart with
  | .inl order => .inl (realizesOrder left right order)
  | .inr order => .inr (realizesOrder right left order)

def realizesApartnessReflect {a b : EffectiveCauchyReal.Carrier} {x y : Value}
    (left : Realizes P baseDepth a x) (right : Realizes P baseDepth b y) (apart : ExternalApartness x y) :
    CarrierApartness a b :=
  match apart with
  | .inl order => .inl (realizesOrderReflect left right order)
  | .inr order => .inr (realizesOrderReflect right left order)

/-- The same external reciprocal candidate is compared by its unit law. -/
def realizesInverseOfUnit {a b : EffectiveCauchyReal.Carrier} {x : Value}
    (source : Realizes P baseDepth a x) (witness : ExternalApartness x ExtensiveCauchyReal.zero)
    (unit : EffectiveCauchyReal.Equivalent (mulCarrier a b) canonicalOneCarrier) :
    Realizes P baseDepth b (externalInverse x witness) := by
  let produced := externalInversePresentation witness
  let candidate := reciprocalName produced.name produced.domain
  let comparison := (regularCharacterization P baseDepth).backward
  let transports := (regularCharacterization P baseDepth).backwardTransports
  have sourceAgrees : EffectiveCauchyReal.Equivalent (comparison.map produced.name) a :=
    (comparison.mapEquivalent (x.coherent produced.member source.member)).trans source.agrees
  have candidateUnit : EffectiveCauchyReal.Equivalent
      (mulCarrier a (comparison.map candidate)) canonicalOneCarrier :=
    (mulCarrierCongr sourceAgrees.symm (.refl _)).trans
      ((transports.mul produced.name candidate).symm.trans
        ((comparison.mapEquivalent (reciprocalNameUnitRight produced.name produced.domain)).trans transports.one))
  have suppliedLeftUnit := ((carrierMultiplicativeLaws P baseDepth).mulComm b a).trans unit
  exact ⟨candidate, classOfContains _, carrierInverseUnique P baseDepth candidateUnit suppliedLeftUnit⟩

def realizesInverse {a : EffectiveCauchyReal.Carrier} {x : Value}
    (source : Realizes P baseDepth a x) (domain : CanonicalCarrierDomain a)
    (witness : ExternalApartness x ExtensiveCauchyReal.zero) :
    Realizes P baseDepth (carrierInverse P baseDepth a domain) (externalInverse x witness) :=
  realizesInverseOfUnit source witness (carrierInverseUnitRight P baseDepth a domain)

def realizesInverseReflect {a : EffectiveCauchyReal.Carrier} {x y : Value}
    (source : Realizes P baseDepth a x) (domain : CanonicalCarrierDomain a)
    (witness : ExternalApartness x ExtensiveCauchyReal.zero)
    (output : Realizes P baseDepth (carrierInverse P baseDepth a domain) y) :
    ExternalEquivalent (externalInverse x witness) y :=
  realizesCorrect (.refl _) (realizesInverse source domain witness) output

def realizesAddReflect {a b : EffectiveCauchyReal.Carrier} {x y z : Value}
    (left : Realizes P baseDepth a x) (right : Realizes P baseDepth b y)
    (output : Realizes P baseDepth (addCarrier a b) z) : ExternalEquivalent (addValue x y) z :=
  realizesCorrect (.refl _) (realizesAdd left right) output

def realizesMulReflect {a b : EffectiveCauchyReal.Carrier} {x y z : Value}
    (left : Realizes P baseDepth a x) (right : Realizes P baseDepth b y)
    (output : Realizes P baseDepth (mulCarrier a b) z) : ExternalEquivalent (mulValue x y) z :=
  realizesCorrect (.refl _) (realizesMul left right) output

def realizesNegReflect {a : EffectiveCauchyReal.Carrier} {x y : Value}
    (source : Realizes P baseDepth a x) (output : Realizes P baseDepth (negCarrier a) y) :
    ExternalEquivalent (negValue x) y := realizesCorrect (.refl _) (realizesNeg source) output

def realizesDensity {a b : EffectiveCauchyReal.Carrier} {x y : Value}
    (left : Realizes P baseDepth a x) (right : Realizes P baseDepth b y)
    (witness : PresentedDensityWitness carrierPresentedCore CarrierOrder a b) : ExternalDensityWitness x y :=
  ⟨witness.1, realizesOrder left (realizesDyadic P baseDepth witness.1) witness.2.1,
    realizesOrder (realizesDyadic P baseDepth witness.1) right witness.2.2⟩

def realizesDensityReflect {a b : EffectiveCauchyReal.Carrier} {x y : Value}
    (left : Realizes P baseDepth a x) (right : Realizes P baseDepth b y)
    (witness : ExternalDensityWitness x y) : PresentedDensityWitness carrierPresentedCore CarrierOrder a b :=
  ⟨witness.code, realizesOrderReflect left (realizesDyadic P baseDepth _) witness.left,
    realizesOrderReflect (realizesDyadic P baseDepth _) right witness.right⟩

def realizesBounds {a : EffectiveCauchyReal.Carrier} {x : Value} (source : Realizes P baseDepth a x)
    (witness : PresentedNaturalBoundsWitness carrierPresentedCore CarrierOrder a) : ExternalNaturalBounds x :=
  ⟨witness.1, witness.2.1, realizesOrder (realizesDyadic P baseDepth _) source witness.2.2.1,
    realizesOrder source (realizesDyadic P baseDepth _) witness.2.2.2⟩

def realizesBoundsReflect {a : EffectiveCauchyReal.Carrier} {x : Value} (source : Realizes P baseDepth a x)
    (witness : ExternalNaturalBounds x) : PresentedNaturalBoundsWitness carrierPresentedCore CarrierOrder a :=
  ⟨witness.lower, witness.upper, realizesOrderReflect (realizesDyadic P baseDepth _) source witness.lowerOrder,
    realizesOrderReflect source (realizesDyadic P baseDepth _) witness.upperOrder⟩

def realizesProducedDensity {a b : EffectiveCauchyReal.Carrier} {x y : Value}
    (left : Realizes P baseDepth a x) (right : Realizes P baseDepth b y) {origin : CarrierOrder a b}
    (produced : CarrierDensityResult P baseDepth a b origin) : ExternalDensityWitness x y :=
  realizesDensity left right ⟨produced.code, produced.left, produced.right⟩

def realizesProducedBounds {a : EffectiveCauchyReal.Carrier} {x : Value} (source : Realizes P baseDepth a x)
    (produced : CarrierNaturalBoundResult P baseDepth a) : ExternalNaturalBounds x :=
  realizesBounds source ⟨produced.lower, produced.upper, produced.lowerOrder, produced.upperOrder⟩

theorem realizesDensityCodeExact {a b : EffectiveCauchyReal.Carrier} {x y : Value}
    (left : Realizes P baseDepth a x) (right : Realizes P baseDepth b y)
    (witness : PresentedDensityWitness carrierPresentedCore CarrierOrder a b) :
    (realizesDensity left right witness).code = witness.1 := rfl

theorem realizesBoundsReadoutExact {a : EffectiveCauchyReal.Carrier} {x : Value}
    (source : Realizes P baseDepth a x) (witness : PresentedNaturalBoundsWitness carrierPresentedCore CarrierOrder a) :
    (realizesBounds source witness).lower = witness.1 ∧
      (realizesBounds source witness).upper = witness.2.1 := ⟨rfl, rfl⟩

theorem realizesProducedDensityCodeExact {a b : EffectiveCauchyReal.Carrier} {x y : Value}
    (left : Realizes P baseDepth a x) (right : Realizes P baseDepth b y) {origin : CarrierOrder a b}
    (produced : CarrierDensityResult P baseDepth a b origin) :
    (realizesProducedDensity left right produced).code = produced.code := rfl

theorem realizesProducedBoundsReadoutExact {a : EffectiveCauchyReal.Carrier} {x : Value}
    (source : Realizes P baseDepth a x) (produced : CarrierNaturalBoundResult P baseDepth a) :
    (realizesProducedBounds source produced).lower = produced.lower ∧
      (realizesProducedBounds source produced).upper = produced.upper := ⟨rfl, rfl⟩

/-- This is the forward map's actual approximation, not a new name adapter. -/
def carrierToNameSameValue (P : CircularPresentation) (baseDepth : Nat)
    (carrier : EffectiveCauchyReal.Carrier) (p : Nat) :
    SameValue ((carrierToReferenceName P baseDepth carrier).approximation p)
      (carrier.approximation (carrier.modulus p)) := constantNameSameValue _ p

def carrierExternalFamily (P : CircularPresentation) (baseDepth : Nat) (family : CarrierFamily) :
    ExternalPresentedFamily where
  terms n := (carrierCoverage P baseDepth (family.terms n)).1
  name n := carrierToReferenceName P baseDepth (family.terms n)
  member n := classOfContains _
  modulus := family.modulus
  modulusMonotone := family.modulusMonotone
  cauchy p n m r s hn hm hr hs := Near.ofSameLeft (carrierToNameSameValue P baseDepth _ r)
    (Near.ofSameRight (family.cauchy p n m _ _ hn hm
      ((family.terms n).modulusMonotone hr) ((family.terms m).modulusMonotone hs))
      (carrierToNameSameValue P baseDepth _ s).symm)

def carrierExternalTermRealizes (P : CircularPresentation) (baseDepth : Nat) (family : CarrierFamily) (n : Nat) :
    Realizes P baseDepth (family.terms n) ((carrierExternalFamily P baseDepth family).terms n) :=
  (carrierCoverage P baseDepth (family.terms n)).2

def externalConvergenceToCarrier (P : CircularPresentation) (baseDepth : Nat) {family : CarrierFamily}
    {value : Value} (convergence : ExternalConverges (carrierExternalFamily P baseDepth family) value) :
    CarrierLimit family (referenceNameToCarrier P baseDepth convergence.candidateName) where
  threshold := convergence.threshold
  converges p n r s hn hr hs := Near.ofSameLeft (carrierToNameSameValue P baseDepth _ r).symm
    (convergence.near p n r s hn hr hs)

/-- Compare two already produced limits, retaining the external candidate. -/
def realizesCarrierProducedLimit (P : CircularPresentation) (baseDepth : Nat) (family : CarrierFamily)
    (carrierProduced : CarrierCompletionResult P baseDepth family)
    (externalProduced : ExternalLimitResult (carrierExternalFamily P baseDepth family)) :
    Realizes P baseDepth carrierProduced.limit externalProduced.value :=
  ⟨externalProduced.convergence.candidateName, externalProduced.convergence.candidateMember,
    (carrierProduced.uniqueness _ (externalConvergenceToCarrier P baseDepth externalProduced.convergence)).symm⟩

/-- The reverse limit transport is precisely the one derived in Gate 7.3.
Its target family is explicitly diagonalized, with its changed modulus. -/
def realizesExternalProducedLimit (P : CircularPresentation) (baseDepth : Nat) (family : ExternalPresentedFamily) :
    Realizes P baseDepth
      ((carrierCompletionStructure P baseDepth).complete
        (diagonalTransportFamily regularPresentedCore carrierPresentedCore (referenceFamily family))).value
      (externalComplete family).value :=
  ⟨(externalComplete family).convergence.candidateName, (externalComplete family).convergence.candidateMember,
    (regularCharacterization P baseDepth).backwardLimit (referenceFamily family)⟩

def RuntimeRealizes (P : CircularPresentation) (baseDepth : Nat)
    (runtime : Real P baseDepth) (value : Value) : Type :=
  Realizes P baseDepth (toCarrier runtime) value

def runtimeCoverage (P : CircularPresentation) (baseDepth : Nat) (runtime : Real P baseDepth) :
    Σ value : Value, RuntimeRealizes P baseDepth runtime value :=
  carrierCoverage P baseDepth (toCarrier runtime)

theorem valueRuntimeCoverage (P : CircularPresentation) (baseDepth : Nat) (value : Value) :
    Nonempty (Σ runtime : Real P baseDepth, RuntimeRealizes P baseDepth runtime value) := by
  obtain ⟨⟨carrier, realization⟩⟩ := relationalCoverage P baseDepth value
  exact ⟨⟨ofCarrier P baseDepth carrier,
    ⟨realization.name, realization.member, realization.agrees.trans (carrier_roundtrip carrier).symm⟩⟩⟩

def runtimeOfReferenceName (P : CircularPresentation) (baseDepth : Nat) (name : RegularDyadicName) :
    Real P baseDepth := ofCarrier P baseDepth (referenceNameToCarrier P baseDepth name)

def runtimeOfReferenceNameRealizes (P : CircularPresentation) (baseDepth : Nat) (name : RegularDyadicName) :
    RuntimeRealizes P baseDepth (runtimeOfReferenceName P baseDepth name) (classOf name) :=
  ⟨name, classOfContains name, (carrier_roundtrip _).symm⟩

def runtimeCorrect {first second : Real P baseDepth} {x y : Value}
    (same : Equivalent first second) (left : RuntimeRealizes P baseDepth first x)
    (right : RuntimeRealizes P baseDepth second y) : ExternalEquivalent x y :=
  realizesCorrect ((equivalentCarrier first second).1 same) left right

def runtimeFaithful {first second : Real P baseDepth} {x y : Value}
    (same : ExternalEquivalent x y) (left : RuntimeRealizes P baseDepth first x)
    (right : RuntimeRealizes P baseDepth second y) : Equivalent first second :=
  (equivalentCarrier first second).2 (realizesFaithful same left right)

def runtimeRealizesDyadic (P : CircularPresentation) (baseDepth : Nat) (code : SignedDyadicCode) :
    RuntimeRealizes P baseDepth (.leaf (RuntimeCorrespondence.constantRuntime P baseDepth code)) (dyadicValue code) :=
  realizesStableCarrier (carrierReadoutConstant P baseDepth code).symm (realizesDyadic P baseDepth code)

def runtimeRealizesAdd {a b : Real P baseDepth} {x y : Value}
    (left : RuntimeRealizes P baseDepth a x) (right : RuntimeRealizes P baseDepth b y) :
    RuntimeRealizes P baseDepth (.add a b) (addValue x y) :=
  realizesStableCarrier (toCarrier_add a b).symm (realizesAdd left right)

def runtimeRealizesNeg {a : Real P baseDepth} {x : Value} (source : RuntimeRealizes P baseDepth a x) :
    RuntimeRealizes P baseDepth (.neg a) (negValue x) :=
  realizesStableCarrier (toCarrier_neg a).symm (realizesNeg source)

def runtimeRealizesMul {a b : Real P baseDepth} {x y : Value}
    (left : RuntimeRealizes P baseDepth a x) (right : RuntimeRealizes P baseDepth b y) :
    RuntimeRealizes P baseDepth (.mul a b) (mulValue x y) :=
  realizesStableCarrier (toCarrier_mul a b).symm (realizesMul left right)

def runtimeRealizesInverse {a : Real P baseDepth} {x : Value} (source : RuntimeRealizes P baseDepth a x)
    (domain : RelationalRealOrder.Apartness a (RelationalRealAddition.zero P baseDepth))
    (witness : ExternalApartness x ExtensiveCauchyReal.zero) :
    RuntimeRealizes P baseDepth (RelationalRealInverse.inverse a domain) (externalInverse x witness) :=
  realizesInverseOfUnit source witness (carrierReadoutLaw (RelationalRealInverse.mul_inverse a domain)
    (carrierReadoutMul (.refl _) (.refl _)) (carrierReadoutConstant P baseDepth SignedDyadicCode.one))

def runtimeRealizesAddReflect {a b : Real P baseDepth} {x y z : Value}
    (left : RuntimeRealizes P baseDepth a x) (right : RuntimeRealizes P baseDepth b y)
    (output : RuntimeRealizes P baseDepth (.add a b) z) : ExternalEquivalent (addValue x y) z :=
  runtimeCorrect (.refl _) (runtimeRealizesAdd left right) output

def runtimeRealizesNegReflect {a : Real P baseDepth} {x y : Value}
    (source : RuntimeRealizes P baseDepth a x) (output : RuntimeRealizes P baseDepth (.neg a) y) :
    ExternalEquivalent (negValue x) y := runtimeCorrect (.refl _) (runtimeRealizesNeg source) output

def runtimeRealizesMulReflect {a b : Real P baseDepth} {x y z : Value}
    (left : RuntimeRealizes P baseDepth a x) (right : RuntimeRealizes P baseDepth b y)
    (output : RuntimeRealizes P baseDepth (.mul a b) z) : ExternalEquivalent (mulValue x y) z :=
  runtimeCorrect (.refl _) (runtimeRealizesMul left right) output

def runtimeRealizesInverseReflect {a : Real P baseDepth} {x y : Value}
    (source : RuntimeRealizes P baseDepth a x)
    (domain : RelationalRealOrder.Apartness a (RelationalRealAddition.zero P baseDepth))
    (witness : ExternalApartness x ExtensiveCauchyReal.zero)
    (output : RuntimeRealizes P baseDepth (RelationalRealInverse.inverse a domain) y) :
    ExternalEquivalent (externalInverse x witness) y :=
  runtimeCorrect (.refl _) (runtimeRealizesInverse source domain witness) output

def runtimeRealizesOrder {a b : Real P baseDepth} {x y : Value}
    (left : RuntimeRealizes P baseDepth a x) (right : RuntimeRealizes P baseDepth b y) (order : StrictOrder a b) :
    ExternalOrder x y := realizesOrder left right order.toCarrier

def runtimeRealizesOrderReflect {a b : Real P baseDepth} {x y : Value}
    (left : RuntimeRealizes P baseDepth a x) (right : RuntimeRealizes P baseDepth b y) (order : ExternalOrder x y) :
    StrictOrder a b := realizeCarrierOrderOn (realizesOrderReflect left right order) (.refl _) (.refl _)

def runtimeRealizesApartness {a b : Real P baseDepth} {x y : Value}
    (left : RuntimeRealizes P baseDepth a x) (right : RuntimeRealizes P baseDepth b y)
    (apart : RelationalRealOrder.Apartness a b) : ExternalApartness x y :=
  realizesApartness left right apart.toCarrier

def runtimeRealizesApartnessReflect {a b : Real P baseDepth} {x y : Value}
    (left : RuntimeRealizes P baseDepth a x) (right : RuntimeRealizes P baseDepth b y)
    (apart : ExternalApartness x y) : RelationalRealOrder.Apartness a b :=
  match apart with
  | .inl order => .forward (runtimeRealizesOrderReflect left right order)
  | .inr order => .backward (runtimeRealizesOrderReflect right left order)

def runtimeDensityFromProduction {a b : Real P baseDepth} {x y : Value}
    (left : RuntimeRealizes P baseDepth a x) (right : RuntimeRealizes P baseDepth b y)
    {origin : StrictOrder a b} {journal : ConstitutiveRuntime.Journal P baseDepth}
    (produced : RelationalRealDensity.Density origin journal) : ExternalDensityWitness x y := by
  have target : RuntimeRealizes P baseDepth produced.target (dyadicValue produced.action.readout) := by
    rw [produced.targetExact]
    exact runtimeRealizesDyadic P baseDepth _
  exact ⟨produced.action.readout, runtimeRealizesOrder left target produced.orders.1,
    runtimeRealizesOrder target right produced.orders.2⟩

def runtimeBoundsFromProduction {source : Real P baseDepth} {x : Value}
    (realized : RuntimeRealizes P baseDepth source x)
    {archive : (environment source).Archive} {journal : ConstitutiveRuntime.Journal P baseDepth}
    (produced : RelationalRealDensity.NaturalBound source archive journal) : ExternalNaturalBounds x := by
  have lower : RuntimeRealizes P baseDepth produced.lowerTarget
      (negativeNaturalValue produced.action.stored.value.lower) := by
    rw [produced.lowerExact]
    exact runtimeRealizesDyadic P baseDepth _
  have upper : RuntimeRealizes P baseDepth produced.upperTarget
      (naturalValue produced.action.stored.value.upper) := by
    rw [produced.upperExact]
    exact runtimeRealizesDyadic P baseDepth _
  exact ⟨produced.action.stored.value.lower, produced.action.stored.value.upper,
    runtimeRealizesOrder lower realized produced.orders.1, runtimeRealizesOrder realized upper produced.orders.2⟩

def runtimeDensityReflect {a b : Real P baseDepth} {x y : Value}
    (left : RuntimeRealizes P baseDepth a x) (right : RuntimeRealizes P baseDepth b y)
    (witness : ExternalDensityWitness x y) :
    Σ code : SignedDyadicCode, StrictOrder a (RelationalRealDensity.dyadic P baseDepth code) ×
      StrictOrder (RelationalRealDensity.dyadic P baseDepth code) b :=
  ⟨witness.code, runtimeRealizesOrderReflect left (runtimeRealizesDyadic P baseDepth _) witness.left,
    runtimeRealizesOrderReflect (runtimeRealizesDyadic P baseDepth _) right witness.right⟩

def runtimeBoundsReflect {source : Real P baseDepth} {x : Value}
    (realized : RuntimeRealizes P baseDepth source x) (witness : ExternalNaturalBounds x) :
    Σ lower upper : Nat,
      StrictOrder (RelationalRealDensity.dyadic P baseDepth (DyadicDensity.negativeNaturalCode lower)) source ×
      StrictOrder source (RelationalRealDensity.dyadic P baseDepth (DyadicDensity.naturalCode upper)) :=
  ⟨witness.lower, witness.upper,
    runtimeRealizesOrderReflect (runtimeRealizesDyadic P baseDepth _) realized witness.lowerOrder,
    runtimeRealizesOrderReflect realized (runtimeRealizesDyadic P baseDepth _) witness.upperOrder⟩

theorem runtimeDensityCodeExact {a b : Real P baseDepth} {x y : Value}
    (left : RuntimeRealizes P baseDepth a x) (right : RuntimeRealizes P baseDepth b y)
    {origin : StrictOrder a b} {journal : ConstitutiveRuntime.Journal P baseDepth}
    (produced : RelationalRealDensity.Density origin journal) :
    (runtimeDensityFromProduction left right produced).code = produced.action.readout := rfl

theorem runtimeBoundsReadoutExact {source : Real P baseDepth} {x : Value}
    (realized : RuntimeRealizes P baseDepth source x)
    {archive : (environment source).Archive} {journal : ConstitutiveRuntime.Journal P baseDepth}
    (produced : RelationalRealDensity.NaturalBound source archive journal) :
    (runtimeBoundsFromProduction realized produced).lower = produced.action.stored.value.lower ∧
      (runtimeBoundsFromProduction realized produced).upper = produced.action.stored.value.upper := ⟨rfl, rfl⟩

def runtimeProducedLimitRealizes (P : CircularPresentation) (baseDepth : Nat) (family : CarrierFamily)
    (carrierProduced : CarrierCompletionResult P baseDepth family)
    (externalProduced : ExternalLimitResult (carrierExternalFamily P baseDepth family)) :
    RuntimeRealizes P baseDepth carrierProduced.native.limit externalProduced.value := by
  have realized := realizesCarrierProducedLimit P baseDepth family carrierProduced externalProduced
  rw [carrierProduced.limitExact] at realized
  exact realized

theorem referenceMapPerimeterIndependent (P Q : CircularPresentation) (d e : Nat) (name : RegularDyadicName)
    (response : Nat) :
    (referenceNameToCarrier P d name).approximation response =
      (referenceNameToCarrier Q e name).approximation response := rfl

theorem carrierReadoutPerimeterIndependent (P Q : CircularPresentation) (d e : Nat)
    (carrier : EffectiveCauchyReal.Carrier) (response : Nat) :
    (carrierToReferenceName P d carrier).approximation response =
      (carrierToReferenceName Q e carrier).approximation response := rfl

section RecognitionPackaging
attribute [local irreducible] referenceNameToCarrier
universe u v g

structure QuotientRecognition where
  coverage : (name : RegularDyadicName) → Σ value : Value, ReferenceRealizes name value
  valueCoverage : (value : Value) → Nonempty (Σ name : RegularDyadicName, ReferenceRealizes name value)
  preserves : {a b : RegularDyadicName} → NameEquivalent a b → ExternalEquivalent (classOf a) (classOf b)
  reflects : {a b : RegularDyadicName} → ExternalEquivalent (classOf a) (classOf b) → NameEquivalent a b
  classCoverage : (value : Value) → Nonempty (Σ name, ExternalEquivalent (classOf name) value)
  extension : {Y : PositiveSetoid.{u,v}} → (f : RegularDyadicName → Y.Carrier) →
    (respects : RespectsNameEquivalent (Y := Y) f) → ExtendsNameMap (Y := Y) f (classDescent f respects)
  uniqueness : {Y : PositiveSetoid.{u,v}} → (f : RegularDyadicName → Y.Carrier) →
    (respects : RespectsNameEquivalent (Y := Y) f) → (M : RelationalMorphism.{1,0,u,v,g} ValuePositiveSetoid Y) →
    ExtendsNameMap (Y := Y) f M → RelationalMorphism.PointwiseEquivalent (classDescent f respects) M

def quotientRecognition : QuotientRecognition.{u,v,g} where
  coverage := ExtensiveCauchyReal.referenceCoverage
  valueCoverage := ExtensiveCauchyReal.valueReferenceCoverage
  preserves := classOfPreserves
  reflects := classOfReflects
  classCoverage := classOfSurjective
  extension := classDescentExtends
  uniqueness f respects M extension := classDescentUnique respects M extension

structure CompletionRecognition where
  complete : (family : PresentedFamily regularPresentedCore) → LimitResult regularPresentedCore family
  ordered : PresentedDyadicOrderedFieldData regularPresentedCore
  readout : SetoidOrderedArchimedeanReadout
  completionComparison : (Target : PresentedDyadicCompletionObject) → RelationalCompletionMorphism Target
  completionUniqueness : (Target : PresentedDyadicCompletionObject) → (F G : RelationalCompletionMorphism Target) →
    (value : Value) → (y z : Target.core.Carrier) → F.Graph value y → G.Graph value z → Target.core.Equivalent y z
  dyadicTransport : (Target : PresentedDyadicCompletionObject) → (M : RelationalCompletionMorphism Target) →
    (code : SignedDyadicCode) → M.Graph (dyadicValue code) (Target.core.dyadic code)
  limitTransport : (Target : PresentedDyadicCompletionObject) → (M : RelationalCompletionMorphism Target) →
    (family : PresentedFamily regularPresentedCore) →
      M.Graph (classOf (regularPresentedCompletion.complete family).value)
        (Target.completion.complete (diagonalTransportFamily regularPresentedCore Target.core family)).value

def completionRecognition : CompletionRecognition where
  complete := regularPresentedCompletion.complete
  ordered := regularOrderedData
  readout := setoidOrderedArchimedeanReadout
  completionComparison := relationalCompletionComparison
  completionUniqueness := fun _ => RelationalCompletionMorphism.unique
  dyadicTransport := fun _ => RelationalCompletionMorphism.dyadic
  limitTransport := fun _ => RelationalCompletionMorphism.producedLimit

structure CarrierValueCorrespondence (P : CircularPresentation) (baseDepth : Nat) where
  carrierCoverage : (carrier : EffectiveCauchyReal.Carrier) → Σ value : Value, Realizes P baseDepth carrier value
  relationalCoverage : (value : Value) → Nonempty (Σ carrier : EffectiveCauchyReal.Carrier, Realizes P baseDepth carrier value)
  correct : {a b : EffectiveCauchyReal.Carrier} → {x y : Value} → EffectiveCauchyReal.Equivalent a b →
    Realizes P baseDepth a x → Realizes P baseDepth b y → ExternalEquivalent x y
  faithful : {a b : EffectiveCauchyReal.Carrier} → {x y : Value} → ExternalEquivalent x y →
    Realizes P baseDepth a x → Realizes P baseDepth b y → EffectiveCauchyReal.Equivalent a b
  dyadic : (code : SignedDyadicCode) → Realizes P baseDepth (dyadicCarrier code) (dyadicValue code)
  add : {a b : EffectiveCauchyReal.Carrier} → {x y : Value} → Realizes P baseDepth a x → Realizes P baseDepth b y →
    Realizes P baseDepth (addCarrier a b) (addValue x y)
  neg : {a : EffectiveCauchyReal.Carrier} → {x : Value} → Realizes P baseDepth a x →
    Realizes P baseDepth (negCarrier a) (negValue x)
  mul : {a b : EffectiveCauchyReal.Carrier} → {x y : Value} → Realizes P baseDepth a x → Realizes P baseDepth b y →
    Realizes P baseDepth (mulCarrier a b) (mulValue x y)
  inverse : {a : EffectiveCauchyReal.Carrier} → {x : Value} → Realizes P baseDepth a x →
    (domain : CanonicalCarrierDomain a) → (witness : ExternalApartness x ExtensiveCauchyReal.zero) →
    Realizes P baseDepth (carrierInverse P baseDepth a domain) (externalInverse x witness)
  addReflection : {a b : EffectiveCauchyReal.Carrier} → {x y z : Value} → Realizes P baseDepth a x →
    Realizes P baseDepth b y → Realizes P baseDepth (addCarrier a b) z → ExternalEquivalent (addValue x y) z
  negReflection : {a : EffectiveCauchyReal.Carrier} → {x y : Value} → Realizes P baseDepth a x →
    Realizes P baseDepth (negCarrier a) y → ExternalEquivalent (negValue x) y
  mulReflection : {a b : EffectiveCauchyReal.Carrier} → {x y z : Value} → Realizes P baseDepth a x →
    Realizes P baseDepth b y → Realizes P baseDepth (mulCarrier a b) z → ExternalEquivalent (mulValue x y) z
  inverseReflection : {a : EffectiveCauchyReal.Carrier} → {x y : Value} → Realizes P baseDepth a x →
    (domain : CanonicalCarrierDomain a) → (witness : ExternalApartness x ExtensiveCauchyReal.zero) →
    Realizes P baseDepth (carrierInverse P baseDepth a domain) y → ExternalEquivalent (externalInverse x witness) y
  order : {a b : EffectiveCauchyReal.Carrier} → {x y : Value} → Realizes P baseDepth a x → Realizes P baseDepth b y →
    CarrierOrder a b → ExternalOrder x y
  orderReflection : {a b : EffectiveCauchyReal.Carrier} → {x y : Value} → Realizes P baseDepth a x → Realizes P baseDepth b y →
    ExternalOrder x y → CarrierOrder a b
  apartness : {a b : EffectiveCauchyReal.Carrier} → {x y : Value} → Realizes P baseDepth a x → Realizes P baseDepth b y →
    CarrierApartness a b → ExternalApartness x y
  apartnessReflection : {a b : EffectiveCauchyReal.Carrier} → {x y : Value} → Realizes P baseDepth a x → Realizes P baseDepth b y →
    ExternalApartness x y → CarrierApartness a b
  density : {a b : EffectiveCauchyReal.Carrier} → {x y : Value} → Realizes P baseDepth a x → Realizes P baseDepth b y →
    PresentedDensityWitness carrierPresentedCore CarrierOrder a b → ExternalDensityWitness x y
  densityReflection : {a b : EffectiveCauchyReal.Carrier} → {x y : Value} → Realizes P baseDepth a x → Realizes P baseDepth b y →
    ExternalDensityWitness x y → PresentedDensityWitness carrierPresentedCore CarrierOrder a b
  bounds : {a : EffectiveCauchyReal.Carrier} → {x : Value} → Realizes P baseDepth a x →
    PresentedNaturalBoundsWitness carrierPresentedCore CarrierOrder a → ExternalNaturalBounds x
  boundsReflection : {a : EffectiveCauchyReal.Carrier} → {x : Value} → Realizes P baseDepth a x →
    ExternalNaturalBounds x → PresentedNaturalBoundsWitness carrierPresentedCore CarrierOrder a
  densityProduction : {a b : EffectiveCauchyReal.Carrier} → {x y : Value} → Realizes P baseDepth a x →
    Realizes P baseDepth b y → {origin : CarrierOrder a b} →
    CarrierDensityResult P baseDepth a b origin → ExternalDensityWitness x y
  densityCodeExact : {a b : EffectiveCauchyReal.Carrier} → {x y : Value} →
    (left : Realizes P baseDepth a x) → (right : Realizes P baseDepth b y) → {origin : CarrierOrder a b} →
    (produced : CarrierDensityResult P baseDepth a b origin) →
    (realizesProducedDensity left right produced).code = produced.code
  boundsProduction : {a : EffectiveCauchyReal.Carrier} → {x : Value} → Realizes P baseDepth a x →
    CarrierNaturalBoundResult P baseDepth a → ExternalNaturalBounds x
  boundsReadoutExact : {a : EffectiveCauchyReal.Carrier} → {x : Value} →
    (source : Realizes P baseDepth a x) → (produced : CarrierNaturalBoundResult P baseDepth a) →
    (realizesProducedBounds source produced).lower = produced.lower ∧
      (realizesProducedBounds source produced).upper = produced.upper
  familyTerms : (family : CarrierFamily) → (n : Nat) →
    Realizes P baseDepth (family.terms n) ((carrierExternalFamily P baseDepth family).terms n)
  producedLimit : (family : CarrierFamily) → (produced : CarrierCompletionResult P baseDepth family) →
    (externalProduced : ExternalLimitResult (carrierExternalFamily P baseDepth family)) →
    Realizes P baseDepth produced.limit externalProduced.value
  externalProducedLimit : (family : ExternalPresentedFamily) → Realizes P baseDepth
    ((carrierCompletionStructure P baseDepth).complete
      (diagonalTransportFamily regularPresentedCore carrierPresentedCore (referenceFamily family))).value
    (externalComplete family).value

def carrierValueCorrespondence (P : CircularPresentation) (baseDepth : Nat) : CarrierValueCorrespondence P baseDepth where
  carrierCoverage := carrierCoverage P baseDepth
  relationalCoverage := relationalCoverage P baseDepth
  correct := realizesCorrect
  faithful := realizesFaithful
  dyadic := realizesDyadic P baseDepth
  add := realizesAdd
  neg := realizesNeg
  mul := realizesMul
  inverse := realizesInverse
  addReflection := realizesAddReflect
  negReflection := realizesNegReflect
  mulReflection := realizesMulReflect
  inverseReflection := realizesInverseReflect
  order := realizesOrder
  orderReflection := realizesOrderReflect
  apartness := realizesApartness
  apartnessReflection := realizesApartnessReflect
  density := realizesDensity
  densityReflection := realizesDensityReflect
  bounds := realizesBounds
  boundsReflection := realizesBoundsReflect
  densityProduction := realizesProducedDensity
  densityCodeExact := realizesProducedDensityCodeExact
  boundsProduction := realizesProducedBounds
  boundsReadoutExact := realizesProducedBoundsReadoutExact
  familyTerms := carrierExternalTermRealizes P baseDepth
  producedLimit := realizesCarrierProducedLimit P baseDepth
  externalProducedLimit := realizesExternalProducedLimit P baseDepth

structure RuntimeValueCorrespondence (P : CircularPresentation) (baseDepth : Nat) where
  runtimeCoverage : (runtime : Real P baseDepth) → Σ value : Value, RuntimeRealizes P baseDepth runtime value
  valueRuntimeCoverage : (value : Value) → Nonempty (Σ runtime : Real P baseDepth, RuntimeRealizes P baseDepth runtime value)
  receivedNameRuntime : (name : RegularDyadicName) →
    RuntimeRealizes P baseDepth (runtimeOfReferenceName P baseDepth name) (classOf name)
  correct : {a b : Real P baseDepth} → {x y : Value} → Equivalent a b →
    RuntimeRealizes P baseDepth a x → RuntimeRealizes P baseDepth b y → ExternalEquivalent x y
  faithful : {a b : Real P baseDepth} → {x y : Value} → ExternalEquivalent x y →
    RuntimeRealizes P baseDepth a x → RuntimeRealizes P baseDepth b y → Equivalent a b
  dyadic : (code : SignedDyadicCode) → RuntimeRealizes P baseDepth
    (RelationalRealDensity.dyadic P baseDepth code) (dyadicValue code)
  add : {a b : Real P baseDepth} → {x y : Value} → RuntimeRealizes P baseDepth a x → RuntimeRealizes P baseDepth b y →
    RuntimeRealizes P baseDepth (.add a b) (addValue x y)
  neg : {a : Real P baseDepth} → {x : Value} → RuntimeRealizes P baseDepth a x →
    RuntimeRealizes P baseDepth (.neg a) (negValue x)
  mul : {a b : Real P baseDepth} → {x y : Value} → RuntimeRealizes P baseDepth a x → RuntimeRealizes P baseDepth b y →
    RuntimeRealizes P baseDepth (.mul a b) (mulValue x y)
  inverse : {a : Real P baseDepth} → {x : Value} → RuntimeRealizes P baseDepth a x →
    (domain : RelationalRealOrder.Apartness a (RelationalRealAddition.zero P baseDepth)) →
    (witness : ExternalApartness x ExtensiveCauchyReal.zero) →
    RuntimeRealizes P baseDepth (RelationalRealInverse.inverse a domain) (externalInverse x witness)
  addReflection : {a b : Real P baseDepth} → {x y z : Value} → RuntimeRealizes P baseDepth a x →
    RuntimeRealizes P baseDepth b y → RuntimeRealizes P baseDepth (.add a b) z → ExternalEquivalent (addValue x y) z
  negReflection : {a : Real P baseDepth} → {x y : Value} → RuntimeRealizes P baseDepth a x →
    RuntimeRealizes P baseDepth (.neg a) y → ExternalEquivalent (negValue x) y
  mulReflection : {a b : Real P baseDepth} → {x y z : Value} → RuntimeRealizes P baseDepth a x →
    RuntimeRealizes P baseDepth b y → RuntimeRealizes P baseDepth (.mul a b) z → ExternalEquivalent (mulValue x y) z
  inverseReflection : {a : Real P baseDepth} → {x y : Value} → RuntimeRealizes P baseDepth a x →
    (domain : RelationalRealOrder.Apartness a (RelationalRealAddition.zero P baseDepth)) →
    (witness : ExternalApartness x ExtensiveCauchyReal.zero) →
    RuntimeRealizes P baseDepth (RelationalRealInverse.inverse a domain) y → ExternalEquivalent (externalInverse x witness) y
  order : {a b : Real P baseDepth} → {x y : Value} → RuntimeRealizes P baseDepth a x → RuntimeRealizes P baseDepth b y →
    StrictOrder a b → ExternalOrder x y
  orderReflection : {a b : Real P baseDepth} → {x y : Value} → RuntimeRealizes P baseDepth a x → RuntimeRealizes P baseDepth b y →
    ExternalOrder x y → StrictOrder a b
  apartness : {a b : Real P baseDepth} → {x y : Value} → RuntimeRealizes P baseDepth a x → RuntimeRealizes P baseDepth b y →
    RelationalRealOrder.Apartness a b → ExternalApartness x y
  apartnessReflection : {a b : Real P baseDepth} → {x y : Value} → RuntimeRealizes P baseDepth a x → RuntimeRealizes P baseDepth b y →
    ExternalApartness x y → RelationalRealOrder.Apartness a b
  densityProduction : {a b : Real P baseDepth} → {x y : Value} →
    RuntimeRealizes P baseDepth a x → RuntimeRealizes P baseDepth b y → {origin : StrictOrder a b} →
    {journal : ConstitutiveRuntime.Journal P baseDepth} → RelationalRealDensity.Density origin journal → ExternalDensityWitness x y
  boundsProduction : {source : Real P baseDepth} → {x : Value} → RuntimeRealizes P baseDepth source x →
    {archive : (environment source).Archive} → {journal : ConstitutiveRuntime.Journal P baseDepth} →
    RelationalRealDensity.NaturalBound source archive journal → ExternalNaturalBounds x
  densityReflection : {a b : Real P baseDepth} → {x y : Value} → RuntimeRealizes P baseDepth a x →
    RuntimeRealizes P baseDepth b y → (witness : ExternalDensityWitness x y) →
    Σ code : SignedDyadicCode, StrictOrder a (RelationalRealDensity.dyadic P baseDepth code) ×
      StrictOrder (RelationalRealDensity.dyadic P baseDepth code) b
  boundsReflection : {source : Real P baseDepth} → {x : Value} → RuntimeRealizes P baseDepth source x →
    (witness : ExternalNaturalBounds x) → Σ lower upper : Nat,
      StrictOrder (RelationalRealDensity.dyadic P baseDepth (DyadicDensity.negativeNaturalCode lower)) source ×
      StrictOrder source (RelationalRealDensity.dyadic P baseDepth (DyadicDensity.naturalCode upper))
  densityCodeExact : {a b : Real P baseDepth} → {x y : Value} →
    (left : RuntimeRealizes P baseDepth a x) → (right : RuntimeRealizes P baseDepth b y) →
    {origin : StrictOrder a b} → {journal : ConstitutiveRuntime.Journal P baseDepth} →
    (produced : RelationalRealDensity.Density origin journal) →
    (runtimeDensityFromProduction left right produced).code = produced.action.readout
  boundsReadoutExact : {source : Real P baseDepth} → {x : Value} →
    (realized : RuntimeRealizes P baseDepth source x) → {archive : (environment source).Archive} →
    {journal : ConstitutiveRuntime.Journal P baseDepth} →
    (produced : RelationalRealDensity.NaturalBound source archive journal) →
    (runtimeBoundsFromProduction realized produced).lower = produced.action.stored.value.lower ∧
      (runtimeBoundsFromProduction realized produced).upper = produced.action.stored.value.upper
  producedLimit : (family : CarrierFamily) → (produced : CarrierCompletionResult P baseDepth family) →
    (externalProduced : ExternalLimitResult (carrierExternalFamily P baseDepth family)) →
    RuntimeRealizes P baseDepth produced.native.limit externalProduced.value

def runtimeValueCorrespondence (P : CircularPresentation) (baseDepth : Nat) : RuntimeValueCorrespondence P baseDepth where
  runtimeCoverage := runtimeCoverage P baseDepth
  valueRuntimeCoverage := valueRuntimeCoverage P baseDepth
  receivedNameRuntime := runtimeOfReferenceNameRealizes P baseDepth
  correct := runtimeCorrect
  faithful := runtimeFaithful
  dyadic := runtimeRealizesDyadic P baseDepth
  add := runtimeRealizesAdd
  neg := runtimeRealizesNeg
  mul := runtimeRealizesMul
  inverse := runtimeRealizesInverse
  addReflection := runtimeRealizesAddReflect
  negReflection := runtimeRealizesNegReflect
  mulReflection := runtimeRealizesMulReflect
  inverseReflection := runtimeRealizesInverseReflect
  order := runtimeRealizesOrder
  orderReflection := runtimeRealizesOrderReflect
  apartness := runtimeRealizesApartness
  apartnessReflection := runtimeRealizesApartnessReflect
  densityProduction := runtimeDensityFromProduction
  boundsProduction := runtimeBoundsFromProduction
  densityReflection := runtimeDensityReflect
  boundsReflection := runtimeBoundsReflect
  densityCodeExact := runtimeDensityCodeExact
  boundsReadoutExact := runtimeBoundsReadoutExact
  producedLimit := runtimeProducedLimitRealizes P baseDepth

/-- All fields below are filled by the already constructed fixed routes. -/
structure ConventionalCauchyReferenceRecognition (P : CircularPresentation) (baseDepth : Nat) where
  quotient : QuotientRecognition.{u,v,g}
  completion : CompletionRecognition
  carrier : CarrierValueCorrespondence P baseDepth
  runtime : RuntimeValueCorrespondence P baseDepth

def recognizesConventionalCauchyReference (P : CircularPresentation) (baseDepth : Nat) :
    ConventionalCauchyReferenceRecognition.{u,v,g} P baseDepth :=
  ⟨quotientRecognition, completionRecognition, carrierValueCorrespondence P baseDepth,
    runtimeValueCorrespondence P baseDepth⟩

end RecognitionPackaging

end RelationalPerimeter.Constitution.Reals.RelationalRealCauchyReference

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealCauchyReference.regularCharacterization
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealCauchyReference.carrierToReferenceName
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealCauchyReference.referenceNameToCarrier
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealCauchyReference.targetPositiveSetoid
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealCauchyReference.DescendedComparison
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealCauchyReference.RelationalCompletionMorphism
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealCauchyReference.RelationalCompletionMorphism.Graph
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealCauchyReference.RelationalCompletionMorphism.underlying
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealCauchyReference.RelationalCompletionMorphism.unique
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealCauchyReference.RelationalCompletionMorphism.onClass
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealCauchyReference.RelationalCompletionMorphism.onClassBack
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealCauchyReference.RelationalCompletionMorphism.dyadic
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealCauchyReference.RelationalCompletionMorphism.producedLimit
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealCauchyReference.relationalCompletionComparison
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealCauchyReference.carrierPositiveSetoid
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealCauchyReference.Realizes
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealCauchyReference.realizationMorphism
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealCauchyReference.carrierCoverage
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealCauchyReference.relationalCoverage
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealCauchyReference.realizesStableValue
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealCauchyReference.realizesStableCarrier
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealCauchyReference.realizesCorrect
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealCauchyReference.realizesFaithful
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealCauchyReference.realizesDyadic
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealCauchyReference.realizesZero
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealCauchyReference.realizesOne
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealCauchyReference.realizesAdd
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealCauchyReference.realizesNeg
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealCauchyReference.realizesMul
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealCauchyReference.realizesOrder
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealCauchyReference.realizesOrderReflect
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealCauchyReference.realizesApartness
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealCauchyReference.realizesApartnessReflect
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealCauchyReference.realizesInverseOfUnit
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealCauchyReference.realizesInverse
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealCauchyReference.realizesInverseReflect
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealCauchyReference.realizesAddReflect
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealCauchyReference.realizesMulReflect
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealCauchyReference.realizesNegReflect
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealCauchyReference.realizesDensity
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealCauchyReference.realizesDensityReflect
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealCauchyReference.realizesBounds
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealCauchyReference.realizesBoundsReflect
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealCauchyReference.realizesProducedDensity
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealCauchyReference.realizesProducedBounds
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealCauchyReference.realizesDensityCodeExact
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealCauchyReference.realizesBoundsReadoutExact
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealCauchyReference.realizesProducedDensityCodeExact
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealCauchyReference.realizesProducedBoundsReadoutExact
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealCauchyReference.carrierToNameSameValue
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealCauchyReference.carrierExternalFamily
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealCauchyReference.carrierExternalTermRealizes
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealCauchyReference.externalConvergenceToCarrier
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealCauchyReference.realizesCarrierProducedLimit
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealCauchyReference.realizesExternalProducedLimit
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealCauchyReference.RuntimeRealizes
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealCauchyReference.runtimeCoverage
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealCauchyReference.valueRuntimeCoverage
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealCauchyReference.runtimeOfReferenceName
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealCauchyReference.runtimeOfReferenceNameRealizes
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealCauchyReference.runtimeCorrect
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealCauchyReference.runtimeFaithful
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealCauchyReference.runtimeRealizesDyadic
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealCauchyReference.runtimeRealizesAdd
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealCauchyReference.runtimeRealizesNeg
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealCauchyReference.runtimeRealizesMul
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealCauchyReference.runtimeRealizesInverse
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealCauchyReference.runtimeRealizesAddReflect
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealCauchyReference.runtimeRealizesNegReflect
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealCauchyReference.runtimeRealizesMulReflect
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealCauchyReference.runtimeRealizesInverseReflect
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealCauchyReference.runtimeRealizesOrder
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealCauchyReference.runtimeRealizesOrderReflect
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealCauchyReference.runtimeRealizesApartness
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealCauchyReference.runtimeRealizesApartnessReflect
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealCauchyReference.runtimeDensityFromProduction
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealCauchyReference.runtimeBoundsFromProduction
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealCauchyReference.runtimeDensityReflect
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealCauchyReference.runtimeBoundsReflect
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealCauchyReference.runtimeDensityCodeExact
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealCauchyReference.runtimeBoundsReadoutExact
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealCauchyReference.runtimeProducedLimitRealizes
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealCauchyReference.referenceMapPerimeterIndependent
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealCauchyReference.carrierReadoutPerimeterIndependent
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealCauchyReference.QuotientRecognition
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealCauchyReference.quotientRecognition
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealCauchyReference.CompletionRecognition
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealCauchyReference.completionRecognition
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealCauchyReference.CarrierValueCorrespondence
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealCauchyReference.carrierValueCorrespondence
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealCauchyReference.RuntimeValueCorrespondence
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealCauchyReference.runtimeValueCorrespondence
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealCauchyReference.ConventionalCauchyReferenceRecognition
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealCauchyReference.recognizesConventionalCauchyReference
/- AXIOM_AUDIT_END -/
