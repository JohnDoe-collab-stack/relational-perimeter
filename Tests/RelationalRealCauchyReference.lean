import RelationalPerimeter.Constitution.Reals.RelationalRealCauchyReference
import Tests.ExtensiveCauchyReal
import Tests.RelationalRealCarrierCompleteness

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace RelationalPerimeter.Tests.RelationalRealCauchyReference
open StrongPerimetralTurning
open RelationalPerimeter.Constitution.Reals
open RelationalPerimeter.Constitution.Reals.ExtensiveCauchyReal
open RelationalPerimeter.Constitution.Reals.RegularDyadicName
open RelationalPerimeter.Constitution.Reals.RegularDyadicCompletion
open RelationalPerimeter.Constitution.Reals.RelationalRealCauchyReference
open PresentedDyadicCompletion DyadicCompletionCharacterization
open RelationalRealAddition RelationalRealOrder CarrierOrderedField
open RelationalRealFamilyTransport
open RelationalPerimeter.Constitution.Reals.RelationalRealCarrierCompleteness
open RelationalPerimeter.Tests.RelationalRealCarrierCompleteness

/-- No closed-program presentation is required of this arbitrary received name. -/
def receivedNameRuntime (P : CircularPresentation) (d : Nat) (name : RegularDyadicName) :
    RuntimeRealizes P d (runtimeOfReferenceName P d name) (classOf name) :=
  runtimeOfReferenceNameRealizes P d name

def referenceCarrierRealizes (P : CircularPresentation) (d : Nat) (name : RegularDyadicName) :
    Realizes P d (referenceNameToCarrier P d name) (classOf name) :=
  ⟨name, classOfContains name, .refl _⟩

def taggedReferenceRealizes (P : CircularPresentation) (d : Nat) (name : RegularDyadicName) :
    Realizes P d (referenceNameToCarrier P d name) (ExtensiveCauchyReal.taggedClass name) :=
  realizesStableValue (ExtensiveCauchyReal.taggedClassEquivalent name) (referenceCarrierRealizes P d name)

def secondNameRealizesSameCarrier (P : CircularPresentation) (d : Nat) (name : RegularDyadicName) :
    Realizes P d (referenceNameToCarrier P d name) (classOf name) :=
  ⟨RegularDyadicName.tailName name 1, RegularDyadicName.tailEquivalent name 1,
   (regularCharacterization P d).backward.mapEquivalent (RegularDyadicName.tailEquivalent name 1).symm⟩

theorem realizationIsDescent (P : CircularPresentation) (d : Nat)
    (carrier : EffectiveCauchyReal.Carrier) (value : Value) :
    Realizes P d carrier value =
      DescendedComparison (Y := carrierPositiveSetoid P d) (referenceNameToCarrier P d) value carrier := rfl

theorem coverageUsesForwardMap (P : CircularPresentation) (d : Nat) (carrier : EffectiveCauchyReal.Carrier) :
    (carrierCoverage P d carrier).2.name = carrierToReferenceName P d carrier := rfl
theorem coverageClassExact (P : CircularPresentation) (d : Nat) (carrier : EffectiveCauchyReal.Carrier) :
    (carrierCoverage P d carrier).1 = classOf (carrierToReferenceName P d carrier) := rfl
theorem coverageConsumesCarrierReturn (P : CircularPresentation) (d : Nat) (carrier : EffectiveCauchyReal.Carrier) :
    (carrierCoverage P d carrier).2.agrees = (regularCharacterization P d).carrierReturn carrier := rfl

theorem taggedRelationalCoverage (P : CircularPresentation) (d : Nat) (name : RegularDyadicName) :
    Nonempty (Σ carrier, Realizes P d carrier (ExtensiveCauchyReal.taggedClass name)) := relationalCoverage P d _

def graphWithFirstName {Target : PresentedDyadicCompletionObject} (M : RelationalCompletionMorphism Target)
    (name : RegularDyadicName) : M.Graph (classOf name) (M.pullback.map name) :=
  ⟨name, classOfContains name, Target.core.equivalentRefl _⟩

def graphWithSecondName {Target : PresentedDyadicCompletionObject} (M : RelationalCompletionMorphism Target)
    {a b : RegularDyadicName} (same : NameEquivalent a b) : M.Graph (classOf a) (M.pullback.map b) :=
  ⟨b, same, Target.core.equivalentRefl _⟩

def differentGraphNamesUnique {Target : PresentedDyadicCompletionObject} (M N : RelationalCompletionMorphism Target)
    {a b : RegularDyadicName} (same : NameEquivalent a b) :
    Target.core.Equivalent (M.pullback.map a) (N.pullback.map b) :=
  RelationalCompletionMorphism.unique M N (classOf a) _ _
    (graphWithFirstName M a) (graphWithSecondName N same)

def distinctZeroGraphNamesUnique {Target : PresentedDyadicCompletionObject}
    (M N : RelationalCompletionMorphism Target) :
    Target.core.Equivalent (M.pullback.map zeroName) (N.pullback.map (RegularDyadicName.tailName zeroName 1)) :=
  differentGraphNamesUnique M N RegularDyadicName.twoDistinctZeroNames

def carrierSameValueDifferentClasses (P : CircularPresentation) (d : Nat) (name : RegularDyadicName) :
    ExternalEquivalent (classOf name) (ExtensiveCauchyReal.taggedClass name) :=
  realizesCorrect (.refl _) (referenceCarrierRealizes P d name) (taggedReferenceRealizes P d name)

def carrierDifferentNamesFaithful (P : CircularPresentation) (d : Nat) {a b : RegularDyadicName}
    (same : NameEquivalent a b) : EffectiveCauchyReal.Equivalent (referenceNameToCarrier P d a) (referenceNameToCarrier P d b) :=
  realizesFaithful (classOfPreserves same) (referenceCarrierRealizes P d a) (referenceCarrierRealizes P d b)

def taggedRuntimeRealizes (P : CircularPresentation) (d : Nat) (name : RegularDyadicName) :
    RuntimeRealizes P d (runtimeOfReferenceName P d name) (ExtensiveCauchyReal.taggedClass name) :=
  realizesStableValue (ExtensiveCauchyReal.taggedClassEquivalent name) (receivedNameRuntime P d name)

def runtimeSameValueDifferentClasses (P : CircularPresentation) (d : Nat) (name : RegularDyadicName) :
    ExternalEquivalent (classOf name) (ExtensiveCauchyReal.taggedClass name) :=
  runtimeCorrect (.refl _) (receivedNameRuntime P d name) (taggedRuntimeRealizes P d name)

def runtimeDifferentNamesFaithful (P : CircularPresentation) (d : Nat) {a b : RegularDyadicName}
    (same : NameEquivalent a b) : Equivalent (runtimeOfReferenceName P d a) (runtimeOfReferenceName P d b) :=
  runtimeFaithful (classOfPreserves same) (receivedNameRuntime P d a) (receivedNameRuntime P d b)

def runtimeComposite (P : CircularPresentation) (d : Nat) (a b : RegularDyadicName) : Real P d :=
  .add (.mul (runtimeOfReferenceName P d a) (runtimeOfReferenceName P d b)) (.neg (runtimeOfReferenceName P d a))

def runtimeCompositeRealizes (P : CircularPresentation) (d : Nat) (a b : RegularDyadicName) :
    RuntimeRealizes P d (runtimeComposite P d a b)
      (addValue (mulValue (classOf a) (classOf b)) (negValue (classOf a))) :=
  runtimeRealizesAdd (runtimeRealizesMul (receivedNameRuntime P d a) (receivedNameRuntime P d b))
    (runtimeRealizesNeg (receivedNameRuntime P d a))

def runtimeCompositeCoverage (P : CircularPresentation) (d : Nat) (a b : RegularDyadicName) :
    Σ value, RuntimeRealizes P d (runtimeComposite P d a b) value := runtimeCoverage P d _

theorem taggedRuntimeCoverage (P : CircularPresentation) (d : Nat) (name : RegularDyadicName) :
    Nonempty (Σ runtime, RuntimeRealizes P d runtime (ExtensiveCauchyReal.taggedClass name)) :=
  valueRuntimeCoverage P d _

def explicitRuntimeRoundtrip (P : CircularPresentation) (d : Nat) {carrier : EffectiveCauchyReal.Carrier}
    {value : Value} (received : Realizes P d carrier value) :
    RuntimeRealizes P d (ofCarrier P d carrier) value :=
  ⟨received.name, received.member, received.agrees.trans (carrier_roundtrip carrier).symm⟩

theorem twoPerimeterReferenceReadouts (name : RegularDyadicName) (response : Nat) :
    (referenceNameToCarrier firstPerimeter 1 name).approximation response =
      (referenceNameToCarrier secondPerimeter 4 name).approximation response :=
  referenceMapPerimeterIndependent firstPerimeter secondPerimeter 1 4 name response

theorem twoPerimeterForwardReadouts (carrier : EffectiveCauchyReal.Carrier) (response : Nat) :
    (carrierToReferenceName firstPerimeter 1 carrier).approximation response =
      (carrierToReferenceName secondPerimeter 4 carrier).approximation response :=
  carrierReadoutPerimeterIndependent firstPerimeter secondPerimeter 1 4 carrier response

def twoPerimeterRealizations (name : RegularDyadicName) :=
  (receivedNameRuntime firstPerimeter 1 name, receivedNameRuntime secondPerimeter 4 name)

def receivedInverseRealization (P : CircularPresentation) (d : Nat) {carrier : EffectiveCauchyReal.Carrier} {value : Value}
    (source : Realizes P d carrier value) (domain : CanonicalCarrierDomain carrier)
    (witness : ExternalApartness value ExtensiveCauchyReal.zero) :
    Realizes P d (carrierInverse P d carrier domain) (externalInverse value witness) := realizesInverse source domain witness

def oneCarrierDomain (P : CircularPresentation) (d : Nat) : CanonicalCarrierDomain canonicalOneCarrier :=
  realizesApartnessReflect (realizesOne P d) (realizesZero P d) ExtensiveCauchyReal.secondApartness

def oneInverseFirstWitness (P : CircularPresentation) (d : Nat) :=
  realizesInverse (realizesOne P d) (oneCarrierDomain P d) ExtensiveCauchyReal.firstApartness
def oneInverseSecondWitness (P : CircularPresentation) (d : Nat) :=
  realizesInverse (realizesOne P d) (oneCarrierDomain P d) ExtensiveCauchyReal.secondApartness

def oneInverseWitnessesAgree (P : CircularPresentation) (d : Nat) :
    ExternalEquivalent (externalInverse ExtensiveCauchyReal.one ExtensiveCauchyReal.firstApartness)
      (externalInverse ExtensiveCauchyReal.one ExtensiveCauchyReal.secondApartness) :=
  realizesCorrect (.refl _) (oneInverseFirstWitness P d) (oneInverseSecondWitness P d)

def runtimeInverseWithReceivedWitness {P : CircularPresentation} {d : Nat} {source : Real P d} {value : Value}
    (realized : RuntimeRealizes P d source value)
    (domain : RelationalRealOrder.Apartness source (RelationalRealAddition.zero P d))
    (witness : ExternalApartness value ExtensiveCauchyReal.zero) :
    RuntimeRealizes P d (RelationalRealInverse.inverse source domain) (externalInverse value witness) :=
  runtimeRealizesInverse realized domain witness

def carrierOrderBothDirections {P : CircularPresentation} {d : Nat} {a b : EffectiveCauchyReal.Carrier} {x y : Value}
    (left : Realizes P d a x) (right : Realizes P d b y) (origin : CarrierOrder a b) : CarrierOrder a b :=
  realizesOrderReflect left right (realizesOrder left right origin)

def runtimeOrderBothDirections {P : CircularPresentation} {d : Nat} {a b : Real P d} {x y : Value}
    (left : RuntimeRealizes P d a x) (right : RuntimeRealizes P d b y) (origin : StrictOrder a b) : StrictOrder a b :=
  runtimeRealizesOrderReflect left right (runtimeRealizesOrder left right origin)

def carrierApartnessBothDirections {P : CircularPresentation} {d : Nat}
    {a b : EffectiveCauchyReal.Carrier} {x y : Value}
    (left : Realizes P d a x) (right : Realizes P d b y) (origin : CarrierApartness a b) : CarrierApartness a b :=
  realizesApartnessReflect left right (realizesApartness left right origin)

def runtimeApartnessBothDirections {P : CircularPresentation} {d : Nat} {a b : Real P d} {x y : Value}
    (left : RuntimeRealizes P d a x) (right : RuntimeRealizes P d b y)
    (origin : RelationalRealOrder.Apartness a b) : RelationalRealOrder.Apartness a b :=
  runtimeRealizesApartnessReflect left right (runtimeRealizesApartness left right origin)

def completionDyadicTransport (Target : PresentedDyadicCompletionObject) (code : SignedDyadicCode) :
    (relationalCompletionComparison Target).Graph (dyadicValue code) (Target.core.dyadic code) :=
  RelationalCompletionMorphism.dyadic _ code

def completionLimitTransport (Target : PresentedDyadicCompletionObject) (family : ExternalPresentedFamily) :
    (relationalCompletionComparison Target).Graph (externalComplete family).value
      (Target.completion.complete (diagonalTransportFamily regularPresentedCore Target.core (referenceFamily family))).value :=
  RelationalCompletionMorphism.producedLimit _ (referenceFamily family)

theorem carrierDensityReflectionCode {P : CircularPresentation} {d : Nat}
    {a b : EffectiveCauchyReal.Carrier} {x y : Value} (left : Realizes P d a x) (right : Realizes P d b y)
    (witness : ExternalDensityWitness x y) : (realizesDensityReflect left right witness).1 = witness.code := rfl

theorem carrierBoundsReflectionReadout {P : CircularPresentation} {d : Nat}
    {source : EffectiveCauchyReal.Carrier} {value : Value} (realized : Realizes P d source value)
    (witness : ExternalNaturalBounds value) :
    (realizesBoundsReflect realized witness).1 = witness.lower ∧
      (realizesBoundsReflect realized witness).2.1 = witness.upper := ⟨rfl, rfl⟩

theorem runtimeDensityReflectionCode {P : CircularPresentation} {d : Nat} {a b : Real P d} {x y : Value}
    (left : RuntimeRealizes P d a x) (right : RuntimeRealizes P d b y) (witness : ExternalDensityWitness x y) :
    (runtimeDensityReflect left right witness).1 = witness.code := rfl

theorem runtimeBoundsReflectionReadout {P : CircularPresentation} {d : Nat} {source : Real P d} {value : Value}
    (realized : RuntimeRealizes P d source value) (witness : ExternalNaturalBounds value) :
    (runtimeBoundsReflect realized witness).1 = witness.lower ∧
      (runtimeBoundsReflect realized witness).2.1 = witness.upper := ⟨rfl, rfl⟩

theorem carrierDensityPacketReadout {P : CircularPresentation} {d : Nat} {a b : EffectiveCauchyReal.Carrier} {x y : Value}
    (left : Realizes P d a x) (right : Realizes P d b y) {origin : CarrierOrder a b}
    (produced : CarrierDensityResult P d a b origin) :
    (realizesProducedDensity left right produced).code = produced.code := rfl

theorem carrierBoundsPacketReadouts {P : CircularPresentation} {d : Nat} {source : EffectiveCauchyReal.Carrier} {value : Value}
    (realized : Realizes P d source value) (produced : CarrierNaturalBoundResult P d source) :
    (realizesProducedBounds realized produced).lower = produced.lower ∧
      (realizesProducedBounds realized produced).upper = produced.upper := ⟨rfl, rfl⟩

theorem runtimeDensityPacketReadout {P : CircularPresentation} {d : Nat} {a b : Real P d} {x y : Value}
    (left : RuntimeRealizes P d a x) (right : RuntimeRealizes P d b y)
    {origin : StrictOrder a b} {journal : ConstitutiveRuntime.Journal P d}
    (produced : RelationalRealDensity.Density origin journal) :
    (runtimeDensityFromProduction left right produced).code = produced.action.readout :=
  runtimeDensityCodeExact left right produced

theorem runtimeBoundsPacketReadouts {P : CircularPresentation} {d : Nat} {source : Real P d} {value : Value}
    (realized : RuntimeRealizes P d source value) {archive : (environment source).Archive}
    {journal : ConstitutiveRuntime.Journal P d}
    (produced : RelationalRealDensity.NaturalBound source archive journal) :
    (runtimeBoundsFromProduction realized produced).lower = produced.action.stored.value.lower ∧
      (runtimeBoundsFromProduction realized produced).upper = produced.action.stored.value.upper :=
  runtimeBoundsReadoutExact realized produced

/-- Both routes consume the same two received production packets. -/
def sharedProducedLimitReadouts (P : CircularPresentation) (d : Nat) (family : CarrierFamily)
    (carrierProduced : CarrierCompletionResult P d family)
    (externalProduced : ExternalLimitResult (carrierExternalFamily P d family)) :
    Realizes P d carrierProduced.limit externalProduced.value ×
      RuntimeRealizes P d carrierProduced.native.limit externalProduced.value :=
  ⟨realizesCarrierProducedLimit P d family carrierProduced externalProduced,
   runtimeProducedLimitRealizes P d family carrierProduced externalProduced⟩

theorem sharedProducedLimitNamesExact (P : CircularPresentation) (d : Nat) (family : CarrierFamily)
    (carrierProduced : CarrierCompletionResult P d family)
    (externalProduced : ExternalLimitResult (carrierExternalFamily P d family)) :
    (sharedProducedLimitReadouts P d family carrierProduced externalProduced).1.name =
      (sharedProducedLimitReadouts P d family carrierProduced externalProduced).2.name := by
  cases carrierProduced with
  | mk native limit limitExact convergence uniqueness =>
    cases limitExact
    rfl

def decaySharedProduction (P : CircularPresentation) (d : Nat) :=
  let carrierProduced := completed P d
  let externalProduced := externalComplete (carrierExternalFamily P d decayFamily)
  sharedProducedLimitReadouts P d decayFamily carrierProduced externalProduced

theorem decayModulePreserved (P : CircularPresentation) (d p : Nat) :
    (carrierExternalFamily P d decayFamily).modulus p = p + 1 := rfl

def receivedExternalProducedLimit (P : CircularPresentation) (d : Nat) :=
  realizesExternalProducedLimit P d ExtensiveCauchyReal.decayingExternalFamily

theorem externalLimitCandidateReadoutExact (P : CircularPresentation) (d : Nat) :
    (receivedExternalProducedLimit P d).name =
      (externalComplete ExtensiveCauchyReal.decayingExternalFamily).convergence.candidateName := rfl

universe u v g
def completeRecognition (P : CircularPresentation) (d : Nat) :
    ConventionalCauchyReferenceRecognition.{u,v,g} P d := recognizesConventionalCauchyReference P d

def recognitionQuotientCoverage (P : CircularPresentation) (d : Nat) (name : RegularDyadicName) :
    Σ value, ReferenceRealizes name value := (completeRecognition.{0,0,0} P d).quotient.coverage name

def recognitionReceivedRuntime (P : CircularPresentation) (d : Nat) (name : RegularDyadicName) :
    RuntimeRealizes P d (runtimeOfReferenceName P d name) (classOf name) :=
  (completeRecognition.{0,0,0} P d).runtime.receivedNameRuntime name

def recognitionCompletionComparison (P : CircularPresentation) (d : Nat) (Target : PresentedDyadicCompletionObject) :
    RelationalCompletionMorphism Target := (completeRecognition.{0,0,0} P d).completion.completionComparison Target

def recognitionCarrierForward (P : CircularPresentation) (d : Nat) (carrier : EffectiveCauchyReal.Carrier) :
    Σ value, Realizes P d carrier value := (completeRecognition.{0,0,0} P d).carrier.carrierCoverage carrier

def recognitionRuntimeComposite (P : CircularPresentation) (d : Nat) (a b : RegularDyadicName) :
    RuntimeRealizes P d (runtimeComposite P d a b)
      (addValue (mulValue (classOf a) (classOf b)) (negValue (classOf a))) :=
  let recognized := completeRecognition.{0,0,0} P d
  recognized.runtime.add
    (recognized.runtime.mul (recognized.runtime.receivedNameRuntime a) (recognized.runtime.receivedNameRuntime b))
    (recognized.runtime.neg (recognized.runtime.receivedNameRuntime a))

theorem recognitionHasAllReadoutLaws (P : CircularPresentation.{0,0,0,0,0}) (d : Nat) : SetoidOrderedArchimedeanReadout :=
  (completeRecognition.{0,0,0} P d).completion.readout

def recognitionCarrierAddReflection (P : CircularPresentation) (d : Nat) {a b : EffectiveCauchyReal.Carrier} {x y : Value}
    (left : Realizes P d a x) (right : Realizes P d b y) : ExternalEquivalent (addValue x y) (addValue x y) :=
  let recognized := (completeRecognition.{0,0,0} P d).carrier
  recognized.addReflection left right (recognized.add left right)

def recognitionRuntimeMulReflection (P : CircularPresentation) (d : Nat) {a b : Real P d} {x y : Value}
    (left : RuntimeRealizes P d a x) (right : RuntimeRealizes P d b y) : ExternalEquivalent (mulValue x y) (mulValue x y) :=
  let recognized := (completeRecognition.{0,0,0} P d).runtime
  recognized.mulReflection left right (recognized.mul left right)

def recognitionRuntimeInverseReflection (P : CircularPresentation) (d : Nat) {a : Real P d} {x : Value}
    (source : RuntimeRealizes P d a x) (domain : RelationalRealOrder.Apartness a (RelationalRealAddition.zero P d))
    (witness : ExternalApartness x ExtensiveCauchyReal.zero) :
    ExternalEquivalent (externalInverse x witness) (externalInverse x witness) :=
  let recognized := (completeRecognition.{0,0,0} P d).runtime
  recognized.inverseReflection source domain witness (recognized.inverse source domain witness)

theorem recognitionNativeDensityReadout {P : CircularPresentation} {d : Nat} {a b : Real P d} {x y : Value}
    (left : RuntimeRealizes P d a x) (right : RuntimeRealizes P d b y)
    {origin : StrictOrder a b} {journal : ConstitutiveRuntime.Journal P d}
    (produced : RelationalRealDensity.Density origin journal) :
    (runtimeDensityFromProduction left right produced).code = produced.action.readout :=
  (completeRecognition.{0,0,0} P d).runtime.densityCodeExact left right produced

theorem recognitionCarrierBoundsReadouts {P : CircularPresentation} {d : Nat}
    {source : EffectiveCauchyReal.Carrier} {value : Value} (realized : Realizes P d source value)
    (produced : CarrierNaturalBoundResult P d source) :
    (realizesProducedBounds realized produced).lower = produced.lower ∧
      (realizesProducedBounds realized produced).upper = produced.upper :=
  (completeRecognition.{0,0,0} P d).carrier.boundsReadoutExact realized produced

end RelationalPerimeter.Tests.RelationalRealCauchyReference

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Tests.RelationalRealCauchyReference.receivedNameRuntime
#print axioms RelationalPerimeter.Tests.RelationalRealCauchyReference.referenceCarrierRealizes
#print axioms RelationalPerimeter.Tests.RelationalRealCauchyReference.taggedReferenceRealizes
#print axioms RelationalPerimeter.Tests.RelationalRealCauchyReference.secondNameRealizesSameCarrier
#print axioms RelationalPerimeter.Tests.RelationalRealCauchyReference.realizationIsDescent
#print axioms RelationalPerimeter.Tests.RelationalRealCauchyReference.coverageUsesForwardMap
#print axioms RelationalPerimeter.Tests.RelationalRealCauchyReference.coverageClassExact
#print axioms RelationalPerimeter.Tests.RelationalRealCauchyReference.coverageConsumesCarrierReturn
#print axioms RelationalPerimeter.Tests.RelationalRealCauchyReference.taggedRelationalCoverage
#print axioms RelationalPerimeter.Tests.RelationalRealCauchyReference.graphWithFirstName
#print axioms RelationalPerimeter.Tests.RelationalRealCauchyReference.graphWithSecondName
#print axioms RelationalPerimeter.Tests.RelationalRealCauchyReference.differentGraphNamesUnique
#print axioms RelationalPerimeter.Tests.RelationalRealCauchyReference.distinctZeroGraphNamesUnique
#print axioms RelationalPerimeter.Tests.RelationalRealCauchyReference.carrierSameValueDifferentClasses
#print axioms RelationalPerimeter.Tests.RelationalRealCauchyReference.carrierDifferentNamesFaithful
#print axioms RelationalPerimeter.Tests.RelationalRealCauchyReference.taggedRuntimeRealizes
#print axioms RelationalPerimeter.Tests.RelationalRealCauchyReference.runtimeSameValueDifferentClasses
#print axioms RelationalPerimeter.Tests.RelationalRealCauchyReference.runtimeDifferentNamesFaithful
#print axioms RelationalPerimeter.Tests.RelationalRealCauchyReference.runtimeComposite
#print axioms RelationalPerimeter.Tests.RelationalRealCauchyReference.runtimeCompositeRealizes
#print axioms RelationalPerimeter.Tests.RelationalRealCauchyReference.runtimeCompositeCoverage
#print axioms RelationalPerimeter.Tests.RelationalRealCauchyReference.taggedRuntimeCoverage
#print axioms RelationalPerimeter.Tests.RelationalRealCauchyReference.explicitRuntimeRoundtrip
#print axioms RelationalPerimeter.Tests.RelationalRealCauchyReference.twoPerimeterReferenceReadouts
#print axioms RelationalPerimeter.Tests.RelationalRealCauchyReference.twoPerimeterForwardReadouts
#print axioms RelationalPerimeter.Tests.RelationalRealCauchyReference.twoPerimeterRealizations
#print axioms RelationalPerimeter.Tests.RelationalRealCauchyReference.receivedInverseRealization
#print axioms RelationalPerimeter.Tests.RelationalRealCauchyReference.oneCarrierDomain
#print axioms RelationalPerimeter.Tests.RelationalRealCauchyReference.oneInverseFirstWitness
#print axioms RelationalPerimeter.Tests.RelationalRealCauchyReference.oneInverseSecondWitness
#print axioms RelationalPerimeter.Tests.RelationalRealCauchyReference.oneInverseWitnessesAgree
#print axioms RelationalPerimeter.Tests.RelationalRealCauchyReference.runtimeInverseWithReceivedWitness
#print axioms RelationalPerimeter.Tests.RelationalRealCauchyReference.carrierOrderBothDirections
#print axioms RelationalPerimeter.Tests.RelationalRealCauchyReference.runtimeOrderBothDirections
#print axioms RelationalPerimeter.Tests.RelationalRealCauchyReference.carrierApartnessBothDirections
#print axioms RelationalPerimeter.Tests.RelationalRealCauchyReference.runtimeApartnessBothDirections
#print axioms RelationalPerimeter.Tests.RelationalRealCauchyReference.completionDyadicTransport
#print axioms RelationalPerimeter.Tests.RelationalRealCauchyReference.completionLimitTransport
#print axioms RelationalPerimeter.Tests.RelationalRealCauchyReference.carrierDensityReflectionCode
#print axioms RelationalPerimeter.Tests.RelationalRealCauchyReference.carrierBoundsReflectionReadout
#print axioms RelationalPerimeter.Tests.RelationalRealCauchyReference.runtimeDensityReflectionCode
#print axioms RelationalPerimeter.Tests.RelationalRealCauchyReference.runtimeBoundsReflectionReadout
#print axioms RelationalPerimeter.Tests.RelationalRealCauchyReference.carrierDensityPacketReadout
#print axioms RelationalPerimeter.Tests.RelationalRealCauchyReference.carrierBoundsPacketReadouts
#print axioms RelationalPerimeter.Tests.RelationalRealCauchyReference.runtimeDensityPacketReadout
#print axioms RelationalPerimeter.Tests.RelationalRealCauchyReference.runtimeBoundsPacketReadouts
#print axioms RelationalPerimeter.Tests.RelationalRealCauchyReference.sharedProducedLimitReadouts
#print axioms RelationalPerimeter.Tests.RelationalRealCauchyReference.sharedProducedLimitNamesExact
#print axioms RelationalPerimeter.Tests.RelationalRealCauchyReference.decaySharedProduction
#print axioms RelationalPerimeter.Tests.RelationalRealCauchyReference.decayModulePreserved
#print axioms RelationalPerimeter.Tests.RelationalRealCauchyReference.receivedExternalProducedLimit
#print axioms RelationalPerimeter.Tests.RelationalRealCauchyReference.externalLimitCandidateReadoutExact
#print axioms RelationalPerimeter.Tests.RelationalRealCauchyReference.completeRecognition
#print axioms RelationalPerimeter.Tests.RelationalRealCauchyReference.recognitionQuotientCoverage
#print axioms RelationalPerimeter.Tests.RelationalRealCauchyReference.recognitionReceivedRuntime
#print axioms RelationalPerimeter.Tests.RelationalRealCauchyReference.recognitionCompletionComparison
#print axioms RelationalPerimeter.Tests.RelationalRealCauchyReference.recognitionCarrierForward
#print axioms RelationalPerimeter.Tests.RelationalRealCauchyReference.recognitionRuntimeComposite
#print axioms RelationalPerimeter.Tests.RelationalRealCauchyReference.recognitionHasAllReadoutLaws
#print axioms RelationalPerimeter.Tests.RelationalRealCauchyReference.recognitionCarrierAddReflection
#print axioms RelationalPerimeter.Tests.RelationalRealCauchyReference.recognitionRuntimeMulReflection
#print axioms RelationalPerimeter.Tests.RelationalRealCauchyReference.recognitionRuntimeInverseReflection
#print axioms RelationalPerimeter.Tests.RelationalRealCauchyReference.recognitionNativeDensityReadout
#print axioms RelationalPerimeter.Tests.RelationalRealCauchyReference.recognitionCarrierBoundsReadouts
/- AXIOM_AUDIT_END -/
