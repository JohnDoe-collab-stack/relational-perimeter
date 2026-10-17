import RelationalPerimeter.Constitution.Reals.RelationalRealInverseLaws

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-! All inverse presentations below are readouts of the already constructed
relational inverse. Realization of a numerical domain executes fresh comparison
Steps; it never claims to recover the occurrences erased by projection. -/
namespace RelationalPerimeter.Constitution.Reals.RelationalRealInverse
open StrongPerimetralTurning RuntimeCorrespondence HeterogeneousRealRuntime
open RelationalRealAddition RelationalRealOrder
variable {P : CircularPresentation} {baseDepth : Nat}

def PresentationDomain (P : CircularPresentation) (baseDepth : Nat) (source : EffectiveDyadicPresentation) : Type :=
  PresentationApartness source (toPresentation (zero P baseDepth))

def realizePresentationDomain (source : EffectiveDyadicPresentation) (numeric : PresentationDomain P baseDepth source)
    (archive : (environment (ofPresentation P baseDepth source)).Archive)
    (zeroArchive : (environment (zero P baseDepth)).Archive) :
    Apartness (ofPresentation P baseDepth source) (zero P baseDepth) := by
  cases numeric with
  | inl order =>
      apply Apartness.forward
      apply reflectPresentationOrder (aa := archive) (ba := zeroArchive)
      refine ⟨order.accuracy, order.response, order.beyond, ?_⟩
      change StrictSeparation order.accuracy (readout (ofPresentation P baseDepth source) order.response)
        (readout (zero P baseDepth) order.response)
      rw [ofPresentation_readout]
      exact order.separation
  | inr order =>
      apply Apartness.backward
      apply reflectPresentationOrder (aa := zeroArchive) (ba := archive)
      refine ⟨order.accuracy, order.response, order.beyond, ?_⟩
      change StrictSeparation order.accuracy (readout (zero P baseDepth) order.response)
        (readout (ofPresentation P baseDepth source) order.response)
      rw [ofPresentation_readout]
      exact order.separation

/-- The numerical operation is derived by realization, executed inverse, then
readout. There is no independently inverted numerical value to repackage. -/
def inversePresentation (source : EffectiveDyadicPresentation) (numeric : PresentationDomain P baseDepth source) :
    EffectiveDyadicPresentation :=
  toPresentation (inverse (ofPresentation P baseDepth source)
    (realizePresentationDomain source numeric (environment (ofPresentation P baseDepth source)).initialArchive
      (environment (zero P baseDepth)).initialArchive))

def toPresentation_inverse (source : Real P baseDepth) (witness : Apartness source (zero P baseDepth)) :
    EffectiveDyadicPresentation.Equivalent (toPresentation (inverse source witness))
      (inversePresentation (toPresentation source) witness.toPresentation) :=
  (equivalentPresentation _ _).1 (inverse_congr (real_roundtrip source).symm witness _)

def realization_inverse (source : EffectiveDyadicPresentation) (numeric : PresentationDomain P baseDepth source) :
    Equivalent (inverse (ofPresentation P baseDepth source)
      (realizePresentationDomain source numeric (environment (ofPresentation P baseDepth source)).initialArchive
        (environment (zero P baseDepth)).initialArchive))
      (ofPresentation P baseDepth (inversePresentation source numeric)) :=
  (real_roundtrip _).symm

def CarrierDomain (P : CircularPresentation) (baseDepth : Nat) (source : EffectiveCauchyReal.Carrier) : Type :=
  CarrierApartness source (toCarrier (zero P baseDepth))

def realizeCarrierDomain (source : EffectiveCauchyReal.Carrier) (numeric : CarrierDomain P baseDepth source)
    (archive : (environment (ofCarrier P baseDepth source)).Archive)
    (zeroArchive : (environment (zero P baseDepth)).Archive) :
    Apartness (ofCarrier P baseDepth source) (zero P baseDepth) :=
  realizePresentationDomain (EffectiveCauchyReal.toPresentation source) numeric archive zeroArchive

def inverseCarrier (source : EffectiveCauchyReal.Carrier) (numeric : CarrierDomain P baseDepth source) :
    EffectiveCauchyReal.Carrier :=
  EffectiveCauchyReal.ofPresentation
    (inversePresentation (P := P) (baseDepth := baseDepth) (EffectiveCauchyReal.toPresentation source) numeric)

def toCarrier_inverse (source : Real P baseDepth) (witness : Apartness source (zero P baseDepth)) :
    EffectiveCauchyReal.Equivalent (toCarrier (inverse source witness))
      (inverseCarrier (toCarrier source) witness.toCarrier) :=
  EffectiveCauchyReal.presentationEquivalentToCarrier (toPresentation_inverse source witness)

def realization_carrier_inverse (source : EffectiveCauchyReal.Carrier) (numeric : CarrierDomain P baseDepth source) :
    Equivalent (inverse (ofCarrier P baseDepth source)
      (realizeCarrierDomain source numeric (environment (ofCarrier P baseDepth source)).initialArchive
        (environment (zero P baseDepth)).initialArchive))
      (ofCarrier P baseDepth (inverseCarrier source numeric)) :=
  realization_inverse (P := P) (baseDepth := baseDepth) _ numeric

end RelationalPerimeter.Constitution.Reals.RelationalRealInverse

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealInverse.PresentationDomain
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealInverse.realizePresentationDomain
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealInverse.inversePresentation
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealInverse.toPresentation_inverse
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealInverse.realization_inverse
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealInverse.CarrierDomain
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealInverse.realizeCarrierDomain
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealInverse.inverseCarrier
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealInverse.toCarrier_inverse
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealInverse.realization_carrier_inverse
/- AXIOM_AUDIT_END -/
