import RelationalPerimeter.Constitution.Reals.CarrierOrderedCompletion

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Relative characterization among explicitly presented dyadic completions

Comparisons are produced from presentation and completion. Uniqueness is
pointwise positive equivalence, never equality of functions or histories.
No external unpresented real or quotient occurs here.
-/
namespace RelationalPerimeter.Constitution.Reals.DyadicCompletionCharacterization
open StrongPerimetralTurning RuntimeCorrespondence ProducedCompleteness
open PresentedDyadicCompletion RelationalRealAddition RelationalRealOrder CarrierOrderedField

structure CompletionMorphism (Source Target : PresentedDyadicCompletionObject) where
  map : Source.core.Carrier → Target.core.Carrier
  mapEquivalent : {x y : Source.core.Carrier} → Source.core.Equivalent x y → Target.core.Equivalent (map x) (map y)
  mapDyadic : (code : SignedDyadicCode) → Target.core.Equivalent (map (Source.core.dyadic code)) (Target.core.dyadic code)
  presents : (x : Source.core.Carrier) → Converges Target.core
    (presentCarrierFamily Target.core (numericalCarrier Source.core.toPresentedDyadicData x)) (map x)

def PointwiseEquivalent {Source Target : PresentedDyadicCompletionObject}
    (f g : CompletionMorphism Source Target) : Type :=
  (x : Source.core.Carrier) → Target.core.Equivalent (f.map x) (g.map x)

def mapAsProducedLimit {Source Target : PresentedDyadicCompletionObject}
    (f : CompletionMorphism Source Target) (x : Source.core.Carrier) :
    Target.core.Equivalent (f.map x) (Target.completion.complete
      (presentCarrierFamily Target.core (numericalCarrier Source.core.toPresentedDyadicData x))).value :=
  Target.core.equivalentSymm ((Target.completion.complete _).unique _ (f.presents x))

def morphismNumerical {Source Target : PresentedDyadicCompletionObject}
    (f : CompletionMorphism Source Target) (x : Source.core.Carrier) :
    EffectiveCauchyReal.Equivalent (numericalCarrier Target.core.toPresentedDyadicData (f.map x))
      (numericalCarrier Source.core.toPresentedDyadicData x) :=
  presentedCarrierEquivalent Target.core _ _ (f.presents x)

def constantPresentationConvergence (Source Target : PresentedDyadicStructure) (code : SignedDyadicCode) :
    Converges Target (presentCarrierFamily Target (numericalCarrier Source.toPresentedDyadicData (Source.dyadic code)))
      (Target.dyadic code) where
  threshold p := p
  near p n r s hn hr hs :=
    ((Target.dyadicExact _ _).trans ((Source.dyadicExact _ _).trans (Target.dyadicExact _ _).symm)).toNear p

def comparisonMorphism (Source Target : PresentedDyadicCompletionObject) : CompletionMorphism Source Target where
  map x := (Target.completion.complete
    (presentCarrierFamily Target.core (numericalCarrier Source.core.toPresentedDyadicData x))).value
  mapEquivalent := by
    intro x y same
    exact carrierToEquivalent ((presentedCarrierEquivalent Target.core _ _ (Target.completion.complete _).convergence).trans
      ((equivalentToCarrier same).trans
        (presentedCarrierEquivalent Target.core _ _ (Target.completion.complete _).convergence).symm))
  mapDyadic code := (Target.completion.complete _).unique _ (constantPresentationConvergence Source.core Target.core code)
  presents x := (Target.completion.complete _).convergence

def comparisonUnique {Source Target : PresentedDyadicCompletionObject}
    (f : CompletionMorphism Source Target) : PointwiseEquivalent f (comparisonMorphism Source Target) :=
  mapAsProducedLimit f

def morphismsPointwiseEquivalent {Source Target : PresentedDyadicCompletionObject}
    (f g : CompletionMorphism Source Target) : PointwiseEquivalent f g :=
  fun x => Target.core.equivalentTrans (mapAsProducedLimit f x) (Target.core.equivalentSymm (mapAsProducedLimit g x))

def preservePresentedLimit {Source Target : PresentedDyadicCompletionObject}
    (f : CompletionMorphism Source Target) {family : PresentedFamily Source.core} {value : Source.core.Carrier}
    (convergence : Converges Source.core family value) :
    Converges Target.core (diagonalTransportFamily Source.core Target.core family) (f.map value) where
  threshold p := p + 3
  near := by
    intro p n r s hn hr hs
    have hnPrecision : PrecisionExtension (p + 1) n := (PrecisionExtension.first _ _).trans hn
    have hnFamily : PrecisionExtension (family.modulus (p + 1)) n := (PrecisionExtension.second _ _).trans hn
    let response := (p + 3) + convergence.threshold (p + 1)
    have source := convergence.near (p + 1) n n response hnFamily hnPrecision (PrecisionExtension.second _ _)
    have compared := normalizedEquivalentNear (morphismNumerical f value).symm (p + 1) response s
      (PrecisionExtension.first _ _) hs
    exact Near.ofSameLeft (Target.core.dyadicExact _ _) (Near.compose source compared)

def mapProducedLimit {Source Target : PresentedDyadicCompletionObject}
    (f : CompletionMorphism Source Target) (family : PresentedFamily Source.core) :
    Target.core.Equivalent (f.map (Source.completion.complete family).value)
      (Target.completion.complete (diagonalTransportFamily Source.core Target.core family)).value :=
  Target.core.equivalentSymm ((Target.completion.complete _).unique _
    (preservePresentedLimit f (Source.completion.complete family).convergence))

def carrierCompletionObject (P : CircularPresentation) (baseDepth : Nat) : PresentedDyadicCompletionObject :=
  ⟨carrierPresentedCore, carrierCompletionStructure P baseDepth⟩

def fromTarget (Target : PresentedDyadicStructure) (y : Target.Carrier) : EffectiveCauchyReal.Carrier :=
  numericalCarrier Target.toPresentedDyadicData y

def toTarget (Target : PresentedDyadicCompletionObject) (x : EffectiveCauchyReal.Carrier) : Target.core.Carrier :=
  (Target.completion.complete (presentCarrierFamily Target.core x)).value

def fromToTarget (Target : PresentedDyadicCompletionObject) (x : EffectiveCauchyReal.Carrier) :
    EffectiveCauchyReal.Equivalent (fromTarget Target.core (toTarget Target x)) x :=
  presentedCarrierEquivalent Target.core x _ (Target.completion.complete _).convergence

def toFromTarget (Target : PresentedDyadicCompletionObject) (y : Target.core.Carrier) :
    Target.core.Equivalent (toTarget Target (fromTarget Target.core y)) y :=
  (Target.completion.complete (ownFamily Target.core y)).unique y (selfConvergence Target.core y)

def fromTargetDyadic (Target : PresentedDyadicStructure) (code : SignedDyadicCode) :
    EffectiveCauchyReal.Equivalent (fromTarget Target (Target.dyadic code)) (dyadicCarrier code) where
  firstThreshold p := p
  secondThreshold p := p
  near p r s hr hs := ((Target.dyadicExact _ _).trans
    (EffectiveDyadicPresentation.constantApproximationSameValue code s).symm).toNear p

def reverseMorphism (Target : PresentedDyadicCompletionObject) (P : CircularPresentation) (baseDepth : Nat) :
    CompletionMorphism Target (carrierCompletionObject P baseDepth) where
  map := fromTarget Target.core
  mapEquivalent := equivalentToCarrier
  mapDyadic := fromTargetDyadic Target.core
  presents y := selfConvergence carrierPresentedCore (fromTarget Target.core y)

def toTargetPreservesEquivalent (Target : PresentedDyadicCompletionObject)
    {x y : EffectiveCauchyReal.Carrier} (same : EffectiveCauchyReal.Equivalent x y) :
    Target.core.Equivalent (toTarget Target x) (toTarget Target y) :=
  carrierToEquivalent ((fromToTarget Target x).trans (same.trans (fromToTarget Target y).symm))

def toTargetReflectsEquivalent (Target : PresentedDyadicCompletionObject)
    {x y : EffectiveCauchyReal.Carrier} (same : Target.core.Equivalent (toTarget Target x) (toTarget Target y)) :
    EffectiveCauchyReal.Equivalent x y :=
  (fromToTarget Target x).symm.trans ((equivalentToCarrier same).trans (fromToTarget Target y))

/-- A finer own family used solely to derive equality by limit uniqueness.
Its terms still are the element's actual codes; its strengthened outer modulus
is explicit and does not replace any operation's canonical family. -/
def comparisonFamily (C : PresentedDyadicStructure) (x : C.Carrier) : PresentedFamily C where
  terms n := C.dyadic (C.approximation x n)
  modulus p := C.modulus x (p + 2)
  modulusMonotone extension := C.modulusMonotone x (extension.succ.succ)
  cauchy p n m r s hn hm hr hs := Near.ofSameLeft (C.dyadicExact _ _)
    (Near.ofSameRight (C.coherent x p n m
      ((C.modulusMonotone x ⟨2, rfl⟩).trans hn) ((C.modulusMonotone x ⟨2, rfl⟩).trans hm)) (C.dyadicExact _ _).symm)

def comparisonSelfConverges (C : PresentedDyadicStructure) (x : C.Carrier) : Converges C (comparisonFamily C x) x where
  threshold p := p
  near p n r s hn hr hs := Near.ofSameLeft (C.dyadicExact _ _)
    (C.coherent x p n (C.modulus x s) ((C.modulusMonotone x ⟨2, rfl⟩).trans hn) (C.modulusMonotone x hs))

def comparisonOtherConverges (C : PresentedDyadicStructure) {x y : C.Carrier}
    (same : EffectiveCauchyReal.Equivalent (numericalCarrier C.toPresentedDyadicData x)
      (numericalCarrier C.toPresentedDyadicData y)) : Converges C (comparisonFamily C x) y where
  threshold p := p + 2
  near := by
    intro p n r s hn hr hs
    let first := C.modulus x (p + 2) + same.firstThreshold (p + 2)
    let second := C.modulus y (p + 2) + same.secondThreshold (p + 2)
    have source := C.coherent x (p + 2) n first hn (PrecisionExtension.first _ _)
    have equivalent := same.near (p + 2) first second (PrecisionExtension.second _ _) (PrecisionExtension.second _ _)
    have target := C.coherent y (p + 2) second (C.modulus y s) (PrecisionExtension.first _ _) (C.modulusMonotone y hs)
    exact Near.ofSameLeft (C.dyadicExact _ _) (Near.compose (Near.compose source equivalent)
      (target.weaken (PrecisionExtension.next (p + 1))))

def equivalentByLimitUniqueness (Target : PresentedDyadicCompletionObject) {x y : Target.core.Carrier}
    (same : EffectiveCauchyReal.Equivalent (fromTarget Target.core x) (fromTarget Target.core y)) :
    Target.core.Equivalent x y :=
  let produced := Target.completion.complete (comparisonFamily Target.core x)
  Target.core.equivalentTrans (Target.core.equivalentSymm (produced.unique x (comparisonSelfConverges Target.core x)))
    (produced.unique y (comparisonOtherConverges Target.core same))

end RelationalPerimeter.Constitution.Reals.DyadicCompletionCharacterization

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Constitution.Reals.DyadicCompletionCharacterization.CompletionMorphism
#print axioms RelationalPerimeter.Constitution.Reals.DyadicCompletionCharacterization.PointwiseEquivalent
#print axioms RelationalPerimeter.Constitution.Reals.DyadicCompletionCharacterization.mapAsProducedLimit
#print axioms RelationalPerimeter.Constitution.Reals.DyadicCompletionCharacterization.morphismNumerical
#print axioms RelationalPerimeter.Constitution.Reals.DyadicCompletionCharacterization.constantPresentationConvergence
#print axioms RelationalPerimeter.Constitution.Reals.DyadicCompletionCharacterization.comparisonMorphism
#print axioms RelationalPerimeter.Constitution.Reals.DyadicCompletionCharacterization.comparisonUnique
#print axioms RelationalPerimeter.Constitution.Reals.DyadicCompletionCharacterization.morphismsPointwiseEquivalent
#print axioms RelationalPerimeter.Constitution.Reals.DyadicCompletionCharacterization.preservePresentedLimit
#print axioms RelationalPerimeter.Constitution.Reals.DyadicCompletionCharacterization.mapProducedLimit
#print axioms RelationalPerimeter.Constitution.Reals.DyadicCompletionCharacterization.carrierCompletionObject
#print axioms RelationalPerimeter.Constitution.Reals.DyadicCompletionCharacterization.fromTarget
#print axioms RelationalPerimeter.Constitution.Reals.DyadicCompletionCharacterization.toTarget
#print axioms RelationalPerimeter.Constitution.Reals.DyadicCompletionCharacterization.fromToTarget
#print axioms RelationalPerimeter.Constitution.Reals.DyadicCompletionCharacterization.toFromTarget
#print axioms RelationalPerimeter.Constitution.Reals.DyadicCompletionCharacterization.fromTargetDyadic
#print axioms RelationalPerimeter.Constitution.Reals.DyadicCompletionCharacterization.reverseMorphism
#print axioms RelationalPerimeter.Constitution.Reals.DyadicCompletionCharacterization.toTargetPreservesEquivalent
#print axioms RelationalPerimeter.Constitution.Reals.DyadicCompletionCharacterization.toTargetReflectsEquivalent
#print axioms RelationalPerimeter.Constitution.Reals.DyadicCompletionCharacterization.comparisonFamily
#print axioms RelationalPerimeter.Constitution.Reals.DyadicCompletionCharacterization.comparisonSelfConverges
#print axioms RelationalPerimeter.Constitution.Reals.DyadicCompletionCharacterization.comparisonOtherConverges
#print axioms RelationalPerimeter.Constitution.Reals.DyadicCompletionCharacterization.equivalentByLimitUniqueness
/- AXIOM_AUDIT_END -/
