import RelationalPerimeter.Constitution.Reals.PresentedDyadicCompletion
import RelationalPerimeter.Constitution.Reals.RelationalRealOrder
import RelationalPerimeter.Constitution.Reals.DyadicOrderTransport

set_option autoImplicit false
set_option linter.unusedVariables false

namespace RelationalPerimeter.Constitution.Reals
open RelationalRealAddition RelationalRealOrder

/-- Three comparisons at p+2, with precisely two composition losses. The
raw intermediate indices exceed both the module and the independent threshold. -/
def normalizedEquivalentNear {x y : EffectiveCauchyReal.Carrier}
    (same : EffectiveCauchyReal.Equivalent x y) (p leftIndex rightIndex : Nat)
    (leftBeyond : PrecisionExtension (p + 2) leftIndex)
    (rightBeyond : PrecisionExtension (p + 2) rightIndex) :
    Near p ((EffectiveCauchyReal.toPresentation x).approximation leftIndex)
      ((EffectiveCauchyReal.toPresentation y).approximation rightIndex) := by
  let leftRaw := x.modulus (p + 2) + same.firstThreshold (p + 2)
  let rightRaw := y.modulus (p + 2) + same.secondThreshold (p + 2)
  have source := x.cauchy (p + 2) (x.modulus leftIndex) leftRaw
    (x.modulusMonotone leftBeyond) (PrecisionExtension.first _ _)
  have equivalent := same.near (p + 2) leftRaw rightRaw
    (PrecisionExtension.second _ _) (PrecisionExtension.second _ _)
  have target := y.cauchy (p + 2) rightRaw (y.modulus rightIndex)
    (PrecisionExtension.first _ _) (y.modulusMonotone rightBeyond)
  exact Near.compose (Near.compose source equivalent)
    (target.weaken (PrecisionExtension.next (p + 1)))

def addCarrierCongr {x y c d : EffectiveCauchyReal.Carrier}
    (left : EffectiveCauchyReal.Equivalent x c) (right : EffectiveCauchyReal.Equivalent y d) :
    EffectiveCauchyReal.Equivalent (addCarrier x y) (addCarrier c d) where
  firstThreshold p := p + 3
  secondThreshold p := p + 3
  near p r s hr hs :=
    Near.add (normalizedEquivalentNear left (p + 1) _ _
      (hr.trans (PrecisionExtension.next r)) (hs.trans (PrecisionExtension.next s)))
      (normalizedEquivalentNear right (p + 1) _ _
        (hr.trans (PrecisionExtension.next r)) (hs.trans (PrecisionExtension.next s)))

def negCarrierCongr {x y : EffectiveCauchyReal.Carrier}
    (same : EffectiveCauchyReal.Equivalent x y) :
    EffectiveCauchyReal.Equivalent (negCarrier x) (negCarrier y) where
  firstThreshold p := p + 2
  secondThreshold p := p + 2
  near p r s hr hs := (normalizedEquivalentNear same p r s hr hs).neg

def carrierMulComparisonPrecisions (x y c d : EffectiveCauchyReal.Carrier) (p : Nat) : List Nat :=
  let rightBound := probeAmplitude ((EffectiveCauchyReal.toPresentation y).approximation 0)
  let leftBound := probeAmplitude ((EffectiveCauchyReal.toPresentation c).approximation 0)
  [p + 1 + rightBound + 2, p + 1 + leftBound + 2]

/-- Each side has its own probes. Crossed amplitudes and the full pool of
normalization losses are required; no probes are identified. -/
def mulCarrierCongr {x y c d : EffectiveCauchyReal.Carrier}
    (left : EffectiveCauchyReal.Equivalent x c) (right : EffectiveCauchyReal.Equivalent y d) :
    EffectiveCauchyReal.Equivalent (mulCarrier x y) (mulCarrier c d) where
  firstThreshold p := precisionPool (carrierMulComparisonPrecisions x y c d p)
  secondThreshold p := precisionPool (carrierMulComparisonPrecisions x y c d p)
  near := by
    intro p r s hr hs
    let pool := carrierMulComparisonPrecisions x y c d p
    have first : PrecisionMember (p + 1 + probeAmplitude
        ((EffectiveCauchyReal.toPresentation y).approximation 0) + 2) pool := .here
    have second : PrecisionMember (p + 1 + probeAmplitude
        ((EffectiveCauchyReal.toPresentation c).approximation 0) + 2) pool := .there .here
    exact Near.mul
      (normalizedEquivalentNear left _ _ _
        ((first.extension.trans hr).trans (PrecisionExtension.refine r _))
        ((first.extension.trans hs).trans (PrecisionExtension.refine s _)))
      (normalizedEquivalentNear right _ _ _
        ((second.extension.trans hr).trans (PrecisionExtension.refine r _))
        ((second.extension.trans hs).trans (PrecisionExtension.refine s _)))
      (presentationAmplitude (EffectiveCauchyReal.toPresentation y) _)
      (presentationAmplitude (EffectiveCauchyReal.toPresentation c) _)

def transportCarrierOrder {a b c d : EffectiveCauchyReal.Carrier}
    (origin : CarrierOrder a b) (left : EffectiveCauchyReal.Equivalent a c)
    (right : EffectiveCauchyReal.Equivalent b d) : CarrierOrder c d := by
  let p := origin.accuracy
  let ar := a.modulus (p + 3) + left.firstThreshold (p + 3)
  let cr := c.modulus (p + 3) + left.secondThreshold (p + 3)
  let br := b.modulus (p + 3) + right.firstThreshold (p + 3)
  let dr := d.modulus (p + 3) + right.secondThreshold (p + 3)
  have l1 := a.cauchy (p + 3) (a.modulus origin.response) ar
    (a.modulusMonotone origin.beyond) (PrecisionExtension.first _ _)
  have l2 := left.near (p + 3) ar cr (PrecisionExtension.second _ _) (PrecisionExtension.second _ _)
  have l3 := c.cauchy (p + 3) cr (c.modulus (p + 5)) (PrecisionExtension.first _ _)
    (c.modulusMonotone ⟨2, rfl⟩)
  have r1 := b.cauchy (p + 3) (b.modulus origin.response) br
    (b.modulusMonotone origin.beyond) (PrecisionExtension.first _ _)
  have r2 := right.near (p + 3) br dr (PrecisionExtension.second _ _) (PrecisionExtension.second _ _)
  have r3 := d.cauchy (p + 3) dr (d.modulus (p + 5)) (PrecisionExtension.first _ _)
    (d.modulusMonotone ⟨2, rfl⟩)
  exact ⟨p + 2, p + 5, .refl _,
    strengthenSeparationThreeLinks origin.separation l1 l2 l3 r1 r2 r3⟩

def transportCarrierApartness {a b c d : EffectiveCauchyReal.Carrier}
    (origin : CarrierApartness a b) (left : EffectiveCauchyReal.Equivalent a c)
    (right : EffectiveCauchyReal.Equivalent b d) : CarrierApartness c d :=
  match origin with
  | .inl forward => .inl (transportCarrierOrder forward left right)
  | .inr backward => .inr (transportCarrierOrder backward right left)

end RelationalPerimeter.Constitution.Reals

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Constitution.Reals.normalizedEquivalentNear
#print axioms RelationalPerimeter.Constitution.Reals.addCarrierCongr
#print axioms RelationalPerimeter.Constitution.Reals.negCarrierCongr
#print axioms RelationalPerimeter.Constitution.Reals.carrierMulComparisonPrecisions
#print axioms RelationalPerimeter.Constitution.Reals.mulCarrierCongr
#print axioms RelationalPerimeter.Constitution.Reals.transportCarrierOrder
#print axioms RelationalPerimeter.Constitution.Reals.transportCarrierApartness
/- AXIOM_AUDIT_END -/
