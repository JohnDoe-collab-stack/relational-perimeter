import RelationalPerimeter.Constitution.Reals.RelationalRealOrder
import RelationalPerimeter.Constitution.Reals.DyadicReciprocal

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Executed domain of the reciprocal

The direction, bound and source successor come from an owned apartness
packet. Every new source Step receives a quantitative certificate by
transport from that very packet; storing the old witness alone is not enough.
-/
namespace RelationalPerimeter.Constitution.Reals.ReciprocalDomain
open StrongPerimetralTurning RuntimeCorrespondence HeterogeneousRealRuntime RelationalRealAddition
open RelationalRealOrder DyadicReciprocal
variable {P : CircularPresentation} {baseDepth : Nat}

def direction {source : Real P baseDepth} : Apartness source (zero P baseDepth) → Direction
  | .forward _ => .negative
  | .backward _ => .positive

def away {source : Real P baseDepth} : Apartness source (zero P baseDepth) → Nat
  | .forward order => order.accuracy + 2
  | .backward order => order.accuracy + 2

def sourceSuccessor {source : Real P baseDepth} : Apartness source (zero P baseDepth) → (environment source).Archive
  | .forward order => order.pair.left.next
  | .backward order => order.pair.right.next

def zeroStepSameValue {archive : (environment (zero P baseDepth)).Archive} {p : Nat}
    (step : Step (environment (zero P baseDepth)) archive p) : SameValue step.code SignedDyadicCode.zero := by
  rw [currentReadout (zero P baseDepth) _ _ step]
  exact constant_readout _ _

def nonzero {source : Real P baseDepth} (witness : Apartness source (zero P baseDepth))
    {archive : (environment source).Archive} {precision : Nat}
    (step : Step (environment source) archive precision) (beyond : PrecisionExtension (away witness) precision) :
    NonzeroCode (direction witness) (away witness) step.code := by
  cases witness with
  | forward order =>
      let sourceNear := (coherent source).near (order.accuracy + 2) _ _ order.pair.left step
        ((PrecisionExtension.next (order.accuracy + 2)).trans order.beyond) beyond
      let zeroNear := (zeroStepSameValue order.pair.right).toNear (order.accuracy + 2)
      exact fromNegativeMargin (strengthenSeparation order.separation sourceNear zeroNear)
  | backward order =>
      let zeroNear := (zeroStepSameValue order.pair.left).toNear (order.accuracy + 2)
      let sourceNear := (coherent source).near (order.accuracy + 2) _ _ order.pair.right step
        ((PrecisionExtension.next (order.accuracy + 2)).trans order.beyond) beyond
      exact fromPositiveMargin (strengthenSeparation order.separation zeroNear sourceNear)

end RelationalPerimeter.Constitution.Reals.ReciprocalDomain

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Constitution.Reals.ReciprocalDomain.direction
#print axioms RelationalPerimeter.Constitution.Reals.ReciprocalDomain.away
#print axioms RelationalPerimeter.Constitution.Reals.ReciprocalDomain.sourceSuccessor
#print axioms RelationalPerimeter.Constitution.Reals.ReciprocalDomain.zeroStepSameValue
#print axioms RelationalPerimeter.Constitution.Reals.ReciprocalDomain.nonzero
/- AXIOM_AUDIT_END -/
