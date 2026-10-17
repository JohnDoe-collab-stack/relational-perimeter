import RelationalPerimeter.Constitution.Reals.DyadicMultiplication

set_option autoImplicit false
set_option linter.unusedVariables false

/-!
# Finite directed dyadic margins

These are numerical certificates for codes already obtained. They are not
operational apartness witnesses: those must additionally own their executions.
-/
namespace RelationalPerimeter.Constitution.Reals

structure DirectedUpper (precision : Nat) (left right : SignedDyadicCode) where
  scale : CommonScale left right
  precisionExtra : Nat
  precisionExact : precision + precisionExtra = scale.common
  bound : liftedPositive left scale.leftExtra + liftedNegative right scale.rightExtra ≤
    liftedPositive right scale.rightExtra + liftedNegative left scale.leftExtra + powerOfTwo precisionExtra

namespace DirectedUpper

def ofNear {p : Nat} {left right : SignedDyadicCode} (near : Near p left right) : DirectedUpper p left right :=
  ⟨near.scale, near.precisionExtra, near.precisionExact, near.leftBound⟩

def liftCommon {p : Nat} {left right : SignedDyadicCode} (upper : DirectedUpper p left right) (extra : Nat) :
    DirectedUpper p left right where
  scale := ⟨upper.scale.common + extra, upper.scale.leftExtra + extra, upper.scale.rightExtra + extra,
    (Nat.add_assoc _ _ _).symm.trans (congrArg (fun n => n + extra) upper.scale.leftExact),
    (Nat.add_assoc _ _ _).symm.trans (congrArg (fun n => n + extra) upper.scale.rightExact)⟩
  precisionExtra := upper.precisionExtra + extra
  precisionExact := (Nat.add_assoc _ _ _).symm.trans (congrArg (fun n => n + extra) upper.precisionExact)
  bound := by
    have h := scaleSignedBound upper.bound extra
    rw [liftedPositive_addSteps, liftedNegative_addSteps,
      liftedPositive_addSteps, liftedNegative_addSteps, powerOfTwo_add]
    exact h

def weaken {coarse fine : Nat} {left right : SignedDyadicCode}
    (extension : PrecisionExtension coarse fine) (upper : DirectedUpper fine left right) :
    DirectedUpper coarse left right where
  scale := upper.scale
  precisionExtra := upper.precisionExtra + extension.extra
  precisionExact := (Nat.add_assoc _ _ _).symm.trans
    ((addSwapMiddle _ _ _).trans (congrArg (fun n => n + upper.precisionExtra) extension.exact) |>.trans upper.precisionExact)
  bound := Nat.le_trans upper.bound (Nat.add_le_add (Nat.le_refl _) (powerOfTwo_extension _ _))

/-- Two one-sided errors consume exactly one precision bit. -/
def compose {p : Nat} {left middle right : SignedDyadicCode}
    (first : DirectedUpper (p + 1) left middle) (second : DirectedUpper (p + 1) middle right) :
    DirectedUpper p left right := by
  let a := first.liftCommon second.scale.common
  let b := second.liftCommon first.scale.common
  have common : a.scale.common = b.scale.common := Nat.add_comm _ _
  have middleExtra : a.scale.rightExtra = b.scale.leftExtra :=
    addLeftCancel (a.scale.rightExact.trans (common.trans b.scale.leftExact.symm))
  have tolerance : a.precisionExtra = b.precisionExtra :=
    addLeftCancel (a.precisionExact.trans (common.trans b.precisionExact.symm))
  have h := b.bound
  rw [← middleExtra, ← tolerance] at h
  refine ⟨⟨a.scale.common, a.scale.leftExtra, b.scale.rightExtra,
    a.scale.leftExact, b.scale.rightExact.trans common.symm⟩,
    a.precisionExtra + 1, (Near.succPrecision _ _).symm.trans a.precisionExact, ?_⟩
  exact composeSignedBound a.bound h

end DirectedUpper

/-- Strict signed margin greater than one full tolerance at the recorded scale. -/
structure StrictSeparation (precision : Nat) (left right : SignedDyadicCode) where
  scale : CommonScale left right
  precisionExtra : Nat
  precisionExact : precision + precisionExtra = scale.common
  strict : liftedPositive left scale.leftExtra + liftedNegative right scale.rightExtra + powerOfTwo precisionExtra <
    liftedPositive right scale.rightExtra + liftedNegative left scale.leftExtra

theorem scaleNat_strict {a b : Nat} (bound : a < b) (extra : Nat) : scaleNat a extra < scaleNat b extra := by
  induction extra with
  | zero => exact bound
  | succ extra ih => exact Nat.add_lt_add ih ih

namespace StrictSeparation

def liftCommon {p : Nat} {left right : SignedDyadicCode}
    (gap : StrictSeparation p left right) (extra : Nat) : StrictSeparation p left right where
  scale := ⟨gap.scale.common + extra, gap.scale.leftExtra + extra, gap.scale.rightExtra + extra,
    (Nat.add_assoc _ _ _).symm.trans (congrArg (fun n => n + extra) gap.scale.leftExact),
    (Nat.add_assoc _ _ _).symm.trans (congrArg (fun n => n + extra) gap.scale.rightExact)⟩
  precisionExtra := gap.precisionExtra + extra
  precisionExact := (Nat.add_assoc _ _ _).symm.trans (congrArg (fun n => n + extra) gap.precisionExact)
  strict := by
    have h := scaleNat_strict gap.strict extra
    rw [scaleNat_additive, scaleNat_additive, scaleNat_additive] at h
    rw [liftedPositive_addSteps, liftedNegative_addSteps,
      liftedPositive_addSteps, liftedNegative_addSteps, powerOfTwo_add]
    exact h

def refuteUpper {p : Nat} {left right : SignedDyadicCode}
    (gap : StrictSeparation p left right) (upper : DirectedUpper p right left) : Empty := by
  let a := gap.liftCommon upper.scale.common
  let b := upper.liftCommon gap.scale.common
  have common : a.scale.common = b.scale.common := Nat.add_comm _ _
  have leftExtra : a.scale.leftExtra = b.scale.rightExtra :=
    addLeftCancel (a.scale.leftExact.trans (common.trans b.scale.rightExact.symm))
  have rightExtra : a.scale.rightExtra = b.scale.leftExtra :=
    addLeftCancel (a.scale.rightExact.trans (common.trans b.scale.leftExact.symm))
  have tolerance : a.precisionExtra = b.precisionExtra :=
    addLeftCancel (a.precisionExact.trans (common.trans b.precisionExact.symm))
  have h := b.bound
  rw [← leftExtra, ← rightExtra, ← tolerance] at h
  exact (Nat.not_lt_of_ge h a.strict).elim

def negReverse {p : Nat} {left right : SignedDyadicCode}
    (gap : StrictSeparation p left right) : StrictSeparation p right.neg left.neg where
  scale := ⟨gap.scale.common, gap.scale.rightExtra, gap.scale.leftExtra,
    gap.scale.rightExact, gap.scale.leftExact⟩
  precisionExtra := gap.precisionExtra
  precisionExact := gap.precisionExact
  strict := by
    change liftedNegative right gap.scale.rightExtra + liftedPositive left gap.scale.leftExtra + _ <
      liftedNegative left gap.scale.leftExtra + liftedPositive right gap.scale.rightExtra
    rw [Nat.add_comm (liftedNegative right _) (liftedPositive left _),
      Nat.add_comm (liftedNegative left _) (liftedPositive right _)]
    exact gap.strict

/-- A strict forward gap supplies a forward upper bound at any tolerance;
only scale extension is performed, never a converse directed bound. -/
def forwardUpper {p : Nat} {left right : SignedDyadicCode}
    (gap : StrictSeparation p left right) (precision : Nat) : DirectedUpper precision left right where
  scale := (gap.liftCommon precision).scale
  precisionExtra := gap.scale.common
  precisionExact := Nat.add_comm _ _
  bound := by
    have exactBound := Nat.le_trans (Nat.le_add_right _ _) (Nat.le_of_lt gap.strict)
    have h := scaleNat_monotone exactBound precision
    rw [scaleNat_additive, scaleNat_additive] at h
    change liftedPositive left (gap.scale.leftExtra + precision) +
      liftedNegative right (gap.scale.rightExtra + precision) ≤
        liftedPositive right (gap.scale.rightExtra + precision) +
          liftedNegative left (gap.scale.leftExtra + precision) + powerOfTwo gap.scale.common
    rw [liftedPositive_addSteps, liftedNegative_addSteps,
      liftedPositive_addSteps, liftedNegative_addSteps]
    exact Nat.le_trans h (Nat.le_add_right _ _)

end StrictSeparation

def finiteComparisonScale (p : Nat) (left right : SignedDyadicCode) : CommonScale left right :=
  ⟨left.scale + right.scale + p, right.scale + p, left.scale + p,
    (Nat.add_assoc _ _ _).symm,
    (Nat.add_assoc _ _ _).symm.trans (congrArg (fun n => n + p) (Nat.add_comm _ _))⟩

/-- Failure is a one-sided bound for these two finite codes only. -/
def inspectGap (p : Nat) (left right : SignedDyadicCode) :
    StrictSeparation p left right ⊕ DirectedUpper p right left :=
  let scale := finiteComparisonScale p left right
  let extra := left.scale + right.scale
  if h : liftedPositive left scale.leftExtra + liftedNegative right scale.rightExtra + powerOfTwo extra <
      liftedPositive right scale.rightExtra + liftedNegative left scale.leftExtra then
    .inl ⟨scale, extra, Nat.add_comm _ _, h⟩
  else .inr ⟨scale.symm, extra, Nat.add_comm _ _, Nat.le_of_not_lt h⟩

/-- The exact three-error consumption used by numerical transport: three
p+2 bounds compose to a p bound, contradicting the original strict margin. -/
def strengthenSeparation {p : Nat} {a b c d : SignedDyadicCode}
    (gap : StrictSeparation p a b) (left : Near (p + 2) a c) (right : Near (p + 2) b d) :
    StrictSeparation (p + 2) c d :=
  match inspectGap (p + 2) c d with
  | .inl result => result
  | .inr upper =>
      (gap.refuteUpper (DirectedUpper.compose
        (DirectedUpper.compose (DirectedUpper.ofNear right) upper)
        ((DirectedUpper.ofNear left.symm).weaken (PrecisionExtension.next (p + 1))))).elim

end RelationalPerimeter.Constitution.Reals

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Constitution.Reals.DirectedUpper
#print axioms RelationalPerimeter.Constitution.Reals.DirectedUpper.ofNear
#print axioms RelationalPerimeter.Constitution.Reals.DirectedUpper.liftCommon
#print axioms RelationalPerimeter.Constitution.Reals.DirectedUpper.weaken
#print axioms RelationalPerimeter.Constitution.Reals.DirectedUpper.compose
#print axioms RelationalPerimeter.Constitution.Reals.StrictSeparation
#print axioms RelationalPerimeter.Constitution.Reals.scaleNat_strict
#print axioms RelationalPerimeter.Constitution.Reals.StrictSeparation.liftCommon
#print axioms RelationalPerimeter.Constitution.Reals.StrictSeparation.refuteUpper
#print axioms RelationalPerimeter.Constitution.Reals.StrictSeparation.negReverse
#print axioms RelationalPerimeter.Constitution.Reals.StrictSeparation.forwardUpper
#print axioms RelationalPerimeter.Constitution.Reals.finiteComparisonScale
#print axioms RelationalPerimeter.Constitution.Reals.inspectGap
#print axioms RelationalPerimeter.Constitution.Reals.strengthenSeparation
/- AXIOM_AUDIT_END -/
