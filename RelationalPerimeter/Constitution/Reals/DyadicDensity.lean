import RelationalPerimeter.Constitution.Reals.DyadicOrderedField

set_option autoImplicit false
set_option linter.unusedVariables false

namespace RelationalPerimeter.Constitution.Reals.DyadicDensity

theorem halfMarginLeft {a an b bn tolerance : Nat} (gap : a + bn + tolerance < b + an) :
    (a + a) + (an + bn) + tolerance < (a + b) + (an + an) := by
  have bound := translateSignedStrict gap a an
  rw [Nat.add_comm bn an, Nat.add_comm b a] at bound
  exact bound

theorem halfMarginRight {a an b bn tolerance : Nat} (gap : a + bn + tolerance < b + an) :
    (a + b) + (bn + bn) + tolerance < (b + b) + (an + bn) := by
  exact translateSignedStrict gap b bn

/-- The common scale belongs to the received positive finite margin. -/
def midpointCode {p : Nat} {a b : SignedDyadicCode} (gap : StrictSeparation p a b) : SignedDyadicCode :=
  ⟨liftedPositive a gap.scale.leftExtra + liftedPositive b gap.scale.rightExtra,
    liftedNegative a gap.scale.leftExtra + liftedNegative b gap.scale.rightExtra, gap.scale.common + 1⟩

structure Bisection {p : Nat} {a b : SignedDyadicCode} (gap : StrictSeparation p a b) where
  private mk ::
  code : SignedDyadicCode
  codeExact : code = midpointCode gap
  leftMargin : StrictSeparation (p + 1) a code
  rightMargin : StrictSeparation (p + 1) code b

def bisect {p : Nat} {a b : SignedDyadicCode} (gap : StrictSeparation p a b) : Bisection gap := by
  let code := midpointCode gap
  have precision : (p + 1) + gap.precisionExtra = gap.scale.common + 1 :=
    (addSwapMiddle _ _ _).trans (congrArg (fun n => n + 1) gap.precisionExact)
  have left : StrictSeparation (p + 1) a code := by
    refine ⟨⟨gap.scale.common + 1, gap.scale.leftExtra + 1, 0,
      (Nat.add_assoc _ _ _).symm.trans (congrArg (fun n => n + 1) gap.scale.leftExact), rfl⟩,
      gap.precisionExtra, precision, ?_⟩
    change liftedPositive a (gap.scale.leftExtra + 1) +
      (liftedNegative a gap.scale.leftExtra + liftedNegative b gap.scale.rightExtra) + powerOfTwo gap.precisionExtra <
      (liftedPositive a gap.scale.leftExtra + liftedPositive b gap.scale.rightExtra) +
        liftedNegative a (gap.scale.leftExtra + 1)
    rw [liftedPositive_addSteps, liftedNegative_addSteps]
    exact halfMarginLeft gap.strict
  have right : StrictSeparation (p + 1) code b := by
    refine ⟨⟨gap.scale.common + 1, 0, gap.scale.rightExtra + 1, rfl,
      (Nat.add_assoc _ _ _).symm.trans (congrArg (fun n => n + 1) gap.scale.rightExact)⟩,
      gap.precisionExtra, precision, ?_⟩
    change (liftedPositive a gap.scale.leftExtra + liftedPositive b gap.scale.rightExtra) +
      liftedNegative b (gap.scale.rightExtra + 1) + powerOfTwo gap.precisionExtra <
      liftedPositive b (gap.scale.rightExtra + 1) +
        (liftedNegative a gap.scale.leftExtra + liftedNegative b gap.scale.rightExtra)
    rw [liftedNegative_addSteps, liftedPositive_addSteps]
    exact halfMarginRight gap.strict
  exact ⟨code, rfl, left, right⟩

def naturalCode (n : Nat) : SignedDyadicCode := ⟨n, 0, 0⟩
def negativeNaturalCode (n : Nat) : SignedDyadicCode := ⟨0, n, 0⟩

theorem positiveComponentBound (positive negative scale : Nat) :
    positive + powerOfTwo scale < scaleNat (positive + 2) scale + negative := by
  have lifted : positive ≤ scaleNat positive scale := by
    have bound := scaleNat_extension positive 0 scale
    rw [Nat.zero_add] at bound
    exact bound
  have strict : powerOfTwo scale < scaleNat 2 scale := by
    change powerOfTwo scale < scaleNat (1 + 1) scale
    rw [scaleNat_additive]
    exact Nat.lt_add_of_pos_right (DyadicReciprocal.power_positive scale)
  calc
    positive + powerOfTwo scale ≤ scaleNat positive scale + powerOfTwo scale := Nat.add_le_add_right lifted _
    _ < scaleNat positive scale + scaleNat 2 scale := Nat.add_lt_add_left strict _
    _ = scaleNat (positive + 2) scale := (scaleNat_additive _ _ _).symm
    _ ≤ scaleNat (positive + 2) scale + negative := Nat.le_add_right _ _

structure NaturalBounds (code : SignedDyadicCode) where
  private mk ::
  upper : Nat
  lower : Nat
  upperExact : upper = code.positive + 2
  lowerExact : lower = code.negative + 2
  upperMargin : StrictSeparation 0 code (naturalCode upper)
  lowerMargin : StrictSeparation 0 (negativeNaturalCode lower) code

/-- Finite coarse-code bounds only, not bounds on future code components. -/
def naturalBounds (code : SignedDyadicCode) : NaturalBounds code := by
  let upper := code.positive + 2
  let lower := code.negative + 2
  have hi : StrictSeparation 0 code (naturalCode upper) := by
    refine ⟨⟨code.scale, 0, code.scale, rfl, Nat.zero_add _⟩, code.scale, Nat.zero_add _, ?_⟩
    change code.positive + scaleNat 0 code.scale + powerOfTwo code.scale <
      scaleNat upper code.scale + code.negative
    rw [SignedDyadicCode.scaleNat_zero, Nat.add_zero]
    exact positiveComponentBound _ _ _
  have lo : StrictSeparation 0 (negativeNaturalCode lower) code := by
    refine ⟨⟨code.scale, code.scale, 0, Nat.zero_add _, rfl⟩, code.scale, Nat.zero_add _, ?_⟩
    change scaleNat 0 code.scale + code.negative + powerOfTwo code.scale <
      code.positive + scaleNat lower code.scale
    rw [SignedDyadicCode.scaleNat_zero, Nat.zero_add, Nat.add_comm code.positive]
    exact positiveComponentBound _ _ _
  exact ⟨upper, lower, rfl, rfl, hi, lo⟩

end RelationalPerimeter.Constitution.Reals.DyadicDensity

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Constitution.Reals.DyadicDensity.halfMarginLeft
#print axioms RelationalPerimeter.Constitution.Reals.DyadicDensity.halfMarginRight
#print axioms RelationalPerimeter.Constitution.Reals.DyadicDensity.midpointCode
#print axioms RelationalPerimeter.Constitution.Reals.DyadicDensity.Bisection
#print axioms RelationalPerimeter.Constitution.Reals.DyadicDensity.bisect
#print axioms RelationalPerimeter.Constitution.Reals.DyadicDensity.naturalCode
#print axioms RelationalPerimeter.Constitution.Reals.DyadicDensity.negativeNaturalCode
#print axioms RelationalPerimeter.Constitution.Reals.DyadicDensity.positiveComponentBound
#print axioms RelationalPerimeter.Constitution.Reals.DyadicDensity.NaturalBounds
#print axioms RelationalPerimeter.Constitution.Reals.DyadicDensity.naturalBounds
/- AXIOM_AUDIT_END -/
