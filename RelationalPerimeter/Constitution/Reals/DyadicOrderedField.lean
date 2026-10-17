import RelationalPerimeter.Constitution.Reals.DyadicReciprocal

set_option autoImplicit false
set_option linter.unusedVariables false

/-! Finite margin laws on already received signed codes. These certificates
cannot replace the owned native Steps of an operational order witness. -/
namespace RelationalPerimeter.Constitution.Reals

theorem replaceSignedStrict {a an m mn c cn tolerance : Nat}
    (same : a + mn = m + an) (bound : m + cn + tolerance < c + mn) :
    a + cn + tolerance < c + an := by
  apply Nat.lt_of_add_lt_add_right
  calc
    (a + cn + tolerance) + mn = (a + mn) + cn + tolerance := by
      rw [addSwapMiddle (a + cn) tolerance mn, addSwapMiddle a cn mn]
    _ = (m + an) + cn + tolerance := by rw [same]
    _ = (m + cn + tolerance) + an := by
      rw [addSwapMiddle m an cn, addSwapMiddle (m + cn) an tolerance]
    _ < (c + mn) + an := Nat.add_lt_add_right bound an
    _ = (c + an) + mn := addSwapMiddle _ _ _

theorem translateSignedStrict {a b c d tolerance : Nat}
    (bound : a + d + tolerance < c + b) (positive negative : Nat) :
    (a + positive) + (d + negative) + tolerance < (c + positive) + (b + negative) := by
  calc
    (a + positive) + (d + negative) + tolerance = (a + d + tolerance) + (positive + negative) :=
      (congrArg (fun n => n + tolerance) (addPairExchange _ _ _ _)).trans (addSwapMiddle _ _ _)
    _ < (c + b) + (positive + negative) := Nat.add_lt_add_right bound _
    _ = (c + positive) + (b + negative) := (addPairExchange _ _ _ _).symm

namespace StrictSeparation

def ofSameLeft {p : Nat} {a b c : SignedDyadicCode}
    (same : SameValue a b) (gap : StrictSeparation p b c) : StrictSeparation p a c := by
  let first := same.liftCommon gap.scale.common
  let second := gap.liftCommon same.scale.common
  have common : first.scale.common = second.scale.common := Nat.add_comm _ _
  have middle : first.scale.rightExtra = second.scale.leftExtra :=
    addLeftCancel (first.scale.rightExact.trans (common.trans second.scale.leftExact.symm))
  have bound := second.strict
  rw [← middle] at bound
  exact ⟨⟨first.scale.common, first.scale.leftExtra, second.scale.rightExtra,
    first.scale.leftExact, second.scale.rightExact.trans common.symm⟩,
    second.precisionExtra, second.precisionExact.trans common.symm, replaceSignedStrict first.exact bound⟩

def ofSameRight {p : Nat} {a b c : SignedDyadicCode}
    (gap : StrictSeparation p a b) (same : SameValue b c) : StrictSeparation p a c := by
  have result := (ofSameLeft same.symm.neg gap.negReverse).negReverse
  rw [SignedDyadicCode.neg_neg_exact, SignedDyadicCode.neg_neg_exact] at result
  exact result

def addRight {p : Nat} {a b : SignedDyadicCode} (gap : StrictSeparation p a b) (code : SignedDyadicCode) :
    StrictSeparation p (a.add code) (b.add code) := by
  let raised := gap.liftCommon code.scale
  refine ⟨⟨gap.scale.common + code.scale, gap.scale.leftExtra, gap.scale.rightExtra,
    (addSwapMiddle _ _ _).trans (congrArg (fun n => n + code.scale) gap.scale.leftExact),
    (addSwapMiddle _ _ _).trans (congrArg (fun n => n + code.scale) gap.scale.rightExact)⟩,
    gap.precisionExtra + code.scale,
    (Nat.add_assoc _ _ _).symm.trans (congrArg (fun n => n + code.scale) gap.precisionExact), ?_⟩
  dsimp only
  rw [SignedDyadicCode.add_positive, SignedDyadicCode.add_negative,
    SignedDyadicCode.add_positive, SignedDyadicCode.add_negative,
    gap.scale.leftExact, gap.scale.rightExact]
  have bound := raised.strict
  change liftedPositive a (gap.scale.leftExtra + code.scale) +
    liftedNegative b (gap.scale.rightExtra + code.scale) + powerOfTwo (gap.precisionExtra + code.scale) <
    liftedPositive b (gap.scale.rightExtra + code.scale) + liftedNegative a (gap.scale.leftExtra + code.scale) at bound
  rw [Nat.add_comm gap.scale.leftExtra code.scale, Nat.add_comm gap.scale.rightExtra code.scale] at bound
  exact translateSignedStrict bound _ _

def addLeft {p : Nat} {a b : SignedDyadicCode} (gap : StrictSeparation p a b) (code : SignedDyadicCode) :
    StrictSeparation p (code.add a) (code.add b) :=
  ofSameRight (ofSameLeft (SignedDyadicCode.add_comm _ _) (gap.addRight code)) (SignedDyadicCode.add_comm _ _)

end StrictSeparation

/-- A positive magnitude lower bound gives a strict margin with one guard bit.
This conversion is valid on non-normalized codes via its exact normalization. -/
def DyadicReciprocal.NonzeroCode.positiveMargin {away : Nat} {code : SignedDyadicCode}
    (certificate : DyadicReciprocal.NonzeroCode .positive away code) :
    StrictSeparation (away + 1) SignedDyadicCode.zero code := by
  let magnitude := DyadicReciprocal.magnitude .positive code
  have lower : powerOfTwo code.scale ≤ scaleNat magnitude away := by
    rw [scaleNat_eq_mul]
    exact certificate.lower
  have strict : powerOfTwo code.scale < scaleNat magnitude (away + 1) := by
    change powerOfTwo code.scale < scaleNat magnitude away + scaleNat magnitude away
    exact Nat.lt_of_lt_of_le (Nat.lt_add_of_pos_right (DyadicReciprocal.power_positive code.scale))
      (Nat.add_le_add lower lower)
  have normalized : StrictSeparation (away + 1) SignedDyadicCode.zero
      (DyadicReciprocal.signedCode .positive magnitude code.scale) :=
    ⟨⟨code.scale + (away + 1), code.scale + (away + 1), away + 1, Nat.zero_add _, rfl⟩,
      code.scale, Nat.add_comm _ _, by
        change scaleNat 0 _ + scaleNat 0 _ + _ < scaleNat magnitude (away + 1) + scaleNat 0 _
        rw [SignedDyadicCode.scaleNat_zero, SignedDyadicCode.scaleNat_zero, Nat.zero_add, Nat.add_zero]
        exact strict⟩
  exact normalized.ofSameRight certificate.normalized.symm

def DyadicReciprocal.NonzeroCode.mulPositive {a b : SignedDyadicCode} {pa pb : Nat}
    (first : DyadicReciprocal.NonzeroCode .positive pa a)
    (second : DyadicReciprocal.NonzeroCode .positive pb b) :
    StrictSeparation (pa + pb + 1) SignedDyadicCode.zero (a.mul b) := by
  let x := DyadicReciprocal.magnitude .positive a
  let y := DyadicReciprocal.magnitude .positive b
  have lower : powerOfTwo (a.scale + b.scale) ≤ (x * y) * powerOfTwo (pa + pb) := by
    rw [powerOfTwo_add_mul, powerOfTwo_add_mul]
    have bound := Nat.mul_le_mul first.lower second.lower
    exact Nat.le_trans bound (Nat.le_of_eq (DyadicReciprocal.mulPairExchange _ _ _ _))
  have positive : 0 < x * y := Nat.mul_pos first.positive second.positive
  let normalized : SignedDyadicCode := DyadicReciprocal.signedCode .positive (x * y) (a.scale + b.scale)
  have cert : DyadicReciprocal.NonzeroCode .positive (pa + pb) normalized :=
    ⟨SameValue.refl _, by change 0 < x * y - 0; rw [Nat.sub_zero]; exact positive,
      by change _ ≤ (x * y - 0) * _; rw [Nat.sub_zero]; exact lower⟩
  have same : SameValue (a.mul b) normalized := by
    have same := first.normalized.mul second.normalized
    rw [DyadicReciprocal.sameDirectionProduct] at same
    exact same
  exact cert.positiveMargin.ofSameRight same.symm

end RelationalPerimeter.Constitution.Reals

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Constitution.Reals.replaceSignedStrict
#print axioms RelationalPerimeter.Constitution.Reals.translateSignedStrict
#print axioms RelationalPerimeter.Constitution.Reals.StrictSeparation.ofSameLeft
#print axioms RelationalPerimeter.Constitution.Reals.StrictSeparation.ofSameRight
#print axioms RelationalPerimeter.Constitution.Reals.StrictSeparation.addRight
#print axioms RelationalPerimeter.Constitution.Reals.StrictSeparation.addLeft
#print axioms RelationalPerimeter.Constitution.Reals.DyadicReciprocal.NonzeroCode.positiveMargin
#print axioms RelationalPerimeter.Constitution.Reals.DyadicReciprocal.NonzeroCode.mulPositive
/- AXIOM_AUDIT_END -/
