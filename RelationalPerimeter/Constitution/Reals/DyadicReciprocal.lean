import RelationalPerimeter.Constitution.Reals.DyadicOrder

set_option autoImplicit false
set_option linter.unusedVariables false

/-!
# Constructive natural reciprocal kernel

The sign and quantitative separation will be supplied by an executed
apartness witness. Natural division below requires a positive denominator
before execution and retains its exact quotient/remainder certificate.
-/
namespace RelationalPerimeter.Constitution.Reals.DyadicReciprocal

theorem subtract_le (value amount : Nat) : value - amount ≤ value := by
  induction amount generalizing value with
  | zero => exact Nat.le_refl _
  | succ amount ih =>
      cases value with
      | zero => rw [Nat.zero_sub]; exact Nat.zero_le _
      | succ value => rw [Nat.succ_sub_succ]; exact Nat.le_trans (ih value) (Nat.le_succ _)

theorem subtract_add : {value amount : Nat} → amount ≤ value → value - amount + amount = value
  | value, 0, _ => rfl
  | 0, amount + 1, impossible => nomatch impossible
  | value + 1, amount + 1, bound => by
      rw [Nat.succ_sub_succ]
      exact congrArg Nat.succ (subtract_add (Nat.le_of_succ_le_succ bound))

theorem subtract_fuel {value denominator fuel : Nat} (positive : 0 < denominator)
    (bound : value ≤ fuel + 1) : value - denominator ≤ fuel := by
  cases denominator with
  | zero => nomatch positive
  | succ denominator =>
      cases value with
      | zero => rw [Nat.zero_sub]; exact Nat.zero_le _
      | succ value =>
          rw [Nat.succ_sub_succ]
          exact Nat.le_trans (subtract_le value denominator) (Nat.le_of_succ_le_succ bound)

structure Division (numerator denominator : Nat) where
  quotient : Nat
  remainder : Nat
  exact : quotient * denominator + remainder = numerator
  small : remainder < denominator

/-- Structurally fuelled repeated subtraction. Every recursive call decreases
the fuel; the invariant prevents fuel exhaustion with unprocessed numerator. -/
def divideFuel : (fuel numerator denominator : Nat) → 0 < denominator → numerator ≤ fuel → Division numerator denominator
  | 0, 0, denominator, positive, _ => ⟨0, 0, Nat.zero_mul denominator, positive⟩
  | 0, numerator + 1, denominator, _, impossible => nomatch impossible
  | fuel + 1, numerator, denominator, positive, bound =>
      if small : numerator < denominator then
        ⟨0, numerator, (congrArg (fun n => n + numerator) (Nat.zero_mul denominator)).trans (Nat.zero_add _), small⟩
      else
        let prior := divideFuel fuel (numerator - denominator) denominator positive (subtract_fuel positive bound)
        ⟨prior.quotient + 1, prior.remainder,
          (congrArg (fun n => n + prior.remainder) (Nat.succ_mul prior.quotient denominator)).trans
            ((addSwapMiddle _ _ _).trans
              ((congrArg (fun n => n + denominator) prior.exact).trans
                (subtract_add (Nat.le_of_not_lt small)))), prior.small⟩

def divide (numerator denominator : Nat) (positive : 0 < denominator) : Division numerator denominator :=
  divideFuel numerator numerator denominator positive (Nat.le_refl _)

theorem Division.lower {n d : Nat} (division : Division n d) : division.quotient * d ≤ n :=
  Nat.le_trans (Nat.le_add_right _ _) (Nat.le_of_eq division.exact)

theorem Division.upper {n d : Nat} (division : Division n d) : n < (division.quotient + 1) * d := by
  have h := Nat.add_lt_add_left division.small (division.quotient * d)
  exact Nat.lt_of_lt_of_le (Nat.lt_of_le_of_lt (Nat.le_of_eq division.exact.symm) h)
    (Nat.le_of_eq (Nat.succ_mul _ _).symm)

inductive Direction where
  | positive
  | negative

def magnitude (direction : Direction) (code : SignedDyadicCode) : Nat :=
  match direction with
  | .positive => code.positive - code.negative
  | .negative => code.negative - code.positive

def signedCode (direction : Direction) (value scale : Nat) : SignedDyadicCode :=
  match direction with
  | .positive => ⟨value, 0, scale⟩
  | .negative => ⟨0, value, scale⟩

structure NonzeroCode (direction : Direction) (away : Nat) (code : SignedDyadicCode) where
  normalized : SameValue code (signedCode direction (magnitude direction code) code.scale)
  positive : 0 < magnitude direction code
  lower : powerOfTwo code.scale ≤ magnitude direction code * powerOfTwo away

theorem power_positive (extra : Nat) : 0 < powerOfTwo extra := by
  have h := powerOfTwo_extension 0 extra
  rw [Nat.zero_add] at h
  exact h

theorem mulSwapLast (a b c : Nat) : (a * b) * c = (a * c) * b :=
  (mulAssociate _ _ _).trans ((congrArg (Nat.mul a) (Nat.mul_comm b c)).trans (mulAssociate _ _ _).symm)

/-- The subtraction certificate respects cancellation in the original code;
the lower bound is brought back from the margin's actual common scale. -/
def fromPositiveMargin {away : Nat} {code : SignedDyadicCode}
    (gap : StrictSeparation away SignedDyadicCode.zero code) : NonzeroCode .positive away code := by
  have strict : scaleNat code.negative gap.scale.rightExtra + powerOfTwo gap.precisionExtra <
      scaleNat code.positive gap.scale.rightExtra := by
    have h := gap.strict
    change scaleNat 0 _ + scaleNat code.negative _ + _ < scaleNat code.positive _ + scaleNat 0 _ at h
    rw [SignedDyadicCode.scaleNat_zero, Nat.zero_add, Nat.add_zero] at h
    exact h
  have order : code.negative ≤ code.positive := by
    cases Nat.le_total code.negative code.positive with
    | inl order => exact order
    | inr reverse =>
        exact (Nat.not_lt_of_ge (scaleNat_monotone reverse gap.scale.rightExtra)
          (Nat.lt_of_le_of_lt (Nat.le_add_right _ _) strict)).elim
  let value := magnitude .positive code
  have cancelled : value + code.negative = code.positive := subtract_add order
  have scaled : powerOfTwo gap.precisionExtra < scaleNat value gap.scale.rightExtra := by
    have h := strict
    rw [← cancelled, scaleNat_additive,
      Nat.add_comm (scaleNat value gap.scale.rightExtra) (scaleNat code.negative gap.scale.rightExtra)] at h
    exact leCancelLeft h
  have positive : 0 < value := by
    cases exactValue : value with
    | zero => rw [exactValue, SignedDyadicCode.scaleNat_zero] at scaled; nomatch scaled
    | succ value => exact Nat.zero_lt_succ value
  have exponent : gap.precisionExtra + away = code.scale + gap.scale.rightExtra :=
    (Nat.add_comm _ _).trans (gap.precisionExact.trans gap.scale.rightExact.symm)
  have multiplied := Nat.mul_le_mul_right (powerOfTwo away) (Nat.le_of_lt scaled)
  rw [scaleNat_eq_mul, ← powerOfTwo_add_mul, exponent, powerOfTwo_add_mul,
    mulSwapLast value (powerOfTwo gap.scale.rightExtra) (powerOfTwo away)] at multiplied
  refine ⟨?_, positive, Nat.le_of_mul_le_mul_right multiplied (power_positive _)⟩
  refine ⟨⟨code.scale, 0, 0, rfl, rfl⟩, ?_⟩
  change code.positive + 0 = value + code.negative
  exact (Nat.add_zero _).trans cancelled.symm

def fromNegativeMargin {away : Nat} {code : SignedDyadicCode}
    (gap : StrictSeparation away code SignedDyadicCode.zero) : NonzeroCode .negative away code :=
  let positive := fromPositiveMargin gap.negReverse
  ⟨positive.normalized.neg, positive.positive, positive.lower⟩

structure ReciprocalResult (direction : Direction) (source : SignedDyadicCode) (rounding : Nat) where
  private mk ::
  division : Division (powerOfTwo source.scale * powerOfTwo rounding) (magnitude direction source)
  code : SignedDyadicCode
  codeExact : code = signedCode direction division.quotient rounding

def computeReciprocal (direction : Direction) (code : SignedDyadicCode) (rounding : Nat)
    (positive : 0 < magnitude direction code) : ReciprocalResult direction code rounding :=
  let division := divide (powerOfTwo code.scale * powerOfTwo rounding) (magnitude direction code) positive
  let target := signedCode direction division.quotient rounding
  ⟨division, target, rfl⟩

/-- Auxiliary natural cross-product inequalities, not a numerical carrier. -/
structure CrossNear (precision a aScale b bScale : Nat) : Type where
  forward : a * bScale * powerOfTwo precision ≤ b * aScale * powerOfTwo precision + aScale * bScale
  backward : b * aScale * powerOfTwo precision ≤ a * bScale * powerOfTwo precision + aScale * bScale

def CrossNear.symm {p a A b B : Nat} (near : CrossNear p a A b B) : CrossNear p b B a A := by
  refine ⟨?_, ?_⟩
  · rw [Nat.mul_comm B A]; exact near.backward
  · rw [Nat.mul_comm B A]; exact near.forward

theorem crossRegroup (a x A B T : Nat) : (a * x) * (A * B * T) = (a * B * T) * (A * x) := by
  calc
    (a * x) * (A * B * T) = (a * (A * B * T)) * x := mulSwapLast _ _ _
    _ = ((a * (A * B)) * T) * x := congrArg (fun n => n * x) (mulAssociate _ _ _).symm
    _ = (((a * B) * A) * T) * x := congrArg (fun n => n * T * x)
      ((mulAssociate _ _ _).symm.trans (mulSwapLast _ _ _))
    _ = (((a * B) * T) * A) * x := congrArg (fun n => n * x) (mulSwapLast _ _ _)
    _ = (a * B * T) * (A * x) := mulAssociate _ _ _

theorem crossScaleBound {a b x y t A B T C : Nat}
    (bound : a * x ≤ b * y + t) (left : A * x = C) (right : B * y = C)
    (tolerance : T * t = C) (positive : 0 < C) :
    a * B * T ≤ b * A * T + A * B := by
  apply Nat.le_of_mul_le_mul_right (hc := positive)
  calc
    (a * B * T) * C = (a * x) * (A * B * T) := by rw [crossRegroup, left]
    _ ≤ (b * y + t) * (A * B * T) := Nat.mul_le_mul_right _ bound
    _ = (b * y) * (A * B * T) + t * (A * B * T) := mulDistributeRight _ _ _
    _ = (b * A * T) * C + (A * B) * C := by
      apply addCongruence
      · rw [Nat.mul_comm A B, crossRegroup, right]
      · rw [Nat.mul_comm t (A * B * T), mulAssociate, tolerance]
    _ = (b * A * T + A * B) * C := (mulDistributeRight _ _ _).symm

def CrossNear.ofNear {p a b sa sb : Nat}
    (near : Near p (signedCode .positive a sa) (signedCode .positive b sb)) :
    CrossNear p a (powerOfTwo sa) b (powerOfTwo sb) := by
  have left : powerOfTwo sa * powerOfTwo near.scale.leftExtra = powerOfTwo near.scale.common :=
    (powerOfTwo_add_mul _ _).symm.trans (congrArg powerOfTwo near.scale.leftExact)
  have right : powerOfTwo sb * powerOfTwo near.scale.rightExtra = powerOfTwo near.scale.common :=
    (powerOfTwo_add_mul _ _).symm.trans (congrArg powerOfTwo near.scale.rightExact)
  have tolerance : powerOfTwo p * powerOfTwo near.precisionExtra = powerOfTwo near.scale.common :=
    (powerOfTwo_add_mul _ _).symm.trans (congrArg powerOfTwo near.precisionExact)
  have forward : a * powerOfTwo near.scale.leftExtra ≤ b * powerOfTwo near.scale.rightExtra + powerOfTwo near.precisionExtra := by
    have h := near.leftBound
    change scaleNat a _ + scaleNat 0 _ ≤ (scaleNat b _ + scaleNat 0 _) + _ at h
    rw [SignedDyadicCode.scaleNat_zero, SignedDyadicCode.scaleNat_zero, Nat.add_zero, Nat.add_zero,
      scaleNat_eq_mul, scaleNat_eq_mul] at h
    exact h
  have backward : b * powerOfTwo near.scale.rightExtra ≤ a * powerOfTwo near.scale.leftExtra + powerOfTwo near.precisionExtra := by
    have h := near.rightBound
    change scaleNat b _ + scaleNat 0 _ ≤ (scaleNat a _ + scaleNat 0 _) + _ at h
    rw [SignedDyadicCode.scaleNat_zero, SignedDyadicCode.scaleNat_zero, Nat.add_zero, Nat.add_zero,
      scaleNat_eq_mul, scaleNat_eq_mul] at h
    exact h
  refine ⟨crossScaleBound forward left right tolerance (power_positive _), ?_⟩
  have reversed := crossScaleBound backward right left tolerance (power_positive _)
  rw [Nat.mul_comm (powerOfTwo sb) (powerOfTwo sa)] at reversed
  exact reversed

def CrossNear.toNear {p a b sa sb : Nat} (cross : CrossNear p a (powerOfTwo sa) b (powerOfTwo sb)) :
    Near p (signedCode .positive a sa) (signedCode .positive b sb) := by
  refine ⟨⟨sa + sb + p, sb + p, sa + p, (Nat.add_assoc _ _ _).symm,
    (Nat.add_assoc _ _ _).symm.trans (congrArg (fun n => n + p) (Nat.add_comm _ _))⟩,
    sa + sb, Nat.add_comm _ _, ?_, ?_⟩
  · change scaleNat a (sb + p) + scaleNat 0 _ ≤ (scaleNat b (sa + p) + scaleNat 0 _) + powerOfTwo (sa + sb)
    rw [SignedDyadicCode.scaleNat_zero, SignedDyadicCode.scaleNat_zero, Nat.add_zero, Nat.add_zero,
      scaleNat_addSteps, scaleNat_addSteps, scaleNat_eq_mul, scaleNat_eq_mul, scaleNat_eq_mul, scaleNat_eq_mul,
      powerOfTwo_add_mul]
    exact cross.forward
  · change scaleNat b (sa + p) + scaleNat 0 _ ≤ (scaleNat a (sb + p) + scaleNat 0 _) + powerOfTwo (sa + sb)
    rw [SignedDyadicCode.scaleNat_zero, SignedDyadicCode.scaleNat_zero, Nat.add_zero, Nat.add_zero,
      scaleNat_addSteps, scaleNat_addSteps, scaleNat_eq_mul, scaleNat_eq_mul, scaleNat_eq_mul, scaleNat_eq_mul,
      powerOfTwo_add_mul]
    exact cross.backward

theorem mulPairExchange (a b c d : Nat) : (a * b) * (c * d) = (a * c) * (b * d) :=
  (mulAssociate _ _ _).symm.trans
    ((congrArg (fun n => n * d) (mulSwapLast _ _ _)).trans (mulAssociate _ _ _))

theorem mulFourSwap (a b t c : Nat) : (a * b * t) * c = (a * c * t) * b :=
  (mulSwapLast _ _ _).trans
    ((congrArg (fun n => n * t) (mulSwapLast _ _ _)).trans (mulSwapLast _ _ _))

theorem double_le_cancel {a b : Nat} (bound : a + a ≤ b + b) : a ≤ b := by
  apply Nat.le_of_mul_le_mul_right (c := 2) (hc := by decide)
  rw [Nat.mul_succ, Nat.mul_one, Nat.mul_succ, Nat.mul_one]
  exact bound

theorem crossComposeBound {a A b B c C T : Nat}
    (first : a * B * T ≤ b * A * T + A * B)
    (second : b * C * T ≤ c * B * T + B * C) (positive : 0 < B) :
    a * C * T ≤ c * A * T + A * C + A * C := by
  have left := Nat.mul_le_mul_right C first
  have right := Nat.mul_le_mul_right A second
  rw [mulDistributeRight, mulFourSwap a B T C, mulFourSwap b A T C, mulSwapLast A B C] at left
  rw [mulDistributeRight, mulFourSwap c B T A,
    Nat.mul_comm B C, mulSwapLast C B A, Nat.mul_comm C A] at right
  have combined := Nat.le_trans left (Nat.add_le_add_right right (A * C * B))
  rw [← mulDistributeRight, ← mulDistributeRight] at combined
  exact Nat.le_of_mul_le_mul_right combined positive

theorem crossComposeFine {p a A b B c C : Nat}
    (first : a * B * powerOfTwo (p + 1) ≤ b * A * powerOfTwo (p + 1) + A * B)
    (second : b * C * powerOfTwo (p + 1) ≤ c * B * powerOfTwo (p + 1) + B * C)
    (positive : 0 < B) : a * C * powerOfTwo p ≤ c * A * powerOfTwo p + A * C := by
  have h := crossComposeBound first second positive
  change a * C * (powerOfTwo p + powerOfTwo p) ≤ c * A * (powerOfTwo p + powerOfTwo p) + A * C + A * C at h
  rw [Nat.mul_add, Nat.mul_add, Nat.add_assoc (c * A * powerOfTwo p + c * A * powerOfTwo p),
    addPairExchange] at h
  exact double_le_cancel h

def CrossNear.compose {p a A b B c C : Nat} (first : CrossNear (p + 1) a A b B)
    (second : CrossNear (p + 1) b B c C) (positive : 0 < B) : CrossNear p a A c C := by
  refine ⟨crossComposeFine first.forward second.forward positive, ?_⟩
  have h := crossComposeFine second.symm.forward first.symm.forward positive
  rw [Nat.mul_comm C A] at h
  exact h

theorem crossWeakenBound {a A b B T X : Nat} (positive : 0 < X)
    (bound : a * B * (T * X) ≤ b * A * (T * X) + A * B) :
    a * B * T ≤ b * A * T + A * B := by
  have increase : A * B ≤ (A * B) * X := by
    have h := Nat.mul_le_mul_left (A * B) positive
    rw [Nat.mul_one] at h
    exact h
  have h := Nat.le_trans bound (Nat.add_le_add_left increase (b * A * (T * X)))
  rw [← mulAssociate, ← mulAssociate, ← mulDistributeRight] at h
  exact Nat.le_of_mul_le_mul_right h positive

def CrossNear.weaken {p q a A b B : Nat} (near : CrossNear q a A b B) (extension : PrecisionExtension p q) :
    CrossNear p a A b B := by
  have exponent : powerOfTwo q = powerOfTwo p * powerOfTwo extension.extra :=
    (congrArg powerOfTwo extension.exact).symm.trans (powerOfTwo_add_mul _ _)
  have forward := near.forward
  have backward := near.backward
  rw [exponent] at forward backward
  refine ⟨crossWeakenBound (power_positive _) forward, ?_⟩
  have h := near.symm.forward
  rw [exponent] at h
  have result := crossWeakenBound (power_positive _) h
  rw [Nat.mul_comm B A] at result
  exact result

def Division.rounding {A d t : Nat} (division : Division (A * powerOfTwo t) d) :
    CrossNear t division.quotient (powerOfTwo t) A d := by
  refine ⟨?_, ?_⟩
  · exact Nat.le_trans (Nat.mul_le_mul_right (powerOfTwo t) division.lower) (Nat.le_add_right _ _)
  · have h := Nat.mul_le_mul_right (powerOfTwo t) (Nat.le_of_lt division.upper)
    rw [Nat.succ_mul, mulDistributeRight, Nat.mul_comm d (powerOfTwo t)] at h
    exact h

def CrossNear.reciprocal {p away a A b B : Nat} (near : CrossNear (p + (away + away)) a A b B)
    (left : A ≤ a * powerOfTwo away) (right : B ≤ b * powerOfTwo away) : CrossNear p A a B b := by
  have amplitudes : A * B ≤ (a * b) * powerOfTwo (away + away) := by
    have h := Nat.le_trans (Nat.mul_le_mul_right B left) (Nat.mul_le_mul_left (a * powerOfTwo away) right)
    rw [mulPairExchange, ← powerOfTwo_add_mul] at h
    exact h
  have directed {u U v V : Nat}
      (bound : v * U * powerOfTwo (p + (away + away)) ≤ u * V * powerOfTwo (p + (away + away)) + U * V)
      (amp : U * V ≤ (u * v) * powerOfTwo (away + away)) :
      U * v * powerOfTwo p ≤ V * u * powerOfTwo p + u * v := by
    apply Nat.le_of_mul_le_mul_right (hc := power_positive (away + away))
    calc
      (U * v * powerOfTwo p) * powerOfTwo (away + away) = v * U * powerOfTwo (p + (away + away)) := by
        rw [powerOfTwo_add_mul p (away + away), Nat.mul_comm U v,
          mulAssociate (v * U) (powerOfTwo p) (powerOfTwo (away + away))]
      _ ≤ u * V * powerOfTwo (p + (away + away)) + U * V := bound
      _ ≤ u * V * powerOfTwo (p + (away + away)) + (u * v) * powerOfTwo (away + away) :=
        Nat.add_le_add_left amp _
      _ = (V * u * powerOfTwo p + u * v) * powerOfTwo (away + away) := by
        rw [mulDistributeRight, powerOfTwo_add_mul p (away + away), Nat.mul_comm V u]
        exact congrArg (fun n => n + u * v * powerOfTwo (away + away))
          (mulAssociate (u * V) (powerOfTwo p) (powerOfTwo (away + away))).symm
  refine ⟨directed near.backward amplitudes, ?_⟩
  have h := directed near.symm.backward (by rw [Nat.mul_comm B A, Nat.mul_comm b a]; exact amplitudes)
  rw [Nat.mul_comm b a] at h
  exact h

def NonzeroCode.positiveNear {direction : Direction} {away p : Nat} {a b : SignedDyadicCode}
    (left : NonzeroCode direction away a) (right : NonzeroCode direction away b) (near : Near p a b) :
    Near p (signedCode .positive (magnitude direction a) a.scale) (signedCode .positive (magnitude direction b) b.scale) := by
  have normalized := Near.ofSameRight (Near.ofSameLeft left.normalized.symm near) right.normalized
  cases direction with
  | positive => exact normalized
  | negative => exact normalized.neg

def sourcePrecision (away precision : Nat) : Nat := precision + 2 + (away + away)
def roundingPrecision (precision : Nat) : Nat := precision + 2

def sourceBeyondAway (away precision : Nat) : PrecisionExtension away (sourcePrecision away precision) :=
  (PrecisionExtension.first away away).trans (PrecisionExtension.second (precision + 2) (away + away))

/-- Three errors at p+2 are composed, not replaced by an informal Lipschitz
estimate. The middle cross-product bounds spend exactly two away exponents. -/
def reciprocalNear {direction : Direction} {away p first second : Nat} {a b : SignedDyadicCode}
    (left : NonzeroCode direction away a) (right : NonzeroCode direction away b)
    (leftResult : ReciprocalResult direction a (roundingPrecision first))
    (rightResult : ReciprocalResult direction b (roundingPrecision second))
    (near : Near (sourcePrecision away p) a b)
    (firstBeyond : PrecisionExtension p first) (secondBeyond : PrecisionExtension p second) :
    Near p leftResult.code rightResult.code := by
  let leftDivision := leftResult.division
  let rightDivision := rightResult.division
  let leftError := leftDivision.rounding.weaken firstBeyond.succ.succ
  let rightError := rightDivision.rounding.weaken secondBeyond.succ.succ
  let middle := (CrossNear.ofNear (left.positiveNear right near)).reciprocal left.lower right.lower
  let combined := CrossNear.compose (CrossNear.compose leftError middle left.positive)
    (rightError.symm.weaken (PrecisionExtension.next (p + 1))) right.positive
  rw [leftResult.codeExact, rightResult.codeExact]
  cases direction with
  | positive => exact combined.toNear
  | negative => exact combined.toNear.neg

theorem subtract_zero : {a b : Nat} → a ≤ b → a - b = 0
  | 0, b, _ => Nat.zero_sub b
  | a + 1, 0, impossible => nomatch impossible
  | a + 1, b + 1, bound => (Nat.succ_sub_succ _ _).trans (subtract_zero (Nat.le_of_succ_le_succ bound))

theorem NonzeroCode.componentOrder {direction : Direction} {away : Nat} {code : SignedDyadicCode}
    (certificate : NonzeroCode direction away code) :
    match direction with
    | .positive => code.negative ≤ code.positive
    | .negative => code.positive ≤ code.negative := by
  have directed {a b : Nat} (positive : 0 < a - b) : b ≤ a := by
    cases Nat.le_total b a with
    | inl bound => exact bound
    | inr reverse => rw [subtract_zero reverse] at positive; nomatch positive
  cases direction with
  | positive => exact directed certificate.positive
  | negative => exact directed certificate.positive

theorem naturalMagnitudeBound {m a b bound common scale extra : Nat} (normalized : m + b = a)
    (amplitude : scaleNat a extra ≤ scaleNat b extra + scaleNat bound common)
    (scaleExact : scale + extra = common) : m ≤ bound * powerOfTwo scale := by
  rw [← normalized, scaleNat_additive, Nat.add_comm (scaleNat m extra) (scaleNat b extra)] at amplitude
  have h := leCancelLeft amplitude
  rw [← scaleExact, scaleNat_addSteps, scaleNat_eq_mul, scaleNat_eq_mul, scaleNat_eq_mul] at h
  exact Nat.le_of_mul_le_mul_right h (power_positive _)

theorem NonzeroCode.magnitudeBound {direction : Direction} {away bound : Nat} {code : SignedDyadicCode}
    (certificate : NonzeroCode direction away code) (amplitude : Amplitude bound code) :
    magnitude direction code ≤ bound * powerOfTwo code.scale := by
  cases direction with
  | positive => exact naturalMagnitudeBound (subtract_add certificate.componentOrder) amplitude.positiveBound amplitude.scaleExact
  | negative => exact naturalMagnitudeBound (subtract_add certificate.componentOrder) amplitude.negativeBound amplitude.scaleExact

theorem roundProductBound {d A p bound t : Nat} (amplitude : d ≤ bound * A)
    (budget : PrecisionExtension (p + bound) t) : d * powerOfTwo p ≤ A * powerOfTwo t := by
  have precision : powerOfTwo (p + bound) ≤ powerOfTwo t := by
    have h := powerOfTwo_extension (p + bound) budget.extra
    rw [budget.exact] at h
    exact h
  calc
    d * powerOfTwo p ≤ (bound * A) * powerOfTwo p := Nat.mul_le_mul_right _ amplitude
    _ = A * (bound * powerOfTwo p) := by rw [Nat.mul_comm bound A, mulAssociate]
    _ ≤ A * (powerOfTwo bound * powerOfTwo p) := Nat.mul_le_mul_left A (Nat.mul_le_mul_right _ (nat_le_powerOfTwo bound))
    _ = A * powerOfTwo (p + bound) := by rw [Nat.mul_comm (powerOfTwo bound) (powerOfTwo p), ← powerOfTwo_add_mul]
    _ ≤ A * powerOfTwo t := Nat.mul_le_mul_left A precision

theorem sameDirectionProduct (direction : Direction) (a b s t : Nat) :
    (signedCode direction a s).mul (signedCode direction b t) = signedCode .positive (a * b) (s + t) := by
  cases direction with
  | positive =>
      apply SignedDyadicCode.extensionality
      · change a * b + 0 * 0 = a * b
        rw [Nat.zero_mul, Nat.add_zero]
      · change a * 0 + 0 * b = 0
        rw [Nat.mul_zero, Nat.zero_mul]
      · rfl
  | negative =>
      apply SignedDyadicCode.extensionality
      · change 0 * 0 + a * b = a * b
        rw [Nat.zero_mul, Nat.zero_add]
      · change 0 * b + a * 0 = 0
        rw [Nat.zero_mul, Nat.mul_zero]
      · rfl

def reciprocalUnit {direction : Direction} {away bound p t : Nat} {code : SignedDyadicCode}
    (certificate : NonzeroCode direction away code) (amplitude : Amplitude bound code)
    (result : ReciprocalResult direction code t)
    (budget : PrecisionExtension (p + bound) t) :
    Near p (code.mul result.code) SignedDyadicCode.one := by
  let division := result.division
  have residual : magnitude direction code * powerOfTwo p ≤ powerOfTwo code.scale * powerOfTwo t :=
    roundProductBound (certificate.magnitudeBound amplitude) budget
  have cross : CrossNear p (division.quotient * magnitude direction code)
      (powerOfTwo code.scale * powerOfTwo t) 1 1 := by
    refine ⟨?_, ?_⟩
    · rw [Nat.mul_one, Nat.one_mul, Nat.mul_one]
      exact Nat.le_trans (Nat.mul_le_mul_right (powerOfTwo p) division.lower) (Nat.le_add_right _ _)
    · rw [Nat.one_mul, Nat.mul_one, Nat.mul_one]
      have h := Nat.mul_le_mul_right (powerOfTwo p) (Nat.le_of_lt division.upper)
      rw [Nat.succ_mul, mulDistributeRight] at h
      exact Nat.le_trans h (Nat.add_le_add_left residual _)
  let crossAtScale := Eq.rec (motive := fun denominator _ =>
    CrossNear p (division.quotient * magnitude direction code) denominator 1 1)
    cross (powerOfTwo_add_mul code.scale t).symm
  let crossAtProduct := Eq.rec (motive := fun numerator _ =>
    CrossNear p numerator (powerOfTwo (code.scale + t)) 1 1)
    crossAtScale (Nat.mul_comm division.quotient (magnitude direction code))
  have normalized : Near p
      ((signedCode direction (magnitude direction code) code.scale).mul
        result.code) SignedDyadicCode.one := by
    rw [result.codeExact, sameDirectionProduct]
    exact crossAtProduct.toNear (sb := 0)
  exact Near.ofSameLeft (certificate.normalized.mulRight _) normalized

theorem ltOfNotLe : {a b : Nat} → (a ≤ b → False) → b < a
  | 0, b, impossible => (impossible (Nat.zero_le _)).elim
  | a + 1, 0, _ => Nat.zero_lt_succ _
  | a + 1, b + 1, impossible =>
      Nat.succ_lt_succ (ltOfNotLe (fun h => impossible (Nat.succ_le_succ h)))

theorem Division.quotient_le {n d : Nat} (first second : Division n d) : first.quotient ≤ second.quotient := by
  if bound : first.quotient ≤ second.quotient then exact bound
  else
    have reversed := Nat.mul_le_mul_right d (ltOfNotLe bound)
    exact (Nat.not_lt_of_ge (Nat.le_trans reversed first.lower) second.upper).elim

theorem Division.quotient_unique {n d : Nat} (first second : Division n d) : first.quotient = second.quotient :=
  Nat.le_antisymm (first.quotient_le second) (second.quotient_le first)

theorem ReciprocalResult.sameCode {direction : Direction} {a b : SignedDyadicCode} {t : Nat}
    (first : ReciprocalResult direction a t) (second : ReciprocalResult direction b t) (same : a = b) :
    first.code = second.code := by
  cases same
  exact first.codeExact.trans ((congrArg (fun n => signedCode direction n t)
    (first.division.quotient_unique second.division)).trans second.codeExact.symm)

end RelationalPerimeter.Constitution.Reals.DyadicReciprocal

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Constitution.Reals.DyadicReciprocal.subtract_le
#print axioms RelationalPerimeter.Constitution.Reals.DyadicReciprocal.subtract_add
#print axioms RelationalPerimeter.Constitution.Reals.DyadicReciprocal.subtract_fuel
#print axioms RelationalPerimeter.Constitution.Reals.DyadicReciprocal.Division
#print axioms RelationalPerimeter.Constitution.Reals.DyadicReciprocal.divideFuel
#print axioms RelationalPerimeter.Constitution.Reals.DyadicReciprocal.divide
#print axioms RelationalPerimeter.Constitution.Reals.DyadicReciprocal.Division.lower
#print axioms RelationalPerimeter.Constitution.Reals.DyadicReciprocal.Division.upper
#print axioms RelationalPerimeter.Constitution.Reals.DyadicReciprocal.Direction
#print axioms RelationalPerimeter.Constitution.Reals.DyadicReciprocal.magnitude
#print axioms RelationalPerimeter.Constitution.Reals.DyadicReciprocal.signedCode
#print axioms RelationalPerimeter.Constitution.Reals.DyadicReciprocal.NonzeroCode
#print axioms RelationalPerimeter.Constitution.Reals.DyadicReciprocal.power_positive
#print axioms RelationalPerimeter.Constitution.Reals.DyadicReciprocal.mulSwapLast
#print axioms RelationalPerimeter.Constitution.Reals.DyadicReciprocal.fromPositiveMargin
#print axioms RelationalPerimeter.Constitution.Reals.DyadicReciprocal.fromNegativeMargin
#print axioms RelationalPerimeter.Constitution.Reals.DyadicReciprocal.ReciprocalResult
#print axioms RelationalPerimeter.Constitution.Reals.DyadicReciprocal.computeReciprocal
#print axioms RelationalPerimeter.Constitution.Reals.DyadicReciprocal.CrossNear
#print axioms RelationalPerimeter.Constitution.Reals.DyadicReciprocal.CrossNear.symm
#print axioms RelationalPerimeter.Constitution.Reals.DyadicReciprocal.crossRegroup
#print axioms RelationalPerimeter.Constitution.Reals.DyadicReciprocal.crossScaleBound
#print axioms RelationalPerimeter.Constitution.Reals.DyadicReciprocal.CrossNear.ofNear
#print axioms RelationalPerimeter.Constitution.Reals.DyadicReciprocal.CrossNear.toNear
#print axioms RelationalPerimeter.Constitution.Reals.DyadicReciprocal.mulPairExchange
#print axioms RelationalPerimeter.Constitution.Reals.DyadicReciprocal.mulFourSwap
#print axioms RelationalPerimeter.Constitution.Reals.DyadicReciprocal.double_le_cancel
#print axioms RelationalPerimeter.Constitution.Reals.DyadicReciprocal.crossComposeBound
#print axioms RelationalPerimeter.Constitution.Reals.DyadicReciprocal.crossComposeFine
#print axioms RelationalPerimeter.Constitution.Reals.DyadicReciprocal.CrossNear.compose
#print axioms RelationalPerimeter.Constitution.Reals.DyadicReciprocal.crossWeakenBound
#print axioms RelationalPerimeter.Constitution.Reals.DyadicReciprocal.CrossNear.weaken
#print axioms RelationalPerimeter.Constitution.Reals.DyadicReciprocal.Division.rounding
#print axioms RelationalPerimeter.Constitution.Reals.DyadicReciprocal.CrossNear.reciprocal
#print axioms RelationalPerimeter.Constitution.Reals.DyadicReciprocal.NonzeroCode.positiveNear
#print axioms RelationalPerimeter.Constitution.Reals.DyadicReciprocal.sourcePrecision
#print axioms RelationalPerimeter.Constitution.Reals.DyadicReciprocal.roundingPrecision
#print axioms RelationalPerimeter.Constitution.Reals.DyadicReciprocal.sourceBeyondAway
#print axioms RelationalPerimeter.Constitution.Reals.DyadicReciprocal.reciprocalNear
#print axioms RelationalPerimeter.Constitution.Reals.DyadicReciprocal.subtract_zero
#print axioms RelationalPerimeter.Constitution.Reals.DyadicReciprocal.NonzeroCode.componentOrder
#print axioms RelationalPerimeter.Constitution.Reals.DyadicReciprocal.naturalMagnitudeBound
#print axioms RelationalPerimeter.Constitution.Reals.DyadicReciprocal.NonzeroCode.magnitudeBound
#print axioms RelationalPerimeter.Constitution.Reals.DyadicReciprocal.roundProductBound
#print axioms RelationalPerimeter.Constitution.Reals.DyadicReciprocal.sameDirectionProduct
#print axioms RelationalPerimeter.Constitution.Reals.DyadicReciprocal.reciprocalUnit
#print axioms RelationalPerimeter.Constitution.Reals.DyadicReciprocal.ltOfNotLe
#print axioms RelationalPerimeter.Constitution.Reals.DyadicReciprocal.Division.quotient_le
#print axioms RelationalPerimeter.Constitution.Reals.DyadicReciprocal.Division.quotient_unique
#print axioms RelationalPerimeter.Constitution.Reals.DyadicReciprocal.ReciprocalResult.sameCode
/- AXIOM_AUDIT_END -/
