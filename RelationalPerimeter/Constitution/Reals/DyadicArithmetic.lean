import RelationalPerimeter.Constitution.Reals.Precision

set_option autoImplicit false
set_option linter.unusedVariables false

namespace RelationalPerimeter.Constitution.Reals

theorem addPairExchange (a b c d : Nat) : (a + b) + (c + d) = (a + c) + (b + d) := by
  calc
    (a + b) + (c + d) = ((a + b) + c) + d := (Nat.add_assoc _ _ _).symm
    _ = ((a + c) + b) + d := congrArg (fun n => n + d) (addSwapMiddle a b c)
    _ = (a + c) + (b + d) := Nat.add_assoc _ _ _

theorem translateSignedBound {a b c d tolerance : Nat}
    (bound : a + d ≤ c + b + tolerance) (positive negative : Nat) :
    (a + positive) + (d + negative) ≤ (c + positive) + (b + negative) + tolerance := by
  calc
    (a + positive) + (d + negative) = (a + d) + (positive + negative) := addPairExchange _ _ _ _
    _ ≤ (c + b + tolerance) + (positive + negative) := Nat.add_le_add bound (Nat.le_refl _)
    _ = ((c + b) + (positive + negative)) + tolerance := addSwapMiddle _ _ _
    _ = ((c + positive) + (b + negative)) + tolerance :=
      congrArg (fun n => n + tolerance) (addPairExchange _ _ _ _)

theorem replaceSignedBound {a an m mn c cn tolerance : Nat}
    (same : a + mn = m + an) (bound : m + cn ≤ c + mn + tolerance) :
    a + cn ≤ c + an + tolerance := by
  apply leCancelRight (c := mn)
  calc
    (a + cn) + mn = (a + mn) + cn := addSwapMiddle _ _ _
    _ = (m + an) + cn := congrArg (fun n => n + cn) same
    _ = (m + cn) + an := addSwapMiddle _ _ _
    _ ≤ (c + mn + tolerance) + an := Nat.add_le_add bound (Nat.le_refl _)
    _ = (c + mn + an) + tolerance := addSwapMiddle _ _ _
    _ = (c + an + mn) + tolerance := congrArg (fun n => n + tolerance) (addSwapMiddle _ _ _)
    _ = (c + an + tolerance) + mn := addSwapMiddle _ _ _

namespace PrecisionExtension

def succ {coarse fine : Nat} (extension : PrecisionExtension coarse fine) :
    PrecisionExtension (Nat.succ coarse) (Nat.succ fine) where
  extra := extension.extra
  exact := (Nat.succ_add _ _).trans (congrArg Nat.succ extension.exact)

def first (left right : Nat) : PrecisionExtension left (left + right) :=
  ⟨right, rfl⟩

def second (left right : Nat) : PrecisionExtension right (left + right) :=
  ⟨left, Nat.add_comm right left⟩

def next (precision : Nat) : PrecisionExtension precision (Nat.succ precision) :=
  ⟨1, rfl⟩

def add {a b c d : Nat} (left : PrecisionExtension a c)
    (right : PrecisionExtension b d) : PrecisionExtension (a + b) (c + d) where
  extra := left.extra + right.extra
  exact := by
    calc
      (a + b) + (left.extra + right.extra) = (a + left.extra) + (b + right.extra) := addPairExchange _ _ _ _
      _ = c + d := by rw [left.exact, right.exact]

end PrecisionExtension

namespace SignedDyadicCode

def neg (code : SignedDyadicCode) : SignedDyadicCode :=
  ⟨code.negative, code.positive, code.scale⟩

theorem neg_neg_exact (code : SignedDyadicCode) : code.neg.neg = code := by
  cases code
  rfl

theorem neg_raise_exact (code : SignedDyadicCode) (extra : Nat) :
    (code.raise extra).neg = code.neg.raise extra := rfl

def zero : SignedDyadicCode := ⟨0, 0, 0⟩
def one : SignedDyadicCode := ⟨1, 0, 0⟩

/-- The common scale is an explicit sum; both increments are retained. -/
def additionScale (left right : SignedDyadicCode) : CommonScale left right :=
  ⟨left.scale + right.scale, right.scale, left.scale, rfl,
    Nat.add_comm right.scale left.scale⟩

def add (left right : SignedDyadicCode) : SignedDyadicCode :=
  let scale := additionScale left right
  ⟨liftedPositive left scale.leftExtra + liftedPositive right scale.rightExtra,
    liftedNegative left scale.leftExtra + liftedNegative right scale.rightExtra,
    scale.common⟩

theorem add_positive (left right : SignedDyadicCode) (extra : Nat) :
    liftedPositive (add left right) extra =
      liftedPositive left (right.scale + extra) +
      liftedPositive right (left.scale + extra) := by
  change scaleNat (_ + _) extra = _
  rw [scaleNat_additive, ← liftedPositive_addSteps, ← liftedPositive_addSteps]
  rfl

theorem add_negative (left right : SignedDyadicCode) (extra : Nat) :
    liftedNegative (add left right) extra =
      liftedNegative left (right.scale + extra) +
      liftedNegative right (left.scale + extra) := by
  change scaleNat (_ + _) extra = _
  rw [scaleNat_additive, ← liftedNegative_addSteps, ← liftedNegative_addSteps]
  rfl

def add_comm (left right : SignedDyadicCode) : SameValue (add left right) (add right left) where
  scale := ⟨left.scale + right.scale, 0, 0, rfl, Nat.add_comm right.scale left.scale⟩
  exact := by
    change (liftedPositive left right.scale + liftedPositive right left.scale) +
      (liftedNegative right left.scale + liftedNegative left right.scale) =
      (liftedPositive right left.scale + liftedPositive left right.scale) +
      (liftedNegative left right.scale + liftedNegative right left.scale)
    rw [Nat.add_comm (liftedPositive left right.scale) (liftedPositive right left.scale),
      Nat.add_comm (liftedNegative right left.scale) (liftedNegative left right.scale)]

theorem scaleNat_zero (extra : Nat) : scaleNat 0 extra = 0 := by
  induction extra with
  | zero => rfl
  | succ extra ih => change scaleNat 0 extra + scaleNat 0 extra = 0; rw [ih]

theorem add_zero_exact (code : SignedDyadicCode) : add code zero = code := by
  cases code
  rename_i positive negative scale
  change SignedDyadicCode.mk (positive + scaleNat 0 scale) (negative + scaleNat 0 scale) scale = _
  rw [scaleNat_zero, Nat.add_zero, Nat.add_zero]

def add_zero (code : SignedDyadicCode) : SameValue (add code zero) code := by
  rw [add_zero_exact]
  exact SameValue.refl code

def zero_add (code : SignedDyadicCode) : SameValue (add zero code) code :=
  (add_comm zero code).trans (add_zero code)

def add_neg (code : SignedDyadicCode) : SameValue (code.add code.neg) zero where
  scale := ⟨code.scale + code.scale, 0, code.scale + code.scale, rfl, Nat.zero_add _⟩
  exact := by
    change (scaleNat code.positive code.scale + scaleNat code.negative code.scale) +
      scaleNat 0 (code.scale + code.scale) =
      scaleNat 0 (code.scale + code.scale) +
        (scaleNat code.negative code.scale + scaleNat code.positive code.scale)
    rw [scaleNat_zero, Nat.add_zero, Nat.zero_add, Nat.add_comm]

def neg_add (code : SignedDyadicCode) : SameValue (code.neg.add code) zero :=
  (add_comm code.neg code).trans (add_neg code)

theorem neg_add_exact (left right : SignedDyadicCode) :
    (left.add right).neg = left.neg.add right.neg := rfl

def add_assoc (a b c : SignedDyadicCode) :
    SameValue (add (add a b) c) (add a (add b c)) where
  scale := ⟨(a.scale + b.scale) + c.scale, 0, 0, rfl,
    (Nat.add_assoc a.scale b.scale c.scale).symm⟩
  exact := by
    change liftedPositive ((a.add b).add c) 0 + liftedNegative (a.add (b.add c)) 0 = _
    rw [add_positive, add_negative, add_positive, add_negative, add_positive, add_negative,
      add_positive, add_negative]
    rw [Nat.add_zero, Nat.add_zero, Nat.add_zero, Nat.add_zero]
    change (liftedPositive a (b.scale + c.scale) + liftedPositive b (a.scale + c.scale) +
      liftedPositive c (a.scale + b.scale)) +
      (liftedNegative a (b.scale + c.scale) + (liftedNegative b (c.scale + a.scale) +
      liftedNegative c (b.scale + a.scale))) =
      (liftedPositive a (b.scale + c.scale) + (liftedPositive b (c.scale + a.scale) +
      liftedPositive c (b.scale + a.scale))) +
      (liftedNegative a (b.scale + c.scale) + liftedNegative b (a.scale + c.scale) +
      liftedNegative c (a.scale + b.scale))
    rw [Nat.add_comm c.scale a.scale, Nat.add_comm b.scale a.scale]
    rw [Nat.add_assoc (liftedPositive a _) (liftedPositive b _) (liftedPositive c _),
      Nat.add_assoc (liftedNegative a _) (liftedNegative b _) (liftedNegative c _)]

end SignedDyadicCode

namespace SameValue

def neg {left right : SignedDyadicCode} (same : SameValue left right) :
    SameValue left.neg right.neg where
  scale := ⟨same.scale.common, same.scale.leftExtra, same.scale.rightExtra,
    same.scale.leftExact, same.scale.rightExact⟩
  exact := (Nat.add_comm _ _).trans (same.exact.symm.trans (Nat.add_comm _ _))

/-- Translate exact signed equality, retaining the common-scale evidence. -/
def addRight {left right : SignedDyadicCode} (same : SameValue left right)
    (code : SignedDyadicCode) :
    SameValue (left.add code) (right.add code) := by
  let lifted := same.liftCommon code.scale
  have leftScale := same.scale.leftExact
  have rightScale := same.scale.rightExact
  refine {
    scale := ⟨same.scale.common + code.scale, same.scale.leftExtra,
      same.scale.rightExtra, ?_, ?_⟩
    exact := ?_ }
  · exact (addSwapMiddle left.scale code.scale same.scale.leftExtra).trans
      (congrArg (fun n => n + code.scale) leftScale)
  · exact (addSwapMiddle right.scale code.scale same.scale.rightExtra).trans
      (congrArg (fun n => n + code.scale) rightScale)
  · dsimp only
    rw [SignedDyadicCode.add_positive, SignedDyadicCode.add_negative,
      SignedDyadicCode.add_positive, SignedDyadicCode.add_negative,
      leftScale, rightScale]
    have bound := lifted.exact
    change liftedPositive left (same.scale.leftExtra + code.scale) +
      liftedNegative right (same.scale.rightExtra + code.scale) =
      liftedPositive right (same.scale.rightExtra + code.scale) +
      liftedNegative left (same.scale.leftExtra + code.scale) at bound
    rw [Nat.add_comm same.scale.leftExtra code.scale,
      Nat.add_comm same.scale.rightExtra code.scale] at bound
    exact (addPairExchange _ _ _ _).trans
      ((congrArg (fun n => n + (liftedPositive code same.scale.common +
        liftedNegative code same.scale.common)) bound).trans
        (addPairExchange _ _ _ _))

def addLeft {left right : SignedDyadicCode} (same : SameValue left right)
    (code : SignedDyadicCode) : SameValue (code.add left) (code.add right) :=
  (SignedDyadicCode.add_comm code left).trans
    ((same.addRight code).trans (SignedDyadicCode.add_comm right code))

def add {a b c d : SignedDyadicCode} (left : SameValue a c)
    (right : SameValue b d) : SameValue (a.add b) (c.add d) :=
  (left.addRight b).trans (right.addLeft c)

end SameValue

namespace Near

def neg {precision : Nat} {left right : SignedDyadicCode}
    (near : Near precision left right) : Near precision left.neg right.neg where
  scale := ⟨near.scale.common, near.scale.leftExtra, near.scale.rightExtra,
    near.scale.leftExact, near.scale.rightExact⟩
  precisionExtra := near.precisionExtra
  precisionExact := near.precisionExact
  leftBound := by
    change liftedNegative left _ + liftedPositive right _ ≤
      liftedNegative right _ + liftedPositive left _ + _
    rw [Nat.add_comm (liftedNegative left _) (liftedPositive right _),
      Nat.add_comm (liftedNegative right _) (liftedPositive left _)]
    exact near.rightBound
  rightBound := by
    change liftedNegative right _ + liftedPositive left _ ≤
      liftedNegative left _ + liftedPositive right _ + _
    rw [Nat.add_comm (liftedNegative right _) (liftedPositive left _),
      Nat.add_comm (liftedNegative left _) (liftedPositive right _)]
    exact near.leftBound

/-- Translation changes the comparison scale, without spending precision. -/
def addRight {precision : Nat} {left right : SignedDyadicCode}
    (near : Near precision left right) (code : SignedDyadicCode) :
    Near precision (left.add code) (right.add code) := by
  let lifted := near.liftCommon code.scale
  have leftScale := near.scale.leftExact
  have rightScale := near.scale.rightExact
  have precisionScale := near.precisionExact
  refine {
    scale := ⟨near.scale.common + code.scale, near.scale.leftExtra,
      near.scale.rightExtra, ?_, ?_⟩
    precisionExtra := near.precisionExtra + code.scale
    precisionExact := ?_
    leftBound := ?_
    rightBound := ?_ }
  · exact (addSwapMiddle left.scale code.scale near.scale.leftExtra).trans
      (congrArg (fun n => n + code.scale) leftScale)
  · exact (addSwapMiddle right.scale code.scale near.scale.rightExtra).trans
      (congrArg (fun n => n + code.scale) rightScale)
  · change precision + (near.precisionExtra + code.scale) = near.scale.common + code.scale
    exact (Nat.add_assoc _ _ _).symm.trans (congrArg (fun n => n + code.scale) precisionScale)
  · dsimp only
    rw [SignedDyadicCode.add_positive, SignedDyadicCode.add_negative,
      SignedDyadicCode.add_positive, SignedDyadicCode.add_negative,
      leftScale, rightScale]
    have bound := lifted.leftBound
    change liftedPositive left (near.scale.leftExtra + code.scale) +
      liftedNegative right (near.scale.rightExtra + code.scale) ≤
      liftedPositive right (near.scale.rightExtra + code.scale) +
      liftedNegative left (near.scale.leftExtra + code.scale) +
      powerOfTwo (near.precisionExtra + code.scale) at bound
    rw [Nat.add_comm near.scale.leftExtra code.scale,
      Nat.add_comm near.scale.rightExtra code.scale] at bound
    exact translateSignedBound bound _ _
  · dsimp only
    rw [SignedDyadicCode.add_positive, SignedDyadicCode.add_negative,
      SignedDyadicCode.add_positive, SignedDyadicCode.add_negative,
      leftScale, rightScale]
    have bound := lifted.rightBound
    change liftedPositive right (near.scale.rightExtra + code.scale) +
      liftedNegative left (near.scale.leftExtra + code.scale) ≤
      liftedPositive left (near.scale.leftExtra + code.scale) +
      liftedNegative right (near.scale.rightExtra + code.scale) +
      powerOfTwo (near.precisionExtra + code.scale) at bound
    rw [Nat.add_comm near.scale.leftExtra code.scale,
      Nat.add_comm near.scale.rightExtra code.scale] at bound
    exact translateSignedBound bound _ _

/-- Replace the left endpoint by an exactly equal code, without error loss. -/
def ofSameLeft {precision : Nat} {a b c : SignedDyadicCode}
    (same : SameValue a b) (near : Near precision b c) : Near precision a c := by
  let first := same.liftCommon near.scale.common
  let second := near.liftCommon same.scale.common
  have hc : first.scale.common = second.scale.common := Nat.add_comm _ _
  have hm : first.scale.rightExtra = second.scale.leftExtra := by
    exact addLeftCancel (first.scale.rightExact.trans (hc.trans second.scale.leftExact.symm))
  have exact := first.exact
  have lb := second.leftBound
  have rb := second.rightBound
  rw [← hm] at lb rb
  refine {
    scale := ⟨first.scale.common, first.scale.leftExtra, second.scale.rightExtra,
      first.scale.leftExact, second.scale.rightExact.trans hc.symm⟩
    precisionExtra := second.precisionExtra
    precisionExact := second.precisionExact.trans hc.symm
    leftBound := ?_
    rightBound := ?_ }
  · dsimp only
    exact replaceSignedBound exact lb
  · dsimp only
    have flipped : liftedNegative a first.scale.leftExtra + liftedPositive b first.scale.rightExtra =
        liftedNegative b first.scale.rightExtra + liftedPositive a first.scale.leftExtra :=
      (Nat.add_comm _ _).trans (exact.symm.trans (Nat.add_comm _ _))
    have reversed : liftedNegative b first.scale.rightExtra + liftedPositive c second.scale.rightExtra ≤
        liftedNegative c second.scale.rightExtra + liftedPositive b first.scale.rightExtra +
        powerOfTwo second.precisionExtra := by
      rw [Nat.add_comm (liftedNegative b _) (liftedPositive c _),
        Nat.add_comm (liftedNegative c _) (liftedPositive b _)]
      exact rb
    have result := replaceSignedBound flipped reversed
    rw [Nat.add_comm (liftedNegative a _) (liftedPositive c _),
      Nat.add_comm (liftedNegative c _) (liftedPositive a _)] at result
    exact result

def ofSameRight {precision : Nat} {a b c : SignedDyadicCode}
    (near : Near precision a b) (same : SameValue b c) : Near precision a c :=
  (ofSameLeft same.symm near.symm).symm

def addLeft {precision : Nat} {left right : SignedDyadicCode}
    (near : Near precision left right) (code : SignedDyadicCode) :
    Near precision (code.add left) (code.add right) :=
  ofSameRight (ofSameLeft (SignedDyadicCode.add_comm code left)
    (near.addRight code)) (SignedDyadicCode.add_comm right code)

/-- Two successor-precision errors spend exactly one precision bit. -/
def add {precision : Nat} {a b c d : SignedDyadicCode}
    (left : Near (Nat.succ precision) a c)
    (right : Near (Nat.succ precision) b d) :
    Near precision (a.add b) (c.add d) :=
  compose (left.addRight b) (right.addLeft c)

end Near

namespace SignedDyadicCode

def add_raise (left right : SignedDyadicCode) (leftExtra rightExtra : Nat) :
    SameValue ((left.raise leftExtra).add (right.raise rightExtra)) (left.add right) :=
  SameValue.add (SameValue.raiseExact left leftExtra).symm
    (SameValue.raiseExact right rightExtra).symm

end SignedDyadicCode

end RelationalPerimeter.Constitution.Reals

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Constitution.Reals.SignedDyadicCode.neg
#print axioms RelationalPerimeter.Constitution.Reals.SignedDyadicCode.neg_neg_exact
#print axioms RelationalPerimeter.Constitution.Reals.SignedDyadicCode.neg_raise_exact
#print axioms RelationalPerimeter.Constitution.Reals.SignedDyadicCode.add_neg
#print axioms RelationalPerimeter.Constitution.Reals.SignedDyadicCode.neg_add
#print axioms RelationalPerimeter.Constitution.Reals.SignedDyadicCode.neg_add_exact
#print axioms RelationalPerimeter.Constitution.Reals.SameValue.neg
#print axioms RelationalPerimeter.Constitution.Reals.Near.neg
#print axioms RelationalPerimeter.Constitution.Reals.addPairExchange
#print axioms RelationalPerimeter.Constitution.Reals.translateSignedBound
#print axioms RelationalPerimeter.Constitution.Reals.replaceSignedBound
#print axioms RelationalPerimeter.Constitution.Reals.PrecisionExtension.succ
#print axioms RelationalPerimeter.Constitution.Reals.PrecisionExtension.first
#print axioms RelationalPerimeter.Constitution.Reals.PrecisionExtension.second
#print axioms RelationalPerimeter.Constitution.Reals.PrecisionExtension.next
#print axioms RelationalPerimeter.Constitution.Reals.PrecisionExtension.add
#print axioms RelationalPerimeter.Constitution.Reals.SignedDyadicCode.zero
#print axioms RelationalPerimeter.Constitution.Reals.SignedDyadicCode.one
#print axioms RelationalPerimeter.Constitution.Reals.SignedDyadicCode.additionScale
#print axioms RelationalPerimeter.Constitution.Reals.SignedDyadicCode.add
#print axioms RelationalPerimeter.Constitution.Reals.SignedDyadicCode.add_positive
#print axioms RelationalPerimeter.Constitution.Reals.SignedDyadicCode.add_negative
#print axioms RelationalPerimeter.Constitution.Reals.SignedDyadicCode.add_comm
#print axioms RelationalPerimeter.Constitution.Reals.SignedDyadicCode.scaleNat_zero
#print axioms RelationalPerimeter.Constitution.Reals.SignedDyadicCode.add_zero_exact
#print axioms RelationalPerimeter.Constitution.Reals.SignedDyadicCode.add_zero
#print axioms RelationalPerimeter.Constitution.Reals.SignedDyadicCode.zero_add
#print axioms RelationalPerimeter.Constitution.Reals.SignedDyadicCode.add_assoc
#print axioms RelationalPerimeter.Constitution.Reals.SameValue.addRight
#print axioms RelationalPerimeter.Constitution.Reals.SameValue.addLeft
#print axioms RelationalPerimeter.Constitution.Reals.SameValue.add
#print axioms RelationalPerimeter.Constitution.Reals.Near.addRight
#print axioms RelationalPerimeter.Constitution.Reals.Near.ofSameLeft
#print axioms RelationalPerimeter.Constitution.Reals.Near.ofSameRight
#print axioms RelationalPerimeter.Constitution.Reals.Near.addLeft
#print axioms RelationalPerimeter.Constitution.Reals.Near.add
#print axioms RelationalPerimeter.Constitution.Reals.SignedDyadicCode.add_raise
/- AXIOM_AUDIT_END -/
