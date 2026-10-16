import Init

set_option autoImplicit false
set_option linter.unusedVariables false

/-!
# Constructive signed dyadic precision

This module builds the numerical precision kernel used by the relational-real
construction.  A signed dyadic is kept as two natural components at an
explicit scale.  No quotient, integer, rational, classical choice, or
propositional extensionality is used.

The witnesses carried by `CommonScale`, `SameValue`, and `Near` are positive
data.  In particular, a comparison records how both operands and the requested
precision reach the very same finite scale.
-/

namespace RelationalPerimeter.Constitution.Reals

/-- Repeated doubling, used instead of a quotient-based dyadic operation. -/
def scaleNat (value : Nat) : Nat → Nat
  | 0 => value
  | Nat.succ extra =>
      scaleNat value extra + scaleNat value extra

/-- The natural numerator representing one unit at an additional scale. -/
def powerOfTwo (extra : Nat) : Nat :=
  scaleNat 1 extra

theorem addSwapMiddle (a b c : Nat) :
    (a + b) + c = (a + c) + b := by
  calc
    (a + b) + c = a + (b + c) := Nat.add_assoc a b c
    _ = a + (c + b) := congrArg (Nat.add a) (Nat.add_comm b c)
    _ = (a + c) + b := (Nat.add_assoc a c b).symm

theorem addRightCancel {a b c : Nat} (same : a + c = b + c) : a = b := by
  induction c with
  | zero =>
      exact same
  | succ c ih =>
      exact ih (Nat.succ.inj same)

theorem addLeftCancel {a b c : Nat} (same : a + b = a + c) : b = c := by
  apply addRightCancel (c := a)
  calc
    b + a = a + b := Nat.add_comm b a
    _ = a + c := same
    _ = c + a := Nat.add_comm a c

theorem leCancelRight {a b c : Nat} (bound : a + c ≤ b + c) : a ≤ b := by
  induction c with
  | zero =>
      exact bound
  | succ c ih =>
      exact ih (Nat.le_of_succ_le_succ bound)

theorem scaleNat_addSteps (value first second : Nat) :
    scaleNat value (first + second) =
      scaleNat (scaleNat value first) second := by
  induction second with
  | zero =>
      rfl
  | succ second ih =>
      change
        scaleNat value (first + second) + scaleNat value (first + second) =
          scaleNat (scaleNat value first) second +
            scaleNat (scaleNat value first) second
      exact congrArg (fun current => current + current) ih

theorem scaleNat_additive (left right extra : Nat) :
    scaleNat (left + right) extra =
      scaleNat left extra + scaleNat right extra := by
  induction extra with
  | zero =>
      rfl
  | succ extra ih =>
      change
        scaleNat (left + right) extra + scaleNat (left + right) extra =
          (scaleNat left extra + scaleNat left extra) +
            (scaleNat right extra + scaleNat right extra)
      rw [ih]
      calc
        (scaleNat left extra + scaleNat right extra) +
            (scaleNat left extra + scaleNat right extra) =
          ((scaleNat left extra + scaleNat right extra) +
            scaleNat left extra) + scaleNat right extra :=
          (Nat.add_assoc
            (scaleNat left extra + scaleNat right extra)
            (scaleNat left extra) (scaleNat right extra)).symm
        _ = ((scaleNat left extra + scaleNat left extra) +
            scaleNat right extra) + scaleNat right extra :=
          congrArg (fun value => value + scaleNat right extra)
            (addSwapMiddle (scaleNat left extra)
              (scaleNat right extra) (scaleNat left extra))
        _ = (scaleNat left extra + scaleNat left extra) +
            (scaleNat right extra + scaleNat right extra) :=
          Nat.add_assoc (scaleNat left extra + scaleNat left extra)
            (scaleNat right extra) (scaleNat right extra)

theorem scaleNat_monotone {left right : Nat} (bound : left ≤ right)
    (extra : Nat) : scaleNat left extra ≤ scaleNat right extra := by
  induction extra with
  | zero =>
      exact bound
  | succ extra ih =>
      exact Nat.add_le_add ih ih

theorem scaleNat_commutes (value first second : Nat) :
    scaleNat (scaleNat value first) second =
      scaleNat (scaleNat value second) first := by
  calc
    scaleNat (scaleNat value first) second =
        scaleNat value (first + second) :=
      (scaleNat_addSteps value first second).symm
    _ = scaleNat value (second + first) :=
      congrArg (scaleNat value) (Nat.add_comm first second)
    _ = scaleNat (scaleNat value second) first :=
      scaleNat_addSteps value second first

theorem powerOfTwo_succ (extra : Nat) :
    powerOfTwo (Nat.succ extra) =
      powerOfTwo extra + powerOfTwo extra := by
  rfl

theorem powerOfTwo_add (first second : Nat) :
    powerOfTwo (first + second) =
      scaleNat (powerOfTwo first) second := by
  exact scaleNat_addSteps 1 first second

theorem powerOfTwo_extension (base extra : Nat) :
    powerOfTwo base ≤ powerOfTwo (base + extra) := by
  induction extra with
  | zero =>
      exact Nat.le_refl _
  | succ extra ih =>
      exact Nat.le_trans ih (Nat.le_add_right _ _)

theorem scaleSignedBound
    {leftPositive rightNegative rightPositive leftNegative tolerance : Nat}
    (bound : leftPositive + rightNegative ≤
      rightPositive + leftNegative + tolerance)
    (extra : Nat) :
    scaleNat leftPositive extra + scaleNat rightNegative extra ≤
      scaleNat rightPositive extra + scaleNat leftNegative extra +
        scaleNat tolerance extra := by
  calc
    scaleNat leftPositive extra + scaleNat rightNegative extra =
        scaleNat (leftPositive + rightNegative) extra :=
      (scaleNat_additive leftPositive rightNegative extra).symm
    _ ≤ scaleNat (rightPositive + leftNegative + tolerance) extra :=
      scaleNat_monotone bound extra
    _ = scaleNat (rightPositive + leftNegative) extra +
          scaleNat tolerance extra :=
      scaleNat_additive (rightPositive + leftNegative) tolerance extra
    _ = (scaleNat rightPositive extra + scaleNat leftNegative extra) +
          scaleNat tolerance extra := by
      rw [scaleNat_additive rightPositive leftNegative extra]

theorem composeSignedBound
    {xPositive xNegative yPositive yNegative zPositive zNegative tolerance : Nat}
    (xy : xPositive + yNegative ≤ yPositive + xNegative + tolerance)
    (yz : yPositive + zNegative ≤ zPositive + yNegative + tolerance) :
    xPositive + zNegative ≤
      zPositive + xNegative + (tolerance + tolerance) := by
  have first :
      (xPositive + yNegative) + zNegative ≤
        (yPositive + xNegative + tolerance) + zNegative :=
    Nat.add_le_add xy (Nat.le_refl zNegative)
  have second :
      (yPositive + zNegative) + (xNegative + tolerance) ≤
        (zPositive + yNegative + tolerance) +
          (xNegative + tolerance) :=
    Nat.add_le_add yz (Nat.le_refl (xNegative + tolerance))
  have firstReordered :
      (xPositive + zNegative) + yNegative ≤
        (yPositive + zNegative) + (xNegative + tolerance) := by
    calc
      (xPositive + zNegative) + yNegative =
          (xPositive + yNegative) + zNegative :=
        (addSwapMiddle xPositive yNegative zNegative).symm
      _ ≤
          (yPositive + xNegative + tolerance) + zNegative := first
      _ = (yPositive + zNegative) + (xNegative + tolerance) := by
        calc
          (yPositive + xNegative + tolerance) + zNegative =
              (yPositive + xNegative + zNegative) + tolerance :=
            addSwapMiddle (yPositive + xNegative) tolerance zNegative
          _ = (yPositive + zNegative + xNegative) + tolerance :=
            congrArg (fun value => value + tolerance)
              (addSwapMiddle yPositive xNegative zNegative)
          _ = (yPositive + zNegative) + (xNegative + tolerance) :=
            Nat.add_assoc (yPositive + zNegative) xNegative tolerance
  have combined :
      (xPositive + zNegative) + yNegative ≤
        (zPositive + xNegative + (tolerance + tolerance)) + yNegative := by
    calc
      (xPositive + zNegative) + yNegative ≤
          (yPositive + zNegative) + (xNegative + tolerance) :=
        firstReordered
      _ ≤ (zPositive + yNegative + tolerance) +
          (xNegative + tolerance) := second
      _ = (zPositive + xNegative + (tolerance + tolerance)) +
          yNegative := by
        calc
          (zPositive + yNegative + tolerance) +
              (xNegative + tolerance) =
            ((zPositive + yNegative + tolerance) + xNegative) +
              tolerance :=
            (Nat.add_assoc (zPositive + yNegative + tolerance)
              xNegative tolerance).symm
          _ = ((zPositive + yNegative + xNegative) + tolerance) +
              tolerance :=
            congrArg (fun value => value + tolerance)
              (addSwapMiddle (zPositive + yNegative) tolerance xNegative)
          _ = ((zPositive + xNegative + yNegative) + tolerance) +
              tolerance :=
            congrArg (fun value => (value + tolerance) + tolerance)
              (addSwapMiddle zPositive yNegative xNegative)
          _ = (zPositive + xNegative + yNegative) +
              (tolerance + tolerance) :=
            Nat.add_assoc (zPositive + xNegative + yNegative)
              tolerance tolerance
          _ = (zPositive + xNegative + (tolerance + tolerance)) +
              yNegative :=
            addSwapMiddle (zPositive + xNegative) yNegative
              (tolerance + tolerance)
  exact leCancelRight combined

/-- A signed dyadic numerator represented as `positive - negative` at scale. -/
structure SignedDyadicCode where
  positive : Nat
  negative : Nat
  scale : Nat

namespace SignedDyadicCode

/-- Raise a code to a finer scale without changing its represented value. -/
def raise (code : SignedDyadicCode) (extra : Nat) : SignedDyadicCode where
  positive := scaleNat code.positive extra
  negative := scaleNat code.negative extra
  scale := code.scale + extra

end SignedDyadicCode

/-- Positive evidence that two codes have been brought to one finite scale. -/
structure CommonScale (left right : SignedDyadicCode) where
  common : Nat
  leftExtra : Nat
  rightExtra : Nat
  leftExact : left.scale + leftExtra = common
  rightExact : right.scale + rightExtra = common

namespace CommonScale

def symm {left right : SignedDyadicCode}
    (scale : CommonScale left right) : CommonScale right left where
  common := scale.common
  leftExtra := scale.rightExtra
  rightExtra := scale.leftExtra
  leftExact := scale.rightExact
  rightExact := scale.leftExact

end CommonScale

def liftedPositive (code : SignedDyadicCode) (extra : Nat) : Nat :=
  scaleNat code.positive extra

def liftedNegative (code : SignedDyadicCode) (extra : Nat) : Nat :=
  scaleNat code.negative extra

theorem liftedPositive_addSteps (code : SignedDyadicCode)
    (first second : Nat) :
    liftedPositive code (first + second) =
      scaleNat (liftedPositive code first) second :=
  scaleNat_addSteps code.positive first second

theorem liftedNegative_addSteps (code : SignedDyadicCode)
    (first second : Nat) :
    liftedNegative code (first + second) =
      scaleNat (liftedNegative code first) second :=
  scaleNat_addSteps code.negative first second

theorem liftedPositive_raise (code : SignedDyadicCode)
    (raiseExtra compareExtra : Nat) :
    liftedPositive (code.raise raiseExtra) compareExtra =
      liftedPositive code (compareExtra + raiseExtra) := by
  calc
    liftedPositive (code.raise raiseExtra) compareExtra =
        scaleNat (scaleNat code.positive compareExtra) raiseExtra :=
      scaleNat_commutes code.positive raiseExtra compareExtra
    _ = liftedPositive code (compareExtra + raiseExtra) :=
      (scaleNat_addSteps code.positive compareExtra raiseExtra).symm

theorem liftedNegative_raise (code : SignedDyadicCode)
    (raiseExtra compareExtra : Nat) :
    liftedNegative (code.raise raiseExtra) compareExtra =
      liftedNegative code (compareExtra + raiseExtra) := by
  calc
    liftedNegative (code.raise raiseExtra) compareExtra =
        scaleNat (scaleNat code.negative compareExtra) raiseExtra :=
      scaleNat_commutes code.negative raiseExtra compareExtra
    _ = liftedNegative code (compareExtra + raiseExtra) :=
      (scaleNat_addSteps code.negative compareExtra raiseExtra).symm

/-- Exact equality of signed dyadic codes, witnessed at a common scale. -/
structure SameValue (left right : SignedDyadicCode) where
  scale : CommonScale left right
  exact :
    liftedPositive left scale.leftExtra +
        liftedNegative right scale.rightExtra =
      liftedPositive right scale.rightExtra +
        liftedNegative left scale.leftExtra

namespace SameValue

def refl (code : SignedDyadicCode) : SameValue code code where
  scale := {
    common := code.scale
    leftExtra := 0
    rightExtra := 0
    leftExact := rfl
    rightExact := rfl
  }
  exact := rfl

def symm {left right : SignedDyadicCode}
    (same : SameValue left right) : SameValue right left where
  scale := same.scale.symm
  exact := same.exact.symm

/-- Raising the scale changes the code but not the represented signed dyadic. -/
def raiseExact (code : SignedDyadicCode) (extra : Nat) :
    SameValue code (code.raise extra) where
  scale := {
    common := code.scale + extra
    leftExtra := extra
    rightExtra := 0
    leftExact := rfl
    rightExact := rfl
  }
  exact := rfl

def liftCommon {left right : SignedDyadicCode}
    (same : SameValue left right) (extra : Nat) : SameValue left right where
  scale := {
    common := same.scale.common + extra
    leftExtra := same.scale.leftExtra + extra
    rightExtra := same.scale.rightExtra + extra
    leftExact := by
      calc
        left.scale + (same.scale.leftExtra + extra) =
            (left.scale + same.scale.leftExtra) + extra :=
          (Nat.add_assoc left.scale same.scale.leftExtra extra).symm
        _ = same.scale.common + extra :=
          congrArg (fun value => value + extra) same.scale.leftExact
    rightExact := by
      calc
        right.scale + (same.scale.rightExtra + extra) =
            (right.scale + same.scale.rightExtra) + extra :=
          (Nat.add_assoc right.scale same.scale.rightExtra extra).symm
        _ = same.scale.common + extra :=
          congrArg (fun value => value + extra) same.scale.rightExact
  }
  exact := by
    have scaled := congrArg (fun value => scaleNat value extra) same.exact
    rw [scaleNat_additive, scaleNat_additive] at scaled
    change
      liftedPositive left (same.scale.leftExtra + extra) +
          liftedNegative right (same.scale.rightExtra + extra) =
        liftedPositive right (same.scale.rightExtra + extra) +
          liftedNegative left (same.scale.leftExtra + extra)
    rw [liftedPositive_addSteps, liftedNegative_addSteps,
      liftedPositive_addSteps, liftedNegative_addSteps]
    exact scaled

def raiseBoth {left right : SignedDyadicCode}
    (same : SameValue left right) (extra : Nat) :
    SameValue (left.raise extra) (right.raise extra) := by
  refine {
    scale := {
      common := same.scale.common + extra
      leftExtra := same.scale.leftExtra
      rightExtra := same.scale.rightExtra
      leftExact := ?_
      rightExact := ?_
    }
    exact := ?_
  }
  · calc
      (left.raise extra).scale + same.scale.leftExtra =
          (left.scale + same.scale.leftExtra) + extra := by
        exact addSwapMiddle left.scale extra same.scale.leftExtra
      _ = same.scale.common + extra :=
        congrArg (fun value => value + extra) same.scale.leftExact
  · calc
      (right.raise extra).scale + same.scale.rightExtra =
          (right.scale + same.scale.rightExtra) + extra := by
        exact addSwapMiddle right.scale extra same.scale.rightExtra
      _ = same.scale.common + extra :=
        congrArg (fun value => value + extra) same.scale.rightExact
  · rw [liftedPositive_raise, liftedNegative_raise,
      liftedPositive_raise, liftedNegative_raise]
    exact (same.liftCommon extra).exact

def lowerRaised {left right : SignedDyadicCode} {extra : Nat}
    (same : SameValue (left.raise extra) (right.raise extra)) :
    SameValue left right where
  scale := {
    common := same.scale.common
    leftExtra := same.scale.leftExtra + extra
    rightExtra := same.scale.rightExtra + extra
    leftExact := by
      calc
        left.scale + (same.scale.leftExtra + extra) =
            (left.scale + same.scale.leftExtra) + extra :=
          (Nat.add_assoc left.scale same.scale.leftExtra extra).symm
        _ =
            (left.scale + extra) + same.scale.leftExtra := by
          exact addSwapMiddle left.scale same.scale.leftExtra extra
        _ = same.scale.common := same.scale.leftExact
    rightExact := by
      calc
        right.scale + (same.scale.rightExtra + extra) =
            (right.scale + same.scale.rightExtra) + extra :=
          (Nat.add_assoc right.scale same.scale.rightExtra extra).symm
        _ =
            (right.scale + extra) + same.scale.rightExtra := by
          exact addSwapMiddle right.scale same.scale.rightExtra extra
        _ = same.scale.common := same.scale.rightExact
  }
  exact := by
    rw [← liftedPositive_raise, ← liftedNegative_raise,
      ← liftedPositive_raise, ← liftedNegative_raise]
    exact same.exact

def trans {left middle right : SignedDyadicCode}
    (leftSame : SameValue left middle)
    (rightSame : SameValue middle right) : SameValue left right := by
  let leftLifted := leftSame.liftCommon rightSame.scale.common
  let rightLifted := rightSame.liftCommon leftSame.scale.common
  have commonExact : leftLifted.scale.common = rightLifted.scale.common :=
    Nat.add_comm leftSame.scale.common rightSame.scale.common
  have middleExtra :
      leftLifted.scale.rightExtra = rightLifted.scale.leftExtra := by
    apply addLeftCancel (a := middle.scale)
    calc
      middle.scale + leftLifted.scale.rightExtra =
          leftLifted.scale.common := leftLifted.scale.rightExact
      _ = rightLifted.scale.common := commonExact
      _ = middle.scale + rightLifted.scale.leftExtra :=
        rightLifted.scale.leftExact.symm
  have rightExact := rightLifted.exact
  rw [← middleExtra] at rightExact
  have forward :
      liftedPositive left leftLifted.scale.leftExtra +
          liftedNegative right rightLifted.scale.rightExtra ≤
        liftedPositive right rightLifted.scale.rightExtra +
          liftedNegative left leftLifted.scale.leftExtra := by
    exact composeSignedBound (tolerance := 0)
      (Nat.le_of_eq leftLifted.exact)
      (Nat.le_of_eq rightExact)
  have backward :
      liftedPositive right rightLifted.scale.rightExtra +
          liftedNegative left leftLifted.scale.leftExtra ≤
        liftedPositive left leftLifted.scale.leftExtra +
          liftedNegative right rightLifted.scale.rightExtra := by
    exact composeSignedBound (tolerance := 0)
      (Nat.le_of_eq rightExact.symm)
      (Nat.le_of_eq leftLifted.exact.symm)
  refine {
    scale := {
      common := leftLifted.scale.common
      leftExtra := leftLifted.scale.leftExtra
      rightExtra := rightLifted.scale.rightExtra
      leftExact := leftLifted.scale.leftExact
      rightExact := Eq.trans rightLifted.scale.rightExact commonExact.symm
    }
    exact := Nat.le_antisymm forward backward
  }

def raiseInvariant {left right : SignedDyadicCode} (extra : Nat) :
    (SameValue left right →
      SameValue (left.raise extra) (right.raise extra)) ×
    (SameValue (left.raise extra) (right.raise extra) →
      SameValue left right) :=
  ⟨fun same => same.raiseBoth extra, lowerRaised⟩

end SameValue

/-- A positive witness that `coarse` asks no more precision than `fine`. -/
structure PrecisionExtension (coarse fine : Nat) where
  extra : Nat
  exact : coarse + extra = fine

namespace PrecisionExtension

def refl (precision : Nat) : PrecisionExtension precision precision where
  extra := 0
  exact := rfl

def trans {coarse middle fine : Nat}
    (first : PrecisionExtension coarse middle)
    (second : PrecisionExtension middle fine) :
    PrecisionExtension coarse fine where
  extra := first.extra + second.extra
  exact := by
    calc
      coarse + (first.extra + second.extra) =
          (coarse + first.extra) + second.extra :=
        (Nat.add_assoc coarse first.extra second.extra).symm
      _ = middle + second.extra :=
        congrArg (fun value => value + second.extra) first.exact
      _ = fine := second.exact

end PrecisionExtension

/-- Symmetric dyadic proximity at precision `precision`.

At the recorded common scale, the two directed numerator differences are
bounded by the numerator representing `2⁻precision`.
-/
structure Near (precision : Nat) (left right : SignedDyadicCode) where
  scale : CommonScale left right
  precisionExtra : Nat
  precisionExact : precision + precisionExtra = scale.common
  leftBound :
    liftedPositive left scale.leftExtra +
        liftedNegative right scale.rightExtra ≤
      liftedPositive right scale.rightExtra +
        liftedNegative left scale.leftExtra +
          powerOfTwo precisionExtra
  rightBound :
    liftedPositive right scale.rightExtra +
        liftedNegative left scale.leftExtra ≤
      liftedPositive left scale.leftExtra +
        liftedNegative right scale.rightExtra +
          powerOfTwo precisionExtra

namespace Near

def refl (precision : Nat) (code : SignedDyadicCode) :
    Near precision code code where
  scale := {
    common := code.scale + precision
    leftExtra := precision
    rightExtra := precision
    leftExact := rfl
    rightExact := rfl
  }
  precisionExtra := code.scale
  precisionExact := Nat.add_comm precision code.scale
  leftBound := Nat.le_add_right _ _
  rightBound := Nat.le_add_right _ _

def symm {precision : Nat} {left right : SignedDyadicCode}
    (near : Near precision left right) : Near precision right left where
  scale := near.scale.symm
  precisionExtra := near.precisionExtra
  precisionExact := near.precisionExact
  leftBound := near.rightBound
  rightBound := near.leftBound

def weaken {coarse fine : Nat} {left right : SignedDyadicCode}
    (extension : PrecisionExtension coarse fine)
    (near : Near fine left right) : Near coarse left right where
  scale := near.scale
  precisionExtra := near.precisionExtra + extension.extra
  precisionExact := by
    calc
      coarse + (near.precisionExtra + extension.extra) =
          (coarse + near.precisionExtra) + extension.extra :=
        (Nat.add_assoc coarse near.precisionExtra extension.extra).symm
      _ =
          (coarse + extension.extra) + near.precisionExtra := by
        exact addSwapMiddle coarse near.precisionExtra extension.extra
      _ = fine + near.precisionExtra :=
        congrArg (fun value => value + near.precisionExtra) extension.exact
      _ = near.scale.common := near.precisionExact
  leftBound := by
    exact Nat.le_trans near.leftBound
      (Nat.add_le_add (Nat.le_refl _)
        (powerOfTwo_extension near.precisionExtra extension.extra))
  rightBound := by
    exact Nat.le_trans near.rightBound
      (Nat.add_le_add (Nat.le_refl _)
        (powerOfTwo_extension near.precisionExtra extension.extra))

def liftCommon {precision : Nat} {left right : SignedDyadicCode}
    (near : Near precision left right) (extra : Nat) :
    Near precision left right where
  scale := {
    common := near.scale.common + extra
    leftExtra := near.scale.leftExtra + extra
    rightExtra := near.scale.rightExtra + extra
    leftExact := by
      calc
        left.scale + (near.scale.leftExtra + extra) =
            (left.scale + near.scale.leftExtra) + extra :=
          (Nat.add_assoc left.scale near.scale.leftExtra extra).symm
        _ = near.scale.common + extra :=
          congrArg (fun value => value + extra) near.scale.leftExact
    rightExact := by
      calc
        right.scale + (near.scale.rightExtra + extra) =
            (right.scale + near.scale.rightExtra) + extra :=
          (Nat.add_assoc right.scale near.scale.rightExtra extra).symm
        _ = near.scale.common + extra :=
          congrArg (fun value => value + extra) near.scale.rightExact
  }
  precisionExtra := near.precisionExtra + extra
  precisionExact := by
    calc
      precision + (near.precisionExtra + extra) =
          (precision + near.precisionExtra) + extra :=
        (Nat.add_assoc precision near.precisionExtra extra).symm
      _ = near.scale.common + extra :=
        congrArg (fun value => value + extra) near.precisionExact
  leftBound := by
    have scaled := scaleSignedBound near.leftBound extra
    change
      liftedPositive left (near.scale.leftExtra + extra) +
          liftedNegative right (near.scale.rightExtra + extra) ≤
        liftedPositive right (near.scale.rightExtra + extra) +
          liftedNegative left (near.scale.leftExtra + extra) +
            powerOfTwo (near.precisionExtra + extra)
    rw [liftedPositive_addSteps, liftedNegative_addSteps,
      liftedPositive_addSteps, liftedNegative_addSteps, powerOfTwo_add]
    exact scaled
  rightBound := by
    have scaled := scaleSignedBound near.rightBound extra
    change
      liftedPositive right (near.scale.rightExtra + extra) +
          liftedNegative left (near.scale.leftExtra + extra) ≤
        liftedPositive left (near.scale.leftExtra + extra) +
          liftedNegative right (near.scale.rightExtra + extra) +
            powerOfTwo (near.precisionExtra + extra)
    rw [liftedPositive_addSteps, liftedNegative_addSteps,
      liftedPositive_addSteps, liftedNegative_addSteps, powerOfTwo_add]
    exact scaled

def raiseBoth {precision : Nat} {left right : SignedDyadicCode}
    (near : Near precision left right) (extra : Nat) :
    Near precision (left.raise extra) (right.raise extra) := by
  refine {
    scale := {
      common := near.scale.common + extra
      leftExtra := near.scale.leftExtra
      rightExtra := near.scale.rightExtra
      leftExact := ?_
      rightExact := ?_
    }
    precisionExtra := near.precisionExtra + extra
    precisionExact := ?_
    leftBound := ?_
    rightBound := ?_
  }
  · calc
      (left.raise extra).scale + near.scale.leftExtra =
          (left.scale + near.scale.leftExtra) + extra := by
        exact addSwapMiddle left.scale extra near.scale.leftExtra
      _ = near.scale.common + extra :=
        congrArg (fun value => value + extra) near.scale.leftExact
  · calc
      (right.raise extra).scale + near.scale.rightExtra =
          (right.scale + near.scale.rightExtra) + extra := by
        exact addSwapMiddle right.scale extra near.scale.rightExtra
      _ = near.scale.common + extra :=
        congrArg (fun value => value + extra) near.scale.rightExact
  · calc
      precision + (near.precisionExtra + extra) =
          (precision + near.precisionExtra) + extra :=
        (Nat.add_assoc precision near.precisionExtra extra).symm
      _ = near.scale.common + extra :=
        congrArg (fun value => value + extra) near.precisionExact
  · rw [liftedPositive_raise, liftedNegative_raise,
      liftedPositive_raise, liftedNegative_raise]
    exact (near.liftCommon extra).leftBound
  · rw [liftedPositive_raise, liftedNegative_raise,
      liftedPositive_raise, liftedNegative_raise]
    exact (near.liftCommon extra).rightBound

def raiseLeft {precision : Nat} {left right : SignedDyadicCode}
    (near : Near precision left right) (extra : Nat) :
    Near precision (left.raise extra) right := by
  refine {
    scale := {
      common := near.scale.common + extra
      leftExtra := near.scale.leftExtra
      rightExtra := near.scale.rightExtra + extra
      leftExact := ?_
      rightExact := ?_
    }
    precisionExtra := near.precisionExtra + extra
    precisionExact := ?_
    leftBound := ?_
    rightBound := ?_
  }
  · calc
      (left.raise extra).scale + near.scale.leftExtra =
          (left.scale + near.scale.leftExtra) + extra :=
        addSwapMiddle left.scale extra near.scale.leftExtra
      _ = near.scale.common + extra :=
        congrArg (fun value => value + extra) near.scale.leftExact
  · calc
      right.scale + (near.scale.rightExtra + extra) =
          (right.scale + near.scale.rightExtra) + extra :=
        (Nat.add_assoc right.scale near.scale.rightExtra extra).symm
      _ = near.scale.common + extra :=
        congrArg (fun value => value + extra) near.scale.rightExact
  · calc
      precision + (near.precisionExtra + extra) =
          (precision + near.precisionExtra) + extra :=
        (Nat.add_assoc precision near.precisionExtra extra).symm
      _ = near.scale.common + extra :=
        congrArg (fun value => value + extra) near.precisionExact
  · rw [liftedPositive_raise, liftedNegative_raise]
    exact (near.liftCommon extra).leftBound
  · rw [liftedPositive_raise, liftedNegative_raise]
    exact (near.liftCommon extra).rightBound

def raiseRight {precision : Nat} {left right : SignedDyadicCode}
    (near : Near precision left right) (extra : Nat) :
    Near precision left (right.raise extra) :=
  (near.symm.raiseLeft extra).symm

def lowerRaised {precision : Nat} {left right : SignedDyadicCode} {extra : Nat}
    (near : Near precision (left.raise extra) (right.raise extra)) :
    Near precision left right where
  scale := {
    common := near.scale.common
    leftExtra := near.scale.leftExtra + extra
    rightExtra := near.scale.rightExtra + extra
    leftExact := by
      calc
        left.scale + (near.scale.leftExtra + extra) =
            (left.scale + near.scale.leftExtra) + extra :=
          (Nat.add_assoc left.scale near.scale.leftExtra extra).symm
        _ =
            (left.scale + extra) + near.scale.leftExtra := by
          exact addSwapMiddle left.scale near.scale.leftExtra extra
        _ = near.scale.common := near.scale.leftExact
    rightExact := by
      calc
        right.scale + (near.scale.rightExtra + extra) =
            (right.scale + near.scale.rightExtra) + extra :=
          (Nat.add_assoc right.scale near.scale.rightExtra extra).symm
        _ =
            (right.scale + extra) + near.scale.rightExtra := by
          exact addSwapMiddle right.scale near.scale.rightExtra extra
        _ = near.scale.common := near.scale.rightExact
  }
  precisionExtra := near.precisionExtra
  precisionExact := near.precisionExact
  leftBound := by
    rw [← liftedPositive_raise, ← liftedNegative_raise,
      ← liftedPositive_raise, ← liftedNegative_raise]
    exact near.leftBound
  rightBound := by
    rw [← liftedPositive_raise, ← liftedNegative_raise,
      ← liftedPositive_raise, ← liftedNegative_raise]
    exact near.rightBound

def lowerLeft {precision : Nat} {left right : SignedDyadicCode} {extra : Nat}
    (near : Near precision (left.raise extra) right) :
    Near precision left right where
  scale := {
    common := near.scale.common
    leftExtra := near.scale.leftExtra + extra
    rightExtra := near.scale.rightExtra
    leftExact := by
      calc
        left.scale + (near.scale.leftExtra + extra) =
            (left.scale + near.scale.leftExtra) + extra :=
          (Nat.add_assoc left.scale near.scale.leftExtra extra).symm
        _ = (left.scale + extra) + near.scale.leftExtra :=
          addSwapMiddle left.scale near.scale.leftExtra extra
        _ = near.scale.common := near.scale.leftExact
    rightExact := near.scale.rightExact
  }
  precisionExtra := near.precisionExtra
  precisionExact := near.precisionExact
  leftBound := by
    rw [← liftedPositive_raise, ← liftedNegative_raise]
    exact near.leftBound
  rightBound := by
    rw [← liftedPositive_raise, ← liftedNegative_raise]
    exact near.rightBound

def lowerRight {precision : Nat} {left right : SignedDyadicCode} {extra : Nat}
    (near : Near precision left (right.raise extra)) :
    Near precision left right :=
  (near.symm.lowerLeft).symm

def raiseInvariant {precision : Nat} {left right : SignedDyadicCode}
    (extra : Nat) :
    (Near precision left right →
      Near precision (left.raise extra) (right.raise extra)) ×
    (Near precision (left.raise extra) (right.raise extra) →
      Near precision left right) :=
  ⟨fun near => near.raiseBoth extra, lowerRaised⟩

def leftRaiseInvariant {precision : Nat} {left right : SignedDyadicCode}
    (extra : Nat) :
    (Near precision left right → Near precision (left.raise extra) right) ×
    (Near precision (left.raise extra) right → Near precision left right) :=
  ⟨fun near => near.raiseLeft extra, lowerLeft⟩

def rightRaiseInvariant {precision : Nat} {left right : SignedDyadicCode}
    (extra : Nat) :
    (Near precision left right → Near precision left (right.raise extra)) ×
    (Near precision left (right.raise extra) → Near precision left right) :=
  ⟨fun near => near.raiseRight extra, lowerRight⟩

theorem succPrecision (precision extra : Nat) :
    Nat.succ precision + extra = precision + Nat.succ extra := by
  induction extra with
  | zero =>
      rfl
  | succ extra ih =>
      exact congrArg Nat.succ ih

def compose {precision : Nat} {left middle right : SignedDyadicCode}
    (leftNear : Near (Nat.succ precision) left middle)
    (rightNear : Near (Nat.succ precision) middle right) :
    Near precision left right := by
  let leftLifted := leftNear.liftCommon rightNear.scale.common
  let rightLifted := rightNear.liftCommon leftNear.scale.common
  have commonExact : leftLifted.scale.common = rightLifted.scale.common :=
    Nat.add_comm leftNear.scale.common rightNear.scale.common
  have middleExtra :
      leftLifted.scale.rightExtra = rightLifted.scale.leftExtra := by
    apply addLeftCancel (a := middle.scale)
    calc
      middle.scale + leftLifted.scale.rightExtra =
          leftLifted.scale.common := leftLifted.scale.rightExact
      _ = rightLifted.scale.common := commonExact
      _ = middle.scale + rightLifted.scale.leftExtra :=
        rightLifted.scale.leftExact.symm
  have toleranceExtra :
      leftLifted.precisionExtra = rightLifted.precisionExtra := by
    apply addLeftCancel (a := Nat.succ precision)
    calc
      Nat.succ precision + leftLifted.precisionExtra =
          leftLifted.scale.common := leftLifted.precisionExact
      _ = rightLifted.scale.common := commonExact
      _ = Nat.succ precision + rightLifted.precisionExtra :=
        rightLifted.precisionExact.symm
  have rightLeftBound := rightLifted.leftBound
  have rightRightBound := rightLifted.rightBound
  rw [← middleExtra, ← toleranceExtra] at rightLeftBound
  rw [← middleExtra, ← toleranceExtra] at rightRightBound
  refine {
    scale := {
      common := leftLifted.scale.common
      leftExtra := leftLifted.scale.leftExtra
      rightExtra := rightLifted.scale.rightExtra
      leftExact := leftLifted.scale.leftExact
      rightExact := ?_
    }
    precisionExtra := Nat.succ leftLifted.precisionExtra
    precisionExact := ?_
    leftBound := ?_
    rightBound := ?_
  }
  · exact Eq.trans rightLifted.scale.rightExact commonExact.symm
  · exact Eq.trans
      (succPrecision precision leftLifted.precisionExtra).symm
      leftLifted.precisionExact
  · change
      liftedPositive left leftLifted.scale.leftExtra +
          liftedNegative right rightLifted.scale.rightExtra ≤
        liftedPositive right rightLifted.scale.rightExtra +
          liftedNegative left leftLifted.scale.leftExtra +
            (powerOfTwo leftLifted.precisionExtra +
              powerOfTwo leftLifted.precisionExtra)
    exact composeSignedBound leftLifted.leftBound rightLeftBound
  · change
      liftedPositive right rightLifted.scale.rightExtra +
          liftedNegative left leftLifted.scale.leftExtra ≤
        liftedPositive left leftLifted.scale.leftExtra +
          liftedNegative right rightLifted.scale.rightExtra +
            (powerOfTwo leftLifted.precisionExtra +
              powerOfTwo leftLifted.precisionExtra)
    exact composeSignedBound rightRightBound leftLifted.rightBound

end Near

namespace SameValue

/-- Exact dyadic sameness supplies proximity at every requested precision. -/
def toNear
    {left right : SignedDyadicCode}
    (same : SameValue left right)
    (precision : Nat) : Near precision left right := by
  let lifted := same.liftCommon precision
  exact
  { scale := lifted.scale
    precisionExtra := same.scale.common
    precisionExact := Nat.add_comm precision same.scale.common
    leftBound := by
      calc
        liftedPositive left lifted.scale.leftExtra +
            liftedNegative right lifted.scale.rightExtra =
          liftedPositive right lifted.scale.rightExtra +
            liftedNegative left lifted.scale.leftExtra :=
          lifted.exact
        _ ≤
            liftedPositive right lifted.scale.rightExtra +
              liftedNegative left lifted.scale.leftExtra +
                powerOfTwo same.scale.common :=
          Nat.le_add_right _ _
    rightBound := by
      calc
        liftedPositive right lifted.scale.rightExtra +
            liftedNegative left lifted.scale.leftExtra =
          liftedPositive left lifted.scale.leftExtra +
            liftedNegative right lifted.scale.rightExtra :=
          lifted.exact.symm
        _ ≤
            liftedPositive left lifted.scale.leftExtra +
              liftedNegative right lifted.scale.rightExtra +
                powerOfTwo same.scale.common :=
          Nat.le_add_right _ _ }

end SameValue

end RelationalPerimeter.Constitution.Reals

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Constitution.Reals.scaleNat
#print axioms RelationalPerimeter.Constitution.Reals.powerOfTwo
#print axioms RelationalPerimeter.Constitution.Reals.addSwapMiddle
#print axioms RelationalPerimeter.Constitution.Reals.addRightCancel
#print axioms RelationalPerimeter.Constitution.Reals.addLeftCancel
#print axioms RelationalPerimeter.Constitution.Reals.leCancelRight
#print axioms RelationalPerimeter.Constitution.Reals.scaleNat_addSteps
#print axioms RelationalPerimeter.Constitution.Reals.scaleNat_additive
#print axioms RelationalPerimeter.Constitution.Reals.scaleNat_monotone
#print axioms RelationalPerimeter.Constitution.Reals.scaleNat_commutes
#print axioms RelationalPerimeter.Constitution.Reals.powerOfTwo_succ
#print axioms RelationalPerimeter.Constitution.Reals.powerOfTwo_add
#print axioms RelationalPerimeter.Constitution.Reals.powerOfTwo_extension
#print axioms RelationalPerimeter.Constitution.Reals.scaleSignedBound
#print axioms RelationalPerimeter.Constitution.Reals.composeSignedBound
#print axioms RelationalPerimeter.Constitution.Reals.SignedDyadicCode
#print axioms RelationalPerimeter.Constitution.Reals.SignedDyadicCode.raise
#print axioms RelationalPerimeter.Constitution.Reals.CommonScale
#print axioms RelationalPerimeter.Constitution.Reals.CommonScale.symm
#print axioms RelationalPerimeter.Constitution.Reals.liftedPositive
#print axioms RelationalPerimeter.Constitution.Reals.liftedNegative
#print axioms RelationalPerimeter.Constitution.Reals.liftedPositive_addSteps
#print axioms RelationalPerimeter.Constitution.Reals.liftedNegative_addSteps
#print axioms RelationalPerimeter.Constitution.Reals.liftedPositive_raise
#print axioms RelationalPerimeter.Constitution.Reals.liftedNegative_raise
#print axioms RelationalPerimeter.Constitution.Reals.SameValue
#print axioms RelationalPerimeter.Constitution.Reals.SameValue.refl
#print axioms RelationalPerimeter.Constitution.Reals.SameValue.symm
#print axioms RelationalPerimeter.Constitution.Reals.SameValue.raiseExact
#print axioms RelationalPerimeter.Constitution.Reals.SameValue.liftCommon
#print axioms RelationalPerimeter.Constitution.Reals.SameValue.raiseBoth
#print axioms RelationalPerimeter.Constitution.Reals.SameValue.lowerRaised
#print axioms RelationalPerimeter.Constitution.Reals.SameValue.trans
#print axioms RelationalPerimeter.Constitution.Reals.SameValue.raiseInvariant
#print axioms RelationalPerimeter.Constitution.Reals.PrecisionExtension
#print axioms RelationalPerimeter.Constitution.Reals.PrecisionExtension.refl
#print axioms RelationalPerimeter.Constitution.Reals.PrecisionExtension.trans
#print axioms RelationalPerimeter.Constitution.Reals.Near
#print axioms RelationalPerimeter.Constitution.Reals.Near.refl
#print axioms RelationalPerimeter.Constitution.Reals.Near.symm
#print axioms RelationalPerimeter.Constitution.Reals.Near.weaken
#print axioms RelationalPerimeter.Constitution.Reals.Near.liftCommon
#print axioms RelationalPerimeter.Constitution.Reals.Near.raiseBoth
#print axioms RelationalPerimeter.Constitution.Reals.Near.raiseLeft
#print axioms RelationalPerimeter.Constitution.Reals.Near.raiseRight
#print axioms RelationalPerimeter.Constitution.Reals.Near.lowerRaised
#print axioms RelationalPerimeter.Constitution.Reals.Near.lowerLeft
#print axioms RelationalPerimeter.Constitution.Reals.Near.lowerRight
#print axioms RelationalPerimeter.Constitution.Reals.Near.raiseInvariant
#print axioms RelationalPerimeter.Constitution.Reals.Near.leftRaiseInvariant
#print axioms RelationalPerimeter.Constitution.Reals.Near.rightRaiseInvariant
#print axioms RelationalPerimeter.Constitution.Reals.Near.succPrecision
#print axioms RelationalPerimeter.Constitution.Reals.Near.compose
#print axioms RelationalPerimeter.Constitution.Reals.SameValue.toNear
/- AXIOM_AUDIT_END -/
