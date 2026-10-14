import RelationalPerimeter.Constitution.HeytingArithmetic.ArithmeticFormulaTools

/-!
# Constructive finite beta encoding

This module builds constructively the finite sequence witness needed by the
arithmetic compiler, independently of Mathlib's Chinese remainder
implementation. Its congruence relation is witnessed positively by two
natural multiples of the modulus. The specialized inverses come from the
factorial shape of Goedel's beta moduli.
-/

namespace RelationalPerimeter
namespace HeytingArithmetic

/-- Structural factorial used by the internal beta encoding. -/
def betaFactorial : Nat -> Nat
  | 0 => 1
  | Nat.succ value => Nat.succ value * betaFactorial value

theorem betaFactorial_positive (value : Nat) :
    0 < betaFactorial value := by
  induction value with
  | zero => exact Nat.zero_lt_one
  | succ value inductionHypothesis =>
      exact Nat.mul_pos (Nat.succ_pos value) inductionHypothesis

/-- Multiplication associativity rebuilt by structural recursion. -/
theorem natMulAssoc (left middle right : Nat) :
    (left * middle) * right = left * (middle * right) := by
  induction right with
  | zero => rfl
  | succ right inductionHypothesis =>
      rw [Nat.mul_succ, Nat.mul_succ, Nat.mul_add, inductionHypothesis]

/-- Right distributivity rebuilt from left distributivity and commutativity. -/
theorem natAddMul (left right factor : Nat) :
    (left + right) * factor = left * factor + right * factor :=
  (Nat.mul_comm (left + right) factor).trans
    ((Nat.mul_add factor left right).trans
      (congrArgTwo Nat.add
        (Nat.mul_comm factor left)
        (Nat.mul_comm factor right)))

/-- Left commutation of multiplication from the constructive associativity law. -/
theorem natMulLeftComm (left middle right : Nat) :
    left * (middle * right) = middle * (left * right) :=
  (natMulAssoc left middle right).symm.trans
    ((congrArg (fun value => value * right) (Nat.mul_comm left middle)).trans
      (natMulAssoc middle left right))

/-- Exchange the two middle summands without algebraic automation. -/
theorem natAddInterchange (first second third fourth : Nat) :
    (first + second) + (third + fourth) =
      (first + third) + (second + fourth) :=
  (Nat.add_assoc first second (third + fourth)).trans
    ((congrArg (first + ·)
      ((Nat.add_assoc second third fourth).symm.trans
        ((congrArg (fun value => value + fourth)
          (Nat.add_comm second third)).trans
          (Nat.add_assoc third second fourth)))).trans
      (Nat.add_assoc first third (second + fourth)).symm)

/-- A right summand is below the whole sum, by recursion on the left one. -/
theorem natLeAddLeft (right left : Nat) : right <= left + right := by
  induction left with
  | zero =>
      rw [Nat.zero_add]
      exact Nat.le_refl right
  | succ left inductionHypothesis =>
      exact Eq.mp
        (congrArg (fun upper => right <= upper)
          (Nat.succ_add left right).symm)
        (Nat.le_trans inductionHypothesis (Nat.le_succ (left + right)))

/-- Swap the final two summands. -/
theorem natAddSwapRight (first second third : Nat) :
    (first + second) + third = (first + third) + second :=
  (Nat.add_assoc first second third).trans
    ((congrArg (first + ·) (Nat.add_comm second third)).trans
      (Nat.add_assoc first third second).symm)

/-- Swap two neighboring factors while retaining a prefix and a suffix. -/
theorem natMulSwapMiddle
    (common left right suffix : Nat) :
    ((common * left) * right) * suffix =
      ((common * right) * left) * suffix :=
  congrArg (· * suffix)
    ((natMulAssoc common left right).trans
      ((congrArg (common * ·) (Nat.mul_comm left right)).trans
        (natMulAssoc common right left).symm))

/-- Exchange the two middle factors of two displayed products. -/
theorem natMulInterchange
    (first second third fourth : Nat) :
    (first * second) * (third * fourth) =
      (first * third) * (second * fourth) :=
  (natMulAssoc (first * second) third fourth).symm.trans
    ((natMulSwapMiddle first second third fourth).trans
      (natMulAssoc (first * third) second fourth))

/-- A direct natural-number certificate for the beta inverse equation. -/
theorem natBetaAlgebra
    (current correction next interaction : Nat)
    (linear : current + correction = next)
    (cross : correction * interaction = next * current) :
    (current + 1) + correction * (interaction + 1) =
      1 + next * (current + 1) := by
  calc
    (current + 1) + correction * (interaction + 1) =
        (current + 1) +
          (correction * interaction + correction * 1) :=
      congrArg ((current + 1) + ·)
        (Nat.mul_add correction interaction 1)
    _ = (current + 1) + (correction * interaction + correction) :=
      congrArg
        (fun value => (current + 1) +
          (correction * interaction + value))
        (Nat.mul_one correction)
    _ = (1 + current) + (correction * interaction + correction) :=
      congrArg
        (fun value => value + (correction * interaction + correction))
        (Nat.add_comm current 1)
    _ = (1 + correction * interaction) + (current + correction) :=
      natAddInterchange 1 current (correction * interaction) correction
    _ = 1 + (correction * interaction + (current + correction)) :=
      Nat.add_assoc 1 (correction * interaction) (current + correction)
    _ = 1 + (next * current + next) :=
      congrArg (1 + ·) (congrArgTwo Nat.add cross linear)
    _ = 1 + (next * current + next * 1) :=
      congrArg
        (fun value => 1 + (next * current + value))
        (Nat.mul_one next).symm
    _ = 1 + next * (current + 1) :=
      congrArg (1 + ·) (Nat.mul_add next current 1).symm

/-- Lift the beta core equation through the final modulus multiplication. -/
theorem natBetaExpanded
    (base correction multiplier interaction : Nat)
    (core :
      base + correction * (interaction + 1) =
        1 + multiplier * base) :
    base * (1 + multiplier * interaction) +
        correction * (interaction + 1) =
      1 + (multiplier * base) * (interaction + 1) := by
  have cross :
      base * (multiplier * interaction) =
        (multiplier * base) * interaction :=
    (natMulAssoc base multiplier interaction).symm.trans
      (congrArg (· * interaction) (Nat.mul_comm base multiplier))
  calc
    base * (1 + multiplier * interaction) +
        correction * (interaction + 1) =
      (base * 1 + base * (multiplier * interaction)) +
        correction * (interaction + 1) :=
      congrArg (· + correction * (interaction + 1))
        (Nat.mul_add base 1 (multiplier * interaction))
    _ = (base + base * (multiplier * interaction)) +
        correction * (interaction + 1) :=
      congrArg
        (fun value =>
          (value + base * (multiplier * interaction)) +
            correction * (interaction + 1))
        (Nat.mul_one base)
    _ = (base + correction * (interaction + 1)) +
        base * (multiplier * interaction) :=
      natAddSwapRight
        base
        (base * (multiplier * interaction))
        (correction * (interaction + 1))
    _ = (1 + multiplier * base) +
        base * (multiplier * interaction) :=
      congrArg
        (fun value => value + base * (multiplier * interaction)) core
    _ = (1 + multiplier * base) +
        (multiplier * base) * interaction :=
      congrArg ((1 + multiplier * base) + ·) cross
    _ = 1 +
        (multiplier * base + (multiplier * base) * interaction) :=
      Nat.add_assoc 1 (multiplier * base)
        ((multiplier * base) * interaction)
    _ = 1 +
        ((multiplier * base) * interaction + multiplier * base) :=
      congrArg (1 + ·)
        (Nat.add_comm
          (multiplier * base)
          ((multiplier * base) * interaction))
    _ = 1 +
        ((multiplier * base) * interaction +
          (multiplier * base) * 1) :=
      congrArg
        (fun value =>
          1 + ((multiplier * base) * interaction + value))
        (Nat.mul_one (multiplier * base)).symm
    _ = 1 + (multiplier * base) * (interaction + 1) :=
      congrArg (1 + ·)
        (Nat.mul_add (multiplier * base) interaction 1).symm

/-- Positive natural congruence, witnessed without quotients or residue classes. -/
def NatCongruent (left right modulus : Nat) : Prop :=
  Exists fun leftMultiple : Nat =>
    Exists fun rightMultiple : Nat =>
      left + leftMultiple * modulus = right + rightMultiple * modulus

theorem NatCongruent.refl (value modulus : Nat) :
    NatCongruent value value modulus :=
  Exists.intro 0 (Exists.intro 0 rfl)

theorem NatCongruent.ofEq
    {left right modulus : Nat}
    (equality : left = right) :
    NatCongruent left right modulus := by
  cases equality
  exact NatCongruent.refl left modulus

theorem NatCongruent.symm
    {left right modulus : Nat}
    (congruent : NatCongruent left right modulus) :
    NatCongruent right left modulus := by
  rcases congruent with ⟨leftMultiple, rightMultiple, equality⟩
  exact ⟨rightMultiple, leftMultiple, equality.symm⟩

theorem NatCongruent.trans
    {left middle right modulus : Nat}
    (first : NatCongruent left middle modulus)
    (second : NatCongruent middle right modulus) :
    NatCongruent left right modulus := by
  rcases first with ⟨firstLeft, firstRight, firstEquality⟩
  rcases second with ⟨secondLeft, secondRight, secondEquality⟩
  refine ⟨firstLeft + secondLeft, secondRight + firstRight, ?_⟩
  calc
    left + (firstLeft + secondLeft) * modulus =
        left + (firstLeft * modulus + secondLeft * modulus) :=
      congrArg (left + ·) (natAddMul firstLeft secondLeft modulus)
    _ = (left + firstLeft * modulus) + secondLeft * modulus :=
      (Nat.add_assoc left (firstLeft * modulus)
        (secondLeft * modulus)).symm
    _ = (middle + firstRight * modulus) + secondLeft * modulus :=
      congrArg (fun value => value + secondLeft * modulus) firstEquality
    _ = middle + (firstRight * modulus + secondLeft * modulus) :=
      Nat.add_assoc middle (firstRight * modulus) (secondLeft * modulus)
    _ = middle + (secondLeft * modulus + firstRight * modulus) :=
      congrArg (middle + ·)
        (Nat.add_comm (firstRight * modulus) (secondLeft * modulus))
    _ = (middle + secondLeft * modulus) + firstRight * modulus :=
      (Nat.add_assoc middle (secondLeft * modulus)
        (firstRight * modulus)).symm
    _ = (right + secondRight * modulus) + firstRight * modulus :=
      congrArg (fun value => value + firstRight * modulus) secondEquality
    _ = right + (secondRight * modulus + firstRight * modulus) :=
      Nat.add_assoc right (secondRight * modulus) (firstRight * modulus)
    _ = right + (secondRight + firstRight) * modulus :=
      congrArg (right + ·) (natAddMul secondRight firstRight modulus).symm

theorem NatCongruent.add
    {left₁ right₁ left₂ right₂ modulus : Nat}
    (first : NatCongruent left₁ right₁ modulus)
    (second : NatCongruent left₂ right₂ modulus) :
    NatCongruent (left₁ + left₂) (right₁ + right₂) modulus := by
  rcases first with ⟨firstLeft, firstRight, firstEquality⟩
  rcases second with ⟨secondLeft, secondRight, secondEquality⟩
  refine ⟨firstLeft + secondLeft, firstRight + secondRight, ?_⟩
  calc
    left₁ + left₂ + (firstLeft + secondLeft) * modulus =
        left₁ + left₂ +
          (firstLeft * modulus + secondLeft * modulus) :=
      congrArg (left₁ + left₂ + ·)
        (natAddMul firstLeft secondLeft modulus)
    _ = (left₁ + firstLeft * modulus) +
          (left₂ + secondLeft * modulus) :=
      natAddInterchange left₁ left₂
        (firstLeft * modulus) (secondLeft * modulus)
    _ = (right₁ + firstRight * modulus) +
          (right₂ + secondRight * modulus) :=
      congrArgTwo Nat.add firstEquality secondEquality
    _ = right₁ + right₂ +
          (firstRight * modulus + secondRight * modulus) :=
      natAddInterchange right₁ (firstRight * modulus)
        right₂ (secondRight * modulus)
    _ = right₁ + right₂ + (firstRight + secondRight) * modulus :=
      congrArg (right₁ + right₂ + ·)
        (natAddMul firstRight secondRight modulus).symm

/-- Multiplying congruent naturals by the same right factor preserves congruence. -/
theorem NatCongruent.mulRight
    {left right modulus : Nat}
    (congruent : NatCongruent left right modulus)
    (factor : Nat) :
    NatCongruent (left * factor) (right * factor) modulus := by
  rcases congruent with ⟨leftMultiple, rightMultiple, equality⟩
  refine ⟨leftMultiple * factor, rightMultiple * factor, ?_⟩
  calc
    left * factor + (leftMultiple * factor) * modulus =
        left * factor + (leftMultiple * modulus) * factor :=
      congrArg (left * factor + ·)
        ((natMulAssoc leftMultiple factor modulus).trans
          ((congrArg (leftMultiple * ·)
            (Nat.mul_comm factor modulus)).trans
            (natMulAssoc leftMultiple modulus factor).symm))
    _ = (left + leftMultiple * modulus) * factor :=
      (natAddMul left (leftMultiple * modulus) factor).symm
    _ = (right + rightMultiple * modulus) * factor :=
      congrArg (fun value => value * factor) equality
    _ = right * factor + (rightMultiple * modulus) * factor :=
      natAddMul right (rightMultiple * modulus) factor
    _ = right * factor + (rightMultiple * factor) * modulus :=
      congrArg (right * factor + ·)
        ((natMulAssoc rightMultiple modulus factor).trans
          ((congrArg (rightMultiple * ·)
            (Nat.mul_comm modulus factor)).trans
            (natMulAssoc rightMultiple factor modulus).symm))

theorem NatCongruent.mul
    {left₁ right₁ left₂ right₂ modulus : Nat}
    (first : NatCongruent left₁ right₁ modulus)
    (second : NatCongruent left₂ right₂ modulus) :
    NatCongruent (left₁ * left₂) (right₁ * right₂) modulus := by
  have firstScaled := first.mulRight left₂
  have secondScaled := second.mulRight right₁
  have reordered :
      NatCongruent (right₁ * left₂) (left₂ * right₁) modulus := by
    exact NatCongruent.ofEq (Nat.mul_comm right₁ left₂)
  have finalReordered :
      NatCongruent (right₂ * right₁) (right₁ * right₂) modulus := by
    exact NatCongruent.ofEq (Nat.mul_comm right₂ right₁)
  exact firstScaled.trans
    (reordered.trans (secondScaled.trans finalReordered))

theorem NatCongruent.addRight
    {left right modulus : Nat}
    (congruent : NatCongruent left right modulus)
    (value : Nat) :
    NatCongruent (left + value) (right + value) modulus :=
  NatCongruent.add congruent (NatCongruent.refl value modulus)

/-- Adding a displayed multiple does not change a congruence class. -/
theorem NatCongruent.addMultiple (value multiple modulus : Nat) :
    NatCongruent (value + multiple * modulus) value modulus := by
  refine ⟨0, multiple, ?_⟩
  calc
    value + multiple * modulus + 0 * modulus =
        value + multiple * modulus + 0 :=
      congrArg (value + multiple * modulus + ·) (Nat.zero_mul modulus)
    _ = value + multiple * modulus := Nat.add_zero _

/-- Structural remainders are invariant under positively witnessed congruence. -/
theorem constructiveRemainder_eq_of_congruent
    {left right modulus : Nat}
    (positive : 0 < modulus)
    (congruent : NatCongruent left right modulus) :
    constructiveRemainder left modulus =
      constructiveRemainder right modulus := by
  rcases congruent with ⟨leftMultiple, rightMultiple, equality⟩
  let leftSpec := constructiveDivMod_spec left modulus positive
  let rightSpec := constructiveDivMod_spec right modulus positive
  apply boundedRemainder_unique
    (dividend := left + leftMultiple * modulus)
    (leftQuotient := constructiveQuotient left modulus + leftMultiple)
    (rightQuotient := constructiveQuotient right modulus + rightMultiple)
  · calc
      left + leftMultiple * modulus =
          (constructiveQuotient left modulus * modulus +
            constructiveRemainder left modulus) +
              leftMultiple * modulus :=
        congrArg (fun value => value + leftMultiple * modulus) leftSpec.1
      _ = (constructiveQuotient left modulus + leftMultiple) * modulus +
          constructiveRemainder left modulus :=
        (natAddSwapRight
          (constructiveQuotient left modulus * modulus)
          (constructiveRemainder left modulus)
          (leftMultiple * modulus)).trans
          (congrArg
            (fun product => product + constructiveRemainder left modulus)
            (natAddMul
              (constructiveQuotient left modulus)
              leftMultiple modulus).symm)
  · calc
      left + leftMultiple * modulus = right + rightMultiple * modulus := equality
      _ = (constructiveQuotient right modulus * modulus +
            constructiveRemainder right modulus) +
              rightMultiple * modulus :=
        congrArg (fun value => value + rightMultiple * modulus) rightSpec.1
      _ = (constructiveQuotient right modulus + rightMultiple) * modulus +
          constructiveRemainder right modulus :=
        (natAddSwapRight
          (constructiveQuotient right modulus * modulus)
          (constructiveRemainder right modulus)
          (rightMultiple * modulus)).trans
          (congrArg
            (fun product => product + constructiveRemainder right modulus)
            (natAddMul
              (constructiveQuotient right modulus)
              rightMultiple modulus).symm)
  · exact leftSpec.2
  · exact rightSpec.2

/-- A value already below a positive modulus is its structural remainder. -/
theorem constructiveRemainder_eq_of_lt
    {value modulus : Nat}
    (bounded : value < modulus) :
    constructiveRemainder value modulus = value := by
  have positive : 0 < modulus := Nat.lt_of_le_of_lt (Nat.zero_le value) bounded
  let specification := constructiveDivMod_spec value modulus positive
  apply boundedRemainder_unique
    (dividend := value)
    (leftQuotient := constructiveQuotient value modulus)
    (rightQuotient := 0)
  · exact specification.1
  · calc
      value = 0 + value := (Nat.zero_add value).symm
      _ = 0 * modulus + value :=
        congrArg (fun zeroValue => zeroValue + value) (Nat.zero_mul modulus).symm
  · exact specification.2
  · exact bounded

/-- Every number is positively congruent to its structural remainder. -/
theorem value_congruent_constructiveRemainder
    (value modulus : Nat)
    (positive : 0 < modulus) :
    NatCongruent value (constructiveRemainder value modulus) modulus := by
  let specification := constructiveDivMod_spec value modulus positive
  refine ⟨0, constructiveQuotient value modulus, ?_⟩
  calc
    value + 0 * modulus = value + 0 :=
      congrArg (value + ·) (Nat.zero_mul modulus)
    _ = value := Nat.add_zero value
    _ = constructiveQuotient value modulus * modulus +
        constructiveRemainder value modulus := specification.1
    _ = constructiveRemainder value modulus +
        constructiveQuotient value modulus * modulus := Nat.add_comm _ _

/-- A divisor has zero structural remainder. -/
theorem constructiveRemainder_eq_zero_of_dvd
    {dividend modulus : Nat}
    (positive : 0 < modulus)
    (divides : modulus ∣ dividend) :
    constructiveRemainder dividend modulus = 0 := by
  rcases divides with ⟨quotient, quotientEquation⟩
  let specification := constructiveDivMod_spec dividend modulus positive
  apply boundedRemainder_unique
    (dividend := dividend)
    (leftQuotient := constructiveQuotient dividend modulus)
    (rightQuotient := quotient)
  · exact specification.1
  · calc
      dividend = modulus * quotient := quotientEquation
      _ = quotient * modulus := Nat.mul_comm modulus quotient
      _ = quotient * modulus + 0 := (Nat.add_zero _).symm
  · exact specification.2
  · exact positive

/-- Exact structural quotient at a positive divisor. -/
theorem constructiveQuotient_mul_eq_of_dvd
    {dividend modulus : Nat}
    (positive : 0 < modulus)
    (divides : modulus ∣ dividend) :
    constructiveQuotient dividend modulus * modulus = dividend := by
  have specification := constructiveDivMod_spec dividend modulus positive
  have remainderZero := constructiveRemainder_eq_zero_of_dvd positive divides
  exact (Nat.add_zero _).symm.trans
    ((congrArg
      (fun remainder =>
        constructiveQuotient dividend modulus * modulus + remainder)
      remainderZero).symm.trans specification.1.symm)

/-- Fully constructive proof that every positive bounded number divides a factorial. -/
theorem dvd_factorial_constructive
    {divisor upper : Nat}
    (positive : 0 < divisor)
    (bounded : divisor <= upper) :
    divisor ∣ betaFactorial upper := by
  induction upper with
  | zero =>
      have impossible : 0 < 0 := Nat.lt_of_lt_of_le positive bounded
      exact (Nat.lt_irrefl 0 impossible).elim
  | succ upper inductionHypothesis =>
      cases Nat.lt_or_eq_of_le bounded with
      | inl earlier =>
          rcases inductionHypothesis (Nat.le_of_lt_succ earlier) with
            ⟨quotient, quotientEquation⟩
          refine ⟨Nat.succ upper * quotient, ?_⟩
          simp only [betaFactorial]
          calc
            Nat.succ upper * betaFactorial upper =
                Nat.succ upper * (divisor * quotient) :=
              congrArg (Nat.succ upper * ·) quotientEquation
            _ = divisor * (Nat.succ upper * quotient) :=
              (natMulAssoc (Nat.succ upper) divisor quotient).symm.trans
                ((congrArg (fun value => value * quotient)
                  (Nat.mul_comm (Nat.succ upper) divisor)).trans
                    (natMulAssoc divisor (Nat.succ upper) quotient))
      | inr equal =>
          cases equal
          exact ⟨betaFactorial upper, rfl⟩

/-- Factorials of positive arguments dominate those arguments. -/
theorem self_le_factorial_constructive
    {value : Nat}
    (positive : 0 < value) :
    value <= betaFactorial value := by
  cases value with
  | zero => exact (Nat.not_lt_zero 0 positive).elim
  | succ predecessor =>
      simp only [betaFactorial]
      exact Nat.le_mul_of_pos_right
        (Nat.succ predecessor) (betaFactorial_positive predecessor)

/-- Additive bound for every entry of a finite vector. -/
def NatVector.maximum {length : Nat} (values : NatVector length) : Nat :=
  match values with
  | NatVector.nil => 0
  | NatVector.cons head tail => head + tail.maximum

/-- Every vector entry is bounded by its computed maximum. -/
theorem NatVector.get_le_maximum
    {length index : Nat}
    (values : NatVector length)
    (bounded : index < length) :
    values.get index bounded <= values.maximum := by
  induction values generalizing index with
  | nil => exact (Nat.not_lt_zero index bounded).elim
  | cons head tail inductionHypothesis =>
      cases index with
      | zero => exact Nat.le_add_right head tail.maximum
      | succ index =>
          exact Nat.le_trans
            (inductionHypothesis
              (index := index) (Nat.lt_of_succ_lt_succ bounded))
            (natLeAddLeft tail.maximum head)

/-- Strict common bound for vector length and every vector entry. -/
def NatVector.betaBound
    {length : Nat}
    (values : NatVector length) : Nat :=
  Nat.succ (length + values.maximum)

/-- Factorial coefficient used by the internal Goedel beta witness. -/
def NatVector.betaCoefficient
    {length : Nat}
    (values : NatVector length) : Nat :=
  betaFactorial values.betaBound

/-- The modulus assigned to one vector position. -/
def betaModulusFor (coefficient index : Nat) : Nat :=
  (index + 1) * coefficient + 1

def NatVector.betaModulus
    {length : Nat}
    (values : NatVector length)
    (index : Nat) : Nat :=
  betaModulusFor values.betaCoefficient index

/-- Every genuine vector entry is strictly below its beta modulus. -/
theorem NatVector.get_lt_betaModulus
    {length index : Nat}
    (values : NatVector length)
    (bounded : index < length) :
    values.get index bounded < values.betaModulus index := by
  have belowBound : values.get index bounded < values.betaBound := by
    unfold NatVector.betaBound
    exact Nat.lt_succ_of_le
      (Nat.le_trans
        (values.get_le_maximum bounded)
        (natLeAddLeft values.maximum length))
  have boundBelowCoefficient : values.betaBound <= values.betaCoefficient :=
    self_le_factorial_constructive (Nat.zero_lt_succ _)
  have coefficientBelowModulus :
      values.betaCoefficient <= values.betaModulus index := by
    unfold NatVector.betaModulus betaModulusFor
    have multipliedRight :=
      Nat.le_mul_of_pos_right values.betaCoefficient (Nat.succ_pos index)
    have multiplied :
        values.betaCoefficient <= (index + 1) * values.betaCoefficient :=
      Eq.mp
        (congrArg
          (fun product => values.betaCoefficient <= product)
          (Nat.mul_comm values.betaCoefficient (index + 1)))
        multipliedRight
    exact Nat.le_trans multiplied
      (Nat.le_succ ((index + 1) * values.betaCoefficient))
  exact Nat.lt_of_lt_of_le belowBound
    (Nat.le_trans boundBelowCoefficient coefficientBelowModulus)

/-- Product of the first `count` beta moduli. -/
def betaPrefixProduct (coefficient : Nat) : Nat -> Nat
  | 0 => 1
  | Nat.succ count =>
      betaPrefixProduct coefficient count * betaModulusFor coefficient count

/-- Structural truncated difference, independent of Mathlib subtraction lemmas. -/
def constructiveDifference (value : Nat) : Nat -> Nat
  | 0 => value
  | Nat.succ smaller =>
      match value with
      | 0 => 0
      | Nat.succ predecessor =>
          constructiveDifference predecessor smaller

/-- Removing a displayed left summand returns its positive remainder. -/
theorem constructiveDifference_add_left (left gap : Nat) :
    constructiveDifference (left + gap) left = gap := by
  induction left with
  | zero =>
      rw [Nat.zero_add]
      unfold constructiveDifference
      rfl
  | succ left inductionHypothesis =>
      change constructiveDifference (Nat.succ left + gap) (Nat.succ left) = gap
      rw [Nat.succ_add]
      exact inductionHypothesis

/-- A strict inequality gives a positive, exact structural difference. -/
theorem constructiveDifference_spec_of_lt
    {smaller larger : Nat}
    (strict : smaller < larger) :
    0 < constructiveDifference larger smaller ∧
      smaller + constructiveDifference larger smaller = larger := by
  rcases natExistsAddSuccEqOfLt strict with ⟨gap, equality⟩
  have differenceEquation :
      constructiveDifference larger smaller = Nat.succ gap := by
    calc
      constructiveDifference larger smaller =
          constructiveDifference (smaller + Nat.succ gap) smaller :=
        congrArg (constructiveDifference · smaller) equality.symm
      _ = Nat.succ gap := constructiveDifference_add_left smaller (Nat.succ gap)
  constructor
  · exact Eq.mp
      (congrArg (fun value => 0 < value) differenceEquation.symm)
      (Nat.zero_lt_succ gap)
  · exact (congrArg (smaller + ·) differenceEquation).trans equality

/-- Specialized natural inverse for two factorial beta moduli. -/
def betaPairInverse (coefficient left right : Nat) : Nat :=
  let leftFactor := left + 1
  let rightFactor := right + 1
  let gap := constructiveDifference rightFactor leftFactor
  let quotient := constructiveQuotient coefficient gap
  let multiplier := leftFactor * quotient * rightFactor
  1 + multiplier * (rightFactor * coefficient)

/-- Product of the specialized inverses for a new modulus. -/
def betaPrefixInverse (coefficient newIndex : Nat) : Nat -> Nat
  | 0 => 1
  | Nat.succ count =>
      betaPrefixInverse coefficient newIndex count *
        betaPairInverse coefficient count newIndex

/-- The arithmetic identity underlying one specialized beta inverse. -/
theorem betaPairAlgebra (leftFactor gap quotient : Nat) :
    let rightFactor := leftFactor + gap
    let coefficient := quotient * gap
    let leftModulus := leftFactor * coefficient + 1
    let rightModulus := rightFactor * coefficient + 1
    let multiplier := leftFactor * quotient * rightFactor
    leftModulus * (1 + multiplier * (rightFactor * coefficient)) +
        (leftFactor * quotient * leftFactor) * rightModulus =
      1 + (multiplier * leftModulus) * rightModulus := by
  dsimp only
  apply natBetaExpanded
  apply natBetaAlgebra
  · calc
      leftFactor * (quotient * gap) +
          leftFactor * quotient * leftFactor =
        (leftFactor * quotient) * gap +
          leftFactor * quotient * leftFactor :=
        congrArg
          (fun value => value + leftFactor * quotient * leftFactor)
          (natMulAssoc leftFactor quotient gap).symm
      _ = leftFactor * quotient * leftFactor +
          (leftFactor * quotient) * gap := Nat.add_comm _ _
      _ = (leftFactor * quotient) * (leftFactor + gap) :=
        (Nat.mul_add (leftFactor * quotient) leftFactor gap).symm
  · calc
      (leftFactor * quotient * leftFactor) *
          ((leftFactor + gap) * (quotient * gap)) =
        ((leftFactor * quotient * leftFactor) *
          (leftFactor + gap)) * (quotient * gap) :=
        (natMulAssoc
          (leftFactor * quotient * leftFactor)
          (leftFactor + gap)
          (quotient * gap)).symm
      _ = ((leftFactor * quotient * (leftFactor + gap)) *
          leftFactor) * (quotient * gap) :=
        natMulSwapMiddle
          (leftFactor * quotient)
          leftFactor
          (leftFactor + gap)
          (quotient * gap)
      _ = (leftFactor * quotient * (leftFactor + gap)) *
          (leftFactor * (quotient * gap)) :=
        natMulAssoc
          (leftFactor * quotient * (leftFactor + gap))
          leftFactor
          (quotient * gap)

/-- Each specialized inverse is valid for its later beta modulus. -/
theorem betaPairInverse_congruent_of_dvd
    {coefficient left right : Nat}
    (ordered : left < right)
    (gapDivides :
      constructiveDifference (right + 1) (left + 1) ∣ coefficient) :
    NatCongruent
      (betaModulusFor coefficient left *
        betaPairInverse coefficient left right)
      1
      (betaModulusFor coefficient right) := by
  let leftFactor := left + 1
  let rightFactor := right + 1
  let gap := constructiveDifference rightFactor leftFactor
  let quotient := constructiveQuotient coefficient gap
  have factorsOrdered : leftFactor < rightFactor :=
    Nat.add_lt_add_right ordered 1
  have gapSpecification := constructiveDifference_spec_of_lt factorsOrdered
  have gapPositive : 0 < gap := gapSpecification.1
  have quotientProduct : quotient * gap = coefficient :=
    constructiveQuotient_mul_eq_of_dvd gapPositive gapDivides
  have factorEquation : leftFactor + gap = rightFactor := gapSpecification.2
  refine ⟨
    leftFactor * quotient * leftFactor,
    (leftFactor * quotient * rightFactor) *
      betaModulusFor coefficient left,
    ?_⟩
  change
    (leftFactor * coefficient + 1) *
        (1 + (leftFactor * quotient * rightFactor) *
          (rightFactor * coefficient)) +
      (leftFactor * quotient * leftFactor) *
        (rightFactor * coefficient + 1) =
      1 +
        ((leftFactor * quotient * rightFactor) *
          (leftFactor * coefficient + 1)) *
            (rightFactor * coefficient + 1)
  rw [← factorEquation, ← quotientProduct]
  exact betaPairAlgebra leftFactor gap quotient

/-- Every earlier beta modulus has its specialized inverse at a later index. -/
theorem NatVector.betaPairInverse_congruent
    {length left right : Nat}
    (values : NatVector length)
    (rightBounded : right < length)
    (ordered : left < right) :
    NatCongruent
      (values.betaModulus left *
        betaPairInverse values.betaCoefficient left right)
      1
      (values.betaModulus right) := by
  apply betaPairInverse_congruent_of_dvd ordered
  apply dvd_factorial_constructive
  · exact (constructiveDifference_spec_of_lt
      (Nat.add_lt_add_right ordered 1)).1
  · unfold NatVector.betaBound
    have differenceSpecification := constructiveDifference_spec_of_lt
      (Nat.add_lt_add_right ordered 1)
    have belowRight :
        constructiveDifference (right + 1) (left + 1) <= right + 1 :=
      Eq.mp
        (congrArg
          (fun upper =>
            constructiveDifference (right + 1) (left + 1) <= upper)
          differenceSpecification.2)
        (natLeAddLeft
          (constructiveDifference (right + 1) (left + 1)) (left + 1))
    exact Nat.le_trans belowRight
      (Nat.le_trans
        (Nat.succ_le_of_lt rightBounded)
        (Nat.le_succ_of_le (Nat.le_add_right length values.maximum)))

/-- The product of all earlier moduli has a product inverse at the new one. -/
theorem NatVector.betaPrefixInverse_congruent
    {length newIndex count : Nat}
    (values : NatVector length)
    (newBounded : newIndex < length)
    (prefixBounded : count <= newIndex) :
    NatCongruent
      (betaPrefixProduct values.betaCoefficient count *
        betaPrefixInverse values.betaCoefficient newIndex count)
      1
      (values.betaModulus newIndex) := by
  induction count with
  | zero =>
      change NatCongruent (1 * 1) 1 (values.betaModulus newIndex)
      exact NatCongruent.ofEq (Nat.one_mul 1)
  | succ count inductionHypothesis =>
      have countEarlier : count < newIndex :=
        Nat.lt_of_succ_le prefixBounded
      have previous := inductionHypothesis (Nat.le_of_lt countEarlier)
      have current := values.betaPairInverse_congruent
        newBounded countEarlier
      have product := previous.mul current
      have productOne :
          NatCongruent
            ((betaPrefixProduct values.betaCoefficient count *
                betaPrefixInverse values.betaCoefficient newIndex count) *
              (values.betaModulus count *
                betaPairInverse values.betaCoefficient count newIndex))
            1
            (values.betaModulus newIndex) :=
        product.trans (NatCongruent.ofEq (Nat.one_mul 1))
      change NatCongruent
        ((betaPrefixProduct values.betaCoefficient count *
            values.betaModulus count) *
          (betaPrefixInverse values.betaCoefficient newIndex count *
            betaPairInverse values.betaCoefficient count newIndex))
        1 (values.betaModulus newIndex)
      exact (NatCongruent.ofEq
        (natMulInterchange
          (betaPrefixProduct values.betaCoefficient count)
          (values.betaModulus count)
          (betaPrefixInverse values.betaCoefficient newIndex count)
          (betaPairInverse values.betaCoefficient count newIndex))).trans
        productOne

/-- Every modulus occurring before a prefix bound divides the prefix product. -/
theorem betaModulusFor_dvd_prefixProduct
    {coefficient index count : Nat}
    (bounded : index < count) :
    betaModulusFor coefficient index ∣ betaPrefixProduct coefficient count := by
  induction count with
  | zero => exact (Nat.not_lt_zero index bounded).elim
  | succ count inductionHypothesis =>
      cases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ bounded) with
      | inl earlier =>
          rcases inductionHypothesis earlier with ⟨quotient, equation⟩
          refine ⟨quotient * betaModulusFor coefficient count, ?_⟩
          unfold betaPrefixProduct
          calc
            betaPrefixProduct coefficient count *
                betaModulusFor coefficient count =
              (betaModulusFor coefficient index * quotient) *
                betaModulusFor coefficient count :=
              congrArg (· * betaModulusFor coefficient count) equation
            _ = betaModulusFor coefficient index *
                (quotient * betaModulusFor coefficient count) :=
              natMulAssoc _ _ _
      | inr equal =>
          cases equal
          refine ⟨betaPrefixProduct coefficient index, ?_⟩
          change
            betaPrefixProduct coefficient index *
                betaModulusFor coefficient index =
              betaModulusFor coefficient index *
                betaPrefixProduct coefficient index
          exact Nat.mul_comm _ _

/-- Canonical constructive CRT extension by the residue at `count`. -/
def NatVector.betaEncodePrefix
    {length : Nat}
    (values : NatVector length) : Nat -> Nat
  | 0 => 0
  | Nat.succ count =>
      let previous := values.betaEncodePrefix count
      let modulus := values.betaModulus count
      let remainder := constructiveRemainder previous modulus
      let delta := constructiveDifference
        (values.getD count + modulus) remainder
      previous +
        (betaPrefixProduct values.betaCoefficient count *
          betaPrefixInverse values.betaCoefficient count count) * delta

/-- Constructive beta dividend for the whole finite vector. -/
def NatVector.betaDividend
    {length : Nat}
    (values : NatVector length) : Nat :=
  values.betaEncodePrefix length

/-- One CRT extension preserves every residue in the earlier prefix. -/
theorem NatVector.betaEncodePrefix_preserves
    {length count index : Nat}
    (values : NatVector length)
    (bounded : index < count) :
    NatCongruent
      (values.betaEncodePrefix (Nat.succ count))
      (values.betaEncodePrefix count)
      (values.betaModulus index) := by
  rcases betaModulusFor_dvd_prefixProduct
      (coefficient := values.betaCoefficient) bounded with
    ⟨quotient, productEquation⟩
  let delta := constructiveDifference
    (values.getD count + values.betaModulus count)
    (constructiveRemainder
      (values.betaEncodePrefix count) (values.betaModulus count))
  have multipleEquation :
      (betaPrefixProduct values.betaCoefficient count *
          betaPrefixInverse values.betaCoefficient count count) * delta =
        (quotient *
          betaPrefixInverse values.betaCoefficient count count * delta) *
            values.betaModulus index := by
    change
      (betaPrefixProduct values.betaCoefficient count *
          betaPrefixInverse values.betaCoefficient count count) * delta =
        (quotient *
          betaPrefixInverse values.betaCoefficient count count * delta) *
            betaModulusFor values.betaCoefficient index
    rw [productEquation]
    calc
      ((betaModulusFor values.betaCoefficient index * quotient) *
          betaPrefixInverse values.betaCoefficient count count) * delta =
        (betaModulusFor values.betaCoefficient index * quotient) *
          (betaPrefixInverse values.betaCoefficient count count * delta) :=
        natMulAssoc
          (betaModulusFor values.betaCoefficient index * quotient)
          (betaPrefixInverse values.betaCoefficient count count)
          delta
      _ = betaModulusFor values.betaCoefficient index *
          (quotient *
            (betaPrefixInverse values.betaCoefficient count count * delta)) :=
        natMulAssoc
          (betaModulusFor values.betaCoefficient index)
          quotient
          (betaPrefixInverse values.betaCoefficient count count * delta)
      _ = betaModulusFor values.betaCoefficient index *
          ((quotient *
            betaPrefixInverse values.betaCoefficient count count) * delta) :=
        congrArg
          (betaModulusFor values.betaCoefficient index * ·)
          (natMulAssoc
            quotient
            (betaPrefixInverse values.betaCoefficient count count)
            delta).symm
      _ = ((quotient *
          betaPrefixInverse values.betaCoefficient count count) * delta) *
            betaModulusFor values.betaCoefficient index :=
        Nat.mul_comm _ _
  change NatCongruent
    (values.betaEncodePrefix count +
      (betaPrefixProduct values.betaCoefficient count *
        betaPrefixInverse values.betaCoefficient count count) * delta)
    (values.betaEncodePrefix count)
    (values.betaModulus index)
  rw [multipleEquation]
  exact NatCongruent.addMultiple _ _ _

/-- One CRT extension realizes its newly requested residue. -/
theorem NatVector.betaEncodePrefix_current
    {length count : Nat}
    (values : NatVector length)
    (bounded : count < length) :
    NatCongruent
      (values.betaEncodePrefix (Nat.succ count))
      (values.get count bounded)
      (values.betaModulus count) := by
  let previous := values.betaEncodePrefix count
  let modulus := values.betaModulus count
  let remainder := constructiveRemainder previous modulus
  let value := values.get count bounded
  let delta := constructiveDifference (value + modulus) remainder
  have modulusPositive : 0 < modulus := by
    unfold modulus NatVector.betaModulus betaModulusFor
    exact Nat.zero_lt_succ _
  have remainderBounded : remainder < modulus :=
    (constructiveDivMod_spec previous modulus modulusPositive).2
  have inverse := values.betaPrefixInverse_congruent
    bounded (Nat.le_refl count)
  have scaledInverse := inverse.mulRight delta
  have previousCongruent :=
    value_congruent_constructiveRemainder previous modulus modulusPositive
  have combined := previousCongruent.add scaledInverse
  have remainderBelowTotal : remainder < value + modulus :=
    Nat.lt_of_lt_of_le remainderBounded (natLeAddLeft modulus value)
  have deltaEquation : remainder + delta = value + modulus := by
    unfold delta
    exact (constructiveDifference_spec_of_lt remainderBelowTotal).2
  have finalCongruence : NatCongruent (remainder + delta) value modulus :=
    (NatCongruent.ofEq deltaEquation).trans
      ((NatCongruent.ofEq
        (congrArg (value + ·) (Nat.one_mul modulus).symm)).trans
        (NatCongruent.addMultiple value 1 modulus))
  change NatCongruent
    (previous +
      (betaPrefixProduct values.betaCoefficient count *
        betaPrefixInverse values.betaCoefficient count count) *
          constructiveDifference (values.getD count + modulus) remainder)
    value modulus
  rw [NatVector.getD_eq_get values bounded]
  have normalizeProduct :
      NatCongruent
        (remainder + 1 * delta)
        (remainder + delta)
        modulus :=
    NatCongruent.ofEq
      (congrArg (remainder + ·) (Nat.one_mul delta))
  exact combined.trans (normalizeProduct.trans finalCongruence)

/-- Every prefix encoder realizes all residues already requested in it. -/
theorem NatVector.betaEncodePrefix_congruent
    {length count index : Nat}
    (values : NatVector length)
    (countBounded : count <= length)
    (indexBounded : index < count) :
    NatCongruent
      (values.betaEncodePrefix count)
      (values.get index (Nat.lt_of_lt_of_le indexBounded countBounded))
      (values.betaModulus index) := by
  induction count with
  | zero => exact (Nat.not_lt_zero index indexBounded).elim
  | succ count inductionHypothesis =>
      cases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ indexBounded) with
      | inl earlier =>
          exact (values.betaEncodePrefix_preserves earlier).trans
            (inductionHypothesis
              (Nat.le_trans (Nat.le_succ count) countBounded)
              earlier)
      | inr equal =>
          cases equal
          exact values.betaEncodePrefix_current
            (Nat.lt_of_succ_le countBounded)

/-- The internal beta witness supplies every entry of a finite vector. -/
theorem constructiveRemainder_betaDividend
    {length index : Nat}
    (values : NatVector length)
    (bounded : index < length) :
    constructiveRemainder
        values.betaDividend
        (values.betaModulus index) =
      values.get index bounded := by
  have modulusPositive : 0 < values.betaModulus index := by
    unfold NatVector.betaModulus betaModulusFor
    exact Nat.zero_lt_succ _
  have congruent := values.betaEncodePrefix_congruent
    (Nat.le_refl length) bounded
  exact (constructiveRemainder_eq_of_congruent
      modulusPositive congruent).trans
    (constructiveRemainder_eq_of_lt
      (values.get_lt_betaModulus bounded))

end HeytingArithmetic
end RelationalPerimeter

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.HeytingArithmetic.betaFactorial
#print axioms RelationalPerimeter.HeytingArithmetic.betaFactorial_positive
#print axioms RelationalPerimeter.HeytingArithmetic.dvd_factorial_constructive
#print axioms RelationalPerimeter.HeytingArithmetic.NatVector.betaPrefixInverse_congruent
#print axioms RelationalPerimeter.HeytingArithmetic.NatVector.betaDividend
#print axioms RelationalPerimeter.HeytingArithmetic.constructiveRemainder_betaDividend
/- AXIOM_AUDIT_END -/
