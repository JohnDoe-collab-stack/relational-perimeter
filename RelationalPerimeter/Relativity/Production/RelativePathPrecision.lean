import RelationalPerimeter.Relativity.Production.RefinedRelativePaths
import RelationalPerimeter.Relativity.Arithmetic.OrderedFractions
import RelationalPerimeter.Relativity.Analysis.ConstructiveContinuum

/-!
# Numerical precision laws of productively refined relative paths

Bounds are eliminated from the actual received paths. Refinement gives
nested closed numerical brackets with halved span. These brackets are
instrumental precision controls, not physical open neighborhoods, and do
not identify sources or erase effects exposed by the existing contract.
-/
set_option genInjectivity false
namespace RelationalPerimeter.Relativity.Production
open Arithmetic

private def countFraction (numerator denominator : Nat) (positive : 0 < denominator) : Fraction :=
  ⟨⟨numerator, 0⟩, denominator, positive⟩

theorem relative_value_count_representation {source : Cursor} (reading : RelativePathReading source) :
    reading.value = Rational.normalize
      (countFraction reading.numerator.relayCount reading.denominator.relayCount reading.positiveScale) := by
  rw [reading.count_ratio_exact, path_count_fraction]
  have count : reading.denominator.relayCount - 1 + 1 = reading.denominator.relayCount :=
    Natural.sub_add_of_le reading.positiveScale
  change Rational.normalize ⟨⟨_, 0⟩, _, _⟩ = Rational.normalize ⟨⟨_, 0⟩, _, _⟩
  apply Rational.normalize_congr
  change reading.numerator.relayCount * reading.denominator.relayCount +
      0 * (reading.denominator.relayCount - 1 + 1) =
    reading.numerator.relayCount * (reading.denominator.relayCount - 1 + 1) +
      0 * reading.denominator.relayCount
  rw [count]

def RelativePathReading.upper {source : Cursor} (reading : RelativePathReading source) : Rational :=
  Rational.normalize (countFraction (reading.numerator.relayCount + 1)
    reading.denominator.relayCount reading.positiveScale)

def RelativePathReading.resolution {source : Cursor} (reading : RelativePathReading source) : Rational :=
  Rational.normalize (countFraction 1 reading.denominator.relayCount reading.positiveScale)

theorem relative_bracket_ordered {source : Cursor} (reading : RelativePathReading source) :
    Rational.Le reading.value reading.upper := by
  rw [relative_value_count_representation]
  apply (Rational.normalize_le_iff _ _).mpr
  change _ * _ + 0 * _ ≤ (_ + 1) * _ + 0 * _
  rw [Nat.zero_mul, Nat.zero_mul, Nat.add_zero, Nat.add_zero]
  exact Nat.mul_le_mul_right _ (Nat.le_add_right ..)

theorem relative_upper_is_reading_plus_resolution {source : Cursor} (reading : RelativePathReading source) :
    Rational.add reading.value reading.resolution = reading.upper := by
  rw [relative_value_count_representation]
  apply Rational.normalize_congr
  apply Fraction.trans (Fraction.add_congr (Rational.normalize_agrees _) (Rational.normalize_agrees _))
  dsimp only [countFraction, RelativePathReading.upper, RelativePathReading.resolution, Fraction.Agree,
    Fraction.add, Balance.Agree, Balance.scale, Balance.add]
  exact_natural

theorem relative_bracket_span {source : Cursor} (reading : RelativePathReading source) :
    Rational.sub reading.upper reading.value = reading.resolution := by
  rw [← relative_upper_is_reading_plus_resolution]
  unfold Rational.sub
  rw [Rational.add_comm reading.value, Rational.add_assoc, Rational.add_neg, Rational.add_zero]

theorem relative_resolution_nonnegative {source : Cursor} (reading : RelativePathReading source) :
    Rational.Le Rational.zero reading.resolution :=
  (Rational.normalize_le_iff _ _).mpr ((Fraction.zero_le_iff _).mpr (Nat.zero_le _))

theorem relative_resolution_nonzero {source : Cursor} (reading : RelativePathReading source) :
    reading.resolution ≠ Rational.zero := by
  intro same
  have agree := Fraction.trans
    (Fraction.symm (Rational.normalize_agrees (countFraction 1 _ reading.positiveScale)))
    (Fraction.trans ((Rational.equal_iff_agree _ _).mp same) (Rational.normalize_agrees Fraction.zero))
  change 1 * 1 + 0 * _ = 0 * _ + 0 * 1 at agree
  rw [Nat.zero_mul, Nat.zero_mul, Nat.add_zero, Nat.zero_add] at agree
  exact Nat.noConfusion agree

theorem relative_refinement_lower_monotone {source choice}
    (result : RelativePathRefinement source choice) :
    Rational.Le source.reading.value result.state.reading.value := by
  rw [relative_value_count_representation, relative_value_count_representation]
  apply (Rational.normalize_le_iff _ _).mpr
  change source.reading.numerator.relayCount * result.state.reading.denominator.relayCount +
      0 * source.reading.denominator.relayCount ≤
    result.state.reading.numerator.relayCount * source.reading.denominator.relayCount +
      0 * result.state.reading.denominator.relayCount
  rw [result.numeratorExact, result.denominatorExact]
  rw [Nat.zero_mul, Nat.zero_mul, Nat.add_zero, Nat.add_zero]
  have expanded : (source.reading.numerator.relayCount +
      (source.reading.numerator.relayCount + choice.extra)) * source.reading.denominator.relayCount =
      source.reading.numerator.relayCount *
        (source.reading.denominator.relayCount + source.reading.denominator.relayCount) +
        choice.extra * source.reading.denominator.relayCount := by exact_natural
  rw [expanded]
  exact Nat.le_add_right ..

theorem relative_refinement_upper_monotone {source choice}
    (result : RelativePathRefinement source choice) :
    Rational.Le result.state.reading.upper source.reading.upper := by
  apply (Rational.normalize_le_iff _ _).mpr
  change (result.state.reading.numerator.relayCount + 1) * source.reading.denominator.relayCount +
      0 * result.state.reading.denominator.relayCount ≤
    (source.reading.numerator.relayCount + 1) * result.state.reading.denominator.relayCount +
      0 * source.reading.denominator.relayCount
  rw [result.numeratorExact, result.denominatorExact]
  rw [Nat.zero_mul, Nat.zero_mul, Nat.add_zero, Nat.add_zero]
  have extra := Nat.mul_le_mul_right source.reading.denominator.relayCount
    (Nat.add_le_add_right choice.extra_le_one 1)
  have left : (source.reading.numerator.relayCount +
      (source.reading.numerator.relayCount + choice.extra) + 1) * source.reading.denominator.relayCount =
      (source.reading.numerator.relayCount + source.reading.numerator.relayCount) *
        source.reading.denominator.relayCount + (choice.extra + 1) * source.reading.denominator.relayCount := by
    exact_natural
  have right : (source.reading.numerator.relayCount + 1) *
      (source.reading.denominator.relayCount + source.reading.denominator.relayCount) =
      (source.reading.numerator.relayCount + source.reading.numerator.relayCount) *
        source.reading.denominator.relayCount + (1 + 1) * source.reading.denominator.relayCount := by
    exact_natural
  rw [left, right]
  exact Nat.add_le_add_left extra _

theorem relative_refinement_halves_span {source choice}
    (result : RelativePathRefinement source choice) :
    Rational.add result.state.reading.resolution result.state.reading.resolution = source.reading.resolution := by
  apply Rational.normalize_congr
  apply Fraction.trans (Fraction.add_congr (Rational.normalize_agrees _) (Rational.normalize_agrees _))
  change ((1 * result.state.reading.denominator.relayCount +
    1 * result.state.reading.denominator.relayCount) * source.reading.denominator.relayCount +
      0 * (result.state.reading.denominator.relayCount * result.state.reading.denominator.relayCount)) =
    1 * (result.state.reading.denominator.relayCount * result.state.reading.denominator.relayCount) +
      (0 * result.state.reading.denominator.relayCount +
        0 * result.state.reading.denominator.relayCount) * source.reading.denominator.relayCount
  rw [Nat.zero_mul, Nat.zero_mul, Nat.zero_add, Nat.zero_mul]
  rw [result.denominatorExact]
  exact_natural

theorem relative_refinement_stays_in_previous_bracket {source choice}
    (result : RelativePathRefinement source choice) :
    Rational.Le source.reading.value result.state.reading.value ∧
      Rational.Le result.state.reading.value source.reading.upper :=
  ⟨relative_refinement_lower_monotone result,
    Rational.le_trans (relative_bracket_ordered _) (relative_refinement_upper_monotone result)⟩

theorem relative_refinement_lower_choice_exact (source : RelativePathState) :
    (refineRelativePaths source .lower).state.reading.value = source.reading.value := by
  rw [relative_value_count_representation, relative_value_count_representation]
  apply Rational.normalize_congr
  change (refineRelativePaths source .lower).state.reading.numerator.relayCount *
      source.reading.denominator.relayCount +
      0 * (refineRelativePaths source .lower).state.reading.denominator.relayCount =
    source.reading.numerator.relayCount *
      (refineRelativePaths source .lower).state.reading.denominator.relayCount +
      0 * source.reading.denominator.relayCount
  rw [(refineRelativePaths source .lower).numeratorExact,
    (refineRelativePaths source .lower).denominatorExact]
  dsimp only [RelativeSubdivision.extra]
  exact_natural

theorem relative_refinement_upper_choice_exact (source : RelativePathState) :
    (refineRelativePaths source .upper).state.reading.upper = source.reading.upper := by
  apply Rational.normalize_congr
  change ((refineRelativePaths source .upper).state.reading.numerator.relayCount + 1) *
      source.reading.denominator.relayCount +
      0 * (refineRelativePaths source .upper).state.reading.denominator.relayCount =
    (source.reading.numerator.relayCount + 1) *
      (refineRelativePaths source .upper).state.reading.denominator.relayCount +
      0 * source.reading.denominator.relayCount
  rw [(refineRelativePaths source .upper).numeratorExact,
    (refineRelativePaths source .upper).denominatorExact]
  dsimp only [RelativeSubdivision.extra]
  exact_natural

theorem relative_refinement_children_meet (source : RelativePathState) :
    (refineRelativePaths source .lower).state.reading.upper =
      (refineRelativePaths source .upper).state.reading.value := by
  rw [relative_value_count_representation]
  apply Rational.normalize_congr
  change ((refineRelativePaths source .lower).state.reading.numerator.relayCount + 1) *
      (refineRelativePaths source .upper).state.reading.denominator.relayCount +
      0 * (refineRelativePaths source .lower).state.reading.denominator.relayCount =
    (refineRelativePaths source .upper).state.reading.numerator.relayCount *
      (refineRelativePaths source .lower).state.reading.denominator.relayCount +
      0 * (refineRelativePaths source .upper).state.reading.denominator.relayCount
  rw [(refineRelativePaths source .lower).numeratorExact,
    (refineRelativePaths source .upper).numeratorExact,
    (refineRelativePaths source .lower).denominatorExact,
    (refineRelativePaths source .upper).denominatorExact]
  dsimp only [RelativeSubdivision.extra]
  exact_natural

/-- Coverage is a downstream rational bracket law. The queried rational is
not an input to either producer and supplies no physical localization. -/
theorem relative_refinement_children_cover (source : RelativePathState) (query : Rational)
    (lower : Rational.Le source.reading.value query) (upper : Rational.Le query source.reading.upper) :
    (Rational.Le (refineRelativePaths source .lower).state.reading.value query ∧
      Rational.Le query (refineRelativePaths source .lower).state.reading.upper) ∨
    (Rational.Le (refineRelativePaths source .upper).state.reading.value query ∧
      Rational.Le query (refineRelativePaths source .upper).state.reading.upper) := by
  if first : Rational.Le query (refineRelativePaths source .lower).state.reading.upper then
    exact .inl ⟨(relative_refinement_lower_choice_exact source).symm ▸ lower, first⟩
  else
    have second := (Rational.le_total query (refineRelativePaths source .lower).state.reading.upper).resolve_left first
    exact .inr ⟨(relative_refinement_children_meet source) ▸ second,
      (relative_refinement_upper_choice_exact source).symm ▸ upper⟩

theorem relative_refinement_chain_brackets {source target}
    (chain : RelativeRefinementChain source target) :
    Rational.Le source.reading.value target.reading.value ∧
      Rational.Le target.reading.upper source.reading.upper := by
  induction chain with
  | root => exact ⟨Rational.le_refl _, Rational.le_refl _⟩
  | step past choice head exactHead ih =>
    exact ⟨Rational.le_trans ih.1 (relative_refinement_lower_monotone head),
      Rational.le_trans (relative_refinement_upper_monotone head) ih.2⟩

theorem relative_refinement_chain_scale {source target}
    (chain : RelativeRefinementChain source target) :
    target.reading.denominator.relayCount =
      source.reading.denominator.relayCount * 2 ^ chain.requests.length := by
  induction chain with
  | root => exact (Nat.mul_one _).symm
  | step past choice head exactHead ih =>
    rw [head.denominatorExact]
    change _ + _ = _ * 2 ^ (past.requests ++ [choice]).length
    have length : (past.requests ++ [choice]).length = past.requests.length + 1 := by
      induction past.requests with
      | nil => rfl
      | cons request tail ih => exact congrArg Nat.succ ih
    rw [length]
    change _ + _ = _ * 2 ^ (_ + 1)
    rw [ih, Nat.pow_succ]
    change _ + _ = _ * (_ * (1 + 1))
    exact_natural

private theorem subdivision_power_bound (n : Nat) : n + 1 ≤ 2 ^ n := by
  induction n with
  | zero => exact Nat.le_refl _
  | succ n ih =>
    have positive : 1 ≤ 2 ^ n := Nat.le_trans (Nat.le_add_left 1 n) ih
    have next := Nat.le_trans (Nat.add_le_add_right ih 1) (Nat.add_le_add_left positive (2 ^ n))
    have expression : 2 ^ n + 2 ^ n = 2 ^ (n + 1) := by
      rw [Nat.pow_succ]
      change _ + _ = _ * (1 + 1)
      exact_natural
    exact Nat.le_trans next (Nat.le_of_eq expression)

theorem relative_resolution_bounded_by_precision {source : Cursor}
    (reading : RelativePathReading source) (precision : Analysis.Precision)
    (enough : precision.denominator ≤ reading.denominator.relayCount) :
    Rational.Le reading.resolution precision.value := by
  apply (Rational.normalize_le_iff _ _).mpr
  change 1 * precision.denominator + 0 * reading.denominator.relayCount ≤
    precision.numerator * reading.denominator.relayCount + 0 * precision.denominator
  rw [Nat.one_mul, Nat.zero_mul, Nat.zero_mul, Nat.add_zero, Nat.add_zero]
  have size := Nat.mul_le_mul_right reading.denominator.relayCount precision.numeratorPositive
  rw [Nat.one_mul] at size
  exact Nat.le_trans enough size

/-- A finite, constructive bound on requests sufficient for any received
positive rational precision. This counts refinement requests, not relays,
runtime work or a physical measurement budget. -/
theorem relative_refinement_reaches_requested_precision {source target}
    (chain : RelativeRefinementChain source target) (precision : Analysis.Precision)
    (enough : precision.denominator ≤ chain.requests.length) :
    Rational.Le target.reading.resolution precision.value := by
  apply relative_resolution_bounded_by_precision
  rw [relative_refinement_chain_scale chain]
  have power : chain.requests.length ≤ 2 ^ chain.requests.length :=
    Nat.le_trans (Nat.le_add_right ..) (subdivision_power_bound _)
  have scale := Nat.mul_le_mul_right (2 ^ chain.requests.length) source.reading.positiveScale
  rw [Nat.one_mul] at scale
  exact Nat.le_trans enough (Nat.le_trans power scale)

theorem relative_refinement_all_requests_precision {source} (prior : RelativeRefinementRun source)
    (requests : List RelativeSubdivision) (precision : Analysis.Precision)
    (enough : precision.denominator ≤ requests.length) :
    Rational.Le (prior.runMore requests).state.reading.resolution precision.value := by
  apply relative_refinement_reaches_requested_precision
  rw [relative_refinement_requested_order]
  have size : (prior.chain.requests ++ requests).length = prior.chain.requests.length + requests.length := by
    induction prior.chain.requests with
    | nil => exact (Nat.zero_add _).symm
    | cons choice tail ih => exact (congrArg Nat.succ ih).trans (Nat.succ_add ..).symm
  rw [size]
  exact Nat.le_trans enough (Nat.le_add_left ..)

/-- A declared finite instrumental schedule sufficient for the requested
precision. It is not a physical localization or an arbitrary numerical
sequence supplied in place of a realization. -/
def relativePrecisionRequests (precision : Analysis.Precision) : List RelativeSubdivision :=
  List.replicate precision.denominator .lower

theorem relative_precision_request_count (precision : Analysis.Precision) :
    (relativePrecisionRequests precision).length = precision.denominator := by
  change (List.replicate precision.denominator RelativeSubdivision.lower).length = _
  induction precision.denominator with
  | zero => rfl
  | succ n ih => exact congrArg Nat.succ ih

structure RelativePrecisionRun (source : RelativePathState) (precision : Analysis.Precision) where
  realization : RelativeRefinementRun source
  bound : Rational.Le realization.state.reading.resolution precision.value

/-- Resume the already returned prefix once through a constructed schedule.
The result contains the actual positive production chain, not just a proof
that some sufficiently long chain would have the required precision. -/
def RelativeRefinementRun.refineToPrecision {source} (prior : RelativeRefinementRun source)
    (precision : Analysis.Precision) : RelativePrecisionRun source precision :=
  let requests := relativePrecisionRequests precision
  let produced := prior.runMore requests
  ⟨produced, relative_refinement_all_requests_precision prior requests precision
    (Nat.le_of_eq (relative_precision_request_count precision).symm)⟩

theorem relative_precision_realization_is_resumption {source} (prior : RelativeRefinementRun source)
    (precision : Analysis.Precision) :
    (prior.refineToPrecision precision).realization = prior.runMore (relativePrecisionRequests precision) := rfl

theorem relative_subdivision_choices_have_different_readings (source : RelativePathState) :
    (refineRelativePaths source .lower).state.reading.value ≠
      (refineRelativePaths source .upper).state.reading.value := by
  intro same
  have equality := ((relative_value_count_representation
    (refineRelativePaths source .lower).state.reading).symm.trans same).trans
      (relative_value_count_representation (refineRelativePaths source .upper).state.reading)
  have agree := Fraction.trans (Fraction.symm (Rational.normalize_agrees _))
    (Fraction.trans ((Rational.equal_iff_agree _ _).mp equality) (Rational.normalize_agrees _))
  change (refineRelativePaths source .lower).state.reading.numerator.relayCount *
      (refineRelativePaths source .upper).state.reading.denominator.relayCount +
      0 * (refineRelativePaths source .lower).state.reading.denominator.relayCount =
    (refineRelativePaths source .upper).state.reading.numerator.relayCount *
      (refineRelativePaths source .lower).state.reading.denominator.relayCount +
      0 * (refineRelativePaths source .upper).state.reading.denominator.relayCount at agree
  rw [(refineRelativePaths source .lower).numeratorExact,
    (refineRelativePaths source .upper).numeratorExact,
    (refineRelativePaths source .lower).denominatorExact,
    (refineRelativePaths source .upper).denominatorExact] at agree
  dsimp only [RelativeSubdivision.extra] at agree
  conv at agree => lhs; simp only [Nat.zero_mul, Nat.add_zero]
  conv at agree => rhs; simp only [Nat.zero_mul, Nat.add_zero, ← Nat.add_assoc]
  have positive : 0 < source.reading.denominator.relayCount + source.reading.denominator.relayCount :=
    Nat.lt_of_lt_of_le source.reading.positiveScale (Nat.le_add_right ..)
  have impossible := Natural.mul_cancel_right positive agree
  exact (Nat.ne_of_lt (Nat.lt_succ_self _)) impossible

end RelationalPerimeter.Relativity.Production
/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Relativity.Production.relative_value_count_representation
#print axioms RelationalPerimeter.Relativity.Production.RelativePathReading.upper
#print axioms RelationalPerimeter.Relativity.Production.RelativePathReading.resolution
#print axioms RelationalPerimeter.Relativity.Production.relative_bracket_ordered
#print axioms RelationalPerimeter.Relativity.Production.relative_upper_is_reading_plus_resolution
#print axioms RelationalPerimeter.Relativity.Production.relative_bracket_span
#print axioms RelationalPerimeter.Relativity.Production.relative_resolution_nonnegative
#print axioms RelationalPerimeter.Relativity.Production.relative_resolution_nonzero
#print axioms RelationalPerimeter.Relativity.Production.relative_refinement_lower_monotone
#print axioms RelationalPerimeter.Relativity.Production.relative_refinement_upper_monotone
#print axioms RelationalPerimeter.Relativity.Production.relative_refinement_halves_span
#print axioms RelationalPerimeter.Relativity.Production.relative_refinement_stays_in_previous_bracket
#print axioms RelationalPerimeter.Relativity.Production.relative_refinement_lower_choice_exact
#print axioms RelationalPerimeter.Relativity.Production.relative_refinement_upper_choice_exact
#print axioms RelationalPerimeter.Relativity.Production.relative_refinement_children_meet
#print axioms RelationalPerimeter.Relativity.Production.relative_refinement_children_cover
#print axioms RelationalPerimeter.Relativity.Production.relative_refinement_chain_brackets
#print axioms RelationalPerimeter.Relativity.Production.relative_refinement_chain_scale
#print axioms RelationalPerimeter.Relativity.Production.relative_resolution_bounded_by_precision
#print axioms RelationalPerimeter.Relativity.Production.relative_refinement_reaches_requested_precision
#print axioms RelationalPerimeter.Relativity.Production.relative_refinement_all_requests_precision
#print axioms RelationalPerimeter.Relativity.Production.relativePrecisionRequests
#print axioms RelationalPerimeter.Relativity.Production.relative_precision_request_count
#print axioms RelationalPerimeter.Relativity.Production.RelativePrecisionRun
#print axioms RelationalPerimeter.Relativity.Production.RelativeRefinementRun.refineToPrecision
#print axioms RelationalPerimeter.Relativity.Production.relative_precision_realization_is_resumption
#print axioms RelationalPerimeter.Relativity.Production.relative_subdivision_choices_have_different_readings
/- AXIOM_AUDIT_END -/
