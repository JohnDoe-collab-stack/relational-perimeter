import RelationalPerimeter.Relativity.Arithmetic.OrderedFractions

/-!
Rational Cauchy representations with explicit moduli and positive agreement
witnesses. Agreement is not equality of encodings. The additive operations
and their agreement laws are closed here. Completeness and
the differential interpretation are separate obligations: this module by
itself is not a completed real analysis or a geometry certificate.
-/
set_option genInjectivity false
namespace RelationalPerimeter.Relativity.Analysis
open Arithmetic

structure Precision where
  numerator : Nat
  denominator : Nat
  numeratorPositive : 0 < numerator
  denominatorPositive : 0 < denominator

namespace Precision

def fraction (e : Precision) : Fraction := ⟨⟨e.numerator, 0⟩, e.denominator, e.denominatorPositive⟩
def value (e : Precision) : Rational := Rational.normalize e.fraction
def half (e : Precision) : Precision :=
  ⟨e.numerator, 2 * e.denominator, e.numeratorPositive,
   Nat.mul_pos (Nat.zero_lt_succ 1) e.denominatorPositive⟩

def unit : Precision := ⟨1, 1, Nat.zero_lt_succ 0, Nat.zero_lt_succ 0⟩

def divideNat (e : Precision) (factor : Nat) (positive : 0 < factor) : Precision :=
  ⟨e.numerator, e.denominator * factor, e.numeratorPositive,
   Nat.mul_pos e.denominatorPositive positive⟩

theorem divide_scale (e : Precision) (factor : Nat) (positive : 0 < factor) :
    Rational.mul (e.divideNat factor positive).value (Rational.ofNat factor) = e.value := by
  apply Rational.normalize_congr
  apply Fraction.trans (Fraction.mul_congr (Rational.normalize_agrees _) (Rational.normalize_agrees _))
  unfold fraction divideNat Fraction.Agree Fraction.mul Fraction.nat Balance.Agree Balance.scale Balance.mul Balance.nat
  exact_natural

theorem zero_le_value (e : Precision) : Rational.Le Rational.zero e.value := by
  apply (Rational.normalize_le_iff _ _).mpr
  unfold Fraction.Le Fraction.zero fraction Balance.Le Balance.scale Balance.zero
  rw [Nat.zero_mul, Nat.mul_one, Nat.add_zero, Nat.zero_add]
  exact Nat.zero_le _

theorem half_add_half (e : Precision) : Rational.add e.half.value e.half.value = e.value := by
  apply Rational.normalize_congr
  apply Fraction.trans (Fraction.add_congr (Rational.normalize_agrees _) (Rational.normalize_agrees _))
  unfold Fraction.Agree Fraction.add fraction half Balance.Agree Balance.scale Balance.add
  exact_natural

end Precision

def Close (a b budget : Rational) : Prop :=
  Rational.Le (Rational.sub a b) budget ∧ Rational.Le (Rational.sub b a) budget

theorem close_refl (a : Rational) (e : Precision) : Close a a e.value := by
  unfold Close
  rw [Rational.sub_self]
  exact ⟨e.zero_le_value, e.zero_le_value⟩

theorem close_symm {a b budget : Rational} (h : Close a b budget) : Close b a budget := ⟨h.2, h.1⟩

theorem close_triangle {a b c left right : Rational} (hab : Close a b left) (hbc : Close b c right) :
    Close a c (Rational.add left right) := by
  have forward := Rational.add_le hab.1 hbc.1
  rw [Rational.sub_compose] at forward
  have backward := Rational.add_le hbc.2 hab.2
  rw [Rational.sub_compose, Rational.add_comm right left] at backward
  exact ⟨forward, backward⟩

theorem difference_of_sums (a b c d : Rational) :
    Rational.sub (Rational.add a b) (Rational.add c d) =
      Rational.add (Rational.sub a c) (Rational.sub b d) := by
  unfold Rational.sub
  rw [Rational.neg_add]
  conv => lhs; simp only [Rational.add_assoc, Rational.add_comm, Rational.add_left_comm]
  conv => rhs; simp only [Rational.add_assoc, Rational.add_comm, Rational.add_left_comm]

theorem close_add {a b c d left right : Rational} (hab : Close a b left) (hcd : Close c d right) :
    Close (Rational.add a c) (Rational.add b d) (Rational.add left right) := by
  constructor
  · rw [difference_of_sums]
    exact Rational.add_le hab.1 hcd.1
  · rw [difference_of_sums]
    exact Rational.add_le hab.2 hcd.2

theorem difference_of_negatives (a b : Rational) :
    Rational.sub (Rational.neg a) (Rational.neg b) = Rational.sub b a := by
  unfold Rational.sub
  rw [Rational.neg_neg, Rational.add_comm]

theorem close_neg {a b budget : Rational} (h : Close a b budget) :
    Close (Rational.neg a) (Rational.neg b) budget := by
  unfold Close
  rw [difference_of_negatives, difference_of_negatives]
  exact ⟨h.2, h.1⟩

def Bound (value limit : Rational) : Prop := Rational.Le value limit ∧ Rational.Le (Rational.neg value) limit

theorem bound_of_close {a b budget limit : Rational} (h : Close a b budget) (hb : Bound b limit) :
    Bound a (Rational.add budget limit) := by
  have first := Rational.add_le h.1 hb.1
  have second := Rational.add_le (close_neg h).1 hb.2
  unfold Rational.sub at first second
  rw [Rational.add_assoc, Rational.neg_add_cancel, Rational.add_zero] at first second
  exact ⟨first, second⟩

private theorem product_upper {a b limit cap : Rational} (ha : Rational.Le a limit)
    (hb : Rational.Le Rational.zero b) (hcap : Rational.Le b cap)
    (hlimit : Rational.Le Rational.zero limit) : Rational.Le (Rational.mul a b) (Rational.mul limit cap) :=
  Rational.le_trans (Rational.mul_le_right ha hb) (Rational.mul_le_left hcap hlimit)

theorem bound_mul {a b left right : Rational} (ha : Bound a left) (hb : Bound b right)
    (hl : Rational.Le Rational.zero left) : Bound (Rational.mul a b) (Rational.mul left right) := by
  if sign : Rational.Le Rational.zero b then
    constructor
    · exact product_upper ha.1 sign hb.1 hl
    · rw [← Rational.neg_mul]
      exact product_upper ha.2 sign hb.1 hl
  else
    have negative : Rational.Le b Rational.zero :=
      match Rational.le_total Rational.zero b with
      | .inl h => False.elim (sign h)
      | .inr h => h
    have nonnegative := Rational.neg_le_neg negative
    rw [Rational.neg_zero] at nonnegative
    constructor
    · have h := product_upper ha.2 nonnegative hb.2 hl
      rw [Rational.neg_mul, Rational.mul_neg, Rational.neg_neg] at h
      exact h
    · have h := product_upper ha.1 nonnegative hb.2 hl
      rw [Rational.mul_neg] at h
      exact h

theorem close_mul_right {a b c budget cap : Rational} (h : Close a b budget)
    (hc : Bound c cap) (positive : Rational.Le Rational.zero budget) :
    Close (Rational.mul a c) (Rational.mul b c) (Rational.mul budget cap) := by
  have difference : Bound (Rational.sub a b) budget := by
    refine ⟨h.1, ?_⟩
    rw [Rational.neg_sub]
    exact h.2
  have product := bound_mul difference hc positive
  unfold Bound at product
  rw [Rational.sub_mul] at product
  rw [Rational.neg_sub] at product
  exact product

theorem close_mul_left {a b c budget cap : Rational} (h : Close a b budget)
    (hc : Bound c cap) (positive : Rational.Le Rational.zero budget) :
    Close (Rational.mul c a) (Rational.mul c b) (Rational.mul budget cap) := by
  have product := close_mul_right h hc positive
  rw [Rational.mul_comm a c, Rational.mul_comm b c] at product
  exact product

structure CauchyRepresentation where
  approximate : Nat → Rational
  modulus : Precision → Nat
  cauchy : ∀ e n m, modulus e ≤ n → modulus e ≤ m →
    Close (approximate n) (approximate m) e.value

/-- Positive evidence of analytic agreement, including a usable modulus.
No operation extracts such a witness from an erased existence statement. -/
structure Agreement (a b : CauchyRepresentation) where
  modulus : Precision → Nat
  close : ∀ e n m, modulus e ≤ n → modulus e ≤ m →
    Close (a.approximate n) (b.approximate m) e.value

namespace Agreement

def reflexive (a : CauchyRepresentation) : Agreement a a := ⟨a.modulus, a.cauchy⟩
def reverse {a b : CauchyRepresentation} (h : Agreement a b) : Agreement b a :=
  ⟨h.modulus, fun e n m hn hm => close_symm (h.close e m n hm hn)⟩

def compose {a b c : CauchyRepresentation} (ab : Agreement a b) (bc : Agreement b c) : Agreement a c where
  modulus e := Natural.join (ab.modulus e.half) (bc.modulus e.half)
  close e n m hn hm := by
    let middle := Natural.join (ab.modulus e.half) (bc.modulus e.half)
    have left := ab.close e.half n middle
      (Nat.le_trans (Natural.le_join_left _ _) hn) (Natural.le_join_left _ _)
    have right := bc.close e.half middle m
      (Natural.le_join_right _ _) (Nat.le_trans (Natural.le_join_right _ _) hm)
    have composed := close_triangle left right
    rw [e.half_add_half] at composed
    exact composed

end Agreement

namespace CauchyRepresentation

def constant (q : Rational) : CauchyRepresentation :=
  ⟨fun _ => q, fun _ => 0, fun e _ _ _ _ => close_refl q e⟩

def add (a b : CauchyRepresentation) : CauchyRepresentation where
  approximate n := Rational.add (a.approximate n) (b.approximate n)
  modulus e := Natural.join (a.modulus e.half) (b.modulus e.half)
  cauchy e n m hn hm := by
    have left := a.cauchy e.half n m
      (Nat.le_trans (Natural.le_join_left _ _) hn) (Nat.le_trans (Natural.le_join_left _ _) hm)
    have right := b.cauchy e.half n m
      (Nat.le_trans (Natural.le_join_right _ _) hn) (Nat.le_trans (Natural.le_join_right _ _) hm)
    have combined := close_add left right
    rw [e.half_add_half] at combined
    exact combined

def neg (a : CauchyRepresentation) : CauchyRepresentation :=
  ⟨fun n => Rational.neg (a.approximate n), a.modulus,
   fun e n m hn hm => close_neg (a.cauchy e n m hn hm)⟩

structure TailBound (a : CauchyRepresentation) where
  start : Nat
  size : Nat
  positive : 0 < size
  bounded : ∀ n, start ≤ n → Bound (a.approximate n) (Rational.ofNat size)

def tailBound (a : CauchyRepresentation) : TailBound a where
  start := a.modulus Precision.unit
  size := 1 + Rational.magnitudeBound (a.approximate (a.modulus Precision.unit))
  positive := by rw [Nat.add_comm 1]; exact Nat.zero_lt_succ _
  bounded n hn := by
    have near := a.cauchy Precision.unit n (a.modulus Precision.unit) hn (Nat.le_refl _)
    have bounded := bound_of_close near (Rational.magnitude_bounds _)
    change Bound (a.approximate n) (Rational.add (Rational.ofNat 1) (Rational.ofNat _)) at bounded
    rw [Rational.nat_add] at bounded
    exact bounded

def productPrecision (a b : CauchyRepresentation) (e : Precision) : Precision :=
  e.divideNat (a.tailBound.size + b.tailBound.size)
    (Nat.lt_of_lt_of_le a.tailBound.positive (Nat.le_add_right ..))

theorem product_budget (a b : CauchyRepresentation) (e : Precision) :
    Rational.add (Rational.mul (productPrecision a b e).value (Rational.ofNat b.tailBound.size))
      (Rational.mul (productPrecision a b e).value (Rational.ofNat a.tailBound.size)) = e.value := by
  rw [← Rational.mul_add, Rational.nat_add, Nat.add_comm b.tailBound.size a.tailBound.size]
  exact e.divide_scale _ _

def mul (a b : CauchyRepresentation) : CauchyRepresentation where
  approximate n := Rational.mul (a.approximate n) (b.approximate n)
  modulus e := Natural.join
    (Natural.join (a.modulus (productPrecision a b e)) (b.modulus (productPrecision a b e)))
    (Natural.join a.tailBound.start b.tailBound.start)
  cauchy e n m hn hm := by
    let precision := productPrecision a b e
    have searchN := Nat.le_trans (Natural.le_join_left _ _) hn
    have searchM := Nat.le_trans (Natural.le_join_left _ _) hm
    have boundsN := Nat.le_trans (Natural.le_join_right _ _) hn
    have boundsM := Nat.le_trans (Natural.le_join_right _ _) hm
    have first := close_mul_right
      (a.cauchy precision n m (Nat.le_trans (Natural.le_join_left _ _) searchN)
        (Nat.le_trans (Natural.le_join_left _ _) searchM))
      (b.tailBound.bounded n (Nat.le_trans (Natural.le_join_right _ _) boundsN)) precision.zero_le_value
    have second := close_mul_left
      (b.cauchy precision n m (Nat.le_trans (Natural.le_join_right _ _) searchN)
        (Nat.le_trans (Natural.le_join_right _ _) searchM))
      (a.tailBound.bounded m (Nat.le_trans (Natural.le_join_left _ _) boundsM)) precision.zero_le_value
    have combined := close_triangle first second
    rw [product_budget] at combined
    exact combined

def pointwiseAgreement (a b : CauchyRepresentation)
    (same : ∀ n, a.approximate n = b.approximate n) : Agreement a b where
  modulus := a.modulus
  close e n m hn hm := by
    rw [← same m]
    exact a.cauchy e n m hn hm

def addAgreement {a b c d : CauchyRepresentation} (ab : Agreement a b) (cd : Agreement c d) :
    Agreement (add a c) (add b d) where
  modulus e := Natural.join (ab.modulus e.half) (cd.modulus e.half)
  close e n m hn hm := by
    have first := ab.close e.half n m
      (Nat.le_trans (Natural.le_join_left _ _) hn) (Nat.le_trans (Natural.le_join_left _ _) hm)
    have second := cd.close e.half n m
      (Nat.le_trans (Natural.le_join_right _ _) hn) (Nat.le_trans (Natural.le_join_right _ _) hm)
    have combined := close_add first second
    rw [e.half_add_half] at combined
    exact combined

def negAgreement {a b : CauchyRepresentation} (h : Agreement a b) : Agreement (neg a) (neg b) :=
  ⟨h.modulus, fun e n m hn hm => close_neg (h.close e n m hn hm)⟩

def mulAgreement {a b c d : CauchyRepresentation} (ab : Agreement a b) (cd : Agreement c d) :
    Agreement (mul a c) (mul b d) where
  modulus e := Natural.join
    (Natural.join (ab.modulus (productPrecision b c e)) (cd.modulus (productPrecision b c e)))
    (Natural.join b.tailBound.start c.tailBound.start)
  close e n m hn hm := by
    let precision := productPrecision b c e
    have searchN := Nat.le_trans (Natural.le_join_left _ _) hn
    have searchM := Nat.le_trans (Natural.le_join_left _ _) hm
    have boundsN := Nat.le_trans (Natural.le_join_right _ _) hn
    have boundsM := Nat.le_trans (Natural.le_join_right _ _) hm
    have first := close_mul_right
      (ab.close precision n m (Nat.le_trans (Natural.le_join_left _ _) searchN)
        (Nat.le_trans (Natural.le_join_left _ _) searchM))
      (c.tailBound.bounded n (Nat.le_trans (Natural.le_join_right _ _) boundsN)) precision.zero_le_value
    have second := close_mul_left
      (cd.close precision n m (Nat.le_trans (Natural.le_join_right _ _) searchN)
        (Nat.le_trans (Natural.le_join_right _ _) searchM))
      (b.tailBound.bounded m (Nat.le_trans (Natural.le_join_left _ _) boundsM)) precision.zero_le_value
    have combined := close_triangle first second
    rw [product_budget] at combined
    exact combined

def additiveCommutativity (a b : CauchyRepresentation) : Agreement (add a b) (add b a) :=
  pointwiseAgreement _ _ (fun n => Rational.add_comm (a.approximate n) (b.approximate n))

def additiveAssociativity (a b c : CauchyRepresentation) : Agreement (add (add a b) c) (add a (add b c)) :=
  pointwiseAgreement _ _ (fun n => Rational.add_assoc (a.approximate n) (b.approximate n) (c.approximate n))

def additiveIdentity (a : CauchyRepresentation) : Agreement (add a (constant Rational.zero)) a :=
  pointwiseAgreement _ _ (fun n => Rational.add_zero (a.approximate n))

def additiveInverse (a : CauchyRepresentation) : Agreement (add a (neg a)) (constant Rational.zero) :=
  pointwiseAgreement _ _ (fun n => Rational.add_neg (a.approximate n))

def constantAddition (a b : Rational) :
    Agreement (add (constant a) (constant b)) (constant (Rational.add a b)) :=
  pointwiseAgreement _ _ (fun _ => rfl)

def multiplicativeCommutativity (a b : CauchyRepresentation) : Agreement (mul a b) (mul b a) :=
  pointwiseAgreement _ _ (fun n => Rational.mul_comm (a.approximate n) (b.approximate n))

def multiplicativeAssociativity (a b c : CauchyRepresentation) : Agreement (mul (mul a b) c) (mul a (mul b c)) :=
  pointwiseAgreement _ _ (fun n => Rational.mul_assoc (a.approximate n) (b.approximate n) (c.approximate n))

def multiplicativeIdentity (a : CauchyRepresentation) : Agreement (mul a (constant Rational.one)) a :=
  pointwiseAgreement _ _ (fun n => Rational.mul_one (a.approximate n))

def distributivity (a b c : CauchyRepresentation) : Agreement (mul a (add b c)) (add (mul a b) (mul a c)) :=
  pointwiseAgreement _ _ (fun n => Rational.mul_add (a.approximate n) (b.approximate n) (c.approximate n))

def constantProduct (a b : Rational) :
    Agreement (mul (constant a) (constant b)) (constant (Rational.mul a b)) :=
  pointwiseAgreement _ _ (fun _ => rfl)

end CauchyRepresentation
end RelationalPerimeter.Relativity.Analysis

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Relativity.Analysis.Precision
#print axioms RelationalPerimeter.Relativity.Analysis.Precision.value
#print axioms RelationalPerimeter.Relativity.Analysis.Precision.half
#print axioms RelationalPerimeter.Relativity.Analysis.Precision.unit
#print axioms RelationalPerimeter.Relativity.Analysis.Precision.divideNat
#print axioms RelationalPerimeter.Relativity.Analysis.Precision.divide_scale
#print axioms RelationalPerimeter.Relativity.Analysis.Precision.zero_le_value
#print axioms RelationalPerimeter.Relativity.Analysis.Precision.half_add_half
#print axioms RelationalPerimeter.Relativity.Analysis.Close
#print axioms RelationalPerimeter.Relativity.Analysis.close_triangle
#print axioms RelationalPerimeter.Relativity.Analysis.close_add
#print axioms RelationalPerimeter.Relativity.Analysis.close_neg
#print axioms RelationalPerimeter.Relativity.Analysis.Bound
#print axioms RelationalPerimeter.Relativity.Analysis.bound_of_close
#print axioms RelationalPerimeter.Relativity.Analysis.bound_mul
#print axioms RelationalPerimeter.Relativity.Analysis.close_mul_right
#print axioms RelationalPerimeter.Relativity.Analysis.close_mul_left
#print axioms RelationalPerimeter.Relativity.Analysis.CauchyRepresentation
#print axioms RelationalPerimeter.Relativity.Analysis.Agreement
#print axioms RelationalPerimeter.Relativity.Analysis.Agreement.reflexive
#print axioms RelationalPerimeter.Relativity.Analysis.Agreement.reverse
#print axioms RelationalPerimeter.Relativity.Analysis.Agreement.compose
#print axioms RelationalPerimeter.Relativity.Analysis.CauchyRepresentation.constant
#print axioms RelationalPerimeter.Relativity.Analysis.CauchyRepresentation.add
#print axioms RelationalPerimeter.Relativity.Analysis.CauchyRepresentation.neg
#print axioms RelationalPerimeter.Relativity.Analysis.CauchyRepresentation.TailBound
#print axioms RelationalPerimeter.Relativity.Analysis.CauchyRepresentation.tailBound
#print axioms RelationalPerimeter.Relativity.Analysis.CauchyRepresentation.productPrecision
#print axioms RelationalPerimeter.Relativity.Analysis.CauchyRepresentation.product_budget
#print axioms RelationalPerimeter.Relativity.Analysis.CauchyRepresentation.mul
#print axioms RelationalPerimeter.Relativity.Analysis.CauchyRepresentation.pointwiseAgreement
#print axioms RelationalPerimeter.Relativity.Analysis.CauchyRepresentation.addAgreement
#print axioms RelationalPerimeter.Relativity.Analysis.CauchyRepresentation.negAgreement
#print axioms RelationalPerimeter.Relativity.Analysis.CauchyRepresentation.mulAgreement
#print axioms RelationalPerimeter.Relativity.Analysis.CauchyRepresentation.additiveCommutativity
#print axioms RelationalPerimeter.Relativity.Analysis.CauchyRepresentation.additiveAssociativity
#print axioms RelationalPerimeter.Relativity.Analysis.CauchyRepresentation.additiveIdentity
#print axioms RelationalPerimeter.Relativity.Analysis.CauchyRepresentation.additiveInverse
#print axioms RelationalPerimeter.Relativity.Analysis.CauchyRepresentation.constantAddition
#print axioms RelationalPerimeter.Relativity.Analysis.CauchyRepresentation.multiplicativeCommutativity
#print axioms RelationalPerimeter.Relativity.Analysis.CauchyRepresentation.multiplicativeAssociativity
#print axioms RelationalPerimeter.Relativity.Analysis.CauchyRepresentation.multiplicativeIdentity
#print axioms RelationalPerimeter.Relativity.Analysis.CauchyRepresentation.distributivity
#print axioms RelationalPerimeter.Relativity.Analysis.CauchyRepresentation.constantProduct
/- AXIOM_AUDIT_END -/
