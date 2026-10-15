import RelationalPerimeter.Instances.HeytingArithmetic.PrimitiveRecursiveCodeSubstitution

/-!
# Primitive-recursive Boolean closure
-/

namespace RelationalPerimeter
namespace HeytingArithmetic

private theorem booleanIndexZero_lt_two : 0 < 2 := Nat.zero_lt_succ 1
private theorem booleanIndexOne_lt_two : 1 < 2 :=
  Nat.succ_lt_succ (Nat.zero_lt_succ 0)

def natAndBit (left right : Nat) : Nat :=
  natIfZero left 0 (natPositiveBit right)

def natOrBit (left right : Nat) : Nat :=
  natIfZero left (natPositiveBit right) 1

@[simp] theorem natIfZero_zero (whenZero whenPositive : Nat) :
    natIfZero 0 whenZero whenPositive = whenZero := rfl

@[simp] theorem natIfZero_succ
    (selector whenZero whenPositive : Nat) :
    natIfZero (Nat.succ selector) whenZero whenPositive = whenPositive := rfl

@[simp] theorem natPositiveBit_zero :
    natPositiveBit 0 = 0 := rfl

@[simp] theorem natPositiveBit_succ (value : Nat) :
    natPositiveBit (Nat.succ value) = 1 := rfl

@[simp] theorem natIfZero_zero_one_eq_positiveBit (value : Nat) :
    natIfZero value 0 1 = natPositiveBit value := rfl

theorem natPositiveBit_eq_one_iff (value : Nat) :
    natPositiveBit value = 1 ↔ 0 < value := by
  cases value with
  | zero =>
      constructor <;> intro impossible
      · exact Nat.noConfusion impossible
      · exact (Nat.not_lt_zero 0 impossible).elim
  | succ value =>
      constructor
      · intro _
        exact Nat.zero_lt_succ value
      · intro _
        rfl

theorem natPositiveBit_pos_iff (value : Nat) :
    0 < natPositiveBit value ↔ 0 < value := by
  cases value with
  | zero =>
      change 0 < 0 ↔ 0 < 0
      constructor
      · intro impossible
        exact (Nat.not_lt_zero 0 impossible).elim
      · intro impossible
        exact (Nat.not_lt_zero 0 impossible).elim
  | succ value =>
      change 0 < 1 ↔ 0 < Nat.succ value
      constructor
      · intro _
        exact Nat.zero_lt_succ value
      · intro _
        exact Nat.zero_lt_succ 0

theorem natEqualBit_succ_succ (left right : Nat) :
    natEqualBit (Nat.succ left) (Nat.succ right) =
      natEqualBit left right := by
  unfold natEqualBit
  rw [Nat.succ_sub_succ_eq_sub, Nat.succ_sub_succ_eq_sub]

theorem natEqualBit_succ_zero (left : Nat) :
    natEqualBit (Nat.succ left) 0 = 0 := by
  unfold natEqualBit
  rw [Nat.sub_zero, Nat.zero_sub, Nat.add_zero]
  rfl

theorem natEqualBit_eq_one_iff (left right : Nat) :
    natEqualBit left right = 1 ↔ left = right := by
  induction left generalizing right with
  | zero =>
      cases right with
      | zero =>
          change 1 = 1 ↔ 0 = 0
          exact Iff.intro (fun _ => rfl) (fun _ => rfl)
      | succ right =>
          change 0 = 1 ↔ 0 = Nat.succ right
          constructor
          · intro impossible
            exact Nat.noConfusion impossible
          · intro impossible
            exact Nat.noConfusion impossible
  | succ left inductionHypothesis =>
      cases right with
      | zero =>
          rw [natEqualBit_succ_zero]
          constructor
          · intro impossible
            exact Nat.noConfusion impossible
          · intro impossible
            exact Nat.noConfusion impossible
      | succ right =>
          rw [natEqualBit_succ_succ]
          constructor
          · intro accepted
            exact congrArg Nat.succ ((inductionHypothesis right).mp accepted)
          · intro equality
            exact (inductionHypothesis right).mpr
              (Nat.succ.inj equality)

theorem natEqualBit_pos_iff (left right : Nat) :
    0 < natEqualBit left right ↔ left = right := by
  induction left generalizing right with
  | zero =>
      cases right with
      | zero =>
          change 0 < 1 ↔ 0 = 0
          exact Iff.intro (fun _ => rfl) (fun _ => Nat.zero_lt_succ 0)
      | succ right =>
          change 0 < 0 ↔ 0 = Nat.succ right
          constructor
          · intro impossible
            exact (Nat.not_lt_zero 0 impossible).elim
          · intro impossible
            exact Nat.noConfusion impossible
  | succ left inductionHypothesis =>
      cases right with
      | zero =>
          rw [natEqualBit_succ_zero]
          constructor
          · intro impossible
            exact (Nat.not_lt_zero 0 impossible).elim
          · intro impossible
            exact Nat.noConfusion impossible
      | succ right =>
          rw [natEqualBit_succ_succ]
          constructor
          · intro positive
            exact congrArg Nat.succ ((inductionHypothesis right).mp positive)
          · intro equality
            exact (inductionHypothesis right).mpr (Nat.succ.inj equality)

theorem natAndBit_eq_one_iff (left right : Nat) :
    natAndBit left right = 1 ↔ 0 < left ∧ 0 < right := by
  cases left with
  | zero =>
      change 0 = 1 ↔ 0 < 0 ∧ 0 < right
      constructor
      · intro impossible
        exact Nat.noConfusion impossible
      · intro positive
        exact (Nat.not_lt_zero 0 positive.1).elim
  | succ left =>
      cases right with
      | zero =>
          change 0 = 1 ↔ 0 < Nat.succ left ∧ 0 < 0
          constructor
          · intro impossible
            exact Nat.noConfusion impossible
          · intro positive
            exact (Nat.not_lt_zero 0 positive.2).elim
      | succ right =>
          change 1 = 1 ↔
            0 < Nat.succ left ∧ 0 < Nat.succ right
          constructor
          · intro _
            exact And.intro (Nat.zero_lt_succ left)
              (Nat.zero_lt_succ right)
          · intro _
            rfl

theorem natAndBit_pos_iff (left right : Nat) :
    0 < natAndBit left right ↔ 0 < left ∧ 0 < right := by
  cases left with
  | zero =>
      change 0 < 0 ↔ 0 < 0 ∧ 0 < right
      constructor
      · intro impossible
        exact (Nat.not_lt_zero 0 impossible).elim
      · intro positive
        exact (Nat.not_lt_zero 0 positive.1).elim
  | succ left =>
      cases right with
      | zero =>
          change 0 < 0 ↔ 0 < Nat.succ left ∧ 0 < 0
          constructor
          · intro impossible
            exact (Nat.not_lt_zero 0 impossible).elim
          · intro positive
            exact (Nat.not_lt_zero 0 positive.2).elim
      | succ right =>
          change 0 < 1 ↔
            0 < Nat.succ left ∧ 0 < Nat.succ right
          constructor
          · intro _
            exact And.intro (Nat.zero_lt_succ left)
              (Nat.zero_lt_succ right)
          · intro _
            exact Nat.zero_lt_succ 0

theorem natOrBit_pos_iff (left right : Nat) :
    0 < natOrBit left right ↔ 0 < left ∨ 0 < right := by
  cases left with
  | zero =>
      cases right with
      | zero =>
          change 0 < 0 ↔ 0 < 0 ∨ 0 < 0
          constructor
          · intro impossible
            exact (Nat.not_lt_zero 0 impossible).elim
          · intro either
            cases either with
            | inl impossible => exact (Nat.not_lt_zero 0 impossible).elim
            | inr impossible => exact (Nat.not_lt_zero 0 impossible).elim
      | succ right =>
          change 0 < 1 ↔ 0 < 0 ∨ 0 < Nat.succ right
          constructor
          · intro _
            exact Or.inr (Nat.zero_lt_succ right)
          · intro _
            exact Nat.zero_lt_succ 0
  | succ left =>
      change 0 < 1 ↔ 0 < Nat.succ left ∨ 0 < right
      constructor
      · intro _
        exact Or.inl (Nat.zero_lt_succ left)
      · intro _
        exact Nat.zero_lt_succ 0

def PRFunction.andBit : PRFunction 2 :=
  PRFunction.composition PRFunction.ifZero
    (PRFunctionVector.cons
      (PRFunction.projection 2 0 booleanIndexZero_lt_two)
      (PRFunctionVector.cons (PRFunction.constant 2 0)
        (PRFunctionVector.singleton
          (PRFunction.composition PRFunction.positiveBit
            (PRFunctionVector.singleton
              (PRFunction.projection 2 1 booleanIndexOne_lt_two))))))

def PRFunction.orBit : PRFunction 2 :=
  PRFunction.composition PRFunction.ifZero
    (PRFunctionVector.cons
      (PRFunction.projection 2 0 booleanIndexZero_lt_two)
      (PRFunctionVector.cons
        (PRFunction.composition PRFunction.positiveBit
          (PRFunctionVector.singleton
            (PRFunction.projection 2 1 booleanIndexOne_lt_two)))
        (PRFunctionVector.singleton (PRFunction.constant 2 1))))

def PRFunction.conjoin
    {arity : Nat} (left right : PRFunction arity) : PRFunction arity :=
  PRFunction.composition PRFunction.andBit
    (PRFunctionVector.cons left (PRFunctionVector.singleton right))

@[simp] theorem PRFunction.run_andBit (left right : Nat) :
    PRFunction.andBit.run
        (NatVector.cons left (NatVector.cons right NatVector.nil)) =
      natAndBit left right := by
  unfold PRFunction.andBit natAndBit
  rw [PRFunction.run_composition, PRFunctionVector.run_cons,
    PRFunctionVector.run_cons, PRFunctionVector.run_singleton]
  change PRFunction.ifZero.run _ = _
  rw [PRFunction.run_ifZero]
  change natIfZero left 0
    (PRFunction.positiveBit.run (NatVector.cons right NatVector.nil)) = _
  rw [PRFunction.run_eq_of_evaluates
    (PRFunction.positiveBit_evaluates right)]

@[simp] theorem PRFunction.run_orBit (left right : Nat) :
    PRFunction.orBit.run
        (NatVector.cons left (NatVector.cons right NatVector.nil)) =
      natOrBit left right := by
  unfold PRFunction.orBit natOrBit
  rw [PRFunction.run_composition, PRFunctionVector.run_cons,
    PRFunctionVector.run_cons, PRFunctionVector.run_singleton]
  change PRFunction.ifZero.run _ = _
  rw [PRFunction.run_ifZero]
  change natIfZero left
    (PRFunction.positiveBit.run (NatVector.cons right NatVector.nil)) 1 = _
  rw [PRFunction.run_eq_of_evaluates
    (PRFunction.positiveBit_evaluates right)]

@[simp] theorem PRFunction.run_conjoin
    {arity : Nat}
    (left right : PRFunction arity)
    (inputs : NatVector arity) :
    (PRFunction.conjoin left right).run inputs =
      natAndBit (left.run inputs) (right.run inputs) := by
  unfold PRFunction.conjoin
  rw [PRFunction.run_composition, PRFunctionVector.run_cons,
    PRFunctionVector.run_singleton, PRFunction.run_andBit]

end HeytingArithmetic
end RelationalPerimeter

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.HeytingArithmetic.PRFunction.andBit
#print axioms RelationalPerimeter.HeytingArithmetic.PRFunction.orBit
#print axioms RelationalPerimeter.HeytingArithmetic.PRFunction.conjoin
#print axioms RelationalPerimeter.HeytingArithmetic.natIfZero_zero
#print axioms RelationalPerimeter.HeytingArithmetic.natIfZero_succ
#print axioms RelationalPerimeter.HeytingArithmetic.natIfZero_zero_one_eq_positiveBit
#print axioms RelationalPerimeter.HeytingArithmetic.natPositiveBit_eq_one_iff
#print axioms RelationalPerimeter.HeytingArithmetic.natPositiveBit_pos_iff
#print axioms RelationalPerimeter.HeytingArithmetic.natEqualBit_eq_one_iff
#print axioms RelationalPerimeter.HeytingArithmetic.natEqualBit_pos_iff
#print axioms RelationalPerimeter.HeytingArithmetic.natAndBit_eq_one_iff
#print axioms RelationalPerimeter.HeytingArithmetic.natAndBit_pos_iff
#print axioms RelationalPerimeter.HeytingArithmetic.natOrBit_pos_iff
/- AXIOM_AUDIT_END -/
