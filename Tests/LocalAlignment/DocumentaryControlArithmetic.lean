import Tests.LocalAlignment.DocumentaryControlBindings

/-! Structural arithmetic on the actual read integers. Each natural constructor
is paid, with a bound depending on magnitude. Native successor, predecessor
and integer constructors remain runtime primitives. The catalogue operation
appears only in erased agreement proofs. -/
set_option genInjectivity false
set_option maxHeartbeats 5000000
namespace ConstitutiveSearch.Agent.Local.Documentary.ControlArithmetic
open Control ControlBindings

abbrev NaturalSum (left right : Nat) := {value : Nat // value = left + right}

def addCode (left right : Nat) : Code Label (NaturalSum left right) :=
  .step .integerNaturalCell (fun _ => match right with
  | 0 => .done ⟨left, rfl⟩
  | right + 1 =>
      (addCode left right).bind (fun actual =>
        .step .integerNaturalReturn (fun _ =>
          .done ⟨actual.1 + 1, congrArg Nat.succ actual.2⟩)))
termination_by structural right

def addBound : Nat → Nat
  | 0 => 1
  | right + 1 => (addBound right + 1) + 1

theorem add_bounded (left right : Nat) : Within (addCode left right) (addBound right) := by
  induction right with
  | zero => exact within_step _ _ (within_done _)
  | succ right previous =>
      rw [addCode]
      apply within_step
      apply within_bind previous
      intro actual
      exact within_step _ _ (within_done _)

abbrev NaturalDifference (left right : Nat) := {value : Int // value = Int.subNatNat left right}

theorem difference_zero (right : Nat) :
    Int.subNatNat 0 (right + 1) = Int.negSucc right := by
  unfold Int.subNatNat
  rw [Nat.sub_zero]

theorem difference_succ (left right : Nat) :
    Int.subNatNat (left + 1) (right + 1) = Int.subNatNat left right := by
  unfold Int.subNatNat
  rw [Nat.succ_sub_succ_eq_sub, Nat.succ_sub_succ_eq_sub]

def differenceCode (left right : Nat) : Code Label (NaturalDifference left right) :=
  .step .integerNaturalCell (fun _ => match right with
  | 0 => .done ⟨Int.ofNat left, by
      unfold Int.subNatNat; rw [Nat.zero_sub, Nat.sub_zero]⟩
  | right + 1 => match left with
      | 0 => .done ⟨Int.negSucc right, (difference_zero right).symm⟩
      | left + 1 => (differenceCode left right).bind (fun actual =>
          .done ⟨actual.1, actual.2.trans (difference_succ left right).symm⟩))
termination_by structural right

theorem difference_bounded (left right : Nat) : Within (differenceCode left right) (right + 1) := by
  induction right generalizing left with
  | zero => rw [differenceCode.eq_def]; exact within_step _ _ (within_done _)
  | succ right previous =>
      rw [differenceCode.eq_def]
      apply within_step
      cases left with
      | zero => exact within_weaken (within_done _) (Nat.zero_le _)
      | succ left =>
          apply within_weaken (within_bind (more := 0) (previous left) (fun _ => within_done _))
          exact Nat.le_refl _

abbrev Sum (left right : Int) := {value : Int // value = left + right}

def sumCode (left right : Int) : Code Label (Sum left right) :=
  .step .integerSign (fun _ => match left, right with
    | .ofNat left, .ofNat right =>
      (addCode left right).bind (fun actual =>
        .step .integerSignReturn (fun _ => .done ⟨Int.ofNat actual.1, congrArg Int.ofNat actual.2⟩))
    | .ofNat left, .negSucc right =>
      (differenceCode left (right + 1)).bind (fun actual => .done ⟨actual.1, actual.2⟩)
    | .negSucc left, .ofNat right =>
      (differenceCode right (left + 1)).bind (fun actual => .done ⟨actual.1, actual.2⟩)
    | .negSucc left, .negSucc right =>
      (addCode left right).bind (fun actual =>
        .step .integerSignReturn (fun _ =>
          .done ⟨Int.negSucc (actual.1 + 1), congrArg (fun value => Int.negSucc (value + 1)) actual.2⟩)))

def sumBound : Int → Int → Nat
  | .ofNat _, .ofNat right => (addBound right + 1) + 1
  | .ofNat _, .negSucc right => (right + 2) + 1
  | .negSucc left, .ofNat _ => (left + 2) + 1
  | .negSucc _, .negSucc right => (addBound right + 1) + 1

theorem sum_bounded (left right : Int) : Within (sumCode left right) (sumBound left right) := by
  cases left <;> cases right <;> unfold sumCode sumBound
  all_goals apply within_step
  · apply within_bind (more := 1) (add_bounded _ _)
    intro actual; exact within_step _ _ (within_done _)
  · apply within_bind (more := 0) (difference_bounded _ _)
    intro actual; exact within_done _
  · apply within_bind (more := 0) (difference_bounded _ _)
    intro actual; exact within_done _
  · apply within_bind (more := 1) (add_bounded _ _)
    intro actual; exact within_step _ _ (within_done _)

abbrev Negation (value : Int) := {result : Int // result = -value}

def negateCode (value : Int) : Code Label (Negation value) :=
  .step .integerNegate (fun _ => match value with
  | .ofNat value => match value with
      | 0 => .done ⟨Int.ofNat 0, rfl⟩
      | value + 1 => .done ⟨Int.negSucc value, rfl⟩
  | .negSucc value => .done ⟨Int.ofNat (value + 1), rfl⟩)

theorem negate_bounded (value : Int) : Within (negateCode value) 1 := by
  cases value with
  | ofNat value =>
      apply within_step
      cases value <;> exact within_done _
  | negSucc value => exact within_step _ _ (within_done _)

abbrev Computation (operation : Deduction.Operation) (left right : Int) :=
  {value : Int // value = Deduction.evaluate operation left right}

def code (operation : Deduction.Operation) (left right : Int) :
    Code Label (Computation operation left right) :=
  .step .integerOperation (fun _ => match operation with
    | .sum => (sumCode left right).bind (fun actual => .done ⟨actual.1, actual.2⟩)
    | .difference => (negateCode left).bind (fun negative =>
        (sumCode right negative.1).bind (fun actual =>
          .done ⟨actual.1, actual.2.trans (congrArg (fun value => right + value) negative.2)⟩)))

def bound (operation : Deduction.Operation) (left right : Int) : Nat :=
  match operation with
  | .sum => (sumBound left right + 0) + 1
  | .difference => (1 + (sumBound right (-left) + 0)) + 1

theorem bounded (operation : Deduction.Operation) (left right : Int) :
    Within (code operation left right) (bound operation left right) := by
  cases operation <;> unfold code bound
  all_goals apply within_step
  · apply within_bind (more := 0) (sum_bounded left right)
    intro actual; exact within_done _
  · apply within_bind (negate_bounded left)
    intro negative
    obtain ⟨negative, same⟩ := negative
    cases same
    apply within_bind (more := 0) (sum_bounded right (-left))
    intro actual; exact within_done _

theorem finite (operation : Deduction.Operation) (left right : Int) : Finite (code operation left right) := by
  obtain ⟨value, labels, trace, _⟩ := bounded operation left right
  exact ⟨value, labels, trace⟩

end ConstitutiveSearch.Agent.Local.Documentary.ControlArithmetic

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlArithmetic.NaturalSum
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlArithmetic.addCode
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlArithmetic.addBound
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlArithmetic.add_bounded
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlArithmetic.NaturalDifference
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlArithmetic.difference_zero
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlArithmetic.difference_succ
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlArithmetic.differenceCode
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlArithmetic.difference_bounded
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlArithmetic.Sum
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlArithmetic.sumCode
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlArithmetic.sumBound
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlArithmetic.sum_bounded
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlArithmetic.Negation
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlArithmetic.negateCode
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlArithmetic.negate_bounded
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlArithmetic.Computation
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlArithmetic.code
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlArithmetic.bound
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlArithmetic.bounded
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlArithmetic.finite
/- AXIOM_AUDIT_END -/
