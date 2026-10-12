import Tests.LocalAlignment.DocumentaryControlBindings

/-! Structural arithmetic on the actual read integers. Each natural constructor
is paid, with a bound depending on magnitude. Native successor, predecessor
and integer constructors remain runtime primitives. The catalogue operation
appears only in erased agreement proofs. -/
set_option genInjectivity false
set_option backward.match.sparseCases false
set_option maxHeartbeats 5000000
namespace ConstitutiveSearch.Agent.Local.Documentary.ControlArithmetic
open Control ControlBindings
universe u

abbrev NaturalSum (left right : Nat) := {value : Nat // value = left + right}

abbrev NaturalActual (expected : Nat) := {value : Nat // value = expected}

abbrev Frames := List Unit

/- Reindexing is proof transport only. Expected sums, maxima and lengths below
occur in types/proofs. Generated C must confirm they are erased. -/
@[inline] def reindex {before after : Nat} (same : before = after)
    (code : Code Label (NaturalActual before)) : Code Label (NaturalActual after) :=
  same ▸ code

def reindex_trace {before after : Nat} (same : before = after)
    {code : Code Label (NaturalActual before)} {labels : List Label}
    (actual : Eval code labels (⟨before, rfl⟩ : NaturalActual before)) :
    Eval (reindex same code) labels (⟨after, rfl⟩ : NaturalActual after) := by
  cases same
  exact actual

def relabel_trace {Value : Type u} {code : Code Label Value}
    {before after : List Label} {value : Value} (same : before = after)
    (actual : Eval code before value) : Eval code after value :=
  same ▸ actual

def canonical_trace {expected : Nat} {code : Code Label (NaturalActual expected)}
    {labels : List Label} (actual : NaturalActual expected) (trace : Eval code labels actual) :
    Eval code labels (⟨expected, rfl⟩ : NaturalActual expected) := by
  obtain ⟨value, same⟩ := actual
  cases same
  exact trace

def returns (value : Nat) (frames : Frames) :
    Code Label (NaturalActual (value + frames.length)) :=
  .admin .frame (fun _ => match frames with
    | [] => .done ⟨value, (Nat.add_zero value).symm⟩
    | _ :: rest => .step .integerNaturalReturn (fun _ =>
        reindex (by rw [List.length_cons, Nat.succ_add, Nat.add_succ])
          (returns (value + 1) rest)))
termination_by structural frames

def descendAdd (left right : Nat) (frames : Frames) :
    Code Label (NaturalActual (left + (right + frames.length))) :=
  .step .integerNaturalCell (fun _ => match right with
    | 0 => reindex (by rw [Nat.zero_add]) (returns left frames)
    | right + 1 =>
      .admin .allocation (fun _ =>
        reindex (by rw [List.length_cons, Nat.add_succ, Nat.succ_add])
          (descendAdd left right (() :: frames))))
termination_by structural right

def addCode (left right : Nat) : Code Label (NaturalSum left right) :=
  reindex (by rw [List.length_nil, Nat.add_zero]) (descendAdd left right [])

def businessLabels (count : Nat) : List Label :=
  List.replicate (count + 1) .integerNaturalCell ++
    List.replicate count .integerNaturalReturn

theorem businessLabels_zero : businessLabels 0 = [.integerNaturalCell] := rfl

theorem businessLabels_succ (count : Nat) :
    businessLabels (count + 1) =
      .integerNaturalCell :: (businessLabels count ++ [.integerNaturalReturn]) := by
  have appendAssoc : ∀ (first second third : List Label),
      (first ++ second) ++ third = first ++ (second ++ third) := by
    intro first second third
    induction first with
    | nil => rfl
    | cons head rest previous => exact congrArg (List.cons head) previous
  have replicateSnoc : ∀ (count : Nat) (label : Label),
      List.replicate (count + 1) label = List.replicate count label ++ [label] := by
    intro count label
    induction count with
    | zero => rfl
    | succ count previous => exact congrArg (List.cons label) previous
  unfold businessLabels
  rw [List.replicate_succ,
    replicateSnoc count Label.integerNaturalReturn,
    List.cons_append, appendAssoc]

theorem businessLabels_length (count : Nat) :
    (businessLabels count).length = 2 * count + 1 := by
  have appendLength : ∀ (first second : List Label),
      (first ++ second).length = first.length + second.length := by
    intro first second
    induction first with
    | nil => exact (Nat.zero_add second.length).symm
    | cons head rest previous =>
        exact (congrArg Nat.succ previous).trans (Nat.succ_add rest.length second.length).symm
  have replicateLength : ∀ (count : Nat) (label : Label),
      (List.replicate count label).length = count := by
    intro count label
    induction count with
    | zero => rfl
    | succ count previous => exact congrArg Nat.succ previous
  rw [businessLabels, appendLength, replicateLength, replicateLength]
  have double : 2 * count = count + count := by
    rw [Nat.succ_mul, Nat.one_mul]
  rw [double, Nat.add_right_comm count 1 count]

def returns_trace (value : Nat) : (frames : Frames) →
    Eval (returns value frames) (List.replicate frames.length .integerNaturalReturn)
      (⟨value + frames.length, rfl⟩ : NaturalActual (value + frames.length))
  | [] => .admin .done
  | _ :: rest => .admin (.step (reindex_trace
      (by rw [List.length_cons, Nat.succ_add, Nat.add_succ])
      (returns_trace (value + 1) rest)))
termination_by structural frames => frames

def descendAdd_trace (left : Nat) : (right : Nat) → (frames : Frames) →
    Eval (descendAdd left right frames)
      (List.replicate (right + 1) .integerNaturalCell ++
        List.replicate (right + frames.length) .integerNaturalReturn)
      (⟨left + (right + frames.length), rfl⟩ : NaturalActual (left + (right + frames.length)))
  | 0, frames => .step (relabel_trace
      (congrArg (fun count => List.replicate count Label.integerNaturalReturn)
        (Nat.zero_add frames.length).symm)
      (reindex_trace (by rw [Nat.zero_add]) (returns_trace left frames)))
  | right + 1, frames => .step (.admin (relabel_trace
      (congrArg (fun count => List.replicate (right + 1) Label.integerNaturalCell ++
        List.replicate count Label.integerNaturalReturn)
        ((Nat.add_succ right frames.length).trans (Nat.succ_add right frames.length).symm))
      (reindex_trace
        (by rw [List.length_cons, Nat.add_succ, Nat.succ_add])
        (descendAdd_trace left right (() :: frames)))))
termination_by structural right _frames => right

def add_trace (left right : Nat) :
    Eval (addCode left right) (businessLabels right)
      (⟨left + right, rfl⟩ : NaturalSum left right) :=
  reindex_trace (by rw [List.length_nil, Nat.add_zero]) (descendAdd_trace left right [])

def addBound : Nat → Nat
  | 0 => 1
  | right + 1 => (addBound right + 1) + 1

theorem addBound_exact (right : Nat) : addBound right = 2 * right + 1 := by
  induction right with
  | zero => rfl
  | succ right previous =>
      rw [addBound, previous, Nat.mul_succ]

theorem add_bounded (left right : Nat) :
    Within (addCode left right) (addBound right) := by
  exact ⟨⟨left + right, rfl⟩, businessLabels right, ⟨add_trace left right⟩,
    Nat.le_of_eq ((businessLabels_length right).trans (addBound_exact right).symm)⟩

theorem add_exact_bound (left right : Nat) :
    Within (addCode left right) (2 * right + 1) :=
  ⟨⟨left + right, rfl⟩, businessLabels right, ⟨add_trace left right⟩,
    Nat.le_of_eq (businessLabels_length right)⟩

theorem add_finite (left right : Nat) : Finite (addCode left right) :=
  ⟨⟨left + right, rfl⟩, businessLabels right, ⟨add_trace left right⟩⟩

theorem run_characterization {Value : Type u} {code : Code Label Value}
    {labels : List Label} {value : Value} (actual : Eval code labels value) (fuel : Nat) :
    runCtl fuel code = if labels.length ≤ fuel then some (value, labels) else none := by
  cases Nat.decLe labels.length fuel with
  | isTrue enough => rw [if_pos enough]; exact ctl_complete actual fuel enough
  | isFalse insufficient =>
      rw [if_neg insufficient]
      exact fuel_short actual fuel (Nat.lt_of_not_ge insufficient)

theorem add_run (left right fuel : Nat) :
    runCtl fuel (addCode left right) =
      if 2 * right + 1 ≤ fuel then
        some ((⟨left + right, rfl⟩ : NaturalSum left right), businessLabels right)
      else none := by
  have received := run_characterization (add_trace left right) fuel
  rw [businessLabels_length] at received
  exact received

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
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlArithmetic.NaturalActual
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlArithmetic.Frames
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlArithmetic.reindex
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlArithmetic.reindex_trace
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlArithmetic.relabel_trace
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlArithmetic.canonical_trace
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlArithmetic.returns
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlArithmetic.descendAdd
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlArithmetic.addCode
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlArithmetic.businessLabels
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlArithmetic.businessLabels_zero
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlArithmetic.businessLabels_succ
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlArithmetic.businessLabels_length
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlArithmetic.returns_trace
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlArithmetic.descendAdd_trace
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlArithmetic.add_trace
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlArithmetic.addBound
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlArithmetic.addBound_exact
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlArithmetic.add_bounded
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlArithmetic.add_exact_bound
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlArithmetic.add_finite
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlArithmetic.run_characterization
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlArithmetic.add_run
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
