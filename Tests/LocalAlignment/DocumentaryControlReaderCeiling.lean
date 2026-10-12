import Tests.LocalAlignment.DocumentaryControlAssignmentApplication
import Tests.LocalAlignment.DocumentaryControlArithmetic

/-! Received finite recipes realize the very same reader-ceiling functions.
Denotation and pointwise agreements are specification data, never an invoked
bound closure in the paid interpreter. Recipe and natural-constructor descent
occur only under paid transitions. Constructors of Realized are fixed data
formations: their caller must pay their assembly. Global envelopes and their
bootstrap are separate obligations. -/
set_option genInjectivity false
set_option backward.match.sparseCases false
set_option maxHeartbeats 10000000
namespace ConstitutiveSearch.Agent.Local.Documentary.ControlReaderCeiling
open SAT Control ControlBindings ControlMasterData ControlAssignmentApplication

inductive Recipe where
  | identity
  | flip (selected : Var)
  | maximum (child : Recipe)
  | trans (first second : Recipe)

def Recipe.denote : Recipe → Nat → Nat
  | .identity => id
  | .flip selected => flipEnvelope selected
  | .maximum child => fun budget => max budget (child.denote budget)
  | .trans first second => fun budget => second.denote (first.denote budget)

structure Realized (expected : Nat → Nat) where
  recipe : Recipe
  exact : ∀ budget, recipe.denote budget = expected budget

def Realized.identity : Realized id :=
  ⟨.identity, fun _ => rfl⟩

def Realized.flip (selected : Var) : Realized (flipEnvelope selected) :=
  ⟨.flip selected, fun _ => rfl⟩

def Realized.maximum {expected : Nat → Nat} (child : Realized expected) :
    Realized (fun budget => max budget (expected budget)) :=
  ⟨.maximum child.recipe, fun budget => congrArg (max budget) (child.exact budget)⟩

def Realized.trans {firstExpected secondExpected : Nat → Nat}
    (first : Realized firstExpected) (second : Realized secondExpected) :
    Realized (fun budget => secondExpected (firstExpected budget)) :=
  ⟨.trans first.recipe second.recipe, fun budget =>
    (second.exact (first.recipe.denote budget)).trans
      (congrArg secondExpected (first.exact budget))⟩

theorem add_finite (left right : Nat) : Finite (ControlArithmetic.addCode left right) := by
  obtain ⟨value, labels, trace, _⟩ := ControlArithmetic.add_bounded left right
  exact ⟨value, labels, trace⟩

theorem maximum_zero_left (right : Nat) : max 0 right = right := by
  rw [Nat.max_def, if_pos (Nat.zero_le right)]

theorem maximum_zero_right (left : Nat) : max left 0 = left := by
  cases Nat.decLe left 0 with
  | isTrue h =>
      rw [Nat.max_def, if_pos h]
      exact (Nat.le_antisymm h (Nat.zero_le left)).symm
  | isFalse h => rw [Nat.max_def, if_neg h]

theorem maximum_succ (left right : Nat) :
    max (left + 1) (right + 1) = max left right + 1 := by
  cases Nat.decLe left right with
  | isTrue h =>
      rw [Nat.max_def, if_pos (Nat.succ_le_succ h),
        Nat.max_def, if_pos h]
  | isFalse h =>
      have next : ¬ left + 1 ≤ right + 1 :=
        fun received => h (Nat.le_of_succ_le_succ received)
      rw [Nat.max_def, if_neg next, Nat.max_def, if_neg h]

def descendMax (left right : Nat) (frames : ControlArithmetic.Frames) :
    Code Label (Actual (max left right + frames.length)) :=
  .step .integerNaturalCell (fun _ => match left, right with
    | 0, right =>
      ControlArithmetic.reindex (by rw [maximum_zero_left]) (ControlArithmetic.returns right frames)
    | left + 1, 0 =>
      ControlArithmetic.reindex (by rw [maximum_zero_right]) (ControlArithmetic.returns (left + 1) frames)
    | left + 1, right + 1 =>
      .admin .allocation (fun _ =>
        ControlArithmetic.reindex (by
          rw [List.length_cons, maximum_succ, Nat.add_succ, Nat.succ_add])
          (descendMax left right (() :: frames))))
termination_by structural left

def maxCode (left right : Nat) : Code Label (Actual (max left right)) :=
  ControlArithmetic.reindex (by rw [List.length_nil, Nat.add_zero]) (descendMax left right [])

theorem minimum_zero_left (right : Nat) : min 0 right = 0 := by
  rw [Nat.min_def, if_pos (Nat.zero_le right)]

theorem minimum_zero_right (left : Nat) : min left 0 = 0 := by
  cases Nat.decLe left 0 with
  | isTrue below =>
      rw [Nat.min_def, if_pos below]
      exact Nat.le_antisymm below (Nat.zero_le left)
  | isFalse above => rw [Nat.min_def, if_neg above]

theorem minimum_succ (left right : Nat) :
    min (left + 1) (right + 1) = min left right + 1 := by
  cases Nat.decLe left right with
  | isTrue below =>
      rw [Nat.min_def, if_pos (Nat.succ_le_succ below), Nat.min_def, if_pos below]
  | isFalse above =>
      have next : ¬ left + 1 ≤ right + 1 :=
        fun received => above (Nat.le_of_succ_le_succ received)
      rw [Nat.min_def, if_neg next, Nat.min_def, if_neg above]

def descendMax_trace : (left right : Nat) → (frames : ControlArithmetic.Frames) →
    Eval (descendMax left right frames)
      (List.replicate (min left right + 1) .integerNaturalCell ++
        List.replicate (min left right + frames.length) .integerNaturalReturn)
      (⟨max left right + frames.length, rfl⟩ : Actual (max left right + frames.length))
  | 0, right, frames =>
      let received := ControlArithmetic.reindex_trace
        (before := right + frames.length) (after := max 0 right + frames.length)
        (by rw [maximum_zero_left]) (ControlArithmetic.returns_trace right frames)
      let trace : Eval (descendMax 0 right frames)
          (Label.integerNaturalCell :: List.replicate frames.length Label.integerNaturalReturn)
          (⟨max 0 right + frames.length, rfl⟩ : Actual (max 0 right + frames.length)) :=
        .step received
      ControlArithmetic.relabel_trace (by
        rw [minimum_zero_left]
        change Label.integerNaturalCell :: List.replicate frames.length Label.integerNaturalReturn =
          Label.integerNaturalCell :: List.replicate (0 + frames.length) Label.integerNaturalReturn
        exact congrArg (List.cons Label.integerNaturalCell)
          (congrArg (fun count => List.replicate count Label.integerNaturalReturn)
            (Nat.zero_add frames.length).symm)) trace
  | left + 1, 0, frames =>
      let received := ControlArithmetic.reindex_trace
        (before := left + 1 + frames.length) (after := max (left + 1) 0 + frames.length)
        (by rw [maximum_zero_right]) (ControlArithmetic.returns_trace (left + 1) frames)
      let trace : Eval (descendMax (left + 1) 0 frames)
          (Label.integerNaturalCell :: List.replicate frames.length Label.integerNaturalReturn)
          (⟨max (left + 1) 0 + frames.length, rfl⟩ : Actual (max (left + 1) 0 + frames.length)) :=
        .step received
      ControlArithmetic.relabel_trace (by
        rw [minimum_zero_right]
        change Label.integerNaturalCell :: List.replicate frames.length Label.integerNaturalReturn =
          Label.integerNaturalCell :: List.replicate (0 + frames.length) Label.integerNaturalReturn
        exact congrArg (List.cons Label.integerNaturalCell)
          (congrArg (fun count => List.replicate count Label.integerNaturalReturn)
            (Nat.zero_add frames.length).symm)) trace
  | left + 1, right + 1, frames =>
      let received := ControlArithmetic.reindex_trace
        (before := max left right + (() :: frames).length)
        (after := max (left + 1) (right + 1) + frames.length)
        (by rw [List.length_cons, maximum_succ, Nat.add_succ, Nat.succ_add])
        (descendMax_trace left right (() :: frames))
      let after : Eval
          (ControlArithmetic.reindex (by rw [List.length_cons, maximum_succ, Nat.add_succ, Nat.succ_add])
            (descendMax left right (() :: frames)))
          (List.replicate (min left right + 1) Label.integerNaturalCell ++
            List.replicate ((min left right + 1) + frames.length) Label.integerNaturalReturn)
          (⟨max (left + 1) (right + 1) + frames.length, rfl⟩ :
            Actual (max (left + 1) (right + 1) + frames.length)) :=
        ControlArithmetic.relabel_trace
          (congrArg (fun count => List.replicate (min left right + 1) Label.integerNaturalCell ++
            List.replicate count Label.integerNaturalReturn)
            ((Nat.add_succ (min left right) frames.length).trans
              (Nat.succ_add (min left right) frames.length).symm)) received
      let trace : Eval (descendMax (left + 1) (right + 1) frames)
          (Label.integerNaturalCell ::
            (List.replicate (min left right + 1) Label.integerNaturalCell ++
              List.replicate ((min left right + 1) + frames.length) Label.integerNaturalReturn))
          (⟨max (left + 1) (right + 1) + frames.length, rfl⟩ :
            Actual (max (left + 1) (right + 1) + frames.length)) :=
        .step (.admin after)
      ControlArithmetic.relabel_trace (by
        rw [minimum_succ,
          List.replicate_succ (n := min left right + 1) (a := Label.integerNaturalCell),
          List.cons_append]) trace
termination_by structural left _right _frames => left

def max_trace (left right : Nat) :
    Eval (maxCode left right) (ControlArithmetic.businessLabels (min left right))
      (⟨max left right, rfl⟩ : Actual (max left right)) :=
  ControlArithmetic.reindex_trace (by rw [List.length_nil, Nat.add_zero]) (descendMax_trace left right [])

theorem max_bounded (left right : Nat) :
    Within (maxCode left right) (2 * min left right + 1) :=
  ⟨⟨max left right, rfl⟩, ControlArithmetic.businessLabels (min left right), ⟨max_trace left right⟩,
    Nat.le_of_eq (ControlArithmetic.businessLabels_length (min left right))⟩

theorem max_finite (left right : Nat) : Finite (maxCode left right) :=
  ⟨⟨max left right, rfl⟩, ControlArithmetic.businessLabels (min left right), ⟨max_trace left right⟩⟩

theorem max_run (left right fuel : Nat) :
    runCtl fuel (maxCode left right) =
      if 2 * min left right + 1 ≤ fuel then
        some ((⟨max left right, rfl⟩ : Actual (max left right)), ControlArithmetic.businessLabels (min left right))
      else none := by
  have received := ControlArithmetic.run_characterization (max_trace left right) fuel
  rw [ControlArithmetic.businessLabels_length] at received
  exact received

def recipeCode (recipe : Recipe) (budget : Nat) :
    Code Label (Actual (recipe.denote budget)) :=
  .step .controlInspect (fun _ => match recipe with
    | .identity => .done ⟨budget, rfl⟩
    | .flip selected =>
        (ControlArithmetic.addCode selected 1).bind (fun selectedNext =>
          (ControlArithmetic.addCode budget 1).bind (fun budgetNext =>
            (ControlArithmetic.addCode selectedNext.1 budgetNext.1).bind (fun combined =>
              .step .integerNaturalReturn (fun _ => .done
                ⟨combined.1 + 1, by
                  change combined.1 + 1 = ((selected + 1) + (budget + 1)) + 1
                  rw [combined.2, selectedNext.2, budgetNext.2]⟩))))
    | .maximum child => (recipeCode child budget).bind (fun received =>
        (maxCode budget received.1).bind (fun combined =>
          .step .controlResult (fun _ => .done
            ⟨combined.1, combined.2.trans (congrArg (max budget) received.2)⟩)))
    | .trans first second => (recipeCode first budget).bind (fun received =>
        (recipeCode second received.1).bind (fun next =>
          .step .controlResult (fun _ => .done
            ⟨next.1, next.2.trans (congrArg second.denote received.2)⟩))))
termination_by structural recipe

theorem recipe_finite (recipe : Recipe) (budget : Nat) : Finite (recipeCode recipe budget) := by
  induction recipe generalizing budget with
  | identity => rw [recipeCode]; exact finite_step _ _ (finite_done _)
  | flip selected =>
      rw [recipeCode]; apply finite_step
      apply finite_bind (add_finite selected 1); intro selectedNext
      apply finite_bind (add_finite budget 1); intro budgetNext
      apply finite_bind (add_finite selectedNext.1 budgetNext.1); intro combined
      exact finite_step _ _ (finite_done _)
  | maximum child previous =>
      rw [recipeCode]; apply finite_step
      apply finite_bind (previous budget); intro received
      apply finite_bind (max_finite budget received.1); intro combined
      exact finite_step _ _ (finite_done _)
  | trans first second firstPrevious secondPrevious =>
      rw [recipeCode]; apply finite_step
      apply finite_bind (firstPrevious budget); intro received
      apply finite_bind (secondPrevious received.1); intro next
      exact finite_step _ _ (finite_done _)

theorem recipe_zero (recipe : Recipe) (budget : Nat) :
    runCtl 0 (recipeCode recipe budget) = none := by
  cases recipe <;> rw [recipeCode] <;> rfl

theorem max_zero (left right : Nat) : runCtl 0 (maxCode left right) = none :=
  (max_run left right 0).trans (if_neg (Nat.not_succ_le_zero (2 * min left right)))
def code {expected : Nat → Nat} (realized : Realized expected) (budget : Nat) :
    Code Label (Actual (expected budget)) :=
  (recipeCode realized.recipe budget).bind (fun received =>
    .step .controlResult (fun _ =>
      .done ⟨received.1, received.2.trans (realized.exact budget)⟩))

theorem finite {expected : Nat → Nat} (realized : Realized expected) (budget : Nat) :
    Finite (code realized budget) := by
  apply finite_bind (recipe_finite realized.recipe budget); intro received
  exact finite_step _ _ (finite_done _)

end ConstitutiveSearch.Agent.Local.Documentary.ControlReaderCeiling

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlReaderCeiling.Recipe
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlReaderCeiling.Recipe.denote
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlReaderCeiling.Realized
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlReaderCeiling.Realized.identity
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlReaderCeiling.Realized.flip
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlReaderCeiling.Realized.maximum
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlReaderCeiling.Realized.trans
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlReaderCeiling.add_finite
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlReaderCeiling.maximum_zero_left
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlReaderCeiling.maximum_zero_right
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlReaderCeiling.maximum_succ
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlReaderCeiling.descendMax
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlReaderCeiling.maxCode
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlReaderCeiling.minimum_zero_left
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlReaderCeiling.minimum_zero_right
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlReaderCeiling.minimum_succ
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlReaderCeiling.descendMax_trace
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlReaderCeiling.max_trace
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlReaderCeiling.max_bounded
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlReaderCeiling.max_finite
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlReaderCeiling.max_run
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlReaderCeiling.recipeCode
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlReaderCeiling.recipe_finite
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlReaderCeiling.recipe_zero
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlReaderCeiling.max_zero
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlReaderCeiling.code
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlReaderCeiling.finite
/- AXIOM_AUDIT_END -/
