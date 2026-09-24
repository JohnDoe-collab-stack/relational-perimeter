import RelationalPerimeter.Foundations.CircularRegime

/- The proposition-valued definitions below are intentionally transparent,
   and the independent input families intentionally keep distinct universes. -/
set_option linter.defProp false
set_option linter.checkUnivs false

namespace StrongPerimetralTurning

universe uE uI uK uD uP uN uEnd uLoop uA uB uV

/-! ## Derived structural length

`Nat` enters only here, after the constitutive boundary and its maximality have
already been proved.  It measures an already constituted history; it does not
generate either the perimeter or its deployment. -/

namespace History

def length
    {State : Type uA}
    {Step : State → State → Type uB}
    {source target : State} :
    History Step source target → Nat
  | .root => 0
  | .extend history _ => history.length + 1

@[simp] theorem length_root
    {State : Type uA}
    {Step : State → State → Type uB}
    {state : State} :
    length (.root : History Step state state) = 0 := rfl

@[simp] theorem length_extend
    {State : Type uA}
    {Step : State → State → Type uB}
    {source middle target : State}
    (history : History Step source middle)
    (step : Step middle target) :
    length (.extend history step) = length history + 1 := rfl

def length_append_exact
    {State : Type uA}
    {Step : State → State → Type uB}
    {source middle target : State}
    (firstHistory : History Step source middle)
    (continuation : History Step middle target) : PLift (
    length (append firstHistory continuation) =
      length firstHistory + length continuation) :=
  match continuation with
  | .root => ⟨rfl⟩
  | .extend previous step =>
      let inductionData := length_append_exact firstHistory previous
      ⟨(congrArg (fun value => value + 1) inductionData.down).trans
        (Nat.add_assoc _ _ 1)⟩

theorem length_append
    {State : Type uA}
    {Step : State → State → Type uB}
    {source middle target : State}
    (firstHistory : History Step source middle)
    (continuation : History Step middle target) :
    length (append firstHistory continuation) =
      length firstHistory + length continuation :=
  (length_append_exact firstHistory continuation).down

end History

private theorem self_le_add_right (left right : Nat) :
    left ≤ left + right := by
  induction right with
  | zero => exact Nat.le_refl left
  | succ right inductionHypothesis =>
      rw [Nat.add_succ]
      exact Nat.le.step inductionHypothesis

private theorem self_lt_add_positive
    (left right : Nat) :
    left < left + (right + 1) := by
  change Nat.succ left ≤ left + (right + 1)
  rw [← Nat.add_assoc]
  exact Nat.succ_le_succ (self_le_add_right left right)

theorem prefix_length_le
    {P : CircularPresentation}
    {first second : RootedGeneratedHistory P}
    (prefixWitness : ConstitutivePrefix first second) :
    first.history.length ≤ second.history.length := by
  rcases prefixWitness with ⟨continuation, equality⟩
  calc
    first.history.length ≤
        first.history.length + continuation.length :=
      self_le_add_right _ _
    _ = (History.append first.history continuation).length :=
      (History.length_append first.history continuation).symm
    _ = second.history.length := congrArg History.length equality

theorem strictPrefix_length_lt
    {P : CircularPresentation}
    {first second : RootedGeneratedHistory P}
    (strict : StrictConstitutivePrefix first second) :
    first.history.length < second.history.length := by
  rcases strict with ⟨continuation, equality⟩
  calc
    first.history.length <
        first.history.length +
          (continuation.priorHistory.length + 1) :=
      self_lt_add_positive _ _
    _ = first.history.length + continuation.toHistory.length := rfl
    _ = (History.append first.history continuation.toHistory).length :=
      (History.length_append first.history continuation.toHistory).symm
    _ = second.history.length := congrArg History.length equality

theorem partial_length_le_perimeter
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (partialPath : FreePartialRealization P history) :
    history.history.length ≤ (perimeterDeployment P).history.length :=
  prefix_length_le (partial_is_prefix_of_perimeter partialPath)

theorem admissible_length_le_perimeter
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (admissible : PerimetrallyAdmissible P history) :
    history.history.length ≤ (perimeterDeployment P).history.length :=
  prefix_length_le (admissible_is_prefix_of_perimeter admissible)

theorem samePerimeter_length_eq
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (refinement : CircularRefinement P history) :
    history.history.length = (perimeterDeployment P).history.length := by
  cases noIntermediateRefinement refinement
  rfl

theorem no_longer_samePerimeter
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (refinement : CircularRefinement P history) :
    ¬ (perimeterDeployment P).history.length < history.history.length := by
  rw [samePerimeter_length_eq refinement]
  exact Nat.lt_irrefl _


end StrongPerimetralTurning

/- AXIOM_AUDIT_BEGIN -/
#print axioms StrongPerimetralTurning.History.length
#print axioms StrongPerimetralTurning.samePerimeter_length_eq
/- AXIOM_AUDIT_END -/
