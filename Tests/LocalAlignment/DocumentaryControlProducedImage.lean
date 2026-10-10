import Tests.LocalAlignment.DocumentaryControlMeasuredTransport
import RelationalPerimeter.Computation.ConstitutiveSearch.ProducedOutputImage

/-! Map the actual finite source, then remove duplicates from the actual
outputs, preserving the original last-occurrence rule and whole regime. -/
set_option genInjectivity false
set_option maxHeartbeats 8000000
namespace ConstitutiveSearch.Agent.Local.Documentary.ControlProducedImage
open Extensive Control ControlBindings ControlMasterData

def mapCode {α β : Type} (map : α → β) (operation : (value : α) → Code Label (Actual (map value))) :
    (values : List α) → Code Label (Actual (values.map map))
  | [] => .step .controlInspect (fun _ => .done ⟨[], rfl⟩)
  | head :: rest => .step .controlInspect (fun _ =>
    .step .controlCall (fun _ => (operation head).bind (fun produced =>
    (mapCode map operation rest).bind (fun tail => .step .masterConstructionReturn (fun _ =>
      .done ⟨produced.1 :: tail.1, by rw [produced.2, tail.2]; rfl⟩)))))

theorem map_finite {α β : Type} (map : α → β) (operation : (value : α) → Code Label (Actual (map value)))
    (closed : ∀ value, Finite (operation value)) (values : List α) : Finite (mapCode map operation values) := by
  induction values with
  | nil => exact finite_step _ _ (finite_done _)
  | cons head rest previous =>
    apply finite_step; apply finite_step; apply finite_bind (closed head); intro produced
    apply finite_bind previous; intro tail; exact finite_step _ _ (finite_done _)

def containsCode {α : Type} (equality : DecidableEq α)
    (compare : (left right : α) → Code Label (Actual (equality left right))) (value : α) :
    (values : List α) → Code Label (Actual (containsWith equality value values))
  | [] => .step .controlInspect (fun _ => .done ⟨false, rfl⟩)
  | head :: tail => .step .controlInspect (fun _ => (compare value head).bind (fun compared =>
    match found : compared.1 with
    | .isTrue _ => .done ⟨true, by rw [containsWith, ← compared.2, found]⟩
    | .isFalse _ => (containsCode equality compare value tail).bind (fun rest => .done
      ⟨rest.1, by rw [rest.2, containsWith, ← compared.2, found]⟩)))

theorem contains_finite {α : Type} (equality : DecidableEq α)
    (compare : (left right : α) → Code Label (Actual (equality left right)))
    (closed : ∀ left right, Finite (compare left right)) (value : α) (values : List α) :
    Finite (containsCode equality compare value values) := by
  induction values with
  | nil => exact finite_step _ _ (finite_done _)
  | cons head tail previous =>
    apply finite_step; apply finite_bind (closed value head); intro compared
    split
    · exact finite_done _
    · apply finite_bind previous; intro rest; exact finite_done _

def deduplicateCode {α : Type} (equality : DecidableEq α)
    (compare : (left right : α) → Code Label (Actual (equality left right))) :
    (values : List α) → Code Label (Actual (deduplicate equality values))
  | [] => .step .controlInspect (fun _ => .done ⟨[], rfl⟩)
  | head :: tail => .step .controlInspect (fun _ =>
    (deduplicateCode equality compare tail).bind (fun reduced =>
    (containsCode equality compare head reduced.1).bind (fun present =>
      .step .masterConstructionReturn (fun _ => match found : present.1 with
        | true => .done ⟨reduced.1, by
            obtain ⟨_, actual⟩ := present; cases actual
            obtain ⟨_, actual⟩ := reduced; cases actual
            dsimp only at found ⊢
            rw [deduplicate, found]; rfl⟩
        | false => .done ⟨head :: reduced.1, by
            obtain ⟨_, actual⟩ := present; cases actual
            obtain ⟨_, actual⟩ := reduced; cases actual
            dsimp only at found ⊢
            rw [deduplicate, found]; rfl⟩))))

theorem deduplicate_finite {α : Type} (equality : DecidableEq α)
    (compare : (left right : α) → Code Label (Actual (equality left right)))
    (closed : ∀ left right, Finite (compare left right)) (values : List α) :
    Finite (deduplicateCode equality compare values) := by
  induction values with
  | nil => exact finite_step _ _ (finite_done _)
  | cons head tail previous =>
    apply finite_step; apply finite_bind previous; intro reduced
    apply finite_bind (contains_finite equality compare closed head reduced.1); intro present
    apply finite_step; split <;> exact finite_done _

def carryCode (source : FiniteCarrier) {Target : Type} (produced : source.Identity → Target)
    (operation : (identity : source.Identity) → Code Label (Actual (produced identity)))
    (identity : source.Identity) : Code Label (Actual (ProducedOutputImage.carry source produced identity)) :=
  (operation identity).bind (fun value => .step .masterConstructionReturn (fun _ => .done
    ⟨⟨value.1, identity, value.2.symm⟩, by obtain ⟨_, actual⟩ := value; cases actual; rfl⟩))

def fromFrontier (source : FiniteCarrier) {Target : Type} (produced : source.Identity → Target)
    (equality : DecidableEq (ProducedOutputImage.Value source produced))
    (frontier : List (ProducedOutputImage.Value source produced))
    (actual : frontier = deduplicate equality (source.frontier.map (ProducedOutputImage.carry source produced))) :
    ObligationRegime source :=
  { Obligation := ProducedOutputImage.Value source produced, decEq := equality
    frontier := frontier
    complete := fun value => by rw [actual]; exact (ProducedOutputImage.imageRegime source produced equality).complete value
    nodup := by rw [actual]; exact deduplicate_nodup equality _
    carry := ProducedOutputImage.carry source produced
    carry_surjective := (ProducedOutputImage.imageRegime source produced equality).carry_surjective }

theorem from_frontier_actual (source : FiniteCarrier) {Target : Type} (produced : source.Identity → Target)
    (equality : DecidableEq (ProducedOutputImage.Value source produced))
    (frontier : List (ProducedOutputImage.Value source produced))
    (actual : frontier = deduplicate equality (source.frontier.map (ProducedOutputImage.carry source produced))) :
    fromFrontier source produced equality frontier actual = ProducedOutputImage.imageRegime source produced equality := by
  cases actual; rfl

def code (source : FiniteCarrier) {Target : Type} (produced : source.Identity → Target)
    (operation : (identity : source.Identity) → Code Label (Actual (produced identity)))
    (equality : DecidableEq (ProducedOutputImage.Value source produced))
    (compare : (left right : ProducedOutputImage.Value source produced) → Code Label (Actual (equality left right))) :
    Code Label (Actual (ProducedOutputImage.imageRegime source produced equality)) :=
  (mapCode (ProducedOutputImage.carry source produced) (carryCode source produced operation) source.frontier).bind
    (fun mapped => (deduplicateCode equality compare mapped.1).bind (fun frontier =>
      .step .masterConstructionReturn (fun _ =>
        let actual := frontier.2.trans (congrArg (deduplicate equality) mapped.2)
        .done ⟨fromFrontier source produced equality frontier.1 actual, from_frontier_actual _ _ _ _ _⟩)))

theorem finite (source : FiniteCarrier) {Target : Type} (produced : source.Identity → Target)
    (operation : (identity : source.Identity) → Code Label (Actual (produced identity)))
    (operationClosed : ∀ identity, Finite (operation identity))
    (equality : DecidableEq (ProducedOutputImage.Value source produced))
    (compare : (left right : ProducedOutputImage.Value source produced) → Code Label (Actual (equality left right)))
    (compareClosed : ∀ left right, Finite (compare left right)) :
    Finite (code source produced operation equality compare) := by
  apply finite_bind (map_finite _ _ (fun identity => by
    apply finite_bind (operationClosed identity); intro value; exact finite_step _ _ (finite_done _)) _)
  intro mapped
  apply finite_bind (deduplicate_finite equality compare compareClosed mapped.1); intro frontier
  exact finite_step _ _ (finite_done _)

end ConstitutiveSearch.Agent.Local.Documentary.ControlProducedImage

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlProducedImage.mapCode
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlProducedImage.map_finite
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlProducedImage.containsCode
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlProducedImage.contains_finite
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlProducedImage.deduplicateCode
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlProducedImage.deduplicate_finite
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlProducedImage.carryCode
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlProducedImage.fromFrontier
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlProducedImage.from_frontier_actual
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlProducedImage.code
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlProducedImage.finite
/- AXIOM_AUDIT_END -/
