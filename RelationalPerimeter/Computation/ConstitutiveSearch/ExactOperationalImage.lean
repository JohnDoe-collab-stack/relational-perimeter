import RelationalPerimeter.Computation.ConstitutiveSearch.FiniteExtensiveAddressing

/-!
# Exact finite images of operational targets

This module constructs the operational carrier as the duplicate-free image of
an actually supplied target map.  It does not prescribe a width.  In
particular, width one is equivalent, for a nonempty finite source, to the
convergence of all produced targets.
-/

namespace ConstitutiveSearch
namespace Extensive

/-- Constructive membership test with an explicit equality decision. -/
def containsWith
    {α : Type}
    (decideEq : DecidableEq α)
    (value : α) : List α → Bool
  | [] => false
  | head :: tail =>
      match decideEq value head with
      | isTrue _ => true
      | isFalse _ => containsWith decideEq value tail

theorem containsWith_eq_true_iff_mem
    {α : Type}
    (decideEq : DecidableEq α)
    (value : α) :
    ∀ values : List α, containsWith decideEq value values = true ↔ value ∈ values
  | [] => by
      constructor <;> intro impossible <;> cases impossible
  | head :: tail => by
      unfold containsWith
      cases same : decideEq value head with
      | isTrue equal =>
          constructor
          · intro _
            exact equal ▸ .head _
          · intro _
            rfl
      | isFalse different =>
          constructor
          · intro found
            exact .tail _ ((containsWith_eq_true_iff_mem decideEq value tail).mp found)
          · intro member
            cases member with
            | head _ => exact False.elim (different rfl)
            | tail _ tailMember =>
                exact (containsWith_eq_true_iff_mem decideEq value tail).mpr tailMember

/-- Constructive duplicate removal, preserving the last occurrence. -/
def deduplicate
    {α : Type}
    (decideEq : DecidableEq α) : List α → List α
  | [] => []
  | head :: tail =>
      let reducedTail := deduplicate decideEq tail
      if containsWith decideEq head reducedTail then
        reducedTail
      else
        head :: reducedTail

/-- Duplicate removal preserves and reflects membership. -/
theorem mem_deduplicate_iff
    {α : Type}
    (decideEq : DecidableEq α)
    (value : α) :
    ∀ values : List α,
      value ∈ deduplicate decideEq values ↔ value ∈ values
  | [] => Iff.rfl
  | head :: tail => by
      change
        value ∈
            (if containsWith decideEq head (deduplicate decideEq tail) then
              deduplicate decideEq tail
            else
              head :: deduplicate decideEq tail) ↔
          value ∈ head :: tail
      cases repeated :
          containsWith decideEq head (deduplicate decideEq tail) with
      | true =>
        rw [if_pos rfl]
        have headRepeated : head ∈ deduplicate decideEq tail :=
          (containsWith_eq_true_iff_mem decideEq head _).mp repeated
        constructor
        · intro reducedMember
          exact .tail _
            ((mem_deduplicate_iff decideEq value tail).mp reducedMember)
        · intro sourceMember
          cases sourceMember with
          | head _ => exact headRepeated
          | tail _ tailMember =>
              exact (mem_deduplicate_iff decideEq value tail).mpr tailMember
      | false =>
        rw [if_neg Bool.false_ne_true]
        constructor
        · intro reducedMember
          cases reducedMember with
          | head _ => exact .head _
          | tail _ tailMember =>
              exact .tail _
                ((mem_deduplicate_iff decideEq value tail).mp tailMember)
        · intro sourceMember
          cases sourceMember with
          | head _ => exact .head _
          | tail _ tailMember =>
              exact .tail _
                ((mem_deduplicate_iff decideEq value tail).mpr tailMember)

/-- Duplicate removal produces a duplicate-free list. -/
theorem deduplicate_nodup
    {α : Type}
    (decideEq : DecidableEq α) :
    ∀ values : List α, (deduplicate decideEq values).Nodup
  | [] => .nil
  | head :: tail => by
      change
        (if containsWith decideEq head (deduplicate decideEq tail) then
          deduplicate decideEq tail
        else
          head :: deduplicate decideEq tail).Nodup
      cases repeated :
          containsWith decideEq head (deduplicate decideEq tail) with
      | true =>
          rw [if_pos rfl]
          exact deduplicate_nodup decideEq tail
      | false =>
          rw [if_neg Bool.false_ne_true]
          exact .cons
            (fun value member same => by
              have headMember : head ∈ deduplicate decideEq tail :=
                same ▸ member
              have found :=
                (containsWith_eq_true_iff_mem decideEq head _).mpr headMember
              rw [repeated] at found
              exact Bool.noConfusion found)
            (deduplicate_nodup decideEq tail)

/-- If a nonempty list has only one value, its duplicate-free image is a singleton. -/
theorem deduplicate_eq_singleton_of_nonempty_of_all_eq
    {α : Type}
    (decideEq : DecidableEq α)
    (values : List α)
    (anchor : α)
    (nonempty : values ≠ [])
    (allEqual : (value : α) → value ∈ values → value = anchor) :
    deduplicate decideEq values = [anchor] := by
  induction values with
  | nil => exact False.elim (nonempty rfl)
  | cons head tail inductionHypothesis =>
      have headExact : head = anchor := allEqual head (.head _)
      cases tail with
      | nil =>
          cases headExact
          rfl
      | cons tailHead tailTail =>
          have tailNonempty : tailHead :: tailTail ≠ [] := by
            intro impossible
            cases impossible
          have tailAllEqual :
              (value : α) → value ∈ tailHead :: tailTail → value = anchor :=
            fun value member => allEqual value (.tail _ member)
          have tailExact :
              deduplicate decideEq (tailHead :: tailTail) = [anchor] :=
            inductionHypothesis tailNonempty tailAllEqual
          change
            (if containsWith decideEq head
                (deduplicate decideEq (tailHead :: tailTail)) then
              deduplicate decideEq (tailHead :: tailTail)
            else
              head :: deduplicate decideEq (tailHead :: tailTail)) = [anchor]
          rw [tailExact, headExact]
          have contained : containsWith decideEq anchor [anchor] = true := by
            unfold containsWith
            cases same : decideEq anchor anchor with
            | isTrue _ => rfl
            | isFalse different => exact False.elim (different rfl)
          rw [contained]
          rw [if_pos rfl]

theorem containsWith_singleton_eq
    {α : Type}
    (decideEq : DecidableEq α)
    (value head : α) :
    containsWith decideEq value [head] = true → value = head := by
  intro found
  cases decision : decideEq value head with
  | isTrue same => exact same
  | isFalse _ =>
      have computed : containsWith decideEq value [head] = false := by
        unfold containsWith
        rw [decision]
        rfl
      exact False.elim (Bool.noConfusion (Eq.trans computed.symm found))

theorem list_ne_nil_of_mem
    {α : Type} {value : α} {values : List α}
    (member : value ∈ values) : values ≠ [] := by
  intro empty
  cases empty
  exact nomatch member

theorem map_ne_nil
    {α β : Type}
    (map : α → β) :
    ∀ {values : List α}, values ≠ [] → values.map map ≠ []
  | [], nonempty => False.elim (nonempty rfl)
  | _ :: _, _ => fun impossible => nomatch impossible

/-- Duplicate-free image of a target map over a complete finite source. -/
def exactTargetImageFrontier
    (source : FiniteCarrier)
    {Target : Type}
    (targetDecEq : DecidableEq Target)
    (target : source.Identity → Target) : List Target := by
  letI : DecidableEq Target := targetDecEq
  exact deduplicate targetDecEq (source.frontier.map target)

theorem exactTargetImageFrontier_complete
    (source : FiniteCarrier)
    {Target : Type}
    (targetDecEq : DecidableEq Target)
    (target : source.Identity → Target)
    (identity : source.Identity) :
    target identity ∈ exactTargetImageFrontier source targetDecEq target := by
  letI : DecidableEq Target := targetDecEq
  exact (mem_deduplicate_iff targetDecEq (target identity) _).mpr
    (Extensive.mem_map target (source.complete identity))

theorem exactTargetImageFrontier_nodup
    (source : FiniteCarrier)
    {Target : Type}
    (targetDecEq : DecidableEq Target)
    (target : source.Identity → Target) :
    (exactTargetImageFrontier source targetDecEq target).Nodup := by
  letI : DecidableEq Target := targetDecEq
  exact deduplicate_nodup targetDecEq _

/-- Positive witness that the computed target image converges at one target. -/
structure ConvergentExactTargetImage
    (source : FiniteCarrier)
    {Target : Type}
    (target : source.Identity → Target)
    (anchor : source.Identity) where
  targetConverges :
    (identity : source.Identity) → target identity = target anchor

/-- Positive provenance of one realized target-image obligation. -/
structure TargetImagePreimage
    (source : FiniteCarrier)
    {Obligation : Type}
    (carry : source.Identity → Obligation)
    (obligation : Obligation) where
  identity : source.Identity
  exact : carry identity = obligation

/--
A finite realization of exactly the image of a target computation.  The
obligation carrier is not allowed to identify distinct target values or to
contain an obligation with no source provenance.
-/
structure ExactTargetImageRealization
    (source : FiniteCarrier)
    {Target : Type}
    (target : source.Identity → Target) where
  Obligation : Type
  decEq : DecidableEq Obligation
  frontier : List Obligation
  complete : (obligation : Obligation) → obligation ∈ frontier
  nodup : frontier.Nodup
  value : Obligation → Target
  value_injective : Function.Injective value
  carry : source.Identity → Obligation
  carry_exact : (identity : source.Identity) →
    value (carry identity) = target identity
  carry_surjective : (obligation : Obligation) →
    TargetImagePreimage source carry obligation

/-- Forget only the target values and provenance, after exact realization. -/
def ExactTargetImageRealization.toObligationRegime
    {source : FiniteCarrier}
    {Target : Type}
    {target : source.Identity → Target}
    (realization : ExactTargetImageRealization source target) :
    ObligationRegime source :=
  { Obligation := realization.Obligation
    decEq := realization.decEq
    frontier := realization.frontier
    complete := realization.complete
    nodup := realization.nodup
    carry := realization.carry
    carry_surjective := fun obligation =>
      let provenance := realization.carry_surjective obligation
      ⟨provenance.identity, provenance.exact⟩ }

/-- An exact realization has exactly the fibres of its target computation. -/
theorem ExactTargetImageRealization.carry_eq_iff_target_eq
    {source : FiniteCarrier}
    {Target : Type}
    {target : source.Identity → Target}
    (realization : ExactTargetImageRealization source target)
    (left right : source.Identity) :
    realization.carry left = realization.carry right ↔
      target left = target right := by
  constructor
  · intro carryExact
    exact Eq.trans (realization.carry_exact left).symm
      (Eq.trans (congrArg realization.value carryExact)
        (realization.carry_exact right))
  · intro targetExact
    apply realization.value_injective
    exact Eq.trans (realization.carry_exact left)
      (Eq.trans targetExact (realization.carry_exact right).symm)

/--
For an exact realization of a nonempty source, width one is equivalent to
convergence of all computed targets. Thus a singleton frontier cannot hide an
additional identification introduced by the realization.
-/
theorem ExactTargetImageRealization.width_one_iff_all_targets_equal
    (source : FiniteCarrier)
    {Target : Type}
    (target : source.Identity → Target)
    (realization : ExactTargetImageRealization source target)
    (anchor : source.Identity) :
    realization.frontier.length = 1 ↔
      ∀ left right : source.Identity, target left = target right := by
  constructor
  · intro widthExact left right
    apply (realization.carry_eq_iff_target_eq left right).mp
    cases frontierExact : realization.frontier with
    | nil =>
        have impossible := realization.complete (realization.carry anchor)
        rw [frontierExact] at impossible
        exact nomatch impossible
    | cons head tail =>
        cases tail with
        | nil =>
            have leftMember := realization.complete (realization.carry left)
            have rightMember := realization.complete (realization.carry right)
            rw [frontierExact] at leftMember rightMember
            have leftExact : realization.carry left = head := by
              cases leftMember with
              | head => rfl
              | tail _ impossible => exact nomatch impossible
            have rightExact : realization.carry right = head := by
              cases rightMember with
              | head => rfl
              | tail _ impossible => exact nomatch impossible
            exact Eq.trans leftExact rightExact.symm
        | cons second rest =>
            rw [frontierExact] at widthExact
            have impossible : Nat.succ rest.length = Nat.zero :=
              Nat.succ.inj widthExact
            exact nomatch impossible
  · intro targetsConverge
    have carriesConverge :
        ∀ left right : source.Identity,
          realization.carry left = realization.carry right :=
      fun left right =>
        (realization.carry_eq_iff_target_eq left right).mpr
          (targetsConverge left right)
    cases frontierExact : realization.frontier with
    | nil =>
        have impossible := realization.complete (realization.carry anchor)
        rw [frontierExact] at impossible
        exact nomatch impossible
    | cons head tail =>
        cases tail with
        | nil => rfl
        | cons second rest =>
            let headPreimage := realization.carry_surjective head
            let secondPreimage := realization.carry_surjective second
            have headEqualsSecond : head = second :=
              Eq.trans headPreimage.exact.symm
                (Eq.trans
                  (carriesConverge
                    headPreimage.identity secondPreimage.identity)
                  secondPreimage.exact)
            have duplicate : head ∈ second :: rest :=
              headEqualsSecond ▸ List.Mem.head rest
            have noDuplicates := realization.nodup
            rw [frontierExact] at noDuplicates
            cases noDuplicates with
            | cons headAbsent _ =>
                exact False.elim
                  (headAbsent second (List.Mem.head rest) headEqualsSecond)

/-- Convergence constructs, rather than assumes, a one-obligation exact image. -/
def convergentExactTargetImageRealization
    (source : FiniteCarrier)
    {Target : Type}
    (target : source.Identity → Target)
    (anchor : source.Identity)
    (convergence : ConvergentExactTargetImage source target anchor) :
    ExactTargetImageRealization source target :=
  { Obligation := Unit
    decEq := fun _ _ => isTrue rfl
    frontier := [()]
    complete := fun obligation => by cases obligation; exact .head _
    nodup := .cons (fun _ impossible _ => nomatch impossible) .nil
    value := fun _ => target anchor
    value_injective := fun left right _ => by cases left; cases right; rfl
    carry := fun _ => ()
    carry_exact := fun identity => (convergence.targetConverges identity).symm
    carry_surjective := fun obligation => by
      cases obligation
      exact { identity := anchor, exact := rfl } }

/-- Unit is used only after target convergence has been constructed. -/
def convergentExactTargetRegime
    (source : FiniteCarrier)
    {Target : Type}
    (target : source.Identity → Target)
    (anchor : source.Identity)
    (_realization : ConvergentExactTargetImage source target anchor) :
    ObligationRegime source :=
  (convergentExactTargetImageRealization
    source target anchor _realization).toObligationRegime

/-- The projected regime has exactly the fibres of the convergent target map. -/
theorem convergentExactTargetRegime_carry_eq_iff_target_eq
    (source : FiniteCarrier)
    {Target : Type}
    (target : source.Identity → Target)
    (anchor : source.Identity)
    (realization : ConvergentExactTargetImage source target anchor)
    (left right : source.Identity) :
    (convergentExactTargetRegime
        source target anchor realization).carry left =
        (convergentExactTargetRegime
          source target anchor realization).carry right ↔
      target left = target right := by
  exact
    (convergentExactTargetImageRealization
      source target anchor realization).carry_eq_iff_target_eq left right

/-- Width one is read only after the convergence witness has been supplied. -/
theorem convergentExactTargetRegime_width_one
    (source : FiniteCarrier)
    {Target : Type}
    (target : source.Identity → Target)
    (anchor : source.Identity)
    (realization : ConvergentExactTargetImage source target anchor) :
    (convergentExactTargetRegime
      source target anchor realization).frontier.length = 1 :=
  by
    unfold convergentExactTargetRegime
    unfold ExactTargetImageRealization.toObligationRegime
    unfold convergentExactTargetImageRealization
    rfl

/--
The exact image is the singleton at the anchor exactly when all computed
targets converge.  Neither side is stored as a field of the other.
-/
theorem exactTargetImage_eq_singleton_iff_all_targets_equal
    (source : FiniteCarrier)
    {Target : Type}
    (targetDecEq : DecidableEq Target)
    (target : source.Identity → Target)
    (anchor : source.Identity) :
    exactTargetImageFrontier source targetDecEq target = [target anchor] ↔
      ∀ left right : source.Identity, target left = target right := by
  constructor
  · intro imageExact left right
    have leftMember :=
      exactTargetImageFrontier_complete source targetDecEq target left
    have rightMember :=
      exactTargetImageFrontier_complete source targetDecEq target right
    have leftFound :
        containsWith targetDecEq (target left)
          (exactTargetImageFrontier source targetDecEq target) = true :=
      (containsWith_eq_true_iff_mem targetDecEq (target left) _).mpr leftMember
    have rightFound :
        containsWith targetDecEq (target right)
          (exactTargetImageFrontier source targetDecEq target) = true :=
      (containsWith_eq_true_iff_mem targetDecEq (target right) _).mpr rightMember
    have leftSingleton :
        containsWith targetDecEq (target left) [target anchor] = true :=
      Eq.mp
        (congrArg
          (fun values => containsWith targetDecEq (target left) values = true)
          imageExact)
        leftFound
    have rightSingleton :
        containsWith targetDecEq (target right) [target anchor] = true :=
      Eq.mp
        (congrArg
          (fun values => containsWith targetDecEq (target right) values = true)
          imageExact)
        rightFound
    exact Eq.trans
      (containsWith_singleton_eq
        targetDecEq (target left) (target anchor) leftSingleton)
      (containsWith_singleton_eq
        targetDecEq (target right) (target anchor) rightSingleton).symm
  · intro allEqual
    have sourceNonempty : source.frontier ≠ [] :=
      list_ne_nil_of_mem (source.complete anchor)
    have imageNonempty : source.frontier.map target ≠ [] :=
      map_ne_nil target sourceNonempty
    have imageExact :
        exactTargetImageFrontier source targetDecEq target = [target anchor] := by
      apply deduplicate_eq_singleton_of_nonempty_of_all_eq targetDecEq
        (source.frontier.map target) (target anchor) imageNonempty
      intro value valueMember
      rcases Extensive.mem_map_preimage target valueMember with
        ⟨identity, _identityMember, identityExact⟩
      exact Eq.trans identityExact.symm (allEqual identity anchor)
    exact imageExact

/-- Convergence therefore gives the exact numeric width one readout. -/
theorem exactTargetImage_width_one_of_all_targets_equal
    (source : FiniteCarrier)
    {Target : Type}
    (targetDecEq : DecidableEq Target)
    (target : source.Identity → Target)
    (anchor : source.Identity)
    (allEqual : ∀ left right : source.Identity, target left = target right) :
    (exactTargetImageFrontier source targetDecEq target).length = 1 :=
  congrArg List.length
    ((exactTargetImage_eq_singleton_iff_all_targets_equal
      source targetDecEq target anchor).mpr allEqual)

end Extensive
end ConstitutiveSearch

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Extensive.deduplicate
#print axioms ConstitutiveSearch.Extensive.containsWith_eq_true_iff_mem
#print axioms ConstitutiveSearch.Extensive.mem_deduplicate_iff
#print axioms ConstitutiveSearch.Extensive.deduplicate_nodup
#print axioms ConstitutiveSearch.Extensive.deduplicate_eq_singleton_of_nonempty_of_all_eq
#print axioms ConstitutiveSearch.Extensive.containsWith_singleton_eq
#print axioms ConstitutiveSearch.Extensive.list_ne_nil_of_mem
#print axioms ConstitutiveSearch.Extensive.map_ne_nil
#print axioms ConstitutiveSearch.Extensive.exactTargetImageFrontier
#print axioms ConstitutiveSearch.Extensive.ConvergentExactTargetImage
#print axioms ConstitutiveSearch.Extensive.TargetImagePreimage
#print axioms ConstitutiveSearch.Extensive.ExactTargetImageRealization
#print axioms ConstitutiveSearch.Extensive.ExactTargetImageRealization.toObligationRegime
#print axioms ConstitutiveSearch.Extensive.ExactTargetImageRealization.carry_eq_iff_target_eq
#print axioms ConstitutiveSearch.Extensive.ExactTargetImageRealization.width_one_iff_all_targets_equal
#print axioms ConstitutiveSearch.Extensive.convergentExactTargetImageRealization
#print axioms ConstitutiveSearch.Extensive.convergentExactTargetRegime
#print axioms ConstitutiveSearch.Extensive.convergentExactTargetRegime_carry_eq_iff_target_eq
#print axioms ConstitutiveSearch.Extensive.convergentExactTargetRegime_width_one
#print axioms ConstitutiveSearch.Extensive.exactTargetImage_eq_singleton_iff_all_targets_equal
#print axioms ConstitutiveSearch.Extensive.exactTargetImage_width_one_of_all_targets_equal
/- AXIOM_AUDIT_END -/
