import Tests.LocalAlignment.DocumentaryControlReference

/-! Actual permission lookup with paid structural natural comparisons,
visited list cells and returned reference construction. Search retains the
first received occurrence, including when the list contains equal entries. -/
set_option genInjectivity false
set_option maxHeartbeats 3000000
namespace ConstitutiveSearch.Agent.Local.Documentary.ControlPermission
open Resources Control ControlBindings

def successorDecision {left right : Nat} : Decidable (left = right) →
    Decidable (left + 1 = right + 1)
  | .isTrue same => .isTrue (congrArg Nat.succ same)
  | .isFalse different => .isFalse (fun same => different (Nat.succ.inj same))

def equalDecision : (left right : Nat) → Decidable (left = right)
  | 0, 0 => .isTrue rfl
  | 0, _ + 1 => .isFalse (fun same => Nat.noConfusion same)
  | _ + 1, 0 => .isFalse (fun same => Nat.noConfusion same)
  | left + 1, right + 1 => successorDecision (equalDecision left right)

def equalCode (left right : Nat) : Code Label (Decidable (left = right)) :=
  .step .naturalComparison (fun _ => match left, right with
    | 0, 0 => .done (.isTrue rfl)
    | 0, _ + 1 => .done (.isFalse (fun same => Nat.noConfusion same))
    | _ + 1, 0 => .done (.isFalse (fun same => Nat.noConfusion same))
    | left + 1, right + 1 => (equalCode left right).bind
        (fun found => .done (successorDecision found)))

def equalLabels : Nat → Nat → List Label
  | 0, _ => [.naturalComparison]
  | _ + 1, 0 => [.naturalComparison]
  | left + 1, right + 1 => .naturalComparison :: equalLabels left right

theorem labels_append_nil (labels : List Label) : labels ++ [] = labels := by
  induction labels with
  | nil => rfl
  | cons head tail rest => exact congrArg (List.cons head) rest

def equalTrace (left right : Nat) :
    Eval (equalCode left right) (equalLabels left right) (equalDecision left right) :=
  match left, right with
  | 0, 0 => .step .done
  | 0, _ + 1 => .step .done
  | _ + 1, 0 => .step .done
  | left + 1, right + 1 => by
      apply Eval.step
      have trace := (equalTrace left right).bind
        (continuation := fun found => .done (successorDecision found))
        (secondLabels := []) Eval.done
      exact labels_append_nil (equalLabels left right) ▸ trace

abbrev Lookup (scope : List Nat) (position : Nat) :=
  {found : Option (Ref scope position) // found = resolvePermission scope position}

def present {head position : Nat} (tail : List Nat) (same : head = position) :
    Lookup (head :: tail) position :=
  ⟨some (same ▸ Ref.here), by
    unfold resolvePermission
    split
    · rfl
    · rename_i different
      exact False.elim (different same)⟩

def previous {head position : Nat} (tail : List Nat) (different : head ≠ position)
    (actual : Lookup tail position) : Lookup (head :: tail) position :=
  ⟨actual.1.map Ref.prior, by
    unfold resolvePermission
    split
    · rename_i same
      exact False.elim (different same)
    · exact congrArg (fun (found : Option (Ref tail position)) =>
        found.map (fun ref => (Ref.prior ref : Ref (head :: tail) position))) actual.2⟩

def lookupCode (scope : List Nat) (position : Nat) : Code Label (Lookup scope position) :=
  .step .permissionCell (fun _ => match scope with
    | [] => .done ⟨none, rfl⟩
    | head :: tail => (equalCode head position).bind (fun decision => match decision with
        | .isTrue same => .step .permissionReturn (fun _ => .done (present tail same))
        | .isFalse different => (lookupCode tail position).bind (fun actual =>
            .step .permissionReturn (fun _ => .done (previous tail different actual)))))

theorem lookup_finite (scope : List Nat) (position : Nat) : Finite (lookupCode scope position) := by
  induction scope with
  | nil => exact finite_step _ _ (finite_done _)
  | cons head tail rest =>
      apply finite_step
      apply finite_bind ⟨_, _, ⟨equalTrace head position⟩⟩
      intro decision
      cases decision with
      | isTrue same => exact finite_step _ _ (finite_done _)
      | isFalse different =>
          apply finite_bind rest
          intro actual
          exact finite_step _ _ (finite_done _)

theorem equal_within (left right fuel : Nat) (enough : (equalLabels left right).length ≤ fuel) :
    runCtl fuel (equalCode left right) = some (equalDecision left right, equalLabels left right) :=
  ctl_complete (equalTrace left right) fuel enough

theorem equal_short (left right fuel : Nat) (short : fuel < (equalLabels left right).length) :
    runCtl fuel (equalCode left right) = none := fuel_short (equalTrace left right) fuel short

def lookupBound : List Nat → Nat → Nat
  | [], _ => 1
  | head :: tail, position =>
      ((equalLabels head position).length + (lookupBound tail position + 1)) + 1

theorem lookup_bounded (scope : List Nat) (position : Nat) :
    Within (lookupCode scope position) (lookupBound scope position) := by
  induction scope with
  | nil => exact within_step _ _ (within_done _)
  | cons head tail rest =>
      apply within_step
      apply within_bind ⟨_, _, ⟨equalTrace head position⟩, Nat.le_refl _⟩
      intro decision
      cases decision with
      | isTrue same =>
          exact within_weaken (within_step _ _ (within_done _))
            (Nat.succ_le_succ (Nat.zero_le _))
      | isFalse different =>
          apply within_bind rest
          intro actual
          exact within_step _ _ (within_done _)

theorem lookup_within (scope : List Nat) (position : Nat) :
    ∃ (value : Lookup scope position) (labels : List Label),
      runCtl (lookupBound scope position) (lookupCode scope position) = some (value, labels) :=
  within_complete (lookup_bounded scope position)

def referencedLookup {Kind : Type u} {kinds : List Kind} {kind : Kind}
    (scope : List Nat) (ref : Ref kinds kind) : Code Label (Lookup scope ref.position) :=
  (ControlReference.positionCode ref).bind (fun actual =>
    (lookupCode scope actual.1).bind (fun permission => .done (actual.2 ▸ permission)))

abbrev LocatedLookup {Kind : Type u} {kinds : List Kind} {kind : Kind}
    (scope : List Nat) (ref : Ref kinds kind) :=
  ControlReference.Position ref × Lookup scope ref.position

/-- Retain the paid position together with the permission for later formation. -/
def locatedLookup {Kind : Type u} {kinds : List Kind} {kind : Kind}
    (scope : List Nat) (ref : Ref kinds kind) : Code Label (LocatedLookup scope ref) :=
  (ControlReference.positionCode ref).bind (fun actual =>
    (lookupCode scope actual.1).bind (fun permission => .done (actual, actual.2 ▸ permission)))

theorem located_bounded {Kind : Type u} {kinds : List Kind} {kind : Kind}
    (scope : List Nat) (ref : Ref kinds kind) :
    Within (locatedLookup scope ref)
      (ControlReference.positionBound ref + lookupBound scope ref.position) := by
  apply within_bind (ControlReference.position_bounded ref)
  intro actual
  obtain ⟨position, same⟩ := actual
  cases same
  apply within_bind (more := 0) (lookup_bounded scope ref.position)
  intro permission
  exact within_done _

theorem located_finite {Kind : Type u} {kinds : List Kind} {kind : Kind}
    (scope : List Nat) (ref : Ref kinds kind) : Finite (locatedLookup scope ref) := by
  obtain ⟨value, labels, trace, _⟩ := located_bounded scope ref
  exact ⟨value, labels, trace⟩

theorem referenced_bounded {Kind : Type u} {kinds : List Kind} {kind : Kind}
    (scope : List Nat) (ref : Ref kinds kind) :
    Within (referencedLookup scope ref)
      (ControlReference.positionBound ref + lookupBound scope ref.position) := by
  apply within_bind (ControlReference.position_bounded ref)
  intro actual
  obtain ⟨position, same⟩ := actual
  cases same
  apply within_bind (more := 0) (lookup_bounded scope ref.position)
  intro permission
  exact within_done _

theorem referenced_finite {Kind : Type u} {kinds : List Kind} {kind : Kind}
    (scope : List Nat) (ref : Ref kinds kind) : Finite (referencedLookup scope ref) := by
  obtain ⟨value, labels, trace, _⟩ := referenced_bounded scope ref
  exact ⟨value, labels, trace⟩

end ConstitutiveSearch.Agent.Local.Documentary.ControlPermission

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlPermission.LocatedLookup
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlPermission.locatedLookup
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlPermission.located_bounded
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlPermission.located_finite
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlPermission.successorDecision
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlPermission.equalDecision
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlPermission.equalCode
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlPermission.equalLabels
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlPermission.labels_append_nil
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlPermission.equalTrace
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlPermission.Lookup
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlPermission.present
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlPermission.previous
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlPermission.lookupCode
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlPermission.lookup_finite
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlPermission.equal_within
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlPermission.equal_short
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlPermission.lookupBound
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlPermission.lookup_bounded
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlPermission.lookup_within
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlPermission.referencedLookup
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlPermission.referenced_bounded
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlPermission.referenced_finite
/- AXIOM_AUDIT_END -/
