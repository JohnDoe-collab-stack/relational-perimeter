import Tests.LocalAlignment.DocumentaryControlBindings

/-! Paid traversal and construction of a received typed reference position.
The computed natural is supplied to permission search; equality is erased.
Computing the bootstrap bound remains separate from executing this code. -/
set_option genInjectivity false
set_option maxHeartbeats 3000000
namespace ConstitutiveSearch.Agent.Local.Documentary.ControlReference
open Resources Control ControlBindings
universe u

abbrev Position {Kind : Type u} {scope : List Kind} {kind : Kind} (ref : Ref scope kind) :=
  {position : Nat // position = ref.position}

def positionCode {Kind : Type u} {scope : List Kind} {kind : Kind} (ref : Ref scope kind) :
    Code Label (Position ref) :=
  .step .referencePosition (fun _ => match ref with
    | .here => .done ⟨0, rfl⟩
    | .prior before => (positionCode before).bind (fun actual =>
        .step .referenceReturn (fun _ => .done ⟨actual.1 + 1, congrArg Nat.succ actual.2⟩)))

def positionLabels {Kind : Type u} {scope : List Kind} {kind : Kind} : Ref scope kind → List Label
  | .here => [.referencePosition]
  | .prior before => .referencePosition :: (positionLabels before ++ [.referenceReturn])

def positionTrace {Kind : Type u} {scope : List Kind} {kind : Kind} (ref : Ref scope kind) :
    Eval (positionCode ref) (positionLabels ref) ⟨ref.position, rfl⟩ :=
  match ref with
  | .here => .step .done
  | .prior before => .step ((positionTrace before).bind (.step .done))

def positionBound {Kind : Type u} {scope : List Kind} {kind : Kind} : Ref scope kind → Nat
  | .here => 1
  | .prior before => (positionBound before + 1) + 1

theorem position_labels_bound {Kind : Type u} {scope : List Kind} {kind : Kind} (ref : Ref scope kind) :
    (positionLabels ref).length = positionBound ref := by
  induction ref with
  | here => rfl
  | prior before rest =>
      exact congrArg Nat.succ ((labels_append_length (positionLabels before) [_]).trans
        (congrArg (fun cost => cost + 1) rest))

theorem position_bounded {Kind : Type u} {scope : List Kind} {kind : Kind} (ref : Ref scope kind) :
    Within (positionCode ref) (positionBound ref) :=
  ⟨_, _, ⟨positionTrace ref⟩, (position_labels_bound ref).symm ▸ Nat.le_refl _⟩

theorem position_short {Kind : Type u} {scope : List Kind} {kind : Kind} (ref : Ref scope kind)
    (fuel : Nat) (short : fuel < positionBound ref) : runCtl fuel (positionCode ref) = none :=
  fuel_short (positionTrace ref) fuel ((position_labels_bound ref).symm ▸ short)

end ConstitutiveSearch.Agent.Local.Documentary.ControlReference

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlReference.Position
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlReference.positionCode
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlReference.positionLabels
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlReference.positionTrace
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlReference.positionBound
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlReference.position_labels_bound
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlReference.position_bounded
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlReference.position_short
/- AXIOM_AUDIT_END -/
