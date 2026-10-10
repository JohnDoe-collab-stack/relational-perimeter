import Tests.LocalAlignment.DocumentaryControlBindings

/-! Traverse the actual typed resource values before formation. A paid cell
returns its stored value; equal values never replace their received references. -/
set_option genInjectivity false
set_option maxHeartbeats 3000000
namespace ConstitutiveSearch.Agent.Local.Documentary.ControlResources
open Resources Control ControlBindings
universe u v
variable {Kind : Type u} {Value : Kind → Type v}

abbrev Read {kinds : List Kind} {kind : Kind}
    (values : Values Value kinds) (ref : Ref kinds kind) :=
  {found : Value kind // found = Resources.read values ref}

def readCode {kinds : List Kind} {kind : Kind}
    (values : Values Value kinds) (ref : Ref kinds kind) : Code Label (Read values ref) :=
  .step .resourceCell (fun _ => match kinds, ref with
    | _ :: _, .here => .done ⟨values.1, rfl⟩
    | _ :: _, .prior before => readCode values.2 before)

def readTrace {kinds : List Kind} {kind : Kind}
    (values : Values Value kinds) (ref : Ref kinds kind) :
    Eval (readCode values ref) (List.replicate (ref.position + 1) .resourceCell)
      ⟨Resources.read values ref, rfl⟩ :=
  match kinds, ref with
  | _ :: _, .here => .step .done
  | _ :: _, .prior before => .step (readTrace values.2 before)

theorem labels_length (count : Nat) :
    (List.replicate count Label.resourceCell).length = count := by
  induction count with
  | zero => rfl
  | succ count previous => exact congrArg Nat.succ previous

theorem read_bounded {kinds : List Kind} {kind : Kind}
    (values : Values Value kinds) (ref : Ref kinds kind) :
    Within (readCode values ref) (ref.position + 1) :=
  ⟨_, _, ⟨readTrace values ref⟩, by rw [labels_length]; exact Nat.le_refl _⟩

theorem read_within {kinds : List Kind} {kind : Kind}
    (values : Values Value kinds) (ref : Ref kinds kind) (fuel : Nat)
    (enough : ref.position + 1 ≤ fuel) :
    runCtl fuel (readCode values ref) =
      some (⟨Resources.read values ref, rfl⟩, List.replicate (ref.position + 1) .resourceCell) :=
  ctl_complete (readTrace values ref) fuel (by rw [labels_length]; exact enough)

theorem read_short {kinds : List Kind} {kind : Kind}
    (values : Values Value kinds) (ref : Ref kinds kind) (fuel : Nat)
    (short : fuel < ref.position + 1) : runCtl fuel (readCode values ref) = none :=
  fuel_short (readTrace values ref) fuel (by rw [labels_length]; exact short)

end ConstitutiveSearch.Agent.Local.Documentary.ControlResources

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlResources.Read
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlResources.readCode
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlResources.readTrace
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlResources.labels_length
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlResources.read_bounded
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlResources.read_within
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlResources.read_short
/- AXIOM_AUDIT_END -/
