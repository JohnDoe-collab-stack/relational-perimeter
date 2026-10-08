import RelationalPerimeter.Relativity.Production.ConstitutedEvents

/-!
# Constructed admission at the current resource boundary

Numerical request addresses select typed occurrences; they are not positions
in spacetime. Resolution returns a positive reference with its exact address,
or refutes that reference. No completed future or admission oracle is received.
The candidate's calibration law is already enforced by the resource type.
-/
set_option genInjectivity false
namespace RelationalPerimeter.Relativity.Production
open ConstitutiveSearch.Resources

def kindDecision (one two : Kind) : Decidable (one = two) := by
  cases one <;> cases two <;> first
    | exact .isTrue rfl
    | exact .isFalse (fun same => Kind.noConfusion same)

structure ReferenceAt (context : List Kind) (kind : Kind) (position : Nat) where
  ref : Ref context kind
  exactPosition : ref.position = position

theorem reference_position_injective {context : List Kind} {kind}
    (one : Ref context kind) : (two : Ref context kind) →
      one.position = two.position → one = two := by
  induction one with
  | here =>
    intro two same
    cases two with
    | here => rfl
    | prior old => exact False.elim (Nat.noConfusion same)
  | prior old ih =>
    intro two same
    cases two with
    | here => exact False.elim (Nat.noConfusion same)
    | prior other => exact congrArg Ref.prior (ih other (Nat.succ.inj same))

def resolve : (context : List Kind) → (kind : Kind) → (position : Nat) →
    PSum (ReferenceAt context kind position) (ReferenceAt context kind position → False)
  | [], _, _ => .inr (fun located => nomatch located.ref)
  | added :: rest, kind, 0 =>
    match kindDecision added kind with
    | .isTrue same => by cases same; exact .inl ⟨.here, rfl⟩
    | .isFalse distinct => .inr (fun located => by
        cases located with
        | mk ref exactPosition =>
          cases ref with
          | here => exact distinct rfl
          | prior old => exact Nat.noConfusion exactPosition)
  | _added :: rest, kind, position + 1 =>
    match resolve rest kind position with
    | .inl located => .inl ⟨.prior located.ref, congrArg (fun n => n + 1) located.exactPosition⟩
    | .inr impossible => .inr (fun located => by
        cases located with
        | mk ref exactPosition =>
          cases ref with
          | here => exact Nat.noConfusion exactPosition
          | prior old => exact impossible ⟨old, Nat.succ.inj exactPosition⟩)
termination_by structural context _kind _position => context

def pairDecision {A B : Type} (one : PSum A (A → False)) (two : PSum B (B → False)) :
    PSum (A × B) (A × B → False) :=
  match one, two with
  | .inl first, .inl second => .inl (first, second)
  | .inr impossible, _ => .inr (fun pair => impossible pair.1)
  | .inl _, .inr impossible => .inr (fun pair => impossible pair.2)

inductive LocalRequest where
  | emit (reading payload : Nat)
  | relay (signal calibration : Nat)
  | receive (signal : Nat)
  | inspect (kind : Kind) (position : Nat)

def LocalAdmission (source : Cursor) : LocalRequest → Type
  | .emit reading payload =>
      ReferenceAt source.kinds .reading reading × ReferenceAt source.kinds .payload payload
  | .relay signal calibration =>
      ReferenceAt source.kinds .signal signal × ReferenceAt source.kinds .calibration calibration
  | .receive signal => ReferenceAt source.kinds .signal signal
  | .inspect kind position => ReferenceAt source.kinds kind position

def decideAdmission (source : Cursor) (request : LocalRequest) :
    PSum (LocalAdmission source request) (LocalAdmission source request → False) :=
  match request with
  | .emit reading payload => pairDecision (resolve source.kinds .reading reading)
      (resolve source.kinds .payload payload)
  | .relay signal calibration => pairDecision (resolve source.kinds .signal signal)
      (resolve source.kinds .calibration calibration)
  | .receive signal => resolve source.kinds .signal signal
  | .inspect kind position => resolve source.kinds kind position

def admissionEnabled (source : Cursor) (request : LocalRequest) : Bool :=
  match decideAdmission source request with
  | .inl _ => true
  | .inr _ => false

def admissionOfEnabled (source : Cursor) (request : LocalRequest)
    (yes : admissionEnabled source request = true) : LocalAdmission source request := by
  cases chosen : decideAdmission source request with
  | inl admitted => exact admitted
  | inr impossible =>
    change (match decideAdmission source request with | .inl _ => true | .inr _ => false) = true at yes
    rw [chosen] at yes
    cases yes

theorem refusal_refutes_admission (source : Cursor) (request : LocalRequest)
    (no : admissionEnabled source request = false) (admitted : LocalAdmission source request) : False := by
  cases chosen : decideAdmission source request with
  | inl witness =>
    change (match decideAdmission source request with | .inl _ => true | .inr _ => false) = false at no
    rw [chosen] at no
    cases no
  | inr impossible => exact impossible admitted

end RelationalPerimeter.Relativity.Production
/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Relativity.Production.kindDecision
#print axioms RelationalPerimeter.Relativity.Production.ReferenceAt
#print axioms RelationalPerimeter.Relativity.Production.reference_position_injective
#print axioms RelationalPerimeter.Relativity.Production.resolve
#print axioms RelationalPerimeter.Relativity.Production.pairDecision
#print axioms RelationalPerimeter.Relativity.Production.LocalAdmission
#print axioms RelationalPerimeter.Relativity.Production.decideAdmission
#print axioms RelationalPerimeter.Relativity.Production.admissionEnabled
#print axioms RelationalPerimeter.Relativity.Production.admissionOfEnabled
#print axioms RelationalPerimeter.Relativity.Production.refusal_refutes_admission
/- AXIOM_AUDIT_END -/
