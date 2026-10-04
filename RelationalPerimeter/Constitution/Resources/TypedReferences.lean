/-!
# Typed references into an already constituted resource context

Kinds and their value family are an explicit interface. References distinguish
occurrences, even when the values read at two occurrences agree. The concrete
producer must instantiate the family with its dependent operational indices.
-/
set_option genInjectivity false
namespace ConstitutiveSearch.Resources
universe u v

inductive Ref {Kind : Type u} : List Kind → Kind → Type u where
  | here {kind rest} : Ref (kind :: rest) kind
  | prior {kind added rest} : Ref rest kind → Ref (added :: rest) kind

def Values {Kind : Type u} (Value : Kind → Type v) : List Kind → Type (max u v)
  | [] => PUnit
  | kind :: rest => Value kind × Values Value rest

def read {Kind : Type u} {Value : Kind → Type v} :
    {context : List Kind} → {kind : Kind} →
      Values Value context → Ref context kind → Value kind
  | _, _, values, .here => values.1
  | _, _, values, .prior ref => read values.2 ref

inductive Ports {Kind : Type u} (context : List Kind) : List Kind → Type u where
  | nil : Ports context []
  | cons {kind rest} : Ref context kind → Ports context rest → Ports context (kind :: rest)

def Ports.read {Kind : Type u} {Value : Kind → Type v} {context : List Kind} :
    {kinds : List Kind} → Ports context kinds → Values Value context → Values Value kinds
  | _, .nil, _ => PUnit.unit
  | _, .cons ref rest, values => (Resources.read values ref, rest.read values)

def Ref.position {Kind : Type u} : {context : List Kind} → {kind : Kind} → Ref context kind → Nat
  | _, _, .here => 0
  | _, _, .prior ref => ref.position + 1

theorem read_prior {Kind : Type u} {Value : Kind → Type v}
    {context : List Kind} {kind added : Kind}
    (values : Values Value context) (newValue : Value added) (ref : Ref context kind) :
    read (Value := Value) (context := added :: context) (newValue, values) (.prior ref) =
      read values ref := rfl

theorem prior_injective {Kind : Type u} {context : List Kind} {kind added : Kind}
    (first second : Ref context kind)
    (same : (Ref.prior first : Ref (added :: context) kind) = .prior second) :
    first = second := by
  cases same
  rfl

theorem fresh_position_distinct {Kind : Type u} {context : List Kind} {kind : Kind}
    (old : Ref context kind) :
    (Ref.here : Ref (kind :: context) kind).position ≠
      (Ref.prior old : Ref (kind :: context) kind).position := by
  intro same
  exact Nat.noConfusion same

end ConstitutiveSearch.Resources
/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Resources.Ref
#print axioms ConstitutiveSearch.Resources.Values
#print axioms ConstitutiveSearch.Resources.read
#print axioms ConstitutiveSearch.Resources.Ports.read
#print axioms ConstitutiveSearch.Resources.Ref.position
#print axioms ConstitutiveSearch.Resources.read_prior
#print axioms ConstitutiveSearch.Resources.prior_injective
#print axioms ConstitutiveSearch.Resources.fresh_position_distinct
/- AXIOM_AUDIT_END -/
