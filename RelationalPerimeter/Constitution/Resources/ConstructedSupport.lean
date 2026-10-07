import RelationalPerimeter.Constitution.Resources.TypedReferences

/-!
# Dependent resource production from earlier typed references

A producer computes both the kind of its output and its value from the values
read at its input occurrences. Formation records that evaluation, rather than
an independently supplied output with a retrospective provenance label.
-/
set_option genInjectivity false
namespace ConstitutiveSearch.Resources
universe u v

structure Producer {Kind : Type u} (Value : Kind → Type v)
    (context : List Kind) where
  inputKinds : List Kind
  inputs : Ports context inputKinds
  outputKind : Values Value inputKinds → Kind
  operation : (arguments : Values Value inputKinds) → Value (outputKind arguments)

def Producer.arguments {Kind : Type u} {Value : Kind → Type v}
    {context : List Kind} (producer : Producer Value context)
    (values : Values Value context) := producer.inputs.read values

inductive Formation {Kind : Type u} (Value : Kind → Type v) :
    {context : List Kind} → Values Value context → Type (max u v) where
  | given {context} (values : Values Value context) : Formation Value values
  | produced {context} {values : Values Value context}
      (prior : Formation Value values) (producer : Producer Value context) :
      Formation Value (context := producer.outputKind (producer.arguments values) :: context)
        (producer.operation (producer.arguments values), values)

structure Support {Kind : Type u} (Value : Kind → Type v) (context : List Kind) where
  values : Values Value context
  formation : Formation Value values

def Support.kinds {Kind : Type u} {Value : Kind → Type v} {context : List Kind}
    (_support : Support Value context) : List Kind := context

def Support.given {Kind : Type u} {Value : Kind → Type v} {context : List Kind}
    (values : Values Value context) : Support Value context := ⟨values, .given values⟩

def Support.extend {Kind : Type u} {Value : Kind → Type v} {context : List Kind}
    (support : Support Value context) (producer : Producer Value context) :
    Support Value (producer.outputKind (producer.arguments support.values) :: context) :=
  ⟨(producer.operation (producer.arguments support.values), support.values),
    .produced support.formation producer⟩

def Support.read {Kind : Type u} {Value : Kind → Type v}
    {context : List Kind} (support : Support Value context) {kind : Kind}
    (ref : Ref context kind) : Value kind := Resources.read support.values ref

theorem produced_value {Kind : Type u} {Value : Kind → Type v}
    {context : List Kind} (support : Support Value context)
    (producer : Producer Value context) :
    (support.extend producer).read .here = producer.operation (producer.arguments support.values) := rfl

theorem produced_preserves {Kind : Type u} {Value : Kind → Type v}
    {context : List Kind} {kind : Kind} (support : Support Value context)
    (producer : Producer Value context) (ref : Ref context kind) :
    (support.extend producer).read (.prior ref) = support.read ref := rfl

/-- A constructed transport of old occurrences into an actually extended
support. Sort, occurrence distinction and evaluation are preserved separately. -/
structure Support.Extension {Kind : Type u} {Value : Kind → Type v}
    {oldKinds newKinds : List Kind} (old : Support Value oldKinds)
    (new : Support Value newKinds) where
  references : {kind : Kind} → Ref oldKinds kind → Ref newKinds kind
  reads : ∀ {kind} (ref : Ref oldKinds kind), new.read (references ref) = old.read ref
  injective : ∀ {kind} (a b : Ref oldKinds kind), references a = references b → a = b
  added : Nat
  positions : ∀ {kind} (ref : Ref oldKinds kind), (references ref).position = ref.position + added

namespace Support.Extension
variable {Kind : Type u} {Value : Kind → Type v}
  {firstKinds middleKinds lastKinds : List Kind}
  {first : Support Value firstKinds} {middle : Support Value middleKinds}
  {last : Support Value lastKinds}

def identity (support : Support Value firstKinds) : Extension support support :=
  ⟨id, fun _ => rfl, fun _ _ same => same, 0, fun _ => rfl⟩

def produced (support : Support Value firstKinds) (producer : Producer Value firstKinds) :
    Extension support (support.extend producer) :=
  ⟨Ref.prior, fun _ => rfl, prior_injective, 1, fun _ => rfl⟩

def compose (one : Extension first middle) (two : Extension middle last) : Extension first last where
  references := fun ref => two.references (one.references ref)
  reads := fun ref => (two.reads (one.references ref)).trans (one.reads ref)
  injective := fun a b same => one.injective a b (two.injective _ _ same)
  added := one.added + two.added
  positions := fun ref => by rw [two.positions, one.positions, Nat.add_assoc]

theorem references_compose (one : Extension first middle) (two : Extension middle last)
    {kind : Kind} (ref : Ref firstKinds kind) :
    (one.compose two).references ref = two.references (one.references ref) := rfl

theorem reads_compose (one : Extension first middle) (two : Extension middle last)
    {kind : Kind} (ref : Ref firstKinds kind) :
    last.read ((one.compose two).references ref) = first.read ref :=
  (one.compose two).reads ref
end Support.Extension

end ConstitutiveSearch.Resources
/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Resources.Producer
#print axioms ConstitutiveSearch.Resources.Producer.arguments
#print axioms ConstitutiveSearch.Resources.Formation
#print axioms ConstitutiveSearch.Resources.Support
#print axioms ConstitutiveSearch.Resources.Support.kinds
#print axioms ConstitutiveSearch.Resources.Support.given
#print axioms ConstitutiveSearch.Resources.Support.extend
#print axioms ConstitutiveSearch.Resources.Support.read
#print axioms ConstitutiveSearch.Resources.produced_value
#print axioms ConstitutiveSearch.Resources.produced_preserves
#print axioms ConstitutiveSearch.Resources.Support.Extension
#print axioms ConstitutiveSearch.Resources.Support.Extension.identity
#print axioms ConstitutiveSearch.Resources.Support.Extension.produced
#print axioms ConstitutiveSearch.Resources.Support.Extension.compose
#print axioms ConstitutiveSearch.Resources.Support.Extension.references_compose
#print axioms ConstitutiveSearch.Resources.Support.Extension.reads_compose
/- AXIOM_AUDIT_END -/
