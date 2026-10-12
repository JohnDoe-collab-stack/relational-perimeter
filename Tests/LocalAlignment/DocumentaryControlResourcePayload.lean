import Tests.LocalAlignment.DocumentaryControlConstitutiveResources

/-! Retain executable payloads alongside the same original produced resource.
Arguments, kind, operation and formation are evaluated once. -/
set_option genInjectivity false
set_option backward.match.sparseCases false
set_option maxHeartbeats 8000000
namespace ConstitutiveSearch.Agent.Local.Documentary.ControlResourcePayload
open Resources Control ControlBindings ControlConstitutiveResources
universe u v w
variable {Kind : Type u} {Value : Kind → Type v}

structure OperationPayload {context : List Kind} (producer : Producer Value context)
    (payload : (args : Values Value producer.inputKinds) → Value (producer.outputKind args) → Type w)
    (args : Values Value producer.inputKinds) where
  produced : Operation producer args
  execution : payload args produced.1

structure CachedPayload {context : List Kind} (support : Support Value context)
    (producer : Producer Value context)
    (payload : (args : Values Value producer.inputKinds) → Value (producer.outputKind args) → Type w) where
  cached : Cached support producer
  produced : Operation producer cached.args.1
  execution : payload cached.args.1 produced.1

def valuesFromParts {context : List Kind} (support : Support Value context)
    (producer : Producer Value context) (args : Arguments producer.inputs support.values)
    (kind : {kind : Kind // kind = producer.outputKind args.1}) (computed : Operation producer args.1) :
    Values Value (kind.1 :: context) :=
  (Eq.rec (motive := fun k _ => Value k) computed.1 kind.2.symm, support.values)

def formationFromParts {context : List Kind} (support : Support Value context)
    (producer : Producer Value context) (args : Arguments producer.inputs support.values)
    (kind : {kind : Kind // kind = producer.outputKind args.1}) (computed : Operation producer args.1) :
    Formation Value (valuesFromParts support producer args kind computed) := by
  obtain ⟨_, sameKind⟩ := kind; cases sameKind
  obtain ⟨_, sameArgs⟩ := args; cases sameArgs
  obtain ⟨_, sameValue⟩ := computed; cases sameValue
  exact .produced support.formation producer

theorem support_from_parts_actual {context : List Kind} (support : Support Value context)
    (producer : Producer Value context) (args : Arguments producer.inputs support.values)
    (kind : {kind : Kind // kind = producer.outputKind args.1}) (computed : Operation producer args.1) :
    HEq (Support.mk (valuesFromParts support producer args kind computed)
      (formationFromParts support producer args kind computed)) (support.extend producer) := by
  obtain ⟨_, sameKind⟩ := kind; cases sameKind
  obtain ⟨_, sameArgs⟩ := args; cases sameArgs
  obtain ⟨_, sameValue⟩ := computed; cases sameValue; rfl

def code {context : List Kind} (support : Support Value context)
    (producer : Producer Value context)
    (payload : (args : Values Value producer.inputKinds) → Value (producer.outputKind args) → Type w)
    (kindCode : (args : Values Value producer.inputKinds) →
      Code Label {kind : Kind // kind = producer.outputKind args})
    (operation : (args : Values Value producer.inputKinds) → Code Label (OperationPayload producer payload args)) :
    Code Label (CachedPayload support producer payload) :=
  (argumentsCode producer.inputs support.values).bind (fun args =>
    (kindCode args.1).bind (fun kind =>
      (operation args.1).bind (fun computed =>
        .step .formationValues (fun _ =>
          let value : Value kind.1 := Eq.rec
            (motive := fun k _ => Value k) computed.produced.1 kind.2.symm
          let values : Values Value (kind.1 :: context) := (value, support.values)
          .step .formationWitness (fun _ =>
            let formation : Formation Value values :=
              formationFromParts support producer args kind computed.produced
            .step .formationResources (fun _ =>
              let cached : Cached support producer :=
                ⟨args, kind.1, kind.2, ⟨values, formation⟩,
                  support_from_parts_actual support producer args kind computed.produced⟩
              .step .executionPayload (fun _ => .done
                ⟨cached, computed.produced, computed.execution⟩)))))))

theorem finite {context : List Kind} (support : Support Value context)
    (producer : Producer Value context)
    (payload : (args : Values Value producer.inputKinds) → Value (producer.outputKind args) → Type w)
    (kindCode : (args : Values Value producer.inputKinds) →
      Code Label {kind : Kind // kind = producer.outputKind args})
    (operation : (args : Values Value producer.inputKinds) → Code Label (OperationPayload producer payload args))
    (kinds : ∀ args, Finite (kindCode args)) (operations : ∀ args, Finite (operation args)) :
    Finite (code support producer payload kindCode operation) := by
  apply finite_bind
  · obtain ⟨value, labels, trace, _⟩ := arguments_bounded _ _
    exact ⟨value, labels, trace⟩
  · intro args
    apply finite_bind (kinds args.1); intro kind
    apply finite_bind (operations args.1); intro computed
    apply finite_step; apply finite_step; apply finite_step; apply finite_step; exact finite_done _

end ConstitutiveSearch.Agent.Local.Documentary.ControlResourcePayload

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlResourcePayload.OperationPayload
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlResourcePayload.CachedPayload
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlResourcePayload.valuesFromParts
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlResourcePayload.formationFromParts
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlResourcePayload.support_from_parts_actual
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlResourcePayload.code
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlResourcePayload.finite
/- AXIOM_AUDIT_END -/
