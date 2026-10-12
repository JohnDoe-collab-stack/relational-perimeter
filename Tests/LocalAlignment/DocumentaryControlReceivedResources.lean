import Tests.LocalAlignment.DocumentaryControlConstitutiveResources

/-! Preserve the actually paid argument receipt for a deferred operation. -/
set_option genInjectivity false
namespace ConstitutiveSearch.Agent.Local.Documentary.ControlReceivedResources
open Resources Control ControlBindings ControlConstitutiveResources
universe u v
variable {Kind : Type u} {Value : Kind → Type v}

def code {context : List Kind} (support : Support Value context)
    (producer : Producer Value context)
    (kindCode : (args : Values Value producer.inputKinds) →
      Code Label {kind : Kind // kind = producer.outputKind args})
    (operation : (args : Arguments producer.inputs support.values) → Code Label (Operation producer args.1)) :
    Code Label (Cached support producer) :=
  (argumentsCode producer.inputs support.values).bind (fun args =>
    (kindCode args.1).bind (fun kind =>
      (operation args).bind (fun computed =>
        .step .formationValues (fun _ =>
          let value : Value kind.1 := Eq.rec
            (motive := fun k _ => Value k) computed.1 kind.2.symm
          let values : Values Value (kind.1 :: context) := (value, support.values)
          .step .formationWitness (fun _ =>
            let formation : Formation Value values := by
              obtain ⟨_, sameKind⟩ := kind; cases sameKind
              obtain ⟨_, sameArgs⟩ := args; cases sameArgs
              obtain ⟨_, sameValue⟩ := computed; cases sameValue
              exact .produced support.formation producer
            .step .formationResources (fun _ => .done
              ⟨args, kind.1, kind.2, ⟨values, formation⟩, by
                obtain ⟨_, sameKind⟩ := kind; cases sameKind
                obtain ⟨_, sameArgs⟩ := args; cases sameArgs
                obtain ⟨_, sameValue⟩ := computed; cases sameValue; rfl⟩))))))

theorem bounded {context : List Kind} (support : Support Value context)
    (producer : Producer Value context)
    (kindCode : (args : Values Value producer.inputKinds) →
      Code Label {kind : Kind // kind = producer.outputKind args})
    (operation : (args : Arguments producer.inputs support.values) → Code Label (Operation producer args.1))
    (kindBound operationBound : Nat)
    (kinds : ∀ args, Within (kindCode args) kindBound)
    (operations : ∀ args, Within (operation args) operationBound) :
    Within (code support producer kindCode operation)
      (argumentsBound producer.inputs + (kindBound + (operationBound + 3))) := by
  apply within_bind (arguments_bounded _ _); intro args
  apply within_bind (kinds args.1); intro kind
  apply within_bind (operations args); intro computed
  apply within_step; apply within_step; apply within_step
  exact within_done _

theorem finite {context : List Kind} (support : Support Value context)
    (producer : Producer Value context)
    (kindCode : (args : Values Value producer.inputKinds) →
      Code Label {kind : Kind // kind = producer.outputKind args})
    (operation : (args : Arguments producer.inputs support.values) → Code Label (Operation producer args.1))
    (kinds : ∀ args, Finite (kindCode args))
    (operations : ∀ args, Finite (operation args)) :
    Finite (code support producer kindCode operation) := by
  apply finite_bind
  · obtain ⟨value, labels, trace, _⟩ := arguments_bounded _ _
    exact ⟨value, labels, trace⟩
  · intro args
    apply finite_bind (kinds args.1); intro kind
    apply finite_bind (operations args); intro computed
    apply finite_step; apply finite_step; apply finite_step
    exact finite_done _

end ConstitutiveSearch.Agent.Local.Documentary.ControlReceivedResources

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlReceivedResources.code
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlReceivedResources.bounded
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlReceivedResources.finite
/- AXIOM_AUDIT_END -/
