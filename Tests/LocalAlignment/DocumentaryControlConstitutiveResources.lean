import Tests.LocalAlignment.DocumentaryControlResources

/-! Paid arguments and formation for higher-universe master resources. An
operation is supplied as controlled code, never called again by formation.
The result preserves the entire original support and its formation. -/
set_option genInjectivity false
set_option maxHeartbeats 4000000
namespace ConstitutiveSearch.Agent.Local.Documentary.ControlConstitutiveResources
open Resources Control ControlBindings
universe u v
variable {Kind : Type u} {Value : Kind → Type v}

abbrev Arguments {context inputs : List Kind}
    (ports : Ports context inputs) (values : Values Value context) :=
  {args : Values Value inputs // args = ports.read values}

def argumentsCode {context inputs : List Kind}
    (ports : Ports context inputs) (values : Values Value context) :
    Code Label (Arguments ports values) :=
  .step .producerPortCell (fun _ => match ports with
    | .nil => .done ⟨PUnit.unit, rfl⟩
    | .cons ref rest => (ControlResources.readCode values ref).bind (fun head =>
        (argumentsCode rest values).bind (fun tail => .done
          ⟨(head.1, tail.1), by
            obtain ⟨_, actualHead⟩ := head
            obtain ⟨_, actualTail⟩ := tail
            cases actualHead; cases actualTail; rfl⟩)))

def argumentsBound {context inputs : List Kind} (ports : Ports context inputs) : Nat :=
  match ports with
  | .nil => 1
  | .cons ref rest => ((ref.position + 1) + argumentsBound rest) + 1

theorem arguments_bounded {context inputs : List Kind}
    (ports : Ports context inputs) (values : Values Value context) :
    Within (argumentsCode ports values) (argumentsBound ports) := by
  induction ports with
  | nil => exact within_step _ _ (within_done _)
  | cons ref rest previous =>
      apply within_step
      apply within_bind (ControlResources.read_bounded values ref)
      intro head
      apply within_weaken
      · apply within_bind (more := 0) previous
        intro tail
        exact within_done _
      · exact Nat.le_of_eq (Nat.add_zero _)

abbrev Operation {context : List Kind} (producer : Producer Value context)
    (args : Values Value producer.inputKinds) :=
  {value : Value (producer.outputKind args) // value = producer.operation args}

abbrev Extended {context : List Kind} (support : Support Value context)
    (producer : Producer Value context) :=
  {after : Support Value (producer.outputKind (producer.arguments support.values) :: context) //
    after = support.extend producer}

def extendCode {context : List Kind} (support : Support Value context)
    (producer : Producer Value context)
    (operation : (args : Values Value producer.inputKinds) → Code Label (Operation producer args)) :
    Code Label (Extended support producer) :=
  (argumentsCode producer.inputs support.values).bind (fun args =>
    (operation args.1).bind (fun computed =>
      .step .formationValues (fun _ =>
        let value : Value (producer.outputKind (producer.arguments support.values)) :=
          Eq.rec (motive := fun received _ => Value (producer.outputKind received)) computed.1 args.2
        let values : Values Value (producer.outputKind (producer.arguments support.values) :: context) :=
          (value, support.values)
        .step .formationWitness (fun _ =>
          let alignment : Formation Value
              (context := producer.outputKind (producer.arguments support.values) :: context)
              (producer.operation (producer.arguments support.values), support.values) =
              Formation Value values := by
            obtain ⟨_, actualArgs⟩ := args
            cases actualArgs
            obtain ⟨_, actualValue⟩ := computed
            cases actualValue; rfl
          let formation := alignment ▸ Formation.produced support.formation producer
          .step .formationResources (fun _ => .done
            ⟨⟨values, formation⟩, by
              obtain ⟨_, actualArgs⟩ := args
              cases actualArgs
              obtain ⟨_, actualValue⟩ := computed
              cases actualValue; rfl⟩)))))

theorem extend_bounded {context : List Kind} (support : Support Value context)
    (producer : Producer Value context)
    (operation : (args : Values Value producer.inputKinds) → Code Label (Operation producer args))
    (bound : Nat) (operationBound : ∀ args, Within (operation args) bound) :
    Within (extendCode support producer operation) (argumentsBound producer.inputs + (bound + 3)) := by
  apply within_bind (arguments_bounded producer.inputs support.values)
  intro args
  apply within_bind (operationBound args.1)
  intro computed
  apply within_step; apply within_step; apply within_step
  exact within_done _

theorem extend_finite {context : List Kind} (support : Support Value context)
    (producer : Producer Value context)
    (operation : (args : Values Value producer.inputKinds) → Code Label (Operation producer args))
    (operationFinite : ∀ args, Finite (operation args)) :
    Finite (extendCode support producer operation) := by
  apply finite_bind
  · obtain ⟨value, labels, trace, _⟩ := arguments_bounded producer.inputs support.values
    exact ⟨value, labels, trace⟩
  · intro args
    apply finite_bind (operationFinite args.1)
    intro computed
    apply finite_step; apply finite_step; apply finite_step
    exact finite_done _

end ConstitutiveSearch.Agent.Local.Documentary.ControlConstitutiveResources

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlConstitutiveResources.Arguments
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlConstitutiveResources.argumentsCode
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlConstitutiveResources.argumentsBound
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlConstitutiveResources.arguments_bounded
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlConstitutiveResources.Operation
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlConstitutiveResources.Extended
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlConstitutiveResources.extendCode
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlConstitutiveResources.extend_bounded
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlConstitutiveResources.extend_finite
/- AXIOM_AUDIT_END -/
