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

/-- Retain the paid arguments and kind alongside the entire produced support.
Downstream resource indices can consume these fields instead of reading the
original support again to recover its producer metadata. -/
structure Cached {context : List Kind} (support : Support Value context)
    (producer : Producer Value context) where
  args : Arguments producer.inputs support.values
  kind : Kind
  kindExact : kind = producer.outputKind args.1
  after : Support Value (kind :: context)
  actual : HEq after (support.extend producer)

theorem Cached.exact {context : List Kind} {support : Support Value context}
    {producer : Producer Value context} (cached : Cached support producer) :
    cached = (⟨⟨producer.arguments support.values, rfl⟩,
      producer.outputKind (producer.arguments support.values), rfl,
      support.extend producer, HEq.rfl⟩ : Cached support producer) := by
  rcases cached with ⟨⟨_, sameArgs⟩, _, sameKind, _, sameSupport⟩
  cases sameKind; cases sameArgs; cases sameSupport; rfl

def cachedCode {context : List Kind} (support : Support Value context)
    (producer : Producer Value context)
    (kindCode : (args : Values Value producer.inputKinds) →
      Code Label {kind : Kind // kind = producer.outputKind args})
    (operation : (args : Values Value producer.inputKinds) → Code Label (Operation producer args)) :
    Code Label (Cached support producer) :=
  (argumentsCode producer.inputs support.values).bind (fun args =>
    (kindCode args.1).bind (fun kind =>
      (operation args.1).bind (fun computed =>
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

theorem cached_bounded {context : List Kind} (support : Support Value context)
    (producer : Producer Value context)
    (kindCode : (args : Values Value producer.inputKinds) →
      Code Label {kind : Kind // kind = producer.outputKind args})
    (operation : (args : Values Value producer.inputKinds) → Code Label (Operation producer args))
    (kindBound operationBound : Nat)
    (kinds : ∀ args, Within (kindCode args) kindBound)
    (operations : ∀ args, Within (operation args) operationBound) :
    Within (cachedCode support producer kindCode operation)
      (argumentsBound producer.inputs + (kindBound + (operationBound + 3))) := by
  apply within_bind (arguments_bounded _ _); intro args
  apply within_bind (kinds args.1); intro kind
  apply within_bind (operations args.1); intro computed
  apply within_step; apply within_step; apply within_step
  exact within_done _

theorem cached_finite {context : List Kind} (support : Support Value context)
    (producer : Producer Value context)
    (kindCode : (args : Values Value producer.inputKinds) →
      Code Label {kind : Kind // kind = producer.outputKind args})
    (operation : (args : Values Value producer.inputKinds) → Code Label (Operation producer args))
    (kinds : ∀ args, Finite (kindCode args))
    (operations : ∀ args, Finite (operation args)) :
    Finite (cachedCode support producer kindCode operation) := by
  apply finite_bind
  · obtain ⟨value, labels, trace, _⟩ := arguments_bounded _ _
    exact ⟨value, labels, trace⟩
  · intro args
    apply finite_bind (kinds args.1); intro kind
    apply finite_bind (operations args.1); intro computed
    apply finite_step; apply finite_step; apply finite_step
    exact finite_done _

/-- The fresh reference is formed with the retained kind, then reindexed only
by its erased equality. It never calls the producer's input reader. -/
def Cached.here {context : List Kind} {support : Support Value context}
    {producer : Producer Value context} (cached : Cached support producer) :
    Ref (cached.kind :: context) (producer.outputKind cached.args.1) :=
  Eq.rec (motive := fun kind _ => Ref (cached.kind :: context) kind)
    Ref.here cached.kindExact

theorem Cached.read_here {context : List Kind} {support : Support Value context}
    {producer : Producer Value context} (cached : Cached support producer) :
    cached.after.read cached.here = producer.operation cached.args.1 := by
  rcases cached with ⟨⟨_, sameArgs⟩, _, sameKind, _, sameSupport⟩
  cases sameKind; cases sameArgs; cases sameSupport; rfl

/-- Transport an earlier occurrence into the retained output context. Callers
use kinds indexed by paid arguments, never by a second input traversal. -/
def retainedPrior {context : List Kind} {kind : Kind}
    (added : Kind) (ref : Ref context kind) : Ref (added :: context) kind :=
  .prior ref

theorem retained_prior_exact {context : List Kind} {kind : Kind}
    (added : Kind) (ref : Ref context kind) :
    retainedPrior added ref = Ref.prior ref := by
  cases ref <;> rfl

theorem Cached.read_prior {context : List Kind} {support : Support Value context}
    {producer : Producer Value context} (cached : Cached support producer)
    {kind : Kind} (ref : Ref context kind) :
    cached.after.read (retainedPrior cached.kind ref) = support.read ref := by
  cases cached.exact
  rw [retained_prior_exact]
  rfl

def retargetRef {context : List Kind} {kind target : Kind}
    (ref : Ref context kind) (same : kind = target) : Ref context target :=
  Eq.rec (motive := fun k _ => Ref context k) ref same

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
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlConstitutiveResources.Cached
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlConstitutiveResources.Cached.exact
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlConstitutiveResources.cachedCode
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlConstitutiveResources.cached_bounded
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlConstitutiveResources.cached_finite
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlConstitutiveResources.Cached.here
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlConstitutiveResources.Cached.read_here
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlConstitutiveResources.retainedPrior
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlConstitutiveResources.retained_prior_exact
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlConstitutiveResources.Cached.read_prior
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlConstitutiveResources.retargetRef
/- AXIOM_AUDIT_END -/
