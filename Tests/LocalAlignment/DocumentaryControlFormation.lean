import Tests.LocalAlignment.DocumentaryControlProducer
import Tests.LocalAlignment.DocumentaryControlResources
import Tests.LocalAlignment.DocumentaryControlArithmetic

/-! Formation consumes the paid catalogue result and retains the actual producer
and prior formation. Each values, witness, support and action constructor is
paid before it is built. Type alignment is erased and performs no replay. -/
set_option genInjectivity false
set_option maxHeartbeats 3000000
namespace ConstitutiveSearch.Agent.Local.Documentary.ControlFormation
open Resources Control ControlBindings
variable {context : List SourceKey} {sources : Support SourceValue context}
  {contract : Contract} {rules : Deduction.Policy} {kinds : List Deduction.Kind}
  {left right : Deduction.Kind}

def code (knowledge : Deduction.Knowledge sources contract rules kinds)
    (request : Deduction.Request rules) (leftRef : Ref kinds left) (rightRef : Ref kinds right)
    (producer : ControlProducer.Packet request leftRef rightRef)
    (leftRead : ControlResources.Read knowledge.resources.values leftRef)
    (rightRead : ControlResources.Read knowledge.resources.values rightRef)
    (computed : ControlArithmetic.Computation producer.operation leftRead.1 rightRead.1) :
    Code Label (Deduction.FormationAction knowledge request leftRef rightRef) :=
  .step .formationValues (fun _ =>
    let values : Values Deduction.Value (Deduction.derivedKind request leftRef rightRef :: kinds) :=
      (computed.1, knowledge.resources.values)
    .step .formationWitness (fun _ =>
      let positive := Formation.produced knowledge.resources.formation producer.formed
      let alignment :
          Formation Deduction.Value
            (context := producer.formed.outputKind (producer.formed.arguments knowledge.resources.values) :: kinds)
            (producer.formed.operation (producer.formed.arguments knowledge.resources.values), knowledge.resources.values) =
          Formation Deduction.Value (context := Deduction.derivedKind request leftRef rightRef :: kinds) values := by
        obtain ⟨formed, formedActual, operation, operationActual⟩ := producer
        obtain ⟨leftValue, leftActual⟩ := leftRead
        obtain ⟨rightValue, rightActual⟩ := rightRead
        obtain ⟨output, outputActual⟩ := computed
        cases operationActual
        cases outputActual
        cases formedActual
        cases leftActual
        cases rightActual
        rfl
      let retained := alignment ▸ positive
      .step .formationResources (fun _ =>
        let resources : Support Deduction.Value (Deduction.derivedKind request leftRef rightRef :: kinds) :=
          ⟨values, retained⟩
        .step .deductionProducer (fun _ =>
          .done (Deduction.formFromSupport knowledge request leftRef rightRef resources (by
            obtain ⟨formed, formedActual, operation, operationActual⟩ := producer
            obtain ⟨leftValue, leftActual⟩ := leftRead
            obtain ⟨rightValue, rightActual⟩ := rightRead
            obtain ⟨output, outputActual⟩ := computed
            cases operationActual
            cases outputActual
            cases formedActual
            cases leftActual
            cases rightActual
            rfl))))))

theorem bounded (knowledge : Deduction.Knowledge sources contract rules kinds)
    (request : Deduction.Request rules) (leftRef : Ref kinds left) (rightRef : Ref kinds right)
    (producer : ControlProducer.Packet request leftRef rightRef)
    (leftRead : ControlResources.Read knowledge.resources.values leftRef)
    (rightRead : ControlResources.Read knowledge.resources.values rightRef)
    (computed : ControlArithmetic.Computation producer.operation leftRead.1 rightRead.1) :
    Within (code knowledge request leftRef rightRef producer leftRead rightRead computed) 4 :=
  within_step _ _ (within_step _ _ (within_step _ _ (within_step _ _ (within_done _))))

theorem actual (knowledge : Deduction.Knowledge sources contract rules kinds)
    (request : Deduction.Request rules) (leftRef : Ref kinds left) (rightRef : Ref kinds right)
    (producer : ControlProducer.Packet request leftRef rightRef)
    (leftRead : ControlResources.Read knowledge.resources.values leftRef)
    (rightRead : ControlResources.Read knowledge.resources.values rightRef)
    (computed : ControlArithmetic.Computation producer.operation leftRead.1 rightRead.1)
    (fuel : Nat) (result : Result (code knowledge request leftRef rightRef producer leftRead rightRead computed) fuel) :
    result.value = Deduction.form knowledge request leftRef rightRef := result.value.eq_form

end ConstitutiveSearch.Agent.Local.Documentary.ControlFormation

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFormation.code
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFormation.bounded
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFormation.actual
/- AXIOM_AUDIT_END -/
