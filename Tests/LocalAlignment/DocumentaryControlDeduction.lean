import Tests.LocalAlignment.DocumentaryControlPermission
import Tests.LocalAlignment.DocumentaryControlResources
import Tests.LocalAlignment.DocumentaryControlProducer

/-! The paid lookup result supplies the actual permission to the existing
formation producer. Paid resource reads supply its actual arguments. The
original decision function occurs only in erased equalities. -/
set_option genInjectivity false
set_option maxHeartbeats 3000000
namespace ConstitutiveSearch.Agent.Local.Documentary.ControlDeduction
open Resources Control ControlBindings ControlPermission

variable {context : List SourceKey} {sources : Support SourceValue context}
  {contract : Contract} {rules : Deduction.Policy} {kinds : List Deduction.Kind}
  {left right : Deduction.Kind}

abbrev Packet (knowledge : Deduction.Knowledge sources contract rules kinds)
    (request : Deduction.Request rules) (leftRef : Ref kinds left) (rightRef : Ref kinds right) :=
  {decision : Deduction.Decision knowledge request leftRef rightRef //
    decision = Deduction.execute knowledge request leftRef rightRef}

def code (knowledge : Deduction.Knowledge sources contract rules kinds)
    (request : Deduction.Request rules) (leftRef : Ref kinds left) (rightRef : Ref kinds right) :
    Code Label (Packet knowledge request leftRef rightRef) :=
  (locatedLookup rules.allowed request.2).bind (fun actual =>
    match found : actual.2.1 with
    | none => .step .deductionDecision (fun _ =>
        let absent := actual.2.2.symm.trans found
        .done ⟨.refused absent, by
          unfold Deduction.execute
          split
          · rfl
          · rename_i permission present
            cases absent.symm.trans present⟩)
    | some permission =>
      (ControlResources.readCode knowledge.resources.values leftRef).bind (fun leftRead =>
      (ControlResources.readCode knowledge.resources.values rightRef).bind (fun rightRead =>
      (ControlProducer.code request leftRef rightRef actual.1).bind (fun producer =>
      .step .deductionProducer (fun _ =>
        let present := actual.2.2.symm.trans found
        let action := Deduction.formFromProducerReads knowledge request leftRef rightRef
          producer.1 producer.2
          leftRead.1 rightRead.1 leftRead.2 rightRead.2
        .done ⟨.accepted action permission, by
          unfold Deduction.execute
          split
          · rename_i absent
            cases present.symm.trans absent
          · rename_i received same
            have identical := Option.some.inj (present.symm.trans same)
            cases identical
            exact congrArg (fun formed => Deduction.Decision.accepted formed permission)
              (Deduction.formFromProducerReads_actual knowledge request leftRef rightRef
                producer.1 producer.2 leftRead.1 rightRead.1 leftRead.2 rightRead.2)⟩)))))

theorem finite (knowledge : Deduction.Knowledge sources contract rules kinds)
    (request : Deduction.Request rules) (leftRef : Ref kinds left) (rightRef : Ref kinds right) :
    Finite (code knowledge request leftRef rightRef) := by
  apply finite_bind (located_finite rules.allowed request.2)
  intro actual
  split
  · exact finite_step _ _ (finite_done _)
  · apply finite_bind ⟨_, _, ⟨ControlResources.readTrace knowledge.resources.values leftRef⟩⟩
    intro leftRead
    apply finite_bind ⟨_, _, ⟨ControlResources.readTrace knowledge.resources.values rightRef⟩⟩
    intro rightRead
    apply finite_bind (ControlProducer.finite request leftRef rightRef actual.1)
    intro producer
    exact finite_step _ _ (finite_done _)

theorem actual_decision (knowledge : Deduction.Knowledge sources contract rules kinds)
    (request : Deduction.Request rules) (leftRef : Ref kinds left) (rightRef : Ref kinds right)
    (fuel : Nat) (actual : Result (code knowledge request leftRef rightRef) fuel) :
    actual.value.1 = Deduction.execute knowledge request leftRef rightRef := actual.value.2

theorem bounded (knowledge : Deduction.Knowledge sources contract rules kinds)
    (request : Deduction.Request rules) (leftRef : Ref kinds left) (rightRef : Ref kinds right) :
    Within (code knowledge request leftRef rightRef)
      ((ControlReference.positionBound request.2 + lookupBound rules.allowed request.2.position) +
        ((leftRef.position + 1) + ((rightRef.position + 1) +
          ((ControlReference.positionBound leftRef + (ControlReference.positionBound rightRef + 8)) + 1)))) := by
  apply within_bind (located_bounded rules.allowed request.2)
  intro actual
  split
  · exact within_weaken (within_step _ _ (within_done _))
      (Nat.succ_le_succ (Nat.zero_le _))
  · apply within_bind (ControlResources.read_bounded knowledge.resources.values leftRef)
    intro leftRead
    apply within_bind (ControlResources.read_bounded knowledge.resources.values rightRef)
    intro rightRead
    apply within_bind (ControlProducer.bounded request leftRef rightRef actual.1)
    intro producer
    exact within_step _ _ (within_done _)

end ConstitutiveSearch.Agent.Local.Documentary.ControlDeduction

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlDeduction.Packet
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlDeduction.code
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlDeduction.finite
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlDeduction.actual_decision
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlDeduction.bounded
/- AXIOM_AUDIT_END -/
