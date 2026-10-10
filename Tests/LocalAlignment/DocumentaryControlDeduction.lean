import Tests.LocalAlignment.DocumentaryControlPermission

/-! The paid lookup result supplies the actual permission to the existing
formation producer. The original decision function occurs only in erased
equalities; there is no second permission lookup or producer invocation. -/
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
  (referencedLookup rules.allowed request.2).bind (fun actual =>
    match found : actual.1 with
    | none => .step .deductionDecision (fun _ =>
        let absent := actual.2.symm.trans found
        .done ⟨.refused absent, by
          unfold Deduction.execute
          split
          · rfl
          · rename_i permission present
            cases absent.symm.trans present⟩)
    | some permission => .step .deductionProducer (fun _ =>
        let present := actual.2.symm.trans found
        let action := Deduction.form knowledge request leftRef rightRef
        .done ⟨.accepted action permission, by
          unfold Deduction.execute
          split
          · rename_i absent
            cases present.symm.trans absent
          · rename_i received same
            have identical := Option.some.inj (present.symm.trans same)
            cases identical
            rfl⟩))

theorem finite (knowledge : Deduction.Knowledge sources contract rules kinds)
    (request : Deduction.Request rules) (leftRef : Ref kinds left) (rightRef : Ref kinds right) :
    Finite (code knowledge request leftRef rightRef) := by
  apply finite_bind (referenced_finite rules.allowed request.2)
  intro actual
  split <;> exact finite_step _ _ (finite_done _)

theorem actual_decision (knowledge : Deduction.Knowledge sources contract rules kinds)
    (request : Deduction.Request rules) (leftRef : Ref kinds left) (rightRef : Ref kinds right)
    (fuel : Nat) (actual : Result (code knowledge request leftRef rightRef) fuel) :
    actual.value.1 = Deduction.execute knowledge request leftRef rightRef := actual.value.2

theorem bounded (knowledge : Deduction.Knowledge sources contract rules kinds)
    (request : Deduction.Request rules) (leftRef : Ref kinds left) (rightRef : Ref kinds right) :
    Within (code knowledge request leftRef rightRef)
      ((ControlReference.positionBound request.2 + lookupBound rules.allowed request.2.position) + 1) := by
  apply within_bind (referenced_bounded rules.allowed request.2)
  intro actual
  split <;> exact within_step _ _ (within_done _)

end ConstitutiveSearch.Agent.Local.Documentary.ControlDeduction

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlDeduction.Packet
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlDeduction.code
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlDeduction.finite
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlDeduction.actual_decision
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlDeduction.bounded
/- AXIOM_AUDIT_END -/
