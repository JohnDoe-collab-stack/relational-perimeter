import Tests.LocalAlignment.DocumentaryControlReference

/-! Construct the existing binary producer from paid positions and received
ports. Its positive packet is consumed by formation, not reconstructed there. -/
set_option genInjectivity false
set_option maxHeartbeats 3000000
namespace ConstitutiveSearch.Agent.Local.Documentary.ControlProducer
open Resources Control ControlBindings ControlReference
variable {rules : Deduction.Policy} {kinds : List Deduction.Kind} {left right : Deduction.Kind}

abbrev Packet (request : Deduction.Request rules)
    (leftRef : Ref kinds left) (rightRef : Ref kinds right) :=
  {formed : Producer Deduction.Value kinds // formed = Deduction.producer request leftRef rightRef}

def buildCode (request : Deduction.Request rules) (leftRef : Ref kinds left) (rightRef : Ref kinds right)
    (rulePosition : Position request.2) (leftPosition : Position leftRef) (rightPosition : Position rightRef) :
    Code Label (Packet request leftRef rightRef) :=
  .step .producerKindCell (fun _ =>
    let emptyKinds : List Deduction.Kind := []
    .step .producerKindCell (fun _ =>
      let rightKinds := right :: emptyKinds
      .step .producerKindCell (fun _ =>
        let inputKinds := left :: rightKinds
        .step .producerPortCell (fun _ =>
          let emptyPorts : Ports kinds [] := .nil
          .step .producerPortCell (fun _ =>
            let rightPorts : Ports kinds [right] := .cons rightRef emptyPorts
            .step .producerPortCell (fun _ =>
              let inputs : Ports kinds [left, right] := .cons leftRef rightPorts
              .step .producerOutputKind (fun _ =>
                let outputKind := Deduction.Kind.derived request.1 rulePosition.1
                  left leftPosition.1 right rightPosition.1
                .step .producerAssembly (fun _ =>
                  let formed : Producer Deduction.Value kinds :=
                    ⟨inputKinds, inputs, fun _ => outputKind,
                      fun arguments => Deduction.evaluate request.1.operation arguments.1 arguments.2.1⟩
                  .done ⟨formed, by
                    obtain ⟨rulePosition, ruleActual⟩ := rulePosition
                    obtain ⟨leftPosition, leftActual⟩ := leftPosition
                    obtain ⟨rightPosition, rightActual⟩ := rightPosition
                    cases ruleActual
                    cases leftActual
                    cases rightActual
                    rfl⟩))))))))

def buildTrace (request : Deduction.Request rules) (leftRef : Ref kinds left) (rightRef : Ref kinds right)
    (rulePosition : Position request.2) (leftPosition : Position leftRef) (rightPosition : Position rightRef) :
    Eval (buildCode request leftRef rightRef rulePosition leftPosition rightPosition)
      [.producerKindCell, .producerKindCell, .producerKindCell,
        .producerPortCell, .producerPortCell, .producerPortCell, .producerOutputKind, .producerAssembly]
      ⟨Deduction.producer request leftRef rightRef, rfl⟩ := by
  obtain ⟨rulePosition, ruleActual⟩ := rulePosition
  obtain ⟨leftPosition, leftActual⟩ := leftPosition
  obtain ⟨rightPosition, rightActual⟩ := rightPosition
  cases ruleActual
  cases leftActual
  cases rightActual
  exact .step (.step (.step (.step (.step (.step (.step (.step .done)))))))

theorem build_bounded (request : Deduction.Request rules) (leftRef : Ref kinds left) (rightRef : Ref kinds right)
    (rulePosition : Position request.2) (leftPosition : Position leftRef) (rightPosition : Position rightRef) :
    Within (buildCode request leftRef rightRef rulePosition leftPosition rightPosition) 8 :=
  ⟨_, _, ⟨buildTrace request leftRef rightRef rulePosition leftPosition rightPosition⟩, Nat.le_refl _⟩

def code (request : Deduction.Request rules) (leftRef : Ref kinds left) (rightRef : Ref kinds right)
    (rulePosition : Position request.2) : Code Label (Packet request leftRef rightRef) :=
  (positionCode leftRef).bind (fun leftPosition =>
    (positionCode rightRef).bind (fun rightPosition =>
      buildCode request leftRef rightRef rulePosition leftPosition rightPosition))

theorem bounded (request : Deduction.Request rules) (leftRef : Ref kinds left) (rightRef : Ref kinds right)
    (rulePosition : Position request.2) :
    Within (code request leftRef rightRef rulePosition)
      (positionBound leftRef + (positionBound rightRef + 8)) := by
  apply within_bind (position_bounded leftRef)
  intro leftPosition
  apply within_bind (position_bounded rightRef)
  intro rightPosition
  exact build_bounded request leftRef rightRef rulePosition leftPosition rightPosition

theorem finite (request : Deduction.Request rules) (leftRef : Ref kinds left) (rightRef : Ref kinds right)
    (rulePosition : Position request.2) : Finite (code request leftRef rightRef rulePosition) := by
  obtain ⟨value, labels, trace, _⟩ := bounded request leftRef rightRef rulePosition
  exact ⟨value, labels, trace⟩

end ConstitutiveSearch.Agent.Local.Documentary.ControlProducer

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlProducer.Packet
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlProducer.buildCode
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlProducer.buildTrace
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlProducer.build_bounded
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlProducer.code
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlProducer.bounded
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlProducer.finite
/- AXIOM_AUDIT_END -/
