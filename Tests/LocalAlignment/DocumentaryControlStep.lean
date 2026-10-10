import Tests.LocalAlignment.DocumentaryControlDeduction

/-! Instrumented binding control feeds the same documentary producers and
assembly functions as Program.step. Producer entry labels count invocations;
their internal computation and assembly costs are separate open boundaries. -/
set_option genInjectivity false
set_option maxHeartbeats 3000000
namespace ConstitutiveSearch.Agent.Local.Documentary.ControlStep
open Resources Program Snapshot Control ControlBindings

variable {context : List SourceKey} {sources : Support SourceValue context}
  {contract : Contract} {rules : Deduction.Policy} {slots : List Specification}
  {spec : Specification}

abbrev Packet (before : FrameData sources contract rules slots)
    (instruction : Instruction context rules slots spec) :=
  {produced : Step before.restore instruction // produced = Program.step before.restore instruction}

def code (before : FrameData sources contract rules slots)
    (instruction : Instruction context rules slots spec) : Code Label (Packet before instruction) :=
  .step .instruction (fun _ => match instruction with
    | .quotation task => .step .quotationProducer (fun _ =>
        let produced := Dossier.step before.dossier task
        .done ⟨quotationStep before.restore task produced, rfl⟩)
    | .conclusion request leftSlot rightSlot demand =>
        (readCode before.bindings leftSlot).bind (fun leftRead =>
          match leftActual : leftRead.1 with
          | none => .step .missingAssembly (fun _ =>
              let absent := leftRead.2.trans leftActual
              let produced := missingStep before.restore request leftSlot rightSlot demand
                (fun complete => by
                  have impossible := absent.symm.trans (complete leftSlot).actual
                  cases impossible)
              .done ⟨produced, by
                dsimp only [Program.step]
                split
                · rfl
                · rename_i occurrence found
                  cases absent.symm.trans found⟩)
          | some leftOccurrence =>
              (readCode before.bindings rightSlot).bind (fun rightRead =>
                match rightActual : rightRead.1 with
                | none => .step .missingAssembly (fun _ =>
                    let absent := rightRead.2.trans rightActual
                    let produced := missingStep before.restore request leftSlot rightSlot demand
                      (fun complete => by
                        have impossible := absent.symm.trans (complete rightSlot).actual
                        cases impossible)
                    .done ⟨produced, by
                      dsimp only [Program.step]
                      split
                      · rename_i missing
                        cases (leftRead.2.trans leftActual).symm.trans missing
                      · rename_i occurrence found
                        have same := Option.some.inj ((leftRead.2.trans leftActual).symm.trans found)
                        cases same
                        split
                        · rfl
                        · rename_i occurrence found
                          cases absent.symm.trans found⟩)
                | some rightOccurrence =>
                  (ControlDeduction.code before.store.2 request
                    leftOccurrence.2 rightOccurrence.2).bind (fun actualDecision =>
                   .step .deductionAssembly (fun _ =>
                    let foundLeft := leftRead.2.trans leftActual
                    let foundRight := rightRead.2.trans rightActual
                    let decision := actualDecision.1
                    let produced := deductionStep before.restore request leftSlot rightSlot demand
                      leftOccurrence rightOccurrence foundLeft foundRight decision
                    .done ⟨produced, by
                      dsimp only [Program.step]
                      split
                      · rename_i missing
                        cases foundLeft.symm.trans missing
                      · rename_i occurrence found
                        have same := Option.some.inj (foundLeft.symm.trans found)
                        cases same
                        split
                        · rename_i missing
                          cases foundRight.symm.trans missing
                        · rename_i occurrence found
                          have same := Option.some.inj (foundRight.symm.trans found)
                          cases same
                          exact congrArg
                            (fun decision => deductionStep before.restore request leftSlot rightSlot demand
                              leftOccurrence rightOccurrence foundLeft foundRight decision) actualDecision.2⟩)))))

def complete (before : FrameData sources contract rules slots)
    (instruction : Instruction context rules slots spec) (fuel : Nat)
    (actual : Result (code before instruction) fuel)
    (ready : Ready sources contract instruction) (initial : Complete before.restore) :
    Complete actual.value.1.next := actual.value.1.progress ready initial

theorem finite (before : FrameData sources contract rules slots)
    (instruction : Instruction context rules slots spec) :
    Finite (code before instruction) := by
  apply finite_step
  cases instruction with
  | quotation task => exact finite_step _ _ (finite_done _)
  | conclusion request leftSlot rightSlot demand =>
      apply finite_bind ⟨_, _, ⟨readTrace before.bindings leftSlot⟩⟩
      intro leftRead
      split
      · exact finite_step _ _ (finite_done _)
      · apply finite_bind ⟨_, _, ⟨readTrace before.bindings rightSlot⟩⟩
        intro rightRead
        split
        · exact finite_step _ _ (finite_done _)
        · apply finite_bind (ControlDeduction.finite _ _ _ _)
          intro decision
          exact finite_step _ _ (finite_done _)

theorem sufficient_fuel (before : FrameData sources contract rules slots)
    (instruction : Instruction context rules slots spec) :
    ∃ (fuel : Nat) (produced : Packet before instruction) (labels : List Label),
      runCtl fuel (code before instruction) = some (produced, labels) :=
  finite_complete (finite before instruction)

theorem actual_step (before : FrameData sources contract rules slots)
    (instruction : Instruction context rules slots spec) (fuel : Nat)
    (actual : Result (code before instruction) fuel) :
    actual.value.1 = Program.step before.restore instruction := actual.value.2

theorem reset_same_code {Context : Type} {final : List Specification}
    (before : PresentData sources contract rules Context final) (policy : Adaptive.Policy Context)
    {spec : Specification} (instruction : Instruction context rules before.slots spec) :
    code (before.reset policy).session.frame instruction = code before.session.frame instruction := rfl

end ConstitutiveSearch.Agent.Local.Documentary.ControlStep

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlStep.Packet
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlStep.code
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlStep.complete
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlStep.finite
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlStep.sufficient_fuel
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlStep.actual_step
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlStep.reset_same_code
/- AXIOM_AUDIT_END -/
