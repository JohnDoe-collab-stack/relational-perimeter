import Tests.LocalAlignment.DocumentaryControlAssembly
import Tests.LocalAlignment.DocumentaryControlMaster
import Tests.LocalAlignment.DocumentaryControlQuotationAssembly
import Tests.LocalAlignment.DocumentaryControlMissingAssembly

/-! Instrumented binding control feeds the same documentary producers and
assembly target as Program.step. Deduction assembly has explicit paid stages;
the quotation master and interpreter administration remain open boundaries. -/
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
    | .quotation task => (ControlMaster.runCode before.dossier task).bind (fun actual =>
        .step .assemblyPacket (fun _ =>
          .done ⟨quotationStep before.restore task actual.1,
            congrArg (quotationStep before.restore task) actual.2⟩))
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
                    let foundLeft := leftRead.2.trans leftActual
                    let foundRight := rightRead.2.trans rightActual
                    let decision := actualDecision.1
                    (ControlAssembly.code before.restore request leftSlot rightSlot demand
                      leftOccurrence rightOccurrence foundLeft foundRight decision).bind (fun assembled =>
                    .done ⟨assembled.1, by
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
                          exact assembled.2.trans (congrArg
                            (fun decision => deductionStep before.restore request leftSlot rightSlot demand
                              leftOccurrence rightOccurrence foundLeft foundRight decision) actualDecision.2)⟩)))))

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
  | quotation task =>
      apply finite_bind (ControlMaster.run_finite before.dossier task)
      intro actual
      exact finite_step _ _ (finite_done _)
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
          apply finite_bind (ControlAssembly.finite _ _ _ _ _ _ _ _ _ _)
          intro assembled
          exact finite_done _

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

def expandedCode (before : FrameData sources contract rules slots)
    (instruction : Instruction context rules slots spec) : Code Label (Packet before instruction) :=
  .step .frameRestore (fun _ =>
    let frame : Frame sources contract rules slots :=
      ⟨before.dossier, before.store, before.bindings.read⟩
    .step .instruction (fun _ => match instruction with
    | .quotation task => (ControlMaster.expandedRunCode before.dossier task).bind (fun actual =>
        (ControlQuotationAssembly.code frame task actual.1).bind (fun assembled =>
          .done ⟨assembled.1, assembled.2.trans (congrArg (quotationStep frame task) actual.2)⟩))
    | .conclusion request leftSlot rightSlot demand =>
        (readCode before.bindings leftSlot).bind (fun leftRead =>
          match leftActual : leftRead.1 with
          | none =>
              let absent := leftRead.2.trans leftActual
              let missing : Complete frame → False := fun complete => by
                have impossible := absent.symm.trans (complete leftSlot).actual
                cases impossible
              (ControlMissingAssembly.code frame request leftSlot rightSlot demand missing).bind (fun assembled =>
                .done ⟨assembled.1, by
                  dsimp only [Program.step]
                  split
                  · exact assembled.2
                  · rename_i occurrence found
                    cases absent.symm.trans found⟩)
          | some leftOccurrence =>
              (readCode before.bindings rightSlot).bind (fun rightRead =>
                match rightActual : rightRead.1 with
                | none =>
                  let absent := rightRead.2.trans rightActual
                  let missing : Complete frame → False := fun complete => by
                    have impossible := absent.symm.trans (complete rightSlot).actual
                    cases impossible
                  (ControlMissingAssembly.code frame request leftSlot rightSlot demand missing).bind (fun assembled =>
                    .done ⟨assembled.1, by
                      dsimp only [Program.step]
                      split
                      · rename_i leftMissing; cases (leftRead.2.trans leftActual).symm.trans leftMissing
                      · rename_i occurrence found
                        have same := Option.some.inj ((leftRead.2.trans leftActual).symm.trans found)
                        cases same
                        split
                        · exact assembled.2
                        · rename_i rightOccurrence foundRight
                          cases absent.symm.trans foundRight⟩)
                | some rightOccurrence =>
                  (ControlDeduction.code before.store.2 request
                    leftOccurrence.2 rightOccurrence.2).bind (fun actualDecision =>
                    let foundLeft := leftRead.2.trans leftActual
                    let foundRight := rightRead.2.trans rightActual
                    let decision := actualDecision.1
                    (ControlAssembly.code frame request leftSlot rightSlot demand
                      leftOccurrence rightOccurrence foundLeft foundRight decision).bind (fun assembled =>
                    .done ⟨assembled.1, by
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
                          exact assembled.2.trans (congrArg
                            (fun decision => deductionStep frame request leftSlot rightSlot demand
                              leftOccurrence rightOccurrence foundLeft foundRight decision) actualDecision.2)⟩))))))

theorem expanded_finite (before : FrameData sources contract rules slots)
    (instruction : Instruction context rules slots spec) : Finite (expandedCode before instruction) := by
  apply finite_step; apply finite_step
  cases instruction with
  | quotation task =>
    apply finite_bind (ControlMaster.expanded_run_finite before.dossier task); intro actual
    apply finite_bind (ControlQuotationAssembly.finite _ _ _); intro assembled
    exact finite_done _
  | conclusion request leftSlot rightSlot demand =>
    apply finite_bind ⟨_, _, ⟨readTrace before.bindings leftSlot⟩⟩; intro leftRead
    split
    · apply finite_bind
      · obtain ⟨value, labels, trace, _⟩ := ControlMissingAssembly.bounded _ _ _ _ _ _
        exact ⟨value, labels, trace⟩
      · intro assembled; exact finite_done _
    · apply finite_bind ⟨_, _, ⟨readTrace before.bindings rightSlot⟩⟩; intro rightRead
      split
      · apply finite_bind
        · obtain ⟨value, labels, trace, _⟩ := ControlMissingAssembly.bounded _ _ _ _ _ _
          exact ⟨value, labels, trace⟩
        · intro assembled; exact finite_done _
      · apply finite_bind (ControlDeduction.finite _ _ _ _); intro decision
        apply finite_bind (ControlAssembly.finite _ _ _ _ _ _ _ _ _ _); intro assembled
        exact finite_done _

theorem expanded_actual (before : FrameData sources contract rules slots)
    (instruction : Instruction context rules slots spec) (fuel : Nat)
    (actual : Result (expandedCode before instruction) fuel) :
    actual.value.1 = Program.step before.restore instruction := actual.value.2

end ConstitutiveSearch.Agent.Local.Documentary.ControlStep

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlStep.Packet
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlStep.code
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlStep.complete
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlStep.finite
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlStep.sufficient_fuel
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlStep.actual_step
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlStep.reset_same_code
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlStep.expandedCode
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlStep.expanded_finite
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlStep.expanded_actual
/- AXIOM_AUDIT_END -/
