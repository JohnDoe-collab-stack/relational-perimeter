import Tests.LocalAlignment.DocumentaryControlStep
import Tests.LocalAlignment.DocumentaryControlMeasuredMaster
import Tests.LocalAlignment.DocumentaryControlAssignmentCapture
import Tests.LocalAlignment.DocumentaryControlAssemblyExecution

/-! A realized snapshot carries the reader of the actual master successor and
an evidence recipe. Every assembly produces its own paid binding realization;
capture consumes it before the next snapshot is returned. -/
set_option genInjectivity false
set_option backward.match.sparseCases false
set_option maxHeartbeats 8000000
namespace ConstitutiveSearch.Agent.Local.Documentary.ControlFrameExecution
open Resources Program Snapshot Control ControlBindings ControlMasterData ControlDeferred
variable {context : List SourceKey} {sources : Support SourceValue context}
  {contract : Contract} {rules : Deduction.Policy} {slots : List Specification} {spec : Specification}

structure Realized (before : FrameData sources contract rules slots) where
  masterReader : ControlMeasuredAssignmentReader.Reader before.dossier.cursor.assignment.reader
  knowledgeRecipe : KnowledgeRecipe before.store.2
  masterRoot : Actual (EndogenousDecomposition.constructMeasuredOperationalRoot before.dossier.cursor.state.searchSeed)

structure Produced (before : FrameData sources contract rules slots)
    (instruction : Instruction context rules slots spec) where
  step : ControlStep.Packet before instruction
  next : Actual (Snapshot.frame step.1.next)
  realized : Realized next.1

@[inline] def formedRoot (before : FrameData sources contract rules slots)
    (state : ControlResources.Read before.dossier.cursor.support.values before.dossier.cursor.source)
    (root : Actual (EndogenousDecomposition.constructMeasuredOperationalRoot state.1.down.searchSeed)) :
    Actual (EndogenousDecomposition.constructMeasuredOperationalRoot before.dossier.cursor.state.searchSeed) := by
  obtain ⟨_, same⟩ := state
  cases same
  exact root

def formCode (before : FrameData sources contract rules slots)
    (correct : AssignmentCapture.Correct before.dossier.cursor) (knowledge : KnowledgeRecipe before.store.2) :
    Code Label (Realized before) :=
  (ControlResources.readCode before.dossier.cursor.support.values before.dossier.cursor.source).bind (fun state =>
    (ControlMasterGeneration.rootCode state.1.down.searchSeed).bind (fun root =>
      (ControlAssignmentCapture.readerCode before.dossier.cursor correct).bind (fun reader =>
        .step .executionPayload (fun _ => .done ⟨reader, knowledge, formedRoot before state root⟩))))

theorem form_finite (before : FrameData sources contract rules slots)
    (correct : AssignmentCapture.Correct before.dossier.cursor) (knowledge : KnowledgeRecipe before.store.2) :
    Finite (formCode before correct knowledge) := by
  apply finite_bind
  · obtain ⟨value, labels, trace, _⟩ := ControlResources.read_bounded before.dossier.cursor.support.values before.dossier.cursor.source
    exact ⟨value, labels, trace⟩
  · intro state
    apply finite_bind (ControlMasterGeneration.root_finite _); intro root
    apply finite_bind (ControlAssignmentCapture.reader_finite _ _); intro reader
    exact finite_step _ _ (finite_done _)

def finishCode (before : FrameData sources contract rules slots)
    (instruction : Instruction context rules slots spec) (step : ControlStep.Packet before instruction)
    (bindings : ControlBindingReader.Reader step.1.next.bindings)
    (knowledge : KnowledgeRecipe step.1.next.store.2)
    (reader : ControlMeasuredAssignmentReader.Reader step.1.next.dossier.cursor.assignment.reader)
    (root : Actual (EndogenousDecomposition.constructMeasuredOperationalRoot step.1.next.dossier.cursor.state.searchSeed)) :
    Code Label (Produced before instruction) :=
  (ControlBindingReader.captureCode (spec :: slots) step.1.next.bindings bindings).bind (fun captured =>
    .step .formationResources (fun _ =>
      let next : Actual (Snapshot.frame step.1.next) :=
        ⟨⟨step.1.next.dossier, step.1.next.store, captured.1⟩,
          by obtain ⟨_, actual⟩ := captured; cases actual; rfl⟩
      .step .executionPayload (fun _ => .done ⟨step, next, ⟨reader, knowledge, root⟩⟩)))

theorem finish_finite (before : FrameData sources contract rules slots)
    (instruction : Instruction context rules slots spec) (step : ControlStep.Packet before instruction)
    (bindings : ControlBindingReader.Reader step.1.next.bindings)
    (knowledge : KnowledgeRecipe step.1.next.store.2)
    (reader : ControlMeasuredAssignmentReader.Reader step.1.next.dossier.cursor.assignment.reader)
    (root : Actual (EndogenousDecomposition.constructMeasuredOperationalRoot step.1.next.dossier.cursor.state.searchSeed)) :
    Finite (finishCode before instruction step bindings knowledge reader root) := by
  apply finite_bind (ControlBindingReader.capture_finite _ _ _); intro captured
  apply finite_step; exact finite_step _ _ (finite_done _)

@[inline] def quotationReader (before : Frame sources contract rules slots)
    (task : Dossier.Obligation context) (produced : Dossier.Step before.dossier task)
    (step : Actual (quotationStep before task produced))
    (reader : ControlMeasuredAssignmentReader.Reader produced.1.next.assignment.reader) :
    ControlMeasuredAssignmentReader.Reader step.1.next.dossier.cursor.assignment.reader := by
  obtain ⟨_, actual⟩ := step; cases actual
  obtain ⟨stage, decision⟩ := produced; cases decision <;> exact reader

@[inline] def missingReader {left right : Specification} (before : Frame sources contract rules slots)
    (request : Deduction.Request rules) (leftSlot : Ref slots left) (rightSlot : Ref slots right)
    (demand : Deduction.Demand) (missing : Complete before → False)
    (step : Actual (missingStep before request leftSlot rightSlot demand missing))
    (reader : ControlMeasuredAssignmentReader.Reader before.dossier.cursor.assignment.reader) :
    ControlMeasuredAssignmentReader.Reader step.1.next.dossier.cursor.assignment.reader := by
  obtain ⟨_, actual⟩ := step; cases actual; exact reader

@[inline] def deductionReader {left right : Specification} (before : Frame sources contract rules slots)
    (request : Deduction.Request rules) (leftSlot : Ref slots left) (rightSlot : Ref slots right)
    (demand : Deduction.Demand) (leftOccurrence rightOccurrence : Occurrence before.store)
    (leftActual : before.bindings leftSlot = some leftOccurrence)
    (rightActual : before.bindings rightSlot = some rightOccurrence)
    (decision : Deduction.Decision before.store.2 request leftOccurrence.2 rightOccurrence.2)
    (step : Actual (deductionStep before request leftSlot rightSlot demand leftOccurrence rightOccurrence leftActual rightActual decision))
    (reader : ControlMeasuredAssignmentReader.Reader before.dossier.cursor.assignment.reader) :
    ControlMeasuredAssignmentReader.Reader step.1.next.dossier.cursor.assignment.reader := by
  obtain ⟨_, actual⟩ := step; cases actual; cases decision <;> exact reader

@[inline] def quotationRoot (before : Frame sources contract rules slots)
    (task : Dossier.Obligation context) (produced : Dossier.Step before.dossier task)
    (step : Actual (quotationStep before task produced))
    (root : Actual (EndogenousDecomposition.constructMeasuredOperationalRoot produced.1.next.state.searchSeed)) :
    Actual (EndogenousDecomposition.constructMeasuredOperationalRoot step.1.next.dossier.cursor.state.searchSeed) := by
  obtain ⟨_, actual⟩ := step; cases actual
  obtain ⟨stage, decision⟩ := produced; cases decision <;> exact root

@[inline] def missingRoot {left right : Specification} (before : Frame sources contract rules slots)
    (request : Deduction.Request rules) (leftSlot : Ref slots left) (rightSlot : Ref slots right)
    (demand : Deduction.Demand) (missing : Complete before → False)
    (step : Actual (missingStep before request leftSlot rightSlot demand missing))
    (root : Actual (EndogenousDecomposition.constructMeasuredOperationalRoot before.dossier.cursor.state.searchSeed)) :
    Actual (EndogenousDecomposition.constructMeasuredOperationalRoot step.1.next.dossier.cursor.state.searchSeed) := by
  obtain ⟨_, actual⟩ := step; cases actual; exact root

@[inline] def deductionRoot {left right : Specification} (before : Frame sources contract rules slots)
    (request : Deduction.Request rules) (leftSlot : Ref slots left) (rightSlot : Ref slots right)
    (demand : Deduction.Demand) (leftOccurrence rightOccurrence : Occurrence before.store)
    (leftActual : before.bindings leftSlot = some leftOccurrence)
    (rightActual : before.bindings rightSlot = some rightOccurrence)
    (decision : Deduction.Decision before.store.2 request leftOccurrence.2 rightOccurrence.2)
    (step : Actual (deductionStep before request leftSlot rightSlot demand leftOccurrence rightOccurrence leftActual rightActual decision))
    (root : Actual (EndogenousDecomposition.constructMeasuredOperationalRoot before.dossier.cursor.state.searchSeed)) :
    Actual (EndogenousDecomposition.constructMeasuredOperationalRoot step.1.next.dossier.cursor.state.searchSeed) := by
  obtain ⟨_, actual⟩ := step; cases actual; cases decision <;> exact root

def code (before : FrameData sources contract rules slots)
    (instruction : Instruction context rules slots spec) (realized : Realized before) : Code Label (Produced before instruction) :=
  .step .frameRestore (fun _ =>
    let frame : Frame sources contract rules slots :=
      ⟨before.dossier, before.store, before.bindings.read⟩
    .step .controlClosure (fun _ =>
      let bindingReader := ControlBindingReader.tableReader before.bindings
      .step .instruction (fun _ => match instruction with
    | .quotation task => (ControlMeasuredMaster.runFromRootCode before.dossier task realized.masterReader realized.masterRoot).bind (fun actual =>
        (ControlAssemblyExecution.quotationCode frame bindingReader realized.knowledgeRecipe task actual.run.1).bind (fun assembled =>
          let step : ControlStep.Packet before (.quotation task) :=
            ⟨assembled.step.1, assembled.step.2.trans (congrArg (quotationStep frame task) actual.run.2)⟩
          finishCode before (.quotation task) step assembled.bindings assembled.knowledge
            (quotationReader frame task actual.run.1 assembled.step actual.reader)
            (quotationRoot frame task actual.run.1 assembled.step actual.root)))
    | .conclusion request leftSlot rightSlot demand =>
        (bindingReader.readCode leftSlot).bind (fun leftRead =>
          match leftActual : leftRead.1 with
          | none =>
              let absent := leftRead.2.symm.trans leftActual
              let missing : Complete frame → False := fun complete => by
                have impossible := absent.symm.trans (complete leftSlot).actual
                cases impossible
              (ControlAssemblyExecution.missingCode frame bindingReader realized.knowledgeRecipe request leftSlot rightSlot demand missing).bind (fun assembled =>
                let step : ControlStep.Packet before (.conclusion request leftSlot rightSlot demand) :=
                  ⟨assembled.step.1, by
                  dsimp only [Program.step]
                  split
                  · exact assembled.step.2
                  · rename_i occurrence found
                    cases absent.symm.trans found⟩
                finishCode before (.conclusion request leftSlot rightSlot demand) step assembled.bindings assembled.knowledge
                  (missingReader frame request leftSlot rightSlot demand missing assembled.step realized.masterReader)
                  (missingRoot frame request leftSlot rightSlot demand missing assembled.step realized.masterRoot))
          | some leftOccurrence =>
              (bindingReader.readCode rightSlot).bind (fun rightRead =>
                match rightActual : rightRead.1 with
                | none =>
                  let absent := rightRead.2.symm.trans rightActual
                  let missing : Complete frame → False := fun complete => by
                    have impossible := absent.symm.trans (complete rightSlot).actual
                    cases impossible
                  (ControlAssemblyExecution.missingCode frame bindingReader realized.knowledgeRecipe request leftSlot rightSlot demand missing).bind (fun assembled =>
                    let step : ControlStep.Packet before (.conclusion request leftSlot rightSlot demand) :=
                  ⟨assembled.step.1, by
                      dsimp only [Program.step]
                      split
                      · rename_i leftMissing; cases (leftRead.2.symm.trans leftActual).symm.trans leftMissing
                      · rename_i occurrence found
                        have same := Option.some.inj ((leftRead.2.symm.trans leftActual).symm.trans found)
                        cases same
                        split
                        · exact assembled.step.2
                        · rename_i rightOccurrence foundRight
                          cases absent.symm.trans foundRight⟩
                    finishCode before (.conclusion request leftSlot rightSlot demand) step assembled.bindings assembled.knowledge
                  (missingReader frame request leftSlot rightSlot demand missing assembled.step realized.masterReader)
                  (missingRoot frame request leftSlot rightSlot demand missing assembled.step realized.masterRoot))
                | some rightOccurrence =>
                  (ControlDeduction.code before.store.2 request
                    leftOccurrence.2 rightOccurrence.2).bind (fun actualDecision =>
                    let foundLeft := leftRead.2.symm.trans leftActual
                    let foundRight := rightRead.2.symm.trans rightActual
                    let decision := actualDecision.1
                    (ControlAssemblyExecution.deductionCode frame bindingReader realized.knowledgeRecipe request leftSlot rightSlot demand
                      leftOccurrence rightOccurrence foundLeft foundRight decision).bind (fun assembled =>
                    let step : ControlStep.Packet before (.conclusion request leftSlot rightSlot demand) :=
                  ⟨assembled.step.1, by
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
                          exact assembled.step.2.trans (congrArg
                            (fun decision => deductionStep frame request leftSlot rightSlot demand
                              leftOccurrence rightOccurrence foundLeft foundRight decision) actualDecision.2)⟩
                    finishCode before (.conclusion request leftSlot rightSlot demand) step assembled.bindings assembled.knowledge
                  (deductionReader frame request leftSlot rightSlot demand leftOccurrence rightOccurrence
                        foundLeft foundRight decision assembled.step realized.masterReader)
                  (deductionRoot frame request leftSlot rightSlot demand leftOccurrence rightOccurrence
                    foundLeft foundRight decision assembled.step realized.masterRoot))))))))

theorem finite (before : FrameData sources contract rules slots)
    (instruction : Instruction context rules slots spec) (realized : Realized before) :
    Finite (code before instruction realized) := by
  apply finite_step; apply finite_step; apply finite_step
  cases instruction with
  | quotation task =>
    apply finite_bind (ControlMeasuredMaster.run_from_root_finite _ _ _ _); intro actual
    apply finite_bind (ControlAssemblyExecution.quotation_finite _ _ _ _ _); intro assembled
    exact finish_finite _ _ _ _ _ _ _
  | conclusion request leftSlot rightSlot demand =>
    apply finite_bind ((ControlBindingReader.tableReader before.bindings).finite leftSlot); intro leftRead
    split
    · apply finite_bind (ControlAssemblyExecution.missing_finite _ _ _ _ _ _ _ _); intro assembled
      exact finish_finite _ _ _ _ _ _ _
    · apply finite_bind ((ControlBindingReader.tableReader before.bindings).finite rightSlot); intro rightRead
      split
      · apply finite_bind (ControlAssemblyExecution.missing_finite _ _ _ _ _ _ _ _); intro assembled
        exact finish_finite _ _ _ _ _ _ _
      · apply finite_bind (ControlDeduction.finite _ _ _ _); intro decision
        apply finite_bind (ControlAssemblyExecution.deduction_finite _ _ _ _ _ _ _ _ _ _ _ _); intro assembled
        exact finish_finite _ _ _ _ _ _ _

end ConstitutiveSearch.Agent.Local.Documentary.ControlFrameExecution

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrameExecution.Realized
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrameExecution.Produced
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrameExecution.formCode
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrameExecution.form_finite
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrameExecution.finishCode
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrameExecution.finish_finite
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrameExecution.quotationReader
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrameExecution.missingReader
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrameExecution.deductionReader
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrameExecution.code
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrameExecution.finite
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrameExecution.quotationRoot
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrameExecution.missingRoot
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrameExecution.deductionRoot
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlFrameExecution.formedRoot
/- AXIOM_AUDIT_END -/
