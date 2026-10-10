import Tests.LocalAlignment.DocumentaryControlStep
import Tests.LocalAlignment.DocumentaryRecoveryDataCases

/-! Instrumented steps consume the received master and actual retained tables.
The executed sum keeps value and source identities. Refusal and missing inputs
remain executable without inventing an admissibility certificate. -/
set_option genInjectivity false
set_option maxRecDepth 8192
set_option maxHeartbeats 30000000
namespace ConstitutiveSearch.Agent.Local.Documentary.ControlInterpreterCases
open Resources Program Snapshot Control ControlBindings

def quoteFrame := MemoryCases.boot.session.frame
def quoteInstruction : Instruction Cases.context DeductionCases.policy [] ProgramCases.baselineSpec :=
  .quotation ProgramCases.baselineTask

def twoQuotes := Program.execute ProgramCases.start
  (.cons (.quotation ProgramCases.baselineTask) (.cons (.quotation ProgramCases.revisedTask) .done))
def twoFrame := Snapshot.frame twoQuotes.1
def differenceInstruction : Instruction Cases.context DeductionCases.policy
    [ProgramCases.revisedSpec, ProgramCases.baselineSpec] ProgramCases.deltaSpec :=
  .conclusion DeductionCases.differenceRequest (.prior .here) .here DeductionCases.deltaDemand
def forbiddenInstruction : Instruction Cases.context DeductionCases.policy
    [ProgramCases.revisedSpec, ProgramCases.baselineSpec] (.conclusion DeductionCases.forbiddenDemand) :=
  .conclusion DeductionCases.duplicateRequest (.prior .here) .here DeductionCases.forbiddenDemand

def sumFrame := Snapshot.frame
  (Program.step ProgramCases.prefixRun.1 (.quotation ProgramCases.baselineTask)).next
def sumInstruction : Instruction Cases.context DeductionCases.policy
    [ProgramCases.baselineSpec, ProgramCases.deltaSpec, ProgramCases.revisedSpec, ProgramCases.baselineSpec]
    ProgramCases.sumSpec :=
  .conclusion DeductionCases.sumRequest (.prior .here) (.prior .here) DeductionCases.sumDemand
def sumExecution := Control.execute 17 (ControlStep.code sumFrame sumInstruction)
def sumActual := sumExecution.get (by rfl)
def sumInitial : Complete sumFrame.restore :=
  Snapshot.complete_forward _
    ((Program.step ProgramCases.prefixRun.1 (.quotation ProgramCases.baselineTask)).progress
      ProgramCases.baselineReady
      (ProgramCases.prefixRun.2.complete
        (.cons ProgramCases.baselineReady (.cons ProgramCases.revisedReady
          (.cons ProgramCases.differenceCompatible .done))) ProgramCases.initiallyComplete))
def sumComplete : Complete sumActual.value.1.next :=
  ControlStep.complete sumFrame sumInstruction 17 sumActual ProgramCases.sumCompatible sumInitial
def terminal := sumComplete (.here : Ref _ ProgramCases.sumSpec)

theorem terminal_value : sumActual.value.1.next.store.2.resources.read terminal.occurrence.2 = 2 :=
  terminal.meets.1
theorem terminal_origins : terminal.occurrence.1.origins = [1, 2, 1, 2] := terminal.meets.2.2
theorem sum_labels : sumActual.labels =
    [.instruction, .binding, .binding, .binding, .binding,
      .referencePosition, .referencePosition, .referenceReturn,
      .permissionCell, .naturalComparison, .permissionCell, .naturalComparison, .naturalComparison,
      .permissionReturn, .permissionReturn, .deductionProducer, .deductionAssembly] := rfl
theorem sum_one_short : (Control.execute 16 (ControlStep.code sumFrame sumInstruction)).isSome = false := rfl
theorem sum_surplus : runCtl 23 (ControlStep.code sumFrame sumInstruction) =
    runCtl 17 (ControlStep.code sumFrame sumInstruction) :=
  (ctl_mono 17 23 (code := ControlStep.code sumFrame sumInstruction)
    (value := sumActual.value) (labels := sumActual.labels) rfl (by decide)).trans rfl

def refusedFrame := Snapshot.frame (Program.step twoQuotes.1 forbiddenInstruction).next
def leftMissing : Instruction Cases.context DeductionCases.policy
    [.conclusion DeductionCases.forbiddenDemand, ProgramCases.revisedSpec, ProgramCases.baselineSpec]
    ProgramCases.sumSpec := .conclusion DeductionCases.sumRequest .here .here DeductionCases.sumDemand
def rightMissing : Instruction Cases.context DeductionCases.policy
    [.conclusion DeductionCases.forbiddenDemand, ProgramCases.revisedSpec, ProgramCases.baselineSpec]
    ProgramCases.sumSpec := .conclusion DeductionCases.sumRequest (.prior .here) .here DeductionCases.sumDemand

theorem forbidden_refused :
    ((Control.execute 19 (ControlStep.code twoFrame forbiddenInstruction)).get (by rfl)).value.1.event =
      .refused := rfl
theorem left_missing :
    ((Control.execute 3 (ControlStep.code refusedFrame leftMissing)).get (by rfl)).value.1.event =
      .missing := rfl
theorem right_missing :
    ((Control.execute 5 (ControlStep.code refusedFrame rightMissing)).get (by rfl)).value.1.event =
      .missing := rfl

def finalTable := (Snapshot.frame ProgramCases.actual.1).bindings
def oldest : Ref [ProgramCases.sumSpec, ProgramCases.baselineSpec, ProgramCases.deltaSpec,
    ProgramCases.revisedSpec, ProgramCases.baselineSpec] ProgramCases.baselineSpec :=
  .prior (.prior (.prior (.prior .here)))
def repeated : Ref [ProgramCases.sumSpec, ProgramCases.baselineSpec, ProgramCases.deltaSpec,
    ProgramCases.revisedSpec, ProgramCases.baselineSpec] ProgramCases.baselineSpec := .prior .here

theorem oldest_read : runCtl 5 (readCode finalTable oldest) =
    some (⟨finalTable.read oldest, rfl⟩, List.replicate 5 .binding) := read_within _ _ 5 (Nat.le_refl _)
theorem repeated_read : runCtl 2 (readCode finalTable repeated) =
    some (⟨finalTable.read repeated, rfl⟩, List.replicate 2 .binding) := read_within _ _ 2 (Nat.le_refl _)

theorem forgotten_same_code :
    ControlStep.code (Memory.project MemoryCases.leftProduced.1).session.frame
        (.quotation ProgramCases.revisedTask) =
      ControlStep.code (Memory.project MemoryCases.rightProduced.1).session.frame
        (.quotation ProgramCases.revisedTask) := rfl

def duplicatePermission :=
  (Control.execute 4 (ControlPermission.lookupCode [1, 1] 1)).get (by rfl)

theorem duplicate_permission_first :
    duplicatePermission.value.1 = some (.here : Ref [1, 1] 1) := rfl

theorem duplicate_permission_labels : duplicatePermission.labels =
    [.permissionCell, .naturalComparison, .naturalComparison, .permissionReturn] := rfl

theorem duplicate_permission_one_short :
    (Control.execute 3 (ControlPermission.lookupCode [1, 1] 1)).isSome = false := rfl

def laterPermission :=
  (Control.execute 14 (ControlPermission.lookupCode [3, 5, 5] 5)).get (by rfl)

theorem later_permission_first :
    laterPermission.value.1 = some (.prior .here : Ref [3, 5, 5] 5) := rfl

theorem later_permission_labels : laterPermission.labels =
    [.permissionCell, .naturalComparison, .naturalComparison, .naturalComparison, .naturalComparison,
      .permissionCell, .naturalComparison, .naturalComparison, .naturalComparison,
      .naturalComparison, .naturalComparison, .naturalComparison,
      .permissionReturn, .permissionReturn] := rfl

theorem empty_permission_paid :
    runCtl 1 (ControlPermission.lookupCode [] 7) =
      some (⟨none, rfl⟩, [.permissionCell]) := rfl

theorem duplicate_bound_conservative : ControlPermission.lookupBound [1, 1] 1 = 9 := rfl

end ConstitutiveSearch.Agent.Local.Documentary.ControlInterpreterCases

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlInterpreterCases.quoteFrame
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlInterpreterCases.quoteInstruction
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlInterpreterCases.twoQuotes
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlInterpreterCases.twoFrame
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlInterpreterCases.differenceInstruction
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlInterpreterCases.forbiddenInstruction
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlInterpreterCases.sumFrame
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlInterpreterCases.sumInstruction
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlInterpreterCases.sumExecution
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlInterpreterCases.sumActual
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlInterpreterCases.sumInitial
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlInterpreterCases.sumComplete
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlInterpreterCases.terminal
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlInterpreterCases.terminal_value
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlInterpreterCases.terminal_origins
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlInterpreterCases.sum_labels
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlInterpreterCases.sum_one_short
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlInterpreterCases.sum_surplus
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlInterpreterCases.refusedFrame
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlInterpreterCases.leftMissing
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlInterpreterCases.rightMissing
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlInterpreterCases.forbidden_refused
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlInterpreterCases.left_missing
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlInterpreterCases.right_missing
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlInterpreterCases.finalTable
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlInterpreterCases.oldest
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlInterpreterCases.repeated
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlInterpreterCases.oldest_read
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlInterpreterCases.repeated_read
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlInterpreterCases.forgotten_same_code
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlInterpreterCases.duplicatePermission
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlInterpreterCases.duplicate_permission_first
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlInterpreterCases.duplicate_permission_labels
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlInterpreterCases.duplicate_permission_one_short
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlInterpreterCases.laterPermission
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlInterpreterCases.later_permission_first
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlInterpreterCases.later_permission_labels
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlInterpreterCases.empty_permission_paid
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlInterpreterCases.duplicate_bound_conservative
/- AXIOM_AUDIT_END -/
