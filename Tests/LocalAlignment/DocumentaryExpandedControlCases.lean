import Tests.LocalAlignment.DocumentaryControlInterpreterCases
import Tests.LocalAlignment.DocumentaryControlDeferred
import Tests.LocalAlignment.DocumentaryControlAdministration

/-! Concrete failure, restoration and administrative cost cases. Historical
Code traces remain qualified separately; these use the expanded execution. -/
set_option genInjectivity false
set_option maxRecDepth 8192
set_option maxHeartbeats 30000000
namespace ConstitutiveSearch.Agent.Local.Documentary.ExpandedControlCases
open Resources Program Snapshot Control ControlBindings ControlInterpreterCases

def leftExecution := Control.execute 8 (ControlStep.expandedCode refusedFrame leftMissing)
def rightExecution := Control.execute 10 (ControlStep.expandedCode refusedFrame rightMissing)
def forbiddenExecution := Control.execute 24 (ControlStep.expandedCode twoFrame forbiddenInstruction)

theorem left_event : (leftExecution.get (by rfl)).value.1.event = .missing := rfl
theorem left_trace : (leftExecution.get (by rfl)).labels =
    [.frameRestore, .instruction, .binding, .missingAssembly, .assemblyExtension,
      .assemblyOutput, .assemblyFrame, .assemblyPacket] := rfl
theorem left_one_short : (Control.execute 7 (ControlStep.expandedCode refusedFrame leftMissing)).isSome = false := rfl
theorem right_event : (rightExecution.get (by rfl)).value.1.event = .missing := rfl
theorem right_one_short : (Control.execute 9 (ControlStep.expandedCode refusedFrame rightMissing)).isSome = false := rfl
theorem forbidden_event : (forbiddenExecution.get (by rfl)).value.1.event = .refused := rfl
theorem forbidden_one_short : (Control.execute 23 (ControlStep.expandedCode twoFrame forbiddenInstruction)).isSome = false := rfl

def oneCode : Code Label Nat := .step .instruction (fun _ => .done 3)
def adminOne := Control.execute 21 (ControlAdministration.executeCode 1 oneCode)

theorem admin_done : (Control.execute 4 (ControlAdministration.executeCode 0 (.done (Label := Label) 3))).isSome = true := rfl
theorem admin_done_short : (Control.execute 3 (ControlAdministration.executeCode 0 (.done (Label := Label) 3))).isSome = false := rfl
theorem admin_one : adminOne.isSome = true := rfl
theorem admin_one_short : (Control.execute 20 (ControlAdministration.executeCode 1 oneCode)).isSome = false := rfl
theorem admin_source_trace : ((adminOne.get (by rfl)).value.1.get (by rfl)).labels = [.instruction] := rfl
theorem admin_source_value : ((adminOne.get (by rfl)).value.1.get (by rfl)).value = 3 := rfl
theorem admin_source_expires :
    ((Control.execute 2 (ControlAdministration.executeCode 0 oneCode)).get (by rfl)).value.1 = none := rfl

theorem after_reset {context : List SourceKey} {sources : Support SourceValue context}
    {contract : Contract} {rules : Deduction.Policy} {Context : Type} {final : List Specification}
    (before : PresentData sources contract rules Context final) (policy : Adaptive.Policy Context)
    {spec : Specification} (instruction : Instruction context rules before.slots spec) :
    ControlStep.expandedCode (before.reset policy).session.frame instruction =
      ControlStep.expandedCode before.session.frame instruction := rfl

theorem forgotten_same :
    ControlStep.expandedCode (Memory.project MemoryCases.leftProduced.1).session.frame
        (.quotation ProgramCases.revisedTask) =
      ControlStep.expandedCode (Memory.project MemoryCases.rightProduced.1).session.frame
        (.quotation ProgramCases.revisedTask) := rfl

def shortComparator := ControlMeasuredComparison.listCode
  EndogenousDecomposition.compareMeasuredLiteral ControlMeasuredComparison.literalCode
  [SAT.Literal.positive 0, .positive 100] [SAT.Literal.negative 0, .negative 100]

theorem comparator_short_circuit : (Control.execute 3 shortComparator).isSome = true := rfl
theorem comparator_one_short : (Control.execute 2 shortComparator).isSome = false := rfl
theorem comparator_short_trace : ((Control.execute 3 shortComparator).get (by rfl)).labels =
    [.masterConstructionCell, .masterConstructionCell, .masterConstructionReturn] := rfl

def repeatedState := (SAT.GeneratedStructuralBranchContext.root []).child 1 false
  (SAT.structuralDecisionsAvoid_of_check_true 1 [] rfl)
def repeatedCandidate := ControlMeasuredDiscovery.candidateCode repeatedState 1
theorem repeated_success : (Control.execute 6 repeatedCandidate).isSome = true := rfl
theorem repeated_short : (Control.execute 5 repeatedCandidate).isSome = false := rfl
theorem repeated_no_endpoint : ((Control.execute 6 repeatedCandidate).get (by rfl)).value.1.produced? = none := rfl
theorem repeated_trace : ((Control.execute 6 repeatedCandidate).get (by rfl)).labels =
    [.masterConstructionCell, .naturalComparison, .naturalComparison,
      .masterConstructionReturn, .masterConstructionReturn, .masterCandidateReturn] := rfl

def emptyCandidate := ControlMeasuredDiscovery.candidateCode (SAT.GeneratedStructuralBranchContext.root []) 0
def emptyCandidateExecution := Control.execute 500 emptyCandidate
def mismatchFormula := ControlMeasuredDiscovery.relationCode 0
  (SAT.GeneratedStructuralBranchContext.root [[SAT.Literal.positive 0]])
  (SAT.GeneratedStructuralBranchContext.root [[SAT.Literal.positive 0]])
def mismatchHistory := ControlMeasuredDiscovery.relationCode 1 repeatedState repeatedState

def transportState := SAT.GeneratedStructuralBranchContext.root []
def transportRelation : SAT.GeneratedStructuralFlipAtRelation 0 transportState transportState := ⟨rfl, rfl⟩
def transportInput : SAT.GeneratedStructuralBranchContinuation transportState := ⟨fun _ => false, True.intro⟩
def transportIdentity := ControlMeasuredTransport.flipCode 0 (.identity transportState) transportInput
def transportAtom := ControlMeasuredTransport.flipCode 0 (.atom transportRelation) transportInput
def transportComposition := ControlMeasuredTransport.flipCode 0
  (.compose (.atom transportRelation) (.atom transportRelation)) transportInput

theorem transport_identity_exact : (Control.execute 2 transportIdentity).isSome = true := rfl
theorem transport_identity_short : (Control.execute 1 transportIdentity).isSome = false := rfl
theorem transport_atom_exact : (Control.execute 5 transportAtom).isSome = true := rfl
theorem transport_atom_short : (Control.execute 4 transportAtom).isSome = false := rfl
theorem transport_atom_bit : ((Control.execute 5 transportAtom).get (by rfl)).value.1.output.1 0 = true := rfl
theorem transport_composition_exact : (Control.execute 18 transportComposition).isSome = true := rfl
theorem transport_composition_short : (Control.execute 17 transportComposition).isSome = false := rfl
theorem transport_composition_atoms :
    ((Control.execute 18 transportComposition).get (by rfl)).value.1.evaluatedAtoms = 2 := rfl
theorem transport_composition_applications :
    ((Control.execute 18 transportComposition).get (by rfl)).value.1.continuationApplications = 2 := rfl
theorem transport_composition_bit :
    ((Control.execute 18 transportComposition).get (by rfl)).value.1.output.1 0 = false := rfl

end ConstitutiveSearch.Agent.Local.Documentary.ExpandedControlCases

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ExpandedControlCases.leftExecution
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ExpandedControlCases.rightExecution
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ExpandedControlCases.forbiddenExecution
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ExpandedControlCases.left_event
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ExpandedControlCases.left_trace
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ExpandedControlCases.left_one_short
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ExpandedControlCases.right_event
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ExpandedControlCases.right_one_short
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ExpandedControlCases.forbidden_event
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ExpandedControlCases.forbidden_one_short
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ExpandedControlCases.oneCode
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ExpandedControlCases.adminOne
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ExpandedControlCases.admin_done
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ExpandedControlCases.admin_done_short
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ExpandedControlCases.admin_one
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ExpandedControlCases.admin_one_short
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ExpandedControlCases.admin_source_trace
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ExpandedControlCases.admin_source_value
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ExpandedControlCases.admin_source_expires
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ExpandedControlCases.after_reset
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ExpandedControlCases.forgotten_same
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ExpandedControlCases.shortComparator
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ExpandedControlCases.comparator_short_circuit
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ExpandedControlCases.comparator_one_short
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ExpandedControlCases.comparator_short_trace
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ExpandedControlCases.repeatedState
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ExpandedControlCases.repeatedCandidate
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ExpandedControlCases.repeated_success
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ExpandedControlCases.repeated_short
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ExpandedControlCases.repeated_no_endpoint
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ExpandedControlCases.repeated_trace
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ExpandedControlCases.emptyCandidate
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ExpandedControlCases.emptyCandidateExecution
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ExpandedControlCases.mismatchFormula
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ExpandedControlCases.mismatchHistory
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ExpandedControlCases.transportState
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ExpandedControlCases.transportRelation
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ExpandedControlCases.transportInput
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ExpandedControlCases.transportIdentity
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ExpandedControlCases.transportAtom
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ExpandedControlCases.transportComposition
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ExpandedControlCases.transport_identity_exact
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ExpandedControlCases.transport_identity_short
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ExpandedControlCases.transport_atom_exact
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ExpandedControlCases.transport_atom_short
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ExpandedControlCases.transport_atom_bit
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ExpandedControlCases.transport_composition_exact
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ExpandedControlCases.transport_composition_short
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ExpandedControlCases.transport_composition_atoms
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ExpandedControlCases.transport_composition_applications
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ExpandedControlCases.transport_composition_bit
/- AXIOM_AUDIT_END -/
