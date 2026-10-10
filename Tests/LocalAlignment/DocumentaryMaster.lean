import Tests.LocalAlignment.DocumentarySelection
import RelationalPerimeter.Computation.ConstitutiveSearch.EndogenousDecomposition.VariableMasterExecution

/-! Semantic two-source application of the existing master. One actual head
supplies both the discovered variable and the successor. Source checks determine
the received SAT problem; actual opening and normalization determine the readout. -/
set_option genInjectivity false
set_option maxHeartbeats 2000000
namespace ConstitutiveSearch.Agent.Local.Documentary.Master
open Resources SAT Selection
open EndogenousDecomposition

structure Stage {context} (cursor : MasterResources.Cursor) (sources : Support SourceValue context)
    (contract : Contract) (demand : Demand) (left right : Location context) where
  private mk ::
  head : VariableMaster.MasterHead cursor
  headExact : head = VariableMaster.masterHead cursor
  leftCheck : Checked sources contract demand left
  leftExact : leftCheck = check sources contract demand left
  rightCheck : Checked sources contract demand right
  rightExact : rightCheck = check sources contract demand right
  opening : VariableMaster.Opening (choiceFormula (VariableMaster.selected head) leftCheck.flag rightCheck.flag)
    [GeneratedStructuralBranchContext.root
      (choiceFormula (VariableMaster.selected head) leftCheck.flag rightCheck.flag)]
  openingExact : opening = VariableMaster.openFrontier _ (VariableMaster.selected head) _
  reduction : VariableMaster.Reduction _ (VariableMaster.selected head) opening
  reductionExact : reduction = normalizeGeneratedStructuralFrontierByFlip _ (VariableMaster.selected head) opening.frontier

def search {context} (cursor : MasterResources.Cursor) (sources : Support SourceValue context)
    (contract : Contract) (demand : Demand) (left right : Location context) :
    Stage cursor sources contract demand left right :=
  let head := VariableMaster.masterHead cursor
  let leftCheck := check sources contract demand left
  let rightCheck := check sources contract demand right
  let formula := choiceFormula (VariableMaster.selected head) leftCheck.flag rightCheck.flag
  let opening := VariableMaster.openFrontier formula (VariableMaster.selected head) [GeneratedStructuralBranchContext.root formula]
  let reduction := normalizeGeneratedStructuralFrontierByFlip formula (VariableMaster.selected head) opening.frontier
  ⟨head, rfl, leftCheck, rfl, rightCheck, rfl, opening, rfl, reduction, rfl⟩

/-- Assemble the same stage from actual paid computations. Equalities specify
the original API; they do not invoke its producers at runtime. -/
def stageFromParts {context} (cursor : MasterResources.Cursor) (sources : Support SourceValue context)
    (contract : Contract) (demand : Demand) (left right : Location context)
    (head : VariableMaster.MasterHead cursor) (headExact : head = VariableMaster.masterHead cursor)
    (leftCheck : Checked sources contract demand left)
    (leftExact : leftCheck = check sources contract demand left)
    (rightCheck : Checked sources contract demand right)
    (rightExact : rightCheck = check sources contract demand right)
    (opening : VariableMaster.Opening (choiceFormula (VariableMaster.selected head) leftCheck.flag rightCheck.flag)
      [GeneratedStructuralBranchContext.root (choiceFormula (VariableMaster.selected head) leftCheck.flag rightCheck.flag)])
    (openingExact : opening = VariableMaster.openFrontier _ (VariableMaster.selected head) _)
    (reduction : VariableMaster.Reduction _ (VariableMaster.selected head) opening)
    (reductionExact : reduction = normalizeGeneratedStructuralFrontierByFlip _
      (VariableMaster.selected head) opening.frontier) : Stage cursor sources contract demand left right :=
  ⟨head, headExact, leftCheck, leftExact, rightCheck, rightExact,
    opening, openingExact, reduction, reductionExact⟩

theorem stageFromParts_actual {context} (cursor : MasterResources.Cursor)
    (sources : Support SourceValue context) (contract : Contract) (demand : Demand)
    (left right : Location context) (head : VariableMaster.MasterHead cursor)
    (headExact : head = VariableMaster.masterHead cursor)
    (leftCheck : Checked sources contract demand left)
    (leftExact : leftCheck = check sources contract demand left)
    (rightCheck : Checked sources contract demand right)
    (rightExact : rightCheck = check sources contract demand right)
    (opening : VariableMaster.Opening (choiceFormula (VariableMaster.selected head) leftCheck.flag rightCheck.flag)
      [GeneratedStructuralBranchContext.root (choiceFormula (VariableMaster.selected head) leftCheck.flag rightCheck.flag)])
    (openingExact : opening = VariableMaster.openFrontier _ (VariableMaster.selected head) _)
    (reduction : VariableMaster.Reduction _ (VariableMaster.selected head) opening)
    (reductionExact : reduction = normalizeGeneratedStructuralFrontierByFlip _
      (VariableMaster.selected head) opening.frontier) :
    stageFromParts cursor sources contract demand left right head headExact
      leftCheck leftExact rightCheck rightExact opening openingExact reduction reductionExact =
      search cursor sources contract demand left right := by
  cases headExact
  cases leftExact
  cases rightExact
  cases openingExact
  cases reductionExact
  rfl

def Stage.formula {context cursor sources contract demand left right}
    (stage : @Stage context cursor sources contract demand left right) : Cnf :=
  choiceFormula (VariableMaster.selected stage.head) stage.leftCheck.flag stage.rightCheck.flag

def Stage.preservation {context cursor sources contract demand left right}
    (stage : @Stage context cursor sources contract demand left right) :
    AcceptedFrontierPreservation (generatedStructuralBranchSystem stage.formula)
      [GeneratedStructuralBranchContext.root stage.formula] stage.reduction.retained :=
  stage.opening.preservation.trans stage.reduction.preservation

def Stage.next {context cursor sources contract demand left right}
    (stage : @Stage context cursor sources contract demand left right) : MasterResources.Cursor := stage.head.next

theorem Stage.next_exact {context cursor sources contract demand left right}
    (stage : @Stage context cursor sources contract demand left right) :
    stage.next.boundary = ⟨cursor.depth + 1, stage.head.head.stage.next,
      stage.head.head.run.nextRun.next, stage.head.head.production.nextContext⟩ :=
  stage.head.boundaryExact

def Stage.candidate {context cursor sources contract demand left right}
    (stage : @Stage context cursor sources contract demand left right)
    (assignment : Assignment) (accepted : Satisfies assignment stage.formula) :
    Candidate sources contract demand := by
  have eligible := (choiceFormula_exact (VariableMaster.selected stage.head) stage.leftCheck.flag
    stage.rightCheck.flag assignment).1 accepted
  cases value : assignment (VariableMaster.selected stage.head)
  · rw [value] at eligible
    exact stage.leftCheck.candidate eligible
  · rw [value] at eligible
    exact stage.rightCheck.candidate eligible

/-- The paid assignment bit selects the actual checked occurrence. -/
def Stage.candidateFromBit {context cursor sources contract demand left right}
    (stage : @Stage context cursor sources contract demand left right)
    (assignment : Assignment) (accepted : Satisfies assignment stage.formula)
    (bit : {bit : Bool // bit = assignment (VariableMaster.selected stage.head)}) :
    Candidate sources contract demand := by
  have eligible := (choiceFormula_exact (VariableMaster.selected stage.head) stage.leftCheck.flag
    stage.rightCheck.flag assignment).1 accepted
  rw [← bit.2] at eligible
  cases value : bit.1
  · rw [value] at eligible
    exact stage.leftCheck.candidate eligible
  · rw [value] at eligible
    exact stage.rightCheck.candidate eligible

theorem Stage.candidateFromBit_actual {context cursor sources contract demand left right}
    (stage : @Stage context cursor sources contract demand left right)
    (assignment : Assignment) (accepted : Satisfies assignment stage.formula)
    (bit : {bit : Bool // bit = assignment (VariableMaster.selected stage.head)}) :
    stage.candidateFromBit assignment accepted bit = stage.candidate assignment accepted := by
  obtain ⟨bit, actual⟩ := bit
  cases actual
  unfold Stage.candidateFromBit Stage.candidate
  dsimp only

/-- The packet stores the actual retained continuation, produced action, authorized
element and goal witness. Its construction shares these productions. The associated
stage carries the produced successor returned with the decision by `run`. -/
structure Completion {context cursor sources contract demand left right}
    (stage : @Stage context cursor sources contract demand left right)
    (memory : Memory sources contract) where
  private mk ::
  continuation : FrontierContinuation (generatedStructuralBranchSystem stage.formula)
    stage.reduction.retained
  accepted : FrontierAccept (generatedStructuralBranchSystem stage.formula)
    stage.reduction.retained continuation
  candidate : Candidate sources contract demand
  candidateExact : candidate = stage.candidate (frontierAssignment continuation)
    (frontier_root_accept continuation accepted)
  action : Extraction sources candidate.origin
  actionExact : action = extract sources candidate.origin
  output : Output sources contract
  outputExact : output = authorize contract action candidate.permission
  result : Memory sources contract × Citation
  resultExact : result = incorporate memory output
  meets : Meets demand result.2
  goal : Goal [demand] result.1.items

def complete {context cursor sources contract demand left right}
    (stage : @Stage context cursor sources contract demand left right)
    (memory : Memory sources contract)
    (continuation : FrontierContinuation (generatedStructuralBranchSystem stage.formula)
      stage.reduction.retained)
    (accepted : FrontierAccept (generatedStructuralBranchSystem stage.formula)
      stage.reduction.retained continuation) : Completion stage memory :=
  let candidate := stage.candidate (frontierAssignment continuation)
    (frontier_root_accept continuation accepted)
  let action := extract sources candidate.origin
  let output := authorize contract action candidate.permission
  let result := incorporate memory output
  have meets : Meets demand result.2 := by
    change Meets demand action.citation
    rw [action.citation_exact]
    exact candidate.meets
  ⟨continuation, accepted, candidate, rfl, action, rfl, output, rfl, result, rfl,
    meets, .cons demand result.2 .here meets (.nil _)⟩

/-- Assemble the completion from its actual controlled productions. -/
def completionFromParts {context cursor sources contract demand left right}
    (stage : @Stage context cursor sources contract demand left right) (memory : Memory sources contract)
    (continuation : FrontierContinuation (generatedStructuralBranchSystem stage.formula) stage.reduction.retained)
    (accepted : FrontierAccept (generatedStructuralBranchSystem stage.formula) stage.reduction.retained continuation)
    (candidate : Candidate sources contract demand)
    (candidateExact : candidate = stage.candidate (frontierAssignment continuation) (frontier_root_accept continuation accepted))
    (action : Extraction sources candidate.origin) (actionExact : action = extract sources candidate.origin)
    (output : Output sources contract) (outputExact : output = authorize contract action candidate.permission)
    (result : Memory sources contract × Citation) (resultExact : result = incorporate memory output) :
    Completion stage memory := by
  have meets : Meets demand result.2 := by
    rw [resultExact, outputExact]
    change Meets demand action.citation
    rw [action.citation_exact]
    exact candidate.meets
  have located : Ref result.1.items result.2 :=
    resultExact.symm ▸ (Ref.here : Ref (incorporate memory output).1.items (incorporate memory output).2)
  exact ⟨continuation, accepted, candidate, candidateExact, action, actionExact,
    output, outputExact, result, resultExact, meets, .cons demand result.2 located meets (.nil _)⟩

theorem completionFromParts_actual {context cursor sources contract demand left right}
    (stage : @Stage context cursor sources contract demand left right) (memory : Memory sources contract)
    (continuation : FrontierContinuation (generatedStructuralBranchSystem stage.formula) stage.reduction.retained)
    (accepted : FrontierAccept (generatedStructuralBranchSystem stage.formula) stage.reduction.retained continuation)
    (candidate : Candidate sources contract demand)
    (candidateExact : candidate = stage.candidate (frontierAssignment continuation) (frontier_root_accept continuation accepted))
    (action : Extraction sources candidate.origin) (actionExact : action = extract sources candidate.origin)
    (output : Output sources contract) (outputExact : output = authorize contract action candidate.permission)
    (result : Memory sources contract × Citation) (resultExact : result = incorporate memory output) :
    completionFromParts stage memory continuation accepted candidate candidateExact action actionExact
      output outputExact result resultExact = complete stage memory continuation accepted := by
  cases candidateExact
  cases actionExact
  cases outputExact
  cases resultExact
  rfl

inductive Decision {context cursor sources contract demand left right}
    (stage : @Stage context cursor sources contract demand left right)
    (memory : Memory sources contract) where
  | complete (packet : Completion stage memory)
  | blocked
      (leftImpossible : Ref contract.allowed left.2.position →
        Meets demand (sourceCitation sources left) → False)
      (rightImpossible : Ref contract.allowed right.2.position →
        Meets demand (sourceCitation sources right) → False)

/-- The seed is a primitive accepted assignment. The actual routing transforms it;
the eventual documentary origin is read from that transformed continuation. -/
def decide {context cursor sources contract demand left right}
    (stage : @Stage context cursor sources contract demand left right)
    (memory : Memory sources contract) : Decision stage memory :=
  match seed (VariableMaster.selected stage.head) stage.leftCheck.flag stage.rightCheck.flag with
  | .blocked impossible =>
      .blocked
        (fun permission meets => impossible false (stage.leftCheck.complete permission meets))
        (fun permission meets => impossible true (stage.rightCheck.complete permission meets))
  | .viable assignment accepted =>
      let input : FrontierContinuation (generatedStructuralBranchSystem stage.formula)
          [GeneratedStructuralBranchContext.root stage.formula] := .head ⟨assignment, True.intro⟩
      let preservation := stage.preservation
      let retained := preservation.forward.map input
      let retainedAccepted := preservation.forward.preservesAccept input accepted
      .complete (complete stage memory retained retainedAccepted)

def run {context} (cursor : MasterResources.Cursor) (sources : Support SourceValue context)
    (contract : Contract) (demand : Demand) (left right : Location context)
    (memory : Memory sources contract) :
    (stage : Stage cursor sources contract demand left right) × Decision stage memory :=
  let stage := search cursor sources contract demand left right
  ⟨stage, decide stage memory⟩

def Decision.result {context cursor sources contract demand left right}
    {stage : @Stage context cursor sources contract demand left right}
    {memory : Memory sources contract} : Decision stage memory →
      Memory sources contract × Option Citation
  | .complete packet => (packet.result.1, some packet.result.2)
  | .blocked _ _ => (memory, none)

/-- Local progress for every received pair having at least one eligible source.
The goal concerns the result of this actual decision, not an alternative run. -/
theorem decide_goal {context cursor sources contract demand left right}
    (stage : @Stage context cursor sources contract demand left right)
    (memory : Memory sources contract)
    (eligible : stage.leftCheck.flag = true ∨ stage.rightCheck.flag = true) :
    Nonempty (Goal [demand] (decide stage memory).result.1.items) := by
  unfold decide
  split
  · rename_i impossible seedExact
    cases eligible with
    | inl left => exact False.elim (impossible false left)
    | inr right => exact False.elim (impossible true right)
  · rename_i assignment accepted seedExact
    exact ⟨(complete stage memory
      (stage.preservation.forward.map (.head ⟨assignment, True.intro⟩))
      (stage.preservation.forward.preservesAccept
        (.head ⟨assignment, True.intro⟩) accepted)).goal⟩

theorem Decision.actual_output_conforms {context cursor sources contract demand left right}
    {stage : @Stage context cursor sources contract demand left right} {memory}
    (decision : Decision stage memory) {item}
    (returned : decision.result.2 = some item) :
    Nonempty (Conforms sources contract item) := by
  cases decision with
  | blocked _ _ => cases returned
  | complete packet =>
      have same : packet.result.2 = item := Option.some.inj returned
      cases same
      rw [packet.resultExact]
      exact ⟨(incorporate memory packet.output).1.valid .here⟩

theorem Decision.actual_output_meets {context cursor sources contract demand left right}
    {stage : @Stage context cursor sources contract demand left right} {memory}
    (decision : Decision stage memory) {item}
    (returned : decision.result.2 = some item) : Meets demand item := by
  cases decision with
  | blocked _ _ => cases returned
  | complete packet =>
      have same : packet.result.2 = item := Option.some.inj returned
      exact same ▸ packet.meets

theorem Completion.actual_item {context cursor sources contract demand left right}
    {stage : @Stage context cursor sources contract demand left right} {memory}
    (packet : Completion stage memory) : packet.result.2 = packet.action.citation := by
  rw [packet.resultExact, packet.outputExact]
  rfl

theorem Completion.actual_origin {context cursor sources contract demand left right}
    {stage : @Stage context cursor sources contract demand left right} {memory}
    (packet : Completion stage memory) :
    packet.result.2.position = packet.candidate.origin.2.position := by
  rw [packet.actual_item]
  rfl

theorem Completion.items_exact {context cursor sources contract demand left right}
    {stage : @Stage context cursor sources contract demand left right} {memory}
    (packet : Completion stage memory) :
    packet.result.1.items = packet.result.2 :: memory.items := by
  rw [packet.resultExact]
  rfl

theorem Completion.old_source_read {context cursor sources contract demand left right}
    {stage : @Stage context cursor sources contract demand left right} {memory}
    (packet : Completion stage memory) {key} (old : Ref context key) :
    packet.action.resources.read (packet.action.transport.references old) = sources.read old :=
  packet.action.old_read old

theorem Completion.conforming {context cursor sources contract demand left right}
    {stage : @Stage context cursor sources contract demand left right} {memory}
    (packet : Completion stage memory) : Nonempty (Conforms sources contract packet.result.2) := by
  rw [packet.resultExact]
  exact ⟨(incorporate memory packet.output).1.valid .here⟩

end ConstitutiveSearch.Agent.Local.Documentary.Master
/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Master.Stage
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Master.search
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Master.stageFromParts
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Master.stageFromParts_actual
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Master.Stage.formula
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Master.Stage.preservation
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Master.Stage.next
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Master.Stage.next_exact
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Master.Stage.candidate
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Master.Stage.candidateFromBit
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Master.Stage.candidateFromBit_actual
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Master.Completion
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Master.complete
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Master.completionFromParts
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Master.completionFromParts_actual
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Master.Decision
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Master.decide
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Master.run
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Master.Decision.result
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Master.decide_goal
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Master.Decision.actual_output_conforms
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Master.Decision.actual_output_meets
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Master.Completion.actual_item
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Master.Completion.actual_origin
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Master.Completion.items_exact
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Master.Completion.old_source_read
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Master.Completion.conforming
/- AXIOM_AUDIT_END -/
