import Tests.LocalAlignment.DocumentaryControlMaster
import Tests.LocalAlignment.DocumentaryControlMasterHeadReader
import Tests.LocalAlignment.DocumentaryControlCeilingCompletion

/-! The same quotation master, with the measured reader of its actual successor
kept alongside the retained search and executable preservation. -/
set_option genInjectivity false
set_option backward.match.sparseCases false
set_option maxHeartbeats 4000000
namespace ConstitutiveSearch.Agent.Local.Documentary.ControlMeasuredMaster
open Resources Control ControlBindings EndogenousDecomposition ControlMaster ControlMeasuredAssignmentReader ControlMasterData

structure ProducedStage {context} (cursor : MasterResources.Cursor) (sources : Support SourceValue context)
    (contract : Contract) (demand : Demand) (left right : Location context) where
  stage : Search cursor sources contract demand left right
  payload : ControlStageCeilingExecution.Payload stage.1
  reader : Reader stage.1.next.assignment.reader
  root : Actual (constructMeasuredOperationalRoot stage.1.next.state.searchSeed)

def searchFromRootCode {context} (cursor : MasterResources.Cursor) (sources : Support SourceValue context)
    (contract : Contract) (demand : Demand) (left right : Location context)
    (reader : Reader cursor.assignment.reader)
    (root : Actual (constructMeasuredOperationalRoot cursor.state.searchSeed)) :
    Code Label (ProducedStage cursor sources contract demand left right) :=
  (ControlMasterHeadReader.codeFromRoot cursor reader root).bind (fun producedHead =>
    let actualHead := producedHead.head
    let head := actualHead.1
    (ControlSelection.checkCode sources contract demand left).bind (fun leftCheck =>
      (ControlSelection.checkCode sources contract demand right).bind (fun rightCheck =>
        .step .citationFormula (fun _ =>
          let formula := Selection.choiceFormula (VariableMaster.selected head) leftCheck.1.flag rightCheck.1.flag
          .step .citationOpening (fun _ =>
            (ControlFrontierCeilingOpening.code formula (VariableMaster.selected head)
              [SAT.GeneratedStructuralBranchContext.root formula]).bind (fun producedOpening =>
            let opening := producedOpening.opening.1
            .step .citationReduction (fun _ =>
              (ControlFrontierNormalization.code formula (VariableMaster.selected head)
                opening.frontier).bind (fun actualReduction =>
              let reduction := actualReduction.1
              .step .citationStage (fun _ =>
                let stage : Search cursor sources contract demand left right :=
                  ⟨Master.stageFromParts cursor sources contract demand left right head actualHead.2
                    leftCheck.1 leftCheck.2 rightCheck.1 rightCheck.2 opening producedOpening.opening.2 reduction actualReduction.2,
                    Master.stageFromParts_actual cursor sources contract demand left right head actualHead.2
                      leftCheck.1 leftCheck.2 rightCheck.1 rightCheck.2 opening producedOpening.opening.2 reduction actualReduction.2⟩
                (ControlStageCeilingExecution.code stage.1 producedOpening.execution producedOpening.preservationExact).bind (fun payload =>
                  .step .formationResources (fun _ => .done ⟨stage, payload, producedHead.reader, producedHead.root⟩)))))))))))

theorem search_from_root_finite {context} (cursor : MasterResources.Cursor) (sources : Support SourceValue context)
    (contract : Contract) (demand : Demand) (left right : Location context)
    (reader : Reader cursor.assignment.reader)
    (root : Actual (constructMeasuredOperationalRoot cursor.state.searchSeed)) :
    Finite (searchFromRootCode cursor sources contract demand left right reader root) := by
  apply finite_bind (ControlMasterHeadReader.from_root_finite cursor reader root); intro actualHead
  apply finite_bind (ControlSelection.check_finite _ _ _ _); intro leftCheck
  apply finite_bind (ControlSelection.check_finite _ _ _ _); intro rightCheck
  apply finite_step; apply finite_step
  apply finite_bind (ControlFrontierCeilingOpening.finite _ _ _); intro producedOpening
  apply finite_step
  apply finite_bind (ControlFrontierNormalization.finite _ _ _); intro actualReduction
  apply finite_step
  apply finite_bind (ControlStageCeilingExecution.finite _ _ _); intro payload
  exact finite_step _ _ (finite_done _)

def searchCode {context} (cursor : MasterResources.Cursor) (sources : Support SourceValue context)
    (contract : Contract) (demand : Demand) (left right : Location context)
    (reader : Reader cursor.assignment.reader) : Code Label (ProducedStage cursor sources contract demand left right) :=
  (ControlMasterRootBootstrap.code cursor).bind
    (fun root => searchFromRootCode cursor sources contract demand left right reader root)

theorem search_finite {context} (cursor : MasterResources.Cursor) (sources : Support SourceValue context)
    (contract : Contract) (demand : Demand) (left right : Location context)
    (reader : Reader cursor.assignment.reader) : Finite (searchCode cursor sources contract demand left right reader) := by
  apply finite_bind (ControlMasterRootBootstrap.finite cursor); intro root
  exact search_from_root_finite _ _ _ _ _ _ reader root

structure ProducedRun {context sources contract} (state : @Dossier.State context sources contract)
    (task : Dossier.Obligation context) where
  run : Run state task
  reader : Reader run.1.1.next.assignment.reader
  root : Actual (constructMeasuredOperationalRoot run.1.1.next.state.searchSeed)

def packetFromParts {context sources contract} (state : @Dossier.State context sources contract)
    (task : Dossier.Obligation context) (stage : Search state.cursor sources contract task.demand task.left task.right)
    (decision : Actual (Master.decide stage.1 state.memory)) : Run state task :=
  ⟨⟨stage.1, decision.1⟩, by
    obtain ⟨_, actualStage⟩ := stage
    obtain ⟨_, actualDecision⟩ := decision
    cases actualStage; cases actualDecision; rfl⟩

def runFromRootCode {context sources contract} (state : @Dossier.State context sources contract)
    (task : Dossier.Obligation context) (reader : Reader state.cursor.assignment.reader)
    (root : Actual (constructMeasuredOperationalRoot state.cursor.state.searchSeed)) :
    Code Label (ProducedRun state task) :=
  (searchFromRootCode state.cursor sources contract task.demand task.left task.right reader root).bind (fun produced =>
    (ControlCeilingCompletion.executedDecideCode produced.stage.1 state.memory produced.payload).bind (fun decision =>
      .step .citationPacket (fun _ =>
        let actual := packetFromParts state task produced.stage decision
        .step .executionPayload (fun _ => .done ⟨actual, produced.reader, produced.root⟩))))

theorem run_from_root_finite {context sources contract} (state : @Dossier.State context sources contract)
    (task : Dossier.Obligation context) (reader : Reader state.cursor.assignment.reader)
    (root : Actual (constructMeasuredOperationalRoot state.cursor.state.searchSeed)) :
    Finite (runFromRootCode state task reader root) := by
  apply finite_bind (search_from_root_finite _ _ _ _ _ _ reader root); intro produced
  apply finite_bind (ControlCeilingCompletion.executed_decide_finite _ _ produced.payload); intro decision
  apply finite_step; apply finite_step; exact finite_done _

def runCode {context sources contract} (state : @Dossier.State context sources contract)
    (task : Dossier.Obligation context) (reader : Reader state.cursor.assignment.reader) :
    Code Label (ProducedRun state task) :=
  (ControlMasterRootBootstrap.code state.cursor).bind
    (fun root => runFromRootCode state task reader root)

theorem run_finite {context sources contract} (state : @Dossier.State context sources contract)
    (task : Dossier.Obligation context) (reader : Reader state.cursor.assignment.reader) :
    Finite (runCode state task reader) := by
  apply finite_bind (ControlMasterRootBootstrap.finite state.cursor); intro root
  exact run_from_root_finite state task reader root

end ConstitutiveSearch.Agent.Local.Documentary.ControlMeasuredMaster

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMeasuredMaster.ProducedStage
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMeasuredMaster.searchCode
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMeasuredMaster.search_finite
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMeasuredMaster.ProducedRun
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMeasuredMaster.packetFromParts
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMeasuredMaster.runCode
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMeasuredMaster.run_finite
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMeasuredMaster.searchFromRootCode
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMeasuredMaster.search_from_root_finite
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMeasuredMaster.runFromRootCode
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMeasuredMaster.run_from_root_finite
/- AXIOM_AUDIT_END -/
