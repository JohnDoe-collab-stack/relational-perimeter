import Tests.LocalAlignment.DocumentaryControlCompletion
import Tests.LocalAlignment.DocumentaryControlMasterHead
import Tests.LocalAlignment.DocumentaryControlFrontierOpening
import Tests.LocalAlignment.DocumentaryControlFrontierNormalization

/-! The quotation search uses the same head, opening and retained reduction.
Paid source checks supply the actual flags and formula. The expanded path opens
head production, frontier opening, normalization and evaluation of the actual
routing syntax. Its executable envelope carries the same opening and reduction
into paid applications and assignment queries. Historical APIs remain intact;
the calculation and bootstrap of a full master envelope remain separate. -/
set_option genInjectivity false
set_option maxHeartbeats 3000000
namespace ConstitutiveSearch.Agent.Local.Documentary.ControlMaster
open Resources Control ControlBindings EndogenousDecomposition

abbrev Search {context} (cursor : MasterResources.Cursor) (sources : Support SourceValue context)
    (contract : Contract) (demand : Demand) (left right : Location context) :=
  {stage : Master.Stage cursor sources contract demand left right //
    stage = Master.search cursor sources contract demand left right}

def searchCode {context} (cursor : MasterResources.Cursor) (sources : Support SourceValue context)
    (contract : Contract) (demand : Demand) (left right : Location context) :
    Code Label (Search cursor sources contract demand left right) :=
  .step .citationHead (fun _ =>
    let head := VariableMaster.masterHead cursor
    (ControlSelection.checkCode sources contract demand left).bind (fun leftCheck =>
      (ControlSelection.checkCode sources contract demand right).bind (fun rightCheck =>
        .step .citationFormula (fun _ =>
          let formula := Selection.choiceFormula (VariableMaster.selected head) leftCheck.1.flag rightCheck.1.flag
          .step .citationOpening (fun _ =>
            let opening := VariableMaster.openFrontier formula (VariableMaster.selected head)
              [SAT.GeneratedStructuralBranchContext.root formula]
            .step .citationReduction (fun _ =>
              let reduction := SAT.normalizeGeneratedStructuralFrontierByFlip formula
                (VariableMaster.selected head) opening.frontier
              .step .citationStage (fun _ => .done
                ⟨Master.stageFromParts cursor sources contract demand left right head rfl
                  leftCheck.1 leftCheck.2 rightCheck.1 rightCheck.2 opening rfl reduction rfl,
                  Master.stageFromParts_actual cursor sources contract demand left right head rfl
                    leftCheck.1 leftCheck.2 rightCheck.1 rightCheck.2 opening rfl reduction rfl⟩)))))))

def searchBound {context} (cursor : MasterResources.Cursor) (sources : Support SourceValue context)
    (contract : Contract) (demand : Demand) (left right : Location context) : Nat :=
  let _ := cursor
  (ControlSelection.checkBound sources contract demand left +
    (ControlSelection.checkBound sources contract demand right + 4)) + 1

theorem search_bounded {context} (cursor : MasterResources.Cursor) (sources : Support SourceValue context)
    (contract : Contract) (demand : Demand) (left right : Location context) :
    Within (searchCode cursor sources contract demand left right)
      (searchBound cursor sources contract demand left right) := by
  apply within_step
  apply within_bind (ControlSelection.check_bounded sources contract demand left)
  intro leftCheck
  apply within_bind (ControlSelection.check_bounded sources contract demand right)
  intro rightCheck
  apply within_step
  apply within_step
  apply within_step
  exact within_step _ _ (within_done _)

abbrev Run {context sources contract} (state : @Dossier.State context sources contract)
    (task : Dossier.Obligation context) :=
  {produced : Dossier.Step state task // produced = Dossier.step state task}

def runCode {context sources contract} (state : @Dossier.State context sources contract)
    (task : Dossier.Obligation context) : Code Label (Run state task) :=
  (searchCode state.cursor sources contract task.demand task.left task.right).bind (fun actual =>
    (ControlCompletion.decideCode actual.1 state.memory).bind (fun decision =>
      .step .citationPacket (fun _ =>
        let produced : Dossier.Step state task := ⟨actual.1, decision.1⟩
        .done ⟨produced, by
          obtain ⟨stage, stageActual⟩ := actual
          obtain ⟨decision, decisionActual⟩ := decision
          cases stageActual
          cases decisionActual
          rfl⟩)))

def runBound {context sources contract} (state : @Dossier.State context sources contract)
    (task : Dossier.Obligation context) : Nat :=
  searchBound state.cursor sources contract task.demand task.left task.right +
    (ControlCompletion.pairBound task.left task.right + 1)

theorem run_bounded {context sources contract} (state : @Dossier.State context sources contract)
    (task : Dossier.Obligation context) : Within (runCode state task) (runBound state task) := by
  apply within_bind (search_bounded state.cursor sources contract task.demand task.left task.right)
  intro actual
  apply within_bind (ControlCompletion.pair_bounded actual.1 state.memory)
  intro decision
  exact within_step _ _ (within_done _)

theorem run_finite {context sources contract} (state : @Dossier.State context sources contract)
    (task : Dossier.Obligation context) : Finite (runCode state task) := by
  obtain ⟨produced, labels, trace, _⟩ := run_bounded state task
  exact ⟨produced, labels, trace⟩

def expandedSearchCode {context} (cursor : MasterResources.Cursor) (sources : Support SourceValue context)
    (contract : Contract) (demand : Demand) (left right : Location context) :
    Code Label (Search cursor sources contract demand left right) :=
  (ControlMasterHead.code cursor).bind (fun actualHead =>
    let head := actualHead.1
    (ControlSelection.checkCode sources contract demand left).bind (fun leftCheck =>
      (ControlSelection.checkCode sources contract demand right).bind (fun rightCheck =>
        .step .citationFormula (fun _ =>
          let formula := Selection.choiceFormula (VariableMaster.selected head) leftCheck.1.flag rightCheck.1.flag
          .step .citationOpening (fun _ =>
            (ControlFrontierOpening.code formula (VariableMaster.selected head)
              [SAT.GeneratedStructuralBranchContext.root formula]).bind (fun actualOpening =>
            let opening := actualOpening.1
            .step .citationReduction (fun _ =>
              (ControlFrontierNormalization.code formula (VariableMaster.selected head)
                opening.frontier).bind (fun actualReduction =>
              let reduction := actualReduction.1
              .step .citationStage (fun _ => .done
                ⟨Master.stageFromParts cursor sources contract demand left right head actualHead.2
                  leftCheck.1 leftCheck.2 rightCheck.1 rightCheck.2 opening actualOpening.2 reduction actualReduction.2,
                  Master.stageFromParts_actual cursor sources contract demand left right head actualHead.2
                    leftCheck.1 leftCheck.2 rightCheck.1 rightCheck.2 opening actualOpening.2 reduction actualReduction.2⟩)))))))))


structure ExecutableStage {context} (cursor : MasterResources.Cursor) (sources : Support SourceValue context)
    (contract : Contract) (demand : Demand) (left right : Location context) where
  stage : Search cursor sources contract demand left right
  payload : ControlStageExecution.Payload stage.1

def executableSearchCode {context} (cursor : MasterResources.Cursor) (sources : Support SourceValue context)
    (contract : Contract) (demand : Demand) (left right : Location context) :
    Code Label (ExecutableStage cursor sources contract demand left right) :=
  (ControlMasterHead.code cursor).bind (fun actualHead =>
    let head := actualHead.1
    (ControlSelection.checkCode sources contract demand left).bind (fun leftCheck =>
      (ControlSelection.checkCode sources contract demand right).bind (fun rightCheck =>
        .step .citationFormula (fun _ =>
          let formula := Selection.choiceFormula (VariableMaster.selected head) leftCheck.1.flag rightCheck.1.flag
          .step .citationOpening (fun _ =>
            (ControlFrontierExecutableOpening.code formula (VariableMaster.selected head)
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
                (ControlStageExecution.code stage.1 producedOpening.execution producedOpening.preservationExact).bind (fun payload =>
                  .step .formationResources (fun _ => .done ⟨stage, payload⟩)))))))))))

theorem executable_search_finite {context} (cursor : MasterResources.Cursor) (sources : Support SourceValue context)
    (contract : Contract) (demand : Demand) (left right : Location context) :
    Finite (executableSearchCode cursor sources contract demand left right) := by
  apply finite_bind (ControlMasterHead.finite cursor); intro actualHead
  apply finite_bind (ControlSelection.check_finite _ _ _ _); intro leftCheck
  apply finite_bind (ControlSelection.check_finite _ _ _ _); intro rightCheck
  apply finite_step; apply finite_step
  apply finite_bind (ControlFrontierExecutableOpening.finite _ _ _); intro producedOpening
  apply finite_step
  apply finite_bind (ControlFrontierNormalization.finite _ _ _); intro actualReduction
  apply finite_step
  apply finite_bind (ControlStageExecution.finite _ _ _); intro payload
  exact finite_step _ _ (finite_done _)

def expandedRunCode {context sources contract} (state : @Dossier.State context sources contract)
    (task : Dossier.Obligation context) : Code Label (Run state task) :=
  (executableSearchCode state.cursor sources contract task.demand task.left task.right).bind (fun actual =>
    (ControlCompletion.executedDecideCode actual.stage.1 state.memory actual.payload).bind (fun decision =>
      .step .citationPacket (fun _ =>
        let produced : Dossier.Step state task := ⟨actual.stage.1, decision.1⟩
        .done ⟨produced, by
          obtain ⟨⟨stage, stageActual⟩, payload⟩ := actual
          obtain ⟨decision, decisionActual⟩ := decision
          cases stageActual
          cases decisionActual
          rfl⟩)))


theorem expanded_search_finite {context} (cursor : MasterResources.Cursor) (sources : Support SourceValue context)
    (contract : Contract) (demand : Demand) (left right : Location context) :
    Finite (expandedSearchCode cursor sources contract demand left right) := by
  apply finite_bind (ControlMasterHead.finite cursor); intro head
  apply finite_bind
  · obtain ⟨value, labels, trace, _⟩ := ControlSelection.check_bounded sources contract demand left
    exact ⟨value, labels, trace⟩
  · intro leftCheck
    apply finite_bind
    · obtain ⟨value, labels, trace, _⟩ := ControlSelection.check_bounded sources contract demand right
      exact ⟨value, labels, trace⟩
    · intro rightCheck
      apply finite_step
      apply finite_step
      apply finite_bind (ControlFrontierOpening.finite _ _ _)
      intro actualOpening
      apply finite_step
      apply finite_bind (ControlFrontierNormalization.finite _ _ _)
      intro actualReduction
      apply finite_step
      exact finite_done _

theorem expanded_run_finite {context sources contract} (state : @Dossier.State context sources contract)
    (task : Dossier.Obligation context) : Finite (expandedRunCode state task) := by
  apply finite_bind (executable_search_finite state.cursor sources contract task.demand task.left task.right)
  intro actual
  apply finite_bind
  · exact ControlCompletion.executed_decide_finite actual.stage.1 state.memory actual.payload
  · intro decision
    exact finite_step _ _ (finite_done _)

end ConstitutiveSearch.Agent.Local.Documentary.ControlMaster

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMaster.Search
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMaster.searchCode
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMaster.searchBound
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMaster.search_bounded
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMaster.Run
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMaster.runCode
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMaster.runBound
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMaster.run_bounded
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMaster.run_finite
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMaster.expandedSearchCode
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMaster.ExecutableStage
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMaster.executableSearchCode
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMaster.executable_search_finite
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMaster.expandedRunCode
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMaster.expanded_search_finite
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMaster.expanded_run_finite
/- AXIOM_AUDIT_END -/
