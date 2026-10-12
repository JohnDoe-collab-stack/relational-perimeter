import Tests.LocalAlignment.DocumentaryControlMasterGeneration
import RelationalPerimeter.Computation.ConstitutiveSearch.EndogenousDecomposition.InstrumentedExecutionRealization
import RelationalPerimeter.Computation.ConstitutiveSearch.EndogenousDecomposition.PrefixLocalOperationalProduction

/-! Causal projection consumes the actual constituted prefix, one received
threaded stage, its generated step, and a paid next operational root.
It never reconstructs the canonical stage/history to supply a runtime index. -/
set_option genInjectivity false
set_option backward.match.sparseCases false
set_option maxHeartbeats 8000000
namespace ConstitutiveSearch.Agent.Local.Documentary.ControlCausalProjection
open SAT EndogenousDecomposition Control ControlBindings ControlMasterData
open StrongPerimetralTurning StrongPerimetralTurning.Example

theorem freeKCore_unique
    {P : CircularPresentation}
    {cursor : PerimeterCursor P}
    {code : BoundaryDifferenceCode P cursor}
    (first second : FreeKCore P cursor code) : first = second := by
  cases first with
  | mk formationTerm formationExact obstruction obstructionExact
      provenance provenanceExact =>
    cases second with
    | mk formationTerm' formationExact' obstruction' obstructionExact'
        provenance' provenanceExact' =>
      cases formationExact
      cases formationExact'
      cases obstructionExact
      cases obstructionExact'
      cases provenanceExact
      cases provenanceExact'
      rfl

theorem freeK_unique
    {P : CircularPresentation}
    {cursor : PerimeterCursor P}
    {previous : FreeConstitution P cursor}
    {difference : BoundaryDifference P previous}
    (first second : FreeK P previous difference) : first = second := by
  cases first with
  | mk core =>
    cases second with
    | mk core' =>
      exact congrArg FreeK.mk
        (freeKCore_unique core core')

theorem integrates_unique
    {P : CircularPresentation}
    {source : PositiveConstitution P}
    (first second : Integrates source) : first = second := by
  cases first with
  | mk firstLayer firstExact =>
    cases second with
    | mk secondLayer secondExact =>
      have layerExact : firstLayer = secondLayer :=
        freeK_unique firstLayer secondLayer
      cases layerExact
      rfl

theorem preservesProvenance_unique
    {P : CircularPresentation}
    {source target : PositiveConstitution P}
    (first second : PreservesProvenance source target) : first = second := by
  cases first with
  | mk firstTarget firstIntegrated =>
    cases second with
    | mk secondTarget secondIntegrated =>
      cases firstTarget
      cases secondTarget
      exact congrArg (PreservesProvenance.mk rfl)
        (integrates_unique firstIntegrated secondIntegrated)

theorem integratesClosureObstruction_unique
    {P : CircularPresentation}
    {source : PositiveConstitution P}
    (first second : IntegratesClosureObstruction source) : first = second := by
  cases first
  cases second
  rfl

theorem continuesDifference_unique
    {P : CircularPresentation}
    {source : PositiveConstitution P}
    (first second : ContinuesDifference source) : first = second := by
  cases first
  cases second
  rfl

theorem freshBoundaryDifference_unique
    {P : CircularPresentation}
    {source : PositiveConstitution P}
    (first second : FreshBoundaryDifference source) : first = second := by
  cases first with
  | mk firstContinuation firstRecord firstRecordExact firstFresh =>
    cases second with
    | mk secondContinuation secondRecord secondRecordExact secondFresh =>
      have continuationExact : firstContinuation = secondContinuation :=
        continuesDifference_unique
          firstContinuation secondContinuation
      have recordExact : firstRecord = secondRecord :=
        firstRecordExact.trans secondRecordExact.symm
      cases continuationExact
      cases recordExact
      rfl

theorem canonicalGeneratedLaws_unique
    {P : CircularPresentation}
    {source : PositiveConstitution P}
    (first second : CanonicalGeneratedLaws source) : first = second := by
  cases first with
  | mk firstCompatibility firstCompatibilityExact firstProvenance
      firstObstruction firstDifference firstFresh =>
    cases second with
    | mk secondCompatibility secondCompatibilityExact secondProvenance
      secondObstruction secondDifference secondFresh =>
      have compatibilityExact : firstCompatibility = secondCompatibility :=
        firstCompatibilityExact.trans secondCompatibilityExact.symm
      have provenanceExact : firstProvenance = secondProvenance :=
        preservesProvenance_unique
          firstProvenance secondProvenance
      have obstructionExact : firstObstruction = secondObstruction :=
        integratesClosureObstruction_unique
          firstObstruction secondObstruction
      have differenceExact : firstDifference = secondDifference :=
        continuesDifference_unique
          firstDifference secondDifference
      have freshExact : firstFresh = secondFresh :=
        freshBoundaryDifference_unique firstFresh secondFresh
      cases compatibilityExact
      cases provenanceExact
      cases obstructionExact
      cases differenceExact
      cases freshExact
      rfl

theorem generatedStep_unique
    {P : CircularPresentation}
    {source target : PositiveConstitution P}
    (first second : GeneratedStep source target) : first = second := by
  cases first with
  | mk firstTarget firstLaws =>
    cases second with
    | mk secondTarget secondLaws =>
      exact congrArg (GeneratedStep.mk firstTarget)
        (canonicalGeneratedLaws_unique
          firstLaws secondLaws)


@[inline] def rawSource {source : CausalConstitutiveState}
    (past : ConstitutedOperationalPrefix source) : CausalConstitutiveState :=
  ConstitutedOperationalPrefix.casesOn (motive := fun _ _ => CausalConstitutiveState) past
    (fun received => received) (fun _ _ decomposition => decomposition.role.nextState)

theorem raw_source_actual {source : CausalConstitutiveState}
    (past : ConstitutedOperationalPrefix source) : rawSource past = source := by
  cases past <;> rfl

@[inline] def sourceFromPast {source : CausalConstitutiveState}
    (past : ConstitutedOperationalPrefix source) : Actual source :=
  ⟨rawSource past, raw_source_actual past⟩

@[inline] def sourceCode {source : CausalConstitutiveState}
    (past : ConstitutedOperationalPrefix source) : Code Label (Actual source) :=
  .step .controlInspect (fun _ => .done (sourceFromPast past))

theorem source_finite {source : CausalConstitutiveState}
    (past : ConstitutedOperationalPrefix source) : Finite (sourceCode past) :=
  finite_step _ _ (finite_done _)

@[inline] def extendHistory (history : RootedGeneratedHistory examplePresentation)
    (target : PositiveConstitution examplePresentation)
    (step : GeneratedStep history.endpoint target) : RootedGeneratedHistory examplePresentation :=
  ⟨target, .extend history.history step⟩

def advanceHistory {depth : Nat} (history : RootedGeneratedHistory examplePresentation)
    (same : history = (constructStage depth).history)
    (generation : CanonicalStageGeneration depth) : RootedGeneratedHistory examplePresentation :=
  extendHistory history generation.target
    (Eq.rec (motive := fun endpoint _ => GeneratedStep endpoint generation.target)
      generation.generated (congrArg RootedGeneratedHistory.endpoint same).symm)

theorem advance_history_actual {depth : Nat} (history : RootedGeneratedHistory examplePresentation)
    (same : history = (constructStage depth).history)
    (generation : CanonicalStageGeneration depth) :
    advanceHistory history same generation = (constructStage (depth + 1)).history := by
  cases same
  cases generation with
  | mk target targetExact generated calls steps provenance certificates =>
    cases targetExact
    have sameStep := generatedStep_unique generated (generateCanonicalStage depth).generated
    cases sameStep
    rfl

def rootPair {index : Nat} (root : MeasuredValue (distinctGrowingDiscoveryRoot index)) :
    Σ formula : Cnf, GeneratedStructuralBranchContext formula :=
  ⟨root.value.context.formula,
    Eq.rec (motive := fun formula _ => GeneratedStructuralBranchContext formula) root.value
      (congrArg (fun received => received.context.formula) root.valueExact).symm⟩

theorem root_pair_actual {index : Nat} (root : MeasuredValue (distinctGrowingDiscoveryRoot index)) :
    rootPair root = ⟨distinctGrowingDiscoveryFormula index, distinctGrowingDiscoveryRoot index⟩ := by
  cases root with
  | mk value actual work => cases actual; rfl

def nextFromParts (history : RootedGeneratedHistory examplePresentation)
    (root : Σ formula : Cnf, GeneratedStructuralBranchContext formula)
    (assignment : Assignment) (seed : Nat) (decisions : List StructuralBranchDecision)
    (provenance : List Var) (actual : provenance = decisions.map (fun decision => decision.var)) :
    CausalConstitutiveState :=
  ⟨history, root.1, root.2, assignment, seed, decisions, provenance, actual⟩

def nextStateFromRoot {depth : Nat} {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment} {stage : SequentialStageRun depth assignment}
    (run : ThreadedConstitutiveStageRun state stage)
    (source : Actual (causalStateOfThreadedState state))
    (root : Actual (constructMeasuredOperationalRoot run.nextRun.next.searchSeed)) : CausalConstitutiveState :=
  nextFromParts (advanceHistory source.1.constitutedHistory
    (congrArg CausalConstitutiveState.constitutedHistory source.2) state.generation)
    (rootPair root.1) stage.next.assignment run.nextRun.next.searchSeed run.nextRun.next.decisions
    run.nextRun.next.provenance run.nextRun.next.provenanceExact

set_option backward.isDefEq.respectTransparency false in
theorem next_state_actual {depth : Nat} {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment} {stage : SequentialStageRun depth assignment}
    (run : ThreadedConstitutiveStageRun state stage)
    (source : Actual (causalStateOfThreadedState state))
    (root : Actual (constructMeasuredOperationalRoot run.nextRun.next.searchSeed)) :
    nextStateFromRoot run source root = causalStateOfThreadedState run.nextRun.next := by
  have seedExact := run.nextRun.next.searchSeedExact.trans (generatedSearchSeed_exact run.nextRun.next.generation)
  have pairActual : rootPair root.1 =
      ⟨distinctGrowingDiscoveryFormula (constructStage (depth + 1 + 1)).searchIndex,
        distinctGrowingDiscoveryRoot (constructStage (depth + 1 + 1)).searchIndex⟩ :=
    (root_pair_actual root.1).trans (congrArg (fun index =>
      (⟨distinctGrowingDiscoveryFormula index, distinctGrowingDiscoveryRoot index⟩ :
        Σ formula : Cnf, GeneratedStructuralBranchContext formula)) seedExact)
  dsimp only [nextStateFromRoot]
  rw [advance_history_actual, pairActual]
  rfl

def stageFromSource {depth : Nat} {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment} {stage : SequentialStageRun depth assignment}
    (run : ThreadedConstitutiveStageRun state stage)
    (source : Actual (causalStateOfThreadedState state))
    (next : Actual (causalStateOfThreadedState run.nextRun.next)) : CausalConstitutiveStageExecution source.1 :=
  let current : CausalConstitutiveStageExecution (causalStateOfThreadedState state) :=
    { selected := stage.discovery.var
      fresh := stage.discovery.fresh
      relation := stage.discovery.relation
      sourceContinuation := stage.sourceContinuation
      sourceAccepted := stage.sourceAccepted
      outputContinuation := stage.application.output
      outputExact := (causalStageOfThreadedStage run).outputExact
      outputAccepted := stage.outputAccepted
      next := next.1
      constitutiveGeneration := Eq.rec (motive := fun received _ =>
        GeneratedStep (causalStateOfThreadedState state).constitutedHistory.endpoint received.constitutedHistory.endpoint)
          (threadedGenerationToProjectedNext state) next.2.symm
      nextAssignmentExact := by rw [next.2]; exact (causalStageOfThreadedStage run).nextAssignmentExact
      nextSearchSeedExact := by rw [next.2]; exact (causalStageOfThreadedStage run).nextSearchSeedExact
      nextDecisionsExact := by rw [next.2]; exact (causalStageOfThreadedStage run).nextDecisionsExact
      nextProvenanceExact := by rw [next.2]; exact (causalStageOfThreadedStage run).nextProvenanceExact }
  Eq.rec (motive := fun received _ => CausalConstitutiveStageExecution received) current source.2.symm

theorem stage_from_source_actual {depth : Nat} {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment} {stage : SequentialStageRun depth assignment}
    (run : ThreadedConstitutiveStageRun state stage)
    (source : Actual (causalStateOfThreadedState state))
    (next : Actual (causalStateOfThreadedState run.nextRun.next)) :
    HEq (stageFromSource run source next) (causalStageOfThreadedStage run) := by
  obtain ⟨_, sourceActual⟩ := source; cases sourceActual
  obtain ⟨_, nextActual⟩ := next; cases nextActual
  rfl

structure Produced {depth : Nat} {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment} {stage : SequentialStageRun depth assignment}
    (run : ThreadedConstitutiveStageRun state stage) where
  source : Actual (causalStateOfThreadedState state)
  stage : CausalConstitutiveStageExecution source.1
  actual : HEq stage (causalStageOfThreadedStage run)
  nextRoot : Actual (constructMeasuredOperationalRoot run.nextRun.next.searchSeed)

def code {depth : Nat} {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment} {stage : SequentialStageRun depth assignment}
    (past : ConstitutedOperationalPrefix (causalStateOfThreadedState state))
    (run : ThreadedConstitutiveStageRun state stage) : Code Label (Produced run) :=
  (sourceCode past).bind (fun source =>
    (ControlMasterGeneration.rootCode run.nextRun.next.searchSeed).bind (fun root =>
      .step .formationValues (fun _ =>
        let next : Actual (causalStateOfThreadedState run.nextRun.next) :=
          ⟨nextStateFromRoot run source root, next_state_actual run source root⟩
        .step .formationResources (fun _ =>
          let actualStage := stageFromSource run source next
          .step .executionPayload (fun _ => .done
            ⟨source, actualStage, stage_from_source_actual run source next, root⟩)))))

theorem finite {depth : Nat} {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment} {stage : SequentialStageRun depth assignment}
    (past : ConstitutedOperationalPrefix (causalStateOfThreadedState state))
    (run : ThreadedConstitutiveStageRun state stage) : Finite (code past run) := by
  apply finite_bind (source_finite past); intro source
  apply finite_bind (ControlMasterGeneration.root_finite _); intro root
  exact finite_step _ _ (finite_step _ _ (finite_step _ _ (finite_done _)))

end ConstitutiveSearch.Agent.Local.Documentary.ControlCausalProjection

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlCausalProjection.freeKCore_unique
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlCausalProjection.freeK_unique
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlCausalProjection.integrates_unique
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlCausalProjection.preservesProvenance_unique
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlCausalProjection.integratesClosureObstruction_unique
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlCausalProjection.continuesDifference_unique
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlCausalProjection.freshBoundaryDifference_unique
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlCausalProjection.canonicalGeneratedLaws_unique
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlCausalProjection.generatedStep_unique
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlCausalProjection.sourceFromPast
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlCausalProjection.sourceCode
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlCausalProjection.source_finite
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlCausalProjection.advanceHistory
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlCausalProjection.advance_history_actual
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlCausalProjection.nextStateFromRoot
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlCausalProjection.next_state_actual
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlCausalProjection.rootPair
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlCausalProjection.root_pair_actual
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlCausalProjection.nextFromParts
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlCausalProjection.stageFromSource
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlCausalProjection.stage_from_source_actual
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlCausalProjection.Produced
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlCausalProjection.code
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlCausalProjection.finite
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlCausalProjection.rawSource
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlCausalProjection.raw_source_actual
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlCausalProjection.extendHistory
/- AXIOM_AUDIT_END -/
