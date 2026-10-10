import Tests.LocalAlignment.DocumentaryControlNextState
import RelationalPerimeter.Computation.ConstitutiveSearch.EndogenousDecomposition.CausalOperationalExecution

/-! Build from the discovery already supplied, consuming the actual controlled
stage and successor. No native whole application builder is replayed. -/
set_option genInjectivity false
set_option maxHeartbeats 8000000
namespace ConstitutiveSearch.Agent.Local.Documentary.ControlMasterApplication
open SAT EndogenousDecomposition Control ControlBindings ControlMasterData

def fromParts {depth : Nat} {assignment : SequentialAssignment depth}
    (state : ThreadedConstitutiveState depth assignment)
    (discoveryRun : ThreadedNextDiscoveryRun depth state)
    (discoveryRunExact : discoveryRun = runThreadedNextDiscovery state)
    (discovery : EndogenousFlipDiscovery (constructStage (depth + 1)).operationalRoot)
    (found : discoveryRun.outcome.discovered? = some discovery)
    (canonicalFound : (stageRecordedDiscoveryRun (depth + 1)).outcome.discovered? = some discovery)
    (workLeCanonical : (discoveryRun.outcome.comparisonWork.add discoveryRun.outcome.constructionWork).total ≤
      ((stageRecordedDiscoveryRun (depth + 1)).outcome.comparisonWork.add
        (stageRecordedDiscoveryRun (depth + 1)).outcome.constructionWork).total)
    (_avoid : StructuralDecisionsAvoid (stageSelectedVar (depth + 1)) state.decisions)
    (stage : SequentialStageRun depth assignment)
    (stageActual : stage = executeSequentialStageFromActiveRecorded depth assignment state.generation
      discoveryRun.asRecorded discoveryRun.extractionExact discovery found canonicalFound workLeCanonical)
    (next : NextOperationalStateRun state stage) : ConstructedThreadedStageRun state :=
  { stage := stage
    run :=
      { discoveryRun := discoveryRun, discoveryRunExact := discoveryRunExact
        discovery := discovery, discoveryFound := found, recordedDiscoveryFound := found
        discoveryExact := canonicalFound, discoveryWorkLeCanonical := workLeCanonical
        stageFromDiscovery := stageActual
        relationFromTransmittedState := by cases stageActual; exact found
        returnedCodeFromThatRelation := executedDiscoverySchedule_code stage.execution
        executedOutputFromThatCode := stage.application.outputExact
        nextRun := next } }

theorem from_parts_actual {depth : Nat} {assignment : SequentialAssignment depth}
    (state : ThreadedConstitutiveState depth assignment)
    (discoveryRun : ThreadedNextDiscoveryRun depth state)
    (discoveryRunExact : discoveryRun = runThreadedNextDiscovery state)
    (discovery : EndogenousFlipDiscovery (constructStage (depth + 1)).operationalRoot)
    (found : discoveryRun.outcome.discovered? = some discovery)
    (canonicalFound : (stageRecordedDiscoveryRun (depth + 1)).outcome.discovered? = some discovery)
    (workLeCanonical : (discoveryRun.outcome.comparisonWork.add discoveryRun.outcome.constructionWork).total ≤
      ((stageRecordedDiscoveryRun (depth + 1)).outcome.comparisonWork.add
        (stageRecordedDiscoveryRun (depth + 1)).outcome.constructionWork).total)
    (avoid : StructuralDecisionsAvoid (stageSelectedVar (depth + 1)) state.decisions)
    (stage : SequentialStageRun depth assignment)
    (stageActual : stage = executeSequentialStageFromActiveRecorded depth assignment state.generation
      discoveryRun.asRecorded discoveryRun.extractionExact discovery found canonicalFound workLeCanonical)
    (next : NextOperationalStateRun state stage) (nextActual : next = realizeNextOperationalState state stage avoid) :
    fromParts state discoveryRun discoveryRunExact discovery found canonicalFound workLeCanonical avoid stage stageActual next =
      buildThreadedConstitutiveStage state discoveryRun discoveryRunExact discovery found canonicalFound workLeCanonical avoid := by
  cases stageActual; cases nextActual; rfl

def buildCode {depth : Nat} {assignment : SequentialAssignment depth}
    (state : ThreadedConstitutiveState depth assignment)
    (discoveryRun : ThreadedNextDiscoveryRun depth state)
    (discoveryRunExact : discoveryRun = runThreadedNextDiscovery state)
    (discovery : EndogenousFlipDiscovery (constructStage (depth + 1)).operationalRoot)
    (found : discoveryRun.outcome.discovered? = some discovery)
    (canonicalFound : (stageRecordedDiscoveryRun (depth + 1)).outcome.discovered? = some discovery)
    (workLeCanonical : (discoveryRun.outcome.comparisonWork.add discoveryRun.outcome.constructionWork).total ≤
      ((stageRecordedDiscoveryRun (depth + 1)).outcome.comparisonWork.add
        (stageRecordedDiscoveryRun (depth + 1)).outcome.constructionWork).total)
    (avoid : StructuralDecisionsAvoid (stageSelectedVar (depth + 1)) state.decisions) :
    Code Label (Actual (buildThreadedConstitutiveStage state discoveryRun discoveryRunExact discovery found
      canonicalFound workLeCanonical avoid)) :=
  (ControlSequentialStage.code depth assignment state.generation discoveryRun.asRecorded
    discoveryRun.extractionExact discovery found canonicalFound workLeCanonical).bind (fun stage =>
    (ControlNextState.code state stage.1 avoid).bind (fun next =>
      .step .masterConstructionReturn (fun _ => .done
        ⟨fromParts state discoveryRun discoveryRunExact discovery found canonicalFound workLeCanonical avoid
          stage.1 stage.2 next.1,
          from_parts_actual _ _ _ _ _ _ _ _ _ _ _ next.2⟩)))

theorem build_finite {depth : Nat} {assignment : SequentialAssignment depth}
    (state : ThreadedConstitutiveState depth assignment)
    (discoveryRun : ThreadedNextDiscoveryRun depth state)
    (discoveryRunExact : discoveryRun = runThreadedNextDiscovery state)
    (discovery : EndogenousFlipDiscovery (constructStage (depth + 1)).operationalRoot)
    (found : discoveryRun.outcome.discovered? = some discovery)
    (canonicalFound : (stageRecordedDiscoveryRun (depth + 1)).outcome.discovered? = some discovery)
    (workLeCanonical : (discoveryRun.outcome.comparisonWork.add discoveryRun.outcome.constructionWork).total ≤
      ((stageRecordedDiscoveryRun (depth + 1)).outcome.comparisonWork.add
        (stageRecordedDiscoveryRun (depth + 1)).outcome.constructionWork).total)
    (avoid : StructuralDecisionsAvoid (stageSelectedVar (depth + 1)) state.decisions) :
    Finite (buildCode state discoveryRun discoveryRunExact discovery found canonicalFound workLeCanonical avoid) := by
  apply finite_bind (ControlSequentialStage.finite _ _ _ _ _ _ _ _ _); intro stage
  apply finite_bind (ControlNextState.finite _ _ _); intro next
  exact finite_step _ _ (finite_done _)

def code {depth : Nat} {assignment : SequentialAssignment depth}
    (state : ThreadedConstitutiveState depth assignment) (fresh : ThreadedStateFreshForNext state)
    (discoveryRun : ThreadedNextDiscoveryRun depth state) (discoveryExact : discoveryRun = runThreadedNextDiscovery state) :
    Code Label (Actual (buildFromExecutedDiscovery state fresh discoveryRun discoveryExact)) :=
  .step .masterApply (fun _ => match found : discoveryRun.outcome.discovered? with
    | none => False.elim ((runThreadedNextDiscovery_found state fresh) (discoveryExact ▸ found))
    | some discovery =>
      (buildCode state discoveryRun discoveryExact discovery found
        (by rw [discoveryExact, runThreadedNextDiscovery_discovered_exact state fresh] at found; exact found)
        (discoveryExact.symm ▸ runThreadedNextDiscovery_work_le_canonical state fresh)
        (state.decisionsAvoidNext fresh)).bind (fun built => .done ⟨built.1, by
          rw [built.2]
          unfold buildFromExecutedDiscovery
          split
          · rename_i failed; rw [found] at failed; cases failed
          · rename_i returned returnedFound
            have same : discovery = returned := Option.some.inj (found.symm.trans returnedFound)
            cases same; rfl⟩))

theorem finite {depth : Nat} {assignment : SequentialAssignment depth}
    (state : ThreadedConstitutiveState depth assignment) (fresh : ThreadedStateFreshForNext state)
    (discoveryRun : ThreadedNextDiscoveryRun depth state) (discoveryExact : discoveryRun = runThreadedNextDiscovery state) :
    Finite (code state fresh discoveryRun discoveryExact) := by
  apply finite_step; split
  · exact False.elim ((runThreadedNextDiscovery_found state fresh) (discoveryExact ▸ (by assumption)))
  · apply finite_bind (build_finite _ _ _ _ _ _ _ _); intro built; exact finite_done _

end ConstitutiveSearch.Agent.Local.Documentary.ControlMasterApplication

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMasterApplication.fromParts
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMasterApplication.from_parts_actual
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMasterApplication.buildCode
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMasterApplication.build_finite
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMasterApplication.code
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMasterApplication.finite
/- AXIOM_AUDIT_END -/
