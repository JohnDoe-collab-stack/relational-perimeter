import Tests.LocalAlignment.DocumentaryControlMasterApplication

/-! Carry the actual sequential reader through the original constructed
threaded stage. Next-state decisions consume its paid MeasuredValue. -/
set_option genInjectivity false
set_option backward.match.sparseCases false
set_option maxHeartbeats 8000000
namespace ConstitutiveSearch.Agent.Local.Documentary.ControlMasterApplicationReader
open SAT EndogenousDecomposition Control ControlBindings ControlMasterData
open ControlMeasuredAssignmentReader ControlMasterApplication

structure Produced {depth : Nat} {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment} (expected : ConstructedThreadedStageRun state) where
  built : Actual expected
  reader : Reader built.1.stage.next.reader

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
    (avoid : StructuralDecisionsAvoid (stageSelectedVar (depth + 1)) state.decisions)
    (reader : Reader assignment.reader) :
    Code Label (Produced (buildThreadedConstitutiveStage state discoveryRun discoveryRunExact discovery found
      canonicalFound workLeCanonical avoid)) :=
  (ControlSequentialReader.code depth assignment state.generation discoveryRun.asRecorded
    discoveryRun.extractionExact discovery found canonicalFound workLeCanonical reader).bind (fun stage =>
    (ControlNextState.withReaderCode state stage.stage.1 avoid stage.reader).bind (fun next =>
      .step .masterConstructionReturn (fun _ =>
        let built : Actual (buildThreadedConstitutiveStage state discoveryRun discoveryRunExact discovery found
            canonicalFound workLeCanonical avoid) :=
          ⟨fromParts state discoveryRun discoveryRunExact discovery found canonicalFound workLeCanonical avoid
            stage.stage.1 stage.stage.2 next.1,
            from_parts_actual _ _ _ _ _ _ _ _ _ _ _ next.2⟩
        .step .executionPayload (fun _ => .done ⟨built, stage.reader⟩))))

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
    (avoid : StructuralDecisionsAvoid (stageSelectedVar (depth + 1)) state.decisions)
    (reader : Reader assignment.reader) :
    Finite (buildCode state discoveryRun discoveryRunExact discovery found canonicalFound workLeCanonical avoid reader) := by
  apply finite_bind (ControlSequentialReader.finite _ _ _ _ _ _ _ _ _ _); intro stage
  apply finite_bind (ControlNextState.with_reader_finite _ _ _ _); intro next
  apply finite_step; apply finite_step; exact finite_done _

def code {depth : Nat} {assignment : SequentialAssignment depth}
    (state : ThreadedConstitutiveState depth assignment) (fresh : ThreadedStateFreshForNext state)
    (discoveryRun : ThreadedNextDiscoveryRun depth state) (discoveryExact : discoveryRun = runThreadedNextDiscovery state)
    (reader : Reader assignment.reader) :
    Code Label (Produced (buildFromExecutedDiscovery state fresh discoveryRun discoveryExact)) :=
  .step .masterApply (fun _ => match found : discoveryRun.outcome.discovered? with
    | none => False.elim ((runThreadedNextDiscovery_found state fresh) (discoveryExact ▸ found))
    | some discovery =>
      (buildCode state discoveryRun discoveryExact discovery found
        (by rw [discoveryExact, runThreadedNextDiscovery_discovered_exact state fresh] at found; exact found)
        (discoveryExact.symm ▸ runThreadedNextDiscovery_work_le_canonical state fresh)
        (state.decisionsAvoidNext fresh) reader).bind (fun built =>
          let actual : Actual (buildFromExecutedDiscovery state fresh discoveryRun discoveryExact) :=
            ⟨built.built.1, by
              rw [built.built.2]
              unfold buildFromExecutedDiscovery
              split
              · rename_i failed; rw [found] at failed; cases failed
              · rename_i returned returnedFound
                have same : discovery = returned := Option.some.inj (found.symm.trans returnedFound)
                cases same; rfl⟩
          .done ⟨actual, built.reader⟩))

theorem finite {depth : Nat} {assignment : SequentialAssignment depth}
    (state : ThreadedConstitutiveState depth assignment) (fresh : ThreadedStateFreshForNext state)
    (discoveryRun : ThreadedNextDiscoveryRun depth state) (discoveryExact : discoveryRun = runThreadedNextDiscovery state)
    (reader : Reader assignment.reader) :
    Finite (code state fresh discoveryRun discoveryExact reader) := by
  apply finite_step; split
  · exact False.elim ((runThreadedNextDiscovery_found state fresh) (discoveryExact ▸ (by assumption)))
  · apply finite_bind (build_finite _ _ _ _ _ _ _ _ _); intro built; exact finite_done _

end ConstitutiveSearch.Agent.Local.Documentary.ControlMasterApplicationReader

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMasterApplicationReader.Produced
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMasterApplicationReader.buildCode
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMasterApplicationReader.build_finite
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMasterApplicationReader.code
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMasterApplicationReader.finite
/- AXIOM_AUDIT_END -/
