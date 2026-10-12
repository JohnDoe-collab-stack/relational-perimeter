import Tests.LocalAlignment.DocumentaryControlMasterDiscovery

/-! Discovery consumes the complete measured root received from the previous
causal production. Only the new candidate extraction and exploration are run. -/
set_option genInjectivity false
set_option backward.match.sparseCases false
set_option maxHeartbeats 8000000
namespace ConstitutiveSearch.Agent.Local.Documentary.ControlReceivedDiscovery
open Resources EndogenousDecomposition SAT Control ControlBindings ControlMasterData
open ControlMasterGeneration ControlMasterDiscovery

def generationCode {depth : Nat} (generation : CanonicalStageGeneration depth)
    (seed : Nat) (seedActual : seed = generatedSearchSeed generation)
    (realized : Actual (constructMeasuredOperationalRoot seed)) :
    Code Label (Actual (measuredGeneratedExtractionFromSeed generation seed seedActual)) :=
  let seedExact := seedActual.trans (generatedSearchSeed_exact generation)
  let indexed := Eq.rec (motive := fun index _ =>
    GeneratedStructuralBranchContext (distinctGrowingDiscoveryFormula index)) realized.1.value seedExact
  have rootExact : indexed = (constructStage (depth + 1)).operationalRoot := by
    cases seedExact
    exact realized.1.valueExact.trans (constructStage (depth + 1)).operationalRootExact.symm
  (extractionCode indexed.context.formula).bind (fun extracted =>
    .step .masterGeneration (fun _ => .done
      ⟨⟨indexed, rootExact, extracted.1, by
            rw [extracted.2, rootExact]; rfl, realized.1.work⟩, by
        obtain ⟨_, actual⟩ := extracted; cases actual
        obtain ⟨_, actual⟩ := realized; cases actual; rfl⟩))

theorem generation_finite {depth : Nat} (generation : CanonicalStageGeneration depth)
    (seed : Nat) (seedActual : seed = generatedSearchSeed generation)
    (realized : Actual (constructMeasuredOperationalRoot seed)) :
    Finite (generationCode generation seed seedActual realized) := by
  apply finite_bind (extraction_finite _)
  intro extracted
  exact finite_step _ _ (finite_done _)


def code {depth : Nat} {assignment : SequentialAssignment depth}
    (state : ThreadedConstitutiveState depth assignment)
    (root : Actual (constructMeasuredOperationalRoot state.searchSeed)) : Code Label (Run state) :=
  (generationCode state.generation state.searchSeed state.searchSeedExact root).bind (fun generatedPacket =>
    let generated := generatedPacket.1
    (ControlProvenance.filterCode state.provenance generated.extraction.candidates).bind (fun filtered =>
      (ControlMasterCandidates.code generated.operationalRoot filtered.1.retained).bind (fun explored =>
        let producedOutcome := explored.1
        let outcome := Eq.rec (motive := fun source _ => RecordedDiscoveryOutcome source)
          producedOutcome generated.operationalRootExact
        .step .masterDiscoveryPacket (fun _ =>
          let run : ThreadedNextDiscoveryRun depth state :=
            { generated := generated
              generatedFromSearchSeed := generatedPacket.2
              generatedExact := generatedPacket.2.trans
                (measuredGeneratedExtractionFromSeed_eq state.generation state.searchSeed state.searchSeedExact)
              filtering := filtered.1
              filteringExact := filtered.2
              candidates := filtered.1.retained
              candidatesExact := rfl
              outcome := outcome
              outcomeExact := (congrArg
                (fun produced => Eq.rec (motive := fun source _ => RecordedDiscoveryOutcome source)
                  produced generated.operationalRootExact) explored.2).trans
                (exploreRecordedCandidates_transport_exact generated.operationalRootExact filtered.1.retained) }
          .done ⟨run, by
            obtain ⟨_, actualOutcome⟩ := explored; cases actualOutcome
            obtain ⟨_, actualFilter⟩ := filtered; cases actualFilter
            obtain ⟨_, actualGenerated⟩ := generatedPacket; cases actualGenerated; rfl⟩))))

theorem finite {depth : Nat} {assignment : SequentialAssignment depth}
    (state : ThreadedConstitutiveState depth assignment)
    (root : Actual (constructMeasuredOperationalRoot state.searchSeed)) : Finite (code state root) := by
  apply finite_bind (generation_finite _ _ _ root)
  intro generatedPacket
  apply finite_bind (ControlProvenance.filter_finite _ _)
  intro filtered
  apply finite_bind (ControlMasterCandidates.finite _ _)
  intro explored
  apply finite_step
  exact finite_done _

end ConstitutiveSearch.Agent.Local.Documentary.ControlReceivedDiscovery

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlReceivedDiscovery.generationCode
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlReceivedDiscovery.generation_finite
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlReceivedDiscovery.code
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlReceivedDiscovery.finite
/- AXIOM_AUDIT_END -/
