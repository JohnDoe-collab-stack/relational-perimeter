import Tests.LocalAlignment.DocumentaryControlProvenance
import Tests.LocalAlignment.DocumentaryControlMasterGeneration
import Tests.LocalAlignment.DocumentaryControlMasterCandidates

/-! Discovery retains generation, the actual paid provenance filter and the
exploration result in the original full packet. Generation and exploration
have separate internal interfaces which are opened by their own controls. -/
set_option genInjectivity false
set_option maxHeartbeats 5000000
namespace ConstitutiveSearch.Agent.Local.Documentary.ControlMasterDiscovery
open EndogenousDecomposition SAT Control ControlBindings

abbrev Run {depth : Nat} {assignment : SequentialAssignment depth}
    (state : ThreadedConstitutiveState depth assignment) :=
  {run : ThreadedNextDiscoveryRun depth state // run = runThreadedNextDiscovery state}

def code {depth : Nat} {assignment : SequentialAssignment depth}
    (state : ThreadedConstitutiveState depth assignment) : Code Label (Run state) :=
  (ControlMasterGeneration.code state.generation state.searchSeed state.searchSeedExact).bind (fun generatedPacket =>
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
    (state : ThreadedConstitutiveState depth assignment) : Finite (code state) := by
  apply finite_bind (ControlMasterGeneration.finite _ _ _)
  intro generatedPacket
  apply finite_bind (ControlProvenance.filter_finite _ _)
  intro filtered
  apply finite_bind (ControlMasterCandidates.finite _ _)
  intro explored
  apply finite_step
  exact finite_done _

end ConstitutiveSearch.Agent.Local.Documentary.ControlMasterDiscovery

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMasterDiscovery.Run
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMasterDiscovery.code
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMasterDiscovery.finite
/- AXIOM_AUDIT_END -/
