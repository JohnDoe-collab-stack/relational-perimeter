import Tests.LocalAlignment.DocumentaryControlSequentialStage

/-! Retain the next state produced from the actual executed stage. The supplied
constitutive generator and function-valued bit query are explicit remaining
engines; this file does not claim their internal instruction costs. -/
set_option genInjectivity false
set_option maxHeartbeats 8000000
namespace ConstitutiveSearch.Agent.Local.Documentary.ControlNextState
open SAT EndogenousDecomposition Control ControlBindings ControlMasterData

def provenanceCode (selected : Var) (history : List Var) :
    Code Label (Actual (prependProvenanceMeasured selected history)) :=
  .step .masterProvenanceReturn (fun _ => .done ⟨⟨selected :: history, rfl, 1, rfl⟩, rfl⟩)

def seedCode {depth : Nat} {assignment : SequentialAssignment depth}
    (stage : SequentialStageRun depth assignment) : Code Label (Actual (executedProducedSearchSeed stage)) :=
  .step .masterConstructionCell (fun _ => match found : stage.execution.producedState.context.decisions with
    | [] => .done ⟨0, by rw [executedProducedSearchSeed, found]⟩
    | decision :: _ => .done ⟨decision.var, by rw [executedProducedSearchSeed, found]⟩)

def decisionCode {depth : Nat} {assignment : SequentialAssignment depth}
    (stage : SequentialStageRun depth assignment) : Code Label (Actual (executedBranchDecision stage)) :=
  .step .masterNextStateQuery (fun _ =>
    let selected := stage.discovery.1
    let bit := stage.application.output.1 selected
    .step .masterConstructionReturn (fun _ => .done ⟨⟨selected, bit⟩, by
      unfold executedBranchDecision
      rw [← sequentialStage_selected_exact stage]; rfl⟩))

def generationCode {depth : Nat} {assignment : SequentialAssignment depth}
    (state : ThreadedConstitutiveState depth assignment) :
    Code Label (Actual (generateCanonicalStageFromSource state.generation.target state.generation.targetExact)) :=
  .step .masterNextStateGeneration (fun _ => .done
    ⟨generateCanonicalStageFromSource state.generation.target state.generation.targetExact, rfl⟩)

def fromParts {depth : Nat} {assignment : SequentialAssignment depth}
    (state : ThreadedConstitutiveState depth assignment) (stage : SequentialStageRun depth assignment)
    (avoid : StructuralDecisionsAvoid (stageSelectedVar (depth + 1)) state.decisions)
    (provenance : ProvenancePrependRun state.provenance stage.schedule.entry.var)
    (provenanceActual : provenance = prependProvenanceMeasured stage.schedule.entry.var state.provenance)
    (generation : CanonicalStageGeneration (depth + 1))
    (generationActual : generation = generateCanonicalStageFromSource state.generation.target state.generation.targetExact)
    (seed : Var) (seedActual : seed = executedProducedSearchSeed stage)
    (decision : StructuralBranchDecision) (decisionActual : decision = executedBranchDecision stage) :
    NextOperationalStateRun state stage :=
  let next : ThreadedConstitutiveState (depth + 1) stage.next :=
    { threadedAssignment := stage.next, threadedAssignmentExact := rfl
      generation := generation
      searchSeed := seed
      searchSeedExact := by
        rw [seedActual, generationActual]
        exact (realizeNextOperationalState state stage avoid).next.searchSeedExact
      decisions := decision :: state.decisions
      provenance := provenance.output
      provenanceExact := by
        rw [decisionActual, provenanceActual]
        exact (realizeNextOperationalState state stage avoid).next.provenanceExact
      decisionsHold := by
        rw [decisionActual]
        exact (realizeNextOperationalState state stage avoid).next.decisionsHold }
  { provenanceRun := provenance, next := next
    assignmentFromExecution := rfl, searchSeedFromProducedState := seedActual
    generationFromProducedTarget := generationActual
    decisionsFromExecutedOutput := congrArg (fun decision => decision :: state.decisions) decisionActual
    decisionsFromExecution := by
      change decision :: state.decisions = _
      rw [decisionActual]; exact (realizeNextOperationalState state stage avoid).decisionsFromExecution
    provenanceFromScheduledOperation := provenance.outputExact
    provenanceFromExecution := by
      change provenance.output = _
      rw [provenance.outputExact, sequentialStage_selected_exact]
    decisionAccumulationWork := 1, decisionAccumulationWorkExact := rfl
    provenanceWork := provenance.visits, provenanceWorkExact := rfl }

theorem from_parts_actual {depth : Nat} {assignment : SequentialAssignment depth}
    (state : ThreadedConstitutiveState depth assignment) (stage : SequentialStageRun depth assignment)
    (avoid : StructuralDecisionsAvoid (stageSelectedVar (depth + 1)) state.decisions)
    (provenance : ProvenancePrependRun state.provenance stage.schedule.entry.var)
    (provenanceActual : provenance = prependProvenanceMeasured stage.schedule.entry.var state.provenance)
    (generation : CanonicalStageGeneration (depth + 1))
    (generationActual : generation = generateCanonicalStageFromSource state.generation.target state.generation.targetExact)
    (seed : Var) (seedActual : seed = executedProducedSearchSeed stage)
    (decision : StructuralBranchDecision) (decisionActual : decision = executedBranchDecision stage) :
    fromParts state stage avoid provenance provenanceActual generation generationActual seed seedActual decision decisionActual =
      realizeNextOperationalState state stage avoid := by
  cases provenanceActual; cases generationActual; cases seedActual; cases decisionActual; rfl

def code {depth : Nat} {assignment : SequentialAssignment depth}
    (state : ThreadedConstitutiveState depth assignment) (stage : SequentialStageRun depth assignment)
    (avoid : StructuralDecisionsAvoid (stageSelectedVar (depth + 1)) state.decisions) :
    Code Label (Actual (realizeNextOperationalState state stage avoid)) :=
  (provenanceCode stage.discovery.1 state.provenance).bind (fun provenance =>
  (generationCode state).bind (fun generation =>
  (seedCode stage).bind (fun seed =>
  (decisionCode stage).bind (fun decision =>
    .step .masterConstructionReturn (fun _ => .done
      ⟨fromParts state stage avoid provenance.1 provenance.2 generation.1 generation.2 seed.1 seed.2 decision.1 decision.2,
        from_parts_actual _ _ _ _ _ _ _ _ _ _ _⟩)))))

theorem finite {depth : Nat} {assignment : SequentialAssignment depth}
    (state : ThreadedConstitutiveState depth assignment) (stage : SequentialStageRun depth assignment)
    (avoid : StructuralDecisionsAvoid (stageSelectedVar (depth + 1)) state.decisions) : Finite (code state stage avoid) := by
  apply finite_bind
  · exact finite_step _ _ (finite_done _)
  · intro provenance
    apply finite_bind
    · exact finite_step _ _ (finite_done _)
    · intro generation
      apply finite_bind
      · unfold seedCode; apply finite_step; split <;> exact finite_done _
      · intro seed
        apply finite_bind
        · exact finite_step _ _ (finite_step _ _ (finite_done _))
        · intro decision; exact finite_step _ _ (finite_done _)

end ConstitutiveSearch.Agent.Local.Documentary.ControlNextState

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlNextState.provenanceCode
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlNextState.seedCode
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlNextState.decisionCode
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlNextState.generationCode
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlNextState.fromParts
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlNextState.from_parts_actual
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlNextState.code
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlNextState.finite
/- AXIOM_AUDIT_END -/
