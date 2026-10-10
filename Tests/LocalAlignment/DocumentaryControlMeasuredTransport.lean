import Tests.LocalAlignment.DocumentaryControlMeasuredSchedule
import RelationalPerimeter.Computation.ConstitutiveSearch.EndogenousDecomposition.SequentialResolution

/-! Interpret the actual returned transport code, consuming the first output
in its second component. Function-valued assignments are formed here; their
later bit reads are a distinct obligation, not a constant-time oracle. -/
set_option genInjectivity false
set_option maxHeartbeats 8000000
namespace ConstitutiveSearch.Agent.Local.Documentary.ControlMeasuredTransport
open SAT EndogenousDecomposition Control ControlBindings ControlMasterData

def code {system : SearchSystem} {Generator : system.State → system.State → Type}
    (action : AcceptedRelationalAction system Generator)
    (operation : {source target : system.State} → (witness : Generator source target) →
      (input : system.Continuation source) → Code Label (Actual ((action.toTransport witness).map input))) :
    {source target : system.State} → (program : TransportCode Generator source target) →
    (input : system.Continuation source) → Code Label (Actual (applyMeasuredTransportCode action program input))
  | _, _, .identity _, input => .step .controlInspect (fun _ =>
    .step .masterConstructionReturn (fun _ => .done ⟨⟨input, 0, 0, rfl, rfl, rfl⟩, rfl⟩))
  | _, _, .atom witness, input => .step .controlInspect (fun _ =>
    .step .controlCall (fun _ => (operation witness input).bind (fun mapped =>
      .step .masterConstructionReturn (fun _ => .done
        ⟨⟨mapped.1, 1, 1, mapped.2, rfl, rfl⟩,
          by obtain ⟨_, actual⟩ := mapped; cases actual; rfl⟩))))
  | _, _, .compose first second, input => .step .controlInspect (fun _ =>
    (code action operation first input).bind (fun middle =>
    (code action operation second middle.1.output).bind (fun output =>
    (ControlArithmetic.addCode middle.1.evaluatedAtoms output.1.evaluatedAtoms).bind (fun atoms =>
    (ControlArithmetic.addCode middle.1.continuationApplications output.1.continuationApplications).bind
      (fun applications => .step .masterConstructionReturn (fun _ => .done
        ⟨⟨output.1.output, atoms.1, applications.1,
            by rw [output.1.outputExact, middle.1.outputExact]; rfl,
            by rw [atoms.2, middle.1.evaluatedAtomsExact, output.1.evaluatedAtomsExact]; rfl,
            by rw [applications.2, middle.1.continuationApplicationsExact,
              output.1.continuationApplicationsExact]; rfl⟩,
          by obtain ⟨_, actual⟩ := applications; cases actual
             obtain ⟨_, actual⟩ := atoms; cases actual
             obtain ⟨_, actual⟩ := output; cases actual
             obtain ⟨_, actual⟩ := middle; cases actual; rfl⟩))))))

theorem finite {system : SearchSystem} {Generator : system.State → system.State → Type}
    (action : AcceptedRelationalAction system Generator)
    (operation : {source target : system.State} → (witness : Generator source target) →
      (input : system.Continuation source) → Code Label (Actual ((action.toTransport witness).map input)))
    (closed : ∀ {source target} (witness : Generator source target) (input : system.Continuation source),
      Finite (operation witness input))
    {source target : system.State} (program : TransportCode Generator source target)
    (input : system.Continuation source) : Finite (code action operation program input) := by
  induction program with
  | identity _ => exact finite_step _ _ (finite_step _ _ (finite_done _))
  | atom witness =>
    apply finite_step; apply finite_step; apply finite_bind (closed witness input); intro mapped
    exact finite_step _ _ (finite_done _)
  | compose first second firstFinite secondFinite =>
    apply finite_step; apply finite_bind (firstFinite input); intro middle
    apply finite_bind (secondFinite middle.1.output); intro output
    apply finite_bind
    · obtain ⟨value, labels, trace, _⟩ := ControlArithmetic.add_bounded
        middle.1.evaluatedAtoms output.1.evaluatedAtoms
      exact ⟨value, labels, trace⟩
    · intro atoms
      apply finite_bind
      · obtain ⟨value, labels, trace, _⟩ := ControlArithmetic.add_bounded
          middle.1.continuationApplications output.1.continuationApplications
        exact ⟨value, labels, trace⟩
      · intro applications; exact finite_step _ _ (finite_done _)

def mapCode {root : Cnf} (selected : Var) {source target : GeneratedStructuralBranchContext root}
    (relation : GeneratedStructuralFlipAtRelation selected source target)
    (input : GeneratedStructuralBranchContinuation source) :
    Code Label (Actual (((generatedStructuralFlipAtAction root selected).toTransport relation).map input)) :=
  .step .controlClosure (fun _ =>
    let assignment : Assignment := fun query =>
      if query = selected then !(input.1 query) else input.1 query
    .step .masterConstructionReturn (fun _ => .done
      ⟨⟨assignment, relation.mapContinuation input |>.property⟩, rfl⟩))

theorem map_finite {root : Cnf} (selected : Var) {source target : GeneratedStructuralBranchContext root}
    (relation : GeneratedStructuralFlipAtRelation selected source target)
    (input : GeneratedStructuralBranchContinuation source) : Finite (mapCode selected relation input) :=
  finite_step _ _ (finite_step _ _ (finite_done _))

def flipCode {root : Cnf} (selected : Var) {source target : GeneratedStructuralBranchContext root}
    (program : TransportCode (GeneratedStructuralFlipAtRelation selected) source target)
    (input : GeneratedStructuralBranchContinuation source) :
    Code Label (Actual (applyMeasuredTransportCode (generatedStructuralFlipAtAction root selected) program input)) :=
  code (generatedStructuralFlipAtAction root selected) (mapCode selected) program input

theorem flip_finite {root : Cnf} (selected : Var) {source target : GeneratedStructuralBranchContext root}
    (program : TransportCode (GeneratedStructuralFlipAtRelation selected) source target)
    (input : GeneratedStructuralBranchContinuation source) : Finite (flipCode selected program input) :=
  finite (generatedStructuralFlipAtAction root selected) (mapCode selected)
    (fun relation input => map_finite selected relation input) program input

def appliedFromRun {root : Cnf} {state : GeneratedStructuralBranchContext root}
    {discovery : EndogenousFlipDiscovery state} {schedule : DiscoverySchedule discovery}
    {validation : ValidatedDiscoverySchedule schedule} (execution : ExecutedDiscoverySchedule validation)
    (input : GeneratedStructuralBranchContinuation schedule.entry.source)
    (run : MeasuredTransportApplication (generatedStructuralFlipAtAction root schedule.entry.var) execution.code input)
    (actual : run = applyMeasuredTransportCode (generatedStructuralFlipAtAction root schedule.entry.var)
      execution.code input) : AppliedDiscoveryExecution execution input :=
  { output := run.output, outputExact := run.outputExact
    evaluatedAtoms := run.evaluatedAtoms, continuationApplications := run.continuationApplications
    outputFromInstrumentedRun := by rw [← actual]
    evaluatedAtomsFromInstrumentedRun := by rw [← actual]
    continuationApplicationsFromInstrumentedRun := by rw [← actual]
    evaluatedAtomsExact := run.evaluatedAtomsExact
    continuationApplicationsExact := run.continuationApplicationsExact }

theorem applied_from_run_actual {root : Cnf} {state : GeneratedStructuralBranchContext root}
    {discovery : EndogenousFlipDiscovery state} {schedule : DiscoverySchedule discovery}
    {validation : ValidatedDiscoverySchedule schedule} (execution : ExecutedDiscoverySchedule validation)
    (input : GeneratedStructuralBranchContinuation schedule.entry.source)
    (run : MeasuredTransportApplication (generatedStructuralFlipAtAction root schedule.entry.var) execution.code input)
    (actual : run = applyMeasuredTransportCode (generatedStructuralFlipAtAction root schedule.entry.var)
      execution.code input) : appliedFromRun execution input run actual = applyDiscoveryExecution execution input := by
  cases actual
  unfold appliedFromRun applyDiscoveryExecution
  congr 1
  exact (applyMeasuredTransportCode (generatedStructuralFlipAtAction root schedule.entry.var)
    execution.code input).outputExact

def applicationCode {root : Cnf} {state : GeneratedStructuralBranchContext root}
    {discovery : EndogenousFlipDiscovery state} {schedule : DiscoverySchedule discovery}
    {validation : ValidatedDiscoverySchedule schedule} (execution : ExecutedDiscoverySchedule validation)
    (input : GeneratedStructuralBranchContinuation schedule.entry.source) :
    Code Label (Actual (applyDiscoveryExecution execution input)) :=
  (flipCode discovery.1 execution.code input).bind (fun run =>
    .step .masterConstructionReturn (fun _ => .done
      ⟨appliedFromRun execution input run.1 run.2, applied_from_run_actual _ _ _ _⟩))

theorem application_finite {root : Cnf} {state : GeneratedStructuralBranchContext root}
    {discovery : EndogenousFlipDiscovery state} {schedule : DiscoverySchedule discovery}
    {validation : ValidatedDiscoverySchedule schedule} (execution : ExecutedDiscoverySchedule validation)
    (input : GeneratedStructuralBranchContinuation schedule.entry.source) :
    Finite (applicationCode execution input) := by
  apply finite_bind (flip_finite _ _ _); intro run
  exact finite_step _ _ (finite_done _)

end ConstitutiveSearch.Agent.Local.Documentary.ControlMeasuredTransport

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMeasuredTransport.code
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMeasuredTransport.finite
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMeasuredTransport.mapCode
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMeasuredTransport.map_finite
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMeasuredTransport.flipCode
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMeasuredTransport.flip_finite
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMeasuredTransport.appliedFromRun
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMeasuredTransport.applied_from_run_actual
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMeasuredTransport.applicationCode
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMeasuredTransport.application_finite
/- AXIOM_AUDIT_END -/
