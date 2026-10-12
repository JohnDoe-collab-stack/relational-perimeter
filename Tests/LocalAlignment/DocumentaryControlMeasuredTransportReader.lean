import Tests.LocalAlignment.DocumentaryControlMeasuredTransport
import Tests.LocalAlignment.DocumentaryControlMeasuredAssignmentReader

/-! Apply the actual master transport while simultaneously retaining the
executable measured reader. Composition consumes the first run's actual
continuation and reader. Entire application counters remain original. -/
set_option genInjectivity false
set_option backward.match.sparseCases false
set_option maxHeartbeats 8000000
namespace ConstitutiveSearch.Agent.Local.Documentary.ControlMeasuredTransportReader
open SAT EndogenousDecomposition Control ControlBindings ControlMasterData
open ControlMeasuredAssignmentReader

structure Produced {root : Cnf} (selected : Var)
    {source target : GeneratedStructuralBranchContext root}
    (program : TransportCode (GeneratedStructuralFlipAtRelation selected) source target)
    (input : GeneratedStructuralBranchContinuation source) (readInput : MeasuredAssignment input.1) where
  run : Actual (applyMeasuredTransportCode (generatedStructuralFlipAtAction root selected) program input)
  reader : Reader (readTransportedAssignment selected program input readInput)

def continuationReader {root : Cnf} {selected : Var}
    {source target : GeneratedStructuralBranchContext root}
    {program : TransportCode (GeneratedStructuralFlipAtRelation selected) source target}
    {input : GeneratedStructuralBranchContinuation source} {readInput : MeasuredAssignment input.1}
    (received : Produced selected program input readInput) : MeasuredAssignment received.run.1.output.1 :=
  Eq.rec (motive := fun assignment _ => MeasuredAssignment assignment)
    (readTransportedAssignment selected program input readInput)
    (congrArg Subtype.val received.run.1.outputExact).symm

def realizedReader {root : Cnf} {selected : Var}
    {source target : GeneratedStructuralBranchContext root}
    {program : TransportCode (GeneratedStructuralFlipAtRelation selected) source target}
    {input : GeneratedStructuralBranchContinuation source} {readInput : MeasuredAssignment input.1}
    (received : Produced selected program input readInput) : Reader (continuationReader received) :=
  castReader _ (congrArg Subtype.val received.run.1.outputExact).symm received.reader

theorem compose_reader_cast {root : Cnf} (selected : Var)
    {source middle target : GeneratedStructuralBranchContext root}
    (first : TransportCode (GeneratedStructuralFlipAtRelation selected) source middle)
    (second : TransportCode (GeneratedStructuralFlipAtRelation selected) middle target)
    (input : GeneratedStructuralBranchContinuation source) (readInput : MeasuredAssignment input.1)
    (actual : GeneratedStructuralBranchContinuation middle)
    (same : actual = (first.eval (generatedStructuralFlipAtAction root selected)).map input) :
    HEq ((PortableAssignment.visit ⟨_, readTransportedAssignment selected second actual
      (Eq.rec (motive := fun assignment _ => MeasuredAssignment assignment)
        (readTransportedAssignment selected first input readInput)
        (congrArg Subtype.val same).symm)⟩).reader)
      (readTransportedAssignment selected (.compose first second) input readInput) := by
  cases same; rfl

def code {root : Cnf} (selected : Var) :
    {source target : GeneratedStructuralBranchContext root} →
    (program : TransportCode (GeneratedStructuralFlipAtRelation selected) source target) →
    (input : GeneratedStructuralBranchContinuation source) → (readInput : MeasuredAssignment input.1) →
    Reader readInput → Code Label (Produced selected program input readInput)
  | _, _, .identity _, input, readInput, realized => .step .controlInspect (fun _ =>
    .step .controlClosure (fun _ =>
      let reader := visitedReader realized
      .step .masterConstructionReturn (fun _ => .done
        ⟨⟨⟨input, 0, 0, rfl, rfl, rfl⟩, rfl⟩, reader⟩)))
  | _, _, .atom witness, input, readInput, realized => .step .controlInspect (fun _ =>
    .step .controlCall (fun _ =>
      (ControlMeasuredTransport.mapCode selected witness input).bind (fun mapped =>
        .step .controlClosure (fun _ =>
          let reader := flippedReader selected realized
          .step .masterConstructionReturn (fun _ => .done
            ⟨⟨⟨mapped.1, 1, 1, mapped.2, rfl, rfl⟩,
              by obtain ⟨_, actual⟩ := mapped; cases actual; rfl⟩, reader⟩)))))
  | _, _, .compose first second, input, readInput, realized => .step .controlInspect (fun _ =>
    (code selected first input readInput realized).bind (fun middle =>
      (code selected second middle.run.1.output (continuationReader middle)
        (realizedReader middle)).bind (fun output =>
        (ControlArithmetic.addCode middle.run.1.evaluatedAtoms output.run.1.evaluatedAtoms).bind (fun atoms =>
          (ControlArithmetic.addCode middle.run.1.continuationApplications output.run.1.continuationApplications).bind
            (fun applications => .step .controlClosure (fun _ =>
              let reader := visitedReader output.reader
              have sameAssignment : _ =
                  (((TransportCode.compose first second).eval
                    (generatedStructuralFlipAtAction root selected)).map input).1 := by
                change ((second.eval (generatedStructuralFlipAtAction root selected)).map middle.run.1.output).1 = _
                exact congrArg (fun continuation =>
                  ((second.eval (generatedStructuralFlipAtAction root selected)).map continuation).1)
                  middle.run.1.outputExact
              have sameReader : HEq
                  ((PortableAssignment.visit
                    ⟨_, readTransportedAssignment selected second middle.run.1.output
                      (continuationReader middle)⟩).reader)
                  (readTransportedAssignment selected (.compose first second) input readInput) := by
                exact compose_reader_cast selected first second input readInput _ middle.run.1.outputExact
              let aligned := retarget sameAssignment sameReader reader
              .step .masterConstructionReturn (fun _ => .done
                ⟨⟨⟨output.run.1.output, atoms.1, applications.1,
                    by rw [output.run.1.outputExact, middle.run.1.outputExact]; rfl,
                    by rw [atoms.2, middle.run.1.evaluatedAtomsExact, output.run.1.evaluatedAtomsExact]; rfl,
                    by rw [applications.2, middle.run.1.continuationApplicationsExact,
                      output.run.1.continuationApplicationsExact]; rfl⟩,
                  by obtain ⟨_, actual⟩ := applications; cases actual
                     obtain ⟨_, actual⟩ := atoms; cases actual
                     obtain ⟨_, actual⟩ := output.run; cases actual
                     obtain ⟨_, actual⟩ := middle.run; cases actual; rfl⟩, aligned⟩)))))))

theorem finite {root : Cnf} (selected : Var)
    {source target : GeneratedStructuralBranchContext root}
    (program : TransportCode (GeneratedStructuralFlipAtRelation selected) source target)
    (input : GeneratedStructuralBranchContinuation source) (readInput : MeasuredAssignment input.1)
    (realized : Reader readInput) : Finite (code selected program input readInput realized) := by
  induction program with
  | identity =>
    rw [code]; apply finite_step; apply finite_step; apply finite_step; exact finite_done _
  | atom witness =>
    apply finite_step; apply finite_step
    apply finite_bind (ControlMeasuredTransport.map_finite selected witness input); intro mapped
    apply finite_step; apply finite_step; exact finite_done _
  | compose first second firstFinite secondFinite =>
    apply finite_step
    apply finite_bind (firstFinite input readInput realized); intro middle
    apply finite_bind (secondFinite _ _ (realizedReader middle)); intro output
    apply finite_bind
    · obtain ⟨value, labels, trace, _⟩ := ControlArithmetic.add_bounded _ _
      exact ⟨value, labels, trace⟩
    · intro atoms
      apply finite_bind
      · obtain ⟨value, labels, trace, _⟩ := ControlArithmetic.add_bounded _ _
        exact ⟨value, labels, trace⟩
      · intro applications
        apply finite_step; apply finite_step; exact finite_done _

structure Applied {root : Cnf} {state : GeneratedStructuralBranchContext root}
    {discovery : EndogenousFlipDiscovery state}
    {validation : ValidatedDiscoverySchedule (scheduleFromDiscovery discovery)}
    (execution : ExecutedDiscoverySchedule validation)
    (input : GeneratedStructuralBranchContinuation (scheduleFromDiscovery discovery).entry.source)
    (readInput : MeasuredAssignment input.1) where
  application : Actual (applyDiscoveryExecution execution input)
  reader : Reader (readTransportedAssignment discovery.var execution.code input readInput)

def applicationCode {root : Cnf} {state : GeneratedStructuralBranchContext root}
    {discovery : EndogenousFlipDiscovery state} (stored : StoredLocalSchedule discovery)
    {validation : ValidatedDiscoverySchedule (scheduleFromDiscovery discovery)}
    (execution : ExecutedDiscoverySchedule validation)
    (input : GeneratedStructuralBranchContinuation (scheduleFromDiscovery discovery).entry.source)
    (readInput : MeasuredAssignment input.1) (realized : Reader readInput) :
    Code Label (Applied execution input readInput) :=
  let received := ControlScheduleCache.input stored input
  have sameInput : received.1 = input.1 := by rcases stored with ⟨entry, actual⟩; cases actual; rfl
  let cachedInput := Eq.rec (motive := fun assignment _ => MeasuredAssignment assignment)
    readInput sameInput.symm
  let cachedReader := castReader _ sameInput.symm realized
  (code discovery.var (ControlScheduleCache.program stored execution) received cachedInput cachedReader).bind
    (fun returned => .step .masterConstructionReturn (fun _ =>
      let run := ControlScheduleCache.originalRun stored execution input returned.run.1
      have runActual := ControlScheduleCache.original_run_actual stored execution input returned.run.1 returned.run.2
      let application : Actual (applyDiscoveryExecution execution input) :=
        ⟨ControlMeasuredTransport.appliedFromRun execution input run runActual,
          ControlMeasuredTransport.applied_from_run_actual execution input run runActual⟩
      have sameOutput : _ = ((execution.code.eval
          (generatedStructuralFlipAtAction root discovery.var)).map input).1 := by
        rcases stored with ⟨entry, actual⟩; cases actual; rfl
      have sameReader : HEq
          (readTransportedAssignment discovery.var (ControlScheduleCache.program stored execution) received cachedInput)
          (readTransportedAssignment discovery.var execution.code input readInput) := by
        rcases stored with ⟨entry, actual⟩; cases actual; rfl
      .done ⟨application, retarget sameOutput sameReader returned.reader⟩))

theorem application_finite {root : Cnf} {state : GeneratedStructuralBranchContext root}
    {discovery : EndogenousFlipDiscovery state} (stored : StoredLocalSchedule discovery)
    {validation : ValidatedDiscoverySchedule (scheduleFromDiscovery discovery)}
    (execution : ExecutedDiscoverySchedule validation)
    (input : GeneratedStructuralBranchContinuation (scheduleFromDiscovery discovery).entry.source)
    (readInput : MeasuredAssignment input.1) (realized : Reader readInput) :
    Finite (applicationCode stored execution input readInput realized) := by
  unfold applicationCode
  apply finite_bind (finite _ _ _ _ _); intro returned
  exact finite_step _ _ (finite_done _)

end ConstitutiveSearch.Agent.Local.Documentary.ControlMeasuredTransportReader

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMeasuredTransportReader.Produced
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMeasuredTransportReader.continuationReader
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMeasuredTransportReader.realizedReader
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMeasuredTransportReader.compose_reader_cast
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMeasuredTransportReader.code
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMeasuredTransportReader.finite
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMeasuredTransportReader.Applied
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMeasuredTransportReader.applicationCode
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMeasuredTransportReader.application_finite
/- AXIOM_AUDIT_END -/
