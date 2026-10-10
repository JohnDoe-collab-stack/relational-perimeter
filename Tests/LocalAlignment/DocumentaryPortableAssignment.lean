import Tests.LocalAlignment.DocumentaryControlCodec
import RelationalPerimeter.Computation.ConstitutiveSearch.EndogenousDecomposition.SequentialResolution

/-! First-order formation of the actual assignment AND its measured reader.
The alternating seed is a declared primitive. Reflection consumes the returned
transport-code structure, including identity and composition visits. Restoring
builds reader closures; it does not query them or execute historical stages.
No arbitrary function, full SequentialAssignment or master cursor codec is claimed. -/
set_option genInjectivity false
set_option maxHeartbeats 3000000
namespace ConstitutiveSearch.Agent.Local.Documentary.PortableAssignment
open SAT EndogenousDecomposition

structure Bundle where
  assignment : Assignment
  reader : MeasuredAssignment assignment

def sequential {depth} (value : SequentialAssignment depth) : Bundle :=
  ⟨value.assignment, value.reader⟩

def seed : Bundle := ⟨alternatingAssignmentBit, readAlternatingAssignment⟩

def visit (before : Bundle) : Bundle :=
  ⟨before.assignment, fun query =>
    let output := before.reader query
    ⟨output.value, output.valueExact, output.work.visit⟩⟩

def flip (selected : Var) (before : Bundle) : Bundle :=
  ⟨Assignment.flipAt selected before.assignment, readFlippedAssignment selected before.reader⟩

inductive Command where
  | visit
  | flip (selected : Var)

abbrev Code := List Command

/-- Commands are stored newest first; each constructor consumes its prior reader. -/
def interpret : Code → Bundle
  | [] => seed
  | .visit :: prior => visit (interpret prior)
  | .flip selected :: prior => flip selected (interpret prior)

structure Formed (value : Bundle) where
  code : Code
  exact : interpret code = value

def initial_formed (depth : Nat) : Formed (sequential (initialSequentialAssignment depth)) :=
  ⟨[], rfl⟩

def capture {value} (formed : Formed value) : Code := formed.code

theorem capture_exact {value} (formed : Formed value) : interpret (capture formed) = value :=
  formed.exact

theorem all_consumers {value} (formed : Formed value) {Result : Type u}
    (consume : Bundle → Result) : consume (interpret (capture formed)) = consume value :=
  congrArg consume formed.exact

def reflect {root : Cnf} {selected : Var} (label : Var) :
    {source target : GeneratedStructuralBranchContext root} →
    TransportCode (GeneratedStructuralFlipAtRelation selected) source target → Code → Code
  | _, _, .identity _, prior => .visit :: prior
  | _, _, .atom _, prior => .flip label :: prior
  | _, _, .compose first second, prior =>
      .visit :: reflect label second (reflect label first prior)

def transported {root : Cnf} (selected : Var)
    {source target : GeneratedStructuralBranchContext root}
    (code : TransportCode (GeneratedStructuralFlipAtRelation selected) source target)
    (input : GeneratedStructuralBranchContinuation source)
    (reader : MeasuredAssignment input.1) : Bundle :=
  ⟨((code.eval (generatedStructuralFlipAtAction root selected)).map input).1,
    readTransportedAssignment selected code input reader⟩

/-- The actual code, not a prescribed flip list, determines the next recipe. -/
theorem reflect_exact {root : Cnf} (selected : Var)
    {source target : GeneratedStructuralBranchContext root}
    (code : TransportCode (GeneratedStructuralFlipAtRelation selected) source target)
    (input : GeneratedStructuralBranchContinuation source)
    (reader : MeasuredAssignment input.1) (prior : Code)
    (actual : interpret prior = (⟨input.1, reader⟩ : Bundle)) :
    interpret (reflect selected code prior) = transported selected code input reader := by
  induction code generalizing prior with
  | identity source =>
      exact congrArg visit actual
  | atom relation =>
      exact congrArg (flip selected) actual
  | @compose source middle target first second ihFirst ihSecond =>
      have firstExact := ihFirst input reader prior actual
      have secondExact := ihSecond
        ((first.eval (generatedStructuralFlipAtAction root selected)).map input)
        (readTransportedAssignment selected first input reader)
        (reflect selected first prior) firstExact
      exact congrArg visit secondExact

def transport_formed {root : Cnf} (selected : Var)
    {source target : GeneratedStructuralBranchContext root}
    (code : TransportCode (GeneratedStructuralFlipAtRelation selected) source target)
    (input : GeneratedStructuralBranchContinuation source)
    (reader : MeasuredAssignment input.1) (prior : Formed (⟨input.1, reader⟩ : Bundle)) :
    Formed (transported selected code input reader) :=
  ⟨reflect selected code prior.code, reflect_exact selected code input reader prior.code prior.exact⟩

theorem bundle_same {left right : Assignment}
    {first : MeasuredAssignment left} {second : MeasuredAssignment right}
    (assignmentExact : left = right) (readerExact : HEq first second) :
    (⟨left, first⟩ : Bundle) = ⟨right, second⟩ := by
  cases assignmentExact
  cases readerExact
  rfl

theorem cast_bundle {left right : Assignment} (reader : MeasuredAssignment left)
    (same : right = left) :
    (⟨right, Eq.rec (motive := fun assignment _ => MeasuredAssignment assignment)
      reader same.symm⟩ : Bundle) = ⟨left, reader⟩ := by
  cases same
  rfl

def stageInput {depth input} (stage : SequentialStageRun depth input) : Bundle :=
  ⟨stage.sourceContinuation.1,
    Eq.rec (motive := fun assignment _ => MeasuredAssignment assignment)
      input.reader stage.sourceAssignmentExact.symm⟩

theorem stage_input_exact {depth input} (stage : SequentialStageRun depth input) :
    stageInput stage = sequential input :=
  cast_bundle input.reader stage.sourceAssignmentExact

theorem stage_output_exact {depth input} (stage : SequentialStageRun depth input) :
    sequential stage.next =
      transported stage.schedule.entry.var stage.execution.code stage.sourceContinuation
        (stageInput stage).reader :=
  bundle_same
    (stage.nextAssignmentExact.trans stage.application.assignment_from_returned_code)
    stage.nextReaderExact

theorem stage_variable_exact {depth input} (stage : SequentialStageRun depth input) :
    stage.discovery.var = stage.schedule.entry.var := by
  rw [stage.scheduleExact]
  rfl

theorem stage_recipe_exact {depth input} (stage : SequentialStageRun depth input)
    (prior : Code) (actual : interpret prior = sequential input) :
    interpret (reflect stage.discovery.var stage.execution.code prior) =
      sequential stage.next := by
  rw [stage_variable_exact]
  exact (reflect_exact stage.schedule.entry.var stage.execution.code stage.sourceContinuation
    (stageInput stage).reader prior (actual.trans (stage_input_exact stage).symm)).trans
    (stage_output_exact stage).symm

/-- Reads the executed stage's returned code; never rebuilds discovery or application. -/
def stage_formed {depth input} (stage : SequentialStageRun depth input)
    (prior : Formed (sequential input)) : Formed (sequential stage.next) :=
  ⟨reflect stage.discovery.var stage.execution.code prior.code,
    stage_recipe_exact stage prior.code prior.exact⟩

def readQueries (data : Bundle) (queries : List Var) :
    List Bool × ComparisonWork :=
  let output := readAssignmentQueries data.reader queries
  (output.bits, output.work)

theorem restored_queries {value} (formed : Formed value) (queries : List Var) :
    readQueries (interpret (capture formed)) queries = readQueries value queries :=
  all_consumers formed (fun data => readQueries data queries)

end ConstitutiveSearch.Agent.Local.Documentary.PortableAssignment
/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableAssignment.Bundle
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableAssignment.sequential
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableAssignment.seed
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableAssignment.visit
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableAssignment.flip
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableAssignment.Command
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableAssignment.Code
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableAssignment.interpret
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableAssignment.Formed
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableAssignment.initial_formed
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableAssignment.capture
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableAssignment.capture_exact
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableAssignment.all_consumers
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableAssignment.reflect
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableAssignment.transported
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableAssignment.reflect_exact
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableAssignment.transport_formed
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableAssignment.bundle_same
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableAssignment.cast_bundle
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableAssignment.stageInput
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableAssignment.stage_input_exact
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableAssignment.stage_output_exact
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableAssignment.stage_variable_exact
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableAssignment.stage_recipe_exact
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableAssignment.stage_formed
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableAssignment.readQueries
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableAssignment.restored_queries
/- AXIOM_AUDIT_END -/
