import RelationalPerimeter.Relativity.Production.LocalInstructions
import RelationalPerimeter.Relativity.Production.OccurrenceTransport
import StrongPerimetralTurning

/-!
# Formed local histories, paired production and genuine continuation

Only received instrument resources can root this family. Every later resource
is formed by a positive `Produces` role on the previous values. Source
occurrences are typed references, not their numerical readings. The generic
support projection is an interpretation of this constituted history; it is
not an independent source of events.
-/
set_option genInjectivity false
namespace RelationalPerimeter.Relativity.Production
open ConstitutiveSearch.Resources

inductive Formed : {context : List Kind} → Values Value context → Type where
  | received (input : Received) : Formed (context := receivedKinds) input.values
  | produced {context} {values : Values Value context} (past : Formed (context := context) values)
      {kind} {instruction : Instruction context kind} {output : Value kind}
      (role : Produces values instruction output) :
      Formed (context := kind :: context) (output, values)

/-- Incremental resource interpretation of the same positive local role.
It consumes the already stored interpretation; it does not replay a history. -/
def Produces.resourceFormation {context kind} {values : Values Value context}
    {instruction : Instruction context kind} {output : Value kind}
    (priorFormation : Formation Value (context := context) values)
    (role : Produces values instruction output) :
    Formation Value (context := kind :: context) (output, values) := by
  cases role with
  | emitted reading payload => exact .produced priorFormation (Instruction.emit reading payload).lower
  | relayed signal calibration => exact .produced priorFormation (Instruction.relay signal calibration).lower
  | received signal => exact .produced priorFormation (Instruction.receive signal).lower

/-- The generic support formation is constrained to interpret the same
received root and each same positive role, not merely the same final values.
The roles remain executable data in `Formed`; this additional proposition
checks the raccord and does not replace those constitutive witnesses. -/
inductive ResourceInterpretation :
    {context : List Kind} → {values : Values Value context} →
    Formed (context := context) values → Formation Value (context := context) values → Prop where
  | received (input : Received) : ResourceInterpretation (.received input) (.given input.values)
  | produced {context kind} {values : Values Value context}
      {prior : Formed (context := context) values}
      {priorResource : Formation Value (context := context) values}
      (raccord : ResourceInterpretation prior priorResource)
      {instruction : Instruction context kind} {output : Value kind}
      (role : Produces values instruction output) :
      ResourceInterpretation (.produced prior role) (role.resourceFormation priorResource)

structure Cursor where
  kinds : List Kind
  values : Values Value kinds
  formation : Formed (context := kinds) values
  resourceFormation : Formation Value (context := kinds) values
  resourceExact : ResourceInterpretation formation resourceFormation

def Cursor.received (input : Received) : Cursor :=
  ⟨receivedKinds, input.values, .received input, .given input.values, .received input⟩

def Cursor.support (cursor : Cursor) : Support Value cursor.kinds :=
  ⟨cursor.values, cursor.resourceFormation⟩

def Cursor.read (cursor : Cursor) {kind} (ref : Ref cursor.kinds kind) : Value kind :=
  ConstitutiveSearch.Resources.read cursor.values ref

abbrev Determination (source : Cursor) {kind} (instruction : Instruction source.kinds kind) :=
  (output : Value kind) ×' Produces source.values instruction output

def Cursor.extend (source : Cursor) {kind} {instruction : Instruction source.kinds kind}
    (production : Determination source instruction) : Cursor :=
  ⟨kind :: source.kinds, (production.1, source.values),
    .produced source.formation production.2,
    production.2.resourceFormation source.resourceFormation,
    .produced source.resourceExact production.2⟩

/-- The event and successor share one positive determination. No independently
specified output or completed future is accepted. -/
structure Production (source : Cursor) {kind} (instruction : Instruction source.kinds kind) where
  determination : Determination source instruction
  successor : Cursor
  successorExact : successor = source.extend determination

def perform (source : Cursor) {kind} (instruction : Instruction source.kinds kind) : Production source instruction :=
  let determination := execute source.values instruction
  let successor := source.extend determination
  ⟨determination, successor, rfl⟩

theorem perform_output_exact (source : Cursor) {kind} (instruction : Instruction source.kinds kind) :
    (perform source instruction).determination.1 = instruction.interpret source.values :=
  execute_output_exact ..

theorem perform_successor_exact (source : Cursor) {kind} (instruction : Instruction source.kinds kind) :
    (perform source instruction).successor = source.extend (perform source instruction).determination := rfl

def extendTransport (source : Cursor) {kind} {instruction : Instruction source.kinds kind}
    (production : Determination source instruction) :
    Support.Extension source.support (source.extend production).support where
  references := Ref.prior
  reads := fun _ => rfl
  injective := prior_injective
  added := 1
  positions := fun _ => rfl

def producedOccurrenceTransport (source : Cursor) {kind} {instruction : Instruction source.kinds kind}
    (production : Determination source instruction) :
    ExactTypeTransport (Occurrence source.kinds ⊕ Unit) (Occurrence (source.extend production).kinds) :=
  occurrenceSplit source.kinds kind

def producedResidualRole (source : Cursor) {kind} {instruction : Instruction source.kinds kind}
    (_production : Determination source instruction) := constitutedFreshRole source.kinds kind

theorem old_read_preserved (source : Cursor) {outputKind} {instruction : Instruction source.kinds outputKind}
    (production : Determination source instruction) {kind} (ref : Ref source.kinds kind) :
    (source.extend production).read (.prior ref) = source.read ref := rfl

theorem fresh_distinct (source : Cursor) {kind} {instruction : Instruction source.kinds kind}
    (production : Determination source instruction)
    (old : Ref source.kinds kind) :
    (Ref.here : Ref (source.extend production).kinds kind) ≠ .prior old := by
  intro same
  exact fresh_position_distinct old (congrArg Ref.position same)

/-- The same founded history interface used by the foundations. Step indices
pin the entire successor cursor, not merely one equal numerical boundary. -/
structure Step (source target : Cursor) where
  kind : Kind
  instruction : Instruction source.kinds kind
  determination : Determination source instruction
  targetExact : target = source.extend determination

abbrev LocalHistory := StrongPerimetralTurning.History Step

def oneStepHistory (source : Cursor) {kind} (instruction : Instruction source.kinds kind) :
    LocalHistory source (perform source instruction).successor :=
  let head := perform source instruction
  .extend .root ⟨kind, instruction, head.determination, head.successorExact⟩

def Step.transport {source target} (step : Step source target) :
    Support.Extension source.support target.support :=
  step.targetExact.symm ▸ extendTransport source step.determination

def historyTransport {source target : Cursor} (history : LocalHistory source target) :
    Support.Extension source.support target.support :=
  match history with
  | .root => Support.Extension.identity _
  | .extend past step => (historyTransport past).compose step.transport
termination_by structural history

theorem history_preserves_reads {source target : Cursor} (history : LocalHistory source target)
    {kind} (ref : Ref source.kinds kind) :
    target.read ((historyTransport history).references ref) = source.read ref :=
  (historyTransport history).reads ref

theorem history_preserves_distinction {source target : Cursor} (history : LocalHistory source target)
    {kind} (one two : Ref source.kinds kind) (distinct : one ≠ two) :
    (historyTransport history).references one ≠ (historyTransport history).references two :=
  fun same => distinct ((historyTransport history).injective one two same)

/- The schedule contains instructions and port indices, not future cursors.
Its tail is indexed only by the resource sorts that will become available.
Values and formed histories are produced inside `run`, not when the schedule
is assembled. -/
inductive Program : List Kind → Type where
  | done {context} : Program context
  | step {context kind} (instruction : Instruction context kind)
      (tail : Program (kind :: context)) : Program context

structure Execution (source : Cursor) where
  cursor : Cursor
  history : LocalHistory source cursor

def runFrom {context : List Kind} (schedule : Program context)
    (values : Values Value context) (formation : Formed (context := context) values)
    (resourceFormation : Formation Value (context := context) values)
    (resourceExact : ResourceInterpretation formation resourceFormation) :
    Execution ⟨context, values, formation, resourceFormation, resourceExact⟩ :=
  match schedule with
  | .done => ⟨⟨context, values, formation, resourceFormation, resourceExact⟩, .root⟩
  | .step instruction tail =>
    let source : Cursor := ⟨context, values, formation, resourceFormation, resourceExact⟩
    let head := perform source instruction
    let resumed := runFrom tail head.successor.values head.successor.formation
      head.successor.resourceFormation head.successor.resourceExact
    ⟨resumed.cursor, StrongPerimetralTurning.History.append
      (.extend .root ⟨_, instruction, head.determination, head.successorExact⟩ : LocalHistory source head.successor)
      resumed.history⟩
termination_by structural schedule

def run (source : Cursor) (schedule : Program source.kinds) : Execution source :=
  runFrom schedule source.values source.formation source.resourceFormation source.resourceExact

def Execution.resume {source} (priorRun : Execution source)
    (continuation : Program priorRun.cursor.kinds) : Execution source :=
  let resumed := run priorRun.cursor continuation
  ⟨resumed.cursor, StrongPerimetralTurning.History.append priorRun.history resumed.history⟩

theorem resume_cursor_exact {source} (priorRun : Execution source)
    (continuation : Program priorRun.cursor.kinds) :
    (priorRun.resume continuation).cursor = (run priorRun.cursor continuation).cursor := rfl

/-- The actual runner records the local production before the suffix history.
This is a dependency/formation statement, not a physical timing theorem. -/
theorem run_step_history_exact (source : Cursor) {kind} (instruction : Instruction source.kinds kind)
    (tail : Program (kind :: source.kinds)) :
    (run source (.step instruction tail)).history =
      StrongPerimetralTurning.History.append (oneStepHistory source instruction)
        (run (perform source instruction).successor tail).history := rfl

def Program.steps : {context : List Kind} → Program context → Nat
  | _, .done => 0
  | _, .step _ tail => tail.steps + 1

theorem runFrom_history_length {context} (schedule : Program context)
    (values : Values Value context) (formation : Formed (context := context) values)
    (resourceFormation : Formation Value (context := context) values)
    (resourceExact : ResourceInterpretation formation resourceFormation) :
    StrongPerimetralTurning.History.length (runFrom schedule values formation resourceFormation resourceExact).history =
      schedule.steps := by
  induction schedule with
  | done => rfl
  | step instruction tail ih =>
    change StrongPerimetralTurning.History.length
      (StrongPerimetralTurning.History.append _ _) = _
    dsimp only [perform, Cursor.extend]
    exact (StrongPerimetralTurning.History.length_append _ _).trans
      ((congrArg (fun n => 1 + n) (ih _ _ _ _)).trans (Nat.add_comm 1 tail.steps))

theorem run_history_length (source : Cursor) (schedule : Program source.kinds) :
    StrongPerimetralTurning.History.length (run source schedule).history = schedule.steps :=
  runFrom_history_length schedule source.values source.formation source.resourceFormation source.resourceExact

end RelationalPerimeter.Relativity.Production
/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Relativity.Production.Formed
#print axioms RelationalPerimeter.Relativity.Production.Produces.resourceFormation
#print axioms RelationalPerimeter.Relativity.Production.ResourceInterpretation
#print axioms RelationalPerimeter.Relativity.Production.Cursor.received
#print axioms RelationalPerimeter.Relativity.Production.Cursor.support
#print axioms RelationalPerimeter.Relativity.Production.Cursor.extend
#print axioms RelationalPerimeter.Relativity.Production.perform
#print axioms RelationalPerimeter.Relativity.Production.perform_output_exact
#print axioms RelationalPerimeter.Relativity.Production.perform_successor_exact
#print axioms RelationalPerimeter.Relativity.Production.extendTransport
#print axioms RelationalPerimeter.Relativity.Production.producedOccurrenceTransport
#print axioms RelationalPerimeter.Relativity.Production.producedResidualRole
#print axioms RelationalPerimeter.Relativity.Production.old_read_preserved
#print axioms RelationalPerimeter.Relativity.Production.fresh_distinct
#print axioms RelationalPerimeter.Relativity.Production.oneStepHistory
#print axioms RelationalPerimeter.Relativity.Production.Step.transport
#print axioms RelationalPerimeter.Relativity.Production.historyTransport
#print axioms RelationalPerimeter.Relativity.Production.history_preserves_reads
#print axioms RelationalPerimeter.Relativity.Production.history_preserves_distinction
#print axioms RelationalPerimeter.Relativity.Production.runFrom
#print axioms RelationalPerimeter.Relativity.Production.run
#print axioms RelationalPerimeter.Relativity.Production.Execution.resume
#print axioms RelationalPerimeter.Relativity.Production.resume_cursor_exact
#print axioms RelationalPerimeter.Relativity.Production.run_step_history_exact
#print axioms RelationalPerimeter.Relativity.Production.Program.steps
#print axioms RelationalPerimeter.Relativity.Production.runFrom_history_length
#print axioms RelationalPerimeter.Relativity.Production.run_history_length
/- AXIOM_AUDIT_END -/
