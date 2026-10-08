import RelationalPerimeter.Relativity.Production.IndependentExchange
import RelationalPerimeter.Relativity.Production.LocalFutureContract

/-!
# Continuations from corresponding constituted cursors

The correspondence preserves readings and positively transports used edges in
both directions. Each extension consumes the two actual paired productions;
it does not rerun them to recover their successor. The runner executes one
production in each presentation, then passes their shared results to the suffix.
This covers arbitrary finite typed programs. Addressed requests, their refusals
and their complete transported contract are a separate obligation.
-/
set_option genInjectivity false
namespace RelationalPerimeter.Relativity.Production
open ConstitutiveSearch.Resources

def InputPort.returned {source target : List Kind} (transport : ReferenceTransport source target)
    {outputKind inputKind} (instruction : Instruction source outputKind) {ref : Ref target inputKind}
    (port : InputPort (instruction.rename transport.forward) ref) :
    InputPort instruction (transport.backward ref) :=
  (Instruction.rename_returns transport instruction) ▸ port.rename transport.backward

structure ConstitutedRaccord (source target : Cursor) where
  reading : ReadRaccord source target
  forwardUsed : ∀ {one two : Occurrence source.kinds}, Used source.formation one two →
    Used target.formation (reading.references.occurrences.forward one)
      (reading.references.occurrences.forward two)
  backwardUsed : ∀ {one two : Occurrence target.kinds}, Used target.formation one two →
    Used source.formation (reading.references.occurrences.backward one)
      (reading.references.occurrences.backward two)

def independentPairConstitution {source firstKind secondKind}
    {first : Instruction source.kinds firstKind} {second : Instruction source.kinds secondKind}
    (original : IndependentPairProduction source first second)
    (reversed : IndependentPairProduction source second first) :
    ConstitutedRaccord original.cursor reversed.cursor :=
  ⟨independentPairRaccord original reversed, independentPairUsed original reversed,
    independentPairUsed reversed original⟩

def ConstitutedRaccord.reverse {source target} (raccord : ConstitutedRaccord source target) :
    ConstitutedRaccord target source :=
  ⟨raccord.reading.reverse, raccord.backwardUsed, raccord.forwardUsed⟩

theorem ConstitutedRaccord.used_iff {source target} (raccord : ConstitutedRaccord source target)
    (one two : Occurrence source.kinds) :
    Nonempty (Used target.formation (raccord.reading.references.occurrences.forward one)
      (raccord.reading.references.occurrences.forward two)) ↔ Nonempty (Used source.formation one two) := by
  constructor
  · intro ⟨edge⟩
    have returned := raccord.backwardUsed edge
    rw [raccord.reading.references.occurrences.forwardBackward one,
      raccord.reading.references.occurrences.forwardBackward two] at returned
    exact ⟨returned⟩
  · intro ⟨edge⟩
    exact ⟨raccord.forwardUsed edge⟩

def ConstitutedRaccord.forwardPath {source target} (raccord : ConstitutedRaccord source target)
    {one two : Occurrence source.kinds} (path : UsedPath source.formation one two) :
    UsedPath target.formation (raccord.reading.references.occurrences.forward one)
      (raccord.reading.references.occurrences.forward two) :=
  match path with
  | .single edge => .single (raccord.forwardUsed edge)
  | .cons head tail => .cons (raccord.forwardUsed head) (raccord.forwardPath tail)
termination_by structural path

theorem paired_outputs_exact {source target} (raccord : ReadRaccord source target)
    {kind} {instruction : Instruction source.kinds kind}
    (first : Production source instruction)
    (second : Production target (instruction.rename raccord.references.forward)) :
    second.determination.1 = first.determination.1 :=
  second.determination.2.output_exact.trans
    ((instruction.rename_interpret _ source.values target.values raccord.reads).trans
      first.determination.2.output_exact.symm)

/-- The positive roles and actual successor equalities are consumed here.
Neither a prescribed output nor a reconstructed suffix is a parameter. -/
def ConstitutedRaccord.afterProduction {source target} (raccord : ConstitutedRaccord source target)
    {kind} {instruction : Instruction source.kinds kind}
    (first : Production source instruction)
    (second : Production target (instruction.rename raccord.reading.references.forward)) :
    ConstitutedRaccord first.successor second.successor := by
  cases first with
  | mk firstDetermination firstSuccessor firstExact =>
    cases firstExact
    cases second with
    | mk secondDetermination secondSuccessor secondExact =>
      cases secondExact
      refine ⟨⟨raccord.reading.references.extend kind, ?_⟩, ?_, ?_⟩
      · intro readKind ref
        cases ref with
        | here =>
          exact paired_outputs_exact raccord.reading
            ⟨firstDetermination, _, rfl⟩ ⟨secondDetermination, _, rfl⟩
        | prior old => exact raccord.reading.reads old
      · intro one two edge
        cases edge with
        | produced past role ref port =>
          exact .produced target.formation secondDetermination.2
            (raccord.reading.references.forward ref) (port.rename raccord.reading.references.forward)
        | inherited role oldEdge => exact .inherited secondDetermination.2 (raccord.forwardUsed oldEdge)
      · intro one two edge
        cases edge with
        | produced past role ref port =>
          exact .produced source.formation firstDetermination.2
            (raccord.reading.references.backward ref) (port.returned raccord.reading.references instruction)
        | inherited role oldEdge => exact .inherited firstDetermination.2 (raccord.backwardUsed oldEdge)

/-- Positive result of the two executions and their constituted raccord. -/
structure ContinuedPair (source target : Cursor) where
  first : Execution source
  second : Execution target
  raccord : ConstitutedRaccord first.cursor second.cursor

def Program.rename {source target : List Kind} (transport : ReferenceTransport source target)
    (schedule : Program source) : Program target :=
  match schedule with
  | .done => .done
  | .step instruction tail => .step (instruction.rename transport.forward)
      (tail.rename (transport.extend _))
termination_by structural schedule

theorem Program.rename_returns {source target : List Kind} (transport : ReferenceTransport source target)
    (schedule : Program source) : (schedule.rename transport).rename transport.reverse = schedule := by
  induction schedule generalizing target with
  | done => rfl
  | step instruction tail ih =>
    change Program.step ((instruction.rename transport.forward).rename transport.backward)
      ((tail.rename (transport.extend _)).rename (transport.extend _).reverse) = _
    rw [Instruction.rename_returns]
    exact congrArg (Program.step instruction) (ih (transport.extend _))

def prefixProduction {source kind} {instruction : Instruction source.kinds kind}
    (head : Production source instruction) (suffix : Execution head.successor) : Execution source :=
  ⟨suffix.cursor, StrongPerimetralTurning.History.append
    (.extend .root ⟨kind, instruction, head.determination, head.successorExact⟩) suffix.history⟩

def continueFrom {context} (schedule : Program context)
    (values : Values Value context) (formation : Formed (context := context) values)
    (resourceFormation : Formation Value (context := context) values)
    (resourceExact : ResourceInterpretation formation resourceFormation) (target : Cursor)
    (raccord : ConstitutedRaccord ⟨context, values, formation, resourceFormation, resourceExact⟩ target) :
    ContinuedPair ⟨context, values, formation, resourceFormation, resourceExact⟩ target :=
  match schedule with
  | .done => ⟨⟨⟨context, values, formation, resourceFormation, resourceExact⟩, .root⟩,
      ⟨target, .root⟩, raccord⟩
  | .step instruction tail =>
    let source : Cursor := ⟨context, values, formation, resourceFormation, resourceExact⟩
    let firstHead := perform source instruction
    let secondHead := perform target (instruction.rename raccord.reading.references.forward)
    let heads := raccord.afterProduction firstHead secondHead
    let suffix := continueFrom tail firstHead.successor.values firstHead.successor.formation
      firstHead.successor.resourceFormation firstHead.successor.resourceExact secondHead.successor heads
    ⟨prefixProduction firstHead suffix.first, prefixProduction secondHead suffix.second, suffix.raccord⟩
termination_by structural schedule

def continueCorresponding {source target} (raccord : ConstitutedRaccord source target)
    (schedule : Program source.kinds) : ContinuedPair source target :=
  continueFrom schedule source.values source.formation source.resourceFormation source.resourceExact target raccord

theorem continueFrom_source_exact {context} (schedule : Program context)
    (values : Values Value context) (formation : Formed (context := context) values)
    (resourceFormation : Formation Value (context := context) values)
    (resourceExact : ResourceInterpretation formation resourceFormation) (target : Cursor)
    (raccord : ConstitutedRaccord ⟨context, values, formation, resourceFormation, resourceExact⟩ target) :
    (continueFrom schedule values formation resourceFormation resourceExact target raccord).first =
      runFrom schedule values formation resourceFormation resourceExact := by
  induction schedule generalizing target with
  | done => rfl
  | step instruction tail ih =>
    let source : Cursor := ⟨_, values, formation, resourceFormation, resourceExact⟩
    let firstHead := perform source instruction
    let secondHead := perform target (instruction.rename raccord.reading.references.forward)
    exact congrArg (prefixProduction firstHead)
      (ih firstHead.successor.values firstHead.successor.formation firstHead.successor.resourceFormation
        firstHead.successor.resourceExact secondHead.successor (raccord.afterProduction firstHead secondHead))

theorem continueCorresponding_source_exact {source target} (raccord : ConstitutedRaccord source target)
    (schedule : Program source.kinds) :
    (continueCorresponding raccord schedule).first = run source schedule :=
  continueFrom_source_exact schedule source.values source.formation source.resourceFormation source.resourceExact
    target raccord

theorem continueFrom_target_exact {context} (schedule : Program context)
    (values : Values Value context) (formation : Formed (context := context) values)
    (resourceFormation : Formation Value (context := context) values)
    (resourceExact : ResourceInterpretation formation resourceFormation) (target : Cursor)
    (raccord : ConstitutedRaccord ⟨context, values, formation, resourceFormation, resourceExact⟩ target) :
    (continueFrom schedule values formation resourceFormation resourceExact target raccord).second =
      run target (schedule.rename raccord.reading.references) := by
  induction schedule generalizing target with
  | done => rfl
  | step instruction tail ih =>
    let source : Cursor := ⟨_, values, formation, resourceFormation, resourceExact⟩
    let firstHead := perform source instruction
    let secondHead := perform target (instruction.rename raccord.reading.references.forward)
    exact congrArg (prefixProduction secondHead)
      (ih firstHead.successor.values firstHead.successor.formation firstHead.successor.resourceFormation
        firstHead.successor.resourceExact secondHead.successor (raccord.afterProduction firstHead secondHead))

theorem continueCorresponding_target_exact {source target} (raccord : ConstitutedRaccord source target)
    (schedule : Program source.kinds) :
    (continueCorresponding raccord schedule).second = run target (schedule.rename raccord.reading.references) :=
  continueFrom_target_exact schedule source.values source.formation source.resourceFormation source.resourceExact
    target raccord

theorem continueCorresponding_source_history_exact {source target}
    (raccord : ConstitutedRaccord source target) (schedule : Program source.kinds) :
    HEq (continueCorresponding raccord schedule).first.history (run source schedule).history := by
  rw [continueCorresponding_source_exact]

theorem independentPair_occurrences_distinct {source firstKind secondKind}
    {first : Instruction source.kinds firstKind} {second : Instruction source.kinds secondKind}
    (produced : IndependentPairProduction source first second) :
    (⟨firstKind, .prior .here⟩ : Occurrence produced.cursor.kinds) ≠
      ⟨secondKind, .here⟩ := by
  intro same
  have positions := congrArg (fun occurrence => occurrence.2.position) same
  change (1 : Nat) = 0 at positions
  cases positions

/-- Full local readout, including a signal's recorded increments, at the
corresponding occurrence. This is not raw same-address future equivalence. -/
theorem transported_inspection_exact {source target} (raccord : ReadRaccord source target)
    {kind} (ref : Ref source.kinds kind) :
    referenceEvent target (.inspect kind (raccord.references.forward ref).position) =
      referenceEvent source (.inspect kind ref.position) := by
  rw [inspection_reference_exact, inspection_reference_exact, raccord.reads]

theorem transported_inspection_admitted {source target} (raccord : ReadRaccord source target)
    {kind} (ref : Ref source.kinds kind) :
    admissionEnabled target (.inspect kind (raccord.references.forward ref).position) = true :=
  inspection_reference_enabled target _

end RelationalPerimeter.Relativity.Production
/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Relativity.Production.InputPort.returned
#print axioms RelationalPerimeter.Relativity.Production.ConstitutedRaccord
#print axioms RelationalPerimeter.Relativity.Production.independentPairConstitution
#print axioms RelationalPerimeter.Relativity.Production.ConstitutedRaccord.reverse
#print axioms RelationalPerimeter.Relativity.Production.ConstitutedRaccord.used_iff
#print axioms RelationalPerimeter.Relativity.Production.ConstitutedRaccord.forwardPath
#print axioms RelationalPerimeter.Relativity.Production.paired_outputs_exact
#print axioms RelationalPerimeter.Relativity.Production.ConstitutedRaccord.afterProduction
#print axioms RelationalPerimeter.Relativity.Production.ContinuedPair
#print axioms RelationalPerimeter.Relativity.Production.Program.rename
#print axioms RelationalPerimeter.Relativity.Production.Program.rename_returns
#print axioms RelationalPerimeter.Relativity.Production.prefixProduction
#print axioms RelationalPerimeter.Relativity.Production.continueFrom
#print axioms RelationalPerimeter.Relativity.Production.continueCorresponding
#print axioms RelationalPerimeter.Relativity.Production.continueFrom_source_exact
#print axioms RelationalPerimeter.Relativity.Production.continueCorresponding_source_exact
#print axioms RelationalPerimeter.Relativity.Production.continueFrom_target_exact
#print axioms RelationalPerimeter.Relativity.Production.continueCorresponding_target_exact
#print axioms RelationalPerimeter.Relativity.Production.continueCorresponding_source_history_exact
#print axioms RelationalPerimeter.Relativity.Production.independentPair_occurrences_distinct
#print axioms RelationalPerimeter.Relativity.Production.transported_inspection_exact
#print axioms RelationalPerimeter.Relativity.Production.transported_inspection_admitted
/- AXIOM_AUDIT_END -/
