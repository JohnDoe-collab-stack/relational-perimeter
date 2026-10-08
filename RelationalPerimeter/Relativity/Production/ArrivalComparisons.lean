import RelationalPerimeter.Relativity.Production.ArrivalContexts

/-!
# A declared two-arrival comparison and its actual continuations

The new instrumental law subtracts the first received reading from the
second. Both ports must be actual, distinct reception occurrences. The
positive arrival witnesses are consumed in computing the result, and the
generic resource formation interprets exactly that result and those ports.
This extends the closed signal law locally; it does not silently extend its
previous request contract or assert spacetime colocation.

After comparison, the existing emit/relay/receive instructions operate on
the produced support. The continuation has its own closed formation witness
because `Formed` deliberately denotes the earlier signal-only law. Both
interpret the same foundational `Formation`, references and founded history.
No new received root, arbitrary producer or prescribed target is introduced.
-/
set_option genInjectivity false
namespace RelationalPerimeter.Relativity.Production
open ConstitutiveSearch.Resources

structure ArrivalPair (source : Cursor) where
  first : Ref source.kinds .reading
  second : Ref source.kinds .reading
  firstSignal : Ref source.kinds .signal
  secondSignal : Ref source.kinds .signal
  firstArrival : Arrived source.formation first firstSignal
  secondArrival : Arrived source.formation second secondSignal
  distinct : first ≠ second

def ArrivalPair.gap {source : Cursor} (pair : ArrivalPair source) : Rational :=
  Rational.sub pair.secondArrival.measure pair.firstArrival.measure

structure ComparisonAdmission (source : Cursor) (firstAddress secondAddress : Nat) where
  first : ArrivalAt source firstAddress
  second : ArrivalAt source secondAddress
  distinct : first.reading.ref ≠ second.reading.ref

def ComparisonAdmission.pair {source : Cursor} {firstAddress secondAddress : Nat}
    (admitted : ComparisonAdmission source firstAddress secondAddress) : ArrivalPair source :=
  ⟨admitted.first.reading.ref, admitted.second.reading.ref,
    admitted.first.signal, admitted.second.signal, admitted.first.arrival,
    admitted.second.arrival, admitted.distinct⟩

def decideComparison (source : Cursor) (firstAddress secondAddress : Nat) :
    PSum (ComparisonAdmission source firstAddress secondAddress)
      (ComparisonAdmission source firstAddress secondAddress → False) :=
  match pairDecision (resolveArrivalAt source firstAddress) (resolveArrivalAt source secondAddress) with
  | .inr impossible => .inr (fun admitted => impossible (admitted.first, admitted.second))
  | .inl arrivals =>
    match Nat.decEq firstAddress secondAddress with
    | .isTrue same => .inr (fun admitted => admitted.distinct
        (reference_position_injective _ _
          (admitted.first.reading.exactPosition.trans (same.trans admitted.second.reading.exactPosition.symm))))
    | .isFalse distinct => .inl ⟨arrivals.1, arrivals.2, fun same => distinct
        (arrivals.1.reading.exactPosition.symm.trans
          ((congrArg Ref.position same).trans arrivals.2.reading.exactPosition))⟩

def comparisonEnabled (source : Cursor) (firstAddress secondAddress : Nat) : Bool :=
  match decideComparison source firstAddress secondAddress with | .inl _ => true | .inr _ => false

def ArrivalPair.lower {source : Cursor} (pair : ArrivalPair source) : Producer Value source.kinds where
  inputKinds := [.reading, .reading]
  inputs := .cons pair.first (.cons pair.second .nil)
  outputKind := fun _ => .reading
  operation := fun arguments => Rational.sub arguments.2.1 arguments.1

theorem ArrivalPair.gap_exact {source : Cursor} (pair : ArrivalPair source) :
    pair.gap = Rational.sub (source.read pair.second) (source.read pair.first) :=
  (congrArg (fun second => Rational.sub second pair.firstArrival.measure) pair.secondArrival.measure_exact).trans
    (congrArg (Rational.sub (source.read pair.second)) pair.firstArrival.measure_exact)

theorem ArrivalPair.lower_exact {source : Cursor} (pair : ArrivalPair source) :
    pair.gap = pair.lower.operation (pair.lower.arguments source.values) := pair.gap_exact

/-- A positive instrumental role, indexed by both actually arrived sources.
It is not an equality of those source occurrences. -/
inductive ComparisonProduces {source : Cursor} (pair : ArrivalPair source) : Rational → Type where
  | compared : ComparisonProduces pair pair.gap

abbrev ComparisonDetermination {source : Cursor} (pair : ArrivalPair source) :=
  (output : Rational) ×' ComparisonProduces pair output

def compareArrivals {source : Cursor} (pair : ArrivalPair source) : ComparisonDetermination pair :=
  ⟨pair.gap, .compared⟩

theorem ComparisonProduces.output_exact {source : Cursor} {pair : ArrivalPair source} {output : Rational}
    (role : ComparisonProduces pair output) : output = pair.gap := by cases role; rfl

def ComparisonProduces.resourceFormation {source : Cursor} {pair : ArrivalPair source} {output : Rational}
    (role : ComparisonProduces pair output) :
    Formation Value (context := .reading :: source.kinds) (output, source.values) := by
  cases role
  have formed := Formation.produced source.resourceFormation pair.lower
  exact (congrArg (fun value => (value, source.values)) pair.lower_exact).symm ▸ formed

inductive ComparisonPort {source : Cursor} (pair : ArrivalPair source) : Ref source.kinds .reading → Type where
  | first : ComparisonPort pair pair.first
  | second : ComparisonPort pair pair.second

/-- Closed extension of the same constituted support. The comparison root
retains the actual signal-law cursor and the same positive instrumental role.
Subsequent productions consume this support; no history is replayed. -/
inductive InstrumentFormation : {context : List Kind} → Values Value context → Type where
  | compared {source : Cursor} (pair : ArrivalPair source) {output : Rational}
      (role : ComparisonProduces pair output) :
      InstrumentFormation (context := .reading :: source.kinds) (output, source.values)
  | produced {context} {values : Values Value context}
      (past : InstrumentFormation (context := context) values)
      {kind} {instruction : Instruction context kind} {output : Value kind}
      (role : Produces values instruction output) :
      InstrumentFormation (context := kind :: context) (output, values)

inductive InstrumentInterpretation : {context : List Kind} → {values : Values Value context} →
    InstrumentFormation (context := context) values → Formation Value (context := context) values → Prop where
  | compared {source : Cursor} (pair : ArrivalPair source) {output : Rational}
      (role : ComparisonProduces pair output) :
      InstrumentInterpretation (.compared pair role) role.resourceFormation
  | produced {context} {values : Values Value context}
      {past : InstrumentFormation (context := context) values}
      {resource : Formation Value (context := context) values}
      (exactPast : InstrumentInterpretation past resource)
      {kind} {instruction : Instruction context kind} {output : Value kind}
      (role : Produces values instruction output) :
      InstrumentInterpretation (.produced past role) (role.resourceFormation resource)

structure InstrumentCursor where
  kinds : List Kind
  values : Values Value kinds
  formation : InstrumentFormation (context := kinds) values
  resourceFormation : Formation Value (context := kinds) values
  resourceExact : InstrumentInterpretation formation resourceFormation

def InstrumentCursor.support (source : InstrumentCursor) : Support Value source.kinds :=
  ⟨source.values, source.resourceFormation⟩

def InstrumentCursor.read (source : InstrumentCursor) {kind} (ref : Ref source.kinds kind) : Value kind :=
  ConstitutiveSearch.Resources.read source.values ref

def instrumentOfComparison {source : Cursor} {pair : ArrivalPair source}
    (determination : ComparisonDetermination pair) : InstrumentCursor :=
  ⟨.reading :: source.kinds, (determination.1, source.values),
    .compared pair determination.2, determination.2.resourceFormation, .compared pair determination.2⟩

structure ComparisonProduction {source : Cursor} (pair : ArrivalPair source) where
  determination : ComparisonDetermination pair
  successor : InstrumentCursor
  successorExact : successor = instrumentOfComparison determination

def performComparison {source : Cursor} (pair : ArrivalPair source) : ComparisonProduction pair :=
  let determination := compareArrivals pair
  let successor := instrumentOfComparison determination
  ⟨determination, successor, rfl⟩

inductive ComparisonOutcome (source : Cursor) (firstAddress secondAddress : Nat) where
  | performed (admission : ComparisonAdmission source firstAddress secondAddress)
      (production : ComparisonProduction admission.pair)
  | refused (refutation : ComparisonAdmission source firstAddress secondAddress → False)

def requestComparison (source : Cursor) (firstAddress secondAddress : Nat) :
    ComparisonOutcome source firstAddress secondAddress :=
  match decideComparison source firstAddress secondAddress with
  | .inl admitted => .performed admitted (performComparison admitted.pair)
  | .inr impossible => .refused impossible

theorem same_arrival_refused (source : Cursor) (address : Nat) :
    comparisonEnabled source address address = false := by
  cases selected : decideComparison source address address with
  | inl admitted =>
    exact False.elim (admitted.distinct (reference_position_injective _ _
      (admitted.first.reading.exactPosition.trans admitted.second.reading.exactPosition.symm)))
  | inr impossible => unfold comparisonEnabled; rw [selected]

theorem comparison_refuses_given_root (input : Received) (one two : Nat) :
    comparisonEnabled (.received input) one two = false := by
  cases selected : decideComparison (.received input) one two with
  | inl admitted => exact False.elim (given_reading_not_arrived input admitted.first.arrival)
  | inr impossible => unfold comparisonEnabled; rw [selected]

def comparisonTransport {source : Cursor} {pair : ArrivalPair source}
    (production : ComparisonProduction pair) : Support.Extension source.support production.successor.support := by
  cases production with
  | mk determination successor exactSuccessor =>
    cases exactSuccessor
    exact ⟨Ref.prior, fun _ => rfl, prior_injective, 1, fun _ => rfl⟩

theorem comparison_output_exact {source : Cursor} (pair : ArrivalPair source) :
    (performComparison pair).successor.read .here =
      Rational.sub (source.read pair.second) (source.read pair.first) := pair.gap_exact

theorem comparison_preserves_source_distinction {source : Cursor} (pair : ArrivalPair source) :
    (comparisonTransport (performComparison pair)).references pair.first ≠
      (comparisonTransport (performComparison pair)).references pair.second :=
  fun same => pair.distinct ((comparisonTransport (performComparison pair)).injective _ _ same)

theorem comparison_is_fresh {source : Cursor} (pair : ArrivalPair source)
    (old : Ref source.kinds .reading) :
    (Ref.here : Ref (performComparison pair).successor.kinds .reading) ≠
      (comparisonTransport (performComparison pair)).references old := by
  intro same
  exact fresh_position_distinct old (congrArg Ref.position same)

theorem comparison_equal_readings_not_equal_sources {source : Cursor} (pair : ArrivalPair source)
    (same : source.read pair.first = source.read pair.second) :
    (performComparison pair).determination.1 = Rational.zero ∧ pair.first ≠ pair.second := by
  constructor
  · exact pair.gap_exact.trans ((congrArg (Rational.sub (source.read pair.second)) same).trans
      (Rational.sub_self _))
  · exact pair.distinct

abbrev InstrumentDetermination (source : InstrumentCursor) {kind} (instruction : Instruction source.kinds kind) :=
  (output : Value kind) ×' Produces source.values instruction output

def InstrumentCursor.extend (source : InstrumentCursor) {kind} {instruction : Instruction source.kinds kind}
    (determination : InstrumentDetermination source instruction) : InstrumentCursor :=
  ⟨kind :: source.kinds, (determination.1, source.values), .produced source.formation determination.2,
    determination.2.resourceFormation source.resourceFormation, .produced source.resourceExact determination.2⟩

inductive InstrumentUsed : {context : List Kind} → {values : Values Value context} →
    InstrumentFormation (context := context) values → Occurrence context → Occurrence context → Type where
  | compared {source : Cursor} {pair : ArrivalPair source} {output : Rational}
      (role : ComparisonProduces pair output) (reading : Ref source.kinds .reading)
      (port : ComparisonPort pair reading) :
      InstrumentUsed (.compared pair role) (oldOccurrence .reading ⟨.reading, reading⟩)
        (freshOccurrence source.kinds .reading)
  | priorHistory {source : Cursor} {pair : ArrivalPair source} {output : Rational}
      (role : ComparisonProduces pair output) {one two : Occurrence source.kinds}
      (edge : Used source.formation one two) :
      InstrumentUsed (.compared pair role) (oldOccurrence .reading one) (oldOccurrence .reading two)
  | produced {context} {values : Values Value context}
      (past : InstrumentFormation (context := context) values)
      {outputKind inputKind} {instruction : Instruction context outputKind} {output : Value outputKind}
      (role : Produces values instruction output) (ref : Ref context inputKind) (port : InputPort instruction ref) :
      InstrumentUsed (.produced past role) (oldOccurrence outputKind ⟨inputKind, ref⟩)
        (freshOccurrence context outputKind)
  | inherited {context} {values : Values Value context}
      {past : InstrumentFormation (context := context) values}
      {outputKind} {instruction : Instruction context outputKind} {output : Value outputKind}
      (role : Produces values instruction output) {one two : Occurrence context}
      (edge : InstrumentUsed past one two) :
      InstrumentUsed (.produced past role) (oldOccurrence outputKind one) (oldOccurrence outputKind two)

theorem InstrumentUsed.position_decreases {context} {values : Values Value context}
    {formation : InstrumentFormation (context := context) values} {one two : Occurrence context}
    (edge : InstrumentUsed formation one two) : two.2.position < one.2.position := by
  induction edge with
  | compared role reading port => exact Nat.zero_lt_succ _
  | priorHistory role edge => exact Nat.add_lt_add_right edge.position_decreases 1
  | produced past role ref port => exact Nat.zero_lt_succ _
  | inherited role edge ih => exact Nat.add_lt_add_right ih 1

theorem InstrumentUsed.no_cycle {context} {values : Values Value context}
    {formation : InstrumentFormation (context := context) values} {one : Occurrence context}
    (edge : InstrumentUsed formation one one) : False := Nat.lt_irrefl _ edge.position_decreases

def comparison_first_used {source : Cursor} (pair : ArrivalPair source) :
    InstrumentUsed (performComparison pair).successor.formation
      (oldOccurrence .reading ⟨.reading, pair.first⟩) (freshOccurrence source.kinds .reading) :=
  .compared .compared pair.first .first

def comparison_second_used {source : Cursor} (pair : ArrivalPair source) :
    InstrumentUsed (performComparison pair).successor.formation
      (oldOccurrence .reading ⟨.reading, pair.second⟩) (freshOccurrence source.kinds .reading) :=
  .compared .compared pair.second .second

def comparison_first_reception_kept {source : Cursor} (pair : ArrivalPair source) :
    InstrumentUsed (performComparison pair).successor.formation
      (oldOccurrence .reading ⟨.signal, pair.firstSignal⟩)
      (oldOccurrence .reading ⟨.reading, pair.first⟩) :=
  .priorHistory .compared pair.firstArrival.usedEdge

structure InstrumentProduction (source : InstrumentCursor) {kind} (instruction : Instruction source.kinds kind) where
  determination : InstrumentDetermination source instruction
  successor : InstrumentCursor
  successorExact : successor = source.extend determination

def performInstrument (source : InstrumentCursor) {kind} (instruction : Instruction source.kinds kind) :
    InstrumentProduction source instruction :=
  let determination := execute source.values instruction
  let successor := source.extend determination
  ⟨determination, successor, rfl⟩

structure InstrumentStep (source target : InstrumentCursor) where
  kind : Kind
  instruction : Instruction source.kinds kind
  determination : InstrumentDetermination source instruction
  targetExact : target = source.extend determination

abbrev InstrumentHistory := StrongPerimetralTurning.History InstrumentStep

def InstrumentStep.transport {source target : InstrumentCursor} (step : InstrumentStep source target) :
    Support.Extension source.support target.support := by
  cases step with
  | mk kind instruction determination exactTarget =>
    cases exactTarget
    exact ⟨Ref.prior, fun _ => rfl, prior_injective, 1, fun _ => rfl⟩

def instrumentHistoryTransport {source target : InstrumentCursor} (history : InstrumentHistory source target) :
    Support.Extension source.support target.support :=
  match history with
  | .root => .identity _
  | .extend past step => (instrumentHistoryTransport past).compose step.transport
termination_by structural history

def InstrumentStep.transportUsed {source target : InstrumentCursor} (step : InstrumentStep source target)
    {one two : Occurrence source.kinds} (edge : InstrumentUsed source.formation one two) :
    InstrumentUsed target.formation ⟨one.1, step.transport.references one.2⟩
      ⟨two.1, step.transport.references two.2⟩ := by
  cases step with
  | mk kind instruction determination exactTarget => cases exactTarget; exact .inherited determination.2 edge

def instrumentHistoryTransportUsed {source target : InstrumentCursor}
    (history : InstrumentHistory source target) {one two : Occurrence source.kinds}
    (edge : InstrumentUsed source.formation one two) :
    InstrumentUsed target.formation ⟨one.1, (instrumentHistoryTransport history).references one.2⟩
      ⟨two.1, (instrumentHistoryTransport history).references two.2⟩ :=
  match history with
  | .root => edge
  | .extend past step => step.transportUsed (instrumentHistoryTransportUsed past edge)
termination_by structural history

structure InstrumentExecution (source : InstrumentCursor) where
  cursor : InstrumentCursor
  history : InstrumentHistory source cursor

def runInstrumentFrom {context} (schedule : Program context)
    (values : Values Value context) (formation : InstrumentFormation (context := context) values)
    (resourceFormation : Formation Value (context := context) values)
    (resourceExact : InstrumentInterpretation formation resourceFormation) :
    InstrumentExecution ⟨context, values, formation, resourceFormation, resourceExact⟩ :=
  match schedule with
  | .done => ⟨⟨context, values, formation, resourceFormation, resourceExact⟩, .root⟩
  | .step instruction tail =>
    let source : InstrumentCursor := ⟨context, values, formation, resourceFormation, resourceExact⟩
    let head := performInstrument source instruction
    let resumed := runInstrumentFrom tail head.successor.values head.successor.formation
      head.successor.resourceFormation head.successor.resourceExact
    ⟨resumed.cursor, StrongPerimetralTurning.History.append
      (.extend .root ⟨_, instruction, head.determination, head.successorExact⟩ : InstrumentHistory source head.successor)
      resumed.history⟩
termination_by structural schedule

def runInstrument (source : InstrumentCursor) (schedule : Program source.kinds) : InstrumentExecution source :=
  runInstrumentFrom schedule source.values source.formation source.resourceFormation source.resourceExact

structure ComparisonExecution {source : Cursor} (pair : ArrivalPair source) where
  head : ComparisonProduction pair
  continuation : InstrumentExecution head.successor

/-- Form the interaction first, then give its actual successor to the suffix.
Only its new resource sorts, not future values or a completed future, index
the received schedule. The cached head is shared with the returned record. -/
def runCompared {source : Cursor} (pair : ArrivalPair source)
    (schedule : Program (.reading :: source.kinds)) : ComparisonExecution pair :=
  let head := performComparison pair
  let resumed := runInstrument head.successor schedule
  ⟨head, resumed⟩

theorem compared_head_independent {source : Cursor} (pair : ArrivalPair source)
    (one two : Program (.reading :: source.kinds)) :
    (runCompared pair one).head = (runCompared pair two).head := rfl

theorem compared_continuation_exact {source : Cursor} (pair : ArrivalPair source)
    (schedule : Program (.reading :: source.kinds)) :
    (runCompared pair schedule).continuation = runInstrument (performComparison pair).successor schedule := rfl

def ComparisonExecution.transport {source : Cursor} {pair : ArrivalPair source}
    (execution : ComparisonExecution pair) :
    Support.Extension source.support execution.continuation.cursor.support :=
  (comparisonTransport execution.head).compose (instrumentHistoryTransport execution.continuation.history)

theorem runInstrumentFrom_length {context} (schedule : Program context)
    (values : Values Value context) (formation : InstrumentFormation (context := context) values)
    (resourceFormation : Formation Value (context := context) values)
    (resourceExact : InstrumentInterpretation formation resourceFormation) :
    StrongPerimetralTurning.History.length
      (runInstrumentFrom schedule values formation resourceFormation resourceExact).history = schedule.steps := by
  induction schedule with
  | done => rfl
  | step instruction tail ih =>
    change StrongPerimetralTurning.History.length (StrongPerimetralTurning.History.append _ _) = _
    dsimp only [performInstrument, InstrumentCursor.extend]
    exact (StrongPerimetralTurning.History.length_append _ _).trans
      ((congrArg (fun n => 1 + n) (ih _ _ _ _)).trans (Nat.add_comm 1 tail.steps))

theorem runInstrument_length (source : InstrumentCursor) (schedule : Program source.kinds) :
    StrongPerimetralTurning.History.length (runInstrument source schedule).history = schedule.steps :=
  runInstrumentFrom_length schedule source.values source.formation source.resourceFormation source.resourceExact

/-- The source prefix is retained by the comparison; the continuation is
strictly downstream. Its full support extension preserves every old reading
and distinct reference, not just the comparison's numerical output. -/
def continuedComparisonTransport {source : Cursor} {pair : ArrivalPair source}
    (production : ComparisonProduction pair) (continuation : Program production.successor.kinds) :
    Support.Extension source.support (runInstrument production.successor continuation).cursor.support :=
  (comparisonTransport production).compose (instrumentHistoryTransport (runInstrument production.successor continuation).history)

/-- A concrete consumer: the comparison's fresh reading is the reading port
of a new emission. The producer receives the shared comparison, not its inputs
to recompute it. -/
def emitComparison {source : Cursor} {pair : ArrivalPair source}
    (production : ComparisonProduction pair) (payload : Ref source.kinds .payload) :
    InstrumentProduction production.successor
      (.emit (production.successorExact.symm ▸ Ref.here)
        (production.successorExact.symm ▸ Ref.prior payload)) :=
  performInstrument production.successor _

theorem emitted_comparison_reading {source : Cursor} {pair : ArrivalPair source}
    (production : ComparisonProduction pair) (payload : Ref source.kinds .payload) :
    (emitComparison production payload).determination.1.reading = production.determination.1 := by
  cases production with
  | mk determination successor exactSuccessor =>
    cases exactSuccessor
    rfl

theorem emitted_comparison_payload {source : Cursor} {pair : ArrivalPair source}
    (production : ComparisonProduction pair) (payload : Ref source.kinds .payload) :
    (emitComparison production payload).determination.1.payload = source.read payload := by
  cases production with
  | mk determination successor exactSuccessor => cases exactSuccessor; rfl

end RelationalPerimeter.Relativity.Production
/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Relativity.Production.ArrivalPair
#print axioms RelationalPerimeter.Relativity.Production.ArrivalPair.gap
#print axioms RelationalPerimeter.Relativity.Production.ComparisonAdmission.pair
#print axioms RelationalPerimeter.Relativity.Production.decideComparison
#print axioms RelationalPerimeter.Relativity.Production.comparisonEnabled
#print axioms RelationalPerimeter.Relativity.Production.ArrivalPair.lower
#print axioms RelationalPerimeter.Relativity.Production.ArrivalPair.gap_exact
#print axioms RelationalPerimeter.Relativity.Production.ArrivalPair.lower_exact
#print axioms RelationalPerimeter.Relativity.Production.ComparisonProduces
#print axioms RelationalPerimeter.Relativity.Production.compareArrivals
#print axioms RelationalPerimeter.Relativity.Production.ComparisonProduces.output_exact
#print axioms RelationalPerimeter.Relativity.Production.ComparisonProduces.resourceFormation
#print axioms RelationalPerimeter.Relativity.Production.ComparisonPort
#print axioms RelationalPerimeter.Relativity.Production.InstrumentFormation
#print axioms RelationalPerimeter.Relativity.Production.InstrumentInterpretation
#print axioms RelationalPerimeter.Relativity.Production.instrumentOfComparison
#print axioms RelationalPerimeter.Relativity.Production.performComparison
#print axioms RelationalPerimeter.Relativity.Production.requestComparison
#print axioms RelationalPerimeter.Relativity.Production.same_arrival_refused
#print axioms RelationalPerimeter.Relativity.Production.comparison_refuses_given_root
#print axioms RelationalPerimeter.Relativity.Production.comparisonTransport
#print axioms RelationalPerimeter.Relativity.Production.comparison_output_exact
#print axioms RelationalPerimeter.Relativity.Production.comparison_preserves_source_distinction
#print axioms RelationalPerimeter.Relativity.Production.comparison_is_fresh
#print axioms RelationalPerimeter.Relativity.Production.comparison_equal_readings_not_equal_sources
#print axioms RelationalPerimeter.Relativity.Production.InstrumentCursor.extend
#print axioms RelationalPerimeter.Relativity.Production.InstrumentUsed
#print axioms RelationalPerimeter.Relativity.Production.InstrumentUsed.position_decreases
#print axioms RelationalPerimeter.Relativity.Production.InstrumentUsed.no_cycle
#print axioms RelationalPerimeter.Relativity.Production.comparison_first_used
#print axioms RelationalPerimeter.Relativity.Production.comparison_second_used
#print axioms RelationalPerimeter.Relativity.Production.comparison_first_reception_kept
#print axioms RelationalPerimeter.Relativity.Production.performInstrument
#print axioms RelationalPerimeter.Relativity.Production.InstrumentStep.transport
#print axioms RelationalPerimeter.Relativity.Production.instrumentHistoryTransport
#print axioms RelationalPerimeter.Relativity.Production.InstrumentStep.transportUsed
#print axioms RelationalPerimeter.Relativity.Production.instrumentHistoryTransportUsed
#print axioms RelationalPerimeter.Relativity.Production.runInstrumentFrom
#print axioms RelationalPerimeter.Relativity.Production.runInstrument
#print axioms RelationalPerimeter.Relativity.Production.runCompared
#print axioms RelationalPerimeter.Relativity.Production.compared_head_independent
#print axioms RelationalPerimeter.Relativity.Production.compared_continuation_exact
#print axioms RelationalPerimeter.Relativity.Production.ComparisonExecution.transport
#print axioms RelationalPerimeter.Relativity.Production.runInstrument_length
#print axioms RelationalPerimeter.Relativity.Production.continuedComparisonTransport
#print axioms RelationalPerimeter.Relativity.Production.emitComparison
#print axioms RelationalPerimeter.Relativity.Production.emitted_comparison_reading
#print axioms RelationalPerimeter.Relativity.Production.emitted_comparison_payload
/- AXIOM_AUDIT_END -/
