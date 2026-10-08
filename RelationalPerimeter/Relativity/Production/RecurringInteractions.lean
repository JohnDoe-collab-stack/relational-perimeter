import RelationalPerimeter.Relativity.Production.ArrivalComparisons

/-!
# Repeated interactions on the same constituted support

The comparison law may be used again after any finite number of productions.
Its ports are positive reception occurrences in the current history, never
readings accepted merely because their values happen to agree. Existing
signal and instrumental cursors enter with their actual formations and cached
resource interpretations. No new given root or replay of an action is used.

This is a closed instrumental extension, not a physical meeting law or a
relativistic geometry. It preserves the distinction between reception,
comparison and occurrence identity.
-/
set_option genInjectivity false
set_option genSizeOf false
namespace RelationalPerimeter.Relativity.Production
open ConstitutiveSearch.Resources

inductive InstrumentArrived : {context : List Kind} → {values : Values Value context} →
    InstrumentFormation (context := context) values → Ref context .reading → Ref context .signal → Type where
  | priorComparison {source : Cursor} {pair : ArrivalPair source} {output : Rational}
      (role : ComparisonProduces pair output) {reading : Ref source.kinds .reading}
      {signal : Ref source.kinds .signal} (arrival : Arrived source.formation reading signal) :
      InstrumentArrived (.compared pair role) (.prior reading) (.prior signal)
  | received {context} {values : Values Value context}
      (past : InstrumentFormation (context := context) values) (signal : Ref context .signal) :
      InstrumentArrived (.produced past (.received signal)) .here (.prior signal)
  | inherited {context} {values : Values Value context} {past : InstrumentFormation (context := context) values}
      {kind} {instruction : Instruction context kind} {output : Value kind}
      (role : Produces values instruction output) {reading : Ref context .reading} {signal : Ref context .signal}
      (arrival : InstrumentArrived past reading signal) :
      InstrumentArrived (.produced past role) (.prior reading) (.prior signal)

def InstrumentArrived.measure {context} {values : Values Value context}
    {past : InstrumentFormation (context := context) values}
    {reading : Ref context .reading} {signal : Ref context .signal}
    (arrival : InstrumentArrived past reading signal) : Rational := by
  cases arrival with
  | priorComparison _ old => exact old.measure
  | @received context values _ signal => exact (read values signal).reading
  | inherited _ old => exact old.measure
termination_by structural arrival

theorem InstrumentArrived.measure_exact {context} {values : Values Value context}
    {past : InstrumentFormation (context := context) values}
    {reading : Ref context .reading} {signal : Ref context .signal}
    (arrival : InstrumentArrived past reading signal) : arrival.measure = read values reading := by
  induction arrival with
  | priorComparison role old => exact old.measure_exact
  | received past signal => rfl
  | inherited role old ih => exact ih

def findInstrumentArrival {context} {values : Values Value context}
    (past : InstrumentFormation (context := context) values) (reading : Ref context .reading) :
    Option ((signal : Ref context .signal) ×' InstrumentArrived past reading signal) := by
  cases past with
  | compared pair role =>
    cases reading with
    | here => exact none
    | prior old => exact (findArrival _ old).map (fun found =>
        ⟨.prior found.1, .priorComparison role found.2⟩)
  | produced old role =>
    cases reading with
    | here => cases role with | received signal => exact some ⟨.prior signal, .received old signal⟩
    | prior ref => exact (findInstrumentArrival old ref).map (fun found =>
        ⟨.prior found.1, .inherited role found.2⟩)
termination_by structural past

theorem InstrumentArrived.find_present {context} {values : Values Value context}
    {past : InstrumentFormation (context := context) values}
    {reading : Ref context .reading} {signal : Ref context .signal}
    (arrival : InstrumentArrived past reading signal) :
    ∃ found, findInstrumentArrival past reading = some found := by
  induction arrival with
  | priorComparison role old =>
    obtain ⟨found, exactFound⟩ := old.find_present
    refine ⟨⟨.prior found.1, .priorComparison role found.2⟩, ?_⟩
    change (findArrival _ _).map _ = _
    rw [exactFound]; rfl
  | received past signal => exact ⟨⟨.prior signal, .received past signal⟩, rfl⟩
  | inherited role old ih =>
    obtain ⟨found, exactFound⟩ := ih
    refine ⟨⟨.prior found.1, .inherited role found.2⟩, ?_⟩
    change (findInstrumentArrival _ _).map _ = _
    rw [exactFound]; rfl

/-- The exact production history. A cursor additionally requires the positive
`RecurringConstitution` below: the history alone does not authorize comparison. -/
def recurringDifference {context} (values : Values Value context) (first second : Ref context .reading) : Rational :=
  Rational.sub (read values second) (read values first)

inductive RecurringComputed {context} (values : Values Value context) (first second : Ref context .reading) :
    Rational → Type where
  | computed : RecurringComputed values first second (recurringDifference values first second)

inductive RecurringFormation : {context : List Kind} → Values Value context → Type where
  | fromCursor (source : Cursor) : RecurringFormation source.values
  | fromInstrument (source : InstrumentCursor) : RecurringFormation source.values
  | signal {context} {values : Values Value context} (past : RecurringFormation values)
      {kind} {instruction : Instruction context kind} {output : Value kind}
      (role : Produces values instruction output) : RecurringFormation (context := kind :: context) (output, values)
  | comparison {context} {values : Values Value context} (past : RecurringFormation values)
      (first second : Ref context .reading) {output : Rational}
      (role : RecurringComputed values first second output) :
      RecurringFormation (context := .reading :: context) (output, values)

inductive RecurringArrival : {context : List Kind} → {values : Values Value context} →
    RecurringFormation (context := context) values → Ref context .reading → Ref context .signal → Type where
  | fromCursor {source : Cursor} {reading : Ref source.kinds .reading} {signal : Ref source.kinds .signal}
      (arrival : Arrived source.formation reading signal) : RecurringArrival (.fromCursor source) reading signal
  | fromInstrument {source : InstrumentCursor} {reading : Ref source.kinds .reading}
      {signal : Ref source.kinds .signal} (arrival : InstrumentArrived source.formation reading signal) :
      RecurringArrival (.fromInstrument source) reading signal
  | received {context} {values : Values Value context} (past : RecurringFormation values)
      (signal : Ref context .signal) : RecurringArrival (.signal past (.received signal)) .here (.prior signal)
  | throughSignal {context} {values : Values Value context} {past : RecurringFormation values}
      {kind} {instruction : Instruction context kind} {output : Value kind}
      (role : Produces values instruction output) {reading : Ref context .reading} {signal : Ref context .signal}
      (arrival : RecurringArrival past reading signal) :
      RecurringArrival (.signal past role) (.prior reading) (.prior signal)
  | throughComparison {context} {values : Values Value context} {past : RecurringFormation values}
      {first second : Ref context .reading} {output : Rational}
      (role : RecurringComputed values first second output)
      {reading : Ref context .reading} {signal : Ref context .signal}
      (arrival : RecurringArrival past reading signal) :
      RecurringArrival (.comparison past first second role) (.prior reading) (.prior signal)

def RecurringArrival.measure {context} {values : Values Value context} {past : RecurringFormation values}
    {reading : Ref context .reading} {signal : Ref context .signal}
    (arrival : RecurringArrival past reading signal) : Rational := by
  cases arrival with
  | fromCursor old => exact old.measure
  | fromInstrument old => exact old.measure
  | @received context values _ signal => exact (read values signal).reading
  | throughSignal _ old => exact old.measure
  | throughComparison _ old => exact old.measure
termination_by structural arrival

theorem RecurringArrival.measure_exact {context} {values : Values Value context} {past : RecurringFormation values}
    {reading : Ref context .reading} {signal : Ref context .signal}
    (arrival : RecurringArrival past reading signal) : arrival.measure = read values reading := by
  induction arrival with
  | fromCursor old => exact old.measure_exact
  | fromInstrument old => exact old.measure_exact
  | received past signal => rfl
  | throughSignal role old ih => exact ih
  | throughComparison role old ih => exact ih

/-- Each comparison is licensed at its own prefix by actual distinct arrivals.
This positive witness covers the entire history and is mandatory in a cursor. -/
inductive RecurringConstitution : {context : List Kind} → {values : Values Value context} →
    RecurringFormation (context := context) values → Type where
  | fromCursor (source : Cursor) : RecurringConstitution (.fromCursor source)
  | fromInstrument (source : InstrumentCursor) : RecurringConstitution (.fromInstrument source)
  | signal {context} {values : Values Value context} {past : RecurringFormation values}
      (constitution : RecurringConstitution past) {kind} {instruction : Instruction context kind}
      {output : Value kind} (role : Produces values instruction output) :
      RecurringConstitution (.signal past role)
  | comparison {context} {values : Values Value context} {past : RecurringFormation values}
      (constitution : RecurringConstitution past) {first second : Ref context .reading}
      {firstSignal secondSignal : Ref context .signal}
      (one : RecurringArrival past first firstSignal) (two : RecurringArrival past second secondSignal)
      (distinct : first ≠ second) {output : Rational} (role : RecurringComputed values first second output) :
      RecurringConstitution (.comparison past first second role)

def findRecurringArrival {context} {values : Values Value context}
    (past : RecurringFormation values) (reading : Ref context .reading) :
    Option ((signal : Ref context .signal) ×' RecurringArrival past reading signal) := by
  cases past with
  | fromCursor source =>
    exact (findArrival source.formation reading).map (fun found => ⟨found.1, .fromCursor found.2⟩)
  | fromInstrument source =>
    exact (findInstrumentArrival source.formation reading).map (fun found => ⟨found.1, .fromInstrument found.2⟩)
  | signal old role =>
    cases reading with
    | here => cases role with | received signal => exact some ⟨.prior signal, .received old signal⟩
    | prior ref => exact (findRecurringArrival old ref).map (fun found => ⟨.prior found.1, .throughSignal role found.2⟩)
  | comparison old first second role =>
    cases reading with
    | here => exact none
    | prior ref => exact (findRecurringArrival old ref).map (fun found => ⟨.prior found.1, .throughComparison role found.2⟩)
termination_by structural past

theorem RecurringArrival.find_present {context} {values : Values Value context} {past : RecurringFormation values}
    {reading : Ref context .reading} {signal : Ref context .signal}
    (arrival : RecurringArrival past reading signal) :
    ∃ found, findRecurringArrival past reading = some found := by
  induction arrival with
  | fromCursor old =>
    obtain ⟨found, exactFound⟩ := old.find_present
    refine ⟨⟨found.1, .fromCursor found.2⟩, ?_⟩
    change (findArrival _ _).map _ = _
    rw [exactFound]; rfl
  | fromInstrument old =>
    obtain ⟨found, exactFound⟩ := old.find_present
    refine ⟨⟨found.1, .fromInstrument found.2⟩, ?_⟩
    change (findInstrumentArrival _ _).map _ = _
    rw [exactFound]; rfl
  | received past signal => exact ⟨⟨.prior signal, .received past signal⟩, rfl⟩
  | throughSignal role old ih =>
    obtain ⟨found, exactFound⟩ := ih
    refine ⟨⟨.prior found.1, .throughSignal role found.2⟩, ?_⟩
    change (findRecurringArrival _ _).map _ = _
    rw [exactFound]; rfl
  | throughComparison role old ih =>
    obtain ⟨found, exactFound⟩ := ih
    refine ⟨⟨.prior found.1, .throughComparison role found.2⟩, ?_⟩
    change (findRecurringArrival _ _).map _ = _
    rw [exactFound]; rfl

def resolveRecurringArrival {context} {values : Values Value context}
    (past : RecurringFormation values) (reading : Ref context .reading) :
    PSum ((signal : Ref context .signal) ×' RecurringArrival past reading signal)
      (((signal : Ref context .signal) ×' RecurringArrival past reading signal) → False) :=
  match found : findRecurringArrival past reading with
  | some arrival => .inl arrival
  | none => .inr (fun arrival => by
      obtain ⟨located, exactLocated⟩ := arrival.2.find_present
      rw [found] at exactLocated
      cases exactLocated)

def recurringComparisonLower {context} (first second : Ref context .reading) : Producer Value context where
  inputKinds := [.reading, .reading]
  inputs := .cons first (.cons second .nil)
  outputKind := fun _ => .reading
  operation := fun arguments => Rational.sub arguments.2.1 arguments.1

def RecurringComputed.resourceFormation {context} {values : Values Value context}
    {first second : Ref context .reading} {output : Rational}
    (role : RecurringComputed values first second output)
    (priorFormation : Formation Value (context := context) values) :
    Formation Value (context := .reading :: context) (output, values) := by
  cases role
  exact .produced priorFormation (recurringComparisonLower first second)

inductive RecurringInterpretation : {context : List Kind} → {values : Values Value context} →
    RecurringFormation (context := context) values → Formation Value (context := context) values → Prop where
  | fromCursor (source : Cursor) : RecurringInterpretation (.fromCursor source) source.resourceFormation
  | fromInstrument (source : InstrumentCursor) :
      RecurringInterpretation (.fromInstrument source) source.resourceFormation
  | signal {context} {values : Values Value context} {past : RecurringFormation values}
      {resource : Formation Value (context := context) values} (exactPast : RecurringInterpretation past resource)
      {kind} {instruction : Instruction context kind} {output : Value kind}
      (role : Produces values instruction output) :
      RecurringInterpretation (.signal past role) (role.resourceFormation resource)
  | comparison {context} {values : Values Value context} {past : RecurringFormation values}
      {resource : Formation Value (context := context) values} (exactPast : RecurringInterpretation past resource)
      {first second : Ref context .reading} {output : Rational}
      (role : RecurringComputed values first second output) :
      RecurringInterpretation (.comparison past first second role) (role.resourceFormation resource)

structure RecurringCursor where
  kinds : List Kind
  values : Values Value kinds
  formation : RecurringFormation values
  constitution : RecurringConstitution formation
  resourceFormation : Formation Value (context := kinds) values
  resourceExact : RecurringInterpretation formation resourceFormation

def RecurringCursor.fromCursor (source : Cursor) : RecurringCursor :=
  ⟨source.kinds, source.values, .fromCursor source, .fromCursor source,
    source.resourceFormation, .fromCursor source⟩

def RecurringCursor.fromInstrument (source : InstrumentCursor) : RecurringCursor :=
  ⟨source.kinds, source.values, .fromInstrument source, .fromInstrument source,
    source.resourceFormation, .fromInstrument source⟩

def RecurringCursor.read (source : RecurringCursor) {kind} (ref : Ref source.kinds kind) : Value kind :=
  ConstitutiveSearch.Resources.read source.values ref

def RecurringCursor.support (source : RecurringCursor) : Support Value source.kinds :=
  ⟨source.values, source.resourceFormation⟩

theorem recurring_embeds_actual_instrument (source : InstrumentCursor) :
    (RecurringCursor.fromInstrument source).support = source.support := rfl

structure RecurringPair (source : RecurringCursor) where
  first : Ref source.kinds .reading
  second : Ref source.kinds .reading
  firstSignal : Ref source.kinds .signal
  secondSignal : Ref source.kinds .signal
  firstArrival : RecurringArrival source.formation first firstSignal
  secondArrival : RecurringArrival source.formation second secondSignal
  distinct : first ≠ second

def RecurringPair.gap {source : RecurringCursor} (pair : RecurringPair source) : Rational :=
  Rational.sub pair.secondArrival.measure pair.firstArrival.measure

theorem RecurringPair.gap_exact {source : RecurringCursor} (pair : RecurringPair source) :
    pair.gap = recurringDifference source.values pair.first pair.second :=
  (congrArg (fun second => Rational.sub second pair.firstArrival.measure) pair.secondArrival.measure_exact).trans
    (congrArg (Rational.sub (source.read pair.second)) pair.firstArrival.measure_exact)

inductive RecurringAction (source : RecurringCursor) : Kind → Type where
  | signal {kind} : Instruction source.kinds kind → RecurringAction source kind
  | compare : RecurringPair source → RecurringAction source .reading

inductive RecurringProduces (source : RecurringCursor) :
    {kind : Kind} → RecurringAction source kind → Value kind → Type where
  | signal {kind} {instruction : Instruction source.kinds kind} {output : Value kind}
      (role : Produces source.values instruction output) : RecurringProduces source (.signal instruction) output
  | compared {pair : RecurringPair source} {output : Rational}
      (role : RecurringComputed source.values pair.first pair.second output) :
      RecurringProduces source (.compare pair) output

abbrev RecurringDetermination (source : RecurringCursor) {kind} (action : RecurringAction source kind) :=
  (output : Value kind) ×' RecurringProduces source action output

def executeRecurring (source : RecurringCursor) :
    {kind : Kind} → (action : RecurringAction source kind) → RecurringDetermination source action
  | _, .signal instruction =>
      let produced := execute source.values instruction
      ⟨produced.1, .signal produced.2⟩
  | _, .compare pair => ⟨pair.gap, .compared (pair.gap_exact.symm ▸ RecurringComputed.computed)⟩

def RecurringProduces.formation {source : RecurringCursor} {kind} {action : RecurringAction source kind}
    {output : Value kind} (role : RecurringProduces source action output) :
    RecurringFormation (context := kind :: source.kinds) (output, source.values) := by
  cases action with
  | signal instruction =>
    cases role with
    | signal localRole => exact .signal source.formation localRole
  | compare pair =>
    cases role with
    | compared comparedRole => exact .comparison source.formation pair.first pair.second comparedRole

def RecurringProduces.constitution {source : RecurringCursor} {kind} {action : RecurringAction source kind}
    {output : Value kind} (role : RecurringProduces source action output) : RecurringConstitution role.formation := by
  cases action with
  | signal instruction =>
    cases role with
    | signal localRole => exact .signal source.constitution localRole
  | compare pair =>
    cases role with
    | compared comparedRole =>
      exact .comparison source.constitution pair.firstArrival pair.secondArrival pair.distinct comparedRole

def RecurringProduces.resourceFormation {source : RecurringCursor} {kind} {action : RecurringAction source kind}
    {output : Value kind} (role : RecurringProduces source action output) :
    Formation Value (context := kind :: source.kinds) (output, source.values) := by
  cases action with
  | signal instruction => cases role with | signal localRole => exact localRole.resourceFormation source.resourceFormation
  | compare pair => cases role with | compared comparedRole => exact comparedRole.resourceFormation source.resourceFormation

theorem RecurringProduces.interpretation {source : RecurringCursor} {kind} {action : RecurringAction source kind}
    {output : Value kind} (role : RecurringProduces source action output) :
    RecurringInterpretation role.formation role.resourceFormation := by
  cases action with
  | signal instruction => cases role with | signal localRole => exact .signal source.resourceExact localRole
  | compare pair => cases role with | compared comparedRole => exact .comparison source.resourceExact comparedRole

/-- Sorts and values are direct projections of the shared determination.
Reading a resource does not eliminate all its formation witnesses first. -/
def RecurringCursor.extend (source : RecurringCursor) {kind} {action : RecurringAction source kind}
    (determination : RecurringDetermination source action) : RecurringCursor :=
  ⟨kind :: source.kinds, (determination.1, source.values), determination.2.formation,
    determination.2.constitution, determination.2.resourceFormation, determination.2.interpretation⟩

structure RecurringProduction (source : RecurringCursor) {kind} (action : RecurringAction source kind) where
  determination : RecurringDetermination source action
  successor : RecurringCursor
  successorExact : successor = source.extend determination

def performRecurring (source : RecurringCursor) {kind} (action : RecurringAction source kind) :
    RecurringProduction source action :=
  let determination := executeRecurring source action
  let successor := source.extend determination
  ⟨determination, successor, rfl⟩

theorem recurring_comparison_output (source : RecurringCursor) (pair : RecurringPair source) :
    (performRecurring source (.compare pair)).determination.1 =
      Rational.sub (source.read pair.second) (source.read pair.first) := pair.gap_exact

def recurringExtendTransport (source : RecurringCursor) {kind} {action : RecurringAction source kind}
    (determination : RecurringDetermination source action) :
    Support.Extension source.support (source.extend determination).support := by
  cases action with
  | signal instruction =>
    cases determination with
    | mk output role => cases role; exact ⟨Ref.prior, fun _ => rfl, prior_injective, 1, fun _ => rfl⟩
  | compare pair =>
    cases determination with
    | mk output role => cases role; exact ⟨Ref.prior, fun _ => rfl, prior_injective, 1, fun _ => rfl⟩

structure RecurringStep (source target : RecurringCursor) where
  kind : Kind
  action : RecurringAction source kind
  determination : RecurringDetermination source action
  targetExact : target = source.extend determination

abbrev RecurringHistory := StrongPerimetralTurning.History RecurringStep

def recurringProductionHistory {source : RecurringCursor} {kind} {action : RecurringAction source kind}
    (head : RecurringProduction source action) : RecurringHistory source head.successor :=
  .extend .root ⟨kind, action, head.determination, head.successorExact⟩

def RecurringStep.transport {source target : RecurringCursor} (step : RecurringStep source target) :
    Support.Extension source.support target.support :=
  step.targetExact.symm ▸ recurringExtendTransport source step.determination

def recurringHistoryTransport {source target : RecurringCursor} (history : RecurringHistory source target) :
    Support.Extension source.support target.support :=
  match history with
  | .root => .identity _
  | .extend past step => (recurringHistoryTransport past).compose step.transport
termination_by structural history

def RecurringStep.transportArrival {source target : RecurringCursor} (step : RecurringStep source target)
    {reading : Ref source.kinds .reading} {signal : Ref source.kinds .signal}
    (arrival : RecurringArrival source.formation reading signal) :
    RecurringArrival target.formation (step.transport.references reading) (step.transport.references signal) := by
  cases step with
  | mk kind action determination exactTarget =>
    cases exactTarget
    cases action with
    | signal instruction =>
      cases determination with
      | mk output role => cases role with | signal localRole => exact .throughSignal localRole arrival
    | compare pair =>
      cases determination with
      | mk output role => cases role with | compared comparedRole => exact .throughComparison comparedRole arrival

def recurringHistoryArrival {source target : RecurringCursor} (history : RecurringHistory source target)
    {reading : Ref source.kinds .reading} {signal : Ref source.kinds .signal}
    (arrival : RecurringArrival source.formation reading signal) :
    RecurringArrival target.formation ((recurringHistoryTransport history).references reading)
      ((recurringHistoryTransport history).references signal) :=
  match history with
  | .root => arrival
  | .extend past step => step.transportArrival (recurringHistoryArrival past arrival)
termination_by structural history

theorem recurring_history_arrival_measure {source target : RecurringCursor} (history : RecurringHistory source target)
    {reading : Ref source.kinds .reading} {signal : Ref source.kinds .signal}
    (arrival : RecurringArrival source.formation reading signal) :
    (recurringHistoryArrival history arrival).measure = arrival.measure :=
  (recurringHistoryArrival history arrival).measure_exact.trans
    (((recurringHistoryTransport history).reads reading).trans arrival.measure_exact.symm)

def recurringArrivalOfProduction {source : RecurringCursor} {signal : Ref source.kinds .signal}
    (head : RecurringProduction source (.signal (.receive signal))) :
    RecurringArrival head.successor.formation
      (head.successorExact.symm ▸ (Ref.here : Ref (source.extend head.determination).kinds .reading))
      (head.successorExact.symm ▸ (Ref.prior signal : Ref (source.extend head.determination).kinds .signal)) := by
  cases head with
  | mk determination successor exactSuccessor =>
    cases exactSuccessor
    cases determination with
    | mk output role =>
      cases role with
      | signal localRole => cases localRole; exact .received source.formation signal

def RecurringPair.transport {source target : RecurringCursor} (pair : RecurringPair source)
    (history : RecurringHistory source target) : RecurringPair target :=
  let extension := recurringHistoryTransport history
  ⟨extension.references pair.first, extension.references pair.second,
    extension.references pair.firstSignal, extension.references pair.secondSignal,
    recurringHistoryArrival history pair.firstArrival, recurringHistoryArrival history pair.secondArrival,
    fun same => pair.distinct (extension.injective _ _ same)⟩

theorem recurring_comparison_not_reception (source : RecurringCursor) (pair : RecurringPair source)
    {signal : Ref (performRecurring source (.compare pair)).successor.kinds .signal}
    (arrival : RecurringArrival (performRecurring source (.compare pair)).successor.formation .here signal) : False := by
  obtain ⟨found, impossible⟩ := arrival.find_present
  change none = some found at impossible
  cases impossible

theorem recurring_given_not_reception (input : Received) {reading : Ref receivedKinds .reading}
    {signal : Ref receivedKinds .signal}
    (arrival : RecurringArrival (RecurringCursor.fromCursor (.received input)).formation reading signal) : False := by
  obtain ⟨found, impossible⟩ := arrival.find_present
  change none = some found at impossible
  cases impossible

inductive RecurringComparisonPort {context : List Kind} (first second : Ref context Kind.reading) :
    Ref context Kind.reading → Type where
  | first : RecurringComparisonPort first second first
  | second : RecurringComparisonPort first second second

inductive RecurringUsed : {context : List Kind} → {values : Values Value context} →
    RecurringFormation (context := context) values → Occurrence context → Occurrence context → Type where
  | fromCursor {source : Cursor} {one two : Occurrence source.kinds} (edge : Used source.formation one two) :
      RecurringUsed (.fromCursor source) one two
  | fromInstrument {source : InstrumentCursor} {one two : Occurrence source.kinds}
      (edge : InstrumentUsed source.formation one two) : RecurringUsed (.fromInstrument source) one two
  | signal {context} {values : Values Value context} (past : RecurringFormation values)
      {kind inputKind} {instruction : Instruction context kind} {output : Value kind}
      (role : Produces values instruction output) (ref : Ref context inputKind) (port : InputPort instruction ref) :
      RecurringUsed (.signal past role) (oldOccurrence kind ⟨inputKind, ref⟩) (freshOccurrence context kind)
  | comparison {context} {values : Values Value context} (past : RecurringFormation values)
      {first second : Ref context .reading} {output : Rational} (role : RecurringComputed values first second output)
      (ref : Ref context .reading) (port : RecurringComparisonPort first second ref) :
      RecurringUsed (.comparison past first second role) (oldOccurrence .reading ⟨.reading, ref⟩)
        (freshOccurrence context .reading)
  | throughSignal {context} {values : Values Value context} {past : RecurringFormation values}
      {kind} {instruction : Instruction context kind} {output : Value kind} (role : Produces values instruction output)
      {one two : Occurrence context} (edge : RecurringUsed past one two) :
      RecurringUsed (.signal past role) (oldOccurrence kind one) (oldOccurrence kind two)
  | throughComparison {context} {values : Values Value context} {past : RecurringFormation values}
      {first second : Ref context .reading} {output : Rational} (role : RecurringComputed values first second output)
      {one two : Occurrence context} (edge : RecurringUsed past one two) :
      RecurringUsed (.comparison past first second role) (oldOccurrence .reading one) (oldOccurrence .reading two)

theorem RecurringUsed.position_decreases {context} {values : Values Value context} {past : RecurringFormation values}
    {one two : Occurrence context} (edge : RecurringUsed past one two) : two.2.position < one.2.position := by
  induction edge with
  | fromCursor old => exact old.position_decreases
  | fromInstrument old => exact old.position_decreases
  | signal past role ref port => exact Nat.zero_lt_succ _
  | comparison past role ref port => exact Nat.zero_lt_succ _
  | throughSignal role old ih => exact Nat.add_lt_add_right ih 1
  | throughComparison role old ih => exact Nat.add_lt_add_right ih 1

theorem RecurringUsed.no_cycle {context} {values : Values Value context} {past : RecurringFormation values}
    {one : Occurrence context} (edge : RecurringUsed past one one) : False := Nat.lt_irrefl _ edge.position_decreases

def RecurringStep.transportUsed {source target : RecurringCursor} (step : RecurringStep source target)
    {one two : Occurrence source.kinds} (edge : RecurringUsed source.formation one two) :
    RecurringUsed target.formation ⟨one.1, step.transport.references one.2⟩ ⟨two.1, step.transport.references two.2⟩ := by
  cases step with
  | mk kind action determination exactTarget =>
    cases exactTarget
    cases action with
    | signal instruction =>
      cases determination with
      | mk output role => cases role with | signal localRole => exact .throughSignal localRole edge
    | compare pair =>
      cases determination with
      | mk output role => cases role with | compared comparedRole => exact .throughComparison comparedRole edge

def recurringHistoryUsed {source target : RecurringCursor} (history : RecurringHistory source target)
    {one two : Occurrence source.kinds} (edge : RecurringUsed source.formation one two) :
    RecurringUsed target.formation ⟨one.1, (recurringHistoryTransport history).references one.2⟩
      ⟨two.1, (recurringHistoryTransport history).references two.2⟩ :=
  match history with
  | .root => edge
  | .extend past step => step.transportUsed (recurringHistoryUsed past edge)
termination_by structural history

def recurring_comparison_first_used (source : RecurringCursor) (pair : RecurringPair source) :
    RecurringUsed (performRecurring source (.compare pair)).successor.formation
      (oldOccurrence .reading ⟨.reading, pair.first⟩) (freshOccurrence source.kinds .reading) :=
  .comparison source.formation _ pair.first .first

def recurring_comparison_second_used (source : RecurringCursor) (pair : RecurringPair source) :
    RecurringUsed (performRecurring source (.compare pair)).successor.formation
      (oldOccurrence .reading ⟨.reading, pair.second⟩) (freshOccurrence source.kinds .reading) :=
  .comparison source.formation _ pair.second .second

end RelationalPerimeter.Relativity.Production
/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Relativity.Production.InstrumentArrived.measure_exact
#print axioms RelationalPerimeter.Relativity.Production.InstrumentArrived.find_present
#print axioms RelationalPerimeter.Relativity.Production.RecurringArrival.measure_exact
#print axioms RelationalPerimeter.Relativity.Production.RecurringArrival.find_present
#print axioms RelationalPerimeter.Relativity.Production.resolveRecurringArrival
#print axioms RelationalPerimeter.Relativity.Production.RecurringComputed.resourceFormation
#print axioms RelationalPerimeter.Relativity.Production.RecurringConstitution
#print axioms RelationalPerimeter.Relativity.Production.recurring_embeds_actual_instrument
#print axioms RelationalPerimeter.Relativity.Production.RecurringPair.gap_exact
#print axioms RelationalPerimeter.Relativity.Production.executeRecurring
#print axioms RelationalPerimeter.Relativity.Production.RecurringCursor.extend
#print axioms RelationalPerimeter.Relativity.Production.RecurringProduces.formation
#print axioms RelationalPerimeter.Relativity.Production.RecurringProduces.constitution
#print axioms RelationalPerimeter.Relativity.Production.RecurringProduces.resourceFormation
#print axioms RelationalPerimeter.Relativity.Production.RecurringProduces.interpretation
#print axioms RelationalPerimeter.Relativity.Production.performRecurring
#print axioms RelationalPerimeter.Relativity.Production.recurring_comparison_output
#print axioms RelationalPerimeter.Relativity.Production.recurringExtendTransport
#print axioms RelationalPerimeter.Relativity.Production.recurringProductionHistory
#print axioms RelationalPerimeter.Relativity.Production.recurringHistoryTransport
#print axioms RelationalPerimeter.Relativity.Production.RecurringStep.transportArrival
#print axioms RelationalPerimeter.Relativity.Production.recurringHistoryArrival
#print axioms RelationalPerimeter.Relativity.Production.recurring_history_arrival_measure
#print axioms RelationalPerimeter.Relativity.Production.RecurringPair.transport
#print axioms RelationalPerimeter.Relativity.Production.recurringArrivalOfProduction
#print axioms RelationalPerimeter.Relativity.Production.recurring_comparison_not_reception
#print axioms RelationalPerimeter.Relativity.Production.recurring_given_not_reception
#print axioms RelationalPerimeter.Relativity.Production.RecurringUsed.position_decreases
#print axioms RelationalPerimeter.Relativity.Production.RecurringUsed.no_cycle
#print axioms RelationalPerimeter.Relativity.Production.RecurringStep.transportUsed
#print axioms RelationalPerimeter.Relativity.Production.recurringHistoryUsed
#print axioms RelationalPerimeter.Relativity.Production.recurring_comparison_first_used
#print axioms RelationalPerimeter.Relativity.Production.recurring_comparison_second_used
/- AXIOM_AUDIT_END -/
