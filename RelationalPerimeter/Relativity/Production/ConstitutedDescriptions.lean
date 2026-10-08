import RelationalPerimeter.Relativity.Production.GroupedRecurringContinuation

/-!
# Descriptions attached to constituted occurrences

A description path incorporates cached productions or an exact presentation
change. It does not create an occurrence from its value, execute a producer,
or erase a path effect. Selecting additional record readers is a descriptive
refinement, not a new physical production or a numerical precision refinement.
The full recurring contract is unchanged; partial agreement is not a license
to forget. No localization, metric or continuum is supplied by these readers.
-/
set_option genInjectivity false
namespace RelationalPerimeter.Relativity.Production
open ConstitutiveSearch.Resources
open ConstitutiveSearch.ContinuationSignatures

inductive DescriptionPath (origin : RecurringCursor) : RecurringCursor → Type where
  | root : DescriptionPath origin origin
  | produced {source} (past : DescriptionPath origin source) {kind}
      {action : RecurringAction source kind} (head : RecurringProduction source action) :
      DescriptionPath origin head.successor
  | reexpressed {source target} (past : DescriptionPath origin source)
      (raccord : AddressedRecurringRaccord source target) : DescriptionPath origin target

def DescriptionPath.reference {origin current} (path : DescriptionPath origin current) :
    {kind : Kind} → Ref origin.kinds kind → Ref current.kinds kind :=
  match path with
  | .root => id
  | .produced past head => fun ref =>
      (recurringHistoryTransport (recurringProductionHistory head)).references (past.reference ref)
  | .reexpressed past raccord => fun ref => raccord.constitution.references.forward (past.reference ref)
termination_by structural path

theorem DescriptionPath.reads {origin current} (path : DescriptionPath origin current)
    {kind} (ref : Ref origin.kinds kind) : current.read (path.reference ref) = origin.read ref := by
  induction path with
  | root => rfl
  | produced past head ih =>
    exact ((recurringHistoryTransport (recurringProductionHistory head)).reads _).trans ih
  | reexpressed past raccord ih => exact (raccord.constitution.reads _).trans ih

theorem DescriptionPath.injective {origin current} (path : DescriptionPath origin current)
    {kind} (one two : Ref origin.kinds kind) (same : path.reference one = path.reference two) : one = two := by
  induction path with
  | root => exact same
  | produced past head ih => exact ih ((recurringHistoryTransport (recurringProductionHistory head)).injective _ _ same)
  | reexpressed past raccord ih =>
    exact ih ((raccord.constitution.references.forwardBackward _).symm.trans
      ((congrArg raccord.constitution.references.backward same).trans
        (raccord.constitution.references.forwardBackward _)))

def DescriptionPath.arrival {origin current} (path : DescriptionPath origin current)
    {reading signal} (arrival : RecurringArrival origin.formation reading signal) :
    RecurringArrival current.formation (path.reference reading) (path.reference signal) :=
  match path with
  | .root => arrival
  | .produced past head => recurringHistoryArrival (recurringProductionHistory head) (past.arrival arrival)
  | .reexpressed past raccord => raccord.constitution.forwardArrival (past.arrival arrival)
termination_by structural path

def DescriptionPath.used {origin current} (path : DescriptionPath origin current)
    {one two : Occurrence origin.kinds} (edge : RecurringUsed origin.formation one two) :
    RecurringUsed current.formation ⟨one.1, path.reference one.2⟩ ⟨two.1, path.reference two.2⟩ :=
  match path with
  | .root => edge
  | .produced past head => recurringHistoryUsed (recurringProductionHistory head) (past.used edge)
  | .reexpressed past raccord => raccord.constitution.forwardUsed (past.used edge)
termination_by structural path

/-- The suffix has already run. This fold consumes its stored determinations. -/
def DescriptionPath.prolong {origin source target} (path : DescriptionPath origin source)
    (history : RecurringHistory source target) : DescriptionPath origin target :=
  match history with
  | .root => path
  | .extend past step => .produced (path.prolong past) ⟨step.determination, _, step.targetExact⟩
termination_by structural history

theorem DescriptionPath.prolong_reference {origin source target} (path : DescriptionPath origin source)
    (history : RecurringHistory source target) {kind} (ref : Ref origin.kinds kind) :
    (path.prolong history).reference ref = (recurringHistoryTransport history).references (path.reference ref) := by
  induction history with
  | root => rfl
  | extend past step ih => exact congrArg step.transport.references ih

def DescriptionPath.append {origin middle current} (first : DescriptionPath origin middle)
    (second : DescriptionPath middle current) : DescriptionPath origin current :=
  match second with
  | .root => first
  | .produced past head => .produced (first.append past) head
  | .reexpressed past raccord => .reexpressed (first.append past) raccord
termination_by structural second

theorem DescriptionPath.append_reference {origin middle current} (first : DescriptionPath origin middle)
    (second : DescriptionPath middle current) {kind} (ref : Ref origin.kinds kind) :
    (first.append second).reference ref = second.reference (first.reference ref) := by
  induction second with
  | root => rfl
  | produced past head ih => exact congrArg (recurringHistoryTransport (recurringProductionHistory head)).references ih
  | reexpressed past raccord ih => exact congrArg raccord.constitution.references.forward ih

def DescriptionPath.producedCount {origin current} (path : DescriptionPath origin current) : Nat :=
  match path with
  | .root => 0
  | .produced past _ => past.producedCount + 1
  | .reexpressed past _ => past.producedCount
termination_by structural path

theorem DescriptionPath.prolong_count {origin source target} (path : DescriptionPath origin source)
    (history : RecurringHistory source target) :
    (path.prolong history).producedCount = path.producedCount + StrongPerimetralTurning.History.length history := by
  induction history with
  | root => rfl
  | extend past step ih => exact (congrArg (fun count => count + 1) ih).trans (Nat.add_assoc ..)

theorem description_round_trip_reference {origin source target} (path : DescriptionPath origin source)
    (raccord : AddressedRecurringRaccord source target) {kind} (ref : Ref origin.kinds kind) :
    ((path.reexpressed raccord).reexpressed raccord.reverse).reference ref = path.reference ref :=
  raccord.constitution.references.forwardBackward _

structure SignalReaders where
  payload : Bool
  reading : Bool
  increments : Bool

def SignalReaders.full : SignalReaders := ⟨true, true, true⟩
def SignalReaders.join (one two : SignalReaders) : SignalReaders :=
  ⟨one.payload || two.payload, one.reading || two.reading, one.increments || two.increments⟩

structure ReaderRefinement (coarse fine : SignalReaders) : Prop where
  payload : coarse.payload = true → fine.payload = true
  reading : coarse.reading = true → fine.reading = true
  increments : coarse.increments = true → fine.increments = true

theorem reader_left_in_join (one two : SignalReaders) : ReaderRefinement one (one.join two) :=
  ⟨fun yes => by change (one.payload || two.payload) = true; rw [yes]; rfl,
    fun yes => by change (one.reading || two.reading) = true; rw [yes]; rfl,
    fun yes => by change (one.increments || two.increments) = true; rw [yes]; rfl⟩

theorem reader_right_in_join (one two : SignalReaders) : ReaderRefinement two (one.join two) :=
  ⟨fun yes => by change (one.payload || two.payload) = true; rw [yes]; cases one.payload <;> rfl,
    fun yes => by change (one.reading || two.reading) = true; rw [yes]; cases one.reading <;> rfl,
    fun yes => by change (one.increments || two.increments) = true; rw [yes]; cases one.increments <;> rfl⟩

theorem ReaderRefinement.trans {one two three : SignalReaders}
    (first : ReaderRefinement one two) (second : ReaderRefinement two three) : ReaderRefinement one three :=
  ⟨fun yes => second.payload (first.payload yes), fun yes => second.reading (first.reading yes),
    fun yes => second.increments (first.increments yes)⟩

structure SignalObservation where
  payload : Option Nat
  reading : Option Rational
  increments : Option (List Rational)

def keepRead {α : Type} (selected : Bool) (value : Option α) : Option α :=
  if selected then value else none

def observeSignal (readers : SignalReaders) (record : SignalRecord) : SignalObservation :=
  ⟨keepRead readers.payload (some record.payload), keepRead readers.reading (some record.reading),
    keepRead readers.increments (some record.increments)⟩

/-- Restriction consumes the richer observation, not the support or a producer. -/
def SignalObservation.restrict (observation : SignalObservation) (readers : SignalReaders) : SignalObservation :=
  ⟨keepRead readers.payload observation.payload, keepRead readers.reading observation.reading,
    keepRead readers.increments observation.increments⟩

theorem keep_read_restrict {α : Type} (coarse fine : Bool)
    (refines : coarse = true → fine = true) (value : Option α) :
    keepRead coarse (keepRead fine value) = keepRead coarse value := by
  cases coarse with
  | false => rfl
  | true => have same := refines rfl; cases same; rfl

theorem restrict_signal_exact {coarse fine} (refinement : ReaderRefinement coarse fine) (record : SignalRecord) :
    (observeSignal fine record).restrict coarse = observeSignal coarse record := by
  dsimp only [observeSignal, SignalObservation.restrict]
  rw [keep_read_restrict _ _ refinement.payload, keep_read_restrict _ _ refinement.reading,
    keep_read_restrict _ _ refinement.increments]

theorem signal_restriction_compose {one two} (refinement : ReaderRefinement one two)
    (observation : SignalObservation) : (observation.restrict two).restrict one = observation.restrict one := by
  dsimp only [SignalObservation.restrict]
  rw [keep_read_restrict _ _ refinement.payload, keep_read_restrict _ _ refinement.reading,
    keep_read_restrict _ _ refinement.increments]

theorem joint_signal_readers_exact (one two : SignalRecord) :
    observeSignal .full one = observeSignal .full two ↔ one = two := by
  constructor
  · intro same
    have payload := Option.some.inj (congrArg SignalObservation.payload same)
    have reading := Option.some.inj (congrArg SignalObservation.reading same)
    have increments := Option.some.inj (congrArg SignalObservation.increments same)
    cases one; cases two
    cases payload; cases reading; cases increments
    rfl
  · intro same; cases same; rfl

/-- The anchor is an occurrence of the formed origin, not a tuple of values. -/
def describeSignal {origin current} (path : DescriptionPath origin current)
    (anchor : Ref origin.kinds .signal) (readers : SignalReaders) : SignalObservation :=
  observeSignal readers (current.read (path.reference anchor))

theorem described_signal_exact {origin current} (path : DescriptionPath origin current)
    (anchor : Ref origin.kinds .signal) (readers : SignalReaders) :
    describeSignal path anchor readers = observeSignal readers (origin.read anchor) :=
  congrArg (observeSignal readers) (path.reads anchor)

theorem described_signal_restriction {origin current} (path : DescriptionPath origin current)
    (anchor : Ref origin.kinds .signal) {coarse fine} (refinement : ReaderRefinement coarse fine) :
    (describeSignal path anchor fine).restrict coarse = describeSignal path anchor coarse :=
  restrict_signal_exact refinement _

theorem described_signal_common_refinement {origin current} (path : DescriptionPath origin current)
    (anchor : Ref origin.kinds .signal) (one two : SignalReaders) :
    (describeSignal path anchor (one.join two)).restrict one = describeSignal path anchor one ∧
      (describeSignal path anchor (one.join two)).restrict two = describeSignal path anchor two :=
  ⟨described_signal_restriction path anchor (reader_left_in_join one two),
    described_signal_restriction path anchor (reader_right_in_join one two)⟩

theorem described_signal_prolong {origin source target} (path : DescriptionPath origin source)
    (history : RecurringHistory source target) (anchor : Ref origin.kinds .signal) (readers : SignalReaders) :
    describeSignal (path.prolong history) anchor readers = describeSignal path anchor readers :=
  (described_signal_exact _ _ _).trans (described_signal_exact _ _ _).symm

theorem described_signal_reexpress {origin source target} (path : DescriptionPath origin source)
    (raccord : AddressedRecurringRaccord source target) (anchor : Ref origin.kinds .signal) (readers : SignalReaders) :
    describeSignal (path.reexpressed raccord) anchor readers = describeSignal path anchor readers :=
  (described_signal_exact _ _ _).trans (described_signal_exact _ _ _).symm

/-- Actual continuation first, then the raccord of its actual final cursors.
Neither the found exchange nor this description calls the continuation again. -/
def continuedExchangeDescription {source firstKind secondKind}
    {first : Instruction source.kinds firstKind} {second : Instruction (firstKind :: source.kinds) secondKind}
    {pair : StoredPairProduction source first second} (found : DiscoveredStoredExchange pair)
    (run : CorrespondingRecurringRequests (RecurringCursor.fromCursor pair.cursor)
      (RecurringCursor.fromCursor found.exchanged.cursor)) :
    DescriptionPath (.fromCursor pair.cursor) run.second.cursor :=
  ((DescriptionPath.root.prolong run.first.history).reexpressed run.raccord)

theorem continued_exchange_description_exact {source firstKind secondKind}
    {first : Instruction source.kinds firstKind} {second : Instruction (firstKind :: source.kinds) secondKind}
    {pair : StoredPairProduction source first second} (found : DiscoveredStoredExchange pair)
    (run : CorrespondingRecurringRequests (RecurringCursor.fromCursor pair.cursor)
      (RecurringCursor.fromCursor found.exchanged.cursor))
    (anchor : Ref pair.cursor.kinds .signal) (readers : SignalReaders) :
    describeSignal (continuedExchangeDescription found run) anchor readers = observeSignal readers (pair.cursor.read anchor) :=
  described_signal_exact _ _ _

/-- A differing path record is still a future separator under the full contract.
Equality of a partial observation cannot be substituted for this obligation. -/
theorem differing_paths_separate_inspection (source target : RecurringCursor)
    (one : Ref source.kinds .signal) (two : Ref target.kinds .signal)
    (samePosition : two.position = one.position)
    (different : (source.read one).increments ≠ (target.read two).increments) :
    recurringContract.outcome source [.local (.inspect .signal one.position)] ≠
      recurringContract.outcome target [.local (.inspect .signal one.position)] := by
  intro same
  have observed := congrArg firstRecurringInspection same
  dsimp only [FutureContract.outcome, recurringContract] at observed
  rw [recurring_inspection_exact source one, ← samePosition, recurring_inspection_exact target two] at observed
  have record := Option.some.inj observed
  have full : source.read one = target.read two := LocalReadout.noConfusion record (fun same => same)
  exact different (congrArg SignalRecord.increments full)

theorem differing_paths_separate_futures (source target : RecurringCursor)
    (one : Ref source.kinds .signal) (two : Ref target.kinds .signal)
    (samePosition : two.position = one.position)
    (different : (source.read one).increments ≠ (target.read two).increments) :
    ¬ FutureEquivalent recurringContract source target := fun same =>
  differing_paths_separate_inspection source target one two samePosition different
    (same [.local (.inspect .signal one.position)])

end RelationalPerimeter.Relativity.Production
/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Relativity.Production.DescriptionPath.reference
#print axioms RelationalPerimeter.Relativity.Production.DescriptionPath.reads
#print axioms RelationalPerimeter.Relativity.Production.DescriptionPath.injective
#print axioms RelationalPerimeter.Relativity.Production.DescriptionPath.arrival
#print axioms RelationalPerimeter.Relativity.Production.DescriptionPath.used
#print axioms RelationalPerimeter.Relativity.Production.DescriptionPath.prolong
#print axioms RelationalPerimeter.Relativity.Production.DescriptionPath.prolong_reference
#print axioms RelationalPerimeter.Relativity.Production.DescriptionPath.append
#print axioms RelationalPerimeter.Relativity.Production.DescriptionPath.append_reference
#print axioms RelationalPerimeter.Relativity.Production.DescriptionPath.producedCount
#print axioms RelationalPerimeter.Relativity.Production.DescriptionPath.prolong_count
#print axioms RelationalPerimeter.Relativity.Production.description_round_trip_reference
#print axioms RelationalPerimeter.Relativity.Production.reader_left_in_join
#print axioms RelationalPerimeter.Relativity.Production.reader_right_in_join
#print axioms RelationalPerimeter.Relativity.Production.ReaderRefinement.trans
#print axioms RelationalPerimeter.Relativity.Production.observeSignal
#print axioms RelationalPerimeter.Relativity.Production.SignalObservation.restrict
#print axioms RelationalPerimeter.Relativity.Production.keep_read_restrict
#print axioms RelationalPerimeter.Relativity.Production.restrict_signal_exact
#print axioms RelationalPerimeter.Relativity.Production.signal_restriction_compose
#print axioms RelationalPerimeter.Relativity.Production.joint_signal_readers_exact
#print axioms RelationalPerimeter.Relativity.Production.describeSignal
#print axioms RelationalPerimeter.Relativity.Production.described_signal_exact
#print axioms RelationalPerimeter.Relativity.Production.described_signal_restriction
#print axioms RelationalPerimeter.Relativity.Production.described_signal_common_refinement
#print axioms RelationalPerimeter.Relativity.Production.described_signal_prolong
#print axioms RelationalPerimeter.Relativity.Production.described_signal_reexpress
#print axioms RelationalPerimeter.Relativity.Production.continuedExchangeDescription
#print axioms RelationalPerimeter.Relativity.Production.continued_exchange_description_exact
#print axioms RelationalPerimeter.Relativity.Production.differing_paths_separate_inspection
#print axioms RelationalPerimeter.Relativity.Production.differing_paths_separate_futures
/- AXIOM_AUDIT_END -/
