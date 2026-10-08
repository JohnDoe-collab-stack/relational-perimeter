import RelationalPerimeter.Relativity.Production.RecurringInteractions
import RelationalPerimeter.Relativity.Production.TransportedContinuations
import RelationalPerimeter.Relativity.Production.AddressTransport
import RelationalPerimeter.Relativity.Production.TransportedRequests

/-!
# Exact presentations of the recurring instrumental productions

Readings alone are insufficient. The raccord positively transports received
occurrences and used dependencies in both directions, with kind-preserving
reference return laws. Its extension consumes cached productions; it neither
replays an action nor supplies a replacement target. This remains the declared
local instrumental law, not an identification of events or a spacetime law.
-/
set_option genInjectivity false
namespace RelationalPerimeter.Relativity.Production
open ConstitutiveSearch.Resources

inductive ReceivedSignal {context : List Kind} (source : Ref context Kind.signal) :
    Ref (Kind.reading :: context) Kind.signal → Type where
  | exact : ReceivedSignal source (.prior source)

def arrivedView {context} {values : Values Value context} (past : Formed (context := context) values)
    (reading : Ref context .reading) (signal : Ref context .signal) : Type := by
  cases past with
  | received input => exact Empty
  | produced old role =>
    cases reading with
    | here => cases role with | received source => exact ReceivedSignal source signal
    | prior reading => cases signal with
      | here => exact Empty
      | prior signal => exact Arrived old reading signal

def Arrived.view {context} {values : Values Value context} {past : Formed (context := context) values}
    {reading signal} (arrival : Arrived past reading signal) : arrivedView past reading signal := by
  cases arrival with
  | received old signal => exact .exact
  | inherited role old => exact old

def Arrived.ofReception {context} {values : Values Value context} (past : Formed (context := context) values)
    {signal : Ref context .signal} {output} (role : Produces values (.receive signal) output) :
    Arrived (.produced past role) .here (.prior signal) := by
  cases role
  exact .received past signal

def Arrived.receptionSignal {context} {values : Values Value context} (past : Formed (context := context) values)
    {received : Ref context .signal} {output} (role : Produces values (.receive received) output)
    {signal : Ref (.reading :: context) .signal} (arrival : Arrived (.produced past role) .here signal) :
    ReceivedSignal received signal := by
  cases role
  exact arrival.view

/-- Positive constructor payloads, obtained from the actual arrival witness.
The views only eliminate stored productions; they do not execute them. -/
def recurringArrivalView {context} {values : Values Value context} (past : RecurringFormation values)
    (reading : Ref context .reading) (signal : Ref context .signal) : Type := by
  cases past with
  | fromCursor source => exact Arrived source.formation reading signal
  | fromInstrument source => exact InstrumentArrived source.formation reading signal
  | @signal context values old kind instruction output role =>
    cases reading with
    | here => cases role with | received source => exact ReceivedSignal source signal
    | prior ref =>
      cases signal with
      | here => exact Empty
      | prior source => exact RecurringArrival old ref source
  | comparison old first second role =>
    cases reading with
    | here => exact Empty
    | prior ref =>
      cases signal with
      | prior source => exact RecurringArrival old ref source

def RecurringArrival.view {context} {values : Values Value context} {past : RecurringFormation values}
    {reading : Ref context .reading} {signal : Ref context .signal}
    (arrival : RecurringArrival past reading signal) : recurringArrivalView past reading signal := by
  cases arrival with
  | fromCursor old => exact old
  | fromInstrument old => exact old
  | received old signal => exact .exact
  | throughSignal role old => exact old
  | throughComparison role old => exact old

def recurringUsedView {context} {values : Values Value context} (past : RecurringFormation values)
    (one two : Occurrence context) : Type := by
  cases past with
  | fromCursor source => exact Used source.formation one two
  | fromInstrument source => exact InstrumentUsed source.formation one two
  | @signal context values old kind instruction output role =>
    cases one with
    | mk firstKind firstRef =>
      cases firstRef with
      | here => exact Empty
      | prior firstRef =>
        cases two with
        | mk secondKind secondRef =>
          cases secondRef with
          | here => exact InputPort instruction firstRef
          | prior secondRef => exact RecurringUsed old ⟨firstKind, firstRef⟩ ⟨secondKind, secondRef⟩
  | comparison old first second role =>
    cases one with
    | mk firstKind firstRef =>
      cases firstRef with
      | here => exact Empty
      | prior firstRef =>
        cases two with
        | mk secondKind secondRef =>
          cases secondRef with
          | here =>
            cases firstKind with
            | reading => exact RecurringComparisonPort first second firstRef
            | signal => exact Empty
            | calibration => exact Empty
            | payload => exact Empty
          | prior secondRef => exact RecurringUsed old ⟨firstKind, firstRef⟩ ⟨secondKind, secondRef⟩

def RecurringUsed.view {context} {values : Values Value context} {past : RecurringFormation values}
    {one two : Occurrence context} (edge : RecurringUsed past one two) : recurringUsedView past one two := by
  cases edge with
  | fromCursor old => exact old
  | fromInstrument old => exact old
  | signal old role ref port => exact port
  | comparison old role ref port => exact port
  | throughSignal role old => exact old
  | throughComparison role old => exact old

structure RecurringRaccord (source target : RecurringCursor) where
  references : ReferenceTransport source.kinds target.kinds
  reads : ∀ {kind} (ref : Ref source.kinds kind), target.read (references.forward ref) = source.read ref
  forwardArrival : ∀ {reading signal}, RecurringArrival source.formation reading signal →
    RecurringArrival target.formation (references.forward reading) (references.forward signal)
  backwardArrival : ∀ {reading signal}, RecurringArrival target.formation reading signal →
    RecurringArrival source.formation (references.backward reading) (references.backward signal)
  forwardUsed : ∀ {one two}, RecurringUsed source.formation one two →
    RecurringUsed target.formation (references.occurrences.forward one) (references.occurrences.forward two)
  backwardUsed : ∀ {one two}, RecurringUsed target.formation one two →
    RecurringUsed source.formation (references.occurrences.backward one) (references.occurrences.backward two)

def RecurringRaccord.identity (source : RecurringCursor) : RecurringRaccord source source :=
  ⟨.identity _, fun _ => rfl, id, id, id, id⟩

def RecurringRaccord.reverse {source target} (raccord : RecurringRaccord source target) :
    RecurringRaccord target source where
  references := raccord.references.reverse
  reads := fun {readKind} ref => by
    have same := raccord.reads (raccord.references.backward ref)
    rw [raccord.references.backwardForward ref] at same
    exact same.symm
  forwardArrival := raccord.backwardArrival
  backwardArrival := raccord.forwardArrival
  forwardUsed := raccord.backwardUsed
  backwardUsed := raccord.forwardUsed

def RecurringPair.rename {source target} (pair : RecurringPair source) (raccord : RecurringRaccord source target) :
    RecurringPair target :=
  ⟨raccord.references.forward pair.first, raccord.references.forward pair.second,
    raccord.references.forward pair.firstSignal, raccord.references.forward pair.secondSignal,
    raccord.forwardArrival pair.firstArrival, raccord.forwardArrival pair.secondArrival,
    fun same => pair.distinct ((raccord.references.forwardBackward pair.first).symm.trans
      ((congrArg raccord.references.backward same).trans (raccord.references.forwardBackward pair.second)))⟩

theorem recurring_renamed_gap {source target} (pair : RecurringPair source) (raccord : RecurringRaccord source target) :
    (pair.rename raccord).gap = pair.gap :=
  (pair.rename raccord).gap_exact.trans
    ((congrArg (fun second => Rational.sub second (target.read (raccord.references.forward pair.first)))
      (raccord.reads pair.second)).trans
      ((congrArg (Rational.sub (source.read pair.second)) (raccord.reads pair.first)).trans pair.gap_exact.symm))

def RecurringAction.rename {source target} (raccord : RecurringRaccord source target) :
    {kind : Kind} → RecurringAction source kind → RecurringAction target kind
  | _, .signal instruction => .signal (instruction.rename raccord.references.forward)
  | _, .compare pair => .compare (pair.rename raccord)

theorem RecurringProduces.output_exact {source} {kind} {action : RecurringAction source kind}
    {output} (role : RecurringProduces source action output) :
    output = (match action with | .signal instruction => instruction.interpret source.values | .compare pair => pair.gap) := by
  cases role with
  | signal localRole => exact localRole.output_exact
  | compared role => cases role; exact RecurringPair.gap_exact _ |>.symm

theorem recurring_paired_outputs_exact {source target} (raccord : RecurringRaccord source target)
    {kind} {action : RecurringAction source kind} (one : RecurringProduction source action)
    (two : RecurringProduction target (action.rename raccord)) : two.determination.1 = one.determination.1 := by
  have first := one.determination.2.output_exact
  have second := two.determination.2.output_exact
  cases action with
  | signal instruction =>
    exact second.trans ((instruction.rename_interpret _ source.values target.values raccord.reads).trans first.symm)
  | compare pair => exact second.trans ((recurring_renamed_gap pair raccord).trans first.symm)

def RecurringComparisonPort.rename {source target} (mapping : {kind : Kind} → Ref source kind → Ref target kind)
    {first second ref : Ref source .reading} (port : RecurringComparisonPort first second ref) :
    RecurringComparisonPort (mapping first) (mapping second) (mapping ref) := by
  cases port with
  | first => exact .first
  | second => exact .second

def RecurringComparisonPort.returned {source target} (mapping : ReferenceTransport source target)
    {first second : Ref source .reading} {ref : Ref target .reading}
    (port : RecurringComparisonPort (mapping.forward first) (mapping.forward second) ref) :
    RecurringComparisonPort first second (mapping.backward ref) := by
  cases port with
  | first => rw [mapping.forwardBackward]; exact .first
  | second => rw [mapping.forwardBackward]; exact .second

def RecurringRaccord.afterSignal {source target} (raccord : RecurringRaccord source target)
    {kind} {instruction : Instruction source.kinds kind}
    (one : RecurringDetermination source (.signal instruction))
    (two : RecurringDetermination target (.signal (instruction.rename raccord.references.forward))) :
    RecurringRaccord (source.extend one) (target.extend two) where
  references := raccord.references.extend kind
  reads := fun ref => by
    cases ref with
    | here =>
      exact recurring_paired_outputs_exact raccord (action := .signal instruction)
        ⟨one, _, rfl⟩ ⟨two, _, rfl⟩
    | prior old => exact raccord.reads old
  forwardArrival := fun {reading signal} arrival => by
    cases one with
    | mk firstOutput firstRole =>
      cases firstRole with
      | signal firstRole =>
        cases two with
        | mk secondOutput secondRole =>
          cases secondRole with
          | signal secondRole =>
            have view := arrival.view
            cases reading with
            | here => cases firstRole; cases secondRole; cases view; exact .received target.formation _
            | prior reading =>
              cases signal with
              | here => exact Empty.elim view
              | prior signal => exact .throughSignal secondRole (raccord.forwardArrival view)
  backwardArrival := fun {reading signal} arrival => by
    cases one with
    | mk firstOutput firstRole =>
      cases firstRole with
      | signal firstRole =>
        cases two with
        | mk secondOutput secondRole =>
          cases secondRole with
          | signal secondRole =>
            have view := arrival.view
            cases reading with
            | here =>
              cases instruction with
              | receive signal =>
                cases firstRole; cases secondRole; cases view
                change RecurringArrival (.signal source.formation (.received signal)) .here
                  (.prior (raccord.references.backward (raccord.references.forward signal)))
                rw [raccord.references.forwardBackward]
                exact .received source.formation signal
            | prior reading =>
              cases signal with
              | here => exact Empty.elim view
              | prior signal => exact .throughSignal firstRole (raccord.backwardArrival view)
  forwardUsed := fun {firstOccurrence secondOccurrence} edge => by
    cases one with
    | mk firstOutput firstRole =>
      cases firstRole with
      | signal firstRole =>
        cases two with
        | mk secondOutput secondRole =>
          cases secondRole with
          | signal secondRole =>
            have view := edge.view
            cases firstOccurrence with | mk firstKind firstRef =>
              cases firstRef with
              | here => exact Empty.elim view
              | prior ref =>
                cases secondOccurrence with | mk secondKind secondRef =>
                  cases secondRef with
                  | here =>
                    exact .signal target.formation secondRole
                      (raccord.references.forward ref) (view.rename raccord.references.forward)
                  | prior ref => exact .throughSignal secondRole (raccord.forwardUsed view)
  backwardUsed := fun {firstOccurrence secondOccurrence} edge => by
    cases one with
    | mk firstOutput firstRole =>
      cases firstRole with
      | signal firstRole =>
        cases two with
        | mk secondOutput secondRole =>
          cases secondRole with
          | signal secondRole =>
            have view := edge.view
            cases firstOccurrence with | mk firstKind firstRef =>
              cases firstRef with
              | here => exact Empty.elim view
              | prior ref =>
                cases secondOccurrence with | mk secondKind secondRef =>
                  cases secondRef with
                  | here =>
                    exact .signal source.formation firstRole
                      (raccord.references.backward ref) (view.returned raccord.references instruction)
                  | prior ref => exact .throughSignal firstRole (raccord.backwardUsed view)

def RecurringRaccord.afterComparison {source target} (raccord : RecurringRaccord source target)
    (pair : RecurringPair source) (one : RecurringDetermination source (.compare pair))
    (two : RecurringDetermination target (.compare (pair.rename raccord))) :
    RecurringRaccord (source.extend one) (target.extend two) where
  references := raccord.references.extend .reading
  reads := fun {readKind} ref => by
    cases ref with
    | here =>
      exact recurring_paired_outputs_exact raccord (action := .compare pair)
        ⟨one, _, rfl⟩ ⟨two, _, rfl⟩
    | prior old => exact raccord.reads old
  forwardArrival := fun {reading signal} arrival => by
    cases one with
    | mk firstOutput firstRole =>
      cases firstRole with
      | compared firstRole =>
        cases two with
        | mk secondOutput secondRole =>
          cases secondRole with
          | compared secondRole =>
            have view := arrival.view
            cases reading with
            | here => exact Empty.elim view
            | prior reading => cases signal with
              | prior signal => exact .throughComparison secondRole (raccord.forwardArrival view)
  backwardArrival := fun {reading signal} arrival => by
    cases one with
    | mk firstOutput firstRole =>
      cases firstRole with
      | compared firstRole =>
        cases two with
        | mk secondOutput secondRole =>
          cases secondRole with
          | compared secondRole =>
            have view := arrival.view
            cases reading with
            | here => exact Empty.elim view
            | prior reading => cases signal with
              | prior signal => exact .throughComparison firstRole (raccord.backwardArrival view)
  forwardUsed := fun {firstOccurrence secondOccurrence} edge => by
    cases one with
    | mk firstOutput firstRole =>
      cases firstRole with
      | compared firstRole =>
        cases two with
        | mk secondOutput secondRole =>
          cases secondRole with
          | compared secondRole =>
            have view := edge.view
            cases firstOccurrence with | mk firstKind firstRef =>
              cases firstRef with
              | here => exact Empty.elim view
              | prior ref =>
                cases secondOccurrence with | mk secondKind secondRef =>
                  cases secondRef with
                  | here =>
                    cases firstKind <;> first
                      | exact .comparison target.formation secondRole _ (view.rename raccord.references.forward)
                      | exact Empty.elim view
                  | prior ref => exact .throughComparison secondRole (raccord.forwardUsed view)
  backwardUsed := fun {firstOccurrence secondOccurrence} edge => by
    cases one with
    | mk firstOutput firstRole =>
      cases firstRole with
      | compared firstRole =>
        cases two with
        | mk secondOutput secondRole =>
          cases secondRole with
          | compared secondRole =>
            have view := edge.view
            cases firstOccurrence with | mk firstKind firstRef =>
              cases firstRef with
              | here => exact Empty.elim view
              | prior ref =>
                cases secondOccurrence with | mk secondKind secondRef =>
                  cases secondRef with
                  | here =>
                    cases firstKind <;> first
                      | exact .comparison source.formation firstRole _ (view.returned raccord.references)
                      | exact Empty.elim view
                  | prior ref => exact .throughComparison firstRole (raccord.backwardUsed view)

def RecurringRaccord.afterProduction {source target} (raccord : RecurringRaccord source target)
    {kind} {action : RecurringAction source kind} (one : RecurringProduction source action)
    (two : RecurringProduction target (action.rename raccord)) : RecurringRaccord one.successor two.successor := by
  cases one with
  | mk first firstSuccessor firstExact =>
    cases firstExact
    cases two with
    | mk second secondSuccessor secondExact =>
      cases secondExact
      cases action with
      | signal instruction => exact raccord.afterSignal first second
      | compare pair => exact raccord.afterComparison pair first second

theorem recurring_signal_references {source target} (raccord : RecurringRaccord source target)
    {kind} {instruction : Instruction source.kinds kind}
    (one : RecurringDetermination source (.signal instruction))
    (two : RecurringDetermination target (.signal (instruction.rename raccord.references.forward))) :
    (raccord.afterSignal one two).references = raccord.references.extend kind := rfl

theorem recurring_comparison_references {source target} (raccord : RecurringRaccord source target)
    (pair : RecurringPair source) (one : RecurringDetermination source (.compare pair))
    (two : RecurringDetermination target (.compare (pair.rename raccord))) :
    (raccord.afterComparison pair one two).references = raccord.references.extend .reading := rfl

structure AddressedRecurringRaccord (source target : RecurringCursor) where
  constitution : RecurringRaccord source target
  addresses : AddressTransport constitution.references

def AddressedRecurringRaccord.reverse {source target} (raccord : AddressedRecurringRaccord source target) :
    AddressedRecurringRaccord target source := ⟨raccord.constitution.reverse, raccord.addresses.reverse⟩

def AddressedRecurringRaccord.afterProduction {source target} (raccord : AddressedRecurringRaccord source target)
    {kind} {action : RecurringAction source kind} (one : RecurringProduction source action)
    (two : RecurringProduction target (action.rename raccord.constitution)) :
    AddressedRecurringRaccord one.successor two.successor := by
  cases one with
  | mk first firstSuccessor firstExact =>
    cases firstExact
    cases two with
    | mk second secondSuccessor secondExact =>
      cases secondExact
      cases action with
      | signal instruction =>
        exact ⟨raccord.constitution.afterSignal first second, raccord.addresses.extend _⟩
      | compare pair =>
        exact ⟨raccord.constitution.afterComparison pair first second, raccord.addresses.extend _⟩

def AddressedRecurringRaccord.fromCursors {source target : Cursor} (raccord : AddressedRaccord source target)
    (forward : ∀ {reading signal}, Arrived source.formation reading signal →
      Arrived target.formation (raccord.constitution.reading.references.forward reading)
        (raccord.constitution.reading.references.forward signal))
    (backward : ∀ {reading signal}, Arrived target.formation reading signal →
      Arrived source.formation (raccord.constitution.reading.references.backward reading)
        (raccord.constitution.reading.references.backward signal)) :
    AddressedRecurringRaccord (.fromCursor source) (.fromCursor target) := by
  refine ⟨⟨raccord.constitution.reading.references, raccord.constitution.reading.reads, ?_, ?_, ?_, ?_⟩,
    raccord.addresses⟩
  · intro reading signal arrival
    exact .fromCursor (forward arrival.view)
  · intro reading signal arrival
    exact .fromCursor (backward arrival.view)
  · intro one two edge
    exact .fromCursor (raccord.constitution.forwardUsed edge.view)
  · intro one two edge
    exact .fromCursor (raccord.constitution.backwardUsed edge.view)

/-- The exchanged receptions keep their actual received signal. The second
instruction uses only old ports, so it cannot receive the first fresh output. -/
def independentPairArrival {source firstKind secondKind}
    {first : Instruction source.kinds firstKind} {second : Instruction source.kinds secondKind}
    (original : IndependentPairProduction source first second)
    (reversed : IndependentPairProduction source second first)
    {reading : Ref original.cursor.kinds .reading} {signal : Ref original.cursor.kinds .signal}
    (arrival : Arrived original.cursor.formation reading signal) :
    Arrived reversed.cursor.formation
      ((independentPairRaccord original reversed).references.forward reading)
      ((independentPairRaccord original reversed).references.forward signal) := by
  have outer := arrival.view
  cases reading with
  | here =>
    cases second with
    | receive signal =>
      have received := Arrived.receptionSignal _ original.secondDetermination.2 arrival
      cases received
      exact .inherited reversed.secondDetermination.2 (Arrived.ofReception source.formation reversed.firstDetermination.2)
  | prior reading =>
    cases signal with
    | here => exact Empty.elim outer
    | prior signal =>
      have inner := outer.view
      cases reading with
      | here =>
        cases first with
        | receive received =>
          have received := Arrived.receptionSignal _ original.firstDetermination.2 outer
          cases received
          exact Arrived.ofReception (source.extend reversed.firstDetermination).formation reversed.secondDetermination.2
      | prior reading =>
        cases signal with
        | here => exact Empty.elim inner
        | prior signal => exact .inherited reversed.secondDetermination.2 (.inherited reversed.firstDetermination.2 inner)

def independentRecurringPair {source firstKind secondKind}
    {first : Instruction source.kinds firstKind} {second : Instruction source.kinds secondKind}
    (original : IndependentPairProduction source first second)
    (reversed : IndependentPairProduction source second first) :
    AddressedRecurringRaccord (.fromCursor original.cursor) (.fromCursor reversed.cursor) :=
  .fromCursors (independentPairAddressed original reversed)
    (independentPairArrival original reversed) (independentPairArrival reversed original)

theorem recurring_raccord_arrival_iff {source target} (raccord : RecurringRaccord source target)
    (reading : Ref source.kinds .reading) (signal : Ref source.kinds .signal) :
    Nonempty (RecurringArrival target.formation (raccord.references.forward reading)
      (raccord.references.forward signal)) ↔ Nonempty (RecurringArrival source.formation reading signal) := by
  constructor
  · intro ⟨arrival⟩
    have returned := raccord.backwardArrival arrival
    rw [raccord.references.forwardBackward reading, raccord.references.forwardBackward signal] at returned
    exact ⟨returned⟩
  · intro ⟨arrival⟩
    exact ⟨raccord.forwardArrival arrival⟩

theorem recurring_raccord_used_iff {source target} (raccord : RecurringRaccord source target)
    (one two : Occurrence source.kinds) :
    Nonempty (RecurringUsed target.formation (raccord.references.occurrences.forward one)
      (raccord.references.occurrences.forward two)) ↔ Nonempty (RecurringUsed source.formation one two) := by
  constructor
  · intro ⟨edge⟩
    have returned := raccord.backwardUsed edge
    rw [raccord.references.occurrences.forwardBackward one, raccord.references.occurrences.forwardBackward two] at returned
    exact ⟨returned⟩
  · intro ⟨edge⟩
    exact ⟨raccord.forwardUsed edge⟩

end RelationalPerimeter.Relativity.Production
/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Relativity.Production.ReceivedSignal
#print axioms RelationalPerimeter.Relativity.Production.arrivedView
#print axioms RelationalPerimeter.Relativity.Production.Arrived.view
#print axioms RelationalPerimeter.Relativity.Production.Arrived.ofReception
#print axioms RelationalPerimeter.Relativity.Production.Arrived.receptionSignal
#print axioms RelationalPerimeter.Relativity.Production.recurringArrivalView
#print axioms RelationalPerimeter.Relativity.Production.RecurringArrival.view
#print axioms RelationalPerimeter.Relativity.Production.recurringUsedView
#print axioms RelationalPerimeter.Relativity.Production.RecurringUsed.view
#print axioms RelationalPerimeter.Relativity.Production.RecurringRaccord
#print axioms RelationalPerimeter.Relativity.Production.RecurringRaccord.identity
#print axioms RelationalPerimeter.Relativity.Production.RecurringRaccord.reverse
#print axioms RelationalPerimeter.Relativity.Production.RecurringPair.rename
#print axioms RelationalPerimeter.Relativity.Production.recurring_renamed_gap
#print axioms RelationalPerimeter.Relativity.Production.RecurringAction.rename
#print axioms RelationalPerimeter.Relativity.Production.RecurringProduces.output_exact
#print axioms RelationalPerimeter.Relativity.Production.recurring_paired_outputs_exact
#print axioms RelationalPerimeter.Relativity.Production.RecurringComparisonPort.rename
#print axioms RelationalPerimeter.Relativity.Production.RecurringComparisonPort.returned
#print axioms RelationalPerimeter.Relativity.Production.RecurringRaccord.afterSignal
#print axioms RelationalPerimeter.Relativity.Production.RecurringRaccord.afterComparison
#print axioms RelationalPerimeter.Relativity.Production.RecurringRaccord.afterProduction
#print axioms RelationalPerimeter.Relativity.Production.recurring_signal_references
#print axioms RelationalPerimeter.Relativity.Production.recurring_comparison_references
#print axioms RelationalPerimeter.Relativity.Production.AddressedRecurringRaccord
#print axioms RelationalPerimeter.Relativity.Production.AddressedRecurringRaccord.reverse
#print axioms RelationalPerimeter.Relativity.Production.AddressedRecurringRaccord.afterProduction
#print axioms RelationalPerimeter.Relativity.Production.AddressedRecurringRaccord.fromCursors
#print axioms RelationalPerimeter.Relativity.Production.independentPairArrival
#print axioms RelationalPerimeter.Relativity.Production.independentRecurringPair
#print axioms RelationalPerimeter.Relativity.Production.recurring_raccord_arrival_iff
#print axioms RelationalPerimeter.Relativity.Production.recurring_raccord_used_iff
/- AXIOM_AUDIT_END -/
