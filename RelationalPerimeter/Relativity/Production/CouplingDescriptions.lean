import RelationalPerimeter.Relativity.Production.ConstitutedEncounters
import RelationalPerimeter.Relativity.Production.GroupedRecurringContinuation
import RelationalPerimeter.Relativity.Production.InteractionDescriptionAgreement

/-!
# Exact descriptions of the occupied coupling state

The addressed resource raccord alone does not determine port availability.
This raccord also carries the actual instrument and its occupied arrivals.
Both states already have positive coupling formations. No availability is
inferred from equal numerical readings or from archived reception alone.
The extension below transports a cached production and its role, not another
execution. This is the declared holding model, not a propagation geometry.
-/
set_option genInjectivity false
namespace RelationalPerimeter.Relativity.Production.Encounter
open ConstitutiveSearch.Resources

theorem arrival_witness_unique {context} {values : Values Value context}
    {past : RecurringFormation values} {reading signal}
    (one two : RecurringArrival past reading signal) : one = two := by
  have same := Option.some.inj (one.find_exact.symm.trans two.find_exact)
  have returned : HEq one two := (PSigma.mk.inj same).2
  exact eq_of_heq returned

theorem pair_references_determine {source} (one two : RecurringPair source)
    (first : one.first = two.first) (second : one.second = two.second)
    (firstSignal : one.firstSignal = two.firstSignal) (secondSignal : one.secondSignal = two.secondSignal) :
    one = two := by
  cases one with
  | mk a b c d arrivalA arrivalB different =>
    cases two with
    | mk e f g h arrivalE arrivalF otherDifferent =>
      cases first; cases second; cases firstSignal; cases secondSignal
      cases arrival_witness_unique arrivalA arrivalE
      cases arrival_witness_unique arrivalB arrivalF
      rfl

def Held.rename {source target} (held : Held source) (raccord : RecurringRaccord source target) : Held target :=
  ⟨raccord.references.forward held.reading, raccord.references.forward held.signal,
    raccord.forwardArrival held.arrival⟩

theorem held_references_determine {source} (one two : Held source)
    (reading : one.reading = two.reading) (signal : one.signal = two.signal) : one = two := by
  cases one with
  | mk a b arrival =>
    cases two with
    | mk c d other =>
      cases reading; cases signal
      cases arrival_witness_unique arrival other
      rfl

def Phase.rename {source target} (phase : Phase source) (raccord : RecurringRaccord source target) : Phase target :=
  match phase with
  | .empty => .empty
  | .left held => .left (held.rename raccord)
  | .right held => .right (held.rename raccord)
  | .ready pair => .ready (pair.rename raccord)

theorem phase_rename_returns {source target} (phase : Phase source) (raccord : RecurringRaccord source target) :
    (phase.rename raccord).rename raccord.reverse = phase := by
  cases phase with
  | empty => rfl
  | left held => exact congrArg Phase.left (held_references_determine _ _
      (raccord.references.forwardBackward _) (raccord.references.forwardBackward _))
  | right held => exact congrArg Phase.right (held_references_determine _ _
      (raccord.references.forwardBackward _) (raccord.references.forwardBackward _))
  | ready pair => exact congrArg Phase.ready (pair_references_determine _ _
      (raccord.references.forwardBackward _) (raccord.references.forwardBackward _)
      (raccord.references.forwardBackward _) (raccord.references.forwardBackward _))

structure StateRaccord (source target : State) where
  resources : AddressedRecurringRaccord source.cursor target.cursor
  phaseExact : target.phase = source.phase.rename resources.constitution
  instrumentExact : target.formation.instrument = resources.constitution.references.forward source.formation.instrument

def StateRaccord.identity (source : State) : StateRaccord source source := by
  refine ⟨.identity source.cursor, ?_, rfl⟩
  cases source.phase with
  | empty => rfl
  | left held => exact congrArg Phase.left (held_references_determine _ _ rfl rfl)
  | right held => exact congrArg Phase.right (held_references_determine _ _ rfl rfl)
  | ready pair => exact congrArg Phase.ready (pair_references_determine _ _ rfl rfl rfl rfl)

def StateRaccord.reverse {source target} (raccord : StateRaccord source target) : StateRaccord target source := by
  refine ⟨raccord.resources.reverse, ?_, ?_⟩
  · rw [raccord.phaseExact]
    exact (phase_rename_returns source.phase raccord.resources.constitution).symm
  · exact (raccord.resources.constitution.references.forwardBackward _).symm.trans
      (congrArg raccord.resources.constitution.references.backward raccord.instrumentExact).symm

def StateRaccord.attached {source target : Cursor} (instrument : Ref source.kinds .calibration)
    (raccord : AddressedRecurringRaccord (.fromCursor source) (.fromCursor target)) :
    StateRaccord (attach source instrument) (attach target (raccord.constitution.references.forward instrument)) :=
  ⟨raccord, rfl, rfl⟩

theorem phase_rename_compose {source middle target} (phase : Phase source)
    (one : AddressedRecurringRaccord source middle) (two : AddressedRecurringRaccord middle target) :
    (phase.rename one.constitution).rename two.constitution = phase.rename (one.compose two).constitution := by
  cases phase with
  | empty => rfl
  | left held => exact congrArg Phase.left (held_references_determine _ _ rfl rfl)
  | right held => exact congrArg Phase.right (held_references_determine _ _ rfl rfl)
  | ready pair => exact congrArg Phase.ready (pair_references_determine _ _ rfl rfl rfl rfl)

def StateRaccord.compose {source middle target} (one : StateRaccord source middle)
    (two : StateRaccord middle target) : StateRaccord source target := by
  refine ⟨one.resources.compose two.resources, ?_, ?_⟩
  · rw [two.phaseExact, one.phaseExact]
    exact phase_rename_compose source.phase one.resources two.resources
  · rw [two.instrumentExact, one.instrumentExact]; rfl

def Vacant.rename {source target} {one : Phase source} {two : Phase target}
    (raccord : RecurringRaccord source target) (same : two = one.rename raccord)
    {port} (vacant : Vacant one port) : Vacant two port := by
  cases same
  cases vacant with
  | empty port => exact .empty port
  | right => exact .right
  | left => exact .left

def EncounterAdmission.rename {source target} (raccord : StateRaccord source target)
    (admitted : EncounterAdmission source) : EncounterAdmission target :=
  ⟨admitted.pair.rename raccord.resources.constitution, by rw [raccord.phaseExact, admitted.ready]; rfl⟩

theorem production_old_reference_square {source target} (raccord : AddressedRecurringRaccord source target)
    {kind} {action : RecurringAction source kind} (one : RecurringProduction source action)
    (two : RecurringProduction target (action.rename raccord.constitution))
    {oldKind} (ref : Ref source.kinds oldKind) :
    (raccord.afterProduction one two).constitution.references.forward
        ((recurringHistoryTransport (recurringProductionHistory one)).references ref) =
      (recurringHistoryTransport (recurringProductionHistory two)).references
        (raccord.constitution.references.forward ref) := by
  cases one with | mk first firstSuccessor firstExact =>
    cases firstExact
    cases two with | mk second secondSuccessor secondExact =>
      cases secondExact
      cases action with
      | signal instruction =>
        cases first with
        | mk output role =>
          cases role with
          | signal localRole =>
            cases second with
            | mk otherOutput otherRole => cases otherRole; rfl
      | compare pair =>
        cases first with
        | mk output role =>
          cases role with
          | compared computation =>
            cases second with
            | mk otherOutput otherRole => cases otherRole; rfl

theorem phase_extension_square {source target} (phase : Phase source)
    (raccord : AddressedRecurringRaccord source target) {kind} {action : RecurringAction source kind}
    (one : RecurringProduction source action) (two : RecurringProduction target (action.rename raccord.constitution)) :
    (phase.rename raccord.constitution).transport (recurringProductionHistory two) =
      (phase.transport (recurringProductionHistory one)).rename (raccord.afterProduction one two).constitution := by
  cases phase with
  | empty => rfl
  | left held => exact congrArg Phase.left (held_references_determine _ _
      (production_old_reference_square raccord one two held.reading).symm
      (production_old_reference_square raccord one two held.signal).symm)
  | right held => exact congrArg Phase.right (held_references_determine _ _
      (production_old_reference_square raccord one two held.reading).symm
      (production_old_reference_square raccord one two held.signal).symm)
  | ready pair => exact congrArg Phase.ready (pair_references_determine _ _
      (production_old_reference_square raccord one two pair.first).symm
      (production_old_reference_square raccord one two pair.second).symm
      (production_old_reference_square raccord one two pair.firstSignal).symm
      (production_old_reference_square raccord one two pair.secondSignal).symm)

theorem delivered_phase_square {source target} {onePhase : Phase source} {twoPhase : Phase target}
    (raccord : AddressedRecurringRaccord source target) (same : twoPhase = onePhase.rename raccord.constitution)
    {port signal} (oneVacant : Vacant onePhase port) (twoVacant : Vacant twoPhase port)
    (one : RecurringProduction source (.signal (.receive signal)))
    (two : RecurringProduction target (.signal (.receive (raccord.constitution.references.forward signal)))) :
    deliveredPhase twoVacant two =
      (deliveredPhase oneVacant one).rename (raccord.afterProduction one two).constitution := by
  cases same
  cases oneVacant with
  | empty port =>
    cases twoVacant
    cases one with | mk first firstSuccessor firstExact =>
      cases firstExact
      cases two with | mk second secondSuccessor secondExact =>
        cases secondExact
        cases port <;> first
          | exact congrArg Phase.left (held_references_determine _ _ rfl rfl)
          | exact congrArg Phase.right (held_references_determine _ _ rfl rfl)
  | right =>
    cases twoVacant
    cases one with | mk first firstSuccessor firstExact =>
      cases firstExact
      cases two with | mk second secondSuccessor secondExact =>
        cases secondExact
        cases first with
        | mk output role =>
          cases role with
          | signal localRole =>
            cases localRole
            cases second with
            | mk output role =>
              cases role with
              | signal localRole =>
                cases localRole
                exact congrArg Phase.ready (pair_references_determine _ _ rfl rfl rfl rfl)
  | left =>
    cases twoVacant
    cases one with | mk first firstSuccessor firstExact =>
      cases firstExact
      cases two with | mk second secondSuccessor secondExact =>
        cases secondExact
        cases first with
        | mk output role =>
          cases role with
          | signal localRole =>
            cases localRole
            cases second with
            | mk output role =>
              cases role with
              | signal localRole =>
                cases localRole
                exact congrArg Phase.ready (pair_references_determine _ _ rfl rfl rfl rfl)

def StateRaccord.afterSignal {source target} (raccord : StateRaccord source target)
    {kind} {instruction : Instruction source.cursor.kinds kind} (one : SignalProduction source instruction)
    (two : SignalProduction target (instruction.rename raccord.resources.constitution.references.forward)) :
    StateRaccord one.next two.next := by
  refine ⟨raccord.resources.afterProduction one.head two.head, ?_, ?_⟩
  · change (target.phase.transport _ ) = (source.phase.transport _).rename _
    rw [raccord.phaseExact]
    exact phase_extension_square source.phase raccord.resources one.head two.head
  · change (recurringHistoryTransport (recurringProductionHistory two.head)).references target.formation.instrument = _
    rw [raccord.instrumentExact]
    exact (production_old_reference_square raccord.resources one.head two.head source.formation.instrument).symm

def StateRaccord.afterDelivery {source target} (raccord : StateRaccord source target)
    {port signal vacant} (one : DeliveryProduction source port signal vacant)
    (two : DeliveryProduction target port (raccord.resources.constitution.references.forward signal)
      (vacant.rename raccord.resources.constitution raccord.phaseExact)) : StateRaccord one.next two.next := by
  refine ⟨raccord.resources.afterProduction one.head two.head, ?_, ?_⟩
  · exact delivered_phase_square raccord.resources raccord.phaseExact _ _ one.head two.head
  · change (recurringHistoryTransport (recurringProductionHistory two.head)).references target.formation.instrument = _
    rw [raccord.instrumentExact]
    exact (production_old_reference_square raccord.resources one.head two.head source.formation.instrument).symm

theorem instrument_phase_cast {cursor} {one two : Phase cursor}
    (formation : CouplingFormation cursor one) (same : one = two) :
    (same ▸ formation).instrument = formation.instrument := by cases same; rfl

def StateRaccord.afterEncounter {source target} (raccord : StateRaccord source target)
    {admitted} (one : EncounterProduction source admitted)
    (two : EncounterProduction target (admitted.rename raccord)) : StateRaccord one.next two.next := by
  refine ⟨raccord.resources.afterProduction one.head two.head, rfl, ?_⟩
  dsimp only [EncounterProduction.next, Encounter.afterEncounter, CouplingFormation.instrument]
  with_reducible
    rw [instrument_phase_cast, instrument_phase_cast, raccord.instrumentExact]
  with_unfolding_all
    exact (production_old_reference_square raccord.resources one.head two.head source.formation.instrument).symm

end RelationalPerimeter.Relativity.Production.Encounter
/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Relativity.Production.Encounter.arrival_witness_unique
#print axioms RelationalPerimeter.Relativity.Production.Encounter.pair_references_determine
#print axioms RelationalPerimeter.Relativity.Production.Encounter.Held.rename
#print axioms RelationalPerimeter.Relativity.Production.Encounter.phase_rename_returns
#print axioms RelationalPerimeter.Relativity.Production.Encounter.StateRaccord.identity
#print axioms RelationalPerimeter.Relativity.Production.Encounter.StateRaccord.reverse
#print axioms RelationalPerimeter.Relativity.Production.Encounter.StateRaccord.attached
#print axioms RelationalPerimeter.Relativity.Production.Encounter.StateRaccord.compose
#print axioms RelationalPerimeter.Relativity.Production.Encounter.Vacant.rename
#print axioms RelationalPerimeter.Relativity.Production.Encounter.EncounterAdmission.rename
#print axioms RelationalPerimeter.Relativity.Production.Encounter.production_old_reference_square
#print axioms RelationalPerimeter.Relativity.Production.Encounter.phase_extension_square
#print axioms RelationalPerimeter.Relativity.Production.Encounter.delivered_phase_square
#print axioms RelationalPerimeter.Relativity.Production.Encounter.StateRaccord.afterSignal
#print axioms RelationalPerimeter.Relativity.Production.Encounter.StateRaccord.afterDelivery
#print axioms RelationalPerimeter.Relativity.Production.Encounter.instrument_phase_cast
#print axioms RelationalPerimeter.Relativity.Production.Encounter.StateRaccord.afterEncounter
/- AXIOM_AUDIT_END -/
