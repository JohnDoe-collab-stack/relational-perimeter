import RelationalPerimeter.Relativity.Production.ConstitutedDescriptions

/-!
# Participants attached to one actually produced interaction

The anchor is the fresh occurrence of a cached arrival comparison, not its
numerical result or a supplied position. Reception and used-port witnesses
are transported together with the actual references. Attached path records
remain readable under the unchanged recurring contract.

This constructs constitutive participation, not spacetime colocation. The
instrumental law supplies no propagation or physical meeting admission.
No location agreement, memory erasure or continuum is inferred from an
anchor shared by participants.
-/
set_option genInjectivity false
namespace RelationalPerimeter.Relativity.Production
open ConstitutiveSearch.Resources
open ConstitutiveSearch.ContinuationSignatures

def comparisonAnchor {source : RecurringCursor} {pair : RecurringPair source}
    (head : RecurringProduction source (.compare pair)) : Ref head.successor.kinds .reading :=
  head.successorExact.symm ▸ Ref.here

def comparisonExtension {source : RecurringCursor} {pair : RecurringPair source}
    (head : RecurringProduction source (.compare pair)) :
    Support.Extension source.support head.successor.support :=
  recurringHistoryTransport (recurringProductionHistory head)

theorem comparison_anchor_output {source : RecurringCursor} {pair : RecurringPair source}
    (head : RecurringProduction source (.compare pair)) :
    head.successor.read (comparisonAnchor head) = head.determination.1 := by
  cases head with | mk determination successor exactSuccessor => cases exactSuccessor; rfl

theorem comparison_output_uses_arrivals {source : RecurringCursor} {pair : RecurringPair source}
    (head : RecurringProduction source (.compare pair)) : head.determination.1 = pair.gap :=
  head.determination.2.output_exact

theorem cached_comparison_event_exact {source : RecurringCursor} {pair : RecurringPair source}
    (head : RecurringProduction source (.compare pair)) :
    RecurringEvent.compared head.determination.1 =
      recurringContract.event source (.compare pair.first.position pair.second.position) :=
  (congrArg RecurringEvent.compared ((comparison_output_uses_arrivals head).trans pair.gap_exact)).trans
    ((recurring_pair_response_output pair).symm.trans (recurring_request_event_exact source _))

def comparisonPortUsed {source : RecurringCursor} {pair : RecurringPair source}
    (head : RecurringProduction source (.compare pair)) {reading : Ref source.kinds .reading}
    (port : RecurringComparisonPort pair.first pair.second reading) :
    RecurringUsed head.successor.formation
      ⟨.reading, (comparisonExtension head).references reading⟩ ⟨.reading, comparisonAnchor head⟩ := by
  cases head with
  | mk determination successor exactSuccessor =>
    cases exactSuccessor
    cases determination with
    | mk output role => cases role with | compared comparedRole => exact .comparison source.formation comparedRole reading port

theorem comparison_anchor_fresh {source : RecurringCursor} {pair : RecurringPair source}
    (head : RecurringProduction source (.compare pair)) (old : Ref source.kinds .reading) :
    comparisonAnchor head ≠ (comparisonExtension head).references old := by
  cases head with
  | mk determination successor exactSuccessor =>
    cases exactSuccessor
    cases determination with
    | mk output role =>
      cases role with
      | compared comparedRole =>
        intro same
        exact fresh_position_distinct old (congrArg Ref.position same)

/-- Both the reception and its participating port belong to this exact head.
The path carries that head's real successor into the current presentation. -/
structure InteractionAttachment {source : RecurringCursor} {pair : RecurringPair source}
    (head : RecurringProduction source (.compare pair)) (current : RecurringCursor) where
  path : DescriptionPath head.successor current
  reading : Ref source.kinds .reading
  signal : Ref source.kinds .signal
  arrival : RecurringArrival source.formation reading signal
  port : RecurringComparisonPort pair.first pair.second reading

def InteractionAttachment.first {source : RecurringCursor} {pair : RecurringPair source}
    (head : RecurringProduction source (.compare pair)) {current}
    (path : DescriptionPath head.successor current) : InteractionAttachment head current :=
  ⟨path, pair.first, pair.firstSignal, pair.firstArrival, .first⟩

def InteractionAttachment.second {source : RecurringCursor} {pair : RecurringPair source}
    (head : RecurringProduction source (.compare pair)) {current}
    (path : DescriptionPath head.successor current) : InteractionAttachment head current :=
  ⟨path, pair.second, pair.secondSignal, pair.secondArrival, .second⟩

def InteractionAttachment.anchor {source pair head current}
    (attached : @InteractionAttachment source pair head current) : Ref current.kinds .reading :=
  attached.path.reference (comparisonAnchor head)

def InteractionAttachment.readingReference {source pair head current}
    (attached : @InteractionAttachment source pair head current) : Ref current.kinds .reading :=
  attached.path.reference ((comparisonExtension head).references attached.reading)

def InteractionAttachment.signalReference {source pair head current}
    (attached : @InteractionAttachment source pair head current) : Ref current.kinds .signal :=
  attached.path.reference ((comparisonExtension head).references attached.signal)

def InteractionAttachment.effects {source pair head current}
    (attached : @InteractionAttachment source pair head current) : SignalRecord :=
  current.read attached.signalReference

def InteractionAttachment.transportedArrival {source pair head current}
    (attached : @InteractionAttachment source pair head current) :
    RecurringArrival current.formation attached.readingReference attached.signalReference :=
  attached.path.arrival (recurringHistoryArrival (recurringProductionHistory head) attached.arrival)

def InteractionAttachment.usedPort {source pair head current}
    (attached : @InteractionAttachment source pair head current) :
    RecurringUsed current.formation ⟨.reading, attached.readingReference⟩ ⟨.reading, attached.anchor⟩ :=
  attached.path.used (comparisonPortUsed head attached.port)

theorem attached_effects_exact {source pair head current}
    (attached : @InteractionAttachment source pair head current) :
    attached.effects = source.read attached.signal :=
  (attached.path.reads _).trans ((comparisonExtension head).reads _)

theorem attached_reading_exact {source pair head current}
    (attached : @InteractionAttachment source pair head current) :
    current.read attached.readingReference = source.read attached.reading :=
  (attached.path.reads _).trans ((comparisonExtension head).reads _)

theorem attached_anchor_output {source pair head current}
    (attached : @InteractionAttachment source pair head current) :
    current.read attached.anchor = head.determination.1 :=
  (attached.path.reads _).trans (comparison_anchor_output head)

theorem participants_share_anchor {source : RecurringCursor} {pair : RecurringPair source}
    (head : RecurringProduction source (.compare pair)) {current}
    (path : DescriptionPath head.successor current) :
    (InteractionAttachment.first head path).anchor = (InteractionAttachment.second head path).anchor := rfl

theorem participants_remain_distinct {source : RecurringCursor} {pair : RecurringPair source}
    (head : RecurringProduction source (.compare pair)) {current}
    (path : DescriptionPath head.successor current) :
    (InteractionAttachment.first head path).readingReference ≠
      (InteractionAttachment.second head path).readingReference := fun same =>
  pair.distinct ((comparisonExtension head).injective _ _ (path.injective _ _ same))

theorem attached_signal_distinction {source : RecurringCursor} {pair : RecurringPair source}
    (head : RecurringProduction source (.compare pair)) {current}
    (path : DescriptionPath head.successor current) (distinct : pair.firstSignal ≠ pair.secondSignal) :
    (InteractionAttachment.first head path).signalReference ≠
      (InteractionAttachment.second head path).signalReference := fun same =>
  distinct ((comparisonExtension head).injective _ _ (path.injective _ _ same))

theorem attached_anchor_not_arrival {source pair head current}
    (attached : @InteractionAttachment source pair head current) :
    attached.anchor ≠ attached.readingReference := fun same =>
  comparison_anchor_fresh head attached.reading (attached.path.injective _ _ same)

def InteractionAttachment.prolong {source pair head current target}
    (attached : @InteractionAttachment source pair head current)
    (history : RecurringHistory current target) : InteractionAttachment head target :=
  { attached with path := attached.path.prolong history }

def InteractionAttachment.reexpress {source pair head current target}
    (attached : @InteractionAttachment source pair head current)
    (raccord : AddressedRecurringRaccord current target) : InteractionAttachment head target :=
  { attached with path := attached.path.reexpressed raccord }

theorem attached_prolong_anchor {source pair head current target}
    (attached : @InteractionAttachment source pair head current) (history : RecurringHistory current target) :
    (attached.prolong history).anchor = (recurringHistoryTransport history).references attached.anchor :=
  attached.path.prolong_reference history _

theorem attached_prolong_effects {source pair head current target}
    (attached : @InteractionAttachment source pair head current) (history : RecurringHistory current target) :
    (attached.prolong history).effects = attached.effects :=
  (attached_effects_exact _).trans (attached_effects_exact attached).symm

theorem attached_reexpress_effects {source pair head current target}
    (attached : @InteractionAttachment source pair head current) (raccord : AddressedRecurringRaccord current target) :
    (attached.reexpress raccord).effects = attached.effects :=
  (attached_effects_exact _).trans (attached_effects_exact attached).symm

theorem attached_reexpress_return_anchor {source pair head current target}
    (attached : @InteractionAttachment source pair head current) (raccord : AddressedRecurringRaccord current target) :
    ((attached.reexpress raccord).reexpress raccord.reverse).anchor = attached.anchor :=
  description_round_trip_reference attached.path raccord _

theorem attached_effects_separate_inspections {source pair head current}
    (one two : @InteractionAttachment source pair head current)
    (different : one.effects ≠ two.effects) :
    recurringContract.outcome current [.local (.inspect .signal one.signalReference.position)] ≠
      recurringContract.outcome current [.local (.inspect .signal two.signalReference.position)] := by
  intro same
  have observed := congrArg firstRecurringInspection same
  dsimp only [FutureContract.outcome, recurringContract] at observed
  rw [recurring_inspection_exact current one.signalReference,
    recurring_inspection_exact current two.signalReference] at observed
  have record := Option.some.inj observed
  exact different (LocalReadout.noConfusion record (fun same => same))

structure AttachedComparison (source : RecurringCursor) (pair : RecurringPair source) where
  head : RecurringProduction source (.compare pair)
  continuation : RecurringRequestedExecution head.successor

/-- A single head is bound before its suffix; the suffix receives its actual
successor. Descriptions then consume the cached continuation, never rerun it. -/
def runAttachedComparison (source : RecurringCursor) (pair : RecurringPair source)
    (requests : List RecurringRequest) : AttachedComparison source pair :=
  let head := performRecurring source (.compare pair)
  let continuation := runRecurringRequests head.successor requests
  ⟨head, continuation⟩

def AttachedComparison.first {source pair} (run : AttachedComparison source pair) :
    InteractionAttachment run.head run.continuation.cursor :=
  InteractionAttachment.first run.head (DescriptionPath.root.prolong run.continuation.history)

def AttachedComparison.second {source pair} (run : AttachedComparison source pair) :
    InteractionAttachment run.head run.continuation.cursor :=
  InteractionAttachment.second run.head (DescriptionPath.root.prolong run.continuation.history)

theorem attached_head_independent (source : RecurringCursor) (pair : RecurringPair source)
    (one two : List RecurringRequest) :
    (runAttachedComparison source pair one).head = (runAttachedComparison source pair two).head := rfl

theorem attached_continuation_exact (source : RecurringCursor) (pair : RecurringPair source)
    (requests : List RecurringRequest) :
    (runAttachedComparison source pair requests).continuation.report =
      recurringContract.outcome (runAttachedComparison source pair requests).head.successor requests :=
  recurring_all_futures_exact ..

end RelationalPerimeter.Relativity.Production
/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Relativity.Production.comparisonAnchor
#print axioms RelationalPerimeter.Relativity.Production.comparisonExtension
#print axioms RelationalPerimeter.Relativity.Production.comparison_anchor_output
#print axioms RelationalPerimeter.Relativity.Production.comparison_output_uses_arrivals
#print axioms RelationalPerimeter.Relativity.Production.cached_comparison_event_exact
#print axioms RelationalPerimeter.Relativity.Production.comparisonPortUsed
#print axioms RelationalPerimeter.Relativity.Production.comparison_anchor_fresh
#print axioms RelationalPerimeter.Relativity.Production.InteractionAttachment
#print axioms RelationalPerimeter.Relativity.Production.InteractionAttachment.first
#print axioms RelationalPerimeter.Relativity.Production.InteractionAttachment.second
#print axioms RelationalPerimeter.Relativity.Production.InteractionAttachment.anchor
#print axioms RelationalPerimeter.Relativity.Production.InteractionAttachment.readingReference
#print axioms RelationalPerimeter.Relativity.Production.InteractionAttachment.signalReference
#print axioms RelationalPerimeter.Relativity.Production.InteractionAttachment.effects
#print axioms RelationalPerimeter.Relativity.Production.InteractionAttachment.transportedArrival
#print axioms RelationalPerimeter.Relativity.Production.InteractionAttachment.usedPort
#print axioms RelationalPerimeter.Relativity.Production.attached_effects_exact
#print axioms RelationalPerimeter.Relativity.Production.attached_reading_exact
#print axioms RelationalPerimeter.Relativity.Production.attached_anchor_output
#print axioms RelationalPerimeter.Relativity.Production.participants_share_anchor
#print axioms RelationalPerimeter.Relativity.Production.participants_remain_distinct
#print axioms RelationalPerimeter.Relativity.Production.attached_signal_distinction
#print axioms RelationalPerimeter.Relativity.Production.attached_anchor_not_arrival
#print axioms RelationalPerimeter.Relativity.Production.InteractionAttachment.prolong
#print axioms RelationalPerimeter.Relativity.Production.InteractionAttachment.reexpress
#print axioms RelationalPerimeter.Relativity.Production.attached_prolong_anchor
#print axioms RelationalPerimeter.Relativity.Production.attached_prolong_effects
#print axioms RelationalPerimeter.Relativity.Production.attached_reexpress_effects
#print axioms RelationalPerimeter.Relativity.Production.attached_reexpress_return_anchor
#print axioms RelationalPerimeter.Relativity.Production.attached_effects_separate_inspections
#print axioms RelationalPerimeter.Relativity.Production.runAttachedComparison
#print axioms RelationalPerimeter.Relativity.Production.AttachedComparison.first
#print axioms RelationalPerimeter.Relativity.Production.AttachedComparison.second
#print axioms RelationalPerimeter.Relativity.Production.attached_head_independent
#print axioms RelationalPerimeter.Relativity.Production.attached_continuation_exact
/- AXIOM_AUDIT_END -/
