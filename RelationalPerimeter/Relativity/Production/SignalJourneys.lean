import RelationalPerimeter.Relativity.Production.UsedDependencies

/-!
# Arrival provenance from the stored positive signal productions

Every available signal is traced to its own emitted occurrence through its
actual relays and the intervening productions. The extractor reads the
constituted formation; it never calls a producer. Equal readings do not
identify emissions or erase their paths. These are paths of the declared
local signal law, not spacetime trajectories or an admission of a meeting.
-/
set_option genInjectivity false
namespace RelationalPerimeter.Relativity.Production
open ConstitutiveSearch.Resources

inductive EmissionOccurrence : {context : List Kind} → {values : Values Value context} →
    Formed (context := context) values → Ref context .signal → Type where
  | emitted {context} {values : Values Value context} (past : Formed (context := context) values)
      (reading : Ref context .reading) (payload : Ref context .payload) :
      EmissionOccurrence (.produced past (.emitted reading payload)) .here
  | inherited {context} {values : Values Value context} {past : Formed (context := context) values}
      {kind} {instruction : Instruction context kind} {output : Value kind}
      (role : Produces values instruction output) {origin : Ref context .signal}
      (event : EmissionOccurrence past origin) : EmissionOccurrence (.produced past role) (.prior origin)

inductive SignalJourney : {context : List Kind} → {values : Values Value context} →
    Formed (context := context) values → Ref context .signal → Type where
  | emitted {context} {values : Values Value context} (past : Formed (context := context) values)
      (reading : Ref context .reading) (payload : Ref context .payload) :
      SignalJourney (.produced past (.emitted reading payload)) .here
  | relayed {context} {values : Values Value context} {past : Formed (context := context) values}
      {signal : Ref context .signal} (calibration : Ref context .calibration)
      (prior : SignalJourney past signal) :
      SignalJourney (.produced past (.relayed signal calibration)) .here
  | inherited {context} {values : Values Value context} {past : Formed (context := context) values}
      {kind} {instruction : Instruction context kind} {output : Value kind}
      (role : Produces values instruction output) {signal : Ref context .signal}
      (prior : SignalJourney past signal) : SignalJourney (.produced past role) (.prior signal)

def SignalJourney.origin {context} {values : Values Value context}
    {formation : Formed (context := context) values} {signal : Ref context .signal}
    (journey : SignalJourney formation signal) : Ref context .signal := by
  cases journey with
  | emitted _ _ _ => exact .here
  | relayed _ prior => exact .prior prior.origin
  | inherited _ prior => exact .prior prior.origin
termination_by structural journey

def SignalJourney.originEvent {context} {values : Values Value context}
    {formation : Formed (context := context) values} {signal : Ref context .signal}
    (journey : SignalJourney formation signal) : EmissionOccurrence formation journey.origin := by
  cases journey with
  | emitted past reading payload => exact .emitted past reading payload
  | relayed calibration prior => exact .inherited (.relayed _ calibration) prior.originEvent
  | inherited role prior => exact .inherited role prior.originEvent
termination_by structural journey

def SignalJourney.relayCount {context} {values : Values Value context}
    {formation : Formed (context := context) values} {signal : Ref context .signal}
    (journey : SignalJourney formation signal) : Nat := by
  cases journey with
  | emitted _ _ _ => exact 0
  | relayed _ prior => exact prior.relayCount + 1
  | inherited _ prior => exact prior.relayCount
termination_by structural journey

def SignalJourney.reaches {context} {values : Values Value context}
    {formation : Formed (context := context) values} {signal : Ref context .signal}
    (journey : SignalJourney formation signal) :
    PSum (journey.origin = signal)
      (UsedPath formation ⟨.signal, journey.origin⟩ ⟨.signal, signal⟩) := by
  cases journey with
  | emitted past reading payload => exact .inl rfl
  | @relayed context values past signal calibration prior =>
    have edge := Used.produced past (Produces.relayed signal calibration) signal
      (InputPort.relaySignal signal calibration)
    cases prior.reaches with
    | inl same =>
      have sourceExact :
          (⟨.signal, Ref.prior prior.origin⟩ : Occurrence (.signal :: context)) =
          oldOccurrence .signal ⟨.signal, signal⟩ :=
        congrArg (fun ref => oldOccurrence .signal ⟨.signal, ref⟩) same
      exact .inr (sourceExact.symm ▸ UsedPath.single edge)
    | inr path => exact .inr ((path.extend (.relayed _ calibration)).append (.single edge))
  | inherited role prior =>
    cases prior.reaches with
    | inl same => exact .inl (congrArg Ref.prior same)
    | inr path => exact .inr (path.extend role)
termination_by structural journey

theorem increments_length_append (left right : List Rational) :
    (left ++ right).length = left.length + right.length := by
  induction left with
  | nil => exact (Nat.zero_add right.length).symm
  | cons head tail ih => exact (congrArg Nat.succ ih).trans (Nat.succ_add _ _).symm

theorem SignalJourney.recorded_length {context} {values : Values Value context}
    {formation : Formed (context := context) values} {signal : Ref context .signal}
    (journey : SignalJourney formation signal) :
    (read values signal).increments.length = journey.relayCount := by
  induction journey with
  | emitted past reading payload => rfl
  | relayed calibration prior ih =>
    exact (increments_length_append _ _).trans (congrArg (fun count => count + 1) ih)
  | inherited role prior ih => exact ih

theorem SignalJourney.payload_from_origin {context} {values : Values Value context}
    {formation : Formed (context := context) values} {signal : Ref context .signal}
    (journey : SignalJourney formation signal) :
    (read values signal).payload = (read values journey.origin).payload := by
  induction journey with
  | emitted past reading payload => rfl
  | relayed calibration prior ih => exact ih
  | inherited role prior ih => exact ih

theorem received_signal_impossible (ref : Ref receivedKinds .signal) : False := by
  cases ref with
  | prior one => cases one with
    | prior two => cases two with
      | prior three => cases three

def signalJourney {context} {values : Values Value context}
    (formation : Formed (context := context) values) (signal : Ref context .signal) :
    SignalJourney formation signal := by
  cases formation with
  | received input => exact False.elim (received_signal_impossible signal)
  | produced past role =>
    cases signal with
    | here =>
      cases role with
      | emitted reading payload => exact .emitted past reading payload
      | relayed previous calibration => exact .relayed calibration (signalJourney past previous)
    | prior old => exact .inherited role (signalJourney past old)
termination_by structural formation

/-- Arrival provenance consumes the actual received production. It does not
replay reception, emission or any relay. The source signal remains distinct
from the newly constituted reading occurrence. -/
def receptionJourney {source : Cursor} {signal : Ref source.kinds .signal}
    (arrival : Production source (.receive signal)) :
    SignalJourney arrival.successor.formation
      (arrival.successorExact.symm ▸ (Ref.prior signal : Ref (source.extend arrival.determination).kinds .signal)) := by
  cases arrival with
  | mk determination successor exactSuccessor =>
    cases exactSuccessor
    exact .inherited determination.2 (signalJourney source.formation signal)

theorem receptionJourney_origin_exact {source : Cursor} {signal : Ref source.kinds .signal}
    (arrival : Production source (.receive signal)) :
    (receptionJourney arrival).origin =
      arrival.successorExact.symm ▸
        (Ref.prior (signalJourney source.formation signal).origin :
          Ref (source.extend arrival.determination).kinds .signal) := by
  cases arrival with
  | mk determination successor exactSuccessor => cases exactSuccessor; rfl

theorem reception_reads_arriving_signal {source : Cursor} {signal : Ref source.kinds .signal}
    (arrival : Production source (.receive signal)) :
    arrival.determination.1 = (source.read signal).reading := arrival.determination.2.output_exact

end RelationalPerimeter.Relativity.Production
/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Relativity.Production.EmissionOccurrence
#print axioms RelationalPerimeter.Relativity.Production.SignalJourney
#print axioms RelationalPerimeter.Relativity.Production.SignalJourney.origin
#print axioms RelationalPerimeter.Relativity.Production.SignalJourney.originEvent
#print axioms RelationalPerimeter.Relativity.Production.SignalJourney.relayCount
#print axioms RelationalPerimeter.Relativity.Production.SignalJourney.reaches
#print axioms RelationalPerimeter.Relativity.Production.increments_length_append
#print axioms RelationalPerimeter.Relativity.Production.SignalJourney.recorded_length
#print axioms RelationalPerimeter.Relativity.Production.SignalJourney.payload_from_origin
#print axioms RelationalPerimeter.Relativity.Production.received_signal_impossible
#print axioms RelationalPerimeter.Relativity.Production.signalJourney
#print axioms RelationalPerimeter.Relativity.Production.receptionJourney
#print axioms RelationalPerimeter.Relativity.Production.receptionJourney_origin_exact
#print axioms RelationalPerimeter.Relativity.Production.reception_reads_arriving_signal
/- AXIOM_AUDIT_END -/
