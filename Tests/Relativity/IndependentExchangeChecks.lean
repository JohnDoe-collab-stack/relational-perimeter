import RelationalPerimeter

/-! Public consumers of independent exchanges. These are executable local
checks, not measurements, physical grouping or reconstruction of geometry. -/
set_option genInjectivity false
namespace Tests.Relativity.IndependentExchangeChecks
open RelationalPerimeter.Relativity
open RelationalPerimeter.Relativity.Production
open ConstitutiveSearch.Resources
open ConstitutiveSearch.ContinuationSignatures

def input : Received := ⟨Rational.zero, 7, Calibration.unit⟩
def source : Cursor := emittedCursor input
def first : Instruction source.kinds .signal := .relay .here (.prior (.prior (.prior .here)))
def second : Instruction source.kinds .reading := .receive .here
def pairProduction := produceIndependentPair source first second
def reversedProduction := produceIndependentPair source second first
def pair := pairProduction.execution
def reversed := reversedProduction.execution
def correspondence := independentPairConstitution pairProduction reversedProduction

theorem two_actual_steps : StrongPerimetralTurning.History.length pair.history = 2 :=
  independentPair_history_length source first second

theorem different_intermediate_kinds :
    (perform source first).successor.kinds ≠ (perform source second).successor.kinds := by
  intro same
  have heads := congrArg List.head? same
  change (some Kind.signal) = some Kind.reading at heads
  cases heads

theorem corresponding_relay_outputs :
    reversed.cursor.read (Ref.here : Ref reversed.cursor.kinds .signal) =
      pair.cursor.read (.prior .here) := correspondence.reading.reads (.prior .here)

theorem corresponding_receive_outputs :
    reversed.cursor.read (Ref.prior .here : Ref reversed.cursor.kinds .reading) =
      pair.cursor.read .here := correspondence.reading.reads .here

theorem occurrence_return (occurrence : Occurrence pair.cursor.kinds) :
    correspondence.reading.references.occurrences.backward
      (correspondence.reading.references.occurrences.forward occurrence) = occurrence :=
  correspondence.reading.references.occurrences.forwardBackward occurrence

theorem reverse_occurrence_return (occurrence : Occurrence reversed.cursor.kinds) :
    correspondence.reading.references.occurrences.forward
      (correspondence.reading.references.occurrences.backward occurrence) = occurrence :=
  correspondence.reading.references.occurrences.backwardForward occurrence

def relayEdge : Used pair.cursor.formation
    (⟨.signal, .prior (.prior .here)⟩ : Occurrence pair.cursor.kinds) ⟨.signal, .prior .here⟩ :=
  .inherited pairProduction.secondDetermination.2
    (.produced source.formation pairProduction.firstDetermination.2 .here
      (.relaySignal .here (.prior (.prior (.prior .here)))))

def transportedRelayEdge := correspondence.forwardUsed relayEdge
def returnedRelayEdge := correspondence.backwardUsed transportedRelayEdge
def transportedRelayPath := correspondence.forwardPath (.single relayEdge)

theorem dependency_presence_exact (one two : Occurrence pair.cursor.kinds) :
    Nonempty (Used reversed.cursor.formation (correspondence.reading.references.occurrences.forward one)
      (correspondence.reading.references.occurrences.forward two)) ↔ Nonempty (Used pair.cursor.formation one two) :=
  correspondence.used_iff one two

def continuation : Program pair.cursor.kinds := .step (.receive (.prior .here)) .done
def continued := continueCorresponding correspondence continuation

theorem continuation_uses_existing_source_runner : continued.first = run pair.cursor continuation :=
  continueCorresponding_source_exact correspondence continuation

theorem continuation_uses_existing_target_runner :
    continued.second = run reversed.cursor (continuation.rename correspondence.reading.references) :=
  continueCorresponding_target_exact correspondence continuation

theorem continuation_return (schedule : Program pair.cursor.kinds) :
    (schedule.rename correspondence.reading.references).rename correspondence.reading.references.reverse = schedule :=
  schedule.rename_returns correspondence.reading.references

theorem inspection_follows_occurrence :
    referenceEvent reversed.cursor (.inspect .reading 1) =
      referenceEvent pair.cursor (.inspect .reading 0) :=
  transported_inspection_exact correspondence.reading .here

theorem untranslated_addresses_are_not_equivalent :
    ¬ FutureEquivalent localContract pair.cursor reversed.cursor := by
  intro same
  have admission := same.enabled (.inspect .reading 0)
  change true = false at admission
  cases admission

theorem continuation_output_exact :
    continued.second.cursor.read (Ref.here : Ref continued.second.cursor.kinds .reading) =
      continued.first.cursor.read (Ref.here : Ref continued.first.cursor.kinds .reading) :=
  continued.raccord.reading.reads .here

theorem continuation_reads_relayed_production :
    continued.first.cursor.read (Ref.here : Ref continued.first.cursor.kinds .reading) = Rational.one := rfl

def arbitrarilyLongContinuation (count : Nat) :=
  continueCorresponding correspondence
    (relayProgram (.prior .here) (.prior (.prior (.prior (.prior (.prior .here))))) count)

def carriedEdgeAfterContinuation (count : Nat) :=
  (arbitrarilyLongContinuation count).raccord.forwardUsed
    (historyTransportUsed (arbitrarilyLongContinuation count).first.history relayEdge)

-- Equal values do not authorize identification of the two fresh occurrences.
def equalSource := Cursor.received input
def equalProduction := produceIndependentPair equalSource emission emission
def equalPair := equalProduction.execution

theorem equal_values_distinct_occurrences :
    equalPair.cursor.read (Ref.here : Ref equalPair.cursor.kinds .signal) =
      equalPair.cursor.read (.prior .here) ∧
    (⟨.signal, .prior .here⟩ : Occurrence equalPair.cursor.kinds) ≠ ⟨.signal, .here⟩ :=
  ⟨rfl, independentPair_occurrences_distinct equalProduction⟩

-- A relay on the newly emitted signal really uses that fresh occurrence.
def dependentRelay : Instruction (.signal :: receivedKinds) .signal :=
  .relay .here (.prior (.prior (.prior .here)))

def dependentFreshPort : InputPort dependentRelay (Ref.here : Ref (.signal :: receivedKinds) .signal) :=
  .relaySignal .here (.prior (.prior (.prior .here)))

theorem dependentRelay_is_not_old_port_weakening (candidate : Instruction receivedKinds .signal)
    (same : candidate.rename Ref.prior = dependentRelay) : False := by
  have port : InputPort (candidate.rename Ref.prior) (Ref.here : Ref (.signal :: receivedKinds) .signal) :=
    same.symm ▸ dependentFreshPort
  obtain ⟨old, _, exactRef⟩ := port.priorOrigin candidate .here
  exact fresh_position_distinct old (congrArg Ref.position exactRef)

-- Executability only. The complete addressed contract remains a separate gate.
#eval (show Rational from continued.first.cursor.read
  (Ref.here : Ref continued.first.cursor.kinds .reading)).index
#eval StrongPerimetralTurning.History.length (arbitrarilyLongContinuation 10).second.history

end Tests.Relativity.IndependentExchangeChecks
/- AXIOM_AUDIT_BEGIN -/
#print axioms Tests.Relativity.IndependentExchangeChecks.two_actual_steps
#print axioms Tests.Relativity.IndependentExchangeChecks.different_intermediate_kinds
#print axioms Tests.Relativity.IndependentExchangeChecks.corresponding_relay_outputs
#print axioms Tests.Relativity.IndependentExchangeChecks.corresponding_receive_outputs
#print axioms Tests.Relativity.IndependentExchangeChecks.occurrence_return
#print axioms Tests.Relativity.IndependentExchangeChecks.reverse_occurrence_return
#print axioms Tests.Relativity.IndependentExchangeChecks.relayEdge
#print axioms Tests.Relativity.IndependentExchangeChecks.transportedRelayEdge
#print axioms Tests.Relativity.IndependentExchangeChecks.returnedRelayEdge
#print axioms Tests.Relativity.IndependentExchangeChecks.transportedRelayPath
#print axioms Tests.Relativity.IndependentExchangeChecks.dependency_presence_exact
#print axioms Tests.Relativity.IndependentExchangeChecks.continuation_uses_existing_source_runner
#print axioms Tests.Relativity.IndependentExchangeChecks.continuation_uses_existing_target_runner
#print axioms Tests.Relativity.IndependentExchangeChecks.continuation_return
#print axioms Tests.Relativity.IndependentExchangeChecks.inspection_follows_occurrence
#print axioms Tests.Relativity.IndependentExchangeChecks.untranslated_addresses_are_not_equivalent
#print axioms Tests.Relativity.IndependentExchangeChecks.continuation_output_exact
#print axioms Tests.Relativity.IndependentExchangeChecks.continuation_reads_relayed_production
#print axioms Tests.Relativity.IndependentExchangeChecks.arbitrarilyLongContinuation
#print axioms Tests.Relativity.IndependentExchangeChecks.carriedEdgeAfterContinuation
#print axioms Tests.Relativity.IndependentExchangeChecks.equal_values_distinct_occurrences
#print axioms Tests.Relativity.IndependentExchangeChecks.dependentRelay_is_not_old_port_weakening
/- AXIOM_AUDIT_END -/
