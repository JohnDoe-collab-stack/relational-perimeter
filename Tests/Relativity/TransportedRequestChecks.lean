import RelationalPerimeter

/-! Public consumers of the full transported local contract. Evaluations are
executability smoke checks, not measurements or relativistic certificates. -/
set_option genInjectivity false
namespace Tests.Relativity.TransportedRequestChecks
open RelationalPerimeter.Relativity
open RelationalPerimeter.Relativity.Production
open ConstitutiveSearch.Resources
open ConstitutiveSearch.ContinuationSignatures

def input : Received := ⟨Rational.zero, 7, Calibration.unit⟩
def source : Cursor := emittedCursor input
def first : Instruction source.kinds .signal := .relay .here (.prior (.prior (.prior .here)))
def second : Instruction source.kinds .reading := .receive .here
def original := produceIndependentPair source first second
def reversed := produceIndependentPair source second first
def raccord := independentPairAddressed original reversed

theorem address_return (position : Nat) :
    raccord.addresses.backward (raccord.addresses.forward position) = position :=
  raccord.addresses.forwardBackward position

theorem request_return (request : LocalRequest) :
    (request.rename raccord.addresses.forward).rename raccord.addresses.backward = request :=
  request.rename_returns _ _ raccord.addresses.forwardBackward

theorem all_admissions_and_refusals (request : LocalRequest) :
    admissionEnabled reversed.cursor (request.rename raccord.addresses.forward) =
      admissionEnabled original.cursor request := transported_admission_exact raccord.addresses request

theorem wrong_sort_refused :
    admissionEnabled original.cursor (.inspect .signal 0) = false ∧
    admissionEnabled reversed.cursor (.inspect .signal 1) = false := ⟨rfl, rfl⟩

theorem absent_port_refused :
    admissionEnabled original.cursor (.receive 100) = false ∧
    admissionEnabled reversed.cursor (.receive 100) = false := ⟨rfl, rfl⟩

def requests : List LocalRequest :=
  [.inspect .reading 0, .inspect .signal 0, .receive 100,
   .receive 1, .inspect .signal 2, .relay 2 6,
   .inspect .signal 0, .emit 2 6, .inspect .signal 0]

def paired := runCorrespondingRequests raccord requests

theorem mixed_requests_translated_exactly : paired.translated =
    [.inspect .reading 1, .inspect .signal 1, .receive 100,
     .receive 0, .inspect .signal 1, .relay 1 6,
     .inspect .signal 0, .emit 3 6, .inspect .signal 0] := rfl

theorem source_runner_unchanged : paired.first = runRequests original.cursor requests :=
  correspondingRequests_source_exact raccord requests

theorem target_runner_unchanged : paired.second = runRequests reversed.cursor paired.translated :=
  correspondingRequests_target_exact raccord requests

theorem complete_forward_contract (future : List LocalRequest) :
    localContract.outcome reversed.cursor (runCorrespondingRequests raccord future).translated =
      localContract.outcome original.cursor future := transported_all_futures_exact raccord future

theorem complete_reverse_contract (future : List LocalRequest) :
    localContract.outcome original.cursor (runCorrespondingRequests raccord.reverse future).translated =
      localContract.outcome reversed.cursor future := transported_all_futures_exact raccord.reverse future

theorem no_request_dropped : paired.translated.length = requests.length :=
  translated_length_exact raccord requests

theorem actual_final_reads {kind} (ref : Ref paired.first.cursor.kinds kind) :
    paired.second.cursor.read (paired.raccord.constitution.reading.references.forward ref) =
      paired.first.cursor.read ref := paired.raccord.constitution.reading.reads ref

def relayEdge : Used original.cursor.formation
    (⟨.signal, .prior (.prior .here)⟩ : Occurrence original.cursor.kinds) ⟨.signal, .prior .here⟩ :=
  .inherited original.secondDetermination.2
    (.produced source.formation original.firstDetermination.2 .here
      (.relaySignal .here (.prior (.prior (.prior .here)))))

def transportedEdge := paired.raccord.constitution.forwardUsed (paired.first.transportUsed relayEdge)
def returnedEdge := paired.raccord.constitution.backwardUsed transportedEdge
def transportedPath := paired.raccord.constitution.forwardPath (paired.first.transportPath (.single relayEdge))

-- After a receive adds a reading, the old exchanged occurrences shift to
-- addresses 1 and 2. A fixed initial swap would point at the wrong occurrence.
def dynamicRequests : List LocalRequest := [.receive 1, .inspect .signal 2]
def dynamicPair := runCorrespondingRequests raccord dynamicRequests

theorem translation_tracks_actual_extension : dynamicPair.translated = [.receive 0, .inspect .signal 1] := rfl

theorem frozen_translation_changes_contract :
    localContract.outcome reversed.cursor (dynamicRequests.map (LocalRequest.rename raccord.addresses.forward)) ≠
      localContract.outcome original.cursor dynamicRequests := by
  intro same
  have suffix := congrArg (fun outcome => match outcome with
    | .stop _ => false
    | .step _ _ _ tail => match tail with
      | .stop _ => false
      | .step _ allowed _ _ => allowed) same
  change false = true at suffix
  cases suffix

def permissions : Outcome LocalEvent Unit → List Bool
  | .stop _ => []
  | .step _ allowed _ rest => allowed :: permissions rest

theorem mixed_permissions : permissions paired.first.report =
    [true, false, false, true, true, true, true, true, true] := rfl

#eval permissions paired.first.report
#eval permissions paired.second.report
#eval StrongPerimetralTurning.History.length paired.first.history

end Tests.Relativity.TransportedRequestChecks
/- AXIOM_AUDIT_BEGIN -/
#print axioms Tests.Relativity.TransportedRequestChecks.address_return
#print axioms Tests.Relativity.TransportedRequestChecks.request_return
#print axioms Tests.Relativity.TransportedRequestChecks.all_admissions_and_refusals
#print axioms Tests.Relativity.TransportedRequestChecks.wrong_sort_refused
#print axioms Tests.Relativity.TransportedRequestChecks.absent_port_refused
#print axioms Tests.Relativity.TransportedRequestChecks.paired
#print axioms Tests.Relativity.TransportedRequestChecks.mixed_requests_translated_exactly
#print axioms Tests.Relativity.TransportedRequestChecks.source_runner_unchanged
#print axioms Tests.Relativity.TransportedRequestChecks.target_runner_unchanged
#print axioms Tests.Relativity.TransportedRequestChecks.complete_forward_contract
#print axioms Tests.Relativity.TransportedRequestChecks.complete_reverse_contract
#print axioms Tests.Relativity.TransportedRequestChecks.no_request_dropped
#print axioms Tests.Relativity.TransportedRequestChecks.actual_final_reads
#print axioms Tests.Relativity.TransportedRequestChecks.transportedEdge
#print axioms Tests.Relativity.TransportedRequestChecks.returnedEdge
#print axioms Tests.Relativity.TransportedRequestChecks.transportedPath
#print axioms Tests.Relativity.TransportedRequestChecks.translation_tracks_actual_extension
#print axioms Tests.Relativity.TransportedRequestChecks.frozen_translation_changes_contract
#print axioms Tests.Relativity.TransportedRequestChecks.mixed_permissions
/- AXIOM_AUDIT_END -/
