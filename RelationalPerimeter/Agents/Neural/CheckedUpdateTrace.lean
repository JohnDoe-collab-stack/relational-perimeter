import RelationalPerimeter.Agents.Neural.IncrementalReferenceEquivalence

/-!
# Finite dependent traces of checked updates

The trace is indexed by its exact source and exact final checked agents.  At a
step, the tail starts from `incremental.checked.next`, the successor returned
by the checker result stored at the head.  The public meta-contract currently
admits only the transition from `initial` to `reconfigured`; consequently its
executable checker accepts the empty trace and one checked update, and rejects
any attempted continuation rather than inventing a self-transition.
-/
set_option genInjectivity false
namespace ConstitutiveSearch.NeuralAgent

/-- A finite trace whose head stores the exact successful checker result and
whose tail consumes that result's dependent successor. -/
inductive CheckedReconfigurationTrace :
    {sourceContract : PublicOperationalContract} ->
      CheckedAgent publicConstitutiveMetaContract sourceContract ->
      List IncrementalNeuralUpdate ->
      {targetContract : PublicOperationalContract} ->
      CheckedAgent publicConstitutiveMetaContract targetContract -> Type 4
  | nil (current : CheckedAgent publicConstitutiveMetaContract contract) :
      CheckedReconfigurationTrace current [] current
  | step
      (update : IncrementalNeuralUpdate)
      (incremental : PublicIncrementalCheckedUpdate)
      (accepted : checkIncrementalUpdate update = .ok incremental)
      (tail : CheckedReconfigurationTrace incremental.checked.next rest final) :
      CheckedReconfigurationTrace publicInitialCheckedAgent
        (update :: rest) final

/-- Constructive soundness evidence for every step in one exact dependent
trace.  `incrementalExact` identifies each stored result with the package
actually assembled by the checker. -/
inductive EveryCheckedStepSatisfies :
    {sourceContract : PublicOperationalContract} ->
      {source : CheckedAgent publicConstitutiveMetaContract sourceContract} ->
      {updates : List IncrementalNeuralUpdate} ->
      {targetContract : PublicOperationalContract} ->
      {final : CheckedAgent publicConstitutiveMetaContract targetContract} ->
      (trace : CheckedReconfigurationTrace source updates final) -> Type 4
  | nil (current : CheckedAgent publicConstitutiveMetaContract contract) :
      EveryCheckedStepSatisfies (.nil current)
  | step
      (update : IncrementalNeuralUpdate)
      (incremental : PublicIncrementalCheckedUpdate)
      (accepted : checkIncrementalUpdate update = .ok incremental)
      (tail : CheckedReconfigurationTrace incremental.checked.next rest final)
      (incrementalExact : incremental = publicIncrementalCheckedUpdate)
      (tailExact : EveryCheckedStepSatisfies tail) :
      EveryCheckedStepSatisfies
        (.step update incremental accepted tail)

def checkedTrace_constitutivelyAligned
    (trace : CheckedReconfigurationTrace source updates final) :
    EveryCheckedStepSatisfies trace :=
  match trace with
  | .nil current => .nil current
  | .step update incremental accepted tail =>
      .step update incremental accepted tail
        (checkIncrementalUpdate_sound update incremental accepted)
        (checkedTrace_constitutivelyAligned tail)

/-- The result returned by `checkUpdates` retains the exact dependent trace;
the constructor is private so a caller cannot pair an arbitrary final agent
with a separately built history. -/
structure CheckedUpdateTraceResult
    (updates : List IncrementalNeuralUpdate) : Type 5 where
  private mk ::
  finalContract : PublicOperationalContract
  final : CheckedAgent publicConstitutiveMetaContract finalContract
  trace : CheckedReconfigurationTrace publicInitialCheckedAgent updates final

/-- Execute the checker over a finite list under the transitions admitted by
the fixed public meta-contract.  No transition out of `reconfigured` exists,
so a nonempty tail is rejected explicitly. -/
def checkUpdates :
    (updates : List IncrementalNeuralUpdate) ->
      Except AlignmentError (CheckedUpdateTraceResult updates)
  | [] => .ok (.mk .initial publicInitialCheckedAgent
      (.nil publicInitialCheckedAgent))
  | update :: rest =>
      match checkedExact : checkIncrementalUpdate update with
      | .error problem => .error problem
      | .ok incremental =>
          match rest with
          | [] => .ok (.mk .reconfigured incremental.checked.next
              (.step update incremental checkedExact
                (.nil incremental.checked.next)))
          | _ :: _ => .error .noAdmittedTransition

theorem checkUpdates_accepts_empty :
    Exists fun result => checkUpdates [] = .ok result := by
  exact ⟨.mk .initial publicInitialCheckedAgent
    (.nil publicInitialCheckedAgent), rfl⟩

theorem checkUpdates_accepts_public_singleton :
    Exists fun result =>
      checkUpdates [publicIncrementalNeuralUpdate] = .ok result := by
  exact ⟨.mk .reconfigured publicIncrementalCheckedUpdate.checked.next
    (.step publicIncrementalNeuralUpdate publicIncrementalCheckedUpdate
      checkIncrementalUpdate_accepts_reference
      (.nil publicIncrementalCheckedUpdate.checked.next)), rfl⟩

theorem checkUpdates_rejects_unadmitted_continuation :
    checkUpdates [publicIncrementalNeuralUpdate,
        publicIncrementalNeuralUpdate] =
      .error .noAdmittedTransition := by
  rfl

/-- A successful result contains soundness evidence for its precise trace,
not merely the existence of some certified history. -/
def checkUpdates_sound
    (updates : List IncrementalNeuralUpdate)
    (result : CheckedUpdateTraceResult updates)
    (_accepted : checkUpdates updates = .ok result) :
    EveryCheckedStepSatisfies result.trace :=
  checkedTrace_constitutivelyAligned result.trace

end ConstitutiveSearch.NeuralAgent
/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.NeuralAgent.CheckedReconfigurationTrace
#print axioms ConstitutiveSearch.NeuralAgent.EveryCheckedStepSatisfies
#print axioms ConstitutiveSearch.NeuralAgent.checkedTrace_constitutivelyAligned
#print axioms ConstitutiveSearch.NeuralAgent.CheckedUpdateTraceResult
#print axioms ConstitutiveSearch.NeuralAgent.checkUpdates
#print axioms ConstitutiveSearch.NeuralAgent.checkUpdates_accepts_public_singleton
#print axioms ConstitutiveSearch.NeuralAgent.checkUpdates_rejects_unadmitted_continuation
#print axioms ConstitutiveSearch.NeuralAgent.checkUpdates_sound
/- AXIOM_AUDIT_END -/
