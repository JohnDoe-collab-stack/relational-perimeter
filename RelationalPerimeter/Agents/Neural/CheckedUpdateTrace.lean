import RelationalPerimeter.Agents.Neural.IncrementalReferenceEquivalence

/-!
# Finite dependent traces of checked updates

The generic trace is indexed by its exact source and exact final checked
agents.  At a step, the tail starts from `result.checked.next`, the successor
returned by the checker result stored at the head.  Its structurally recursive
program accepts every finite length admitted by the supplied dependent
checker.  The public meta-contract has a one-step specialization because its
update type has no constructor at the reconfigured successor.
-/
set_option genInjectivity false
namespace ConstitutiveSearch.NeuralAgent

/-! ## Generic dependent trace and finite checker -/

/-- Existentially packages the next contract together with the exact checked
update returned from one source agent.  The private constructor prevents a
caller from pairing a contract index with an unrelated checked transition. -/
structure DependentCheckedUpdateResult
    {constitution : ConstitutiveMetaContract}
    {currentContract : constitution.Contract}
    (current : CheckedAgent constitution currentContract) : Type 5 where
  private mk ::
  nextContract : constitution.Contract
  checked : CheckedUpdate current nextContract

def dependentCheckedUpdateResult
    {constitution : ConstitutiveMetaContract}
    {currentContract nextContract : constitution.Contract}
    {current : CheckedAgent constitution currentContract}
    (checked : CheckedUpdate current nextContract) :
    DependentCheckedUpdateResult current :=
  .mk nextContract checked

/-- A closed executable checker family.  Its update language may depend on the
exact current checked agent.  Consequently a transition absent from the
meta-contract need not be represented by an update constructor at all. -/
structure DependentIncrementalChecker
    (constitution : ConstitutiveMetaContract) : Type 7 where
  Error : Type
  Update : {contract : constitution.Contract} ->
    CheckedAgent constitution contract -> Type 6
  check : {contract : constitution.Contract} ->
    (current : CheckedAgent constitution contract) ->
    Update current -> Except Error (DependentCheckedUpdateResult current)

/-- A finite trace whose next source is definitionally the exact successor
returned by the checker at the preceding step. -/
inductive CheckedReconfigurationTrace
    {constitution : ConstitutiveMetaContract}
    (checker : DependentIncrementalChecker constitution) :
    {sourceContract : constitution.Contract} ->
      (source : CheckedAgent constitution sourceContract) ->
      {targetContract : constitution.Contract} ->
      CheckedAgent constitution targetContract -> Type 7
  | nil (current : CheckedAgent constitution contract) :
      CheckedReconfigurationTrace checker current current
  | step
      (update : checker.Update current)
      (result : DependentCheckedUpdateResult current)
      (accepted : checker.check current update = .ok result)
      (tail : CheckedReconfigurationTrace checker
        result.checked.next final) :
      CheckedReconfigurationTrace checker current final

/-- Constructive evidence that every edge of a generic trace is an actual
successful call to the supplied checker family. -/
inductive EveryCheckedStepSatisfies
    {constitution : ConstitutiveMetaContract}
    {checker : DependentIncrementalChecker constitution} :
    {sourceContract : constitution.Contract} ->
      {source : CheckedAgent constitution sourceContract} ->
      {targetContract : constitution.Contract} ->
      {final : CheckedAgent constitution targetContract} ->
      CheckedReconfigurationTrace checker source final -> Type 7
  | nil (current : CheckedAgent constitution contract) :
      EveryCheckedStepSatisfies (.nil current)
  | step
      (update : checker.Update current)
      (result : DependentCheckedUpdateResult current)
      (accepted : checker.check current update = .ok result)
      (tail : CheckedReconfigurationTrace checker
        result.checked.next final)
      (tailExact : EveryCheckedStepSatisfies tail) :
      EveryCheckedStepSatisfies
        (.step update result accepted tail)

/-- Contract evidence exposed by one exact checked result.  Persistent
obligations are transported through the permission stored in the checked
update, while every covered finite future is read from the exact successor
certificate. -/
structure CheckedStepContractPreservation
    {constitution : ConstitutiveMetaContract}
    {currentContract : constitution.Contract}
    {current : CheckedAgent constitution currentContract}
    (result : DependentCheckedUpdateResult current) : Type 7 where
  transportPersistent :
    (obligation : constitution.PersistentObligation currentContract
      result.nextContract) ->
    constitution.SourcePersistentWitness currentContract result.nextContract
      obligation ->
    constitution.TargetPersistentWitness currentContract result.nextContract
      obligation
  preserveEveryFiniteFuture :
    (requests : List
      (constitution.operational result.nextContract).FutureInput) ->
    (constitution.operational result.nextContract).futureContract.outcome
        ((constitution.operational result.nextContract).futureSourceOfState
          result.checked.next.state)
        requests =
      result.checked.next.certificate.futureRealization.reducedContract.outcome
        (result.checked.next.certificate.futureRealization.project
          ((constitution.operational result.nextContract).futureSourceOfState
            result.checked.next.state)) requests

def checkedStepContractPreservation
    {constitution : ConstitutiveMetaContract}
    {currentContract : constitution.Contract}
    {current : CheckedAgent constitution currentContract}
    (result : DependentCheckedUpdateResult current) :
    CheckedStepContractPreservation result :=
  { transportPersistent := fun obligation witness =>
      result.checked.transition.transport obligation witness
    preserveEveryFiniteFuture := fun requests =>
      result.checked.nextPreservesEveryFiniteFuture requests }

/-- Every accepted edge preserves the obligations and finite futures owned by
the exact contracts at that edge. -/
inductive EveryCheckedStepPreservesContracts
    {constitution : ConstitutiveMetaContract}
    {checker : DependentIncrementalChecker constitution} :
    {sourceContract : constitution.Contract} ->
      {source : CheckedAgent constitution sourceContract} ->
      {targetContract : constitution.Contract} ->
      {final : CheckedAgent constitution targetContract} ->
      CheckedReconfigurationTrace checker source final -> Type 8
  | nil (current : CheckedAgent constitution contract) :
      EveryCheckedStepPreservesContracts (.nil current)
  | step
      (update : checker.Update current)
      (result : DependentCheckedUpdateResult current)
      (accepted : checker.check current update = .ok result)
      (tail : CheckedReconfigurationTrace checker
        result.checked.next final)
      (headExact : CheckedStepContractPreservation result)
      (tailExact : EveryCheckedStepPreservesContracts tail) :
      EveryCheckedStepPreservesContracts
        (.step update result accepted tail)

def checkedTrace_constitutivelyAligned
    {constitution : ConstitutiveMetaContract}
    {checker : DependentIncrementalChecker constitution}
    {sourceContract targetContract : constitution.Contract}
    {source : CheckedAgent constitution sourceContract}
    {final : CheckedAgent constitution targetContract}
    (trace : CheckedReconfigurationTrace checker source final) :
    EveryCheckedStepSatisfies trace :=
  match trace with
  | .nil current => .nil current
  | .step update result accepted tail =>
      .step update result accepted tail
        (checkedTrace_constitutivelyAligned tail)

def checkedTrace_preservesContracts
    {constitution : ConstitutiveMetaContract}
    {checker : DependentIncrementalChecker constitution}
    {sourceContract targetContract : constitution.Contract}
    {source : CheckedAgent constitution sourceContract}
    {final : CheckedAgent constitution targetContract}
    (trace : CheckedReconfigurationTrace checker source final) :
    EveryCheckedStepPreservesContracts trace :=
  match trace with
  | .nil current => .nil current
  | .step update result accepted tail =>
      .step update result accepted tail
        (checkedStepContractPreservation result)
        (checkedTrace_preservesContracts tail)

/-- A finite dependent program of updates.  Its continuation is selected only
after the checker has produced the exact next checked agent.  This is the
generic replacement for a homogeneous list that would lose the dependency
between consecutive states. -/
inductive CheckedUpdateProgram
    {constitution : ConstitutiveMetaContract}
    (checker : DependentIncrementalChecker constitution) :
    {contract : constitution.Contract} ->
      CheckedAgent constitution contract -> Type 8
  | nil (current : CheckedAgent constitution contract) :
      CheckedUpdateProgram checker current
  | step
      (update : checker.Update current)
      (tail : (result : DependentCheckedUpdateResult current) ->
        CheckedUpdateProgram checker result.checked.next) :
      CheckedUpdateProgram checker current

/-- Exact execution of a dependent update program.  Each tail is the one
selected by the concrete result returned at its head. -/
inductive ExecutedCheckedUpdateProgram
    {constitution : ConstitutiveMetaContract}
    {checker : DependentIncrementalChecker constitution} :
    {sourceContract : constitution.Contract} ->
      (source : CheckedAgent constitution sourceContract) ->
      CheckedUpdateProgram checker source ->
      {targetContract : constitution.Contract} ->
      CheckedAgent constitution targetContract -> Type 8
  | nil (current : CheckedAgent constitution contract) :
      ExecutedCheckedUpdateProgram current (.nil current) current
  | step
      (update : checker.Update current)
      (tail : (result : DependentCheckedUpdateResult current) ->
        CheckedUpdateProgram checker result.checked.next)
      (result : DependentCheckedUpdateResult current)
      (accepted : checker.check current update = .ok result)
      (executedTail : ExecutedCheckedUpdateProgram result.checked.next
        (tail result) final) :
      ExecutedCheckedUpdateProgram current (.step update tail) final

def ExecutedCheckedUpdateProgram.toTrace
    {constitution : ConstitutiveMetaContract}
    {checker : DependentIncrementalChecker constitution}
    {sourceContract targetContract : constitution.Contract}
    {source : CheckedAgent constitution sourceContract}
    {final : CheckedAgent constitution targetContract}
    {program : CheckedUpdateProgram checker source}
    (executed : ExecutedCheckedUpdateProgram source program final) :
    CheckedReconfigurationTrace checker source final :=
  match executed with
  | .nil current => .nil current
  | .step update _ result accepted tail =>
      .step update result accepted tail.toTrace

/-- Successful result of checking a complete finite dependent program. -/
structure CheckedUpdateTraceResult
    {constitution : ConstitutiveMetaContract}
    (checker : DependentIncrementalChecker constitution)
    {sourceContract : constitution.Contract}
    (source : CheckedAgent constitution sourceContract)
    (program : CheckedUpdateProgram checker source) : Type 9 where
  private mk ::
  finalContract : constitution.Contract
  final : CheckedAgent constitution finalContract
  executed : ExecutedCheckedUpdateProgram source program final

/-- Execute every update in a finite dependent program.  There is no bound on
its length in this algorithm: admissibility of each next step is decided only
by the checker supplied for the exact current agent. -/
def checkUpdates
    {constitution : ConstitutiveMetaContract}
    (checker : DependentIncrementalChecker constitution) :
    {contract : constitution.Contract} ->
      (current : CheckedAgent constitution contract) ->
      (program : CheckedUpdateProgram checker current) ->
      Except checker.Error
        (CheckedUpdateTraceResult checker current program)
  | _, current, .nil _ =>
      .ok (.mk _ current (.nil current))
  | _, current, .step update tail =>
      match accepted : checker.check current update with
      | .error problem => .error problem
      | .ok result =>
          match checkUpdates checker result.checked.next (tail result) with
          | .error problem => .error problem
          | .ok completed =>
              .ok (.mk completed.finalContract completed.final
                (.step update tail result accepted completed.executed))

def ExecutedCheckedUpdateProgram.result
    {constitution : ConstitutiveMetaContract}
    {checker : DependentIncrementalChecker constitution}
    {sourceContract targetContract : constitution.Contract}
    {source : CheckedAgent constitution sourceContract}
    {final : CheckedAgent constitution targetContract}
    {program : CheckedUpdateProgram checker source}
    (executed : ExecutedCheckedUpdateProgram source program final) :
    CheckedUpdateTraceResult checker source program :=
  .mk targetContract final executed

/-- Completeness for finite dependent programs: every structurally finite
program whose every edge carries its actual successful checker equality is
accepted, independently of its length. -/
theorem checkUpdates_complete
    {constitution : ConstitutiveMetaContract}
    {checker : DependentIncrementalChecker constitution}
    {sourceContract targetContract : constitution.Contract}
    {source : CheckedAgent constitution sourceContract}
    {final : CheckedAgent constitution targetContract}
    {program : CheckedUpdateProgram checker source}
    (executed : ExecutedCheckedUpdateProgram source program final) :
    checkUpdates checker source program = .ok executed.result := by
  induction executed with
  | nil current => rfl
  | step update tail result accepted executedTail tailComplete =>
      unfold checkUpdates
      split
      · rename_i problem rejected
        have impossible : Except.error problem = Except.ok result :=
          rejected.symm.trans accepted
        cases impossible
      · rename_i actual acceptedActual
        have actualExact : actual = result :=
          Except.ok.inj (acceptedActual.symm.trans accepted)
        subst actual
        simp only [tailComplete]
        rfl

def checkUpdates_sound
    {constitution : ConstitutiveMetaContract}
    {checker : DependentIncrementalChecker constitution}
    {sourceContract : constitution.Contract}
    {source : CheckedAgent constitution sourceContract}
    {program : CheckedUpdateProgram checker source}
    (result : CheckedUpdateTraceResult checker source program)
    (_accepted : checkUpdates checker source program = .ok result) :
    EveryCheckedStepSatisfies result.executed.toTrace :=
  checkedTrace_constitutivelyAligned result.executed.toTrace

def checkUpdates_preservesContracts
    {constitution : ConstitutiveMetaContract}
    {checker : DependentIncrementalChecker constitution}
    {sourceContract : constitution.Contract}
    {source : CheckedAgent constitution sourceContract}
    {program : CheckedUpdateProgram checker source}
    (result : CheckedUpdateTraceResult checker source program)
    (_accepted : checkUpdates checker source program = .ok result) :
    EveryCheckedStepPreservesContracts result.executed.toTrace :=
  checkedTrace_preservesContracts result.executed.toTrace

/-- The public checker's dependent update language contains a constructor only
at the exact certified initial agent.  The absence of a constructor at the
reconfigured successor reflects the public meta-contract; it is not a length
test in the generic trace algorithm. -/
inductive PublicDependentIncrementalUpdate :
    {contract : PublicOperationalContract} ->
      CheckedAgent publicConstitutiveMetaContract contract -> Type 6
  | reconfigure (update : IncrementalNeuralUpdate) :
      PublicDependentIncrementalUpdate publicInitialCheckedAgent

def publicDependentIncrementalChecker :
    DependentIncrementalChecker publicConstitutiveMetaContract where
  Error := AlignmentError
  Update := PublicDependentIncrementalUpdate
  check := fun current update =>
    match update with
    | .reconfigure received =>
        match checkIncrementalUpdate received with
        | .error problem => .error problem
        | .ok checked =>
            .ok (dependentCheckedUpdateResult checked.checked)

def publicGenericSingletonProgram :
    CheckedUpdateProgram publicDependentIncrementalChecker
      publicInitialCheckedAgent :=
  .step (PublicDependentIncrementalUpdate.reconfigure
      publicIncrementalNeuralUpdate)
    (fun result => .nil result.checked.next)

theorem publicDependentIncrementalChecker_accepts_reference :
    publicDependentIncrementalChecker.check publicInitialCheckedAgent
        (PublicDependentIncrementalUpdate.reconfigure
          publicIncrementalNeuralUpdate) =
      .ok (dependentCheckedUpdateResult
        publicIncrementalCheckedUpdate.checked) := by
  rfl

def publicGenericSingletonResult :
    CheckedUpdateTraceResult publicDependentIncrementalChecker
      publicInitialCheckedAgent publicGenericSingletonProgram :=
  .mk .reconfigured publicIncrementalCheckedUpdate.checked.next (by
    unfold publicGenericSingletonProgram
    exact ExecutedCheckedUpdateProgram.step
      (checker := publicDependentIncrementalChecker)
      (current := publicInitialCheckedAgent)
      (PublicDependentIncrementalUpdate.reconfigure
        publicIncrementalNeuralUpdate)
      (fun result => .nil result.checked.next)
      (dependentCheckedUpdateResult publicIncrementalCheckedUpdate.checked)
      publicDependentIncrementalChecker_accepts_reference
      (.nil publicIncrementalCheckedUpdate.checked.next))

theorem checkUpdates_accepts_public_singleton :
    checkUpdates publicDependentIncrementalChecker
        publicInitialCheckedAgent publicGenericSingletonProgram =
      .ok publicGenericSingletonResult := by
  rfl

/-! ## Closed public specialization -/

/-- A finite trace whose head stores the exact successful checker result and
whose tail consumes that result's dependent successor. -/
inductive PublicCheckedReconfigurationTrace :
    {sourceContract : PublicOperationalContract} ->
      CheckedAgent publicConstitutiveMetaContract sourceContract ->
      List IncrementalNeuralUpdate ->
      {targetContract : PublicOperationalContract} ->
      CheckedAgent publicConstitutiveMetaContract targetContract -> Type 4
  | nil (current : CheckedAgent publicConstitutiveMetaContract contract) :
      PublicCheckedReconfigurationTrace current [] current
  | step
      (update : IncrementalNeuralUpdate)
      (incremental : PublicIncrementalCheckedUpdate)
      (accepted : checkIncrementalUpdate update = .ok incremental)
      (tail : PublicCheckedReconfigurationTrace incremental.checked.next rest final) :
      PublicCheckedReconfigurationTrace publicInitialCheckedAgent
        (update :: rest) final

/-- Constructive soundness evidence for every step in one exact dependent
trace.  `incrementalExact` identifies each stored result with the package
actually assembled by the checker. -/
inductive EveryPublicCheckedStepSatisfies :
    {sourceContract : PublicOperationalContract} ->
      {source : CheckedAgent publicConstitutiveMetaContract sourceContract} ->
      {updates : List IncrementalNeuralUpdate} ->
      {targetContract : PublicOperationalContract} ->
      {final : CheckedAgent publicConstitutiveMetaContract targetContract} ->
      (trace : PublicCheckedReconfigurationTrace source updates final) -> Type 4
  | nil (current : CheckedAgent publicConstitutiveMetaContract contract) :
      EveryPublicCheckedStepSatisfies (.nil current)
  | step
      (update : IncrementalNeuralUpdate)
      (incremental : PublicIncrementalCheckedUpdate)
      (accepted : checkIncrementalUpdate update = .ok incremental)
      (tail : PublicCheckedReconfigurationTrace incremental.checked.next rest final)
      (incrementalExact : incremental = publicIncrementalCheckedUpdate)
      (tailExact : EveryPublicCheckedStepSatisfies tail) :
      EveryPublicCheckedStepSatisfies
        (.step update incremental accepted tail)

def publicCheckedTrace_constitutivelyAligned
    (trace : PublicCheckedReconfigurationTrace source updates final) :
    EveryPublicCheckedStepSatisfies trace :=
  match trace with
  | .nil current => .nil current
  | .step update incremental accepted tail =>
      .step update incremental accepted tail
        (checkIncrementalUpdate_sound update incremental accepted)
        (publicCheckedTrace_constitutivelyAligned tail)

/-- The result returned by `checkPublicUpdates` retains the exact dependent trace;
the constructor is private so a caller cannot pair an arbitrary final agent
with a separately built history. -/
structure PublicCheckedUpdateTraceResult
    (updates : List IncrementalNeuralUpdate) : Type 5 where
  private mk ::
  finalContract : PublicOperationalContract
  final : CheckedAgent publicConstitutiveMetaContract finalContract
  trace : PublicCheckedReconfigurationTrace publicInitialCheckedAgent updates final

/-- Execute the checker over a finite list under the transitions admitted by
the fixed public meta-contract.  No transition out of `reconfigured` exists,
so a nonempty tail is rejected explicitly. -/
def checkPublicUpdates :
    (updates : List IncrementalNeuralUpdate) ->
      Except AlignmentError (PublicCheckedUpdateTraceResult updates)
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

theorem checkPublicUpdates_accepts_empty :
    Exists fun result => checkPublicUpdates [] = .ok result := by
  exact ⟨.mk .initial publicInitialCheckedAgent
    (.nil publicInitialCheckedAgent), rfl⟩

theorem checkPublicUpdates_accepts_singleton :
    Exists fun result =>
      checkPublicUpdates [publicIncrementalNeuralUpdate] = .ok result := by
  exact ⟨.mk .reconfigured publicIncrementalCheckedUpdate.checked.next
    (.step publicIncrementalNeuralUpdate publicIncrementalCheckedUpdate
      checkIncrementalUpdate_accepts_reference
      (.nil publicIncrementalCheckedUpdate.checked.next)), rfl⟩

theorem checkPublicUpdates_rejects_unadmitted_continuation :
    checkPublicUpdates [publicIncrementalNeuralUpdate,
        publicIncrementalNeuralUpdate] =
      .error .noAdmittedTransition := by
  rfl

/-- A successful result contains soundness evidence for its precise trace,
not merely the existence of some certified history. -/
def checkPublicUpdates_sound
    (updates : List IncrementalNeuralUpdate)
    (result : PublicCheckedUpdateTraceResult updates)
    (_accepted : checkPublicUpdates updates = .ok result) :
    EveryPublicCheckedStepSatisfies result.trace :=
  publicCheckedTrace_constitutivelyAligned result.trace

end ConstitutiveSearch.NeuralAgent
/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.NeuralAgent.DependentCheckedUpdateResult
#print axioms ConstitutiveSearch.NeuralAgent.DependentIncrementalChecker
#print axioms ConstitutiveSearch.NeuralAgent.CheckedReconfigurationTrace
#print axioms ConstitutiveSearch.NeuralAgent.EveryCheckedStepSatisfies
#print axioms ConstitutiveSearch.NeuralAgent.CheckedStepContractPreservation
#print axioms ConstitutiveSearch.NeuralAgent.checkedStepContractPreservation
#print axioms ConstitutiveSearch.NeuralAgent.EveryCheckedStepPreservesContracts
#print axioms ConstitutiveSearch.NeuralAgent.checkedTrace_preservesContracts
#print axioms ConstitutiveSearch.NeuralAgent.CheckedUpdateProgram
#print axioms ConstitutiveSearch.NeuralAgent.ExecutedCheckedUpdateProgram
#print axioms ConstitutiveSearch.NeuralAgent.checkUpdates
#print axioms ConstitutiveSearch.NeuralAgent.ExecutedCheckedUpdateProgram.result
#print axioms ConstitutiveSearch.NeuralAgent.checkUpdates_complete
#print axioms ConstitutiveSearch.NeuralAgent.checkUpdates_sound
#print axioms ConstitutiveSearch.NeuralAgent.checkUpdates_preservesContracts
#print axioms ConstitutiveSearch.NeuralAgent.PublicDependentIncrementalUpdate
#print axioms ConstitutiveSearch.NeuralAgent.publicDependentIncrementalChecker
#print axioms ConstitutiveSearch.NeuralAgent.publicDependentIncrementalChecker_accepts_reference
#print axioms ConstitutiveSearch.NeuralAgent.checkUpdates_accepts_public_singleton
#print axioms ConstitutiveSearch.NeuralAgent.PublicCheckedReconfigurationTrace
#print axioms ConstitutiveSearch.NeuralAgent.EveryPublicCheckedStepSatisfies
#print axioms ConstitutiveSearch.NeuralAgent.publicCheckedTrace_constitutivelyAligned
#print axioms ConstitutiveSearch.NeuralAgent.PublicCheckedUpdateTraceResult
#print axioms ConstitutiveSearch.NeuralAgent.checkPublicUpdates
#print axioms ConstitutiveSearch.NeuralAgent.checkPublicUpdates_accepts_singleton
#print axioms ConstitutiveSearch.NeuralAgent.checkPublicUpdates_rejects_unadmitted_continuation
#print axioms ConstitutiveSearch.NeuralAgent.checkPublicUpdates_sound
/- AXIOM_AUDIT_END -/
