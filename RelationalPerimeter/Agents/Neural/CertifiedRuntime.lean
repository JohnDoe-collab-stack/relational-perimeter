import RelationalPerimeter.Agents.Neural.CheckedUpdateTrace

/-!
# Closed certified runtime API

The executable runtime is parametric in a constitutive meta-contract and its
dependent checker.  Its private constructor retains the exact checked history
that reaches its current agent.  `submitUpdate` is the sole generic
reconfiguration operation: it invokes the checker on the stored agent and, on
success, installs exactly the successor carried by the returned checked
update.  No raw artifact or separately reconstructed successor enters the
runtime state.
-/
set_option genInjectivity false
namespace ConstitutiveSearch.NeuralAgent

/-! ## Generic closed runtime -/

/-- A snoc history of successful submissions.  Unlike the public compatibility
trace below, it supports every finite length admitted by the supplied checker
and records each exact dependent successor. -/
inductive CertifiedRuntimeHistory
    {constitution : ConstitutiveMetaContract}
    (checker : DependentIncrementalChecker constitution)
    {initialContract : constitution.Contract}
    (initial : CheckedAgent constitution initialContract) :
    {currentContract : constitution.Contract} ->
      CheckedAgent constitution currentContract -> Type 8
  | initial : CertifiedRuntimeHistory checker initial initial
  | submitted
      (history : CertifiedRuntimeHistory checker initial current)
      (update : checker.Update current)
      (result : DependentCheckedUpdateResult current)
      (accepted : checker.check current update = .ok result) :
      CertifiedRuntimeHistory checker initial result.checked.next

/-- Every stored runtime edge is exactly a successful checker result. -/
inductive EveryRuntimeStepSatisfies
    {constitution : ConstitutiveMetaContract}
    {checker : DependentIncrementalChecker constitution}
    {initialContract : constitution.Contract}
    {initial : CheckedAgent constitution initialContract} :
    {currentContract : constitution.Contract} ->
      {current : CheckedAgent constitution currentContract} ->
      CertifiedRuntimeHistory checker initial current -> Type 8
  | initial : EveryRuntimeStepSatisfies (.initial)
  | submitted
      (history : CertifiedRuntimeHistory checker initial current)
      (update : checker.Update current)
      (result : DependentCheckedUpdateResult current)
      (accepted : checker.check current update = .ok result)
      (prior : EveryRuntimeStepSatisfies history) :
      EveryRuntimeStepSatisfies
        (.submitted history update result accepted)

/-- Every runtime edge transports the persistent obligations of its exact
contract transition and preserves every finite future covered by its exact
successor certificate. -/
inductive EveryRuntimeStepPreservesContracts
    {constitution : ConstitutiveMetaContract}
    {checker : DependentIncrementalChecker constitution}
    {initialContract : constitution.Contract}
    {initial : CheckedAgent constitution initialContract} :
    {currentContract : constitution.Contract} ->
      {current : CheckedAgent constitution currentContract} ->
      CertifiedRuntimeHistory checker initial current -> Type 8
  | initial : EveryRuntimeStepPreservesContracts (.initial)
  | submitted
      (history : CertifiedRuntimeHistory checker initial current)
      (update : checker.Update current)
      (result : DependentCheckedUpdateResult current)
      (accepted : checker.check current update = .ok result)
      (prior : EveryRuntimeStepPreservesContracts history)
      (headExact : CheckedStepContractPreservation result) :
      EveryRuntimeStepPreservesContracts
        (.submitted history update result accepted)

def runtimeHistory_sound
    {constitution : ConstitutiveMetaContract}
    {checker : DependentIncrementalChecker constitution}
    {initialContract currentContract : constitution.Contract}
    {initial : CheckedAgent constitution initialContract}
    {current : CheckedAgent constitution currentContract}
    (history : CertifiedRuntimeHistory checker initial current) :
    EveryRuntimeStepSatisfies history :=
  match history with
  | .initial => .initial
  | .submitted priorHistory update result accepted =>
      .submitted priorHistory update result accepted
        (runtimeHistory_sound priorHistory)

def runtimeHistory_preservesContracts
    {constitution : ConstitutiveMetaContract}
    {checker : DependentIncrementalChecker constitution}
    {initialContract currentContract : constitution.Contract}
    {initial : CheckedAgent constitution initialContract}
    {current : CheckedAgent constitution currentContract}
    (history : CertifiedRuntimeHistory checker initial current) :
    EveryRuntimeStepPreservesContracts history :=
  match history with
  | .initial => .initial
  | .submitted priorHistory update result accepted =>
      .submitted priorHistory update result accepted
        (runtimeHistory_preservesContracts priorHistory)
        (checkedStepContractPreservation result)

/-- Closed runtime state for an arbitrary constitutive meta-contract and
dependent incremental checker. -/
structure CertifiedRuntime
    {constitution : ConstitutiveMetaContract}
    (checker : DependentIncrementalChecker constitution)
    {initialContract : constitution.Contract}
    (initial : CheckedAgent constitution initialContract) : Type 9 where
  private mk ::
  currentContract : constitution.Contract
  current : CheckedAgent constitution currentContract
  history : CertifiedRuntimeHistory checker initial current

def initialCertifiedRuntime
    {constitution : ConstitutiveMetaContract}
    (checker : DependentIncrementalChecker constitution)
    {initialContract : constitution.Contract}
    (initial : CheckedAgent constitution initialContract) :
    CertifiedRuntime checker initial :=
  .mk initialContract initial .initial

/-- The sole generic state-changing operation.  It calls the supplied checker
on the exact stored current agent and installs exactly the returned successor. -/
def submitUpdate
    {constitution : ConstitutiveMetaContract}
    {checker : DependentIncrementalChecker constitution}
    {initialContract : constitution.Contract}
    {initial : CheckedAgent constitution initialContract}
    (runtime : CertifiedRuntime checker initial)
    (update : checker.Update runtime.current) :
    Except checker.Error (CertifiedRuntime checker initial) :=
  match accepted : checker.check runtime.current update with
  | .error problem => .error problem
  | .ok result =>
      .ok (.mk result.nextContract result.checked.next
        (.submitted runtime.history update result accepted))

def CertifiedRuntime.checkedHistory
    {constitution : ConstitutiveMetaContract}
    {checker : DependentIncrementalChecker constitution}
    {initialContract : constitution.Contract}
    {initial : CheckedAgent constitution initialContract}
    (runtime : CertifiedRuntime checker initial) :
    EveryRuntimeStepSatisfies runtime.history :=
  runtimeHistory_sound runtime.history

def CertifiedRuntime.preservedContracts
    {constitution : ConstitutiveMetaContract}
    {checker : DependentIncrementalChecker constitution}
    {initialContract : constitution.Contract}
    {initial : CheckedAgent constitution initialContract}
    (runtime : CertifiedRuntime checker initial) :
    EveryRuntimeStepPreservesContracts runtime.history :=
  runtimeHistory_preservesContracts runtime.history

def submitUpdate_sound
    {constitution : ConstitutiveMetaContract}
    {checker : DependentIncrementalChecker constitution}
    {initialContract : constitution.Contract}
    {initial : CheckedAgent constitution initialContract}
    (runtime next : CertifiedRuntime checker initial)
    (update : checker.Update runtime.current)
    (_accepted : submitUpdate runtime update = .ok next) :
    EveryRuntimeStepSatisfies next.history :=
  next.checkedHistory

/-- A rejected checker result cannot install any runtime state.  The statement
is generic in the meta-contract and checker; it follows from the same exact
checker call consumed by `submitUpdate`, rather than from a later comparison
of runtime states. -/
theorem submitUpdate_rejected_cannot_install
    {constitution : ConstitutiveMetaContract}
    {checker : DependentIncrementalChecker constitution}
    {initialContract : constitution.Contract}
    {initial : CheckedAgent constitution initialContract}
    (runtime : CertifiedRuntime checker initial)
    (update : checker.Update runtime.current)
    (problem : checker.Error)
    (rejected : checker.check runtime.current update = .error problem) :
    Not (Exists fun next => submitUpdate runtime update = .ok next) := by
  intro installed
  rcases installed with ⟨next, installed⟩
  unfold submitUpdate at installed
  split at installed
  · cases installed
  · rename_i result accepted
    have impossible : Except.error problem = Except.ok result :=
      rejected.symm.trans accepted
    cases impossible

def publicInitialCertifiedRuntime :
    CertifiedRuntime publicDependentIncrementalChecker
      publicInitialCheckedAgent :=
  initialCertifiedRuntime publicDependentIncrementalChecker
    publicInitialCheckedAgent

def publicUpdatedCertifiedRuntime :
    CertifiedRuntime publicDependentIncrementalChecker
      publicInitialCheckedAgent :=
  match submitUpdate publicInitialCertifiedRuntime
      (.reconfigure publicIncrementalNeuralUpdate) with
  | .error _ => publicInitialCertifiedRuntime
  | .ok runtime => runtime

theorem submitUpdate_public_result_exact :
    submitUpdate publicInitialCertifiedRuntime
        (.reconfigure publicIncrementalNeuralUpdate) =
      .ok publicUpdatedCertifiedRuntime := by
  rfl

/-! ## Closed public specialization -/

structure PublicCertifiedRuntime : Type 5 where
  private mk ::
  updates : List IncrementalNeuralUpdate
  currentContract : PublicOperationalContract
  current : CheckedAgent publicConstitutiveMetaContract currentContract
  trace : PublicCheckedReconfigurationTrace publicInitialCheckedAgent updates current
  everyStep : EveryPublicCheckedStepSatisfies trace

def initialPublicCertifiedRuntime : PublicCertifiedRuntime :=
  .mk [] .initial publicInitialCheckedAgent
    (.nil publicInitialCheckedAgent)
    (.nil publicInitialCheckedAgent)

/-- Submit one update through the checker.  The sealed update history exposes
whether the fixed meta-contract still admits a transition. -/
def submitPublicUpdate (runtime : PublicCertifiedRuntime)
    (update : IncrementalNeuralUpdate) :
    Except AlignmentError PublicCertifiedRuntime :=
  match runtime.updates with
  | [] =>
      match checkedExact : checkIncrementalUpdate update with
      | .error problem => .error problem
      | .ok incremental =>
          let nextTrace : PublicCheckedReconfigurationTrace publicInitialCheckedAgent
              [update] incremental.checked.next :=
            .step update incremental checkedExact
              (.nil incremental.checked.next)
          .ok (.mk [update] .reconfigured incremental.checked.next nextTrace
            (publicCheckedTrace_constitutivelyAligned nextTrace))
  | _ :: _ => .error .noAdmittedTransition

def publicUpdatedPublicCertifiedRuntime : PublicCertifiedRuntime :=
  match checkedExact : checkIncrementalUpdate publicIncrementalNeuralUpdate with
  | .error _ => initialPublicCertifiedRuntime
  | .ok incremental =>
      let trace : PublicCheckedReconfigurationTrace publicInitialCheckedAgent
          [publicIncrementalNeuralUpdate] incremental.checked.next :=
        .step publicIncrementalNeuralUpdate incremental checkedExact
          (.nil incremental.checked.next)
      .mk [publicIncrementalNeuralUpdate] .reconfigured
        incremental.checked.next trace
        (publicCheckedTrace_constitutivelyAligned trace)

theorem submitPublicUpdate_accepts_reference :
    Exists fun runtime =>
      submitPublicUpdate initialPublicCertifiedRuntime publicIncrementalNeuralUpdate =
        .ok runtime := by
  exact ⟨publicUpdatedPublicCertifiedRuntime, rfl⟩

theorem submitPublicUpdate_result_exact :
    submitPublicUpdate initialPublicCertifiedRuntime publicIncrementalNeuralUpdate =
      .ok publicUpdatedPublicCertifiedRuntime := by
  rfl

theorem submitPublicUpdate_rejects_unadmitted_second_transition :
    submitPublicUpdate publicUpdatedPublicCertifiedRuntime publicIncrementalNeuralUpdate =
      .error .noAdmittedTransition := by
  rfl

/-- Every runtime returned by the closed API carries the exact dependent trace
and its stepwise checker soundness evidence. -/
def PublicCertifiedRuntime.checkedTrace (runtime : PublicCertifiedRuntime) :
    EveryPublicCheckedStepSatisfies runtime.trace :=
  runtime.everyStep

/-- A successful submission cannot install a runtime state without retaining
the trace produced through the checker. -/
def submitPublicUpdate_sound
    (runtime next : PublicCertifiedRuntime)
    (update : IncrementalNeuralUpdate)
    (_accepted : submitPublicUpdate runtime update = .ok next) :
    EveryPublicCheckedStepSatisfies next.trace :=
  next.everyStep

end ConstitutiveSearch.NeuralAgent
/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.NeuralAgent.CertifiedRuntime
#print axioms ConstitutiveSearch.NeuralAgent.EveryRuntimeStepPreservesContracts
#print axioms ConstitutiveSearch.NeuralAgent.runtimeHistory_preservesContracts
#print axioms ConstitutiveSearch.NeuralAgent.initialCertifiedRuntime
#print axioms ConstitutiveSearch.NeuralAgent.submitUpdate
#print axioms ConstitutiveSearch.NeuralAgent.submitUpdate_sound
#print axioms ConstitutiveSearch.NeuralAgent.submitUpdate_rejected_cannot_install
#print axioms ConstitutiveSearch.NeuralAgent.CertifiedRuntime.preservedContracts
#print axioms ConstitutiveSearch.NeuralAgent.publicInitialCertifiedRuntime
#print axioms ConstitutiveSearch.NeuralAgent.publicUpdatedCertifiedRuntime
#print axioms ConstitutiveSearch.NeuralAgent.submitUpdate_public_result_exact
#print axioms ConstitutiveSearch.NeuralAgent.PublicCertifiedRuntime
#print axioms ConstitutiveSearch.NeuralAgent.initialPublicCertifiedRuntime
#print axioms ConstitutiveSearch.NeuralAgent.submitPublicUpdate
#print axioms ConstitutiveSearch.NeuralAgent.submitPublicUpdate_accepts_reference
#print axioms ConstitutiveSearch.NeuralAgent.publicUpdatedPublicCertifiedRuntime
#print axioms ConstitutiveSearch.NeuralAgent.submitPublicUpdate_result_exact
#print axioms ConstitutiveSearch.NeuralAgent.submitPublicUpdate_rejects_unadmitted_second_transition
#print axioms ConstitutiveSearch.NeuralAgent.PublicCertifiedRuntime.checkedTrace
#print axioms ConstitutiveSearch.NeuralAgent.submitPublicUpdate_sound
/- AXIOM_AUDIT_END -/
