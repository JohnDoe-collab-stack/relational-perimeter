import RelationalPerimeter.Agents.Neural.CheckedUpdateTrace

/-!
# Closed certified runtime API

The executable runtime has a private constructor and retains the dependent
checked trace that reaches its current agent.  `submitUpdate` is the sole
public reconfiguration operation: it invokes the incremental checker and, on
success, installs exactly the successor carried by the returned checked
update.  No raw artifact or separately reconstructed successor enters the
runtime state.
-/
set_option genInjectivity false
namespace ConstitutiveSearch.NeuralAgent

structure CertifiedRuntime : Type 5 where
  private mk ::
  updates : List IncrementalNeuralUpdate
  currentContract : PublicOperationalContract
  current : CheckedAgent publicConstitutiveMetaContract currentContract
  trace : CheckedReconfigurationTrace publicInitialCheckedAgent updates current
  everyStep : EveryCheckedStepSatisfies trace

def initialCertifiedRuntime : CertifiedRuntime :=
  .mk [] .initial publicInitialCheckedAgent
    (.nil publicInitialCheckedAgent)
    (.nil publicInitialCheckedAgent)

/-- Submit one update through the checker.  The sealed update history exposes
whether the fixed meta-contract still admits a transition. -/
def submitUpdate (runtime : CertifiedRuntime)
    (update : IncrementalNeuralUpdate) :
    Except AlignmentError CertifiedRuntime :=
  match runtime.updates with
  | [] =>
      match checkedExact : checkIncrementalUpdate update with
      | .error problem => .error problem
      | .ok incremental =>
          let nextTrace : CheckedReconfigurationTrace publicInitialCheckedAgent
              [update] incremental.checked.next :=
            .step update incremental checkedExact
              (.nil incremental.checked.next)
          .ok (.mk [update] .reconfigured incremental.checked.next nextTrace
            (checkedTrace_constitutivelyAligned nextTrace))
  | _ :: _ => .error .noAdmittedTransition

def publicUpdatedCertifiedRuntime : CertifiedRuntime :=
  match checkedExact : checkIncrementalUpdate publicIncrementalNeuralUpdate with
  | .error _ => initialCertifiedRuntime
  | .ok incremental =>
      let trace : CheckedReconfigurationTrace publicInitialCheckedAgent
          [publicIncrementalNeuralUpdate] incremental.checked.next :=
        .step publicIncrementalNeuralUpdate incremental checkedExact
          (.nil incremental.checked.next)
      .mk [publicIncrementalNeuralUpdate] .reconfigured
        incremental.checked.next trace
        (checkedTrace_constitutivelyAligned trace)

theorem submitUpdate_accepts_public_reference :
    Exists fun runtime =>
      submitUpdate initialCertifiedRuntime publicIncrementalNeuralUpdate =
        .ok runtime := by
  exact ⟨publicUpdatedCertifiedRuntime, rfl⟩

theorem submitUpdate_public_result_exact :
    submitUpdate initialCertifiedRuntime publicIncrementalNeuralUpdate =
      .ok publicUpdatedCertifiedRuntime := by
  rfl

theorem submitUpdate_rejects_unadmitted_second_transition :
    submitUpdate publicUpdatedCertifiedRuntime publicIncrementalNeuralUpdate =
      .error .noAdmittedTransition := by
  rfl

/-- Every runtime returned by the closed API carries the exact dependent trace
and its stepwise checker soundness evidence. -/
def CertifiedRuntime.checkedTrace (runtime : CertifiedRuntime) :
    EveryCheckedStepSatisfies runtime.trace :=
  runtime.everyStep

/-- A successful submission cannot install a runtime state without retaining
the trace produced through the checker. -/
def submitUpdate_sound
    (runtime next : CertifiedRuntime)
    (update : IncrementalNeuralUpdate)
    (_accepted : submitUpdate runtime update = .ok next) :
    EveryCheckedStepSatisfies next.trace :=
  next.everyStep

end ConstitutiveSearch.NeuralAgent
/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.NeuralAgent.CertifiedRuntime
#print axioms ConstitutiveSearch.NeuralAgent.initialCertifiedRuntime
#print axioms ConstitutiveSearch.NeuralAgent.submitUpdate
#print axioms ConstitutiveSearch.NeuralAgent.submitUpdate_accepts_public_reference
#print axioms ConstitutiveSearch.NeuralAgent.publicUpdatedCertifiedRuntime
#print axioms ConstitutiveSearch.NeuralAgent.submitUpdate_public_result_exact
#print axioms ConstitutiveSearch.NeuralAgent.submitUpdate_rejects_unadmitted_second_transition
#print axioms ConstitutiveSearch.NeuralAgent.CertifiedRuntime.checkedTrace
#print axioms ConstitutiveSearch.NeuralAgent.submitUpdate_sound
/- AXIOM_AUDIT_END -/
