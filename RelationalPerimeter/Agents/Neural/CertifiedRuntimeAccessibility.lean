import RelationalPerimeter.Agents.Neural.CertifiedRuntime

/-!
# Accessibility of every state produced by the closed runtime API

Reachability is generated only by the initial runtime and successful calls to
`submitUpdate`.  The accessibility theorem returns a trace indexed by the
exact stored update list and exact current checked agent of the reached
runtime, together with constructive soundness evidence for every trace step.
-/
set_option genInjectivity false
namespace ConstitutiveSearch.NeuralAgent

/-- The least family of runtime states obtainable from the public initial
state by successful submissions through the closed API. -/
inductive CertifiedRuntimeReachable : CertifiedRuntime -> Type 5
  | initial : CertifiedRuntimeReachable initialCertifiedRuntime
  | submitted
      (source : CertifiedRuntime)
      (update : IncrementalNeuralUpdate)
      (next : CertifiedRuntime)
      (sourceReachable : CertifiedRuntimeReachable source)
      (accepted : submitUpdate source update = .ok next) :
      CertifiedRuntimeReachable next

/-- Exact accessibility evidence for one runtime.  Both indices are the
runtime projections themselves, so neither the update history nor the final
checked agent can be reconstructed independently. -/
structure CertifiedRuntimeAccessibility
    (runtime : CertifiedRuntime) : Type 5 where
  trace : CheckedReconfigurationTrace publicInitialCheckedAgent
    runtime.updates runtime.current
  everyStep : EveryCheckedStepSatisfies trace

/-- Every state reachable through the closed API carries its exact dependent
checked trace.  The conclusion is stronger than mere trace existence: it also
returns constructive soundness evidence for every stored step. -/
def reachableRuntime_accessibility
    (runtime : CertifiedRuntime)
    (_reachable : CertifiedRuntimeReachable runtime) :
    CertifiedRuntimeAccessibility runtime :=
  { trace := runtime.trace
    everyStep := runtime.everyStep }

def publicInitialCertifiedRuntime_reachable :
    CertifiedRuntimeReachable initialCertifiedRuntime :=
  .initial

def publicUpdatedCertifiedRuntime_reachable :
    CertifiedRuntimeReachable publicUpdatedCertifiedRuntime :=
  .submitted initialCertifiedRuntime publicIncrementalNeuralUpdate
    publicUpdatedCertifiedRuntime publicInitialCertifiedRuntime_reachable
    submitUpdate_public_result_exact

def publicUpdatedCertifiedRuntime_accessibility :
    CertifiedRuntimeAccessibility publicUpdatedCertifiedRuntime :=
  reachableRuntime_accessibility publicUpdatedCertifiedRuntime
    publicUpdatedCertifiedRuntime_reachable

/-- No state can be added after the public reconfiguration because the fixed
meta-contract admits no outgoing transition from `reconfigured`. -/
theorem publicUpdatedCertifiedRuntime_has_no_successor :
    Not (Exists fun next =>
      submitUpdate publicUpdatedCertifiedRuntime
        publicIncrementalNeuralUpdate = .ok next) := by
  intro accepted
  rcases accepted with ⟨next, exact⟩
  rw [submitUpdate_rejects_unadmitted_second_transition] at exact
  cases exact

end ConstitutiveSearch.NeuralAgent
/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.NeuralAgent.CertifiedRuntimeReachable
#print axioms ConstitutiveSearch.NeuralAgent.CertifiedRuntimeAccessibility
#print axioms ConstitutiveSearch.NeuralAgent.reachableRuntime_accessibility
#print axioms ConstitutiveSearch.NeuralAgent.publicInitialCertifiedRuntime_reachable
#print axioms ConstitutiveSearch.NeuralAgent.publicUpdatedCertifiedRuntime_reachable
#print axioms ConstitutiveSearch.NeuralAgent.publicUpdatedCertifiedRuntime_accessibility
#print axioms ConstitutiveSearch.NeuralAgent.publicUpdatedCertifiedRuntime_has_no_successor
/- AXIOM_AUDIT_END -/
