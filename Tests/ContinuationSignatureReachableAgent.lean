import RelationalPerimeter

/-! Client checks on the unchanged complete agent contract, not on the
restricted role-read contract. All reached history lengths are quantified. -/
set_option genInjectivity false
namespace Tests.ContinuationSignatureReachableAgent
open ConstitutiveSearch ConstitutiveSearch.EndogenousDecomposition
open ConstitutiveSearch.ContinuationSignatures

theorem full_contract_exact {input : Nat} (master : UnifiedMaster.Instance input)
    (requirement : Agent.Requirement)
    (left right : ReachableAgent.Reachable master requirement) :
    ReachableAgent.signature left = ReachableAgent.signature right ↔
      FutureEquivalent (ReachableAgent.contract master requirement) left right :=
  ReachableAgent.signature_exact master requirement left right

theorem complete_basis {input : Nat} (master : UnifiedMaster.Instance input)
    (requirement : Agent.Requirement)
    (left right : ReachableAgent.Reachable master requirement)
    (same : TestAgreement (ReachableAgent.contract master requirement) [[]] left right) :
    FutureEquivalent (ReachableAgent.contract master requirement) left right :=
  (ReachableAgent.basis master requirement).complete left right same

def produced_separator {input : Nat} (master : UnifiedMaster.Instance input)
    (requirement : Agent.Requirement) (first second : Nat) (different : first ≠ second) :
    FutureSeparator (ReachableAgent.contract master requirement)
      (ReachableAgent.coveredSource master requirement first)
      (ReachableAgent.coveredSource master requirement second) :=
  ReachableAgent.separator master requirement _ _ (fun same => different
    ((ReachableAgent.every_signature_reachable master requirement first).symm.trans
      (same.trans (ReachableAgent.every_signature_reachable master requirement second))))

theorem complete_execution_updates {input : Nat} (master : UnifiedMaster.Instance input)
    (requirement : Agent.Requirement) (source : ReachableAgent.Reachable master requirement)
    (requests : List Agent.Request) :
    ReachableAgent.signature (Grouping.Continuation.run ReachableAgent.next source
      (requests.map ULift.up)) =
    ReachableAgent.dynamics master requirement (ReachableAgent.signature source) requests :=
  ReachableAgent.dynamics_exact master requirement source requests

theorem actual_input_production {input : Nat} (master : UnifiedMaster.Instance input)
    (requirement : Agent.Requirement) (source : ReachableAgent.Reachable master requirement)
    (request : Agent.Request) :
    (ReachableAgent.executeSignedInput input (Agent.project source.1) request).2.2 =
      ReachableAgent.update input requirement (ReachableAgent.signature source) request :=
  ReachableAgent.executeSignedInput_signature master requirement source request

theorem permission_return {input : Nat} (master : UnifiedMaster.Instance input)
    (requirement : Agent.Requirement) (source : ReachableAgent.Reachable master requirement)
    (request : ULift.{3} Agent.Request)
    (witness : (ReachableAgent.contract master requirement).Allow source request) :
    (ReachableAgent.realization master requirement).backward source request
      ((ReachableAgent.realization master requirement).forward source request witness) = witness :=
  (ReachableAgent.realization master requirement).backward_forward source request witness

theorem other_memory_must_keep_count {input : Nat} (master : UnifiedMaster.Instance input)
    (requirement : Agent.Requirement) {Memory : Type 3}
    (other : ExactRealization (ReachableAgent.contract master requirement) Memory)
    {left right : ReachableAgent.Reachable master requirement}
    (same : other.project left = other.project right) :
    ReachableAgent.signature left = ReachableAgent.signature right :=
  ReachableAgent.necessary_distinctions master requirement other same

theorem autonomous_count_memory {input : Nat} (master : UnifiedMaster.Instance input)
    (requirement : Agent.Requirement) (source : ReachableAgent.Reachable master requirement)
    (requests : List (ULift.{3} Agent.Request)) :
    (ReachableAgent.contract master requirement).outcome source requests =
      (ReachableAgent.countContract master requirement).outcome
        ⟨ReachableAgent.signature source⟩ requests :=
  (ReachableAgent.countRealization master requirement).outcome_exact source requests

theorem count_rights_return {input : Nat} (master : UnifiedMaster.Instance input)
    (requirement : Agent.Requirement) (source : ReachableAgent.Reachable master requirement)
    (request : ULift.{3} Agent.Request)
    (witness : (ReachableAgent.countContract master requirement).Allow
      ⟨ReachableAgent.signature source⟩ request) :
    (ReachableAgent.countRealization master requirement).forward source request
      ((ReachableAgent.countRealization master requirement).backward source request witness) = witness :=
  (ReachableAgent.countRealization master requirement).forward_backward source request witness

theorem count_memory_not_singleton {input : Nat} (master : UnifiedMaster.Instance input)
    (requirement : Agent.Requirement) :
    ¬ FutureEquivalent (ReachableAgent.contract master requirement)
      (ReachableAgent.coveredSource master requirement 0)
      (ReachableAgent.coveredSource master requirement 1) :=
  (produced_separator master requirement 0 1 (by intro impossible; cases impossible)).not_equivalent

theorem closed_certificate_pins_realization {input : Nat} (master : UnifiedMaster.Instance input)
    (requirement : Agent.Requirement) :
    (ReachableAgent.certify master requirement).realization =
      ReachableAgent.countRealization master requirement := rfl

theorem positive_factorization {input : Nat} (master : UnifiedMaster.Instance input)
    (requirement : Agent.Requirement) {Memory : Type 3}
    (other : ExactRealization (ReachableAgent.contract master requirement) Memory)
    (coverage : PositiveCoverage other) (source : ReachableAgent.Reachable master requirement) :
    ReachableAgent.recoverCount master requirement other coverage (other.project source) =
      ReachableAgent.signature source :=
  ReachableAgent.recoverCount_exact master requirement other coverage source

theorem singleton_is_not_an_agent {input : Nat} (master : UnifiedMaster.Instance input)
    (requirement : Agent.Requirement) :
    ExactRealization (ReachableAgent.contract master requirement) (ULift.{3} Unit) → False :=
  ReachableAgent.no_singleton_realization master requirement

theorem public_certificate_closes (input : Nat) (var : SAT.Var) :
    (ReachableAgent.publicCertificate input var).realization =
      ReachableAgent.countRealization (UnifiedMaster.publicInstance input)
        (ReachableAgent.receivedSingleton var) := rfl

end Tests.ContinuationSignatureReachableAgent
/- AXIOM_AUDIT_BEGIN -/
#print axioms Tests.ContinuationSignatureReachableAgent.full_contract_exact
#print axioms Tests.ContinuationSignatureReachableAgent.complete_basis
#print axioms Tests.ContinuationSignatureReachableAgent.produced_separator
#print axioms Tests.ContinuationSignatureReachableAgent.complete_execution_updates
#print axioms Tests.ContinuationSignatureReachableAgent.actual_input_production
#print axioms Tests.ContinuationSignatureReachableAgent.permission_return
#print axioms Tests.ContinuationSignatureReachableAgent.other_memory_must_keep_count
#print axioms Tests.ContinuationSignatureReachableAgent.autonomous_count_memory
#print axioms Tests.ContinuationSignatureReachableAgent.count_rights_return
#print axioms Tests.ContinuationSignatureReachableAgent.count_memory_not_singleton
#print axioms Tests.ContinuationSignatureReachableAgent.closed_certificate_pins_realization
#print axioms Tests.ContinuationSignatureReachableAgent.positive_factorization
#print axioms Tests.ContinuationSignatureReachableAgent.singleton_is_not_an_agent
#print axioms Tests.ContinuationSignatureReachableAgent.public_certificate_closes
/- AXIOM_AUDIT_END -/
