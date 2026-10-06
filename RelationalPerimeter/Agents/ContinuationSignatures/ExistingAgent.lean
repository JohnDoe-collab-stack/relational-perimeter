import RelationalPerimeter.Agents.Constitutive.Persistence

/-! Conservative initial-domain result. The agent keeps its existing runtime
memory and transition interpreter. An initial Unit signature is not a dynamic
Unit implementation of its register, rights, or resumed search stages. -/
set_option genInjectivity false
namespace ConstitutiveSearch.ContinuationSignatures.ExistingAgent
open EndogenousDecomposition

def InitialFutureEquivalent {input : Nat} (master : UnifiedMaster.Instance input)
    (requirement : Agent.Requirement) (left right : RoleOccurrenceProfile master.roles) : Prop :=
  ∀ requests, Agent.executeRequests (Agent.start master requirement left) requests =
    Agent.executeRequests (Agent.start master requirement right) requests

def initialSignature {input : Nat} (master : UnifiedMaster.Instance input)
    (_requirement : Agent.Requirement) (_profile : RoleOccurrenceProfile master.roles) : Unit := ()

theorem initialSignature_exact {input : Nat} (master : UnifiedMaster.Instance input)
    (requirement : Agent.Requirement) (left right : RoleOccurrenceProfile master.roles) :
    initialSignature master requirement left = initialSignature master requirement right ↔
      InitialFutureEquivalent master requirement left right :=
  ⟨fun _ requests => Agent.forgotten_sources_same_future master requirement left right requests,
    fun _ => rfl⟩

theorem initialSignature_minimal {input : Nat} (master : UnifiedMaster.Instance input)
    (requirement : Agent.Requirement) {Memory : Type} (project : RoleOccurrenceProfile master.roles → Memory)
    {left right : RoleOccurrenceProfile master.roles} (_same : project left = project right) :
    initialSignature master requirement left = initialSignature master requirement right := rfl

theorem existing_memory_not_replaced {input : Nat} (master : UnifiedMaster.Instance input)
    (requirement : Agent.Requirement) (left right : RoleOccurrenceProfile master.roles) :
    Agent.start master requirement left = Agent.start master requirement right :=
  Agent.initial_memories_equal master requirement left right

end ConstitutiveSearch.ContinuationSignatures.ExistingAgent
/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.ContinuationSignatures.ExistingAgent.initialSignature
#print axioms ConstitutiveSearch.ContinuationSignatures.ExistingAgent.initialSignature_exact
#print axioms ConstitutiveSearch.ContinuationSignatures.ExistingAgent.initialSignature_minimal
#print axioms ConstitutiveSearch.ContinuationSignatures.ExistingAgent.existing_memory_not_replaced
/- AXIOM_AUDIT_END -/
