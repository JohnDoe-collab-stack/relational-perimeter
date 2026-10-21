import RelationalPerimeter.Mechanisms.Native.Intervention

/-!
# Explanations reconstructed from executed causal roles

An explanation does not receive a graph or a circuit independently.  Its
output occurrence is selected by the causal role, its path is obtained by
erasing the role's executed change propagation, and its circuit is the exact
reconstruction of the causal cone of that same output in that same run.
-/
set_option genInjectivity false
namespace ConstitutiveSearch.NativeMechanism

structure CausalExplanation
    (system : NativeSystem Input Proposal) (input : Input)
    (focus : ActivationOccurrence (system.run input)) : Type 1 where
  private mk ::
  role : CausalRole system input focus
  focusMember :
    (reconstructCircuit (system.run input)
      (.neuronOutput (system.outputs.sources.get role.output))).Contains focus

def CausalExplanation.circuit
    {system : NativeSystem Input Proposal} {input : Input}
    {focus : ActivationOccurrence (system.run input)}
    (explanation : CausalExplanation system input focus) :
    ConstructedCircuit (system.run input)
      (.neuronOutput (system.outputs.sources.get explanation.role.output)) :=
  reconstructCircuit (system.run input)
    (.neuronOutput (system.outputs.sources.get explanation.role.output))

def explainCausalRole
    {system : NativeSystem Input Proposal} {input : Input}
    {focus : ActivationOccurrence (system.run input)}
    (role : CausalRole system input focus) :
    CausalExplanation system input focus :=
  let executedPath := causal_role_has_executed_path role
  { role := role
    focusMember := reconstructed_path_to_member (system.run input)
      (.neuronOutput (system.outputs.sources.get role.output)) focus
      executedPath.2 }

def CausalExplanation.executedPath
    {system : NativeSystem Input Proposal} {input : Input}
    {focus : ActivationOccurrence (system.run input)}
    (explanation : CausalExplanation system input focus) :
    Reaches (system.run input) focus
      (.neuronOutput
        (system.outputs.sources.get explanation.role.output)) :=
  reconstructed_member_to_path (system.run input)
    (.neuronOutput (system.outputs.sources.get explanation.role.output)) focus
    explanation.focusMember

end ConstitutiveSearch.NativeMechanism
/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.NativeMechanism.CausalExplanation
#print axioms ConstitutiveSearch.NativeMechanism.CausalExplanation.circuit
#print axioms ConstitutiveSearch.NativeMechanism.explainCausalRole
#print axioms ConstitutiveSearch.NativeMechanism.CausalExplanation.executedPath
/- AXIOM_AUDIT_END -/
