import RelationalPerimeter.Agents.Constitutive.Execution
import RelationalPerimeter.Constitution.Continuation.Minimality

/-! Received read permissions precede machine configuration. They are not
discovered relations, and do not replace the constituted role domain. -/
set_option genInjectivity false
namespace ConstitutiveSearch.ConnectedFabric
open SAT Resources

structure Channel where
  requirement : Agent.Requirement
  query : Var
  permission : Ref requirement.realizedScope query

def Channel.connect (requirement : Agent.Requirement) (query : Var) : Option Channel :=
  (requirement.permission query).map (fun permission => ⟨requirement, query, permission⟩)

def Channel.singleton (query : Var) : Channel :=
  let requirement := (Agent.receive [query]).get (Agent.receive_nonempty query [])
  ⟨requirement, query, by change Ref [query] query; exact .here⟩

abbrev Scope := List Channel
abbrev Signals := List Bool

end ConstitutiveSearch.ConnectedFabric
/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.ConnectedFabric.Channel.connect
#print axioms ConstitutiveSearch.ConnectedFabric.Channel.singleton
/- AXIOM_AUDIT_END -/
