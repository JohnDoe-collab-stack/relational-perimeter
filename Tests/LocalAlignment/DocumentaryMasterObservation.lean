import Tests.LocalAlignment.DocumentaryMasterFormation

/-! Read actual input ports from the retained formation, without constructing a
new recipe certificate or executing a producer. The logical recipe witness
establishes agreement with its first-order records; these ports alone do not
recover a producer or a complete master state. -/
set_option genInjectivity false
set_option maxHeartbeats 3000000
namespace ConstitutiveSearch.Agent.Local.Documentary.MasterObservation
open Resources MasterOperations MasterFormation
universe u v

def observedPorts {Kind : Type u} {Value : Kind → Type v} {kinds values}
    (formation : @Formation Kind Value kinds values) : List (List Nat) := by
  cases formation with
  | given _ => exact []
  | produced prior producer => exact observedPorts prior ++ [portPositions producer.inputs]

theorem map_append {α β : Type u} (function : α → β) (first second : List α) :
    (first ++ second).map function = first.map function ++ second.map function := by
  induction first with
  | nil => rfl
  | cons head tail ih => exact congrArg (List.cons (function head)) ih

theorem formed_ports {kinds} (support : Support EndogenousDecomposition.MasterResources.Value kinds)
    (formed : Formed support) :
    observedPorts support.formation = formed.records.map (fun record => record.fields.2) := by
  induction formed with
  | given _ => rfl
  | @produced priorKinds previous prior operation ih =>
      change observedPorts previous.formation ++ [portPositions operation.producer.inputs] =
        (prior.records ++ [operation.record]).map (fun record => record.fields.2)
      rw [map_append, ih, producer_ports]
      rfl

theorem captured_ports {kinds} (support : Support EndogenousDecomposition.MasterResources.Value kinds)
    (formed : Formed support) :
    observedPorts (resources support formed).restore.formation = observedPorts support.formation := by
  rw [resources_exact]

end ConstitutiveSearch.Agent.Local.Documentary.MasterObservation
/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Agent.Local.Documentary.MasterObservation.observedPorts
#print axioms ConstitutiveSearch.Agent.Local.Documentary.MasterObservation.map_append
#print axioms ConstitutiveSearch.Agent.Local.Documentary.MasterObservation.formed_ports
#print axioms ConstitutiveSearch.Agent.Local.Documentary.MasterObservation.captured_ports
/- AXIOM_AUDIT_END -/
