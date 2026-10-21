import RelationalPerimeter.Agents.Neural.PublicActionRealization

namespace Tests.Mechanisms.NeuralReconfigurationRegression
open ConstitutiveSearch.NativeMechanism ConstitutiveSearch.NeuralAgent

def denyInput : PublicRequirementInput := ⟨.deny, ()⟩
def allowInput : PublicRequirementInput := ⟨.allow, ()⟩

theorem target_is_built_from_exact_source_run_and_next_requirement :
    (publicReconfiguration denyInput allowInput).targetSystem =
      publicReconfigurationBuilder.build
        publicRequirementSystem (publicRequirementSystem.run denyInput)
        allowInput :=
  (publicReconfiguration denyInput allowInput).target_exact

theorem source_and_requirement_use_distinct_ports :
    (publicRequiredMechanismTransport denyInput allowInput).sourcePort ≠
      (publicRequiredMechanismTransport denyInput allowInput).requirementPort :=
  (publicRequiredMechanismTransport denyInput allowInput).portsDistinct

def reconfiguration_is_authorized :
    ConstitutiveSearch.Resources.Ref
      (publicRequirementFamily.received allowInput.requirement).realizedScope
      (publicReconfigurationBuilder.permissionVariable allowInput.requirement) :=
  (publicReconfiguration denyInput allowInput).permission

def source_occurrence_reaches_reconfigured_output :
    Reaches ((publicReconfiguration denyInput allowInput).targetSystem.run allowInput)
      (.receivedInput publicReconfigurationSourcePort)
      (.neuronOutput publicReconfigurationOutput) :=
  (publicRequiredMechanismTransport denyInput allowInput).sourcePath

def requirement_occurrence_reaches_reconfigured_output :
    Reaches ((publicReconfiguration denyInput allowInput).targetSystem.run allowInput)
      (.receivedInput publicReconfigurationRequirementPort)
      (.neuronOutput publicReconfigurationOutput) :=
  (publicRequiredMechanismTransport denyInput allowInput).requirementPath

theorem changing_source_changes_executed_material :
    ((publicReconfiguration denyInput denyInput).targetSystem.encode denyInput).read
        publicReconfigurationSourcePort ≠
      ((publicReconfiguration allowInput denyInput).targetSystem.encode denyInput).read
        publicReconfigurationSourcePort :=
  public_reconfiguration_reads_source_distinction denyInput

theorem changing_requirement_changes_executed_material :
    ((publicReconfiguration denyInput denyInput).targetSystem.encode denyInput).read
        publicReconfigurationRequirementPort ≠
      ((publicReconfiguration denyInput allowInput).targetSystem.encode allowInput).read
        publicReconfigurationRequirementPort :=
  public_reconfiguration_reads_requirement_distinction denyInput

theorem changing_source_changes_reconfigured_output :
    (publicReconfiguration denyInput denyInput).targetSystem.outputValues
        denyInput ≠
      (publicReconfiguration allowInput denyInput).targetSystem.outputValues
        denyInput :=
  public_reconfiguration_source_changes_output

theorem changing_requirement_changes_reconfigured_output :
    (publicReconfiguration denyInput denyInput).targetSystem.outputValues
        denyInput ≠
      (publicReconfiguration denyInput allowInput).targetSystem.outputValues
        allowInput :=
  public_reconfiguration_requirement_changes_output

end Tests.Mechanisms.NeuralReconfigurationRegression
/- AXIOM_AUDIT_BEGIN -/
#print axioms Tests.Mechanisms.NeuralReconfigurationRegression.target_is_built_from_exact_source_run_and_next_requirement
#print axioms Tests.Mechanisms.NeuralReconfigurationRegression.source_and_requirement_use_distinct_ports
#print axioms Tests.Mechanisms.NeuralReconfigurationRegression.reconfiguration_is_authorized
#print axioms Tests.Mechanisms.NeuralReconfigurationRegression.source_occurrence_reaches_reconfigured_output
#print axioms Tests.Mechanisms.NeuralReconfigurationRegression.requirement_occurrence_reaches_reconfigured_output
#print axioms Tests.Mechanisms.NeuralReconfigurationRegression.changing_source_changes_executed_material
#print axioms Tests.Mechanisms.NeuralReconfigurationRegression.changing_requirement_changes_executed_material
#print axioms Tests.Mechanisms.NeuralReconfigurationRegression.changing_source_changes_reconfigured_output
#print axioms Tests.Mechanisms.NeuralReconfigurationRegression.changing_requirement_changes_reconfigured_output
/- AXIOM_AUDIT_END -/
