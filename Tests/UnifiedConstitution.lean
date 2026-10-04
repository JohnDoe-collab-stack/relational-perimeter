import RelationalPerimeter

/-! Client checks for resources and grouping. The reconstruction statements
below concern the stronger raw-read contract on chronological prefixes, not
the different profile-forgetting domain of Tests.ProducedContinuation. -/
namespace UnifiedConstitutionTests
open ConstitutiveSearch ConstitutiveSearch.EndogenousDecomposition
open ConstitutiveSearch.Grouping

theorem resources_erase_to_public (input : Nat) :
    (MasterResources.execute (resolutionLength input)
      (MasterContinuation.publicInitialCursor input)).1 = publicCausalOperationalExecution input :=
  MasterResources.execute_erases _ _

theorem complete_head_objects_are_pinned (input : Nat) :
    (publicCausalOperationalExecution input).allHeadsExact
      (initialThreadedConstitutiveStateFromInitialization_fresh (initializeConstitutiveHistory input)) :=
  (publicExecutionConstitutionCertificate input).allHeadsExact

theorem exact_grouping_fibres {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    {roles : RelationalConstitutiveRoleHistory run} (history : RoleStatus.History roles)
    (p q : RoleOccurrenceProfile roles) :
    rolewiseCarry history.policy p = rolewiseCarry history.policy q ↔
      Nonempty (Chain (CertifiedRoleGrouping.rules history).Step p q) :=
  CertifiedRoleGrouping.carry_fibres history p q

theorem normalizing_traces_act_coherently {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    {roles : RelationalConstitutiveRoleHistory run} (history : RoleStatus.History roles)
    (p : RoleOccurrenceProfile roles)
    (first second : Trace (CertifiedRoleGrouping.rules history).Step p (history.selected p))
    (data : RoleProfilePayload p) :
    (CertifiedRoleGrouping.acceptanceAction history).transport first data =
      (CertifiedRoleGrouping.acceptanceAction history).transport second data :=
  CertifiedRoleGrouping.normalization_coherent history p first second data

theorem canonical_prefix_coordinates {Memory : Type} {project : MasterContinuation.PublicPrefix → Memory}
    (contract : MasterContinuation.PreservesDiscoveryReads Memory project)
    (p : MasterContinuation.PublicPrefix) :
    contract.coordinates (project p) = (p.input, p.elapsed) :=
  MasterContinuation.coordinates_exact contract p

theorem canonical_prefix_recovered {Memory : Type} {project : MasterContinuation.PublicPrefix → Memory}
    (contract : MasterContinuation.PreservesDiscoveryReads Memory project)
    (p : MasterContinuation.PublicPrefix) :
    contract.decode (project p) = some p :=
  MasterContinuation.decode_exact contract p

theorem canonical_cursor_recovered {Memory : Type} {project : MasterContinuation.PublicPrefix → Memory}
    (contract : MasterContinuation.PreservesDiscoveryReads Memory project)
    (p : MasterContinuation.PublicPrefix) :
    contract.recoverRead MasterContinuation.PublicPrefix.cursor (project p) = some p.cursor :=
  MasterContinuation.recoverRead_exact contract MasterContinuation.PublicPrefix.cursor p

end UnifiedConstitutionTests
/- AXIOM_AUDIT_BEGIN -/
#print axioms UnifiedConstitutionTests.resources_erase_to_public
#print axioms UnifiedConstitutionTests.complete_head_objects_are_pinned
#print axioms UnifiedConstitutionTests.exact_grouping_fibres
#print axioms UnifiedConstitutionTests.normalizing_traces_act_coherently
#print axioms UnifiedConstitutionTests.canonical_prefix_coordinates
#print axioms UnifiedConstitutionTests.canonical_prefix_recovered
#print axioms UnifiedConstitutionTests.canonical_cursor_recovered
/- AXIOM_AUDIT_END -/
