import RelationalPerimeter.Agents.Neural.InteractionHistory

/-!
# Requirement-directed mechanism reconfiguration

The next native mechanism is computed from the exact preceding run and the
next received requirement.  Authorization is a positive reference into that
requirement's realized scope.  A separate transport witnesses that both the
preceding proposal and the new requirement occur in the newly executed
mechanism and reach its declared output.
-/
set_option genInjectivity false
set_option maxHeartbeats 2000000
namespace ConstitutiveSearch.NeuralAgent
open NativeMechanism Resources

universe u v w

structure ReconfigurationBuilder
    {RequirementCase : Type u} {Context : Type v} {Proposal : Type w}
    (family : RequirementFamily RequirementCase Context Proposal) where
  permissionVariable : RequirementCase -> SAT.Var
  sourceCode : Proposal -> Activation
  requirementCode : RequirementCase -> Activation
  build : (sourceSystem : NativeSystem (RequirementInput family) Proposal) ->
    NativeRun sourceSystem.program -> RequirementInput family ->
      NativeSystem (RequirementInput family) Proposal

/-- The target system is not supplied by the client: it is fixed to the output
of `builder.build` on the actual source run and next requirement. -/
structure Reconfiguration
    {RequirementCase : Type u} {Context : Type v} {Proposal : Type w}
    {family : RequirementFamily RequirementCase Context Proposal}
    (builder : ReconfigurationBuilder family)
    (sourceSystem : NativeSystem (RequirementInput family) Proposal)
    (sourceInput nextInput : RequirementInput family) : Type (max 3 (max u (max v w))) where
  private mk ::
  targetSystem : NativeSystem (RequirementInput family) Proposal
  targetExact : targetSystem =
    builder.build sourceSystem (sourceSystem.run sourceInput) nextInput
  permission : Ref (family.received nextInput.requirement).realizedScope
    (builder.permissionVariable nextInput.requirement)

def reconfigure
    {RequirementCase : Type u} {Context : Type v} {Proposal : Type w}
    {family : RequirementFamily RequirementCase Context Proposal}
    {sourceSystem : NativeSystem (RequirementInput family) Proposal}
    (builder : ReconfigurationBuilder family)
    (sourceInput nextInput : RequirementInput family)
    (permission : Ref (family.received nextInput.requirement).realizedScope
      (builder.permissionVariable nextInput.requirement)) :
    Reconfiguration builder sourceSystem sourceInput nextInput :=
  .mk (builder.build sourceSystem (sourceSystem.run sourceInput)
    nextInput) rfl permission

theorem Reconfiguration.target_exact
    {RequirementCase : Type u} {Context : Type v} {Proposal : Type w}
    {family : RequirementFamily RequirementCase Context Proposal}
    {sourceSystem : NativeSystem (RequirementInput family) Proposal}
    {builder : ReconfigurationBuilder family}
    {sourceInput nextInput : RequirementInput family}
    (configuration : Reconfiguration builder sourceSystem sourceInput nextInput) :
    configuration.targetSystem =
      builder.build sourceSystem (sourceSystem.run sourceInput) nextInput :=
  configuration.targetExact

/-- Exact occurrence transport into the reconfigured mechanism.  The two
materials remain separate and both participate in its executed output. -/
structure RequiredMechanismTransport
    {RequirementCase : Type u} {Context : Type v} {Proposal : Type w}
    {family : RequirementFamily RequirementCase Context Proposal}
    {sourceSystem : NativeSystem (RequirementInput family) Proposal}
    {builder : ReconfigurationBuilder family}
    {sourceInput nextInput : RequirementInput family}
    (configuration : Reconfiguration builder sourceSystem sourceInput nextInput) :
    Type (max 3 (max u (max v w))) where
  sourcePort : Fin configuration.targetSystem.inputCount
  requirementPort : Fin configuration.targetSystem.inputCount
  portsDistinct : sourcePort ≠ requirementPort
  output : Fin configuration.targetSystem.producedCount
  sourceExact :
    (configuration.targetSystem.encode nextInput).read sourcePort =
      builder.sourceCode (sourceSystem.proposal sourceInput)
  requirementExact :
    (configuration.targetSystem.encode nextInput).read requirementPort =
      builder.requirementCode nextInput.requirement
  sourcePath : Reaches (configuration.targetSystem.run nextInput)
    (.receivedInput sourcePort) (.neuronOutput output)
  requirementPath : Reaches (configuration.targetSystem.run nextInput)
    (.receivedInput requirementPort) (.neuronOutput output)
  proposalExact :
    configuration.targetSystem.proposal nextInput =
      family.requiredProposal nextInput.requirement nextInput.context

/-- The usable reconfiguration includes both its exact production and the
required occurrence transport. -/
structure CertifiedReconfiguration
    {RequirementCase : Type u} {Context : Type v} {Proposal : Type w}
    {family : RequirementFamily RequirementCase Context Proposal}
    {builder : ReconfigurationBuilder family}
    {sourceSystem : NativeSystem (RequirementInput family) Proposal}
    {sourceInput nextInput : RequirementInput family} :
    Type (max 3 (max u (max v w))) where
  private mk ::
  configuration : Reconfiguration builder sourceSystem sourceInput nextInput
  transport : RequiredMechanismTransport configuration

def certifyReconfiguration
    {RequirementCase : Type u} {Context : Type v} {Proposal : Type w}
    {family : RequirementFamily RequirementCase Context Proposal}
    {sourceSystem : NativeSystem (RequirementInput family) Proposal}
    {builder : ReconfigurationBuilder family}
    {sourceInput nextInput : RequirementInput family}
    (configuration : Reconfiguration builder sourceSystem sourceInput nextInput)
    (transport : RequiredMechanismTransport configuration) :
    CertifiedReconfiguration (builder := builder) (sourceSystem := sourceSystem)
      (sourceInput := sourceInput) (nextInput := nextInput) :=
  .mk configuration transport

end ConstitutiveSearch.NeuralAgent
/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.NeuralAgent.ReconfigurationBuilder
#print axioms ConstitutiveSearch.NeuralAgent.Reconfiguration
#print axioms ConstitutiveSearch.NeuralAgent.reconfigure
#print axioms ConstitutiveSearch.NeuralAgent.Reconfiguration.target_exact
#print axioms ConstitutiveSearch.NeuralAgent.RequiredMechanismTransport
#print axioms ConstitutiveSearch.NeuralAgent.CertifiedReconfiguration
#print axioms ConstitutiveSearch.NeuralAgent.certifyReconfiguration
/- AXIOM_AUDIT_END -/
