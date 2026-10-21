import RelationalPerimeter.Agents.Neural.InteractionHistory

/-!
# Requirement-directed mechanism reconfiguration

The next native mechanism is computed from the exact preceding run and the
next received requirement.  Authorization is a positive reference into that
requirement's realized scope.  Existence, admission, and incorporation of that
permission remain separate, and the incorporated resource is consumed by the
mechanism builder.  A separate transport witnesses that the preceding
proposal, the new requirement, and the incorporated authorization occur in
the newly executed mechanism and reach its declared output.
-/
set_option genInjectivity false
set_option maxHeartbeats 2000000
namespace ConstitutiveSearch.NeuralAgent
open NativeMechanism Resources

universe u v w

/-- A permission is an exact occurrence in the realized scope of the received
requirement.  Its existence is kept distinct from its admission and from its
incorporation into a reconfiguration. -/
abbrev ReconfigurationPermission
    {RequirementCase : Type u} {Context : Type v} {Proposal : Type w}
    (family : RequirementFamily RequirementCase Context Proposal)
    (permissionVariable : RequirementCase -> SAT.Var)
    (nextInput : RequirementInput family) :=
  Ref (family.received nextInput.requirement).realizedScope
    (permissionVariable nextInput.requirement)

/-- Admission records that this exact permission occurrence is accepted for
the exact next requirement.  It does not yet authorize construction. -/
structure AdmittedReconfigurationPermission
    {RequirementCase : Type u} {Context : Type v} {Proposal : Type w}
    (family : RequirementFamily RequirementCase Context Proposal)
    (permissionVariable : RequirementCase -> SAT.Var)
    (nextInput : RequirementInput family) where
  private mk ::
  permission : ReconfigurationPermission family permissionVariable nextInput
  admitted :
    (family.received nextInput.requirement).permission
        (permissionVariable nextInput.requirement) =
      some permission

def admitReconfigurationPermission
    {RequirementCase : Type u} {Context : Type v} {Proposal : Type w}
    {family : RequirementFamily RequirementCase Context Proposal}
    {permissionVariable : RequirementCase -> SAT.Var}
    {nextInput : RequirementInput family}
    (permission : ReconfigurationPermission family permissionVariable nextInput)
    (admitted :
      (family.received nextInput.requirement).permission
          (permissionVariable nextInput.requirement) =
        some permission) :
    AdmittedReconfigurationPermission family permissionVariable nextInput :=
  .mk permission admitted

/-- Incorporation is the resource consumed by the mechanism builder.  It is
not interchangeable with the mere existence or admission of a permission. -/
structure IncorporatedReconfigurationPermission
    {RequirementCase : Type u} {Context : Type v} {Proposal : Type w}
    (family : RequirementFamily RequirementCase Context Proposal)
    (permissionVariable : RequirementCase -> SAT.Var)
    (nextInput : RequirementInput family) where
  private mk ::
  admission : AdmittedReconfigurationPermission family permissionVariable
    nextInput

def incorporateReconfigurationPermission
    {RequirementCase : Type u} {Context : Type v} {Proposal : Type w}
    {family : RequirementFamily RequirementCase Context Proposal}
    {permissionVariable : RequirementCase -> SAT.Var}
    {nextInput : RequirementInput family}
    (admission : AdmittedReconfigurationPermission family permissionVariable
      nextInput) :
    IncorporatedReconfigurationPermission family permissionVariable nextInput :=
  .mk admission

structure ReconfigurationBuilder
    {RequirementCase : Type u} {Context : Type v} {Proposal : Type w}
    (family : RequirementFamily RequirementCase Context Proposal) where
  permissionVariable : RequirementCase -> SAT.Var
  sourceCode : Proposal -> Activation
  requirementCode : RequirementCase -> Context -> Activation
  authorizationCode : (nextInput : RequirementInput family) ->
    ReconfigurationPermission family permissionVariable nextInput -> Activation
  build : (sourceSystem : NativeSystem (RequirementInput family) Proposal) ->
    NativeRun sourceSystem.program -> (nextInput : RequirementInput family) ->
      IncorporatedReconfigurationPermission family permissionVariable nextInput ->
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
  authorization : IncorporatedReconfigurationPermission family
    builder.permissionVariable nextInput
  targetSystem : NativeSystem (RequirementInput family) Proposal
  targetExact : targetSystem =
    builder.build sourceSystem (sourceSystem.run sourceInput) nextInput
      authorization

def Reconfiguration.permission
    {RequirementCase : Type u} {Context : Type v} {Proposal : Type w}
    {family : RequirementFamily RequirementCase Context Proposal}
    {builder : ReconfigurationBuilder family}
    {sourceSystem : NativeSystem (RequirementInput family) Proposal}
    {sourceInput nextInput : RequirementInput family}
    (configuration : Reconfiguration builder sourceSystem sourceInput nextInput) :
    ReconfigurationPermission family builder.permissionVariable nextInput :=
  configuration.authorization.admission.permission

def reconfigure
    {RequirementCase : Type u} {Context : Type v} {Proposal : Type w}
    {family : RequirementFamily RequirementCase Context Proposal}
    {sourceSystem : NativeSystem (RequirementInput family) Proposal}
    (builder : ReconfigurationBuilder family)
    (sourceInput nextInput : RequirementInput family)
    (authorization : IncorporatedReconfigurationPermission family
      builder.permissionVariable nextInput) :
    Reconfiguration builder sourceSystem sourceInput nextInput :=
  .mk authorization
    (builder.build sourceSystem (sourceSystem.run sourceInput)
      nextInput authorization) rfl

theorem Reconfiguration.target_exact
    {RequirementCase : Type u} {Context : Type v} {Proposal : Type w}
    {family : RequirementFamily RequirementCase Context Proposal}
    {sourceSystem : NativeSystem (RequirementInput family) Proposal}
    {builder : ReconfigurationBuilder family}
    {sourceInput nextInput : RequirementInput family}
    (configuration : Reconfiguration builder sourceSystem sourceInput nextInput) :
    configuration.targetSystem =
      builder.build sourceSystem (sourceSystem.run sourceInput) nextInput
        configuration.authorization :=
  configuration.targetExact

/-- Exact occurrence transport into the reconfigured mechanism.  The three
materials remain separate.  Each transported occurrence must also carry a
full interventionally witnessed causal role in the target proposal; a graph
path by itself is not accepted as participation. -/
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
  authorizationPort : Fin configuration.targetSystem.inputCount
  portsDistinct : sourcePort ≠ requirementPort
  sourceAuthorizationDistinct : sourcePort ≠ authorizationPort
  requirementAuthorizationDistinct : requirementPort ≠ authorizationPort
  sourceExact :
    (configuration.targetSystem.encode nextInput).read sourcePort =
      builder.sourceCode (sourceSystem.proposal sourceInput)
  requirementExact :
    (configuration.targetSystem.encode nextInput).read requirementPort =
      builder.requirementCode nextInput.requirement nextInput.context
  authorizationExact :
    (configuration.targetSystem.encode nextInput).read authorizationPort =
      builder.authorizationCode nextInput configuration.permission
  sourceRole : CausalRole configuration.targetSystem nextInput
    (.receivedInput sourcePort)
  requirementRole : CausalRole configuration.targetSystem nextInput
    (.receivedInput requirementPort)
  authorizationRole : CausalRole configuration.targetSystem nextInput
    (.receivedInput authorizationPort)

/-- Local derivation of the reconfigured proposal.  The target execution is
first exposed as a combination of the three values that were actually encoded
at the transported ports.  Only afterwards may the exact transport equations
replace those values by the executed source proposal and the new requirement
code.  `decoderExact` specifies the target decoder on that combined
representation; it is not the final proposal equality. -/
structure ReconfiguredProposalDerivation
    {RequirementCase : Type u} {Context : Type v} {Proposal : Type w}
    {family : RequirementFamily RequirementCase Context Proposal}
    {sourceSystem : NativeSystem (RequirementInput family) Proposal}
    {builder : ReconfigurationBuilder family}
    {sourceInput nextInput : RequirementInput family}
    (configuration : Reconfiguration builder sourceSystem sourceInput nextInput)
    (transport : RequiredMechanismTransport configuration) :
    Type (max 3 (max u (max v w))) where
  combine : Activation -> Activation -> Activation -> List Activation
  combinationExecuted :
    configuration.targetSystem.outputValues nextInput =
      combine
        ((configuration.targetSystem.encode nextInput).read
          transport.sourcePort)
        ((configuration.targetSystem.encode nextInput).read
          transport.requirementPort)
        ((configuration.targetSystem.encode nextInput).read
          transport.authorizationPort)
  decoderExact :
    configuration.targetSystem.decode
        (combine
          (builder.sourceCode (sourceSystem.proposal sourceInput))
          (builder.requirementCode nextInput.requirement nextInput.context)
          (builder.authorizationCode nextInput configuration.permission)) =
      family.requiredProposal nextInput.requirement nextInput.context

/-- The final equality is derived by eliminating the target execution, then
consuming all three exact transports, and finally applying the target decoder's
local equation. -/
theorem ReconfiguredProposalDerivation.proposal_exact
    {RequirementCase : Type u} {Context : Type v} {Proposal : Type w}
    {family : RequirementFamily RequirementCase Context Proposal}
    {sourceSystem : NativeSystem (RequirementInput family) Proposal}
    {builder : ReconfigurationBuilder family}
    {sourceInput nextInput : RequirementInput family}
    {configuration : Reconfiguration builder sourceSystem sourceInput nextInput}
    {transport : RequiredMechanismTransport configuration}
    (derivation : ReconfiguredProposalDerivation configuration transport) :
    configuration.targetSystem.proposal nextInput =
      family.requiredProposal nextInput.requirement nextInput.context := by
  unfold NativeSystem.proposal
  rw [derivation.combinationExecuted, transport.sourceExact,
    transport.requirementExact, transport.authorizationExact]
  exact derivation.decoderExact

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
  derivation : ReconfiguredProposalDerivation configuration transport

def certifyReconfiguration
    {RequirementCase : Type u} {Context : Type v} {Proposal : Type w}
    {family : RequirementFamily RequirementCase Context Proposal}
    {sourceSystem : NativeSystem (RequirementInput family) Proposal}
    {builder : ReconfigurationBuilder family}
    {sourceInput nextInput : RequirementInput family}
    (configuration : Reconfiguration builder sourceSystem sourceInput nextInput)
    (transport : RequiredMechanismTransport configuration)
    (derivation : ReconfiguredProposalDerivation configuration transport) :
    CertifiedReconfiguration (builder := builder) (sourceSystem := sourceSystem)
      (sourceInput := sourceInput) (nextInput := nextInput) :=
  .mk configuration transport derivation

end ConstitutiveSearch.NeuralAgent
/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.NeuralAgent.ReconfigurationBuilder
#print axioms ConstitutiveSearch.NeuralAgent.ReconfigurationPermission
#print axioms ConstitutiveSearch.NeuralAgent.AdmittedReconfigurationPermission
#print axioms ConstitutiveSearch.NeuralAgent.admitReconfigurationPermission
#print axioms ConstitutiveSearch.NeuralAgent.IncorporatedReconfigurationPermission
#print axioms ConstitutiveSearch.NeuralAgent.incorporateReconfigurationPermission
#print axioms ConstitutiveSearch.NeuralAgent.Reconfiguration
#print axioms ConstitutiveSearch.NeuralAgent.Reconfiguration.permission
#print axioms ConstitutiveSearch.NeuralAgent.reconfigure
#print axioms ConstitutiveSearch.NeuralAgent.Reconfiguration.target_exact
#print axioms ConstitutiveSearch.NeuralAgent.RequiredMechanismTransport
#print axioms ConstitutiveSearch.NeuralAgent.ReconfiguredProposalDerivation
#print axioms ConstitutiveSearch.NeuralAgent.ReconfiguredProposalDerivation.proposal_exact
#print axioms ConstitutiveSearch.NeuralAgent.CertifiedReconfiguration
#print axioms ConstitutiveSearch.NeuralAgent.certifyReconfiguration
/- AXIOM_AUDIT_END -/
