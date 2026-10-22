import RelationalPerimeter.Agents.Neural.StateConstitutiveCertificate

/-!
# Executable reflected interface for a constitutive meta-contract

This module defines the executable boundary required by a fixed constitutive
meta-contract.  Received names and artifacts remain proof-free data.  Every
positive local decision reflects to the exact dependent witness consumed by
the state certificate; no acceptance bit is allowed to stand in for that
witness.

The interface deliberately contains neither `CheckedAgent` nor
`CheckedUpdate`.  It verifies the material from which those objects may later
be produced, and therefore cannot contain its own result in advance.
-/
set_option genInjectivity false
namespace ConstitutiveSearch.NeuralAgent

/-- A Boolean decision together with constructive reflection of its positive
branch.  The witness remains in `Type` and is obtained only from the exact
positive result of this decision. -/
structure ReflectedDecision (Witness : Sort u) : Type (max 1 u) where
  result : Bool
  reflect : result = true -> Witness

def ReflectedDecision.accept
    {Witness : Sort u}
    (decision : ReflectedDecision Witness)
    (accepted : decision.result = true) : Witness :=
  decision.reflect accepted

/-- Successful contract-name decoding identifies the received code with the
encoding of one exact member of the fixed meta-contract. -/
structure DecodedContractName
    (constitution : ConstitutiveMetaContract)
    {ContractCode : Type v}
    (encode : constitution.Contract -> ContractCode)
    (source : ContractCode) : Type (max 1 v) where
  contract : constitution.Contract
  exact : encode contract = source

/-- A transition request is plain endpoint data. -/
structure ContractTransitionRequest
    (constitution : ConstitutiveMetaContract) where
  current : constitution.Contract
  next : constitution.Contract

/-- The executable interface owned by, and indexed by, one fixed
meta-contract.  Artifact decoding is represented by an associated dependent
type, but its projections are not opaque: the decoded contract, network, and
stable keys are all tied back to the received source by exact equations and
indexed decoding witnesses. -/
structure ExecutableMetaContractInterface
    (constitution : ConstitutiveMetaContract) : Type 6 where
  ContractCode : Type
  encodeContract : constitution.Contract -> ContractCode
  encodeContractInjective : Function.Injective encodeContract
  ContractNameError : Type
  decodeContractName :
    (source : ContractCode) ->
      Except ContractNameError
        (DecodedContractName constitution encodeContract source)

  ReceivedArtifact : Type
  artifactContractCode : ReceivedArtifact -> ContractCode
  artifactNetwork : ReceivedArtifact -> SerializedNetwork
  artifactStableNaming : ReceivedArtifact -> SerializedStableArtifactNaming
  ArtifactError : Type
  DecodedArtifact : ReceivedArtifact -> Type 4
  decodedContract :
    {source : ReceivedArtifact} -> DecodedArtifact source ->
      constitution.Contract
  decodedContractExact :
    {source : ReceivedArtifact} -> (decoded : DecodedArtifact source) ->
      encodeContract (decodedContract decoded) = artifactContractCode source
  decodedNeuralArtifact :
    {source : ReceivedArtifact} -> (decoded : DecodedArtifact source) ->
      DecodedNeuralArtifact (constitution.operational (decodedContract decoded))
  decodedNetworkExact :
    {source : ReceivedArtifact} -> (decoded : DecodedArtifact source) ->
      (decodedNeuralArtifact decoded).source = artifactNetwork source
  decodedStableNaming :
    {source : ReceivedArtifact} -> (decoded : DecodedArtifact source) ->
      DecodedStableArtifactNaming (decodedNeuralArtifact decoded)
        (artifactStableNaming source)
  decodeReceivedArtifact :
    (source : ReceivedArtifact) -> Except ArtifactError (DecodedArtifact source)

  stateOfArtifact :
    {source : ReceivedArtifact} -> (decoded : DecodedArtifact source) ->
      ReconfiguredExecutionState
        (constitution.operational (decodedContract decoded)).family

  admissionDecision :
    (contract : constitution.Contract) ->
      ReflectedDecision (constitution.Admits contract)
  transitionDecision :
    (request : ContractTransitionRequest constitution) ->
      ReflectedDecision
        (OperationalContractTransition constitution request.current request.next)

  basisDecision :
    {source : ReceivedArtifact} -> (decoded : DecodedArtifact source) ->
      ReflectedDecision
        (FiniteCausalBasis (constitution.operational (decodedContract decoded))
          (decodedNeuralArtifact decoded))
  systemDecision :
    {source : ReceivedArtifact} -> (decoded : DecodedArtifact source) ->
      ReflectedDecision
        ((stateOfArtifact decoded).system = (decodedNeuralArtifact decoded).system)
  declaredInputDecision :
    {source : ReceivedArtifact} -> (decoded : DecodedArtifact source) ->
      ReflectedDecision
        (Listed (stateOfArtifact decoded).input
          (constitution.operational
            (decodedContract decoded)).declaredCurrentInputs)
  requirementDecision :
    {source : ReceivedArtifact} -> (decoded : DecodedArtifact source) ->
      ReflectedDecision
        ((constitution.operational
          (decodedContract decoded)).requirementEncoding.Witness
            ((constitution.operational
              (decodedContract decoded)).requirementEncodingAt
                (stateOfArtifact decoded)))
  contextDecision :
    {source : ReceivedArtifact} -> (decoded : DecodedArtifact source) ->
      ReflectedDecision
        ((constitution.operational
          (decodedContract decoded)).causalCondition.Witness
            ((constitution.operational
              (decodedContract decoded)).causalConditionAt
                (stateOfArtifact decoded)))
  authorizationDecision :
    {source : ReceivedArtifact} -> (decoded : DecodedArtifact source) ->
      ReflectedDecision
        ((constitution.operational
          (decodedContract decoded)).authorizationAdmission.Witness
            ((constitution.operational
              (decodedContract decoded)).authorizationAdmissionAt
                (stateOfArtifact decoded)))
  actionDecision :
    {source : ReceivedArtifact} -> (decoded : DecodedArtifact source) ->
      ReflectedDecision
        ((constitution.operational
          (decodedContract decoded)).proposalActionPreservation.Witness
            ((constitution.operational
              (decodedContract decoded)).proposalActionPreservationAt
                (stateOfArtifact decoded)))
  effectDecision :
    {source : ReceivedArtifact} -> (decoded : DecodedArtifact source) ->
      ReflectedDecision
        ((constitution.operational
          (decodedContract decoded)).effectSatisfaction.Witness
            ((constitution.operational
              (decodedContract decoded)).effectSatisfactionAt
                (stateOfArtifact decoded)))
  historicalDecision :
    {source : ReceivedArtifact} -> (decoded : DecodedArtifact source) ->
      ReflectedDecision
        ((constitution.operational
          (decodedContract decoded)).historicalPolicy.Witness
            ((constitution.operational
              (decodedContract decoded)).historicalPolicyAt
                (stateOfArtifact decoded)))
  coveredFuturesDecision :
    {source : ReceivedArtifact} -> (decoded : DecodedArtifact source) ->
      ReflectedDecision
        ((requests : List (RequirementInput
          (constitution.operational (decodedContract decoded)).family)) ->
            (constitution.operational
              (decodedContract decoded)).coveredFuture.Witness
                ((constitution.operational
                  (decodedContract decoded)).coveredFutureAt
                    (stateOfArtifact decoded) requests))
  futureRealizationDecision :
    {source : ReceivedArtifact} -> (decoded : DecodedArtifact source) ->
      ReflectedDecision
        (CoveredFutureRealization
          (constitution.operational (decodedContract decoded)))

/-- Exact positive outcomes needed to turn one decoded artifact and one
executed state into a complete constitutive state certificate.  The fields
contain only equalities saying that the corresponding executable decisions
returned `true`; the witnesses themselves are reconstructed by reflection. -/
structure ExecutableStateAcceptance
    {constitution : ConstitutiveMetaContract}
    (interface : ExecutableMetaContractInterface constitution)
    {source : interface.ReceivedArtifact}
    (decoded : interface.DecodedArtifact source) :
    Type 5 where
  basis : (interface.basisDecision decoded).result = true
  system : (interface.systemDecision decoded).result = true
  declaredInput :
    (interface.declaredInputDecision decoded).result = true
  requirement : (interface.requirementDecision decoded).result = true
  context : (interface.contextDecision decoded).result = true
  authorization :
    (interface.authorizationDecision decoded).result = true
  action : (interface.actionDecision decoded).result = true
  effect : (interface.effectDecision decoded).result = true
  historical : (interface.historicalDecision decoded).result = true
  coveredFutures :
    (interface.coveredFuturesDecision decoded).result = true
  futureRealization :
    (interface.futureRealizationDecision decoded).result = true

/-- Recompute the complete dependent fragment bundle from the separately
reflected decisions for the received artifact.  No already-assembled state
certificate is accepted by this construction. -/
def ExecutableMetaContractInterface.certifyFragments
    {constitution : ConstitutiveMetaContract}
    (interface : ExecutableMetaContractInterface constitution)
    {source : interface.ReceivedArtifact}
    {decoded : interface.DecodedArtifact source}
    (accepted : ExecutableStateAcceptance interface decoded) :
    StateCertificateFragments
      (constitution.operational (interface.decodedContract decoded))
      (interface.decodedNeuralArtifact decoded)
      (interface.stateOfArtifact decoded) :=
  let basis := (interface.basisDecision decoded).accept accepted.basis
  { structural :=
      { basis := basis
        systemExact :=
          (interface.systemDecision decoded).accept accepted.system
        inputDeclared :=
          (interface.declaredInputDecision decoded).accept
            accepted.declaredInput
        observations := stableStructuralObservationSnapshot basis.naming
        observationsExact := rfl }
    requirement :=
      { witness :=
          (interface.requirementDecision decoded).accept accepted.requirement }
    causal :=
      { witness :=
          (interface.contextDecision decoded).accept accepted.context }
    proposalAction :=
      { witness := (interface.actionDecision decoded).accept accepted.action }
    authorization :=
      { witness :=
          (interface.authorizationDecision decoded).accept
            accepted.authorization }
    effect :=
      { witness := (interface.effectDecision decoded).accept accepted.effect }
    historical :=
      { witness :=
          (interface.historicalDecision decoded).accept accepted.historical }
    futures :=
      { covered :=
          (interface.coveredFuturesDecision decoded).accept
            accepted.coveredFutures
        realization :=
          (interface.futureRealizationDecision decoded).accept
            accepted.futureRealization } }

/-- Generic correction theorem for the executable meta-contract interface.
It assembles the state certificate only after every dependent fragment has
been recomputed from its own reflected decision. -/
def ExecutableMetaContractInterface.certifyState
    {constitution : ConstitutiveMetaContract}
    (interface : ExecutableMetaContractInterface constitution)
    {source : interface.ReceivedArtifact}
    {decoded : interface.DecodedArtifact source}
    (accepted : ExecutableStateAcceptance interface decoded) :
    StateConstitutiveCertificate
      (constitution.operational (interface.decodedContract decoded))
      (interface.decodedNeuralArtifact decoded)
      (interface.stateOfArtifact decoded) :=
  assembleStateConstitution (interface.certifyFragments accepted)

/-- Contract-name decoding reflects the exact received code. -/
theorem ExecutableMetaContractInterface.contractName_reflects
    {constitution : ConstitutiveMetaContract}
    (interface : ExecutableMetaContractInterface constitution)
    (source : interface.ContractCode)
    (decoded : DecodedContractName constitution interface.encodeContract source)
    (_accepted : interface.decodeContractName source = .ok decoded) :
    interface.encodeContract decoded.contract = source :=
  decoded.exact

/-- Complete artifact decoding reflects both the received network and its
stable-key layout. -/
theorem ExecutableMetaContractInterface.artifactNetwork_reflects
    {constitution : ConstitutiveMetaContract}
    (interface : ExecutableMetaContractInterface constitution)
    {source : interface.ReceivedArtifact}
    (decoded : interface.DecodedArtifact source)
    (_accepted : interface.decodeReceivedArtifact source = .ok decoded) :
    (interface.decodedNeuralArtifact decoded).source =
      interface.artifactNetwork source :=
  interface.decodedNetworkExact decoded

end ConstitutiveSearch.NeuralAgent
/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.NeuralAgent.ReflectedDecision
#print axioms ConstitutiveSearch.NeuralAgent.ReflectedDecision.accept
#print axioms ConstitutiveSearch.NeuralAgent.DecodedContractName
#print axioms ConstitutiveSearch.NeuralAgent.ContractTransitionRequest
#print axioms ConstitutiveSearch.NeuralAgent.ExecutableMetaContractInterface
#print axioms ConstitutiveSearch.NeuralAgent.ExecutableStateAcceptance
#print axioms ConstitutiveSearch.NeuralAgent.ExecutableMetaContractInterface.certifyFragments
#print axioms ConstitutiveSearch.NeuralAgent.ExecutableMetaContractInterface.certifyState
#print axioms ConstitutiveSearch.NeuralAgent.ExecutableMetaContractInterface.contractName_reflects
#print axioms ConstitutiveSearch.NeuralAgent.ExecutableMetaContractInterface.artifactNetwork_reflects
/- AXIOM_AUDIT_END -/
