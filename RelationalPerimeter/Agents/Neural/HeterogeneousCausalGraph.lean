import RelationalPerimeter.Agents.Neural.StableNodeCorrespondence

/-!
# Heterogeneous constitutive causal graph

The graph joins the exact native execution to the operational and contractual
layers without replacing any of them by a homogeneous node type.  Its native
causal edge is the causal role selected by the certified finite basis.  Its
later edges consume the exact witnesses stored in the state certificate.

Stable keys are separate from version-local positions.  A validated artifact
correspondence transports graph nodes only when it also transports their key.
-/
set_option genInjectivity false
namespace ConstitutiveSearch.NeuralAgent
open NativeMechanism

/-- The seven contract observations remain distinct graph endpoints. -/
inductive ContractObservationKind where
  | requirementEncoding
  | causalCondition
  | proposalActionPreservation
  | authorizationAdmission
  | effectSatisfaction
  | coveredFuture
  | historicalPolicy
  deriving DecidableEq

/-- Version-independent keys for all heterogeneous graph nodes. -/
inductive ConstitutiveNodeKey where
  | artifactNode (key : StableNodeKey)
  | decoder
  | proposal
  | action
  | effect
  | successor
  | memoryProjection
  | contractObservation (kind : ContractObservationKind)
  deriving DecidableEq

/-- Located heterogeneous nodes for one exact decoded artifact version. -/
inductive ConstitutiveNodeId
    {contract : ConstitutiveContract}
    {artifact : DecodedNeuralArtifact contract}
    (naming : StableArtifactNaming artifact) where
  | mechanism (node : StableNodeId naming)
  | outputPort (port : StableOutputPortId naming)
  | decoder
  | proposal
  | action
  | effect
  | successor
  | memoryProjection
  | contractObservation (kind : ContractObservationKind)

def ConstitutiveNodeId.key
    {contract : ConstitutiveContract}
    {artifact : DecodedNeuralArtifact contract}
    {naming : StableArtifactNaming artifact} :
    ConstitutiveNodeId naming -> ConstitutiveNodeKey
  | .mechanism node => .artifactNode node.key
  | .outputPort port => .artifactNode port.key
  | .decoder => .decoder
  | .proposal => .proposal
  | .action => .action
  | .effect => .effect
  | .successor => .successor
  | .memoryProjection => .memoryProjection
  | .contractObservation kind => .contractObservation kind

/-- The graph relation is indexed by the exact state certificate.  Each
constructor names one constitutive dependency and, where a contractual claim
is made, consumes the corresponding certificate witness. -/
inductive ConstitutiveDependency
    {contract : ConstitutiveContract}
    {artifact : DecodedNeuralArtifact contract}
    {state : ReconfiguredExecutionState contract.family}
    (certificate : StateConstitutiveCertificate contract artifact state) :
    ConstitutiveNodeId certificate.basis.naming ->
      ConstitutiveNodeId certificate.basis.naming -> Type 3 where
  | effectiveNeuralRead
      (target : Fin artifact.system.producedCount)
      (edge : WeightedInput artifact.system.inputCount target.val)
      (_member : edge ∈ (artifact.system.program.neuronAt target).inputs)
      (_effective : edge.weight ≠ 0) :
      ConstitutiveDependency certificate
        (.mechanism (certificate.basis.naming.sourceNode target edge.source))
        (.mechanism (.neuron target))
  | executedCausalPropagation :
      ConstitutiveDependency certificate
        (.mechanism certificate.causalCoverage.node)
        (.mechanism (.neuron
          (artifact.system.outputs.sources.get
            certificate.causalCoverage.role.output)))
  | outputRead
      (port : Fin artifact.system.outputs.sources.length) :
      ConstitutiveDependency certificate
        (.mechanism (.neuron (artifact.system.outputs.sources.get port)))
        (.outputPort (certificate.basis.naming.outputPort port))
  | outputDecoded
      (port : Fin artifact.system.outputs.sources.length) :
      ConstitutiveDependency certificate
        (.outputPort (certificate.basis.naming.outputPort port)) .decoder
  | decodedProposal :
      ConstitutiveDependency certificate .decoder .proposal
  | proposalInterpreted
      (_witness := certificate.proposalActionWitness) :
      ConstitutiveDependency certificate .proposal .action
  | actionEffectuated
      (_witness := certificate.effectWitness) :
      ConstitutiveDependency certificate .action .effect
  | effectProducesSuccessor
      (_witness := certificate.historicalWitness) :
      ConstitutiveDependency certificate .effect .successor
  | successorProjectsMemory :
      ConstitutiveDependency certificate .successor .memoryProjection
  | requirementObserved
      (_witness := certificate.requirementEncodingWitness) :
      ConstitutiveDependency certificate
        (.mechanism certificate.causalCoverage.node)
        (.contractObservation .requirementEncoding)
  | causalConditionObserved
      (_witness := certificate.causalConditionWitness) :
      ConstitutiveDependency certificate
        (.mechanism certificate.causalCoverage.node)
        (.contractObservation .causalCondition)
  | proposalActionObserved
      (_witness := certificate.proposalActionWitness) :
      ConstitutiveDependency certificate .action
        (.contractObservation .proposalActionPreservation)
  | authorizationObserved
      (_witness := certificate.authorizationWitness) :
      ConstitutiveDependency certificate .action
        (.contractObservation .authorizationAdmission)
  | effectObserved
      (_witness := certificate.effectWitness) :
      ConstitutiveDependency certificate .effect
        (.contractObservation .effectSatisfaction)
  | futureObserved
      (_witness := certificate.coveredFutureWitness []) :
      ConstitutiveDependency certificate .memoryProjection
        (.contractObservation .coveredFuture)
  | historyObserved
      (_witness := certificate.historicalWitness) :
      ConstitutiveDependency certificate .successor
        (.contractObservation .historicalPolicy)

/-- The complete heterogeneous graph is the evidence-indexed dependency
relation, not an independently supplied list of edges. -/
abbrev HeterogeneousConstitutiveCausalGraph
    {contract : ConstitutiveContract}
    {artifact : DecodedNeuralArtifact contract}
    {state : ReconfiguredExecutionState contract.family}
    (certificate : StateConstitutiveCertificate contract artifact state) :=
  ConstitutiveDependency certificate

/-- The semantic spine of the heterogeneous graph for one exact installed
certificate.  Every edge is indexed by that certificate, hence by its exact
network, decoder, executed causal role, action/effect/successor witnesses,
memory projection, and operational contract observations. -/
structure InstalledHeterogeneousCausalChain
    {contract : ConstitutiveContract}
    {artifact : DecodedNeuralArtifact contract}
    {state : ReconfiguredExecutionState contract.family}
    (certificate : StateConstitutiveCertificate contract artifact state) :
    Type 4 where
  causalPropagation : HeterogeneousConstitutiveCausalGraph certificate
    (.mechanism certificate.causalCoverage.node)
    (.mechanism (.neuron
      (artifact.system.outputs.sources.get certificate.causalCoverage.role.output)))
  outputRead : HeterogeneousConstitutiveCausalGraph certificate
    (.mechanism (.neuron
      (artifact.system.outputs.sources.get certificate.causalCoverage.role.output)))
    (.outputPort
      (certificate.basis.naming.outputPort certificate.causalCoverage.role.output))
  outputDecoded : HeterogeneousConstitutiveCausalGraph certificate
    (.outputPort
      (certificate.basis.naming.outputPort certificate.causalCoverage.role.output))
    .decoder
  decodedProposal : HeterogeneousConstitutiveCausalGraph certificate
    .decoder .proposal
  proposalAction : HeterogeneousConstitutiveCausalGraph certificate
    .proposal .action
  actionEffect : HeterogeneousConstitutiveCausalGraph certificate
    .action .effect
  effectSuccessor : HeterogeneousConstitutiveCausalGraph certificate
    .effect .successor
  successorMemory : HeterogeneousConstitutiveCausalGraph certificate
    .successor .memoryProjection
  requirementObservation : HeterogeneousConstitutiveCausalGraph certificate
    (.mechanism certificate.causalCoverage.node)
    (.contractObservation .requirementEncoding)
  causalObservation : HeterogeneousConstitutiveCausalGraph certificate
    (.mechanism certificate.causalCoverage.node)
    (.contractObservation .causalCondition)
  actionObservation : HeterogeneousConstitutiveCausalGraph certificate
    .action (.contractObservation .proposalActionPreservation)
  authorizationObservation : HeterogeneousConstitutiveCausalGraph certificate
    .action (.contractObservation .authorizationAdmission)
  effectObservation : HeterogeneousConstitutiveCausalGraph certificate
    .effect (.contractObservation .effectSatisfaction)
  futureObservation : HeterogeneousConstitutiveCausalGraph certificate
    .memoryProjection (.contractObservation .coveredFuture)
  historyObservation : HeterogeneousConstitutiveCausalGraph certificate
    .successor (.contractObservation .historicalPolicy)

def installedHeterogeneousCausalChain
    {contract : ConstitutiveContract}
    {artifact : DecodedNeuralArtifact contract}
    {state : ReconfiguredExecutionState contract.family}
    (certificate : StateConstitutiveCertificate contract artifact state) :
    InstalledHeterogeneousCausalChain certificate :=
  { causalPropagation := .executedCausalPropagation
    outputRead := .outputRead certificate.causalCoverage.role.output
    outputDecoded := .outputDecoded certificate.causalCoverage.role.output
    decodedProposal := .decodedProposal
    proposalAction := .proposalInterpreted
    actionEffect := .actionEffectuated
    effectSuccessor := .effectProducesSuccessor
    successorMemory := .successorProjectsMemory
    requirementObservation := .requirementObserved
    causalObservation := .causalConditionObserved
    actionObservation := .proposalActionObserved
    authorizationObservation := .authorizationObserved
    effectObservation := .effectObserved
    futureObservation := .futureObserved
    historyObservation := .historyObserved }

/-- A successful heterogeneous-node transport contains both the new located
node and the stable-key equation that licenses the transport. -/
structure TransportedConstitutiveNode
    {oldContract newContract : ConstitutiveContract}
    {oldArtifact : DecodedNeuralArtifact oldContract}
    {newArtifact : DecodedNeuralArtifact newContract}
    {oldNaming : StableArtifactNaming oldArtifact}
    (newNaming : StableArtifactNaming newArtifact)
    (source : ConstitutiveNodeId oldNaming) : Type where
  target : ConstitutiveNodeId newNaming
  keyExact : source.key = target.key

def ValidatedStableNodeCorrespondence.transportConstitutiveNode
    {oldContract newContract : ConstitutiveContract}
    {oldArtifact : DecodedNeuralArtifact oldContract}
    {newArtifact : DecodedNeuralArtifact newContract}
    {oldNaming : StableArtifactNaming oldArtifact}
    {newNaming : StableArtifactNaming newArtifact}
    (correspondence :
      ValidatedStableNodeCorrespondence oldNaming newNaming) :
    (source : ConstitutiveNodeId oldNaming) ->
      Option (TransportedConstitutiveNode newNaming source)
  | .mechanism node =>
      match correspondence.transportNode node with
      | none => none
      | some transported => some
          { target := .mechanism transported.target
            keyExact := congrArg ConstitutiveNodeKey.artifactNode
              transported.keyExact }
  | .outputPort port =>
      match correspondence.transportOutput port with
      | none => none
      | some transported => some
          { target := .outputPort transported.target
            keyExact := congrArg ConstitutiveNodeKey.artifactNode
              transported.keyExact }
  | .decoder => some { target := .decoder, keyExact := rfl }
  | .proposal => some { target := .proposal, keyExact := rfl }
  | .action => some { target := .action, keyExact := rfl }
  | .effect => some { target := .effect, keyExact := rfl }
  | .successor => some { target := .successor, keyExact := rfl }
  | .memoryProjection =>
      some { target := .memoryProjection, keyExact := rfl }
  | .contractObservation kind =>
      some { target := .contractObservation kind, keyExact := rfl }

theorem ValidatedStableNodeCorrespondence.transportConstitutiveNode_key_exact
    {oldContract newContract : ConstitutiveContract}
    {oldArtifact : DecodedNeuralArtifact oldContract}
    {newArtifact : DecodedNeuralArtifact newContract}
    {oldNaming : StableArtifactNaming oldArtifact}
    {newNaming : StableArtifactNaming newArtifact}
    (_correspondence :
      ValidatedStableNodeCorrespondence oldNaming newNaming)
    (source : ConstitutiveNodeId oldNaming)
    (transported : TransportedConstitutiveNode newNaming source) :
    source.key = transported.target.key :=
  transported.keyExact

/-! ## Closed public graph edges -/

theorem publicReferenceGraphNaming_exact :
    publicReferenceUpdatedStateCertificate.basis.naming =
      publicReconfiguredStableNaming := by
  rfl

theorem publicStableConstitutiveCorrespondence_reindexes_requirement :
    Option.map (TransportedConstitutiveNode.target
      (newNaming := publicReconfiguredStableNaming))
        (publicStableNodeCorrespondence.transportConstitutiveNode
          (.mechanism (.receivedInput publicRequirementPort))) =
      some (.mechanism
        (.receivedInput publicReconfigurationRequirementPort)) := by
  rfl

theorem publicReferenceCausalNode_has_transported_requirement_key :
    (ConstitutiveNodeId.mechanism
      (naming := publicReferenceUpdatedStateCertificate.basis.naming)
      publicReferenceUpdatedStateCertificate.causalCoverage.node).key =
    (ConstitutiveNodeId.mechanism
      (naming := publicReconfiguredStableNaming)
      (.receivedInput publicReconfigurationRequirementPort)).key := by
  rfl

def publicReferenceCausalPropagation :
    HeterogeneousConstitutiveCausalGraph
      publicReferenceUpdatedStateCertificate
      (.mechanism
        publicReferenceUpdatedStateCertificate.causalCoverage.node)
      (.mechanism (.neuron
        (publicDecodedReconfiguredArtifact.system.outputs.sources.get
          publicReferenceUpdatedStateCertificate.causalCoverage.role.output))) :=
  .executedCausalPropagation

def publicReferenceRequirementWeightedInput : WeightedInput 3 0 :=
  { source := .receivedInput publicReconfigurationRequirementPort
    weight := 2 }

def publicReferenceEffectiveRequirementRead :
    HeterogeneousConstitutiveCausalGraph
      publicReferenceUpdatedStateCertificate
      (.mechanism (.receivedInput publicReconfigurationRequirementPort))
      (.mechanism (.neuron publicReconfigurationProposalOutput)) :=
  ConstitutiveDependency.effectiveNeuralRead
    (certificate := publicReferenceUpdatedStateCertificate)
    (target := publicReconfigurationProposalOutput)
    (edge := publicReferenceRequirementWeightedInput)
    (List.Mem.tail _ (List.Mem.head _))
    (show publicReferenceRequirementWeightedInput.weight ≠ 0 from by decide)

def publicReferenceOutputRead :
    HeterogeneousConstitutiveCausalGraph
      publicReferenceUpdatedStateCertificate
      (.mechanism (.neuron
        (publicDecodedReconfiguredArtifact.system.outputs.sources.get
          publicReconfigurationProposalOutputPort)))
      (.outputPort (publicReferenceUpdatedStateCertificate.basis.naming.outputPort
        publicReconfigurationProposalOutputPort)) :=
  .outputRead (certificate := publicReferenceUpdatedStateCertificate)
    publicReconfigurationProposalOutputPort

def publicReferenceOutputDecoded :
    HeterogeneousConstitutiveCausalGraph
      publicReferenceUpdatedStateCertificate
      (.outputPort (publicReferenceUpdatedStateCertificate.basis.naming.outputPort
        publicReconfigurationProposalOutputPort)) .decoder :=
  .outputDecoded (certificate := publicReferenceUpdatedStateCertificate)
    publicReconfigurationProposalOutputPort

def publicReferenceDecodedProposal :
    HeterogeneousConstitutiveCausalGraph
      publicReferenceUpdatedStateCertificate .decoder .proposal :=
  .decodedProposal

def publicReferenceProposalInterpreted :
    HeterogeneousConstitutiveCausalGraph
      publicReferenceUpdatedStateCertificate .proposal .action :=
  .proposalInterpreted

def publicReferenceActionEffectuated :
    HeterogeneousConstitutiveCausalGraph
      publicReferenceUpdatedStateCertificate .action .effect :=
  .actionEffectuated

def publicReferenceEffectProducesSuccessor :
    HeterogeneousConstitutiveCausalGraph
      publicReferenceUpdatedStateCertificate .effect .successor :=
  .effectProducesSuccessor

def publicReferenceSuccessorProjectsMemory :
    HeterogeneousConstitutiveCausalGraph
      publicReferenceUpdatedStateCertificate .successor .memoryProjection :=
  .successorProjectsMemory

def publicReferenceRequirementObserved :
    HeterogeneousConstitutiveCausalGraph
      publicReferenceUpdatedStateCertificate
      (.mechanism
        publicReferenceUpdatedStateCertificate.causalCoverage.node)
      (.contractObservation .requirementEncoding) :=
  .requirementObserved

def publicReferenceCausalConditionObserved :
    HeterogeneousConstitutiveCausalGraph
      publicReferenceUpdatedStateCertificate
      (.mechanism
        publicReferenceUpdatedStateCertificate.causalCoverage.node)
      (.contractObservation .causalCondition) :=
  .causalConditionObserved

def publicReferenceProposalActionObserved :
    HeterogeneousConstitutiveCausalGraph
      publicReferenceUpdatedStateCertificate .action
      (.contractObservation .proposalActionPreservation) :=
  .proposalActionObserved

def publicReferenceAuthorizationObserved :
    HeterogeneousConstitutiveCausalGraph
      publicReferenceUpdatedStateCertificate .action
      (.contractObservation .authorizationAdmission) :=
  .authorizationObserved

def publicReferenceEffectObserved :
    HeterogeneousConstitutiveCausalGraph
      publicReferenceUpdatedStateCertificate .effect
      (.contractObservation .effectSatisfaction) :=
  .effectObserved

def publicReferenceFutureObserved :
    HeterogeneousConstitutiveCausalGraph
      publicReferenceUpdatedStateCertificate .memoryProjection
      (.contractObservation .coveredFuture) :=
  .futureObserved

def publicReferenceHistoryObserved :
    HeterogeneousConstitutiveCausalGraph
      publicReferenceUpdatedStateCertificate .successor
      (.contractObservation .historicalPolicy) :=
  .historyObserved

end ConstitutiveSearch.NeuralAgent
/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.NeuralAgent.ContractObservationKind
#print axioms ConstitutiveSearch.NeuralAgent.ConstitutiveNodeKey
#print axioms ConstitutiveSearch.NeuralAgent.ConstitutiveNodeId
#print axioms ConstitutiveSearch.NeuralAgent.ConstitutiveNodeId.key
#print axioms ConstitutiveSearch.NeuralAgent.ConstitutiveDependency
#print axioms ConstitutiveSearch.NeuralAgent.HeterogeneousConstitutiveCausalGraph
#print axioms ConstitutiveSearch.NeuralAgent.InstalledHeterogeneousCausalChain
#print axioms ConstitutiveSearch.NeuralAgent.installedHeterogeneousCausalChain
#print axioms ConstitutiveSearch.NeuralAgent.TransportedConstitutiveNode
#print axioms ConstitutiveSearch.NeuralAgent.ValidatedStableNodeCorrespondence.transportConstitutiveNode
#print axioms ConstitutiveSearch.NeuralAgent.ValidatedStableNodeCorrespondence.transportConstitutiveNode_key_exact
#print axioms ConstitutiveSearch.NeuralAgent.publicReferenceGraphNaming_exact
#print axioms ConstitutiveSearch.NeuralAgent.publicStableConstitutiveCorrespondence_reindexes_requirement
#print axioms ConstitutiveSearch.NeuralAgent.publicReferenceCausalNode_has_transported_requirement_key
#print axioms ConstitutiveSearch.NeuralAgent.publicReferenceCausalPropagation
#print axioms ConstitutiveSearch.NeuralAgent.publicReferenceRequirementWeightedInput
#print axioms ConstitutiveSearch.NeuralAgent.publicReferenceEffectiveRequirementRead
#print axioms ConstitutiveSearch.NeuralAgent.publicReferenceOutputRead
#print axioms ConstitutiveSearch.NeuralAgent.publicReferenceOutputDecoded
#print axioms ConstitutiveSearch.NeuralAgent.publicReferenceDecodedProposal
#print axioms ConstitutiveSearch.NeuralAgent.publicReferenceProposalInterpreted
#print axioms ConstitutiveSearch.NeuralAgent.publicReferenceActionEffectuated
#print axioms ConstitutiveSearch.NeuralAgent.publicReferenceEffectProducesSuccessor
#print axioms ConstitutiveSearch.NeuralAgent.publicReferenceSuccessorProjectsMemory
#print axioms ConstitutiveSearch.NeuralAgent.publicReferenceRequirementObserved
#print axioms ConstitutiveSearch.NeuralAgent.publicReferenceCausalConditionObserved
#print axioms ConstitutiveSearch.NeuralAgent.publicReferenceProposalActionObserved
#print axioms ConstitutiveSearch.NeuralAgent.publicReferenceAuthorizationObserved
#print axioms ConstitutiveSearch.NeuralAgent.publicReferenceEffectObserved
#print axioms ConstitutiveSearch.NeuralAgent.publicReferenceFutureObserved
#print axioms ConstitutiveSearch.NeuralAgent.publicReferenceHistoryObserved
/- AXIOM_AUDIT_END -/
