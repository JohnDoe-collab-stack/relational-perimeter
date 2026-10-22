import RelationalPerimeter.Agents.Neural.IndependentLearnedArtifact

/-!
# Separation of aligned and bypass learned updates

Both candidates start from the same independently learned artifact and carry
the same admitted operational intent.  Their current output tables coincide on
the complete declared authorized domain.  The aligned target nevertheless
retains a nonzero path from the authorization input to its primary output,
whereas the bypass target obtains that same current output through the learned
bypass observation.  The executable checker validates this structural
dependency before an artifact can be installed.
-/
set_option genInjectivity false
namespace ConstitutiveSearch.NeuralAgent
open NativeMechanism

/-- The independent artifact is evaluated on the three signals used by its
learning protocol: requirement, context, and authorization. -/
structure IndependentLearnedInput where
  requirement : Bool
  context : Bool
  authorization : Bool
  deriving DecidableEq

def IndependentLearnedInput.activations
    (input : IndependentLearnedInput) : SizedActivations 3 :=
  ((SizedActivations.snoc SizedActivations.empty
      (asActivation input.requirement)).snoc
        (asActivation input.context)).snoc
          (asActivation input.authorization)

/-- Four cases exhaust the declared current domain.  Authorization is true in
that domain; the later counterfactual witness is outside it. -/
inductive IndependentLearnedCurrentCase where
  | neither
  | contextOnly
  | requirementOnly
  | both
  deriving DecidableEq

def IndependentLearnedCurrentCase.input :
    IndependentLearnedCurrentCase -> IndependentLearnedInput
  | .neither => ⟨false, false, true⟩
  | .contextOnly => ⟨false, true, true⟩
  | .requirementOnly => ⟨true, false, true⟩
  | .both => ⟨true, true, true⟩

/-- The single canonical current domain of the learned experiment.  Every
specialized and generic current-behavior view is derived from this list. -/
def learnedRuntimeDeclaredCurrentDomain : List IndependentLearnedInput :=
  [IndependentLearnedCurrentCase.neither.input,
   IndependentLearnedCurrentCase.contextOnly.input,
   IndependentLearnedCurrentCase.requirementOnly.input,
   IndependentLearnedCurrentCase.both.input]

theorem learnedRuntimeDeclaredCurrentDomain_complete
    (current : IndependentLearnedCurrentCase) :
    current.input ∈ learnedRuntimeDeclaredCurrentDomain := by
  cases current with
  | neither => exact List.Mem.head _
  | contextOnly => exact List.Mem.tail _ (List.Mem.head _)
  | requirementOnly =>
      exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))
  | both =>
      exact List.Mem.tail _
        (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

/-- Decode the received serialized network, then execute its actual decoded
program on the supplied raw learned signals. -/
def executeIndependentLearnedArtifact
    (artifact : SerializedNetwork) (input : IndependentLearnedInput) :
    Except ArtifactError (List Activation) :=
  match decodeArtifact PublicReconfiguredOperationalContract artifact with
  | .error problem => .error problem
  | .ok decoded =>
      .ok (readOutputs decoded.system.outputs
        (executeProgram decoded.system.program
          (decoded.decodingExact.contractInputCountExact.symm ▸
            input.activations)))

/-- Total execution of the proof-free serialized format.  The checker below
separately establishes well-formedness before installation; this interpreter
is used only for counterfactual observation. -/
def learnedActivationAt : List Activation -> Nat -> Activation
  | [], _ => 0
  | value :: _, 0 => value
  | _ :: rest, index + 1 => learnedActivationAt rest index

def serializedSourceActivation
    (inputs prior : List Activation) : SerializedSource -> Activation
  | .receivedInput index => learnedActivationAt inputs index
  | .priorNeuron index => learnedActivationAt prior index

def serializedWeightedSum
    (inputs prior : List Activation) :
    List SerializedWeightedInput -> Activation
  | [] => 0
  | edge :: rest =>
      serializedSourceActivation inputs prior edge.source * edge.weight +
        serializedWeightedSum inputs prior rest

def executeSerializedNeuron
    (inputs prior : List Activation) (neuron : SerializedNeuron) : Activation :=
  asActivation (fires ⟨neuron.threshold⟩
    (serializedWeightedSum inputs prior neuron.inputs + neuron.bias))

def executeSerializedNeurons (inputs : List Activation) :
    List Activation -> List SerializedNeuron -> List Activation
  | prior, [] => prior
  | prior, neuron :: rest =>
      executeSerializedNeurons inputs
        (prior ++ [executeSerializedNeuron inputs prior neuron]) rest

def executeSerializedArtifact
    (artifact : SerializedNetwork) (input : IndependentLearnedInput) :
    List Activation :=
  let activations := executeSerializedNeurons input.activations.values []
    artifact.neurons
  artifact.outputs.map (learnedActivationAt activations)

inductive IndependentLearnedUpdateIntent where
  | preserveAuthorizedBehavior
  deriving DecidableEq

/-- Admission concerns the proposed operational intention.  It is deliberately
separate from certification of the produced target artifact. -/
inductive AdmittedIndependentLearnedIntent :
    IndependentLearnedUpdateIntent -> Type where
  | preserveAuthorizedBehavior :
      AdmittedIndependentLearnedIntent .preserveAuthorizedBehavior

/-- A candidate contains data only.  In particular it contains no dependency
witness and no certificate. -/
structure IndependentLearnedUpdateCandidate where
  sourceArtifact : SerializedNetwork
  targetArtifact : SerializedNetwork
  intent : IndependentLearnedUpdateIntent

/-- The adversarial target copies the learned bypass observation into the
primary port.  It has the same authorized-domain behavior as the aligned
successor, but no path from received authorization input 2 to primary output
neuron 6. -/
def independentLearnedBypassNeuron : SerializedNeuron :=
  { inputs := [{ source := .priorNeuron 5, weight := 1 }]
    bias := -3
    threshold := -2 }

def independentLearnedBypassNetwork : SerializedNetwork :=
  { inputCount := 3
    neurons := independentLearnedInitialNetwork.neurons ++
      [independentLearnedBypassNeuron]
    outputs := [6, 3, 5] }

def learnedBoolAt : List Bool -> Nat -> Bool
  | [], _ => false
  | value :: _, 0 => value
  | _ :: rest, index + 1 => learnedBoolAt rest index

def alignedUpdate : IndependentLearnedUpdateCandidate :=
  { sourceArtifact := independentLearnedInitialNetwork
    targetArtifact := independentLearnedFirstSuccessorNetwork
    intent := .preserveAuthorizedBehavior }

def bypassUpdate : IndependentLearnedUpdateCandidate :=
  { sourceArtifact := independentLearnedInitialNetwork
    targetArtifact := independentLearnedBypassNetwork
    intent := .preserveAuthorizedBehavior }

/-- Compute, in chronological order, whether each neuron depends through at
least one nonzero edge on a selected received input. -/
def extendSerializedDependencies (received : Nat) :
    List Bool -> List SerializedNeuron -> List Bool
  | prior, [] => prior
  | prior, neuron :: rest =>
      let depends := neuron.inputs.any (fun edge =>
        if edge.weight == 0 then false else
          match edge.source with
          | .receivedInput index => index == received
          | .priorNeuron index => learnedBoolAt prior index)
      extendSerializedDependencies received (prior ++ [depends]) rest

def serializedNeuronDependencies
    (artifact : SerializedNetwork) (received : Nat) : List Bool :=
  extendSerializedDependencies received [] artifact.neurons

/-- Dependency of the first output is calculated from the serialized graph;
it is not supplied by the candidate. -/
def primaryOutputDependsOn
    (artifact : SerializedNetwork) (received : Nat) : Bool :=
  match artifact.outputs with
  | [] => false
  | output :: _ =>
      learnedBoolAt (serializedNeuronDependencies artifact received) output

theorem alignedUpdate_authorization_dependency :
    primaryOutputDependsOn alignedUpdate.targetArtifact 2 = true := by
  rfl

theorem bypassUpdate_has_no_authorization_dependency :
    primaryOutputDependsOn bypassUpdate.targetArtifact 2 = false := by
  rfl

def independentLearnedAuthorizationOffInput : IndependentLearnedInput :=
  ⟨true, false, false⟩

def independentLearnedAuthorizationOnInput : IndependentLearnedInput :=
  ⟨true, false, true⟩

def independentLearnedPrimaryOutput
    (artifact : SerializedNetwork) (input : IndependentLearnedInput) :
    Activation :=
  learnedActivationAt (executeSerializedArtifact artifact input) 0

/-- A nonzero serialized path is not sufficient by itself.  The selected
authorization change must also change the primary output on the fixed causal
separator pair. -/
def primaryAuthorizationConstitutivelyConsumed
    (artifact : SerializedNetwork) : Bool :=
  primaryOutputDependsOn artifact 2 &&
    !(independentLearnedPrimaryOutput artifact
        independentLearnedAuthorizationOffInput ==
      independentLearnedPrimaryOutput artifact
        independentLearnedAuthorizationOnInput)

theorem alignedUpdate_consumes_authorization :
    primaryAuthorizationConstitutivelyConsumed
      alignedUpdate.targetArtifact = true := by
  rfl

theorem bypassUpdate_does_not_consume_authorization :
    primaryAuthorizationConstitutivelyConsumed
      bypassUpdate.targetArtifact = false := by
  rfl

inductive IndependentLearnedUpdateError where
  | malformedArtifact (problem : ArtifactError)
  | unexpectedSourceArtifact
  | unadmittedIntent
  | missingConstitutiveDependency
  deriving DecidableEq

/-- The common learned source is decoded and fixed before either update is
examined.  Its constructor is private, so update checking cannot receive a
source merely asserted to be the learned artifact. -/
structure CheckedIndependentLearnedInitial : Type 4 where
  private mk ::
  sourceArtifact : SerializedNetwork
  decodedSource :
    DecodedNeuralArtifact PublicReconfiguredOperationalContract
  sourceExact : sourceArtifact = independentLearnedInitialNetwork
  decodedExact :
    decodeArtifact PublicReconfiguredOperationalContract sourceArtifact =
      .ok decodedSource

def checkIndependentLearnedInitial (source : SerializedNetwork) :
    Except IndependentLearnedUpdateError CheckedIndependentLearnedInitial :=
  match decodedExact :
      decodeArtifact PublicReconfiguredOperationalContract source with
  | .error problem => .error (.malformedArtifact problem)
  | .ok decoded =>
      if sourceExact : source = independentLearnedInitialNetwork then
        .ok (.mk source decoded sourceExact decodedExact)
      else
        .error .unexpectedSourceArtifact

def checkedIndependentLearnedInitial : CheckedIndependentLearnedInitial :=
  match exact : checkIndependentLearnedInitial independentLearnedInitialNetwork with
  | .ok checked => checked
  | .error _ => False.elim (by cases exact)

theorem checkIndependentLearnedInitial_accepts_learned :
    checkIndependentLearnedInitial independentLearnedInitialNetwork =
      .ok checkedIndependentLearnedInitial := by
  rfl

/-- A successful check retains the decoded target and the dependency equality
computed from that exact serialized target. -/
structure CheckedIndependentLearnedUpdate
    (candidate : IndependentLearnedUpdateCandidate) : Type 4 where
  private mk ::
  initial : CheckedIndependentLearnedInitial
  sourceMatchesInitial :
    candidate.sourceArtifact = initial.sourceArtifact
  decodedTarget :
    DecodedNeuralArtifact PublicReconfiguredOperationalContract
  decodedExact :
    decodeArtifact PublicReconfiguredOperationalContract
      candidate.targetArtifact = .ok decodedTarget
  intentExact :
    candidate.intent = .preserveAuthorizedBehavior
  authorizationDependencyExact :
    primaryAuthorizationConstitutivelyConsumed
      candidate.targetArtifact = true

/-- The checker first fixes the learned source and admitted intention, then
decodes the exact target and finally requires the computed authorization path.
The target is not compared to a privileged aligned literal. -/
def checkIndependentLearnedUpdate
    (initial : CheckedIndependentLearnedInitial)
    (candidate : IndependentLearnedUpdateCandidate) :
    Except IndependentLearnedUpdateError
      (CheckedIndependentLearnedUpdate candidate) :=
  if sourceMatchesInitial :
      candidate.sourceArtifact = initial.sourceArtifact then
    if intentExact :
        candidate.intent = .preserveAuthorizedBehavior then
      match decodedExact :
          decodeArtifact PublicReconfiguredOperationalContract
            candidate.targetArtifact with
      | .error problem => .error (.malformedArtifact problem)
      | .ok decoded =>
          if dependencyExact :
              primaryAuthorizationConstitutivelyConsumed
                candidate.targetArtifact = true then
            .ok (.mk initial sourceMatchesInitial decoded decodedExact intentExact
              dependencyExact)
          else
            .error .missingConstitutiveDependency
    else
      .error .unadmittedIntent
  else
    .error .unexpectedSourceArtifact

def checkedAlignedUpdate : CheckedIndependentLearnedUpdate alignedUpdate :=
  match exact : checkIndependentLearnedUpdate
      checkedIndependentLearnedInitial alignedUpdate with
  | .ok checked => checked
  | .error _ => False.elim (by cases exact)

theorem checkIndependentLearnedUpdate_accepts_aligned :
    checkIndependentLearnedUpdate checkedIndependentLearnedInitial
      alignedUpdate = .ok checkedAlignedUpdate := by
  rfl

theorem checkIndependentLearnedUpdate_rejects_bypass :
    checkIndependentLearnedUpdate checkedIndependentLearnedInitial
      bypassUpdate =
      .error .missingConstitutiveDependency := by
  rfl

/-- Pure counterfactual simulation.  It never installs the candidate and
therefore cannot perform an update effect. -/
def simulateUncheckedUpdate
    (initial : CheckedIndependentLearnedInitial)
    (candidate : IndependentLearnedUpdateCandidate)
    (input : IndependentLearnedInput) : List Activation :=
  if candidate.sourceArtifact = initial.sourceArtifact then
    executeSerializedArtifact candidate.targetArtifact input
  else
    []

def CurrentBehaviorEquivalentAfterUpdate
    (initial : CheckedIndependentLearnedInitial)
    (left right : IndependentLearnedUpdateCandidate) : Prop :=
  forall current : IndependentLearnedCurrentCase,
    simulateUncheckedUpdate initial left current.input =
      simulateUncheckedUpdate initial right current.input

theorem candidateCurrentBehaviorEquivalent :
    CurrentBehaviorEquivalentAfterUpdate checkedIndependentLearnedInitial
      alignedUpdate bypassUpdate := by
  intro current
  cases current <;> rfl

structure SameAdmittedUpdateIntent
    (left right : IndependentLearnedUpdateCandidate) : Type where
  admission : AdmittedIndependentLearnedIntent left.intent
  sameIntent : left.intent = right.intent

def alignedBypassSameAdmittedUpdateIntent :
    SameAdmittedUpdateIntent alignedUpdate bypassUpdate :=
  { admission := .preserveAuthorizedBehavior
    sameIntent := rfl }

/-- An extensional current verifier is explicitly restricted to factoring
through the complete four-case current behavior table. -/
structure CurrentExtensionalVerifier where
  verdict : List (List Activation) -> Bool

def independentLearnedCurrentBehaviorTable
    (initial : CheckedIndependentLearnedInitial)
    (candidate : IndependentLearnedUpdateCandidate) :
    List (List Activation) :=
  learnedRuntimeDeclaredCurrentDomain.map
    (simulateUncheckedUpdate initial candidate)

theorem alignedBypass_currentBehaviorTable_exact :
    independentLearnedCurrentBehaviorTable checkedIndependentLearnedInitial
        alignedUpdate =
      independentLearnedCurrentBehaviorTable checkedIndependentLearnedInitial
        bypassUpdate := by
  rfl

def EveryCurrentExtensionalVerifierAgrees
    (initial : CheckedIndependentLearnedInitial)
    (left right : IndependentLearnedUpdateCandidate) : Prop :=
  forall verifier : CurrentExtensionalVerifier,
    verifier.verdict (independentLearnedCurrentBehaviorTable initial left) =
      verifier.verdict (independentLearnedCurrentBehaviorTable initial right)

theorem everyCurrentExtensionalVerifierAgrees_aligned_bypass :
    EveryCurrentExtensionalVerifierAgrees checkedIndependentLearnedInitial
      alignedUpdate bypassUpdate := by
  intro verifier
  rw [alignedBypass_currentBehaviorTable_exact]

/-- Installation is downstream of the checker.  A rejected candidate has no
installed target value. -/
def installIndependentLearnedUpdate
    (initial : CheckedIndependentLearnedInitial)
    (candidate : IndependentLearnedUpdateCandidate) :
    Except IndependentLearnedUpdateError SerializedNetwork :=
  match checkIndependentLearnedUpdate initial candidate with
  | .error problem => .error problem
  | .ok _ => .ok candidate.targetArtifact

theorem installIndependentLearnedUpdate_accepts_aligned :
    installIndependentLearnedUpdate checkedIndependentLearnedInitial
      alignedUpdate =
      .ok alignedUpdate.targetArtifact := by
  rfl

def RejectedBeforeEffect
    (initial : CheckedIndependentLearnedInitial)
    (candidate : IndependentLearnedUpdateCandidate) : Prop :=
  installIndependentLearnedUpdate initial candidate =
    .error .missingConstitutiveDependency

theorem bypassUpdate_rejectedBeforeEffect :
    RejectedBeforeEffect checkedIndependentLearnedInitial bypassUpdate := by
  rfl

end ConstitutiveSearch.NeuralAgent
/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.NeuralAgent.IndependentLearnedInput
#print axioms ConstitutiveSearch.NeuralAgent.learnedRuntimeDeclaredCurrentDomain
#print axioms ConstitutiveSearch.NeuralAgent.learnedRuntimeDeclaredCurrentDomain_complete
#print axioms ConstitutiveSearch.NeuralAgent.executeIndependentLearnedArtifact
#print axioms ConstitutiveSearch.NeuralAgent.executeSerializedArtifact
#print axioms ConstitutiveSearch.NeuralAgent.IndependentLearnedUpdateCandidate
#print axioms ConstitutiveSearch.NeuralAgent.alignedUpdate
#print axioms ConstitutiveSearch.NeuralAgent.bypassUpdate
#print axioms ConstitutiveSearch.NeuralAgent.primaryOutputDependsOn
#print axioms ConstitutiveSearch.NeuralAgent.alignedUpdate_authorization_dependency
#print axioms ConstitutiveSearch.NeuralAgent.bypassUpdate_has_no_authorization_dependency
#print axioms ConstitutiveSearch.NeuralAgent.primaryAuthorizationConstitutivelyConsumed
#print axioms ConstitutiveSearch.NeuralAgent.alignedUpdate_consumes_authorization
#print axioms ConstitutiveSearch.NeuralAgent.bypassUpdate_does_not_consume_authorization
#print axioms ConstitutiveSearch.NeuralAgent.CheckedIndependentLearnedInitial
#print axioms ConstitutiveSearch.NeuralAgent.checkIndependentLearnedInitial
#print axioms ConstitutiveSearch.NeuralAgent.checkedIndependentLearnedInitial
#print axioms ConstitutiveSearch.NeuralAgent.checkIndependentLearnedInitial_accepts_learned
#print axioms ConstitutiveSearch.NeuralAgent.CheckedIndependentLearnedUpdate
#print axioms ConstitutiveSearch.NeuralAgent.checkIndependentLearnedUpdate
#print axioms ConstitutiveSearch.NeuralAgent.checkIndependentLearnedUpdate_accepts_aligned
#print axioms ConstitutiveSearch.NeuralAgent.checkIndependentLearnedUpdate_rejects_bypass
#print axioms ConstitutiveSearch.NeuralAgent.candidateCurrentBehaviorEquivalent
#print axioms ConstitutiveSearch.NeuralAgent.SameAdmittedUpdateIntent
#print axioms ConstitutiveSearch.NeuralAgent.alignedBypassSameAdmittedUpdateIntent
#print axioms ConstitutiveSearch.NeuralAgent.CurrentExtensionalVerifier
#print axioms ConstitutiveSearch.NeuralAgent.everyCurrentExtensionalVerifierAgrees_aligned_bypass
#print axioms ConstitutiveSearch.NeuralAgent.installIndependentLearnedUpdate
#print axioms ConstitutiveSearch.NeuralAgent.bypassUpdate_rejectedBeforeEffect
/- AXIOM_AUDIT_END -/
