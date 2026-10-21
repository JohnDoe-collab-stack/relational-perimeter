import RelationalPerimeter.Agents.Neural.HeterogeneousCausalGraph

/-!
# Executable affected constitutive cone

The affected cone is computed rather than supplied.  Its initial nodes are
exactly the new artifact nodes without a validated stable antecedent, the
transported nodes whose structural observation changed, the decoder, and the
contract observations that must be rechecked across the contract transition.
The computation then closes those seeds under the actual nonzero neural reads,
output-port reads, and the complete downstream operational chain.
-/
set_option genInjectivity false
namespace ConstitutiveSearch.NeuralAgent
open NativeMechanism

/-- Constructively enumerate every location in a finite execution index. -/
def finiteLocations : (count : Nat) -> List (Fin count)
  | 0 => []
  | count + 1 =>
      ⟨0, Nat.zero_lt_succ count⟩ ::
        (finiteLocations count).map Fin.succ

/-- A weighted read expressed only through stable identities. -/
structure StableWeightedRead where
  source : StableNodeKey
  weight : Int

/-- The local structural observation whose equality licenses reuse.  It is
independent of artifact-local `Fin` positions. -/
inductive StableArtifactObservation where
  | receivedInput
  | neuron (reads : List StableWeightedRead) (bias threshold : Int)
  | outputPort (source : StableNodeKey)

def stableNodeKeyEquality
    (left right : StableNodeKey) : Decidable (left = right) := by
  cases left with
  | receivedInput leftSerial =>
      cases right with
      | receivedInput rightSerial =>
          exact match Nat.decEq leftSerial rightSerial with
          | .isTrue same => .isTrue (congrArg StableNodeKey.receivedInput same)
          | .isFalse different => .isFalse (fun same =>
              by cases same; exact different rfl)
      | neuron _ => exact .isFalse (fun same => nomatch same)
      | outputPort _ => exact .isFalse (fun same => nomatch same)
  | neuron leftSerial =>
      cases right with
      | receivedInput _ => exact .isFalse (fun same => nomatch same)
      | neuron rightSerial =>
          exact match Nat.decEq leftSerial rightSerial with
          | .isTrue same => .isTrue (congrArg StableNodeKey.neuron same)
          | .isFalse different => .isFalse (fun same =>
              by cases same; exact different rfl)
      | outputPort _ => exact .isFalse (fun same => nomatch same)
  | outputPort leftSerial =>
      cases right with
      | receivedInput _ => exact .isFalse (fun same => nomatch same)
      | neuron _ => exact .isFalse (fun same => nomatch same)
      | outputPort rightSerial =>
          exact match Nat.decEq leftSerial rightSerial with
          | .isTrue same => .isTrue (congrArg StableNodeKey.outputPort same)
          | .isFalse different => .isFalse (fun same =>
              by cases same; exact different rfl)

def contractObservationKindEquality
    (left right : ContractObservationKind) : Decidable (left = right) := by
  cases left <;> cases right <;>
    first | exact .isTrue rfl | exact .isFalse (fun same => nomatch same)

def constitutiveNodeKeyEquality
    (left right : ConstitutiveNodeKey) : Decidable (left = right) := by
  cases left with
  | artifactNode leftKey =>
      cases right with
      | artifactNode rightKey =>
          exact match stableNodeKeyEquality leftKey rightKey with
          | .isTrue same => .isTrue
              (congrArg ConstitutiveNodeKey.artifactNode same)
          | .isFalse different => .isFalse (fun same =>
              by cases same; exact different rfl)
      | decoder | proposal | action | effect | successor | memoryProjection =>
          exact .isFalse (fun same => nomatch same)
      | contractObservation _ => exact .isFalse (fun same => nomatch same)
  | decoder =>
      cases right <;>
        first | exact .isTrue rfl | exact .isFalse (fun same => nomatch same)
  | proposal =>
      cases right <;>
        first | exact .isTrue rfl | exact .isFalse (fun same => nomatch same)
  | action =>
      cases right <;>
        first | exact .isTrue rfl | exact .isFalse (fun same => nomatch same)
  | effect =>
      cases right <;>
        first | exact .isTrue rfl | exact .isFalse (fun same => nomatch same)
  | successor =>
      cases right <;>
        first | exact .isTrue rfl | exact .isFalse (fun same => nomatch same)
  | memoryProjection =>
      cases right <;>
        first | exact .isTrue rfl | exact .isFalse (fun same => nomatch same)
  | contractObservation leftKind =>
      cases right with
      | artifactNode _ | decoder | proposal | action | effect | successor |
          memoryProjection => exact .isFalse (fun same => nomatch same)
      | contractObservation rightKind =>
          exact match contractObservationKindEquality leftKind rightKind with
          | .isTrue same => .isTrue
              (congrArg ConstitutiveNodeKey.contractObservation same)
          | .isFalse different => .isFalse (fun same =>
              by cases same; exact different rfl)

def stableWeightedReadEquality
    (left right : StableWeightedRead) : Decidable (left = right) := by
  cases left with
  | mk leftSource leftWeight =>
      cases right with
      | mk rightSource rightWeight =>
          exact match stableNodeKeyEquality leftSource rightSource,
              Int.decEq leftWeight rightWeight with
          | .isTrue sourceExact, .isTrue weightExact =>
              .isTrue (by cases sourceExact; cases weightExact; rfl)
          | .isFalse different, _ => .isFalse (fun same =>
              different (congrArg StableWeightedRead.source same))
          | _, .isFalse different => .isFalse (fun same =>
              different (congrArg StableWeightedRead.weight same))

def stableWeightedReadsEquality :
    (left right : List StableWeightedRead) -> Decidable (left = right)
  | [], [] => .isTrue rfl
  | [], _ :: _ => .isFalse (fun same => nomatch same)
  | _ :: _, [] => .isFalse (fun same => nomatch same)
  | leftHead :: leftTail, rightHead :: rightTail =>
      match stableWeightedReadEquality leftHead rightHead,
          stableWeightedReadsEquality leftTail rightTail with
      | .isTrue headExact, .isTrue tailExact =>
          .isTrue (by cases headExact; cases tailExact; rfl)
      | .isFalse different, _ => .isFalse (fun same =>
          different (List.cons.inj same).1)
      | _, .isFalse different => .isFalse (fun same =>
          different (List.cons.inj same).2)

def stableArtifactObservationEquality
    (left right : StableArtifactObservation) : Decidable (left = right) := by
  cases left with
  | receivedInput =>
      cases right with
      | receivedInput => exact .isTrue rfl
      | neuron _ _ _ | outputPort _ =>
          exact .isFalse (fun same => nomatch same)
  | neuron leftReads leftBias leftThreshold =>
      cases right with
      | receivedInput | outputPort _ =>
          exact .isFalse (fun same => nomatch same)
      | neuron rightReads rightBias rightThreshold =>
          exact match stableWeightedReadsEquality leftReads rightReads,
              Int.decEq leftBias rightBias,
              Int.decEq leftThreshold rightThreshold with
          | .isTrue readsExact, .isTrue biasExact, .isTrue thresholdExact =>
              .isTrue (by
                cases readsExact; cases biasExact; cases thresholdExact; rfl)
          | .isFalse different, _, _ => .isFalse (fun same =>
              by cases same; exact different rfl)
          | _, .isFalse different, _ => .isFalse (fun same =>
              by cases same; exact different rfl)
          | _, _, .isFalse different => .isFalse (fun same =>
              by cases same; exact different rfl)
  | outputPort leftSource =>
      cases right with
      | receivedInput | neuron _ _ _ =>
          exact .isFalse (fun same => nomatch same)
      | outputPort rightSource =>
          exact match stableNodeKeyEquality leftSource rightSource with
          | .isTrue same => .isTrue
              (congrArg StableArtifactObservation.outputPort same)
          | .isFalse different => .isFalse (fun same =>
              by cases same; exact different rfl)

def observationOptionEquality
    (left right : Option StableArtifactObservation) : Decidable (left = right) :=
  match left, right with
  | none, none => .isTrue rfl
  | none, some _ => .isFalse (fun same => nomatch same)
  | some _, none => .isFalse (fun same => nomatch same)
  | some leftObservation, some rightObservation =>
      match stableArtifactObservationEquality leftObservation rightObservation with
      | .isTrue same => .isTrue (congrArg Option.some same)
      | .isFalse different => .isFalse (fun same =>
          different (Option.some.inj same))

/-- Proof-free equality readout used by the executable cone.  It is defined
structurally so the runtime never eliminates a proposition in order to decide
whether a node changed. -/
def naturalNumbersSame : Nat -> Nat -> Bool
  | 0, 0 => true
  | 0, _ + 1 => false
  | _ + 1, 0 => false
  | left + 1, right + 1 => naturalNumbersSame left right

theorem naturalNumbersSame_true
    (left right : Nat)
    (same : naturalNumbersSame left right = true) : left = right := by
  induction left generalizing right with
  | zero =>
      cases right with
      | zero => rfl
      | succ _ => cases same
  | succ left ih =>
      cases right with
      | zero => cases same
      | succ right => exact congrArg Nat.succ (ih right same)

def integersSame : Int -> Int -> Bool
  | .ofNat left, .ofNat right => naturalNumbersSame left right
  | .negSucc left, .negSucc right => naturalNumbersSame left right
  | .ofNat _, .negSucc _ => false
  | .negSucc _, .ofNat _ => false

theorem integersSame_true
    (left right : Int)
    (same : integersSame left right = true) : left = right := by
  cases left with
  | ofNat left =>
      cases right with
      | ofNat right =>
          exact congrArg Int.ofNat
            (naturalNumbersSame_true left right same)
      | negSucc _ => cases same
  | negSucc left =>
      cases right with
      | ofNat _ => cases same
      | negSucc right =>
          exact congrArg Int.negSucc
            (naturalNumbersSame_true left right same)

def stableNodeKeysSame : StableNodeKey -> StableNodeKey -> Bool
  | .receivedInput left, .receivedInput right => naturalNumbersSame left right
  | .receivedInput _, .neuron _ => false
  | .receivedInput _, .outputPort _ => false
  | .neuron _, .receivedInput _ => false
  | .neuron left, .neuron right => naturalNumbersSame left right
  | .neuron _, .outputPort _ => false
  | .outputPort _, .receivedInput _ => false
  | .outputPort _, .neuron _ => false
  | .outputPort left, .outputPort right => naturalNumbersSame left right

theorem stableNodeKeysSame_true
    (left right : StableNodeKey)
    (same : stableNodeKeysSame left right = true) : left = right := by
  cases left with
  | receivedInput left =>
      cases right with
      | receivedInput right =>
          exact (congrArg StableNodeKey.receivedInput
            (naturalNumbersSame_true left right same))
      | neuron _ => cases same
      | outputPort _ => cases same
  | neuron left =>
      cases right with
      | receivedInput _ => cases same
      | neuron right =>
          exact (congrArg StableNodeKey.neuron
            (naturalNumbersSame_true left right same))
      | outputPort _ => cases same
  | outputPort left =>
      cases right with
      | receivedInput _ => cases same
      | neuron _ => cases same
      | outputPort right =>
          exact (congrArg StableNodeKey.outputPort
            (naturalNumbersSame_true left right same))

def stableWeightedReadsSame :
    List StableWeightedRead -> List StableWeightedRead -> Bool
  | [], [] => true
  | [], _ :: _ => false
  | _ :: _, [] => false
  | left :: leftRest, right :: rightRest =>
      stableNodeKeysSame left.source right.source &&
        integersSame left.weight right.weight &&
        stableWeightedReadsSame leftRest rightRest

theorem stableWeightedReadsSame_true
    (left right : List StableWeightedRead)
    (same : stableWeightedReadsSame left right = true) : left = right := by
  induction left generalizing right with
  | nil =>
      cases right with
      | nil => rfl
      | cons _ _ => cases same
  | cons leftHead leftRest ih =>
      cases right with
      | nil => cases same
      | cons rightHead rightRest =>
          cases leftHead with
          | mk leftSource leftWeight =>
              cases rightHead with
              | mk rightSource rightWeight =>
                  cases sourceCase : stableNodeKeysSame leftSource rightSource with
                  | false =>
                      change (stableNodeKeysSame leftSource rightSource &&
                        integersSame leftWeight rightWeight &&
                        stableWeightedReadsSame leftRest rightRest) = true at same
                      rw [sourceCase] at same
                      cases same
                  | true =>
                      cases weightCase : integersSame leftWeight rightWeight with
                      | false =>
                          change (stableNodeKeysSame leftSource rightSource &&
                            integersSame leftWeight rightWeight &&
                            stableWeightedReadsSame leftRest rightRest) = true at same
                          rw [sourceCase, weightCase] at same
                          cases same
                      | true =>
                          cases restCase : stableWeightedReadsSame leftRest rightRest with
                          | false =>
                              change (stableNodeKeysSame leftSource rightSource &&
                                integersSame leftWeight rightWeight &&
                                stableWeightedReadsSame leftRest rightRest) = true at same
                              rw [sourceCase, weightCase, restCase] at same
                              cases same
                          | true =>
                              have sourceExact := stableNodeKeysSame_true
                                leftSource rightSource sourceCase
                              have weightExact := integersSame_true
                                leftWeight rightWeight weightCase
                              have restExact := ih rightRest restCase
                              cases sourceExact
                              cases weightExact
                              cases restExact
                              rfl

def stableArtifactObservationsSame :
    StableArtifactObservation -> StableArtifactObservation -> Bool
  | .receivedInput, .receivedInput => true
  | .receivedInput, .neuron _ _ _ => false
  | .receivedInput, .outputPort _ => false
  | .neuron _ _ _, .receivedInput => false
  | .neuron leftReads leftBias leftThreshold,
      .neuron rightReads rightBias rightThreshold =>
      stableWeightedReadsSame leftReads rightReads &&
        integersSame leftBias rightBias &&
        integersSame leftThreshold rightThreshold
  | .neuron _ _ _, .outputPort _ => false
  | .outputPort _, .receivedInput => false
  | .outputPort _, .neuron _ _ _ => false
  | .outputPort left, .outputPort right => stableNodeKeysSame left right

theorem stableArtifactObservationsSame_true
    (left right : StableArtifactObservation)
    (same : stableArtifactObservationsSame left right = true) : left = right := by
  cases left with
  | receivedInput =>
      cases right with
      | receivedInput => rfl
      | neuron _ _ _ => cases same
      | outputPort _ => cases same
  | neuron leftReads leftBias leftThreshold =>
      cases right with
      | receivedInput => cases same
      | outputPort _ => cases same
      | neuron rightReads rightBias rightThreshold =>
          cases readsCase : stableWeightedReadsSame leftReads rightReads with
          | false =>
              change (stableWeightedReadsSame leftReads rightReads &&
                integersSame leftBias rightBias &&
                integersSame leftThreshold rightThreshold) = true at same
              rw [readsCase] at same
              cases same
          | true =>
              cases biasCase : integersSame leftBias rightBias with
              | false =>
                  change (stableWeightedReadsSame leftReads rightReads &&
                    integersSame leftBias rightBias &&
                    integersSame leftThreshold rightThreshold) = true at same
                  rw [readsCase, biasCase] at same
                  cases same
              | true =>
                  cases thresholdCase : integersSame leftThreshold
                      rightThreshold with
                  | false =>
                      change (stableWeightedReadsSame leftReads rightReads &&
                        integersSame leftBias rightBias &&
                        integersSame leftThreshold rightThreshold) = true at same
                      rw [readsCase, biasCase, thresholdCase] at same
                      cases same
                  | true =>
                      have readsExact := stableWeightedReadsSame_true
                        leftReads rightReads readsCase
                      have biasExact := integersSame_true
                        leftBias rightBias biasCase
                      have thresholdExact := integersSame_true
                        leftThreshold rightThreshold thresholdCase
                      cases readsExact
                      cases biasExact
                      cases thresholdExact
                      rfl
  | outputPort leftSource =>
      cases right with
      | receivedInput => cases same
      | neuron _ _ _ => cases same
      | outputPort rightSource =>
          exact (congrArg StableArtifactObservation.outputPort
            (stableNodeKeysSame_true leftSource rightSource same))

def observationOptionsSame :
    Option StableArtifactObservation -> Option StableArtifactObservation -> Bool
  | none, none => true
  | none, some _ => false
  | some _, none => false
  | some left, some right => stableArtifactObservationsSame left right

theorem observationOptionsSame_true
    (left right : Option StableArtifactObservation)
    (same : observationOptionsSame left right = true) : left = right := by
  cases left with
  | none =>
      cases right with
      | none => rfl
      | some _ => cases same
  | some left =>
      cases right with
      | none => cases same
      | some right =>
          exact (congrArg Option.some
            (stableArtifactObservationsSame_true left right same))

def structuralInitiallyAffected (transported unchanged : Bool) : Bool :=
  match transported with
  | false => true
  | true => !unchanged

theorem structuralInitiallyAffected_false_unchanged_true
    (transported unchanged : Bool)
    (notAffected : structuralInitiallyAffected transported unchanged = false) :
    unchanged = true := by
  cases transported <;> cases unchanged <;>
    first | rfl | cases notAffected

def StableArtifactNaming.weightedRead
    {contract : ConstitutiveContract}
    {artifact : DecodedNeuralArtifact contract}
    (naming : StableArtifactNaming artifact)
    (target : Fin artifact.system.producedCount)
    (edge : WeightedInput artifact.system.inputCount target.val) :
    StableWeightedRead :=
  { source := (naming.sourceNode target edge.source).key
    weight := edge.weight }

def StableArtifactNaming.mechanismObservation
    {contract : ConstitutiveContract}
    {artifact : DecodedNeuralArtifact contract}
    (naming : StableArtifactNaming artifact) :
    StableNodeId naming -> StableArtifactObservation
  | .receivedInput _ => .receivedInput
  | .neuron target =>
      let neuron := artifact.system.program.neuronAt target
      .neuron (neuron.inputs.map (naming.weightedRead target))
        neuron.bias neuron.threshold.level

def StableArtifactNaming.outputObservation
    {contract : ConstitutiveContract}
    {artifact : DecodedNeuralArtifact contract}
    (naming : StableArtifactNaming artifact)
    (port : StableOutputPortId naming) : StableArtifactObservation :=
  .outputPort
    (StableNodeId.neuron
      (naming := naming)
      (artifact.system.outputs.sources.get port.index)).key

/-- A complete stable snapshot of the artifact-local part of one certificate.
The certificate supplies the authoritative naming; the observations are read
from its exact decoded artifact. -/
def structuralObservationSnapshot
    {contract : ConstitutiveContract}
    {artifact : DecodedNeuralArtifact contract}
    {state : ReconfiguredExecutionState contract.family}
    (certificate : StateConstitutiveCertificate contract artifact state) :
    List (StableNodeKey × StableArtifactObservation) :=
  (finiteLocations artifact.system.inputCount).map (fun index =>
      let node : StableNodeId certificate.basis.naming := .receivedInput index
      (node.key,
        certificate.basis.naming.mechanismObservation node)) ++
  (finiteLocations artifact.system.producedCount).map (fun index =>
      let node : StableNodeId certificate.basis.naming := .neuron index
      (node.key,
        certificate.basis.naming.mechanismObservation node)) ++
  (finiteLocations artifact.system.outputs.sources.length).map (fun index =>
      let port := certificate.basis.naming.outputPort index
      (port.key, certificate.basis.naming.outputObservation port))

def lookupStructuralObservation (key : StableNodeKey) :
    List (StableNodeKey × StableArtifactObservation) ->
      Option StableArtifactObservation
  | [] => none
  | entry :: rest =>
      if entry.1 = key then some entry.2
      else lookupStructuralObservation key rest

def keyOccurs (target : ConstitutiveNodeKey) :
    List ConstitutiveNodeKey -> Bool
  | [] => false
  | key :: rest =>
      match constitutiveNodeKeyEquality key target with
      | .isTrue _ => true
      | .isFalse _ => keyOccurs target rest

def insertConstitutiveKey (key : ConstitutiveNodeKey)
    (keys : List ConstitutiveNodeKey) : List ConstitutiveNodeKey :=
  match keyOccurs key keys with
  | true => keys
  | false => key :: keys

/-- Stable target keys positively produced by the validated partial
correspondence.  Merely finding the same serial in both snapshots is not
enough: the key must occur as the result of the validated map. -/
def transportedArtifactKeys
    {oldContract newContract : ConstitutiveContract}
    {oldArtifact : DecodedNeuralArtifact oldContract}
    {newArtifact : DecodedNeuralArtifact newContract}
    {oldNaming : StableArtifactNaming oldArtifact}
    {newNaming : StableArtifactNaming newArtifact}
    (correspondence :
      ValidatedStableNodeCorrespondence oldNaming newNaming) :
    List ConstitutiveNodeKey :=
  (finiteLocations oldArtifact.system.inputCount).filterMap (fun source =>
      match correspondence.inputMap source with
      | none => none
      | some target => some (.artifactNode
          (.receivedInput (newNaming.inputSerial target)))) ++
  (finiteLocations oldArtifact.system.producedCount).filterMap (fun source =>
      match correspondence.neuronMap source with
      | none => none
      | some target => some (.artifactNode
          (.neuron (newNaming.neuronSerial target)))) ++
  (finiteLocations oldArtifact.system.outputs.sources.length).filterMap
    (fun source =>
      match correspondence.outputMap source with
      | none => none
      | some target => some (.artifactNode
          (.outputPort (newNaming.outputSerial target))))

/-- One executable dependency edge in the finite heterogeneous graph. -/
structure ConstitutiveDependencyEdge where
  source : ConstitutiveNodeKey
  target : ConstitutiveNodeKey
  deriving DecidableEq

def effectiveReadEdges
    {contract : ConstitutiveContract}
    {artifact : DecodedNeuralArtifact contract}
    (naming : StableArtifactNaming artifact)
    (target : Fin artifact.system.producedCount) :
    List (WeightedInput artifact.system.inputCount target.val) ->
      List ConstitutiveDependencyEdge
  | [] => []
  | edge :: rest =>
      if _effective : edge.weight ≠ 0 then
        { source := .artifactNode (naming.sourceNode target edge.source).key
          target := .artifactNode (.neuron (naming.neuronSerial target)) } ::
          effectiveReadEdges naming target rest
      else
        effectiveReadEdges naming target rest

def neuralDependencyEdges
    {contract : ConstitutiveContract}
    {artifact : DecodedNeuralArtifact contract}
    (naming : StableArtifactNaming artifact) :
    List ConstitutiveDependencyEdge :=
  (finiteLocations artifact.system.producedCount).flatMap (fun target =>
    effectiveReadEdges naming target
      (artifact.system.program.neuronAt target).inputs)

def outputDependencyEdges
    {contract : ConstitutiveContract}
    {artifact : DecodedNeuralArtifact contract}
    (naming : StableArtifactNaming artifact) :
    List ConstitutiveDependencyEdge :=
  (finiteLocations artifact.system.outputs.sources.length).map (fun port =>
    { source := .artifactNode
        (.neuron (naming.neuronSerial
          (artifact.system.outputs.sources.get port)))
      target := .artifactNode (.outputPort (naming.outputSerial port)) })

def operationalDependencyEdges : List ConstitutiveDependencyEdge :=
  [ { source := .decoder, target := .proposal },
    { source := .proposal, target := .action },
    { source := .action, target := .effect },
    { source := .effect, target := .successor },
    { source := .successor, target := .memoryProjection },
    { source := .action,
      target := .contractObservation .proposalActionPreservation },
    { source := .action,
      target := .contractObservation .authorizationAdmission },
    { source := .effect,
      target := .contractObservation .effectSatisfaction },
    { source := .memoryProjection,
      target := .contractObservation .coveredFuture },
    { source := .successor,
      target := .contractObservation .historicalPolicy } ]

def decoderDependencyEdges
    {contract : ConstitutiveContract}
    {artifact : DecodedNeuralArtifact contract}
    (naming : StableArtifactNaming artifact) :
    List ConstitutiveDependencyEdge :=
  (finiteLocations artifact.system.outputs.sources.length).map (fun port =>
    { source := .artifactNode (.outputPort (naming.outputSerial port))
      target := .decoder })

def causalObservationDependencyEdges
    {contract : ConstitutiveContract}
    {artifact : DecodedNeuralArtifact contract}
    (naming : StableArtifactNaming artifact) :
    List ConstitutiveDependencyEdge :=
  ((finiteLocations artifact.system.inputCount).map (fun index =>
      ConstitutiveNodeKey.artifactNode
        (.receivedInput (naming.inputSerial index))) ++
    (finiteLocations artifact.system.producedCount).map (fun index =>
      ConstitutiveNodeKey.artifactNode
        (.neuron (naming.neuronSerial index)))).flatMap
    (fun source =>
      [ { source := source,
          target := .contractObservation .requirementEncoding },
        { source := source,
          target := .contractObservation .causalCondition } ])

def heterogeneousDependencyEdges
    {contract : ConstitutiveContract}
    {artifact : DecodedNeuralArtifact contract}
    (naming : StableArtifactNaming artifact) :
    List ConstitutiveDependencyEdge :=
  neuralDependencyEdges naming ++ outputDependencyEdges naming ++
    decoderDependencyEdges naming ++ causalObservationDependencyEdges naming ++
    operationalDependencyEdges

def semanticConstitutiveKeys : List ConstitutiveNodeKey :=
  [ .decoder, .proposal, .action, .effect, .successor, .memoryProjection,
    .contractObservation .requirementEncoding,
    .contractObservation .causalCondition,
    .contractObservation .proposalActionPreservation,
    .contractObservation .authorizationAdmission,
    .contractObservation .effectSatisfaction,
    .contractObservation .coveredFuture,
    .contractObservation .historicalPolicy ]

def completeConstitutiveKeys
    {contract : ConstitutiveContract}
    {artifact : DecodedNeuralArtifact contract}
    {state : ReconfiguredExecutionState contract.family}
    (certificate : StateConstitutiveCertificate contract artifact state) :
    List ConstitutiveNodeKey :=
  (structuralObservationSnapshot certificate).map
      (fun entry => .artifactNode entry.1) ++
    semanticConstitutiveKeys

/-- The initial affected predicate is entirely derived from the two exact
certificates and the validated correspondence.  Cross-contract decoding and
contract observations are conservatively invalidated; downstream operational
nodes are reached through edges rather than inserted by assertion. -/
def initiallyAffected
    {oldContract newContract : ConstitutiveContract}
    {oldArtifact : DecodedNeuralArtifact oldContract}
    {newArtifact : DecodedNeuralArtifact newContract}
    {oldState : ReconfiguredExecutionState oldContract.family}
    {newState : ReconfiguredExecutionState newContract.family}
    (oldCertificate :
      StateConstitutiveCertificate oldContract oldArtifact oldState)
    (newCertificate :
      StateConstitutiveCertificate newContract newArtifact newState)
    (correspondence : ValidatedStableNodeCorrespondence
      oldCertificate.basis.naming newCertificate.basis.naming) :
    ConstitutiveNodeKey -> Bool
  | .artifactNode key =>
      structuralInitiallyAffected
        (keyOccurs (.artifactNode key)
          (transportedArtifactKeys correspondence))
        (observationOptionsSame
          (lookupStructuralObservation key
            (structuralObservationSnapshot oldCertificate))
          (lookupStructuralObservation key
            (structuralObservationSnapshot newCertificate)))
  | .decoder => true
  | .contractObservation _ => true
  | .proposal => false
  | .action => false
  | .effect => false
  | .successor => false
  | .memoryProjection => false

def edgePropagates
    (previous : ConstitutiveNodeKey -> Bool)
    (target : ConstitutiveNodeKey) :
    List ConstitutiveDependencyEdge -> Bool
  | [] => false
  | edge :: rest =>
      (match constitutiveNodeKeyEquality edge.target target with
       | .isTrue _ => previous edge.source
       | .isFalse _ => false) || edgePropagates previous target rest

/-- Bounded closure is executable.  The graph is finite and acyclic by its
typed chronological neural edges and fixed downstream chain; the number of
new-version nodes therefore bounds every dependency path. -/
def affectedWithin
    (initial : ConstitutiveNodeKey -> Bool)
    (edges : List ConstitutiveDependencyEdge) :
    Nat -> ConstitutiveNodeKey -> Bool
  | 0, key => initial key
  | fuel + 1, key =>
      initial key || edgePropagates (affectedWithin initial edges fuel) key edges

theorem affectedWithin_false_initial_false
    (initial : ConstitutiveNodeKey -> Bool)
    (edges : List ConstitutiveDependencyEdge)
    (fuel : Nat)
    (key : ConstitutiveNodeKey)
    (outside : affectedWithin initial edges fuel key = false) :
    initial key = false := by
  cases fuel with
  | zero => exact outside
  | succ fuel =>
      unfold affectedWithin at outside
      cases initialExact : initial key with
      | false => exact rfl
      | true =>
          rw [initialExact] at outside
          cases outside

/-- Executable characteristic function of the affected constitutive cone. -/
def affectedConstitutiveNode
    {oldContract newContract : ConstitutiveContract}
    {oldArtifact : DecodedNeuralArtifact oldContract}
    {newArtifact : DecodedNeuralArtifact newContract}
    {oldState : ReconfiguredExecutionState oldContract.family}
    {newState : ReconfiguredExecutionState newContract.family}
    (oldCertificate :
      StateConstitutiveCertificate oldContract oldArtifact oldState)
    (newCertificate :
      StateConstitutiveCertificate newContract newArtifact newState)
    (correspondence : ValidatedStableNodeCorrespondence
      oldCertificate.basis.naming newCertificate.basis.naming)
    (key : ConstitutiveNodeKey) : Bool :=
  affectedWithin
    (initiallyAffected oldCertificate newCertificate correspondence)
    (heterogeneousDependencyEdges newCertificate.basis.naming)
    (completeConstitutiveKeys newCertificate).length key

def selectAffectedKeys
    (affected : ConstitutiveNodeKey -> Bool) :
    List ConstitutiveNodeKey -> List ConstitutiveNodeKey
  | [] => []
  | key :: rest =>
      match affected key with
      | true => key :: selectAffectedKeys affected rest
      | false => selectAffectedKeys affected rest

/-- The material finite cone returned to the incremental runtime. -/
def affectedConstitutiveCone
    {oldContract newContract : ConstitutiveContract}
    {oldArtifact : DecodedNeuralArtifact oldContract}
    {newArtifact : DecodedNeuralArtifact newContract}
    {oldState : ReconfiguredExecutionState oldContract.family}
    {newState : ReconfiguredExecutionState newContract.family}
    (oldCertificate :
      StateConstitutiveCertificate oldContract oldArtifact oldState)
    (newCertificate :
      StateConstitutiveCertificate newContract newArtifact newState)
    (correspondence : ValidatedStableNodeCorrespondence
      oldCertificate.basis.naming newCertificate.basis.naming) :
    List ConstitutiveNodeKey :=
  selectAffectedKeys
    (affectedConstitutiveNode oldCertificate newCertificate correspondence)
    (completeConstitutiveKeys newCertificate)

/-- Outside the computed cone, a transported structural key has exactly the
same stable observation.  This is a consequence of the seed computation, not
an extra reuse assumption. -/
theorem outsideAffectedCone_unchanged
    {oldContract newContract : ConstitutiveContract}
    {oldArtifact : DecodedNeuralArtifact oldContract}
    {newArtifact : DecodedNeuralArtifact newContract}
    {oldState : ReconfiguredExecutionState oldContract.family}
    {newState : ReconfiguredExecutionState newContract.family}
    (oldCertificate :
      StateConstitutiveCertificate oldContract oldArtifact oldState)
    (newCertificate :
      StateConstitutiveCertificate newContract newArtifact newState)
    (correspondence : ValidatedStableNodeCorrespondence
      oldCertificate.basis.naming newCertificate.basis.naming)
    (key : StableNodeKey)
    (outside : affectedConstitutiveNode oldCertificate newCertificate
      correspondence (.artifactNode key) = false) :
    lookupStructuralObservation key
        (structuralObservationSnapshot oldCertificate) =
      lookupStructuralObservation key
        (structuralObservationSnapshot newCertificate) := by
  have initialFalse := affectedWithin_false_initial_false
    (initiallyAffected oldCertificate newCertificate correspondence)
    (heterogeneousDependencyEdges newCertificate.basis.naming)
    (completeConstitutiveKeys newCertificate).length
    (.artifactNode key) outside
  change structuralInitiallyAffected
    (keyOccurs (.artifactNode key) (transportedArtifactKeys correspondence))
    (observationOptionsSame
      (lookupStructuralObservation key
        (structuralObservationSnapshot oldCertificate))
      (lookupStructuralObservation key
        (structuralObservationSnapshot newCertificate))) = false at initialFalse
  exact observationOptionsSame_true _ _
    (structuralInitiallyAffected_false_unchanged_true _ _ initialFalse)

theorem publicRequirementNode_is_outsideAffectedCone :
    affectedConstitutiveNode publicInitialStateConstitutiveCertificate
      publicReferenceUpdatedStateCertificate publicStableNodeCorrespondence
      (.artifactNode (.receivedInput 1)) = false := by
  rfl

theorem publicAuthorizationNode_is_affected :
    affectedConstitutiveNode publicInitialStateConstitutiveCertificate
      publicReferenceUpdatedStateCertificate publicStableNodeCorrespondence
      (.artifactNode (.receivedInput 2)) = true := by
  rfl

theorem publicProposalNeuron_is_affected :
    affectedConstitutiveNode publicInitialStateConstitutiveCertificate
      publicReferenceUpdatedStateCertificate publicStableNodeCorrespondence
      (.artifactNode (.neuron 0)) = true := by
  rfl

theorem publicAction_is_affected_downstream :
    affectedConstitutiveNode publicInitialStateConstitutiveCertificate
      publicReferenceUpdatedStateCertificate publicStableNodeCorrespondence
      .action = true := by
  rfl

end ConstitutiveSearch.NeuralAgent
/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.NeuralAgent.StableArtifactObservation
#print axioms ConstitutiveSearch.NeuralAgent.stableNodeKeyEquality
#print axioms ConstitutiveSearch.NeuralAgent.contractObservationKindEquality
#print axioms ConstitutiveSearch.NeuralAgent.constitutiveNodeKeyEquality
#print axioms ConstitutiveSearch.NeuralAgent.stableWeightedReadEquality
#print axioms ConstitutiveSearch.NeuralAgent.stableWeightedReadsEquality
#print axioms ConstitutiveSearch.NeuralAgent.stableArtifactObservationEquality
#print axioms ConstitutiveSearch.NeuralAgent.observationOptionEquality
#print axioms ConstitutiveSearch.NeuralAgent.observationOptionsSame
#print axioms ConstitutiveSearch.NeuralAgent.observationOptionsSame_true
#print axioms ConstitutiveSearch.NeuralAgent.structuralInitiallyAffected
#print axioms ConstitutiveSearch.NeuralAgent.structuralInitiallyAffected_false_unchanged_true
#print axioms ConstitutiveSearch.NeuralAgent.naturalNumbersSame
#print axioms ConstitutiveSearch.NeuralAgent.integersSame
#print axioms ConstitutiveSearch.NeuralAgent.stableNodeKeysSame
#print axioms ConstitutiveSearch.NeuralAgent.stableNodeKeysSame_true
#print axioms ConstitutiveSearch.NeuralAgent.stableWeightedReadsSame
#print axioms ConstitutiveSearch.NeuralAgent.stableWeightedReadsSame_true
#print axioms ConstitutiveSearch.NeuralAgent.stableArtifactObservationsSame
#print axioms ConstitutiveSearch.NeuralAgent.stableArtifactObservationsSame_true
#print axioms ConstitutiveSearch.NeuralAgent.keyOccurs
#print axioms ConstitutiveSearch.NeuralAgent.structuralObservationSnapshot
#print axioms ConstitutiveSearch.NeuralAgent.transportedArtifactKeys
#print axioms ConstitutiveSearch.NeuralAgent.ConstitutiveDependencyEdge
#print axioms ConstitutiveSearch.NeuralAgent.heterogeneousDependencyEdges
#print axioms ConstitutiveSearch.NeuralAgent.initiallyAffected
#print axioms ConstitutiveSearch.NeuralAgent.affectedWithin
#print axioms ConstitutiveSearch.NeuralAgent.affectedConstitutiveNode
#print axioms ConstitutiveSearch.NeuralAgent.affectedConstitutiveCone
#print axioms ConstitutiveSearch.NeuralAgent.outsideAffectedCone_unchanged
#print axioms ConstitutiveSearch.NeuralAgent.publicRequirementNode_is_outsideAffectedCone
#print axioms ConstitutiveSearch.NeuralAgent.publicAuthorizationNode_is_affected
#print axioms ConstitutiveSearch.NeuralAgent.publicProposalNeuron_is_affected
#print axioms ConstitutiveSearch.NeuralAgent.publicAction_is_affected_downstream
/- AXIOM_AUDIT_END -/
