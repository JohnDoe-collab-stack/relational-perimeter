import RelationalPerimeter.Agents.Neural.ParameterizedCompiledCheckerFamily

/-!
# Causal parameterized family for complete-property scaling

The historical v11 family remains unchanged: it measured rich state
obligations but its transition relation did not make the successor depend on
the predecessor.  This family closes that gap.  Every target state is produced
by executing the target network's action from the exact memory of the checked
source.  The incremental checker and the independent full recheck consume the
same proof-free command and certify that same produced transition.

This parameterized family is an experimental scaling workload.  It does not
replace `IndependentLearnedArtifact` or supply the learned weights of the
substantive public lineage.
-/
set_option genInjectivity false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
namespace ConstitutiveSearch.NeuralAgent
open NativeMechanism

def causalScalingStateWithMemory
    (size : Nat) (version : ScalingArtifactVersion) (memory : Agent.Memory) :
    ReconfiguredExecutionState publicRequirementFamily :=
  { system := scalingSystem size version
    input := scalingInput
    memory := memory }

def causalScalingActionState
    (source : ReconfiguredExecutionState publicRequirementFamily)
    (size : Nat) (version : ScalingArtifactVersion) :
    ReconfiguredExecutionState publicRequirementFamily :=
  causalScalingStateWithMemory size version source.memory

/-- The measured action is the action produced by the proposal channel itself.
There is no second request-selection layer between the neural proposal and the
executor.  In particular, a proposal for `.advance 0` remains `.advance 0`;
structural progress of an accepted artifact update is never simulated by
rewriting its operational request. -/
abbrev CausalScalingActionWitness
    (state : ReconfiguredExecutionState publicRequirementFamily) :=
  ScalingActionWitness state

def causalScalingAction
    (source : ReconfiguredExecutionState publicRequirementFamily)
    (size : Nat) (version : ScalingArtifactVersion) :
    CausalScalingActionWitness (causalScalingActionState source size version) :=
  executeScalingAction (causalScalingActionState source size version)

/-- Effect produced from the exact proposal action occurrence.  The action
stored here is the one that was executed; no extensionally equal request is
executed again to manufacture the successor. -/
structure CausalScalingEffectWitness
    (state : ReconfiguredExecutionState publicRequirementFamily) : Type 3 where
  private mk ::
  action : CausalScalingActionWitness state
  successor : Agent.Memory
  event : Agent.Event
  successorExact : successor = action.result.1
  eventExact : event = action.result.2

def causalScalingEffectOfAction
    {source : ReconfiguredExecutionState publicRequirementFamily}
    {size : Nat} {version : ScalingArtifactVersion}
    (action : CausalScalingActionWitness
      (causalScalingActionState source size version)) :
    CausalScalingEffectWitness (causalScalingActionState source size version) :=
  { action := action
    successor := action.result.1
    event := action.result.2
    successorExact := rfl
    eventExact := rfl }

def causalScalingEffect
    (source : ReconfiguredExecutionState publicRequirementFamily)
    (size : Nat) (version : ScalingArtifactVersion) :
    CausalScalingEffectWitness (causalScalingActionState source size version) :=
  causalScalingEffectOfAction (causalScalingAction source size version)

/-- The successor is computed from the effect whose action reads the exact
source memory.  No target memory is accepted as an argument. -/
def causalScalingTargetState
    (source : ReconfiguredExecutionState publicRequirementFamily)
    (size : Nat) (version : ScalingArtifactVersion) :
    ReconfiguredExecutionState publicRequirementFamily :=
  causalScalingStateWithMemory size version
    (causalScalingEffect source size version).successor

/-- Substantive execution relation for the measured family.  It retains the
exact action and effect produced from the source memory and identifies the
target with their successor. -/
structure CausalScalingExecutedStateTransition
    (source target : ReconfiguredExecutionState publicRequirementFamily) : Type 4 where
  size : Nat
  version : ScalingArtifactVersion
  action : CausalScalingActionWitness
    (causalScalingActionState source size version)
  actionExact : action = causalScalingAction source size version
  effect : CausalScalingEffectWitness (causalScalingActionState source size version)
  effectActionExact : effect.action = action
  targetExact : target = causalScalingStateWithMemory size version effect.successor

def causalScalingMetaContract : ConstitutiveMetaContract where
  Contract := Unit
  operational := fun _ => scalingContract
  Admits := fun _ => Unit
  TransitionPermission := fun _ _ => Unit
  PersistentObligation := fun _ _ => Unit
  SourcePersistentWitness := fun _ _ _ => ScalingUnit3
  TargetPersistentWitness := fun _ _ _ => ScalingUnit3
  transportPersistent := fun _ _ _ => scalingUnit3
  RecheckObligation := fun _ _ => Unit
  RecheckedWitness := fun _ _ _ => ScalingUnit3
  recheckInvalidated := fun _ _ => scalingUnit3
  ExecutedStateTransition := fun _ source target =>
    CausalScalingExecutedStateTransition source target

def causalScalingOperationalTransition :
    OperationalContractTransition causalScalingMetaContract () () :=
  certifyOperationalContractTransition () () ()

structure CausalScalingTransitionCommand where
  size : Nat
  version : ScalingArtifactVersion
  deriving DecidableEq, Repr

/-- Private production object owned by the causal transition kernel. -/
structure CausalScalingTransitionProduction
    (source : ReconfiguredExecutionState publicRequirementFamily)
    (command : CausalScalingTransitionCommand) : Type 3 where
  private mk ::
  action : CausalScalingActionWitness
    (causalScalingActionState source command.size command.version)
  actionExact : action = causalScalingAction source command.size command.version
  effect : CausalScalingEffectWitness
    (causalScalingActionState source command.size command.version)
  effectActionExact : effect.action = action
  target : ReconfiguredExecutionState publicRequirementFamily
  targetExact : target = causalScalingStateWithMemory command.size command.version
    effect.successor

def produceCausalScalingTransition
    (source : ReconfiguredExecutionState publicRequirementFamily)
    (command : CausalScalingTransitionCommand) :
    CausalScalingTransitionProduction source command :=
  let action := causalScalingAction source command.size command.version
  let effect := causalScalingEffectOfAction action
  .mk action rfl effect rfl
    (causalScalingStateWithMemory command.size command.version effect.successor) rfl

def causalScalingTransitionKernel :
    TransitionProductionKernel causalScalingMetaContract where
  Material := fun _ _ => ULift.{3} CausalScalingTransitionCommand
  Production := fun current _ command =>
    CausalScalingTransitionProduction current.state command.down
  produce := fun current _ command =>
    produceCausalScalingTransition current.state command.down
  targetOf := fun _ _ _ production => production.target
  execution := fun _ _ command production =>
    { size := command.down.size
      version := command.down.version
      action := production.action
      actionExact := production.actionExact
      effect := production.effect
      effectActionExact := production.effectActionExact
      targetExact := production.targetExact }

theorem causalScalingProducedTarget_exact
    {current : CheckedAgent causalScalingMetaContract ()}
    (transition : OperationalContractTransition causalScalingMetaContract () ())
    (command : CausalScalingTransitionCommand) :
    (produceTransition causalScalingTransitionKernel current
      transition (ULift.up command)).targetState =
        causalScalingTargetState current.state command.size command.version := by
  rfl

def causalScalingStateFragmentsOfProducedState
    (size : Nat) (version : ScalingArtifactVersion)
    (memory : Agent.Memory)
    (state : ReconfiguredExecutionState publicRequirementFamily)
    (stateExact : state =
      causalScalingStateWithMemory size version memory) :
    StateCertificateFragments scalingContract
      (scalingDecodedArtifact size version)
      state :=
  let basis := scalingFiniteCausalBasis size version
  let action := executeScalingAction state
  let effect : ScalingEffectWitness state :=
    { action := action
      successor := action.result.1
      event := action.result.2
      successorExact := rfl
      eventExact := rfl }
  {
    structural :=
      { basis := basis
        systemExact := by rw [stateExact]; rfl
        inputDeclared := by rw [stateExact]; exact .head
        observations := stableStructuralObservationSnapshot basis.naming
        observationsExact := rfl },
    requirement :=
      { witness := by
          rw [stateExact]
          exact
            { incorporation := publicRequirementIncorporation scalingInput
              port := publicRequirementPort
              encodedValue := 2
              encodedExact := rfl } },
    causal :=
      { witness := by
          rw [stateExact]
          exact
            { port := publicRequirementPort
              role := scalingCausalRole size version } },
    proposalAction := { witness := action },
    authorization :=
      { witness :=
          { incorporated := publicReconfigurationAuthorization state.input } },
    effect := { witness := effect },
    historical :=
      { witness :=
          { run := state.system.run state.input
            runExact := rfl } },
    futures :=
      { covered := fun requests => publicInteractionHistory state.memory requests
        realization := scalingFutureRealization } }

def causalScalingStateFragments
    (size : Nat) (version : ScalingArtifactVersion) (memory : Agent.Memory) :
    StateCertificateFragments scalingContract
      (scalingDecodedArtifact size version)
      (causalScalingStateWithMemory size version memory) :=
  causalScalingStateFragmentsOfProducedState size version
    memory (causalScalingStateWithMemory size version memory) rfl

def causalScalingRecomputedCertificateFragmentsOfProducedState
    (size : Nat) (version : ScalingArtifactVersion)
    (memory : Agent.Memory)
    (state : ReconfiguredExecutionState publicRequirementFamily)
    (stateExact : state =
      causalScalingStateWithMemory size version memory) :
    RecomputedStateCertificateFragments scalingContract
      (scalingDecodedArtifact size version) state :=
  let fragments := causalScalingStateFragmentsOfProducedState size version memory
    state stateExact
  { requirement := fragments.requirement
    causal := fragments.causal
    proposalAction := fragments.proposalAction
    authorization := fragments.authorization
    effect := fragments.effect
    historical := fragments.historical
    futures := fragments.futures }

def causalScalingRecomputedCertificateFragments
    (size : Nat) (version : ScalingArtifactVersion) (memory : Agent.Memory) :
    RecomputedStateCertificateFragments scalingContract
      (scalingDecodedArtifact size version)
      (causalScalingStateWithMemory size version memory) :=
  causalScalingRecomputedCertificateFragmentsOfProducedState size version
    memory (causalScalingStateWithMemory size version memory) rfl

def causalScalingStateCertificate
    (size : Nat) (version : ScalingArtifactVersion) (memory : Agent.Memory) :
    StateConstitutiveCertificate scalingContract
      (scalingDecodedArtifact size version)
      (causalScalingStateWithMemory size version memory) :=
  assembleStateConstitution (causalScalingStateFragments size version memory)

def causalScalingInitialAgent (size : Nat) :
    CheckedAgent causalScalingMetaContract () :=
  certifyCheckedAgent () (scalingDecodedArtifact size .source)
    (causalScalingStateWithMemory size .source publicActionMemory)
    (causalScalingStateCertificate size .source publicActionMemory)

abbrev CausalScalingReceivedArtifact := CausalScalingTransitionCommand

def causalScalingExecutableInterface
    (current : CheckedAgent causalScalingMetaContract ()) :
    ExecutableMetaContractInterface causalScalingMetaContract where
  ContractCode := Unit
  encodeContract := fun _ => ()
  encodeContractInjective := by intro left right _; cases left; cases right; rfl
  ContractNameError := Empty
  decodeContractName := fun _ => .ok { contract := (), exact := rfl }
  ReceivedArtifact := CausalScalingReceivedArtifact
  artifactContractCode := fun _ => ()
  artifactNetwork := fun source => scalingSerializedNetwork source.size source.version
  artifactStableNaming := fun source => scalingSerializedStableNaming source.size
  ArtifactError := Empty
  DecodedArtifact := fun _ => ScalingDecodedToken
  decodedContract := fun _ => ()
  decodedContractExact := fun _ => rfl
  decodedNeuralArtifact := fun {source} _ =>
    scalingDecodedArtifact source.size source.version
  decodedNetworkExact := fun _ => rfl
  decodedStableNaming := fun {source} _ =>
    scalingDecodedStableNaming source.size source.version
  decodeReceivedArtifact := fun _ => .ok scalingDecodedToken
  stateOfArtifact := fun {source} _ =>
    causalScalingTargetState current.state source.size source.version
  admissionDecision := fun _ => scalingReflectedTrue ()
  transitionDecision := fun _ =>
    scalingReflectedTrue causalScalingOperationalTransition
  basisDecision := fun {source} _ =>
    scalingReflectedTrue (scalingFiniteCausalBasis source.size source.version)
  systemDecision := fun _ => scalingReflectedTrue rfl
  declaredInputDecision := fun _ => scalingReflectedTrue Listed.head
  requirementDecision := fun {source} _ =>
    scalingReflectedTrue
      { incorporation := publicRequirementIncorporation scalingInput
        port := publicRequirementPort
        encodedValue := 2
        encodedExact := rfl }
  contextDecision := fun {source} _ =>
    scalingReflectedTrue
      { port := publicRequirementPort
        role := scalingCausalRole source.size source.version }
  authorizationDecision := fun _ =>
    scalingReflectedTrue
      { incorporated := publicReconfigurationAuthorization scalingInput }
  actionDecision := fun {source} _ =>
    scalingReflectedTrue
      (executeScalingAction
        (causalScalingTargetState current.state source.size source.version))
  effectDecision := fun {source} _ =>
    scalingReflectedTrue
      (produceScalingEffect
        (causalScalingTargetState current.state source.size source.version))
  historicalDecision := fun {source} _ =>
    scalingReflectedTrue
      { run := (causalScalingTargetState current.state source.size source.version).system.run
          (causalScalingTargetState current.state source.size source.version).input
        runExact := rfl }
  coveredFuturesDecision := fun {source} _ =>
    scalingReflectedTrue (fun requests =>
      publicInteractionHistory
        (causalScalingTargetState current.state source.size source.version).memory
        requests)
  futureRealizationDecision := fun _ =>
    scalingReflectedTrue scalingFutureRealization

structure CausalScalingIncrementalDecodedTarget
    (current : CheckedAgent causalScalingMetaContract ())
    (update : CausalScalingReceivedArtifact) : Type 5 where
  decodedArtifact :
    (causalScalingExecutableInterface current).DecodedArtifact update
  decodedExact :
    (causalScalingExecutableInterface current).decodeReceivedArtifact update =
      .ok decodedArtifact

def decodeCausalScalingIncrementalTarget
    (current : CheckedAgent causalScalingMetaContract ())
    (update : CausalScalingReceivedArtifact) :
    Except ScalingCheckerError
      (CausalScalingIncrementalDecodedTarget current update) :=
  .ok { decodedArtifact := scalingDecodedToken, decodedExact := rfl }

def causalScalingIncrementalGraph
    (current : CheckedAgent causalScalingMetaContract ())
    {update : CausalScalingReceivedArtifact}
    (target : CausalScalingIncrementalDecodedTarget current update) :
    PreCertificateConstitutiveGraph current.certificate.basis.naming
      ((causalScalingExecutableInterface current).decodedStableNaming
        target.decodedArtifact).naming :=
  calculatePreCertificateConstitutiveGraph current.certificate.basis.naming
    ((causalScalingExecutableInterface current).decodedStableNaming
      target.decodedArtifact).naming

def causalScalingIncrementalTransportLicenses
    (current : CheckedAgent causalScalingMetaContract ())
    {update : CausalScalingReceivedArtifact}
    (target : CausalScalingIncrementalDecodedTarget current update) :=
  calculateLicensedStructuralTransports current.certificate
    (causalScalingIncrementalGraph current target)

def causalScalingIncrementalTransported
    (current : CheckedAgent causalScalingMetaContract ())
    {update : CausalScalingReceivedArtifact}
    (target : CausalScalingIncrementalDecodedTarget current update) :=
  licensedStructuralEntries
    (causalScalingIncrementalTransportLicenses current target)

def causalScalingIncrementalRecomputed
    (current : CheckedAgent causalScalingMetaContract ())
    {update : CausalScalingReceivedArtifact}
    (target : CausalScalingIncrementalDecodedTarget current update) :=
  recomputeAffectedStructuralObservations current.certificate
    ((causalScalingExecutableInterface current).decodedStableNaming
      target.decodedArtifact).naming
    (causalScalingIncrementalGraph current target)

def calculateCausalScalingIncrementalStructuralAssembly
    (current : CheckedAgent causalScalingMetaContract ())
    {update : CausalScalingReceivedArtifact}
    (target : CausalScalingIncrementalDecodedTarget current update) :=
  calculateIncrementalStructuralAssembly current.certificate
    (causalScalingIncrementalGraph current target)
    (causalScalingIncrementalTransported current target)
    (causalScalingIncrementalRecomputed current target)

def checkCausalScalingIncrementalStructuralAssembly
    (current : CheckedAgent causalScalingMetaContract ())
    {update : CausalScalingReceivedArtifact}
    (target : CausalScalingIncrementalDecodedTarget current update) :
    Except ScalingCheckerError
      (CalculatedIncrementalStructuralAssembly current.certificate
        (causalScalingIncrementalGraph current target)
        (causalScalingIncrementalTransported current target)
        (causalScalingIncrementalRecomputed current target)) :=
  let graph := causalScalingIncrementalGraph current target
  match calculated : calculateCausalScalingIncrementalStructuralAssembly current target with
  | .error _ => .error .structuralAssembly
  | .ok observations =>
      if targetExact : observations = graph.targetObservations then
        .ok (certifyCalculatedIncrementalStructuralAssembly calculated targetExact)
      else
        .error .structuralMismatch

structure CausalScalingIncrementalAnalysis
    (current : CheckedAgent causalScalingMetaContract ())
    (update : CausalScalingReceivedArtifact) : Type 6 where
  target : CausalScalingIncrementalDecodedTarget current update
  assembly : CalculatedIncrementalStructuralAssembly current.certificate
    (causalScalingIncrementalGraph current target)
    (causalScalingIncrementalTransported current target)
    (causalScalingIncrementalRecomputed current target)
  transitionDecision : AcceptedTransitionDecision
    (causalScalingExecutableInterface current)
    { current := (), next := () }
  production : ExecutedTransitionProduction causalScalingTransitionKernel
    current transitionDecision.transition (ULift.up update)
  productionExact : production =
    produceTransition causalScalingTransitionKernel current
      transitionDecision.transition (ULift.up update)

structure CausalScalingIncrementalLocalConditions
    (current : CheckedAgent causalScalingMetaContract ())
    (update : CausalScalingReceivedArtifact) : Type 6 where
  target : CausalScalingIncrementalDecodedTarget current update
  targetChecked : decodeCausalScalingIncrementalTarget current update = .ok target
  assembly : CalculatedIncrementalStructuralAssembly current.certificate
    (causalScalingIncrementalGraph current target)
    (causalScalingIncrementalTransported current target)
    (causalScalingIncrementalRecomputed current target)
  assemblyChecked : checkCausalScalingIncrementalStructuralAssembly current target =
    .ok assembly
  transitionDecision : AcceptedTransitionDecision
    (causalScalingExecutableInterface current) { current := (), next := () }
  transitionAccepted : decideDecodedTransition
    (causalScalingExecutableInterface current) () target.decodedArtifact =
      some transitionDecision

def analyzeCausalScalingIncrementalUpdate
    (current : CheckedAgent causalScalingMetaContract ())
    (update : CausalScalingReceivedArtifact) :
    Except ScalingCheckerError (CausalScalingIncrementalAnalysis current update) :=
  match decodeCausalScalingIncrementalTarget current update with
  | .error problem => .error problem
  | .ok target =>
      match checkCausalScalingIncrementalStructuralAssembly current target with
      | .error problem => .error problem
      | .ok assembly =>
          match decideDecodedTransition (causalScalingExecutableInterface current) ()
              target.decodedArtifact with
          | none => .error .transition
          | some decision =>
              .ok
                { target := target
                  assembly := assembly
                  transitionDecision := decision
                  production := produceTransition causalScalingTransitionKernel current
                    decision.transition (ULift.up update)
                  productionExact := rfl }

def completeCausalScalingIncrementalAnalysis
    (current : CheckedAgent causalScalingMetaContract ())
    (update : CausalScalingReceivedArtifact)
    (conditions : CausalScalingIncrementalLocalConditions current update) :
    { analysis : CausalScalingIncrementalAnalysis current update //
      analyzeCausalScalingIncrementalUpdate current update = .ok analysis } := by
  unfold analyzeCausalScalingIncrementalUpdate
  split
  · have impossible := ‹decodeCausalScalingIncrementalTarget current update =
        .error _›.symm.trans conditions.targetChecked
    cases impossible
  · rename_i target targetChecked
    have targetExact : target = conditions.target :=
      Except.ok.inj (targetChecked.symm.trans conditions.targetChecked)
    cases targetExact
    rw [conditions.assemblyChecked]
    rw [conditions.transitionAccepted]
    exact ⟨_, rfl⟩

def causalScalingIncrementalLocalConditionsOfSuccess
    (current : CheckedAgent causalScalingMetaContract ())
    (update : CausalScalingReceivedArtifact)
    (analysis : CausalScalingIncrementalAnalysis current update)
    (accepted : analyzeCausalScalingIncrementalUpdate current update = .ok analysis) :
    CausalScalingIncrementalLocalConditions current update := by
  unfold analyzeCausalScalingIncrementalUpdate at accepted
  split at accepted
  · cases accepted
  · rename_i target targetChecked
    split at accepted
    · cases accepted
    · rename_i assembly assemblyChecked
      split at accepted
      · cases accepted
      · rename_i decision transitionAccepted
        have analysisExact := Except.ok.inj accepted
        cases analysisExact
        exact CausalScalingIncrementalLocalConditions.mk target targetChecked
          assembly assemblyChecked decision transitionAccepted

theorem causalScalingIncrementalProducedStateExact
    {current : CheckedAgent causalScalingMetaContract ()}
    {update : CausalScalingReceivedArtifact}
    (analysis : CausalScalingIncrementalAnalysis current update) :
    analysis.production.targetState =
      causalScalingStateWithMemory update.size update.version
        analysis.production.targetState.memory := by
  have stateProduced : analysis.production.targetState =
      causalScalingTargetState current.state update.size update.version :=
    (congrArg ExecutedTransitionProduction.targetState
      analysis.productionExact).trans
      (causalScalingProducedTarget_exact (current := current)
        analysis.transitionDecision.transition update)
  rw [stateProduced]
  rfl

def causalScalingIncrementalTargetAnalysis
    {current : CheckedAgent causalScalingMetaContract ()}
    {update : CausalScalingReceivedArtifact}
    (analysis : CausalScalingIncrementalAnalysis current update) :
    IncrementalTargetAnalysis current :=
  let state := analysis.production.targetState
  have stateExact : state =
      causalScalingTargetState current.state update.size update.version :=
    (congrArg ExecutedTransitionProduction.targetState
      analysis.productionExact).trans
      (causalScalingProducedTarget_exact (current := current)
        analysis.transitionDecision.transition update)
  { nextContract := ()
    contractAdmitted := ()
    artifact := scalingDecodedArtifact update.size update.version
    state := state
    targetNaming := scalingStableNaming update.size update.version
    preCertificateGraph := causalScalingIncrementalGraph current analysis.target
    transportedLicenses := causalScalingIncrementalTransportLicenses current analysis.target
    recomputedStructural := causalScalingIncrementalRecomputed current analysis.target
    structuralAssembly := analysis.assembly
    structuralBasis := scalingFiniteCausalBasis update.size update.version
    structuralBasisNamingExact := rfl
    structuralSystemExact := by rw [stateExact]; rfl
    structuralInputDeclared := by rw [stateExact]; exact .head
    recomputedCertificateFragments :=
      causalScalingRecomputedCertificateFragmentsOfProducedState
        update.size update.version state.memory state
        (causalScalingIncrementalProducedStateExact analysis)
    transition := analysis.transitionDecision.transition
    execution := analysis.production.execution }

def causalScalingIncrementalCheckerEngine
    (current : CheckedAgent causalScalingMetaContract ()) :
    IncrementalCheckerEngine current where
  Update := CausalScalingReceivedArtifact
  Error := ScalingCheckerError
  Analysis := CausalScalingIncrementalAnalysis current
  analyze := analyzeCausalScalingIncrementalUpdate current
  LocalConditions := CausalScalingIncrementalLocalConditions current
  complete := completeCausalScalingIncrementalAnalysis current
  localOfSuccess := causalScalingIncrementalLocalConditionsOfSuccess current
  target := causalScalingIncrementalTargetAnalysis

def causalScalingFullRecheckEngine
    (current : CheckedAgent causalScalingMetaContract ()) :
    FullRecheckEngine (causalScalingExecutableInterface current) current where
  Update := CausalScalingReceivedArtifact
  Error := ScalingCheckerError
  targetArtifact := fun update => update
  mapTargetError := fun _ => .target
  transitionRejected := .transition
  kernel := causalScalingTransitionKernel
  recomputeExecution := fun update _target _decision =>
    .ok { material := ULift.up update, targetExact := rfl }

theorem causalScalingIncrementalTarget_is_produced
    {current : CheckedAgent causalScalingMetaContract ()}
    {update : CausalScalingReceivedArtifact}
    (analysis : CausalScalingIncrementalAnalysis current update) :
    (causalScalingIncrementalTargetAnalysis analysis).state =
      causalScalingTargetState current.state update.size update.version := by
  change analysis.production.targetState =
    causalScalingTargetState current.state update.size update.version
  exact (congrArg ExecutedTransitionProduction.targetState
    analysis.productionExact).trans
    (causalScalingProducedTarget_exact (current := current)
      analysis.transitionDecision.transition update)

theorem causalScalingIncrementalProduction_consumes_source
    {current : CheckedAgent causalScalingMetaContract ()}
    {update : CausalScalingReceivedArtifact}
    (analysis : CausalScalingIncrementalAnalysis current update) :
    analysis.production.production.action =
      causalScalingAction current.state update.size update.version := by
  rw [analysis.productionExact]
  rfl

theorem causalScalingAction_reads_exact_source
    (source : ReconfiguredExecutionState publicRequirementFamily)
    (size : Nat) (version : ScalingArtifactVersion) :
    (causalScalingActionState source size version).memory = source.memory := by
  rfl

theorem causalScalingStateFragments_share_proposal_action
    (size : Nat) (version : ScalingArtifactVersion) (memory : Agent.Memory) :
    (causalScalingStateFragments size version memory).effect.witness.action =
      (causalScalingStateFragments size version memory).proposalAction.witness := by
  rfl

theorem causalScalingProducedStateFragments_use_received_state
    (size : Nat) (version : ScalingArtifactVersion)
    (memory : Agent.Memory)
    (state : ReconfiguredExecutionState publicRequirementFamily)
    (stateExact : state =
      causalScalingStateWithMemory size version memory) :
    (causalScalingStateFragmentsOfProducedState size version memory state
      stateExact).proposalAction.witness =
        executeScalingAction state := by
  cases stateExact
  rfl

theorem causalScalingIncrementalFragments_use_produced_state
    {current : CheckedAgent causalScalingMetaContract ()}
    {update : CausalScalingReceivedArtifact}
    (analysis : CausalScalingIncrementalAnalysis current update) :
    (causalScalingIncrementalTargetAnalysis analysis).recomputedCertificateFragments.proposalAction.witness =
      executeScalingAction analysis.production.targetState := by
  change
    (causalScalingRecomputedCertificateFragmentsOfProducedState update.size
      update.version analysis.production.targetState.memory
      analysis.production.targetState
      (causalScalingIncrementalProducedStateExact analysis)).proposalAction.witness =
        executeScalingAction analysis.production.targetState
  simpa only [causalScalingRecomputedCertificateFragmentsOfProducedState] using
      (causalScalingProducedStateFragments_use_received_state update.size
        update.version analysis.production.targetState.memory
        analysis.production.targetState
        (causalScalingIncrementalProducedStateExact analysis))

theorem causalScalingAction_is_exact_proposal_action
    (source : ReconfiguredExecutionState publicRequirementFamily)
    (size : Nat) (version : ScalingArtifactVersion) :
    causalScalingAction source size version =
      executeScalingAction (causalScalingActionState source size version) := by
  rfl

theorem causalScalingAction_request_is_proposal_request
    (source : ReconfiguredExecutionState publicRequirementFamily)
    (size : Nat) (version : ScalingArtifactVersion) :
    (causalScalingAction source size version).request =
      publicAgentActionChannel.command
        ((causalScalingActionState source size version).system.proposal
          (causalScalingActionState source size version).input) := by
  exact (causalScalingAction source size version).requestExact

/-- At the concrete first local update, the network proposes no memory advance.
The executed action preserves that decision instead of replacing it by a
synthetic positive step. -/
theorem causalScalingFirstLocalAction_is_advance_zero
    (source : ReconfiguredExecutionState publicRequirementFamily) :
    (causalScalingAction source 0 .local).request = .advance 0 := by
  rfl

/-- The first accepted update is structurally nontrivial even though its exact
proposal action is allowed to request zero memory steps.  Positivity is carried
by the received artifact transition, not fabricated in the action channel. -/
theorem causalScalingFirstUpdate_changes_serialized_system :
    scalingSerializedNetwork 0 .source ≠ scalingSerializedNetwork 0 .local := by
  decide

theorem causalScalingEffect_consumes_produced_action
    (source : ReconfiguredExecutionState publicRequirementFamily)
    (size : Nat) (version : ScalingArtifactVersion) :
    (causalScalingEffect source size version).action =
      causalScalingAction source size version := by
  rfl

theorem causalScalingTarget_consumes_produced_effect
    (source : ReconfiguredExecutionState publicRequirementFamily)
    (size : Nat) (version : ScalingArtifactVersion) :
    (causalScalingTargetState source size version).memory =
      (causalScalingEffect source size version).successor := by
  rfl

theorem causalScalingProduction_effect_exact
    {current : CheckedAgent causalScalingMetaContract ()}
    {update : CausalScalingReceivedArtifact}
    (analysis : CausalScalingIncrementalAnalysis current update) :
    analysis.production.production.effect =
      causalScalingEffect current.state update.size update.version := by
  rw [analysis.productionExact]
  rfl

theorem causalScalingProduction_effect_consumes_same_action
    {current : CheckedAgent causalScalingMetaContract ()}
    {update : CausalScalingReceivedArtifact}
    (analysis : CausalScalingIncrementalAnalysis current update) :
    analysis.production.production.effect.action =
      analysis.production.production.action := by
  exact analysis.production.production.effectActionExact

/-- Accounting inputs extracted from the exact causal analysis.  These counts
do not assert a time bound: they expose the growing graph, its affected cone,
and the fragments actually transported or recomputed by the compiled path. -/
def causalScalingPairMetrics
    {current : CheckedAgent causalScalingMetaContract ()}
    {update : CausalScalingReceivedArtifact}
    (analysis : CausalScalingIncrementalAnalysis current update) :
    ScalingPairMetrics :=
  let targetKeys :=
    (causalScalingIncrementalGraph current analysis.target).targetKeys
  let affected := affectedConstitutiveCone current.certificate
    (causalScalingIncrementalGraph current analysis.target)
  let structuralKeys := stableStructuralKeys
    ((causalScalingExecutableInterface current).decodedStableNaming
      analysis.target.decodedArtifact).naming
  let recomputed := causalScalingIncrementalRecomputed current analysis.target
  { neuralNodeCount := update.size + 2
    profileWidth := structuralKeys.length
    causalGraphNodeCount := targetKeys.length
    causalGraphEdgeCount :=
      (causalScalingIncrementalGraph current analysis.target).dependencyEdges.length
    affectedConeCount := affected.length
    transportedFragmentCount :=
      (causalScalingIncrementalTransportLicenses current analysis.target).length
    recomputedFragmentCount := recomputed.length
    otherNecessaryCalculationCount :=
      1 + targetKeys.length +
        (causalScalingIncrementalGraph current analysis.target).dependencyEdges.length +
        affected.length }

structure CausalScalingPairedStepResult
    (current : CheckedAgent causalScalingMetaContract ())
    (update : CausalScalingReceivedArtifact) : Type 8 where
  incremental : GenericIncrementalCheckSuccess
    (causalScalingIncrementalCheckerEngine current) update
  full : FullRecheckSuccess (causalScalingFullRecheckEngine current) update
  sameTarget : incremental.checked.next.state = full.checked.next.state

def checkCausalScalingStep
    (current : CheckedAgent causalScalingMetaContract ())
    (update : CausalScalingReceivedArtifact) :
    Except ScalingCheckerError (CausalScalingPairedStepResult current update) :=
  match checkGenericIncrementalUpdate
      (causalScalingIncrementalCheckerEngine current) update with
  | .error problem => .error problem
  | .ok incremental =>
      match checkFullUpdate (causalScalingFullRecheckEngine current) update with
      | .error problem => .error problem
      | .ok full =>
          .ok
            { incremental := incremental
              full := full
              sameTarget :=
                causalScalingIncrementalTarget_is_produced incremental.analysis }

structure CausalScalingStepObservation where
  step : Nat
  version : ScalingArtifactVersion
  transportedFragments : Nat
  recomputedFragments : Nat
  sourceRegisterLength : Nat
  targetRegisterLength : Nat
  deriving Repr

structure CausalScalingTraceResult (parameters : ScalingFamilyParameters) where
  final : CheckedAgent causalScalingMetaContract ()
  observations : List CausalScalingStepObservation
  lengthExact : observations.length = parameters.traceLength

def checkCausalScalingTraceFrom
    (size step : Nat)
    (current : CheckedAgent causalScalingMetaContract ()) :
    (remaining : Nat) -> Except ScalingCheckerError
      { result : CheckedAgent causalScalingMetaContract () ×
          List CausalScalingStepObservation // result.2.length = remaining }
  | 0 => .ok ⟨(current, []), rfl⟩
  | remaining + 1 =>
      let version := scalingVersionAt step
      let update : CausalScalingReceivedArtifact := { size := size, version := version }
      match checkCausalScalingStep current update with
      | .error problem => .error problem
      | .ok checked =>
          let next := checked.incremental.checked.next
          match checkCausalScalingTraceFrom size (step + 1) next remaining with
          | .error problem => .error problem
          | .ok tail =>
              .ok ⟨(tail.1.1,
                { step := step
                  version := version
                  transportedFragments := checked.incremental.target.transportedLicenses.length
                  recomputedFragments := checked.incremental.target.recomputedStructural.length
                  sourceRegisterLength := current.state.memory.register.length
                  targetRegisterLength := next.state.memory.register.length } :: tail.1.2),
                congrArg Nat.succ tail.2⟩

def checkCausalScalingFamily (parameters : ScalingFamilyParameters) :
    Except ScalingCheckerError (CausalScalingTraceResult parameters) :=
  let initial := causalScalingInitialAgent parameters.size
  match checkCausalScalingTraceFrom parameters.size 0 initial parameters.traceLength with
  | .error problem => .error problem
  | .ok result =>
      .ok (CausalScalingTraceResult.mk result.1.1 result.1.2 result.2)

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.NeuralAgent.causalScalingTargetState
#print axioms ConstitutiveSearch.NeuralAgent.causalScalingEffectOfAction
#print axioms ConstitutiveSearch.NeuralAgent.CausalScalingActionWitness
#print axioms ConstitutiveSearch.NeuralAgent.CausalScalingEffectWitness
#print axioms ConstitutiveSearch.NeuralAgent.CausalScalingExecutedStateTransition
#print axioms ConstitutiveSearch.NeuralAgent.causalScalingMetaContract
#print axioms ConstitutiveSearch.NeuralAgent.CausalScalingTransitionProduction
#print axioms ConstitutiveSearch.NeuralAgent.produceCausalScalingTransition
#print axioms ConstitutiveSearch.NeuralAgent.causalScalingTransitionKernel
#print axioms ConstitutiveSearch.NeuralAgent.causalScalingProducedTarget_exact
#print axioms ConstitutiveSearch.NeuralAgent.causalScalingStateFragmentsOfProducedState
#print axioms ConstitutiveSearch.NeuralAgent.causalScalingStateFragments
#print axioms ConstitutiveSearch.NeuralAgent.causalScalingRecomputedCertificateFragmentsOfProducedState
#print axioms ConstitutiveSearch.NeuralAgent.causalScalingInitialAgent
#print axioms ConstitutiveSearch.NeuralAgent.causalScalingExecutableInterface
#print axioms ConstitutiveSearch.NeuralAgent.analyzeCausalScalingIncrementalUpdate
#print axioms ConstitutiveSearch.NeuralAgent.causalScalingIncrementalProducedStateExact
#print axioms ConstitutiveSearch.NeuralAgent.causalScalingIncrementalTargetAnalysis
#print axioms ConstitutiveSearch.NeuralAgent.causalScalingFullRecheckEngine
#print axioms ConstitutiveSearch.NeuralAgent.causalScalingIncrementalTarget_is_produced
#print axioms ConstitutiveSearch.NeuralAgent.causalScalingIncrementalProduction_consumes_source
#print axioms ConstitutiveSearch.NeuralAgent.causalScalingAction_reads_exact_source
#print axioms ConstitutiveSearch.NeuralAgent.causalScalingStateFragments_share_proposal_action
#print axioms ConstitutiveSearch.NeuralAgent.causalScalingProducedStateFragments_use_received_state
#print axioms ConstitutiveSearch.NeuralAgent.causalScalingIncrementalFragments_use_produced_state
#print axioms ConstitutiveSearch.NeuralAgent.causalScalingAction_is_exact_proposal_action
#print axioms ConstitutiveSearch.NeuralAgent.causalScalingAction_request_is_proposal_request
#print axioms ConstitutiveSearch.NeuralAgent.causalScalingFirstLocalAction_is_advance_zero
#print axioms ConstitutiveSearch.NeuralAgent.causalScalingFirstUpdate_changes_serialized_system
#print axioms ConstitutiveSearch.NeuralAgent.causalScalingEffect_consumes_produced_action
#print axioms ConstitutiveSearch.NeuralAgent.causalScalingTarget_consumes_produced_effect
#print axioms ConstitutiveSearch.NeuralAgent.causalScalingProduction_effect_exact
#print axioms ConstitutiveSearch.NeuralAgent.causalScalingProduction_effect_consumes_same_action
#print axioms ConstitutiveSearch.NeuralAgent.causalScalingPairMetrics
#print axioms ConstitutiveSearch.NeuralAgent.checkCausalScalingStep
#print axioms ConstitutiveSearch.NeuralAgent.checkCausalScalingFamily
/- AXIOM_AUDIT_END -/
