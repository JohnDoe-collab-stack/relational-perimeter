import RelationalPerimeter.Agents.Neural.LearnedRuntimeAdapterCore

/-!
# Successive learned runtime adapter

This module closes the received, predecessor-indexed successive transition,
incremental certificate assembly, dependent checker, and certified runtime.
Its public module name remains the stable import boundary for consumers.
-/
set_option genInjectivity false
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
namespace ConstitutiveSearch.NeuralAgent
open NativeMechanism
open ContinuationSignatures

/-! ## One successive analysis consumed by both checker interfaces -/

/-- Every dependency retained here has been obtained by executing the decoder,
the reflected transition decision, and the two finite authorization checks on
the received update.  No checked target or target certificate is a field. -/
structure LearnedSuccessiveExecutedDependencies
    (source : LearnedSerializedConstitutiveUpdate) : Type 6 where
  decoded : DecodedLearnedSuccessiveUpdate source
  decodedExact : decodeLearnedSuccessiveUpdate source = .ok decoded
  receivedDecision : AcceptedTransitionDecision
    learnedExecutableMetaContractInterface source.transition
  transitionAccepted :
    decideTransition learnedExecutableMetaContractInterface source.transition =
      some receivedDecision
  authorizationConsumed :
    primaryAuthorizationConstitutivelyConsumed source.targetNetwork = true
  targetNetworkExact :
    source.targetNetwork = independentLearnedSecondSuccessorNetwork

theorem LearnedSuccessiveExecutedDependencies.unique
    {source : LearnedSerializedConstitutiveUpdate}
    (left right : LearnedSuccessiveExecutedDependencies source) :
    left = right := by
  cases left with
  | mk leftDecoded leftDecodedExact leftDecision leftTransitionAccepted
      leftAuthorization leftTarget =>
      cases right with
      | mk rightDecoded rightDecodedExact rightDecision rightTransitionAccepted
          rightAuthorization rightTarget =>
          have decodedExact : leftDecoded = rightDecoded :=
            Except.ok.inj (leftDecodedExact.symm.trans rightDecodedExact)
          cases decodedExact
          have decisionExact : leftDecision = rightDecision :=
            Option.some.inj
              (leftTransitionAccepted.symm.trans rightTransitionAccepted)
          cases decisionExact
          rfl

def LearnedSuccessiveExecutedDependencies.extendedDecision
    {source : LearnedSerializedConstitutiveUpdate}
    (executed : LearnedSuccessiveExecutedDependencies source) :
    AcceptedTransitionDecision learnedExecutableMetaContractInterface
      ({ current := .aligned, next := .extended } :
        ContractTransitionRequest learnedConstitutiveMetaContract) :=
  executed.receivedDecision.transportRequest executed.decoded.transitionExact

/-- Execute the canonical successive transition used by the reference engine.
This constructor is intentionally specialized to `LearnedAlignedCheckedAgent`;
the dependent runtime path is distinct and passes its received predecessor to
`analyzeDecodedLearnedSuccessiveUpdateAtCurrent`. -/
def LearnedSuccessiveExecutedDependencies.production
    {source : LearnedSerializedConstitutiveUpdate}
    (executed : LearnedSuccessiveExecutedDependencies source) :
    ExecutedTransitionProduction learnedTransitionProductionKernel
      (current := LearnedAlignedCheckedAgent)
      executed.extendedDecision.transition .installExtended :=
  produceTransition learnedTransitionProductionKernel LearnedAlignedCheckedAgent
    executed.extendedDecision.transition .installExtended

theorem LearnedSuccessiveExecutedDependencies.production_target_exact
    {source : LearnedSerializedConstitutiveUpdate}
    (executed : LearnedSuccessiveExecutedDependencies source) :
    executed.production.targetState = learnedExtendedState := by
  have decisionExact := executed.extendedDecision.unique
    learnedExtendedTransitionDecision
  cases decisionExact
  rfl

def LearnedSuccessiveExecutedDependencies.preCertificateGraph
    {source : LearnedSerializedConstitutiveUpdate}
    (executed : LearnedSuccessiveExecutedDependencies source) :
    PreCertificateConstitutiveGraph
      LearnedAlignedCheckedAgent.certificate.basis.naming
      executed.decoded.stable.naming :=
  calculatePreCertificateConstitutiveGraph
    LearnedAlignedCheckedAgent.certificate.basis.naming
    executed.decoded.stable.naming

def LearnedSuccessiveExecutedDependencies.transportedLicenses
    {source : LearnedSerializedConstitutiveUpdate}
    (executed : LearnedSuccessiveExecutedDependencies source) :
    List (LicensedStructuralTransport LearnedAlignedCheckedAgent.certificate
      executed.preCertificateGraph) :=
  calculateLicensedStructuralTransports LearnedAlignedCheckedAgent.certificate
    executed.preCertificateGraph

def LearnedSuccessiveExecutedDependencies.recomputedStructural
    {source : LearnedSerializedConstitutiveUpdate}
    (executed : LearnedSuccessiveExecutedDependencies source) :
    List (StableNodeKey × StableArtifactObservation) :=
  recomputeAffectedStructuralObservations LearnedAlignedCheckedAgent.certificate
    executed.decoded.stable.naming executed.preCertificateGraph

/-- Execute and validate the structural assembly on the received decoded
naming.  Success retains the observations produced by the calculation itself;
the target snapshot is used only as the independently decoded equality check. -/
def checkLearnedSuccessiveStructuralAssembly
    {source : LearnedSerializedConstitutiveUpdate}
    (executed : LearnedSuccessiveExecutedDependencies source) :
    Except LearnedRuntimeUpdateError
      (CalculatedIncrementalStructuralAssembly
        LearnedAlignedCheckedAgent.certificate executed.preCertificateGraph
        (licensedStructuralEntries executed.transportedLicenses)
        executed.recomputedStructural) :=
  match calculated : calculateIncrementalStructuralAssembly
      LearnedAlignedCheckedAgent.certificate executed.preCertificateGraph
      (licensedStructuralEntries executed.transportedLicenses)
      executed.recomputedStructural with
  | .error _ => .error .structuralAssembly
  | .ok observations =>
      if targetExact : observations =
          stableStructuralObservationSnapshot executed.decoded.stable.naming then
        .ok (certifyCalculatedIncrementalStructuralAssembly calculated targetExact)
      else
        .error .structuralMismatch

theorem checkLearnedSuccessiveStructuralAssembly_of_calculated
    {source : LearnedSerializedConstitutiveUpdate}
    (executed : LearnedSuccessiveExecutedDependencies source)
    (assembly : CalculatedIncrementalStructuralAssembly
      LearnedAlignedCheckedAgent.certificate executed.preCertificateGraph
      (licensedStructuralEntries executed.transportedLicenses)
      executed.recomputedStructural) :
    checkLearnedSuccessiveStructuralAssembly executed = .ok assembly := by
  rcases assembly with ⟨assemblyObservations, assemblyCalculated,
    assemblyTargetExact⟩
  unfold checkLearnedSuccessiveStructuralAssembly
  split
  · have impossible :=
      ‹calculateIncrementalStructuralAssembly
          LearnedAlignedCheckedAgent.certificate executed.preCertificateGraph
          (licensedStructuralEntries executed.transportedLicenses)
          executed.recomputedStructural = .error _›.symm.trans
        assemblyCalculated
    cases impossible
  · rename_i observations calculated
    have observationsExact : observations = assemblyObservations :=
      Except.ok.inj (calculated.symm.trans assemblyCalculated)
    cases observationsExact
    split
    · rfl
    · exact False.elim (‹assemblyObservations ≠
        stableStructuralObservationSnapshot executed.decoded.stable.naming›
          assemblyTargetExact)

structure LearnedSuccessiveEngineAnalysis
    (source : LearnedSerializedConstitutiveUpdate) : Type 6 where
  private mk ::
  executed : LearnedSuccessiveExecutedDependencies source
  structuralAssembly : CalculatedIncrementalStructuralAssembly
    LearnedAlignedCheckedAgent.certificate executed.preCertificateGraph
    (licensedStructuralEntries executed.transportedLicenses)
    executed.recomputedStructural
  structuralAssemblyChecked :
    checkLearnedSuccessiveStructuralAssembly executed = .ok structuralAssembly

/-- The only public formation rule for an engine analysis.  It consumes the
executed dependencies, the assembly calculated over those exact dependencies,
and the successful local check; it cannot receive a completed target
certificate from outside the engine. -/
def LearnedSuccessiveEngineAnalysis.ofExecuted
    {source : LearnedSerializedConstitutiveUpdate}
    (executed : LearnedSuccessiveExecutedDependencies source)
    (structuralAssembly : CalculatedIncrementalStructuralAssembly
      LearnedAlignedCheckedAgent.certificate executed.preCertificateGraph
      (licensedStructuralEntries executed.transportedLicenses)
      executed.recomputedStructural)
    (structuralAssemblyChecked :
      checkLearnedSuccessiveStructuralAssembly executed = .ok structuralAssembly) :
    LearnedSuccessiveEngineAnalysis source :=
  .mk executed structuralAssembly structuralAssemblyChecked

def learnedExtendedFiniteCausalBasisFromReceived
    (target : DecodedNeuralArtifact LearnedExtendedOperationalContract)
    (naming : StableArtifactNaming target)
    (targetExact : target = learnedDecodedExtendedArtifact) :
    FiniteCausalBasis LearnedExtendedOperationalContract target := by
  subst target
  exact learnedExtendedFiniteCausalBasisFor naming

theorem learnedExtendedFiniteCausalBasisFromReceived_naming_exact
    (target : DecodedNeuralArtifact LearnedExtendedOperationalContract)
    (naming : StableArtifactNaming target)
    (targetExact : target = learnedDecodedExtendedArtifact) :
    (learnedExtendedFiniteCausalBasisFromReceived target naming
      targetExact).naming = naming := by
  subst target
  rfl

def learnedExtendedRecomputedCertificateFragmentsFromReceived
    (target : DecodedNeuralArtifact LearnedExtendedOperationalContract)
    (state : ReconfiguredExecutionState
      LearnedExtendedOperationalContract.family)
    (targetExact : target = learnedDecodedExtendedArtifact)
    (stateExact : state = learnedExtendedState) :
    RecomputedStateCertificateFragments LearnedExtendedOperationalContract
      target state := by
  subst target
  subst state
  exact learnedExtendedRecomputedCertificateFragments

theorem learnedExtendedReceivedState_system_exact
    (target : DecodedNeuralArtifact LearnedExtendedOperationalContract)
    (state : ReconfiguredExecutionState
      LearnedExtendedOperationalContract.family)
    (targetExact : target = learnedDecodedExtendedArtifact)
    (stateExact : state = learnedExtendedState) :
    state.system = target.system := by
  subst target
  subst state
  rfl

def learnedExtendedReceivedState_input_declared
    (state : ReconfiguredExecutionState
      LearnedExtendedOperationalContract.family)
    (stateExact : state = learnedExtendedState) :
    Listed state.input LearnedExtendedOperationalContract.declaredCurrentInputs := by
  subst state
  exact .tail (.tail .head)

/-- Build the successive analysis from one executed received-dependency chain.
The artifact and naming are the decoder outputs; the state and execution are
the two projections of one transition production; and the structural fields
are calculated on that received naming.  Exact-domain equalities are used only
to transport semantic witnesses indexed by those data. -/
def learnedSuccessiveTargetAnalysisFromReceivedArtifact
    {source : LearnedSerializedConstitutiveUpdate}
    (executed : LearnedSuccessiveExecutedDependencies source)
    (structuralAssembly : CalculatedIncrementalStructuralAssembly
      LearnedAlignedCheckedAgent.certificate executed.preCertificateGraph
      (licensedStructuralEntries executed.transportedLicenses)
      executed.recomputedStructural) :
    IncrementalTargetAnalysis LearnedAlignedCheckedAgent :=
  { nextContract := .extended
    contractAdmitted := .extended
    artifact := executed.decoded.target
    state := executed.production.targetState
    targetNaming := executed.decoded.stable.naming
    preCertificateGraph := executed.preCertificateGraph
    transportedLicenses := executed.transportedLicenses
    recomputedStructural := executed.recomputedStructural
    structuralAssembly := structuralAssembly
    structuralBasis := learnedExtendedFiniteCausalBasisFromReceived
      executed.decoded.target executed.decoded.stable.naming
      (executed.decoded.targetArtifactExact executed.targetNetworkExact)
    structuralBasisNamingExact :=
      learnedExtendedFiniteCausalBasisFromReceived_naming_exact
        executed.decoded.target executed.decoded.stable.naming
        (executed.decoded.targetArtifactExact executed.targetNetworkExact)
    structuralSystemExact := learnedExtendedReceivedState_system_exact
      executed.decoded.target executed.production.targetState
      (executed.decoded.targetArtifactExact executed.targetNetworkExact)
      executed.production_target_exact
    structuralInputDeclared := learnedExtendedReceivedState_input_declared
      executed.production.targetState executed.production_target_exact
    recomputedCertificateFragments :=
      learnedExtendedRecomputedCertificateFragmentsFromReceived
        executed.decoded.target executed.production.targetState
        (executed.decoded.targetArtifactExact executed.targetNetworkExact)
        executed.production_target_exact
    transition := executed.extendedDecision.transition
    execution := executed.production.execution }

theorem learnedSuccessiveTargetAnalysisFromReceivedArtifact_artifact_exact
    {source : LearnedSerializedConstitutiveUpdate}
    (executed : LearnedSuccessiveExecutedDependencies source)
    (structuralAssembly : CalculatedIncrementalStructuralAssembly
      LearnedAlignedCheckedAgent.certificate executed.preCertificateGraph
      (licensedStructuralEntries executed.transportedLicenses)
      executed.recomputedStructural) :
    HEq (learnedSuccessiveTargetAnalysisFromReceivedArtifact executed
      structuralAssembly).artifact
      executed.decoded.target := by
  rfl

theorem learnedSuccessiveTargetAnalysisFromReceivedArtifact_naming_exact
    {source : LearnedSerializedConstitutiveUpdate}
    (executed : LearnedSuccessiveExecutedDependencies source)
    (structuralAssembly : CalculatedIncrementalStructuralAssembly
      LearnedAlignedCheckedAgent.certificate executed.preCertificateGraph
      (licensedStructuralEntries executed.transportedLicenses)
      executed.recomputedStructural) :
    HEq (learnedSuccessiveTargetAnalysisFromReceivedArtifact executed
      structuralAssembly).targetNaming executed.decoded.stable.naming := by
  rfl

/-- The target analysis is transported from the data actually decoded from
the received update.  Eliminating the exact decoder equations is what makes
the calculated graph, transported fragments, recomputed fragments, produced
state, and executed transition share one dependent target. -/
def LearnedSuccessiveEngineAnalysis.target
    {source : LearnedSerializedConstitutiveUpdate}
    (analysis : LearnedSuccessiveEngineAnalysis source) :
    IncrementalTargetAnalysis LearnedAlignedCheckedAgent := by
  exact learnedSuccessiveTargetAnalysisFromReceivedArtifact analysis.executed
    analysis.structuralAssembly

theorem LearnedSuccessiveEngineAnalysis.receivedDecodedArtifact_installed
    {source : LearnedSerializedConstitutiveUpdate}
    (analysis : LearnedSuccessiveEngineAnalysis source) :
    HEq analysis.target.artifact analysis.executed.decoded.target := by
  rfl

theorem LearnedSuccessiveEngineAnalysis.receivedDecodedStableNaming_installed
    {source : LearnedSerializedConstitutiveUpdate}
    (analysis : LearnedSuccessiveEngineAnalysis source) :
    HEq analysis.target.targetNaming analysis.executed.decoded.stable.naming := by
  rfl

theorem LearnedSuccessiveEngineAnalysis.receivedProductionTarget_installed
    {source : LearnedSerializedConstitutiveUpdate}
    (analysis : LearnedSuccessiveEngineAnalysis source) :
    HEq analysis.target.state analysis.executed.production.targetState := by
  rfl

theorem LearnedSuccessiveEngineAnalysis.receivedProductionExecution_installed
    {source : LearnedSerializedConstitutiveUpdate}
    (analysis : LearnedSuccessiveEngineAnalysis source) :
    HEq analysis.target.execution analysis.executed.production.execution := by
  rfl

theorem LearnedSuccessiveEngineAnalysis.receivedStructuralGraph_installed
    {source : LearnedSerializedConstitutiveUpdate}
    (analysis : LearnedSuccessiveEngineAnalysis source) :
    HEq analysis.target.preCertificateGraph
      analysis.executed.preCertificateGraph := by
  rfl

theorem LearnedSuccessiveEngineAnalysis.receivedTransportedLicenses_installed
    {source : LearnedSerializedConstitutiveUpdate}
    (analysis : LearnedSuccessiveEngineAnalysis source) :
    HEq analysis.target.transportedLicenses
      analysis.executed.transportedLicenses := by
  rfl

theorem LearnedSuccessiveEngineAnalysis.receivedStructuralFragments_installed
    {source : LearnedSerializedConstitutiveUpdate}
    (analysis : LearnedSuccessiveEngineAnalysis source) :
    analysis.target.recomputedStructural =
      analysis.executed.recomputedStructural := by
  rfl

theorem LearnedSuccessiveEngineAnalysis.receivedStructuralAssembly_installed
    {source : LearnedSerializedConstitutiveUpdate}
    (analysis : LearnedSuccessiveEngineAnalysis source) :
    HEq analysis.target.structuralAssembly analysis.structuralAssembly := by
  rfl

theorem LearnedSuccessiveEngineAnalysis.structuralAssembly_installed
    {source : LearnedSerializedConstitutiveUpdate}
    (analysis : LearnedSuccessiveEngineAnalysis source) :
    analysis.target.structuralAssembly.observations =
      stableStructuralObservationSnapshot analysis.target.targetNaming :=
  analysis.target.structuralAssembly.targetExact

/-- Finish one already executed dependency chain by running its structural
assembly check.  This named boundary lets completeness transport the exact
received chain without re-evaluating or reconstructing it. -/
def analyzeLearnedSuccessiveExecutedDependencies
    {source : LearnedSerializedConstitutiveUpdate}
    (executed : LearnedSuccessiveExecutedDependencies source) :
    Except LearnedRuntimeUpdateError (LearnedSuccessiveEngineAnalysis source) :=
  match assemblyChecked : checkLearnedSuccessiveStructuralAssembly executed with
  | .error problem => .error problem
  | .ok structuralAssembly =>
      .ok (.mk executed structuralAssembly assemblyChecked)

/-- Execute the remaining reflected checks for an already decoded successive
request.  This is the sole producer of a successive engine analysis. -/
def analyzeDecodedLearnedSuccessiveUpdate
    (source : LearnedSerializedConstitutiveUpdate)
    (decoded : DecodedLearnedSuccessiveUpdate source)
    (decodedExact : decodeLearnedSuccessiveUpdate source = .ok decoded) :
    Except LearnedRuntimeUpdateError (LearnedSuccessiveEngineAnalysis source) :=
  match transitionAccepted :
      decideTransition learnedExecutableMetaContractInterface source.transition with
  | none => .error .unexpectedTransition
  | some receivedDecision =>
      if authorizationConsumed :
          primaryAuthorizationConstitutivelyConsumed source.targetNetwork = true then
        if targetNetworkExact : source.targetNetwork =
            independentLearnedSecondSuccessorNetwork then
          let executed : LearnedSuccessiveExecutedDependencies source :=
            { decoded := decoded
              decodedExact := decodedExact
              receivedDecision := receivedDecision
              transitionAccepted := transitionAccepted
              authorizationConsumed := authorizationConsumed
              targetNetworkExact := targetNetworkExact }
          analyzeLearnedSuccessiveExecutedDependencies executed
        else
          .error .unsupportedTargetArtifact
      else
        .error .missingConstitutiveDependency

/-- Runtime successive analysis.  Unlike the canonical standalone engine, its
material producer, structural graph, transports, and recomputations all read
the exact predecessor argument received by the checker. -/
def analyzeDecodedLearnedSuccessiveUpdateAtCurrent
    (current : CheckedAgent learnedConstitutiveMetaContract .aligned)
    (currentExact : current = LearnedAlignedCheckedAgent)
    (source : LearnedSerializedConstitutiveUpdate)
    (decoded : DecodedLearnedSuccessiveUpdate source)
    (_decodedExact : decodeLearnedSuccessiveUpdate source = .ok decoded) :
    Except LearnedRuntimeUpdateError (IncrementalTargetAnalysis current) :=
  match transitionAccepted :
      decideTransition learnedExecutableMetaContractInterface source.transition with
  | none => .error .unexpectedTransition
  | some receivedDecision =>
      if authorizationConsumed :
          primaryAuthorizationConstitutivelyConsumed source.targetNetwork = true then
        if targetNetworkExact : source.targetNetwork =
            independentLearnedSecondSuccessorNetwork then
          let decision := receivedDecision.transportRequest decoded.transitionExact
          let production := produceTransition learnedTransitionProductionKernel current
            decision.transition .installExtended
          let graph := calculatePreCertificateConstitutiveGraph
            current.certificate.basis.naming decoded.stable.naming
          let transported := calculateLicensedStructuralTransports
            current.certificate graph
          let recomputed := recomputeAffectedStructuralObservations
            current.certificate decoded.stable.naming graph
          match calculated : calculateIncrementalStructuralAssembly
              current.certificate graph (licensedStructuralEntries transported)
              recomputed with
          | .error _ => .error .structuralAssembly
          | .ok observations =>
              if observationsExact : observations =
                  stableStructuralObservationSnapshot decoded.stable.naming then
                have productionTargetExact : production.targetState =
                    learnedExtendedState := by
                  cases currentExact
                  have decisionExact := decision.unique
                    learnedExtendedTransitionDecision
                  cases decisionExact
                  rfl
                let assembly := certifyCalculatedIncrementalStructuralAssembly
                  calculated observationsExact
                .ok
                  { nextContract := .extended
                    contractAdmitted := .extended
                    artifact := decoded.target
                    state := production.targetState
                    targetNaming := decoded.stable.naming
                    preCertificateGraph := graph
                    transportedLicenses := transported
                    recomputedStructural := recomputed
                    structuralAssembly := assembly
                    structuralBasis := learnedExtendedFiniteCausalBasisFromReceived
                      decoded.target decoded.stable.naming
                      (decoded.targetArtifactExact targetNetworkExact)
                    structuralBasisNamingExact :=
                      learnedExtendedFiniteCausalBasisFromReceived_naming_exact
                        decoded.target decoded.stable.naming
                        (decoded.targetArtifactExact targetNetworkExact)
                    structuralSystemExact := learnedExtendedReceivedState_system_exact
                      decoded.target production.targetState
                      (decoded.targetArtifactExact targetNetworkExact)
                      productionTargetExact
                    structuralInputDeclared := learnedExtendedReceivedState_input_declared
                      production.targetState productionTargetExact
                    recomputedCertificateFragments :=
                      learnedExtendedRecomputedCertificateFragmentsFromReceived
                        decoded.target production.targetState
                        (decoded.targetArtifactExact targetNetworkExact)
                        productionTargetExact
                    transition := decision.transition
                    execution := production.execution }
              else
                .error .structuralMismatch
        else
          .error .unsupportedTargetArtifact
      else
        .error .missingConstitutiveDependency

def analyzeLearnedSuccessiveUpdate
    (source : LearnedSerializedConstitutiveUpdate) :
    Except LearnedRuntimeUpdateError (LearnedSuccessiveEngineAnalysis source) :=
  match decodedExact : decodeLearnedSuccessiveUpdate source with
  | .error problem => .error problem
  | .ok decoded =>
      analyzeDecodedLearnedSuccessiveUpdate source decoded decodedExact

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.NeuralAgent.LearnedSuccessiveExecutedDependencies
#print axioms ConstitutiveSearch.NeuralAgent.LearnedSuccessiveExecutedDependencies.production
#print axioms ConstitutiveSearch.NeuralAgent.LearnedSuccessiveExecutedDependencies.preCertificateGraph
#print axioms ConstitutiveSearch.NeuralAgent.LearnedSuccessiveExecutedDependencies.transportedLicenses
#print axioms ConstitutiveSearch.NeuralAgent.LearnedSuccessiveExecutedDependencies.recomputedStructural
#print axioms ConstitutiveSearch.NeuralAgent.checkLearnedSuccessiveStructuralAssembly
#print axioms ConstitutiveSearch.NeuralAgent.LearnedSuccessiveEngineAnalysis
#print axioms ConstitutiveSearch.NeuralAgent.LearnedSuccessiveEngineAnalysis.ofExecuted
#print axioms ConstitutiveSearch.NeuralAgent.LearnedSuccessiveEngineAnalysis.target
#print axioms ConstitutiveSearch.NeuralAgent.analyzeLearnedSuccessiveExecutedDependencies
#print axioms ConstitutiveSearch.NeuralAgent.analyzeDecodedLearnedSuccessiveUpdateAtCurrent
/- AXIOM_AUDIT_END -/

