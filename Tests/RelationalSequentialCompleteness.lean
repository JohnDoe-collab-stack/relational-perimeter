import RelationalPerimeter.Constitution.Godel.RelationalCompleteness
import RelationalPerimeter.Instances.HeytingArithmetic.RelationalCompleteness

set_option autoImplicit false
set_option linter.unusedVariables false

namespace RelationalPerimeter.Tests.RelationalSequentialCompleteness

open StrongPerimetralTurning
open StrongPerimetralTurning.GodelGroupingTower
open StrongPerimetralTurning.GodelRelationalCompleteness
open StrongPerimetralTurning.GodelRuntimePersistence
open RelationalPerimeter.HeytingArithmetic
open RelationalPerimeter.Constitution.Reals
open RelationalPerimeter.Constitution.Reals.ConstitutiveRuntime
open RelationalPerimeter.Constitution.Reals.ProducedCompleteness
open RelationalPerimeter.Constitution.Reals.AuthoritativeRuntime
open ConstitutiveSearch.ContinuationSignatures

abbrev P : CircularPresentation :=
  godelPerimetralPresentation heytingArithmeticGodelExecution

def baseCode : SignedDyadicCode :=
  { positive := 3, negative := 1, scale := 2 }

def producedConstantProducer : SourceProducer :=
  { calculate := fun _request => baseCode }

/-- A concrete executed Cauchy family whose codes are produced during search. -/
def producedConstantFamily : ExecutedCauchyFamily P 1 where
  producer := producedConstantProducer
  termCoherent := fun _term precision _leftPrecision _rightPrecision
      _leftBeyond _rightBeyond =>
    Near.refl precision baseCode
  modulus := fun precision => precision
  modulusMonotone := fun extension => extension
  cauchy := by
    intro precision firstJournal secondJournal firstRequest secondRequest
      firstBeyond secondBeyond firstRefines secondRefines first second
    rw [first.readout_is_storedAction, second.readout_is_storedAction]
    rw [sourceProgram_actionCode_exact, sourceProgram_actionCode_exact]
    exact Near.refl precision baseCode

def rootJournal : Journal P 1 :=
  Journal.root P 1

def sourceAt (precision : Nat) : producedConstantFamily.SourceAt precision :=
  producedConstantFamily.diagonalSourceAt precision

def producedSourceAt (precision : Nat) :
    producedConstantFamily.ProducedSourceAt rootJournal (sourceAt precision) :=
  producedConstantFamily.produceSourceAt rootJournal (sourceAt precision)

theorem producedSourceReadoutIsCalculated (precision : Nat) :
    (producedSourceAt precision).readout = baseCode := by
  rw [(producedSourceAt precision).readout_is_calculated]
  rfl

def executedLimitProductionAtFour :
    ExecutedLimitProduction producedConstantFamily rootJournal 4 :=
  executeLimitProduction producedConstantFamily rootJournal 4

theorem executedLimitConsumesItsOwnedSource :
    executedLimitProductionAtFour.readout =
      executedLimitProductionAtFour.source.readout :=
  executedLimitProductionAtFour.readout_is_source

theorem executedLimitReadoutComesFromGroupingAction :
    executedLimitProductionAtFour.readout =
      (LimitGrouping.program executedLimitProductionAtFour.source).actionCode
        executedLimitProductionAtFour.execution.action :=
  executedLimitProductionAtFour.readout_is_groupingAction

/-- The retained witness relates the executed source to the produced target. -/
def executedLimitSourceNearProducedTarget :
    Near 4 executedLimitProductionAtFour.source.readout
      executedLimitProductionAtFour.targetCode :=
  executedLimitProductionAtFour.sourceNearTarget

/-- The public target witness is a transport of the one produced by normalization. -/
theorem executedLimitTargetWitnessIsNormalized :
    HEq executedLimitProductionAtFour.execution.action.target.sourceNearTarget
      executedLimitProductionAtFour.execution.action.target.normalized.consumedNearTarget :=
  LimitGrouping.ProducedTarget.sourceNearTarget_is_normalized _

/-- Acceptance consumes that same normalized witness, without a Cauchy replay. -/
theorem executedLimitPreservationUsesNormalizedWitness :
    HEq executedLimitProductionAtFour.execution.memory.continued.authorized.accepted.preservation
      executedLimitProductionAtFour.execution.action.target.normalized.consumedNearTarget :=
  LimitGrouping.Accepted.preservation_is_normalized _

theorem executedLimitProductionReachesDepthThirteen :
    executedLimitProductionAtFour.completedJournal.absoluteDepth = 13 := by
  rw [executedLimitProductionAtFour.completedDepth]
  rfl

/-- A second source is distinct by request, not identified by its equal code. -/
def secondSource : producedConstantFamily.SourceAt 4 where
  request := { term := 5, precision := 5 }
  indexBeyondModulus := { extra := 1, exact := rfl }
  readoutRefines := { extra := 1, exact := rfl }

theorem sourceRequestsRemainDistinct : sourceAt 4 ≠ secondSource := by
  intro equality
  have termEquality := congrArg
    (fun source : producedConstantFamily.SourceAt 4 => source.request.term)
    equality
  exact (by decide : (4 : Nat) ≠ 5) termEquality

def emptyExecutedSourceChain :
    producedConstantFamily.ExecutedSourceChain 4 rootJournal rootJournal 0 :=
  .empty rootJournal

def firstExecutedSourceChain :=
  ExecutedCauchyFamily.ExecutedSourceChain.append
    producedConstantFamily emptyExecutedSourceChain (sourceAt 4)

def secondExecutedSourceChain :=
  ExecutedCauchyFamily.ExecutedSourceChain.append
    producedConstantFamily firstExecutedSourceChain secondSource

theorem emptyExecutedSourceChainDepthExact :
    rootJournal.absoluteDepth = rootJournal.absoluteDepth +
      ExecutedCauchyFamily.ExecutedSourceChain.operationCount 0 :=
  emptyExecutedSourceChain.finalDepth_exact

theorem firstExecutedSourceChainDepthExact :
    (producedConstantFamily.produceSourceAt rootJournal
      (sourceAt 4)).completedJournal.absoluteDepth =
        rootJournal.absoluteDepth +
          ExecutedCauchyFamily.ExecutedSourceChain.operationCount 1 :=
  firstExecutedSourceChain.finalDepth_exact

theorem secondExecutedSourceChainDepthExact :
    (producedConstantFamily.produceSourceAt
      (producedConstantFamily.produceSourceAt rootJournal
        (sourceAt 4)).completedJournal secondSource).completedJournal.absoluteDepth =
        rootJournal.absoluteDepth +
          ExecutedCauchyFamily.ExecutedSourceChain.operationCount 2 :=
  secondExecutedSourceChain.finalDepth_exact

def finiteBatchGrouping :
    producedConstantFamily.ExecutedFiniteGrouping secondExecutedSourceChain :=
  producedConstantFamily.executeFiniteGrouping secondExecutedSourceChain

/-- Exhaustivity is the structural consumption of this exact chronological chain. -/
def finiteBatchGroupingConsumesEverySource :
    producedConstantFamily.ExactConsumption finiteBatchGrouping.anchor
      secondExecutedSourceChain :=
  finiteBatchGrouping.consumesEverySource

theorem finiteBatchGroupingShapeIsExact :
    finiteBatchGrouping.consumption.indexing = allIndices 2 :=
  finiteBatchGrouping.consumptionShape_exact

theorem finiteBatchExactConsumptionCount :
    finiteBatchGrouping.consumption.count = 2 :=
  finiteBatchGrouping.consumption.count_exact

theorem finiteBatchGroupingReadoutIsProducedTarget :
    finiteBatchGrouping.readout = finiteBatchGrouping.target.readout :=
  finiteBatchGrouping.readout_is_producedTarget

theorem finiteBatchHistoricalNormalizationAccepted :
    HistoricalGrouping.BatchAccepted
      (.target : HistoricalGrouping.BatchState 2)
      finiteBatchGrouping.normalizedBatch :=
  finiteBatchGrouping.normalizedBatch_accepted

theorem finiteBatchHistoricalNormalizationConsumesTwo :
    finiteBatchGrouping.normalizedBatch.consumed.length = 2 :=
  finiteBatchGrouping.normalizedBatch_consumed_length

def initialRuntime : Runtime producedConstantFamily :=
  initialState producedConstantFamily

theorem initialRuntimeHasNoReadout : read initialRuntime = none :=
  rfl

def limitStepAtFour :
    ExecutedStep producedConstantFamily initialRuntime (.limit 4) :=
  perform producedConstantFamily initialRuntime (.limit 4)

theorem limitStepReadoutIsFromItsRetainedResponse :
    read limitStepAtFour.next = some limitStepAtFour.response.observation :=
  limitStepAtFour.next_read

def singletonLimitRun :
    ExecutedRun producedConstantFamily initialRuntime [.limit 4] :=
  ExecutedRun.singleton limitStepAtFour

def singletonLimitRunFinalReachable :
    Reachable producedConstantFamily singletonLimitRun.finalState :=
  singletonLimitRun.finalReachable (.initial)

def commonRefusalStamp : RequestStamp := .source 99 101

theorem unsupportedRequestPreservesContinuation :
    runCommon producedConstantFamily initialRuntime
        [.unsupported commonRefusalStamp, .limit 4] =
      .step (read initialRuntime) false
        (.refused initialRuntime.journal.absoluteDepth commonRefusalStamp)
        (runCommon producedConstantFamily initialRuntime [.limit 4]) :=
  refusal_continues producedConstantFamily initialRuntime
    commonRefusalStamp [.limit 4]

def commonRuntimeRealization :
    ExactRealization (futureContract producedConstantFamily) ReducedState :=
  runtimeRealization producedConstantFamily

def initialLiveRuntime : LiveRuntime :=
  initializeLive producedConstantFamily

theorem unsupportedLiveRequestPreservesContinuation :
    runLive producedConstantFamily initialLiveRuntime
        [.unsupported commonRefusalStamp, .limit 4] =
      .step (readLive initialLiveRuntime) false
        (.refused initialLiveRuntime.depth commonRefusalStamp)
        (runLive producedConstantFamily initialLiveRuntime [.limit 4]) :=
  rfl

theorem equalLiveRuntimeHasSameFiniteFutures :
    FutureEquivalent (liveContract producedConstantFamily)
      initialLiveRuntime initialLiveRuntime :=
  (liveMinimality producedConstantFamily).1 rfl

theorem equalLiveMemoryHasSameFiniteFutures :
    FutureEquivalent (futureContract producedConstantFamily)
      initialRuntime initialRuntime :=
  (minimality producedConstantFamily).1 rfl

def completeGodelRaccord :
    Result heytingArithmeticGodelExecution producedConstantFamily :=
  raccord heytingArithmeticGodelExecution producedConstantFamily

theorem completeGodelRaccordReachesDepthThirteen :
    completeGodelRaccord.firstLimitProduction.completedJournal.absoluteDepth = 13 :=
  firstLimitProduction_depth_thirteen
    heytingArithmeticGodelExecution producedConstantFamily

theorem completeGodelRaccordSourceReachesDepthSeven :
    completeGodelRaccord.firstLimitProduction.source.completedJournal.absoluteDepth =
      7 :=
  firstSource_depth_seven
    heytingArithmeticGodelExecution producedConstantFamily

def persistedThroughOwnedRun :
    RunPersistence heytingArithmeticGodelExecution producedConstantFamily
      completeGodelRaccord.firstRun.traceEvidence
      completeGodelRaccord.initialPersistence :=
  completeGodelRaccord.runPersistence

def persistedThroughOwnedLimitProduction :
    PersistedGodelOccurrences
      heytingArithmeticGodelExecution
      completeGodelRaccord.firstLimitProduction.completedJournal.absoluteDepth := by
  rw [← completeGodelRaccord.finalJournalExact]
  exact completeGodelRaccord.persistedThroughLimit

theorem completeGodelRaccordUsesUniversalProducer :
    completeGodelRaccord.firstLimitProduction =
      completeGodelRaccord.firstRun.firstStep.response.limitProduction :=
  completeGodelRaccord.firstLimitProductionExact

theorem completeGodelRaccordFirstRunReusesProducedStep :
    completeGodelRaccord.firstRun.firstStep =
      completeGodelRaccord.producedReal.produce
        completeGodelRaccord.initial completeGodelRaccord.initialReachable 0 := by
  rw [completeGodelRaccord.firstRunExact]
  exact completeGodelRaccord.firstStepExact

theorem completeGodelRaccordUsesCanonicalMaster :
    completeGodelRaccord.firstLimitProduction =
      executeLimitProduction producedConstantFamily
        completeGodelRaccord.initial.journal 0 :=
  rfl

theorem completeGodelRaccordUniversalProducerUsesRuntime
    (precision : Nat) :
    completeGodelRaccord.producedReal.produce
        completeGodelRaccord.initial completeGodelRaccord.initialReachable
        precision =
      perform producedConstantFamily completeGodelRaccord.initial
        (.limit precision) :=
  completeGodelRaccord.producedRealRuntimeExact _
    completeGodelRaccord.initialReachable precision

def reachableSourceStepAtZero :
    ExecutedStep producedConstantFamily completeGodelRaccord.initial
      (.source 0 (producedConstantFamily.diagonalSourceAt 0)) :=
  perform producedConstantFamily completeGodelRaccord.initial
    (.source 0 (producedConstantFamily.diagonalSourceAt 0))

/-- Terminal convergence consumes reachability of both source and limit states. -/
def completeGodelRaccordSourceNearUsesReachableStates :
    Near 0 reachableSourceStepAtZero.response.readout
      (completeGodelRaccord.producedReal.produce
        completeGodelRaccord.initial completeGodelRaccord.initialReachable
        0).response.readout :=
  completeGodelRaccord.sourceNearProducedLimit 0
    completeGodelRaccord.initialReachable
    (producedConstantFamily.diagonalSourceAt 0)
    reachableSourceStepAtZero
    completeGodelRaccord.initialReachable

end RelationalPerimeter.Tests.RelationalSequentialCompleteness

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Tests.RelationalSequentialCompleteness.P
#print axioms RelationalPerimeter.Tests.RelationalSequentialCompleteness.baseCode
#print axioms RelationalPerimeter.Tests.RelationalSequentialCompleteness.producedConstantProducer
#print axioms RelationalPerimeter.Tests.RelationalSequentialCompleteness.producedConstantFamily
#print axioms RelationalPerimeter.Tests.RelationalSequentialCompleteness.rootJournal
#print axioms RelationalPerimeter.Tests.RelationalSequentialCompleteness.sourceAt
#print axioms RelationalPerimeter.Tests.RelationalSequentialCompleteness.producedSourceAt
#print axioms RelationalPerimeter.Tests.RelationalSequentialCompleteness.producedSourceReadoutIsCalculated
#print axioms RelationalPerimeter.Tests.RelationalSequentialCompleteness.executedLimitProductionAtFour
#print axioms RelationalPerimeter.Tests.RelationalSequentialCompleteness.executedLimitConsumesItsOwnedSource
#print axioms RelationalPerimeter.Tests.RelationalSequentialCompleteness.executedLimitReadoutComesFromGroupingAction
#print axioms RelationalPerimeter.Tests.RelationalSequentialCompleteness.executedLimitSourceNearProducedTarget
#print axioms RelationalPerimeter.Tests.RelationalSequentialCompleteness.executedLimitTargetWitnessIsNormalized
#print axioms RelationalPerimeter.Tests.RelationalSequentialCompleteness.executedLimitPreservationUsesNormalizedWitness
#print axioms RelationalPerimeter.Tests.RelationalSequentialCompleteness.executedLimitProductionReachesDepthThirteen
#print axioms RelationalPerimeter.Tests.RelationalSequentialCompleteness.secondSource
#print axioms RelationalPerimeter.Tests.RelationalSequentialCompleteness.sourceRequestsRemainDistinct
#print axioms RelationalPerimeter.Tests.RelationalSequentialCompleteness.emptyExecutedSourceChain
#print axioms RelationalPerimeter.Tests.RelationalSequentialCompleteness.firstExecutedSourceChain
#print axioms RelationalPerimeter.Tests.RelationalSequentialCompleteness.secondExecutedSourceChain
#print axioms RelationalPerimeter.Tests.RelationalSequentialCompleteness.emptyExecutedSourceChainDepthExact
#print axioms RelationalPerimeter.Tests.RelationalSequentialCompleteness.firstExecutedSourceChainDepthExact
#print axioms RelationalPerimeter.Tests.RelationalSequentialCompleteness.secondExecutedSourceChainDepthExact
#print axioms RelationalPerimeter.Tests.RelationalSequentialCompleteness.finiteBatchGrouping
#print axioms RelationalPerimeter.Tests.RelationalSequentialCompleteness.finiteBatchGroupingConsumesEverySource
#print axioms RelationalPerimeter.Tests.RelationalSequentialCompleteness.finiteBatchGroupingShapeIsExact
#print axioms RelationalPerimeter.Tests.RelationalSequentialCompleteness.finiteBatchExactConsumptionCount
#print axioms RelationalPerimeter.Tests.RelationalSequentialCompleteness.finiteBatchGroupingReadoutIsProducedTarget
#print axioms RelationalPerimeter.Tests.RelationalSequentialCompleteness.finiteBatchHistoricalNormalizationAccepted
#print axioms RelationalPerimeter.Tests.RelationalSequentialCompleteness.finiteBatchHistoricalNormalizationConsumesTwo
#print axioms RelationalPerimeter.Tests.RelationalSequentialCompleteness.initialRuntime
#print axioms RelationalPerimeter.Tests.RelationalSequentialCompleteness.initialRuntimeHasNoReadout
#print axioms RelationalPerimeter.Tests.RelationalSequentialCompleteness.limitStepAtFour
#print axioms RelationalPerimeter.Tests.RelationalSequentialCompleteness.limitStepReadoutIsFromItsRetainedResponse
#print axioms RelationalPerimeter.Tests.RelationalSequentialCompleteness.singletonLimitRun
#print axioms RelationalPerimeter.Tests.RelationalSequentialCompleteness.singletonLimitRunFinalReachable
#print axioms RelationalPerimeter.Tests.RelationalSequentialCompleteness.commonRefusalStamp
#print axioms RelationalPerimeter.Tests.RelationalSequentialCompleteness.unsupportedRequestPreservesContinuation
#print axioms RelationalPerimeter.Tests.RelationalSequentialCompleteness.commonRuntimeRealization
#print axioms RelationalPerimeter.Tests.RelationalSequentialCompleteness.initialLiveRuntime
#print axioms RelationalPerimeter.Tests.RelationalSequentialCompleteness.unsupportedLiveRequestPreservesContinuation
#print axioms RelationalPerimeter.Tests.RelationalSequentialCompleteness.equalLiveRuntimeHasSameFiniteFutures
#print axioms RelationalPerimeter.Tests.RelationalSequentialCompleteness.equalLiveMemoryHasSameFiniteFutures
#print axioms RelationalPerimeter.Tests.RelationalSequentialCompleteness.completeGodelRaccord
#print axioms RelationalPerimeter.Tests.RelationalSequentialCompleteness.completeGodelRaccordReachesDepthThirteen
#print axioms RelationalPerimeter.Tests.RelationalSequentialCompleteness.completeGodelRaccordSourceReachesDepthSeven
#print axioms RelationalPerimeter.Tests.RelationalSequentialCompleteness.persistedThroughOwnedRun
#print axioms RelationalPerimeter.Tests.RelationalSequentialCompleteness.persistedThroughOwnedLimitProduction
#print axioms RelationalPerimeter.Tests.RelationalSequentialCompleteness.completeGodelRaccordUsesUniversalProducer
#print axioms RelationalPerimeter.Tests.RelationalSequentialCompleteness.completeGodelRaccordFirstRunReusesProducedStep
#print axioms RelationalPerimeter.Tests.RelationalSequentialCompleteness.completeGodelRaccordUsesCanonicalMaster
#print axioms RelationalPerimeter.Tests.RelationalSequentialCompleteness.completeGodelRaccordUniversalProducerUsesRuntime
#print axioms RelationalPerimeter.Tests.RelationalSequentialCompleteness.reachableSourceStepAtZero
#print axioms RelationalPerimeter.Tests.RelationalSequentialCompleteness.completeGodelRaccordSourceNearUsesReachableStates
/- AXIOM_AUDIT_END -/
