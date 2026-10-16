import RelationalPerimeter.Constitution.Reals.LimitProduction
import RelationalPerimeter.Constitution.Godel.RelationalCompleteness
import RelationalPerimeter.Instances.HeytingArithmetic.Godel

set_option autoImplicit false
set_option linter.unusedVariables false

namespace RelationalPerimeter.Tests.RelationalSequentialCompleteness

open StrongPerimetralTurning
open StrongPerimetralTurning.GodelGroupingTower
open StrongPerimetralTurning.GodelRelationalCompleteness
open RelationalPerimeter.HeytingArithmetic
open RelationalPerimeter.Constitution.Reals

abbrev P : CircularPresentation :=
  godelPerimetralPresentation heytingArithmeticGodelExecution

def baseCode : SignedDyadicCode :=
  { positive := 3, negative := 1, scale := 2 }

def constantTerm (index : Nat) : RelationalReal P :=
  RelationalReal.constant P baseCode

def raisedConstant : RelationalReal P :=
  RelationalReal.constant P (baseCode.raise 2)

def constantPresentationEquivalent :
    RelationalReal.Equivalent (constantTerm 0) raisedConstant :=
  RelationalReal.constantEquivalent P (SameValue.raiseExact baseCode 2)

def constantEquivalenceRoundTrip :
    RelationalReal.Equivalent (constantTerm 0) (constantTerm 0) :=
  constantPresentationEquivalent.trans constantPresentationEquivalent.symm

/-- A concrete effective Cauchy family whose terms retain their indices. -/
def constantFamily : ExecutedCauchyFamily P where
  term := constantTerm
  modulus := fun precision => precision
  modulusMonotone := fun extension => extension
  cauchy := by
    intro precision firstIndex secondIndex firstReadout secondReadout
      firstBeyond secondBeyond firstRefines secondRefines
    exact
      ((SameValue.raiseExact baseCode firstReadout).symm.trans
        (SameValue.raiseExact baseCode secondReadout)).toNear precision

def completed : SequentialCompletenessResult constantFamily :=
  effectiveSequentialCompleteness constantFamily

def fullyCompleted : FullyExecutedSequentialCompleteness constantFamily :=
  fullyExecutedSequentialCompleteness constantFamily

theorem fullyCompletedRetainsSameSequentialResult :
    fullyCompleted.sequential = completed :=
  rfl

def sourceAt (precision : Nat) : constantFamily.SourceAt precision where
  index := precision
  readoutPrecision := precision
  indexBeyondModulus := PrecisionExtension.refl precision
  readoutRefines := PrecisionExtension.refl precision

def convergesAtEveryPrecision (precision : Nat) :
    Near precision
      (ExecutedCauchyFamily.sourceCode (sourceAt precision))
      (completed.limit.approximation precision) :=
  completed.convergence.near precision (sourceAt precision)

def rootJournal : OperationJournal ApproximationPayload :=
  .root

def producedSourceAt (precision : Nat) :
    constantFamily.ProducedSourceAt precision :=
  constantFamily.produceSourceAt rootJournal (sourceAt precision)

def executedLimitAtFour :
    ExecutedApproximation P rootJournal
      (limitPayload 4 (completed.limit.approximation 4)) :=
  completed.convergence.executeLimit rootJournal 4

theorem executedLimitReadoutAtFour :
    executedLimitAtFour.readout = completed.limit.approximation 4 :=
  completed.convergence.limitReadout_exact rootJournal 4

theorem groupedAtFour :
    (LocalGrouping.acceptanceAction
      (constantFamily.groupingEnvelope 4)).Accept
      LocalGrouping.State.target
      (effectiveLimitGroupedCharge constantFamily 4 (producedSourceAt 4)) :=
  effectiveLimit_groupedSourceAccepted constantFamily 4 (producedSourceAt 4)

theorem groupedAtFourConsumesExecutedSource :
    (effectiveLimitGroupedCharge constantFamily 4
      (producedSourceAt 4)).consumedCode = (producedSourceAt 4).code :=
  effectiveLimitGroupedCharge_consumesSourceCode constantFamily 4
    (producedSourceAt 4)

theorem groupedAtFourConsumesConvergenceWitness :
    (effectiveLimitGroupedCharge constantFamily 4
      (producedSourceAt 4)).consumedNearTarget =
        (producedSourceAt 4).nearLimit :=
  effectiveLimitGroupedCharge_consumesNear constantFamily 4
    (producedSourceAt 4)

theorem executedLimitReadoutIsGroupingAction :
    executedLimitAtFour.readout =
      effectiveLimitGroupedCode constantFamily 4 (producedSourceAt 4) :=
  effectiveLimitReadout_is_groupedCode constantFamily rootJournal 4
    (producedSourceAt 4)

def firstFiniteSelection :
    HistoricalGrouping.FiniteSelection
      (constantFamily.groupingEnvelope 4) 1 :=
  (HistoricalGrouping.emptySelection
    (constantFamily.groupingEnvelope 4)).snoc (producedSourceAt 4)

def secondSource : constantFamily.SourceAt 4 where
  index := 5
  readoutPrecision := 5
  indexBeyondModulus :=
    { extra := 1, exact := rfl }
  readoutRefines :=
    { extra := 1, exact := rfl }

def secondJournal : OperationJournal ApproximationPayload :=
  ExecutedApproximation.completedJournal rootJournal
    (sourcePayload (sourceAt 4).index (sourceAt 4).readoutPrecision
      (ExecutedCauchyFamily.sourceCode (sourceAt 4)))

def secondProducedSource : constantFamily.ProducedSourceAt 4 :=
  constantFamily.produceSourceAt secondJournal secondSource

/-- A distinct source produced at the same historical depth as the first. -/
def parallelProducedSource : constantFamily.ProducedSourceAt 4 :=
  constantFamily.produceSourceAt rootJournal secondSource

/-- Two actual source executions chained in one chronological journal. -/
def emptyExecutedSourceChain :
    ExecutedSourceChain constantFamily 4 rootJournal rootJournal 0 :=
  .empty rootJournal

def firstExecutedSourceChain :=
  emptyExecutedSourceChain.append (sourceAt 4)

def secondExecutedSourceChain :=
  firstExecutedSourceChain.append secondSource

def finiteBatchGrouping :=
  fullyCompleted.produceFiniteGrouping secondExecutedSourceChain

def consumedCodes :
    List (HistoricalGrouping.ConsumedSourceCharge 4
      (constantFamily.limitApproximation 4)) -> List SignedDyadicCode
  | [] => []
  | charge :: remaining => charge.code :: consumedCodes remaining

theorem finiteBatchGroupingConsumesExactChronology :
    finiteBatchGrouping.grouped.consumed =
      HistoricalGrouping.chargesForIndices
        secondExecutedSourceChain.selection
        (HistoricalGrouping.initialBatchCharge
          secondExecutedSourceChain.selection).available
        (HistoricalGrouping.allIndices 2) :=
  finiteBatchGrouping.consumedExact

theorem finiteBatchGroupingConsumesBothSources :
    finiteBatchGrouping.grouped.consumed.length = 2 :=
  finiteBatchGrouping.consumesEverySource

theorem finiteBatchGroupingConsumesCodesChronologically :
    consumedCodes finiteBatchGrouping.grouped.consumed =
      [ (producedSourceAt 4).code, secondProducedSource.code ] :=
  rfl

def finiteBatchGroupingOutputExact :
    SameValue finiteBatchGrouping.grouped.outputCode
      (constantFamily.limitApproximation 4) :=
  fullyCompleted.finiteGroupingOutputExact secondExecutedSourceChain

theorem finiteBatchGroupingNormalizesAllSources :
    (HistoricalGrouping.batchRules
      secondExecutedSourceChain.selection).normal
        (HistoricalGrouping.initialBatchState
          secondExecutedSourceChain.selection) = .target :=
  finiteBatchGrouping.normalizedTarget

theorem finiteBatchGroupingKeepsChronologicalAppendOrder :
    HistoricalGrouping.initialBatchState
        secondExecutedSourceChain.selection =
      HistoricalGrouping.stateOfIndices
        (HistoricalGrouping.appendIndex
          (HistoricalGrouping.liftIndices (HistoricalGrouping.allIndices 1))
          (Sum.inr Unit.unit)) :=
  HistoricalGrouping.initialBatchState_snoc
    firstExecutedSourceChain.selection secondProducedSource

theorem fourNeFive : (4 : Nat) ≠ 5 := by decide

theorem sourceCertificatesRemainDistinct : sourceAt 4 ≠ secondSource := by
  intro equality
  have indexEquality :=
    congrArg
      (fun source : constantFamily.SourceAt 4 => source.index)
      equality
  exact fourNeFive indexEquality

theorem producedSourcesRemainDistinct :
    producedSourceAt 4 ≠ parallelProducedSource := by
  intro equality
  have indexEquality :=
    congrArg
      (fun source : constantFamily.ProducedSourceAt 4 =>
        source.source.index)
      equality
  exact fourNeFive indexEquality

theorem sharedTargetWithoutIdentifyingSources :
    LocalGrouping.SharedTargetWithoutSourceIdentification
      (constantFamily.groupingEnvelope 4)
      (producedSourceAt 4) parallelProducedSource :=
  LocalGrouping.sharedTargetWithoutSourceIdentification
    (constantFamily.groupingEnvelope 4) producedSourcesRemainDistinct

def parallelGroupedSourcesHaveSameFuture :
    MasterContinuation.SameNormalizedFuture constantFamily
      fullyCompleted.master
      (groupedFutureState constantFamily 4 (producedSourceAt 4))
      (groupedFutureState constantFamily 4 parallelProducedSource) :=
  fullyCompleted.groupedSourcesSameMasterFuture 4
    (producedSourceAt 4) parallelProducedSource rfl

def executedLimitProductionAtFour :
    ExecutedLimitProduction constantFamily rootJournal 4 :=
  fullyCompleted.produceLimit rootJournal 4

theorem executedLimitProductionUsesModulusSource :
    executedLimitProductionAtFour.source.source.index =
      constantFamily.modulus 4 :=
  executedLimitProductionAtFour.sourceIndexExact

theorem executedLimitProductionConsumesSourceReadout :
    executedLimitProductionAtFour.groupedCharge.consumedCode =
      executedLimitProductionAtFour.source.code :=
  executedLimitProductionAtFour.groupedCharge_consumesSourceReadout

theorem executedLimitProductionReadoutExact :
    executedLimitProductionAtFour.readout =
      constantFamily.limitApproximation 4 :=
  executedLimitProductionAtFour.readout_is_limitApproximation

theorem executedLimitProductionAddsTwelveOperations :
    executedLimitProductionAtFour.completedJournal.depth = 12 :=
  executedLimitProductionAtFour.completedJournal_depth

def completeGodelRaccord :
    Result heytingArithmeticGodelExecution constantFamily :=
  raccord heytingArithmeticGodelExecution constantFamily

theorem completeGodelRaccordReachesDepthThirteen :
    completeGodelRaccord.firstLimitProduction.completedJournal.depth = 13 :=
  firstLimitProduction_depth_thirteen
    heytingArithmeticGodelExecution constantFamily

theorem completeGodelRaccordSourceReachesDepthSeven :
    completeGodelRaccord.firstLimitProduction.source.afterExecutionState.journal.depth =
      7 :=
  firstSourceJournal_depth_seven
    heytingArithmeticGodelExecution constantFamily

def persistedThroughOwnedSource :
    PersistedGodelOccurrences
      heytingArithmeticGodelExecution
      completeGodelRaccord.firstLimitProduction.source.afterExecutionState.journal.depth :=
  completeGodelRaccord.persistedThroughSource

def persistedThroughOwnedLimitProduction :
    PersistedGodelOccurrences
      heytingArithmeticGodelExecution
      completeGodelRaccord.firstLimitProduction.completedJournal.depth :=
  completeGodelRaccord.persistedThroughLimitProduction

theorem completeGodelRaccordUsesUniversalProducer :
    completeGodelRaccord.firstLimitProduction =
      completeGodelRaccord.executedSequentialCompleteness.produceLimit
        completeGodelRaccord.seed 0 :=
  completeGodelRaccord.firstLimitProductionExact

theorem completeGodelRaccordUsesCanonicalMaster :
    completeGodelRaccord.firstLimitProduction =
      executeLimitProduction constantFamily completeGodelRaccord.seed 0 :=
  firstLimitProduction_is_canonicalProducer
    heytingArithmeticGodelExecution constantFamily

def finiteHistoricalExtension :=
  (constantFamily.groupingFutureContract 4).extend
    firstFiniteSelection secondProducedSource

def finiteBatchHistoricalExtension :=
  (constantFamily.groupingFutureContract 4).extendBatch
    firstFiniteSelection secondProducedSource

theorem finiteBatchHistoricalExtensionPreservesOldCursor :
    finiteBatchHistoricalExtension.embedding
        (HistoricalGrouping.initialBatchState firstFiniteSelection) =
      HistoricalGrouping.embedBatchState
        (HistoricalGrouping.initialBatchState firstFiniteSelection) :=
  rfl

def twoStepHistoricalExtension :=
  HistoricalGrouping.twoStepExtension
    (HistoricalGrouping.emptySelection (constantFamily.groupingEnvelope 4))
    (producedSourceAt 4) secondProducedSource

theorem twoStepExtensionComposesOnTarget :
    twoStepHistoricalExtension.embedding LocalGrouping.State.target =
      (HistoricalGrouping.extension firstFiniteSelection
        secondProducedSource).embedding
        ((HistoricalGrouping.extension
          (HistoricalGrouping.emptySelection
            (constantFamily.groupingEnvelope 4))
          (producedSourceAt 4)).embedding LocalGrouping.State.target) :=
  HistoricalGrouping.twoStepExtension_embedding
    (HistoricalGrouping.emptySelection (constantFamily.groupingEnvelope 4))
    (producedSourceAt 4) secondProducedSource LocalGrouping.State.target

def richRoot : ResponseContinuation.RichState P :=
  { journal := rootJournal, memory := baseCode }

def twoRequests : List ApproximationPayload :=
  [ sourcePayload 4 4 (producedSourceAt 4).code,
    limitPayload 4 (completed.limit.approximation 4) ]

def twoTypedRequests : List constantFamily.Request :=
  [ ExecutedCauchyFamily.Request.source 4 (sourceAt 4),
    ExecutedCauchyFamily.Request.limit 4 ]

def twoRequestsAdmitted :=
  completed.allFiniteRequestsAdmitted richRoot twoRequests

def twoTypedRequestsAdmitted :=
  fullyCompleted.allTypedRequestsAdmitted richRoot twoTypedRequests

def firstGroupedFutureAdmitted :=
  fullyCompleted.allTypedRequestsAdmitted
    (groupedFutureState constantFamily 4 (producedSourceAt 4)) twoTypedRequests

/-- Admission is transported through the normalized future contract. -/
def secondGroupedFutureAdmittedFromFirst :=
  parallelGroupedSourcesHaveSameFuture.admittedForward twoTypedRequests
    firstGroupedFutureAdmitted

/-- The same admission equivalence is available in the reverse direction. -/
def firstGroupedFutureAdmittedFromSecond :=
  parallelGroupedSourcesHaveSameFuture.admittedBackward twoTypedRequests
    secondGroupedFutureAdmittedFromFirst

theorem twoRequestsProjectionExact :
    (ResponseContinuation.bridge P).project
        (ConstitutiveSearch.Grouping.Continuation.run
          (ResponseContinuation.bridge P).sourceNext richRoot twoRequests) =
      ConstitutiveSearch.Grouping.Continuation.run
        (ResponseContinuation.bridge P).reducedNext
        ((ResponseContinuation.bridge P).project richRoot) twoRequests :=
  completed.finiteRunExact richRoot twoRequests

/-- The typed future runs the retained source/grouping/limit master. -/
theorem twoTypedRequestsProjectionExact :
    (MasterContinuation.bridge constantFamily fullyCompleted.master).project
        (ConstitutiveSearch.Grouping.Continuation.run
          (MasterContinuation.bridge constantFamily
            fullyCompleted.master).sourceNext richRoot twoTypedRequests) =
      ConstitutiveSearch.Grouping.Continuation.run
        (MasterContinuation.bridge constantFamily
          fullyCompleted.master).reducedNext
        ((MasterContinuation.bridge constantFamily
          fullyCompleted.master).project richRoot) twoTypedRequests :=
  fullyCompleted.finiteRunExact richRoot twoTypedRequests

def retainedMasterLimitResponse :=
  fullyCompleted.master richRoot
    (ExecutedCauchyFamily.Request.limit 4)

/-- A typed limit future owns the complete twelve-operation production. -/
theorem retainedMasterLimitAddsTwelve :
    retainedMasterLimitResponse.completedJournal.depth =
      richRoot.journal.depth + 12 :=
  retainedMasterLimitResponse.completedJournal_depth

/-- Its grouping step consumes the source execution owned by that response. -/
theorem retainedMasterLimitConsumesOwnedSource :
    retainedMasterLimitResponse.execution.groupedCharge.consumedCode =
      retainedMasterLimitResponse.execution.source.code :=
  retainedMasterLimitResponse.execution.groupedCharge_consumesSourceReadout

theorem producedSourceProvenanceIsSourceRequest :
    (producedSourceAt 4).execution.provenance.request =
      ApproximationRequest.source 4 4 :=
  rfl

theorem finiteExtensionRenormalizes
    (state : LocalGrouping.State
      (HistoricalGrouping.finiteSpecification firstFiniteSelection)) :
    (LocalGrouping.rules
      (HistoricalGrouping.finiteSpecification
        (firstFiniteSelection.snoc secondProducedSource))).normal
        (finiteHistoricalExtension.embedding
          ((LocalGrouping.rules
            (HistoricalGrouping.finiteSpecification
              firstFiniteSelection)).normal state)) =
      (LocalGrouping.rules
        (HistoricalGrouping.finiteSpecification
          (firstFiniteSelection.snoc secondProducedSource))).normal
        (finiteHistoricalExtension.embedding state) :=
  finiteHistoricalExtension.renormalized state

end RelationalPerimeter.Tests.RelationalSequentialCompleteness

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Tests.RelationalSequentialCompleteness.P
#print axioms RelationalPerimeter.Tests.RelationalSequentialCompleteness.baseCode
#print axioms RelationalPerimeter.Tests.RelationalSequentialCompleteness.constantTerm
#print axioms RelationalPerimeter.Tests.RelationalSequentialCompleteness.raisedConstant
#print axioms RelationalPerimeter.Tests.RelationalSequentialCompleteness.constantPresentationEquivalent
#print axioms RelationalPerimeter.Tests.RelationalSequentialCompleteness.constantEquivalenceRoundTrip
#print axioms RelationalPerimeter.Tests.RelationalSequentialCompleteness.constantFamily
#print axioms RelationalPerimeter.Tests.RelationalSequentialCompleteness.completed
#print axioms RelationalPerimeter.Tests.RelationalSequentialCompleteness.fullyCompleted
#print axioms RelationalPerimeter.Tests.RelationalSequentialCompleteness.fullyCompletedRetainsSameSequentialResult
#print axioms RelationalPerimeter.Tests.RelationalSequentialCompleteness.sourceAt
#print axioms RelationalPerimeter.Tests.RelationalSequentialCompleteness.convergesAtEveryPrecision
#print axioms RelationalPerimeter.Tests.RelationalSequentialCompleteness.rootJournal
#print axioms RelationalPerimeter.Tests.RelationalSequentialCompleteness.producedSourceAt
#print axioms RelationalPerimeter.Tests.RelationalSequentialCompleteness.executedLimitAtFour
#print axioms RelationalPerimeter.Tests.RelationalSequentialCompleteness.executedLimitReadoutAtFour
#print axioms RelationalPerimeter.Tests.RelationalSequentialCompleteness.groupedAtFour
#print axioms RelationalPerimeter.Tests.RelationalSequentialCompleteness.groupedAtFourConsumesExecutedSource
#print axioms RelationalPerimeter.Tests.RelationalSequentialCompleteness.groupedAtFourConsumesConvergenceWitness
#print axioms RelationalPerimeter.Tests.RelationalSequentialCompleteness.executedLimitReadoutIsGroupingAction
#print axioms RelationalPerimeter.Tests.RelationalSequentialCompleteness.firstFiniteSelection
#print axioms RelationalPerimeter.Tests.RelationalSequentialCompleteness.secondSource
#print axioms RelationalPerimeter.Tests.RelationalSequentialCompleteness.secondJournal
#print axioms RelationalPerimeter.Tests.RelationalSequentialCompleteness.secondProducedSource
#print axioms RelationalPerimeter.Tests.RelationalSequentialCompleteness.parallelProducedSource
#print axioms RelationalPerimeter.Tests.RelationalSequentialCompleteness.emptyExecutedSourceChain
#print axioms RelationalPerimeter.Tests.RelationalSequentialCompleteness.firstExecutedSourceChain
#print axioms RelationalPerimeter.Tests.RelationalSequentialCompleteness.secondExecutedSourceChain
#print axioms RelationalPerimeter.Tests.RelationalSequentialCompleteness.finiteBatchGrouping
#print axioms RelationalPerimeter.Tests.RelationalSequentialCompleteness.consumedCodes
#print axioms RelationalPerimeter.Tests.RelationalSequentialCompleteness.finiteBatchGroupingConsumesExactChronology
#print axioms RelationalPerimeter.Tests.RelationalSequentialCompleteness.finiteBatchGroupingConsumesBothSources
#print axioms RelationalPerimeter.Tests.RelationalSequentialCompleteness.finiteBatchGroupingConsumesCodesChronologically
#print axioms RelationalPerimeter.Tests.RelationalSequentialCompleteness.finiteBatchGroupingOutputExact
#print axioms RelationalPerimeter.Tests.RelationalSequentialCompleteness.finiteBatchGroupingNormalizesAllSources
#print axioms RelationalPerimeter.Tests.RelationalSequentialCompleteness.finiteBatchGroupingKeepsChronologicalAppendOrder
#print axioms RelationalPerimeter.Tests.RelationalSequentialCompleteness.fourNeFive
#print axioms RelationalPerimeter.Tests.RelationalSequentialCompleteness.sourceCertificatesRemainDistinct
#print axioms RelationalPerimeter.Tests.RelationalSequentialCompleteness.producedSourcesRemainDistinct
#print axioms RelationalPerimeter.Tests.RelationalSequentialCompleteness.sharedTargetWithoutIdentifyingSources
#print axioms RelationalPerimeter.Tests.RelationalSequentialCompleteness.parallelGroupedSourcesHaveSameFuture
#print axioms RelationalPerimeter.Tests.RelationalSequentialCompleteness.executedLimitProductionAtFour
#print axioms RelationalPerimeter.Tests.RelationalSequentialCompleteness.executedLimitProductionUsesModulusSource
#print axioms RelationalPerimeter.Tests.RelationalSequentialCompleteness.executedLimitProductionConsumesSourceReadout
#print axioms RelationalPerimeter.Tests.RelationalSequentialCompleteness.executedLimitProductionReadoutExact
#print axioms RelationalPerimeter.Tests.RelationalSequentialCompleteness.executedLimitProductionAddsTwelveOperations
#print axioms RelationalPerimeter.Tests.RelationalSequentialCompleteness.completeGodelRaccord
#print axioms RelationalPerimeter.Tests.RelationalSequentialCompleteness.completeGodelRaccordReachesDepthThirteen
#print axioms RelationalPerimeter.Tests.RelationalSequentialCompleteness.completeGodelRaccordSourceReachesDepthSeven
#print axioms RelationalPerimeter.Tests.RelationalSequentialCompleteness.persistedThroughOwnedSource
#print axioms RelationalPerimeter.Tests.RelationalSequentialCompleteness.persistedThroughOwnedLimitProduction
#print axioms RelationalPerimeter.Tests.RelationalSequentialCompleteness.completeGodelRaccordUsesUniversalProducer
#print axioms RelationalPerimeter.Tests.RelationalSequentialCompleteness.completeGodelRaccordUsesCanonicalMaster
#print axioms RelationalPerimeter.Tests.RelationalSequentialCompleteness.finiteHistoricalExtension
#print axioms RelationalPerimeter.Tests.RelationalSequentialCompleteness.finiteBatchHistoricalExtension
#print axioms RelationalPerimeter.Tests.RelationalSequentialCompleteness.finiteBatchHistoricalExtensionPreservesOldCursor
#print axioms RelationalPerimeter.Tests.RelationalSequentialCompleteness.twoStepHistoricalExtension
#print axioms RelationalPerimeter.Tests.RelationalSequentialCompleteness.twoStepExtensionComposesOnTarget
#print axioms RelationalPerimeter.Tests.RelationalSequentialCompleteness.richRoot
#print axioms RelationalPerimeter.Tests.RelationalSequentialCompleteness.twoRequests
#print axioms RelationalPerimeter.Tests.RelationalSequentialCompleteness.twoTypedRequests
#print axioms RelationalPerimeter.Tests.RelationalSequentialCompleteness.twoRequestsAdmitted
#print axioms RelationalPerimeter.Tests.RelationalSequentialCompleteness.twoTypedRequestsAdmitted
#print axioms RelationalPerimeter.Tests.RelationalSequentialCompleteness.firstGroupedFutureAdmitted
#print axioms RelationalPerimeter.Tests.RelationalSequentialCompleteness.secondGroupedFutureAdmittedFromFirst
#print axioms RelationalPerimeter.Tests.RelationalSequentialCompleteness.firstGroupedFutureAdmittedFromSecond
#print axioms RelationalPerimeter.Tests.RelationalSequentialCompleteness.twoRequestsProjectionExact
#print axioms RelationalPerimeter.Tests.RelationalSequentialCompleteness.twoTypedRequestsProjectionExact
#print axioms RelationalPerimeter.Tests.RelationalSequentialCompleteness.retainedMasterLimitResponse
#print axioms RelationalPerimeter.Tests.RelationalSequentialCompleteness.retainedMasterLimitAddsTwelve
#print axioms RelationalPerimeter.Tests.RelationalSequentialCompleteness.retainedMasterLimitConsumesOwnedSource
#print axioms RelationalPerimeter.Tests.RelationalSequentialCompleteness.producedSourceProvenanceIsSourceRequest
#print axioms RelationalPerimeter.Tests.RelationalSequentialCompleteness.finiteExtensionRenormalizes
/- AXIOM_AUDIT_END -/
