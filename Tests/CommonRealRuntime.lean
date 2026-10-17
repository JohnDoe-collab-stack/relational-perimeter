import RelationalPerimeter.Instances.HeytingArithmetic.RealCorrespondence
import RelationalPerimeter.Constitution.Reals.CommonRealRuntime

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace RelationalPerimeter.Tests.CommonRealRuntime

open StrongPerimetralTurning
open RelationalPerimeter.HeytingArithmetic
open RelationalPerimeter.Constitution.Reals
open RelationalPerimeter.Constitution.Reals.ConstitutiveRuntime
open RelationalPerimeter.Constitution.Reals.ProducedCompleteness
open RelationalPerimeter.Constitution.Reals.AuthoritativeRuntime
open RelationalPerimeter.Constitution.Reals.RuntimeCorrespondence
open ConstitutiveSearch.ContinuationSignatures

abbrev P := heytingArithmeticGodelPresentation
def zero : SignedDyadicCode := { positive := 0, negative := 0, scale := 0 }
def one : SignedDyadicCode := { positive := 1, negative := 0, scale := 0 }

def oneNearZero : Near 0 one zero where
  scale := {
    common := 0
    leftExtra := 0
    rightExtra := 0
    leftExact := rfl
    rightExact := rfl
  }
  precisionExtra := 0
  precisionExact := rfl
  leftBound := Nat.le_refl 1
  rightBound := Nat.zero_le _

def changingApproximation : Nat -> SignedDyadicCode
  | 0 => one
  | Nat.succ _ => zero

def changingCoherent (precision left right : Nat)
    (leftBeyond : PrecisionExtension precision left)
    (rightBeyond : PrecisionExtension precision right) :
    Near precision (changingApproximation left) (changingApproximation right) := by
  cases precision with
  | zero =>
      cases left <;> cases right
      · exact Near.refl 0 one
      · exact oneNearZero
      · exact oneNearZero.symm
      · exact Near.refl 0 zero
  | succ precision =>
      cases left with
      | zero =>
          have impossible : Nat.succ (precision + leftBeyond.extra) = 0 :=
            (Nat.succ_add precision leftBeyond.extra).symm.trans leftBeyond.exact
          exact False.elim (Nat.noConfusion impossible)
      | succ left =>
          cases right with
          | zero =>
              have impossible : Nat.succ (precision + rightBeyond.extra) = 0 :=
                (Nat.succ_add precision rightBeyond.extra).symm.trans rightBeyond.exact
              exact False.elim (Nat.noConfusion impossible)
          | succ right => exact Near.refl _ zero

def changingPresentation : EffectiveDyadicPresentation where
  approximation := changingApproximation
  coherent := changingCoherent

def real : RuntimeReal P 1 := presentationToRuntime P 1 changingPresentation
abbrev family := real.family
def master : RelationalPerimeter.Constitution.Reals.CommonRealRuntime.Completeness family := RelationalPerimeter.Constitution.Reals.CommonRealRuntime.complete family
def initial : AuthoritativeRuntime.Runtime family := AuthoritativeRuntime.initialState family

/-- G1: non-diagonal response, both occurrences and exact trace from ONE execution. -/
def nonDiagonal : family.SourceAt 0 where
  request := { term := 2, precision := 1 }
  indexBeyondModulus := { extra := 2, exact := rfl }
  readoutRefines := { extra := 1, exact := rfl }

def source := family.produceSourceAt initial.journal nonDiagonal
def sourceOrigin : ExecutedRequest.Provenance source.execution := source.execution.provenance
theorem sourceOriginReceived : sourceOrigin.receivedAt = source.execution.receivedOccurrence := sourceOrigin.receivedExact
theorem sourceOriginProduced : sourceOrigin.producedAt = source.execution.producedOccurrence := sourceOrigin.producedExact
theorem sourceOriginTrace : sourceOrigin.constitutiveTrace = source.execution.memory := sourceOrigin.traceExact
theorem sourceOriginStamp : sourceOrigin.stamp = .source 2 1 := sourceOrigin.stampExact

def limit := executeLimitProduction family initial.journal 0
def limitOrigin : ExecutedRequest.Provenance limit.execution := limit.execution.provenance
theorem limitOriginTrace : limitOrigin.constitutiveTrace = limit.execution.memory := limitOrigin.traceExact
theorem limitOriginStamp : limitOrigin.stamp = .limit 0 := limitOrigin.stampExact

/-- G2/G4/G5/G6: exact ordered resources, transported and normalized, not equal codes. -/
def grouped := master.group initial [nonDiagonal, family.diagonalSourceAt 0]
def selection := grouped.grouped.execution.memory.continued.authorized.acted.searched.result.selection
def normalized := grouped.grouped.normalizedBatch

theorem normalizedConsumedExactly :
    normalized.consumed = HistoricalGrouping.chargesForIndices selection.indexedSelection
      (HistoricalGrouping.initialBatchCharge selection.indexedSelection).available
      (HistoricalGrouping.allIndices grouped.size) :=
  grouped.grouped.normalizedBatch_consumed_exact

theorem normalizedCount : normalized.consumed.length = 2 := by
  exact grouped.grouped.normalizedBatch_consumed_length

theorem historicalExtensionsActuallyRetained :
    grouped.grouped.target.history.resources.length = 2 := by decide

theorem transportedLocalChargesRetained :
    grouped.grouped.target.history.localCharges.length = 1 := by decide

theorem historicalSeedWasConsumed :
    grouped.grouped.target.normalized =
      family.normalizeHistorical selection grouped.grouped.target.history :=
  grouped.grouped.target.normalizedFromHistory

/-- This type ties the final resource to every exact previous batch input. -/
def historicalResourceChain : family.HistoricalNormalization grouped.grouped.anchor selection
    grouped.grouped.target.history.seed := grouped.grouped.target.history.normalization

def lastHistoricalInput :=
  grouped.grouped.target.history.resources[1]'(by decide)

/-- The actual input of the last normalization still owns the consumed prefix.
A fresh initialBatchCharge of identical output code has length zero, not one. -/
theorem lastHistoricalInputOwnsPrefix : lastHistoricalInput.charge.consumed.length = 1 := by decide

theorem lastNormalizationConsumesTransportedResource :
    normalized.consumed = HistoricalGrouping.appendIndex lastHistoricalInput.charge.consumed
      (HistoricalGrouping.consumedEvidence lastHistoricalInput.selection (.inr ())
        lastHistoricalInput.charge.available) := rfl

def transportedFirstEvidence := lastHistoricalInput.charge.consumed[0]'(by decide)
def normalizedFirstEvidence := normalized.consumed[0]'(by decide)

/-- The very Near in the transported consumed prefix reaches the final batch. -/
theorem lastNormalizationKeepsTransportedNear :
    HEq normalizedFirstEvidence.nearTarget transportedFirstEvidence.nearTarget := HEq.refl _

theorem historicalResourceCannotBeFreshSeed :
    grouped.grouped.target.history.seed ≠
      HistoricalGrouping.initialBatchCharge selection.indexedSelection := by
  intro equal
  have impossible : (2 : Nat) = 0 := congrArg (fun charge => charge.consumed.length) equal
  exact (by decide : (2 : Nat) ≠ 0) impossible

theorem firstSourceCode : (normalized.available (.inl (.inr ()))).receivedCode = zero := by
  unfold normalized
  rw [grouped.grouped.normalizedBatch_exact]
  rfl

theorem targetCode : grouped.grouped.readout = one := by
  rw [ExecutedCauchyFamily.readout_is_anchor]
  exact grouped.grouped.anchor.source.readout_is_calculated

theorem sourceAndTargetNotEqual : zero ≠ grouped.grouped.readout := by
  rw [targetCode]
  intro equal
  exact (by decide : (0 : Nat) ≠ 1) (congrArg SignedDyadicCode.positive equal)

def nonReflexiveReceivedNear : Near 0 zero one := by
  have retained := (normalized.available (.inl (.inr ()))).receivedNearTarget
  rw [firstSourceCode] at retained
  exact retained

/-- Same positive object received from Cauchy, not a newly manufactured Near. -/
theorem retainedNearIsReceived :
    HEq (normalized.available (.inl (.inr ()))).receivedNearTarget
      (family.consumeSource grouped.grouped.anchor
        { journal := initial.journal, sourceAt := nonDiagonal, produced := source }).nearTarget := by
  unfold normalized
  rw [grouped.grouped.normalizedBatch_exact]
  rfl

theorem normalizedAccepted :
    HistoricalGrouping.BatchAccepted (.target : HistoricalGrouping.BatchState grouped.size) normalized :=
  grouped.grouped.normalizedBatch_accepted

theorem normalTarget :
    (HistoricalGrouping.batchRules selection.indexedSelection).normal
      (HistoricalGrouping.initialBatchState selection.indexedSelection) = .target :=
  grouped.grouped.execution.memory.continued.authorized.accepted.normalTarget

/-- A genuine two-step historical extension on the exact selected envelope. -/
def emptySelection := HistoricalGrouping.emptySelection (family.groupingSpecification grouped.grouped.anchor)
def chargedFirst : family.ChargedRecord grouped.grouped.anchor :=
  selection.indexedSelection.lookup (.inl (.inr ()))
def chargedSecond : family.ChargedRecord grouped.grouped.anchor :=
  selection.indexedSelection.lookup (.inr ())

theorem extensionCompositionExact (state : LocalGrouping.State
    (HistoricalGrouping.finiteSpecification emptySelection)) :
    (HistoricalGrouping.twoStepExtension emptySelection chargedFirst chargedSecond).embedding state =
      (HistoricalGrouping.extension (emptySelection.snoc chargedFirst) chargedSecond).embedding
        ((HistoricalGrouping.extension emptySelection chargedFirst).embedding state) :=
  HistoricalGrouping.twoStepExtension_embedding _ _ _ _

/-- G3: install precisely the action's owned target, then read that resource. -/
theorem installsTheActionTarget :
    grouped.next.target = some (.batch grouped.grouped) := rfl

def continued : ContinuedStep family grouped.next 2 :=
  (AuthoritativeRuntime.continueInstalled family grouped.next 2).get (by decide)

theorem continuationWasInstalled : grouped.next.target = some continued.target := continued.installedExact
theorem continuationRetainsSameTarget :
    continued.execution.action.retained.value = OwnedTarget.batch grouped.grouped := rfl
theorem continuationReadsSameTarget :
    continued.execution.readout = grouped.grouped.readout.raise 2 :=
  targetContinuation_readout _ _ _
theorem continuationMemoryRetainsSameTarget :
    continued.next.target = some (.rescaled (.batch grouped.grouped) 2) := rfl

theorem freshGroupingOccurrence :
    (grouped.grouped.execution.memory.continued.authorized.acted.phase.transportPrior
      grouped.grouped.execution.memory.continued.authorized.acted.searched.phase.occurrence) ≠
      ExecutedCauchyFamily.targetOccurrence grouped.grouped :=
  grouped.grouped.execution.memory.continued.authorized.acted.phase.transportPrior_ne_fresh _

/-- G7: one complete mixed future includes refusals, non-diagonal input and resume. -/
def mixedRequests : List RelationalPerimeter.Constitution.Reals.CommonRealRuntime.Request :=
  [.source { term := 2, precision := 1 }, .unsupported (.source 91 92),
   .group 0 [{ term := 2, precision := 1 }, { term := 0, precision := 0 }],
   .continueInstalled 2, .limit 1]

theorem completeMixedOutcomeExact :
    (RelationalPerimeter.Constitution.Reals.CommonRealRuntime.archiveContract family).outcome initial mixedRequests =
      RelationalPerimeter.Constitution.Reals.CommonRealRuntime.runReal (RelationalPerimeter.Constitution.Reals.CommonRealRuntime.projectArchive family initial) mixedRequests :=
  RelationalPerimeter.Constitution.Reals.CommonRealRuntime.archiveFutures_exact family initial mixedRequests

theorem mixedEventsExact :
    ConstitutiveSearch.Grouping.Continuation.events
        (RelationalPerimeter.Constitution.Reals.CommonRealRuntime.archiveContract family).next (RelationalPerimeter.Constitution.Reals.CommonRealRuntime.archiveContract family).event initial mixedRequests =
      ConstitutiveSearch.Grouping.Continuation.events
        RelationalPerimeter.Constitution.Reals.CommonRealRuntime.contract.next RelationalPerimeter.Constitution.Reals.CommonRealRuntime.contract.event (RelationalPerimeter.Constitution.Reals.CommonRealRuntime.projectArchive family initial) mixedRequests :=
  (RelationalPerimeter.Constitution.Reals.CommonRealRuntime.archiveRealization family).continuationBridge.events_exact initial mixedRequests

theorem mixedObservationsExact :
    ConstitutiveSearch.Grouping.Continuation.observations
        (RelationalPerimeter.Constitution.Reals.CommonRealRuntime.archiveContract family).next (RelationalPerimeter.Constitution.Reals.CommonRealRuntime.archiveContract family).read initial mixedRequests =
      ConstitutiveSearch.Grouping.Continuation.observations
        RelationalPerimeter.Constitution.Reals.CommonRealRuntime.contract.next RelationalPerimeter.Constitution.Reals.CommonRealRuntime.contract.read (RelationalPerimeter.Constitution.Reals.CommonRealRuntime.projectArchive family initial) mixedRequests :=
  (RelationalPerimeter.Constitution.Reals.CommonRealRuntime.archiveRealization family).continuationBridge.observations_exact initial mixedRequests

/-- G8: the concrete Gödel result consumes this exact generic master. -/
def godel := GodelRelationalCompleteness.raccord heytingArithmeticGodelExecution family
theorem godelSharesMaster : godel.master = master := godel.masterExact
theorem godelSharesProduced : godel.producedReal = master.rich.produced := rfl
theorem genericTermsExact (term : Nat) : master.rich.terms term = family.termModel term :=
  master.rich.termsExact term

/-- G9: distinct encodings, same number, no occurrence equality. -/
def encodedZero := zero.raise 1
def constantFirst := constantRuntime P 1 zero
def constantSecond := constantRuntime P 1 encodedZero
theorem constantCodesDistinct : zero ≠ encodedZero := by
  intro equal
  exact (by decide : (0 : Nat) ≠ 1) (congrArg SignedDyadicCode.scale equal)
def constantReadoutEquivalence : RuntimeReadoutEquivalent constantFirst constantSecond :=
  constantRuntimeEquivalent P 1 (SameValue.raiseExact zero 1)
def constantNumericalFutures :
    RelationalPerimeter.Constitution.Reals.CommonRealRuntime.NumericalFutureEquivalent (RelationalPerimeter.Constitution.Reals.CommonRealRuntime.environmentOfFamily constantFirst.family)
      (RelationalPerimeter.Constitution.Reals.CommonRealRuntime.environmentOfFamily constantSecond.family) :=
  RelationalPerimeter.Constitution.Reals.CommonRealRuntime.numericalFuturesOfReadouts constantReadoutEquivalence
def constantReadoutsRecovered : RuntimeReadoutEquivalent constantFirst constantSecond :=
  RelationalPerimeter.Constitution.Reals.CommonRealRuntime.readoutsOfNumericalFutures constantNumericalFutures
def constantCodeSameValue (state : AuthoritativeRuntime.Runtime constantFirst.family) (precision : Nat)
    (step : ExecutedStep constantFirst.family state (.limit precision)) :
    SameValue step.response.readout zero := constantRuntimeReadoutSameValue P 1 zero step

/-- G10: all terms, including a term BEFORE the limit modulus. -/
def beforeModulus := master.rich.terms 0
def beforeModulusFirst := beforeModulus.respond initial.journal 2
def beforeModulusSecond := beforeModulus.respond grouped.next.journal 3
def beforeModulusCoherence :
    Near 1 beforeModulusFirst.readout beforeModulusSecond.readout :=
  beforeModulus.coherent 1 2 3 { extra := 1, exact := rfl } { extra := 2, exact := rfl }
    beforeModulusFirst beforeModulusSecond
theorem termReallyBeforeModulus : 0 < family.modulus 2 := by decide

theorem fixedEnvironmentMemoryExact (environment : RelationalPerimeter.Constitution.Reals.CommonRealRuntime.Environment) (first second : RelationalPerimeter.Constitution.Reals.CommonRealRuntime.Memory) :
    first = second ↔ FutureEquivalent (RelationalPerimeter.Constitution.Reals.CommonRealRuntime.memoryContract environment) first second :=
  RelationalPerimeter.Constitution.Reals.CommonRealRuntime.fixedEnvironmentMinimality environment
theorem anyRealizationNeedsThisMemory (environment : RelationalPerimeter.Constitution.Reals.CommonRealRuntime.Environment) {Other : Type}
    (other : ExactRealization (RelationalPerimeter.Constitution.Reals.CommonRealRuntime.memoryContract environment) Other)
    {first second : RelationalPerimeter.Constitution.Reals.CommonRealRuntime.Memory} (same : other.project first = other.project second) :
    first = second := RelationalPerimeter.Constitution.Reals.CommonRealRuntime.anyFixedEnvironmentRealization environment other same

def oneEnvironment : RelationalPerimeter.Constitution.Reals.CommonRealRuntime.Environment := { producer := { calculate := fun _ => one }, modulus := fun p => p }
def zeroEnvironment : RelationalPerimeter.Constitution.Reals.CommonRealRuntime.Environment := { producer := { calculate := fun _ => zero }, modulus := fun p => p }
theorem identicalMemoryAcrossPrograms :
    (RelationalPerimeter.Constitution.Reals.CommonRealRuntime.initialState oneEnvironment 1).memory = (RelationalPerimeter.Constitution.Reals.CommonRealRuntime.initialState zeroEnvironment 1).memory := rfl
theorem differentProgramsActuallyExecuted :
    RelationalPerimeter.Constitution.Reals.CommonRealRuntime.eventCode (RelationalPerimeter.Constitution.Reals.CommonRealRuntime.performReal (RelationalPerimeter.Constitution.Reals.CommonRealRuntime.initialState oneEnvironment 1) (.limit 0)).event ≠
      RelationalPerimeter.Constitution.Reals.CommonRealRuntime.eventCode (RelationalPerimeter.Constitution.Reals.CommonRealRuntime.performReal (RelationalPerimeter.Constitution.Reals.CommonRealRuntime.initialState zeroEnvironment 1) (.limit 0)).event := by
  intro equal
  exact (by decide : (1 : Nat) ≠ 0) (congrArg SignedDyadicCode.positive equal)


/-- The local normalizer consumes the very Near already owned by this batch. -/
theorem localActionKeepsTheReceivedNear :
    HEq (grouped.grouped.target.localGrouped (.inl (.inr ()))).consumedNearTarget
      (normalized.available (.inl (.inr ()))).receivedNearTarget :=
  ExecutedCauchyFamily.BatchGrouping.ProducedTarget.localGrouped_consumedNear
    grouped.chain grouped.grouped.anchor grouped.grouped.target (.inl (.inr ()))

theorem localActionAccepted :
    LocalGrouping.AcceptedCharge
      (specification := HistoricalGrouping.finiteSpecification selection.indexedSelection)
      LocalGrouping.State.target
      (grouped.grouped.target.localGrouped (.inl (.inr ()))) :=
  ExecutedCauchyFamily.BatchGrouping.ProducedTarget.localGrouped_accepted
    grouped.chain grouped.grouped.anchor grouped.grouped.target (.inl (.inr ()))

theorem parallelGroupedSourcesHaveSameCompleteFuture :
    FutureEquivalent (RelationalPerimeter.Constitution.Reals.CommonRealRuntime.archiveContract family)
      (RelationalPerimeter.Constitution.Reals.CommonRealRuntime.groupSource family initial nonDiagonal source).next
      (RelationalPerimeter.Constitution.Reals.CommonRealRuntime.groupSource family initial
        (family.diagonalSourceAt 0) (family.produceSourceAt initial.journal (family.diagonalSourceAt 0))).next :=
  RelationalPerimeter.Constitution.Reals.CommonRealRuntime.groupedSourcesSameFuture family _ _ _ _ rfl


/-- Future source produced after the installed batch, not forged from a code. -/
def thirdSourceAt : family.SourceAt 0 where
  request := { term := 3, precision := 2 }
  indexBeyondModulus := { extra := 3, exact := rfl }
  readoutRefines := { extra := 2, exact := rfl }
def thirdSource := family.produceSourceAt grouped.next.journal thirdSourceAt
def chargedThird : family.ChargedRecord grouped.grouped.anchor :=
  { record := { journal := grouped.next.journal, sourceAt := thirdSourceAt, produced := thirdSource }
    charge := family.consumeSource grouped.grouped.anchor
      { journal := grouped.next.journal, sourceAt := thirdSourceAt, produced := thirdSource } }
def firstSelection := emptySelection.snoc chargedFirst
def firstRetainedCharge := LocalGrouping.sourceCharge
  (HistoricalGrouping.finiteSpecification firstSelection) (.inr ())
def twiceLiftedCharge :=
  HistoricalGrouping.liftSourceCharge (firstSelection.snoc chargedSecond) chargedThird
    (.inl (.inr ()))
    (HistoricalGrouping.liftSourceCharge firstSelection chargedSecond (.inr ()) firstRetainedCharge)

theorem twoAppendsRetainOriginalCode :
    twiceLiftedCharge.receivedCode = firstRetainedCharge.receivedCode := rfl
theorem twoAppendsRetainOriginalNear :
    twiceLiftedCharge.receivedNearTarget = firstRetainedCharge.receivedNearTarget := rfl

def twiceGroupedCharge :=
  (LocalGrouping.acceptanceAction
    (HistoricalGrouping.finiteSpecification ((firstSelection.snoc chargedSecond).snoc chargedThird))).transport
    ((HistoricalGrouping.twoStepExtension firstSelection chargedSecond chargedThird).trace
      (ConstitutiveSearch.Grouping.Trace.one
        (LocalGrouping.Step.group (specification := HistoricalGrouping.finiteSpecification firstSelection) (.inr ()))))
    twiceLiftedCharge

theorem twoAppendsActionRetainsOriginalNear :
    HEq twiceGroupedCharge.consumedNearTarget firstRetainedCharge.receivedNearTarget := HEq.refl _

theorem twoAppendsRenormalizeSameOccurrence :
    (LocalGrouping.rules
      (HistoricalGrouping.finiteSpecification ((firstSelection.snoc chargedSecond).snoc chargedThird))).normal
      ((HistoricalGrouping.twoStepExtension firstSelection chargedSecond chargedThird).embedding
        ((LocalGrouping.rules (HistoricalGrouping.finiteSpecification firstSelection)).normal (.source (.inr ())))) =
    (LocalGrouping.rules
      (HistoricalGrouping.finiteSpecification ((firstSelection.snoc chargedSecond).snoc chargedThird))).normal
      ((HistoricalGrouping.twoStepExtension firstSelection chargedSecond chargedThird).embedding (.source (.inr ()))) :=
  (HistoricalGrouping.twoStepExtension firstSelection chargedSecond chargedThird).renormalized _

end RelationalPerimeter.Tests.CommonRealRuntime

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Tests.CommonRealRuntime.zero
#print axioms RelationalPerimeter.Tests.CommonRealRuntime.one
#print axioms RelationalPerimeter.Tests.CommonRealRuntime.oneNearZero
#print axioms RelationalPerimeter.Tests.CommonRealRuntime.changingApproximation
#print axioms RelationalPerimeter.Tests.CommonRealRuntime.changingCoherent
#print axioms RelationalPerimeter.Tests.CommonRealRuntime.changingPresentation
#print axioms RelationalPerimeter.Tests.CommonRealRuntime.real
#print axioms RelationalPerimeter.Tests.CommonRealRuntime.master
#print axioms RelationalPerimeter.Tests.CommonRealRuntime.initial
#print axioms RelationalPerimeter.Tests.CommonRealRuntime.nonDiagonal
#print axioms RelationalPerimeter.Tests.CommonRealRuntime.source
#print axioms RelationalPerimeter.Tests.CommonRealRuntime.sourceOrigin
#print axioms RelationalPerimeter.Tests.CommonRealRuntime.sourceOriginReceived
#print axioms RelationalPerimeter.Tests.CommonRealRuntime.sourceOriginProduced
#print axioms RelationalPerimeter.Tests.CommonRealRuntime.sourceOriginTrace
#print axioms RelationalPerimeter.Tests.CommonRealRuntime.sourceOriginStamp
#print axioms RelationalPerimeter.Tests.CommonRealRuntime.limit
#print axioms RelationalPerimeter.Tests.CommonRealRuntime.limitOrigin
#print axioms RelationalPerimeter.Tests.CommonRealRuntime.limitOriginTrace
#print axioms RelationalPerimeter.Tests.CommonRealRuntime.limitOriginStamp
#print axioms RelationalPerimeter.Tests.CommonRealRuntime.grouped
#print axioms RelationalPerimeter.Tests.CommonRealRuntime.selection
#print axioms RelationalPerimeter.Tests.CommonRealRuntime.normalized
#print axioms RelationalPerimeter.Tests.CommonRealRuntime.normalizedConsumedExactly
#print axioms RelationalPerimeter.Tests.CommonRealRuntime.normalizedCount
#print axioms RelationalPerimeter.Tests.CommonRealRuntime.historicalExtensionsActuallyRetained
#print axioms RelationalPerimeter.Tests.CommonRealRuntime.transportedLocalChargesRetained
#print axioms RelationalPerimeter.Tests.CommonRealRuntime.historicalSeedWasConsumed
#print axioms RelationalPerimeter.Tests.CommonRealRuntime.firstSourceCode
#print axioms RelationalPerimeter.Tests.CommonRealRuntime.targetCode
#print axioms RelationalPerimeter.Tests.CommonRealRuntime.sourceAndTargetNotEqual
#print axioms RelationalPerimeter.Tests.CommonRealRuntime.nonReflexiveReceivedNear
#print axioms RelationalPerimeter.Tests.CommonRealRuntime.retainedNearIsReceived
#print axioms RelationalPerimeter.Tests.CommonRealRuntime.normalizedAccepted
#print axioms RelationalPerimeter.Tests.CommonRealRuntime.normalTarget
#print axioms RelationalPerimeter.Tests.CommonRealRuntime.emptySelection
#print axioms RelationalPerimeter.Tests.CommonRealRuntime.chargedFirst
#print axioms RelationalPerimeter.Tests.CommonRealRuntime.chargedSecond
#print axioms RelationalPerimeter.Tests.CommonRealRuntime.extensionCompositionExact
#print axioms RelationalPerimeter.Tests.CommonRealRuntime.installsTheActionTarget
#print axioms RelationalPerimeter.Tests.CommonRealRuntime.continued
#print axioms RelationalPerimeter.Tests.CommonRealRuntime.continuationWasInstalled
#print axioms RelationalPerimeter.Tests.CommonRealRuntime.continuationRetainsSameTarget
#print axioms RelationalPerimeter.Tests.CommonRealRuntime.continuationReadsSameTarget
#print axioms RelationalPerimeter.Tests.CommonRealRuntime.continuationMemoryRetainsSameTarget
#print axioms RelationalPerimeter.Tests.CommonRealRuntime.freshGroupingOccurrence
#print axioms RelationalPerimeter.Tests.CommonRealRuntime.mixedRequests
#print axioms RelationalPerimeter.Tests.CommonRealRuntime.completeMixedOutcomeExact
#print axioms RelationalPerimeter.Tests.CommonRealRuntime.mixedEventsExact
#print axioms RelationalPerimeter.Tests.CommonRealRuntime.mixedObservationsExact
#print axioms RelationalPerimeter.Tests.CommonRealRuntime.godel
#print axioms RelationalPerimeter.Tests.CommonRealRuntime.godelSharesMaster
#print axioms RelationalPerimeter.Tests.CommonRealRuntime.godelSharesProduced
#print axioms RelationalPerimeter.Tests.CommonRealRuntime.genericTermsExact
#print axioms RelationalPerimeter.Tests.CommonRealRuntime.encodedZero
#print axioms RelationalPerimeter.Tests.CommonRealRuntime.constantFirst
#print axioms RelationalPerimeter.Tests.CommonRealRuntime.constantSecond
#print axioms RelationalPerimeter.Tests.CommonRealRuntime.constantCodesDistinct
#print axioms RelationalPerimeter.Tests.CommonRealRuntime.constantReadoutEquivalence
#print axioms RelationalPerimeter.Tests.CommonRealRuntime.constantNumericalFutures
#print axioms RelationalPerimeter.Tests.CommonRealRuntime.constantReadoutsRecovered
#print axioms RelationalPerimeter.Tests.CommonRealRuntime.constantCodeSameValue
#print axioms RelationalPerimeter.Tests.CommonRealRuntime.beforeModulus
#print axioms RelationalPerimeter.Tests.CommonRealRuntime.beforeModulusFirst
#print axioms RelationalPerimeter.Tests.CommonRealRuntime.beforeModulusSecond
#print axioms RelationalPerimeter.Tests.CommonRealRuntime.beforeModulusCoherence
#print axioms RelationalPerimeter.Tests.CommonRealRuntime.termReallyBeforeModulus
#print axioms RelationalPerimeter.Tests.CommonRealRuntime.fixedEnvironmentMemoryExact
#print axioms RelationalPerimeter.Tests.CommonRealRuntime.anyRealizationNeedsThisMemory
#print axioms RelationalPerimeter.Tests.CommonRealRuntime.oneEnvironment
#print axioms RelationalPerimeter.Tests.CommonRealRuntime.zeroEnvironment
#print axioms RelationalPerimeter.Tests.CommonRealRuntime.identicalMemoryAcrossPrograms
#print axioms RelationalPerimeter.Tests.CommonRealRuntime.differentProgramsActuallyExecuted
#print axioms RelationalPerimeter.Tests.CommonRealRuntime.localActionKeepsTheReceivedNear
#print axioms RelationalPerimeter.Tests.CommonRealRuntime.localActionAccepted
#print axioms RelationalPerimeter.Tests.CommonRealRuntime.parallelGroupedSourcesHaveSameCompleteFuture
#print axioms RelationalPerimeter.Tests.CommonRealRuntime.thirdSourceAt
#print axioms RelationalPerimeter.Tests.CommonRealRuntime.thirdSource
#print axioms RelationalPerimeter.Tests.CommonRealRuntime.chargedThird
#print axioms RelationalPerimeter.Tests.CommonRealRuntime.firstSelection
#print axioms RelationalPerimeter.Tests.CommonRealRuntime.firstRetainedCharge
#print axioms RelationalPerimeter.Tests.CommonRealRuntime.twiceLiftedCharge
#print axioms RelationalPerimeter.Tests.CommonRealRuntime.twoAppendsRetainOriginalCode
#print axioms RelationalPerimeter.Tests.CommonRealRuntime.twoAppendsRetainOriginalNear
#print axioms RelationalPerimeter.Tests.CommonRealRuntime.twiceGroupedCharge
#print axioms RelationalPerimeter.Tests.CommonRealRuntime.twoAppendsActionRetainsOriginalNear
#print axioms RelationalPerimeter.Tests.CommonRealRuntime.twoAppendsRenormalizeSameOccurrence
#print axioms RelationalPerimeter.Tests.CommonRealRuntime.historicalResourceChain
#print axioms RelationalPerimeter.Tests.CommonRealRuntime.lastHistoricalInput
#print axioms RelationalPerimeter.Tests.CommonRealRuntime.lastHistoricalInputOwnsPrefix
#print axioms RelationalPerimeter.Tests.CommonRealRuntime.lastNormalizationConsumesTransportedResource
#print axioms RelationalPerimeter.Tests.CommonRealRuntime.transportedFirstEvidence
#print axioms RelationalPerimeter.Tests.CommonRealRuntime.normalizedFirstEvidence
#print axioms RelationalPerimeter.Tests.CommonRealRuntime.lastNormalizationKeepsTransportedNear
#print axioms RelationalPerimeter.Tests.CommonRealRuntime.historicalResourceCannotBeFreshSeed
/- AXIOM_AUDIT_END -/
