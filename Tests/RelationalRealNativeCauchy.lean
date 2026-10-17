import RelationalPerimeter.Constitution.Reals.RelationalRealNativeCauchy
import Tests.RelationalRealFamilyTransport

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace RelationalPerimeter.Tests.RelationalRealNativeCauchy
open StrongPerimetralTurning
open RelationalPerimeter.Constitution.Reals
open ProducedCompleteness RuntimeCorrespondence HeterogeneousRealRuntime
open RelationalRealAddition RelationalRealCauchy RelationalRealLimitUniqueness
open RelationalRealFamilyTransport RelationalRealNativeCauchy

variable {P : CircularPresentation} {d : Nat}

/-- Test input is genuinely composed; its law consumes the two owned additions'
four native children, not a presentation comparison supplied as production. -/
def composedFamily (family : ExecutedCauchyFamily P d) : NativeCauchyFamily P d where
  terms n := .add (termReal family n) (zero P d)
  kernels n := nativeTermKernel (.add (termReal family n) (zero P d))
  kernelExact n p := fun {archive} step => nativeStep_liveCode _ p step
  modulus p := family.modulus (Nat.succ p)
  modulusMonotone extension := family.modulusMonotone extension.succ
  cauchy := by
    intro p n m r s aa ba first second hn hm hr hs
    change AdditionArchive (environment (termReal family n)) (environment (zero P d)) at aa
    change AdditionArchive (environment (termReal family m)) (environment (zero P d)) at ba
    change Step (addEnvironment (environment (termReal family n)) (environment (zero P d))) aa r at first
    change Step (addEnvironment (environment (termReal family m)) (environment (zero P d))) ba s at second
    let near := Near.add
      (termsCauchy family (Nat.succ p) n m (Nat.succ r) (Nat.succ s)
        first.resource.left second.resource.left hn hm hr.succ hs.succ)
      ((coherent (zero P d)).near (Nat.succ p) _ _ first.resource.right second.resource.right hr.succ hs.succ)
    exact LimitGrouping.transportNear (AdditionProduction.readoutExact first.resource).symm
      (AdditionProduction.readoutExact second.resource).symm near

variable (family : ExecutedCauchyFamily P d)

def native := composedFamily family
def priorTerm := executeReal ((native family).terms ((native family).modulus 0)) 1
def seededBank : ContextBank (native family) := fun n => (executeReal ((native family).terms n) 1).next
def seededArchive : NativeArchive (native family) :=
  seedNativeArchive (native family) (seededBank family)
def priorLimit := executeAt (nativeLimit (native family)) (seededArchive family) 2
def priorDiagonal := executeReal ((native family).terms ((native family).modulus 3)) 1
def firstTerm := executeAt ((native family).terms ((native family).modulus 0)) (priorTerm family).next 2
def firstLimit := executeAt (nativeLimit (native family)) (priorLimit family).next 3
def firstObservation := RelationalRealNativeCauchy.observeLimit (native family) 0 ((native family).modulus 0) 2 3
  (firstTerm family) (firstLimit family) (.refl _) ⟨2,rfl⟩ ⟨3,rfl⟩

def secondTerm := executeAt ((native family).terms ((native family).modulus 0)) (firstTerm family).next 4
def secondLimit := executeAt (nativeLimit (native family)) (firstLimit family).next 3
def secondObservation := RelationalRealNativeCauchy.observeLimit (native family) 0 ((native family).modulus 0) 4 3
  (secondTerm family) (secondLimit family) (.refl _) ⟨4,rfl⟩ ⟨3,rfl⟩

theorem firstDiagonalCurrent : (firstObservation family).diagonal = executeAt
    ((native family).terms ((native family).modulus 3)) ((priorLimit family).next.bank ((native family).modulus 3)) 3 :=
  (firstLimit family).resource.source.diagonalExact

theorem secondDiagonalContinues : (firstLimit family).next.bank ((native family).modulus 3) =
    (firstObservation family).diagonal.next := nativeNext_bank _ _

theorem currentSourceOwned : (firstObservation family).diagonal =
    (firstLimit family).resource.diagonal := (firstObservation family).diagonalExact

theorem nativeLawUsesOwnedSteps : (firstObservation family).nativeNear =
    (native family).cauchy 0 ((native family).modulus 0) ((native family).modulus 3) 2 3
      (firstTerm family) (firstObservation family).diagonal
      (.refl _) ((native family).modulusMonotone ⟨3,rfl⟩) ⟨2,rfl⟩ ⟨3,rfl⟩ :=
  (firstObservation family).nativeNearExact

def pairObservation := observePair (native family) 0 ((native family).modulus 0) ((native family).modulus 0) 2 3
  (priorTerm family).next (firstTerm family).next (.refl _) (.refl _) ⟨2,rfl⟩ ⟨3,rfl⟩

theorem projectedCodes (n p : Nat) :
    ((toEffectiveFamily (native family)).terms n).approximation p = readout ((native family).terms n) p := rfl

def termEquivalent := RelationalRealNativeCauchy.realizedTermEquivalent (native family) 2
def termFutures := RelationalRealNativeCauchy.realizedTermFutures (native family) 2
def completeness := nativeCompleteness (native family)
def nativeCandidate := nativeAuthoritative (native family)

/-- Same certified native limit service; this compatibility wrapper is not
a test of distinct Real constructors. currentReadout only certifies uniformity. -/
def certifiedCandidate : NativeCandidate (native family) where
  real := .certified {
    service := environment (nativeLimit (native family))
    coherence := coherent (nativeLimit (native family))
    uniform := fun _ p step => currentReadout (nativeLimit (native family)) _ p step }
  threshold := fun p => p
  converges := (nativeAuthoritative (native family)).converges

/-- A genuinely different Real constructor. Convergence consumes the received
addition's exact limit and zero Steps; it neither replays them nor equates
their resources with those of the authoritative candidate. -/
def addZeroCandidate : NativeCandidate (native family) where
  real := .add (nativeLimit (native family)) (zero P d)
  threshold := fun p => p
  converges := by
    intro p n r s ta archive termStep candidateStep hn hr hs
    change AdditionArchive (environment (nativeLimit (native family))) (environment (zero P d)) at archive
    change Step (addEnvironment (environment (nativeLimit (native family))) (environment (zero P d))) archive s at candidateStep
    let near := (RelationalRealNativeCauchy.observeLimit (native family) p n r (Nat.succ s)
      termStep candidateStep.resource.left hn hr (hs.trans (PrecisionExtension.next s))).near
    let same := (SameValue.add (SameValue.refl candidateStep.resource.left.code)
      (constantRuntimeReadoutSameValue P d SignedDyadicCode.zero candidateStep.resource.right.resource)).trans
        (SignedDyadicCode.add_zero candidateStep.resource.left.code)
    exact LimitGrouping.transportNear rfl (AdditionProduction.readoutExact candidateStep.resource).symm
      (Near.ofSameRight near same.symm)

/-- Numerical uniqueness cannot identify even these Real constructors,
let alone their archives, resources or historical occurrences. -/
def candidateConstructorsDistinct :
    (nativeCandidate family).real = (addZeroCandidate family).real → Empty := by
  intro equality
  cases equality

def uniqueness := nativeUnique (nativeCandidate family) (addZeroCandidate family)
def authoritativeUniqueness := nativeAuthoritativeUnique (addZeroCandidate family)

def numericalAgreementWithoutIdentity :
    (Equivalent (nativeCandidate family).real (addZeroCandidate family).real ×
      NumericalFutureEquivalent (nativeCandidate family).real (addZeroCandidate family).real) ×
    ((nativeCandidate family).real = (addZeroCandidate family).real → Empty) :=
  ⟨uniqueness family, candidateConstructorsDistinct family⟩

def oldFirst := asExecutedCandidate (nativeCandidate family)
def oldSecond := asExecutedCandidate (addZeroCandidate family)
def queryOne : LimitQuery (uniquenessThreshold (oldFirst family) (oldSecond family)) := ⟨0,2,3,.refl _,⟨1,rfl⟩⟩
def queryTwo : LimitQuery (uniquenessThreshold (oldFirst family) (oldSecond family)) := ⟨2,7,8,⟨1,rfl⟩,⟨2,rfl⟩⟩
def mediatorPrior := executeReal (termReal (realizedFamily (native family)) 0) 1
def firstPrior := executeReal (nativeCandidate family).real 1
def secondPrior := executeReal (addZeroCandidate family).real 1
def rich := produceTrace (oldFirst family) (oldSecond family) (mediatorPrior family).next
  (firstPrior family).next (secondPrior family).next [queryOne family,queryTwo family]
def projectedTrace := (rich family).toNumerical

/-- The constitutive native uniqueness route has its own queries and begins
from a received current native bank.  The older realized-family trace above is
kept only as a downstream numerical-adapter test. -/
def nativeQueryOne : LimitQuery
    (nativeUniquenessThreshold (nativeCandidate family) (addZeroCandidate family)) :=
  ⟨0, 2, 3, .refl _, ⟨1, rfl⟩⟩

def nativeQueryTwo : LimitQuery
    (nativeUniquenessThreshold (nativeCandidate family) (addZeroCandidate family)) :=
  ⟨2, 7, 8, ⟨1, rfl⟩, ⟨2, rfl⟩⟩

def nativePacketOne := mediateNative (nativeCandidate family) (addZeroCandidate family)
  (seededBank family) (firstPrior family).next (secondPrior family).next (nativeQueryOne family)

theorem nativeMediatorFromCurrentBank : (nativePacketOne family).termStep = executeAt
    ((native family).terms ((native family).modulus 1))
    (seededBank family ((native family).modulus 1)) 1 :=
  (nativePacketOne family).termExact

theorem nativeFirstLawUsesMediator : (nativePacketOne family).firstNear =
    (nativeCandidate family).converges 1 ((native family).modulus 1) 1 2
      (nativePacketOne family).termStep (nativePacketOne family).firstStep
      (.refl _) (.refl _) (nativeFirstExtension
        (nativeCandidate family) (addZeroCandidate family) (nativeQueryOne family)) :=
  (nativePacketOne family).firstNearExact

theorem nativeSecondLawUsesSameMediator : (nativePacketOne family).secondNear =
    (addZeroCandidate family).converges 1 ((native family).modulus 1) 1 3
      (nativePacketOne family).termStep (nativePacketOne family).secondStep
      (.refl _) (.refl _) (nativeSecondExtension
        (nativeCandidate family) (addZeroCandidate family) (nativeQueryOne family)) :=
  (nativePacketOne family).secondNearExact

theorem nativeMediatorBankContinues :
    updateBank (seededBank family) ((native family).modulus 1)
      (nativePacketOne family).termStep.next ((native family).modulus 1) =
        (nativePacketOne family).termStep.next :=
  updateBank_hit _ _ _

def nativeRich := produceNativeUniquenessTrace
  (nativeCandidate family) (addZeroCandidate family) (seededBank family)
  (firstPrior family).next (secondPrior family).next
  [nativeQueryOne family, nativeQueryTwo family]

def nativeProjectedTrace := (nativeRich family).toNumerical
def nativeFinalBank := (nativeRich family).finalBank

def futureTrace := (uniqueness family).2.traces (firstPrior family).next (secondPrior family).next
  [nativeQueryOne family, nativeQueryTwo family]

def realizedCurrent := executeAt (termReal (realizedFamily (native family)) ((native family).modulus 0))
  (mediatorPrior family).next 2
def candidateObservation := observeCandidate (nativeCandidate family) 0 ((native family).modulus 0) 2 3
  (realizedCurrent family) (firstLimit family) (priorTerm family).next (.refl _) ⟨2,rfl⟩ ⟨3,rfl⟩
theorem candidateNativeCurrent : (candidateObservation family).nativeStep = executeAt
    ((native family).terms ((native family).modulus 0)) (priorTerm family).next 2 :=
  (candidateObservation family).nativeExact


/-- Changing the native term/diagonal index receives separate current contexts;
composite archive types are not silently cast across different term indices. -/
def higherTermContext := executeReal ((native family).terms ((native family).modulus 2)) 2
def higherDiagonalContext := executeReal ((native family).terms ((native family).modulus 5)) 2
def higherTerm := executeAt ((native family).terms ((native family).modulus 2)) (higherTermContext family).next 4
def higherLimit := executeAt (nativeLimit (native family)) (secondLimit family).next 5
def higherObservation := RelationalRealNativeCauchy.observeLimit (native family) 2 ((native family).modulus 2) 4 5
  (higherTerm family) (higherLimit family) (.refl _) ⟨2,rfl⟩ ⟨3,rfl⟩
theorem higherSourceOwned : (higherObservation family).diagonal =
    (higherLimit family).resource.diagonal := (higherObservation family).diagonalExact

theorem groupingConsumesExact : (firstLimit family).resource.grouping.memory.stored.action.source =
    (firstLimit family).resource.source := (firstLimit family).resource.groupedSourceExact

theorem targetInstalledExact : (firstLimit family).next.installed =
    some ⟨(priorLimit family).next.bank, (priorLimit family).next.journal, 3, (firstLimit family).resource⟩ := rfl

theorem targetReadExact : readNativeInstalled (firstLimit family).next = some (firstLimit family).code := rfl

theorem liveEventExact : (firstLimit family).liveEvent =
    ((environment (nativeLimit (native family))).liveStep
      ((environment (nativeLimit (native family))).project (priorLimit family).next) 3).event :=
  (firstLimit family).eventProjection

theorem liveNextExact : (environment (nativeLimit (native family))).project (firstLimit family).next =
    ((environment (nativeLimit (native family))).liveStep
      ((environment (nativeLimit (native family))).project (priorLimit family).next) 3).next :=
  (firstLimit family).nextProjection

theorem unvisitedBankUnchanged (k : Nat) (different : k ≠ (native family).modulus 3) :
    (firstLimit family).next.bank k = (priorLimit family).next.bank k := updateBank_other _ _ _ _ different

/-- On a new diagonal index, the old index remains available for a later return. -/
theorem returnToEarlierIndex (different : (native family).modulus 3 ≠ (native family).modulus 5) :
    (higherLimit family).next.bank ((native family).modulus 3) =
      (secondLimit family).next.bank ((native family).modulus 3) := updateBank_other _ _ _ _ different

def returnedLimit := executeAt (nativeLimit (native family)) (higherLimit family).next 3

theorem returnedDiagonalCurrent : (returnedLimit family).resource.diagonal =
    executeAt ((native family).terms ((native family).modulus 3))
      ((higherLimit family).next.bank ((native family).modulus 3)) 3 :=
  (returnedLimit family).resource.source.diagonalExact

def numericalLimitView := nativeProducedLimitCorrespondence (native family)


end RelationalPerimeter.Tests.RelationalRealNativeCauchy

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Tests.RelationalRealNativeCauchy.composedFamily
#print axioms RelationalPerimeter.Tests.RelationalRealNativeCauchy.native
#print axioms RelationalPerimeter.Tests.RelationalRealNativeCauchy.priorTerm
#print axioms RelationalPerimeter.Tests.RelationalRealNativeCauchy.priorLimit
#print axioms RelationalPerimeter.Tests.RelationalRealNativeCauchy.seededBank
#print axioms RelationalPerimeter.Tests.RelationalRealNativeCauchy.seededArchive
#print axioms RelationalPerimeter.Tests.RelationalRealNativeCauchy.priorDiagonal
#print axioms RelationalPerimeter.Tests.RelationalRealNativeCauchy.firstTerm
#print axioms RelationalPerimeter.Tests.RelationalRealNativeCauchy.firstLimit
#print axioms RelationalPerimeter.Tests.RelationalRealNativeCauchy.firstObservation
#print axioms RelationalPerimeter.Tests.RelationalRealNativeCauchy.secondTerm
#print axioms RelationalPerimeter.Tests.RelationalRealNativeCauchy.secondLimit
#print axioms RelationalPerimeter.Tests.RelationalRealNativeCauchy.secondObservation
#print axioms RelationalPerimeter.Tests.RelationalRealNativeCauchy.firstDiagonalCurrent
#print axioms RelationalPerimeter.Tests.RelationalRealNativeCauchy.secondDiagonalContinues
#print axioms RelationalPerimeter.Tests.RelationalRealNativeCauchy.currentSourceOwned
#print axioms RelationalPerimeter.Tests.RelationalRealNativeCauchy.nativeLawUsesOwnedSteps
#print axioms RelationalPerimeter.Tests.RelationalRealNativeCauchy.pairObservation
#print axioms RelationalPerimeter.Tests.RelationalRealNativeCauchy.projectedCodes
#print axioms RelationalPerimeter.Tests.RelationalRealNativeCauchy.termEquivalent
#print axioms RelationalPerimeter.Tests.RelationalRealNativeCauchy.termFutures
#print axioms RelationalPerimeter.Tests.RelationalRealNativeCauchy.completeness
#print axioms RelationalPerimeter.Tests.RelationalRealNativeCauchy.nativeCandidate
#print axioms RelationalPerimeter.Tests.RelationalRealNativeCauchy.certifiedCandidate
#print axioms RelationalPerimeter.Tests.RelationalRealNativeCauchy.addZeroCandidate
#print axioms RelationalPerimeter.Tests.RelationalRealNativeCauchy.candidateConstructorsDistinct
#print axioms RelationalPerimeter.Tests.RelationalRealNativeCauchy.uniqueness
#print axioms RelationalPerimeter.Tests.RelationalRealNativeCauchy.authoritativeUniqueness
#print axioms RelationalPerimeter.Tests.RelationalRealNativeCauchy.numericalAgreementWithoutIdentity
#print axioms RelationalPerimeter.Tests.RelationalRealNativeCauchy.oldFirst
#print axioms RelationalPerimeter.Tests.RelationalRealNativeCauchy.oldSecond
#print axioms RelationalPerimeter.Tests.RelationalRealNativeCauchy.queryOne
#print axioms RelationalPerimeter.Tests.RelationalRealNativeCauchy.queryTwo
#print axioms RelationalPerimeter.Tests.RelationalRealNativeCauchy.mediatorPrior
#print axioms RelationalPerimeter.Tests.RelationalRealNativeCauchy.firstPrior
#print axioms RelationalPerimeter.Tests.RelationalRealNativeCauchy.secondPrior
#print axioms RelationalPerimeter.Tests.RelationalRealNativeCauchy.rich
#print axioms RelationalPerimeter.Tests.RelationalRealNativeCauchy.projectedTrace
#print axioms RelationalPerimeter.Tests.RelationalRealNativeCauchy.nativeQueryOne
#print axioms RelationalPerimeter.Tests.RelationalRealNativeCauchy.nativeQueryTwo
#print axioms RelationalPerimeter.Tests.RelationalRealNativeCauchy.nativePacketOne
#print axioms RelationalPerimeter.Tests.RelationalRealNativeCauchy.nativeMediatorFromCurrentBank
#print axioms RelationalPerimeter.Tests.RelationalRealNativeCauchy.nativeFirstLawUsesMediator
#print axioms RelationalPerimeter.Tests.RelationalRealNativeCauchy.nativeSecondLawUsesSameMediator
#print axioms RelationalPerimeter.Tests.RelationalRealNativeCauchy.nativeMediatorBankContinues
#print axioms RelationalPerimeter.Tests.RelationalRealNativeCauchy.nativeRich
#print axioms RelationalPerimeter.Tests.RelationalRealNativeCauchy.nativeProjectedTrace
#print axioms RelationalPerimeter.Tests.RelationalRealNativeCauchy.nativeFinalBank
#print axioms RelationalPerimeter.Tests.RelationalRealNativeCauchy.futureTrace
#print axioms RelationalPerimeter.Tests.RelationalRealNativeCauchy.realizedCurrent
#print axioms RelationalPerimeter.Tests.RelationalRealNativeCauchy.candidateObservation
#print axioms RelationalPerimeter.Tests.RelationalRealNativeCauchy.candidateNativeCurrent
#print axioms RelationalPerimeter.Tests.RelationalRealNativeCauchy.higherTermContext
#print axioms RelationalPerimeter.Tests.RelationalRealNativeCauchy.higherDiagonalContext
#print axioms RelationalPerimeter.Tests.RelationalRealNativeCauchy.higherTerm
#print axioms RelationalPerimeter.Tests.RelationalRealNativeCauchy.higherLimit
#print axioms RelationalPerimeter.Tests.RelationalRealNativeCauchy.higherObservation
#print axioms RelationalPerimeter.Tests.RelationalRealNativeCauchy.higherSourceOwned
#print axioms RelationalPerimeter.Tests.RelationalRealNativeCauchy.groupingConsumesExact
#print axioms RelationalPerimeter.Tests.RelationalRealNativeCauchy.targetInstalledExact
#print axioms RelationalPerimeter.Tests.RelationalRealNativeCauchy.targetReadExact
#print axioms RelationalPerimeter.Tests.RelationalRealNativeCauchy.liveEventExact
#print axioms RelationalPerimeter.Tests.RelationalRealNativeCauchy.liveNextExact
#print axioms RelationalPerimeter.Tests.RelationalRealNativeCauchy.unvisitedBankUnchanged
#print axioms RelationalPerimeter.Tests.RelationalRealNativeCauchy.returnToEarlierIndex
#print axioms RelationalPerimeter.Tests.RelationalRealNativeCauchy.returnedLimit
#print axioms RelationalPerimeter.Tests.RelationalRealNativeCauchy.returnedDiagonalCurrent
#print axioms RelationalPerimeter.Tests.RelationalRealNativeCauchy.numericalLimitView
/- AXIOM_AUDIT_END -/
