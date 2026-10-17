import RelationalPerimeter.Constitution.Reals.RelationalRealAddition

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace RelationalPerimeter.Tests.RelationalRealRuntime
open StrongPerimetralTurning
open RelationalPerimeter.Constitution.Reals
open RuntimeCorrespondence
open HeterogeneousRealRuntime
open RelationalRealAddition

variable (P : CircularPresentation) (baseDepth : Nat)

def halfRuntime : RuntimeReal P baseDepth := constantRuntime P baseDepth ⟨1, 0, 1⟩
def quarterRuntime : RuntimeReal P baseDepth := constantRuntime P baseDepth ⟨1, 0, 2⟩
def half : Real P baseDepth := .leaf (halfRuntime P baseDepth)
def quarter : Real P baseDepth := .leaf (quarterRuntime P baseDepth)
def sum : Real P baseDepth := .add (half P baseDepth) (quarter P baseDepth)
def leftNested : Real P baseDepth := .add (sum P baseDepth) (one P baseDepth)
def rightNested : Real P baseDepth := .add (half P baseDepth) (.add (quarter P baseDepth) (one P baseDepth))

theorem leafIsAuthoritative (p : Nat) :
    (executeReal (half P baseDepth) p).resource =
      AuthoritativeRuntime.perform (halfRuntime P baseDepth).family (halfRuntime P baseDepth).initial (.limit p) :=
  (halfRuntime P baseDepth).stepAt_is_perform p

theorem bothSourcesRetained (p : Nat) :
    (executeReal (sum P baseDepth) p).resource.left.resource = (halfRuntime P baseDepth).stepAt (Nat.succ p) ∧
    (executeReal (sum P baseDepth) p).resource.right.resource = (quarterRuntime P baseDepth).stepAt (Nat.succ p) :=
  ⟨rfl, rfl⟩

theorem receivedContextOwnsBoth (p : Nat) :
    (executeReal (sum P baseDepth) p).resource.action.memory.continued.authorized.acted.searched.received.context =
      ⟨(executeReal (sum P baseDepth) p).resource.left,
        (executeReal (sum P baseDepth) p).resource.right⟩ :=
  (executeReal (sum P baseDepth) p).resource.action.receivedContext_is_produced

theorem oneInstalledTarget (p : Nat) :
    (executeReal (sum P baseDepth) p).code = (executeReal (sum P baseDepth) p).resource.action.action.code ∧
      (executeReal (sum P baseDepth) p).next.last =
        some (executeReal (sum P baseDepth) p).resource.action.action.code ∧
      (executeReal (sum P baseDepth) p).liveEvent.code =
        (executeReal (sum P baseDepth) p).resource.action.action.code :=
  additionPacketSameTarget _

theorem leftNestingRetainsInnerExecution (p : Nat) :
    (executeReal (leftNested P baseDepth) p).resource.left.resource.left.resource =
      (halfRuntime P baseDepth).stepAt (Nat.succ (Nat.succ p)) ∧
    (executeReal (leftNested P baseDepth) p).resource.left.resource.right.resource =
      (quarterRuntime P baseDepth).stepAt (Nat.succ (Nat.succ p)) := ⟨rfl, rfl⟩

theorem rightNestingRetainsInnerExecution (p : Nat) :
    (executeReal (rightNested P baseDepth) p).resource.right.resource.left.resource =
      (quarterRuntime P baseDepth).stepAt (Nat.succ (Nat.succ p)) ∧
    (executeReal (rightNested P baseDepth) p).resource.left.resource =
      (halfRuntime P baseDepth).stepAt (Nat.succ p) := ⟨rfl, rfl⟩

def leafProvenance (p : Nat) :=
  (executeReal (sum P baseDepth) p).resource.left.resource.response.limitProduction.execution.provenance

/-- Both native Steps are retained even when their canonical values coincide. -/
def repeatedBothOrigins (p : Nat) :=
  let step := executeReal (.add (half P baseDepth) (half P baseDepth)) p
  (step.resource.left, step.resource.right)

theorem repeatedReadoutsCoincide (p : Nat) :
    (repeatedBothOrigins P baseDepth p).1.resource.response.readout =
      (repeatedBothOrigins P baseDepth p).2.resource.response.readout := rfl

/-- Role distinction does not assert inequality of the underlying Lean values. -/
theorem repeatedNativeStepsMayCoincide (p : Nat) :
    (repeatedBothOrigins P baseDepth p).1 = (repeatedBothOrigins P baseDepth p).2 := rfl

/-- Even in that case the action owns both ordered operand positions. -/
theorem repeatedActionKeepsBothRoles (p : Nat) :
    (executeReal (.add (half P baseDepth) (half P baseDepth)) p).resource.action.action.operands =
      repeatedBothOrigins P baseDepth p := by
  rw [(executeReal (.add (half P baseDepth) (half P baseDepth)) p).resource.action.action.operandsExact,
    (executeReal (.add (half P baseDepth) (half P baseDepth)) p).resource.action.searchResult_is_receivedContextOutput,
    (executeReal (.add (half P baseDepth) (half P baseDepth)) p).resource.action.receivedContext_is_produced]
  rfl

def zeroReadoutsAtTwoPrecisions :
    SameValue (readout (zero P baseDepth) 0) SignedDyadicCode.zero ×
      SameValue (readout (zero P baseDepth) 7) (SignedDyadicCode.zero.raise 3) :=
  ⟨constant_readout _ _, (constant_readout _ _).trans (SameValue.raiseExact _ 3)⟩

def oneReadoutsAtTwoPrecisions :
    SameValue (readout (one P baseDepth) 1) SignedDyadicCode.one ×
      SameValue (readout (one P baseDepth) 8) (SignedDyadicCode.one.raise 4) :=
  ⟨constant_readout _ _, (constant_readout _ _).trans (SameValue.raiseExact _ 4)⟩

/-- The runtime sum, not an external presentation, produces three quarters. -/
def sumHasExpectedValue (p : Nat) :
    SameValue (readout (sum P baseDepth) p) (⟨3, 0, 2⟩ : SignedDyadicCode) :=
  (add_readout _ _ _).trans
    ((SameValue.add (constant_readout ⟨1, 0, 1⟩ (Nat.succ p))
      (constant_readout ⟨1, 0, 2⟩ (Nat.succ p))).trans
      (SameValue.raiseExact (⟨3, 0, 2⟩ : SignedDyadicCode) 1).symm)

def sumReadoutsAtTwoPrecisions :=
  (sumHasExpectedValue P baseDepth 0, sumHasExpectedValue P baseDepth 6)

def firstSumStep (p : Nat) := executeReal (sum P baseDepth) p
def secondSumStep (p q : Nat) := executeAt (sum P baseDepth) (firstSumStep P baseDepth p).next q

theorem secondLeftUsesCurrentArchive (p q : Nat) :
    (secondSumStep P baseDepth p q).resource.left.resource =
      AuthoritativeRuntime.perform (halfRuntime P baseDepth).family
        (firstSumStep P baseDepth p).next.left.state (.limit (Nat.succ q)) :=
  (halfRuntime P baseDepth).produced.produceCanonical
    (firstSumStep P baseDepth p).next.left.state (firstSumStep P baseDepth p).next.left.reachable (Nat.succ q)

theorem sourceDepthAfterTwo (p q : Nat) :
    (secondSumStep P baseDepth p q).next.left.state.journal.absoluteDepth = baseDepth + 24 := by
  have firstDepth := limitStep_nextDepth (firstSumStep P baseDepth p).resource.left.resource
  have secondDepth := limitStep_nextDepth (secondSumStep P baseDepth p q).resource.left.resource
  exact secondDepth.trans ((congrArg (fun depth => depth + 12) firstDepth).trans (Nat.add_assoc baseDepth 12 12))

theorem arithmeticJournalContinues (p q : Nat) :
    (secondSumStep P baseDepth p q).next.journal.absoluteDepth = baseDepth + 12 := by
  change (secondSumStep P baseDepth p q).resource.action.completedJournal.absoluteDepth = _
  rw [(secondSumStep P baseDepth p q).resource.action.completed_absoluteDepth]
  change (firstSumStep P baseDepth p).resource.action.completedJournal.absoluteDepth + 6 = _
  rw [(firstSumStep P baseDepth p).resource.action.completed_absoluteDepth]
  exact Nat.add_assoc baseDepth 6 6

theorem archiveRetainsTwoEntries (p q : Nat) :
    (secondSumStep P baseDepth p q).next.retained.length = 2 := rfl

theorem archiveRetainsExactProduction (p : Nat) :
    (firstSumStep P baseDepth p).next.retained =
      [⟨(environment (half P baseDepth)).initialArchive, (environment (quarter P baseDepth)).initialArchive,
        ConstitutiveRuntime.Journal.root P baseDepth, p, (firstSumStep P baseDepth p).resource⟩] := rfl

theorem eventRetainsRealOperandFuture (p q : Nat) :
    (secondSumStep P baseDepth p q).event.production.left =
        (secondSumStep P baseDepth p q).resource.left ∧
      (secondSumStep P baseDepth p q).event.production.right =
        (secondSumStep P baseDepth p q).resource.right := ⟨rfl, rfl⟩

theorem richEventOwnsCurrentArchive (p q : Nat) :
    (secondSumStep P baseDepth p q).event.archive = (firstSumStep P baseDepth p).next ∧
      (secondSumStep P baseDepth p q).event.precision = q ∧
      (secondSumStep P baseDepth p q).event.production =
        (secondSumStep P baseDepth p q).resource :=
  additionRichEventOwnsProduction _

/-- Equal numerical answers do not erase the current archive from a rich event. -/
theorem chronologicalRichEventsRemainDistinct (p : Nat) :
    (firstSumStep P baseDepth p).event ≠ (secondSumStep P baseDepth p p).event := by
  intro same
  have lengths := congrArg (fun event => event.archive.retained.length) same
  change 0 = 1 at lengths
  cases lengths

theorem chronologicalAnswersCanCoincide (p : Nat) :
    (firstSumStep P baseDepth p).code = (secondSumStep P baseDepth p p).code :=
  (currentReadout _ _ _ _).trans (currentReadout _ _ _ _).symm

theorem currentAnswersAgreeNumerically (p q : Nat) :
    (secondSumStep P baseDepth p q).code = readout (sum P baseDepth) q :=
  currentReadout _ _ _ _

def sumCoherent (p l r : Nat) (hl : PrecisionExtension p l) (hr : PrecisionExtension p r) :
    Near p (readout (sum P baseDepth) l) (readout (sum P baseDepth) r) :=
  readoutsNear _ p l r hl hr

def currentSumCoherent (p q accuracy : Nat) (hp : PrecisionExtension accuracy p) (hq : PrecisionExtension accuracy q) :
    Near accuracy (firstSumStep P baseDepth p).code (secondSumStep P baseDepth p q).code :=
  (coherent (sum P baseDepth)).near accuracy p q (firstSumStep P baseDepth p) (secondSumStep P baseDepth p q) hp hq

def nestedAssociativity : Equivalent (leftNested P baseDepth) (rightNested P baseDepth) :=
  RelationalRealAddition.add_assoc _ _ _

def nestedFutures : NumericalFutureEquivalent (leftNested P baseDepth) (rightNested P baseDepth) :=
  (nestedAssociativity P baseDepth).toFutures

def query (accuracy : Nat) : LimitQuery (nestedFutures P baseDepth).threshold :=
  ⟨accuracy, (nestedFutures P baseDepth).threshold accuracy,
    (nestedFutures P baseDepth).threshold accuracy, PrecisionExtension.refl _, PrecisionExtension.refl _⟩

def twoExecutedFutures :
    NumericalTrace (leftNested P baseDepth) (rightNested P baseDepth) (nestedFutures P baseDepth).threshold
      (environment (leftNested P baseDepth)).initialArchive (environment (rightNested P baseDepth)).initialArchive
      [query P baseDepth 0, query P baseDepth 3] :=
  (nestedFutures P baseDepth).traces
    (environment (leftNested P baseDepth)).initialArchive (environment (rightNested P baseDepth)).initialArchive
    [query P baseDepth 0, query P baseDepth 3]

def congruence : Equivalent (.add (leftNested P baseDepth) (sum P baseDepth))
    (.add (rightNested P baseDepth) (sum P baseDepth)) :=
  add_congr (nestedAssociativity P baseDepth) (Equivalent.refl _)

def zeroLaw : Equivalent (.add (zero P baseDepth) (sum P baseDepth)) (sum P baseDepth) :=
  RelationalRealAddition.zero_add _

def commutativeLaw : Equivalent (sum P baseDepth) (.add (quarter P baseDepth) (half P baseDepth)) :=
  RelationalRealAddition.add_comm _ _

def readoutAfterConstruction (p : Nat) : SameValue
    (readout (sum P baseDepth) p)
    ((readout (half P baseDepth) (Nat.succ p)).add (readout (quarter P baseDepth) (Nat.succ p))) := add_readout _ _ _

def presentationTransport := toPresentation_add (half P baseDepth) (quarter P baseDepth)
def carrierTransport := toCarrier_add (half P baseDepth) (quarter P baseDepth)
def runtimeRoundtrip := real_roundtrip (leftNested P baseDepth)

theorem archiveNextProjects (p q : Nat) :
    (environment (sum P baseDepth)).project (secondSumStep P baseDepth p q).next =
      ((environment (sum P baseDepth)).liveStep
        ((environment (sum P baseDepth)).project (firstSumStep P baseDepth p).next) q).next :=
  (secondSumStep P baseDepth p q).nextProjection

theorem archiveEventProjects (p q : Nat) :
    (secondSumStep P baseDepth p q).liveEvent =
      ((environment (sum P baseDepth)).liveStep
        ((environment (sum P baseDepth)).project (firstSumStep P baseDepth p).next) q).event :=
  (secondSumStep P baseDepth p q).eventProjection

theorem exactMemoryContract {first second : (environment (sum P baseDepth)).Memory} :
    first = second ↔ ConstitutiveSearch.ContinuationSignatures.FutureEquivalent
      (liveContract (environment (sum P baseDepth))) first second := liveMinimality _

def executedRun : RunResult (environment (leftNested P baseDepth))
    (environment (leftNested P baseDepth)).initialArchive [0, 2] :=
  run (environment (leftNested P baseDepth)) (environment (leftNested P baseDepth)).initialArchive [0, 2]

theorem executedRunRetainsTwoPackets : (executedRun P baseDepth).trace.length = 2 := run_length _ _ _

theorem executedRunReadsInstalledFinalTarget :
    (executedRun P baseDepth).final.last =
      some (executeAt (leftNested P baseDepth) (executeReal (leftNested P baseDepth) 0).next 2).code := by
  exact congrArg AdditionArchive.last (run_two_final (environment (leftNested P baseDepth))
    (environment (leftNested P baseDepth)).initialArchive 0 2)

theorem executedRunHasExactContract :
    (executedRun P baseDepth).trace.outcome =
      (richContract (environment (leftNested P baseDepth))).outcome
        (environment (leftNested P baseDepth)).initialArchive [0, 2] := run_contract _ _ _

theorem richContractProjectsToArchiveContract :
    projectOutcome (environment (leftNested P baseDepth))
        ((richContract (environment (leftNested P baseDepth))).outcome
          (environment (leftNested P baseDepth)).initialArchive [0, 2]) =
      (projectedArchiveContract (environment (leftNested P baseDepth))).outcome
        (environment (leftNested P baseDepth)).initialArchive [0, 2] :=
  projectOutcome_richContract _ _ _

theorem wholeRunProjectsToLive :
    projectOutcome (environment (leftNested P baseDepth)) (executedRun P baseDepth).trace.outcome =
      (liveContract (environment (leftNested P baseDepth))).outcome
        ((environment (leftNested P baseDepth)).project (environment (leftNested P baseDepth)).initialArchive) [0, 2] :=
  (run_outcome_projects _ _ _).trans
    (runLive_contract _ _ _)

def executedRunReachable :
    Reachable (environment (leftNested P baseDepth)) (executedRun P baseDepth).final :=
  (executedRun P baseDepth).trace.reachable .initial

def executedLiveRun : LiveRunResult (environment (leftNested P baseDepth)).liveEnvironment :=
  runLive (environment (leftNested P baseDepth)).liveEnvironment
    ((environment (leftNested P baseDepth)).project (environment (leftNested P baseDepth)).initialArchive) [0, 2]

theorem liveRunUsesProjectedFinalMemory :
    (environment (leftNested P baseDepth)).project (executedRun P baseDepth).final =
      (executedLiveRun P baseDepth).final := run_final_projects _ _ _

theorem liveRunHasProjectedOutcome :
    projectOutcome (environment (leftNested P baseDepth)) (executedRun P baseDepth).trace.outcome =
      (executedLiveRun P baseDepth).outcome := run_outcome_projects _ _ _

theorem archivedRuntimeBridge :
    (runArchived (initialReal (leftNested P baseDepth)) [0, 2]).1.live =
      (runRuntime (initialReal (leftNested P baseDepth)).live [0, 2]).1 := runArchived_runtime _ _

theorem liveStepHasSameCode (p : Nat) :
    (executeReal (leftNested P baseDepth) p).code =
      (performRuntime (initialReal (leftNested P baseDepth)).live p).code := archivedCode_runtime _ _ _

end RelationalPerimeter.Tests.RelationalRealRuntime

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Tests.RelationalRealRuntime.halfRuntime
#print axioms RelationalPerimeter.Tests.RelationalRealRuntime.quarterRuntime
#print axioms RelationalPerimeter.Tests.RelationalRealRuntime.half
#print axioms RelationalPerimeter.Tests.RelationalRealRuntime.quarter
#print axioms RelationalPerimeter.Tests.RelationalRealRuntime.sum
#print axioms RelationalPerimeter.Tests.RelationalRealRuntime.leftNested
#print axioms RelationalPerimeter.Tests.RelationalRealRuntime.rightNested
#print axioms RelationalPerimeter.Tests.RelationalRealRuntime.leafIsAuthoritative
#print axioms RelationalPerimeter.Tests.RelationalRealRuntime.bothSourcesRetained
#print axioms RelationalPerimeter.Tests.RelationalRealRuntime.receivedContextOwnsBoth
#print axioms RelationalPerimeter.Tests.RelationalRealRuntime.oneInstalledTarget
#print axioms RelationalPerimeter.Tests.RelationalRealRuntime.leftNestingRetainsInnerExecution
#print axioms RelationalPerimeter.Tests.RelationalRealRuntime.rightNestingRetainsInnerExecution
#print axioms RelationalPerimeter.Tests.RelationalRealRuntime.leafProvenance
#print axioms RelationalPerimeter.Tests.RelationalRealRuntime.repeatedBothOrigins
#print axioms RelationalPerimeter.Tests.RelationalRealRuntime.repeatedReadoutsCoincide
#print axioms RelationalPerimeter.Tests.RelationalRealRuntime.repeatedNativeStepsMayCoincide
#print axioms RelationalPerimeter.Tests.RelationalRealRuntime.repeatedActionKeepsBothRoles
#print axioms RelationalPerimeter.Tests.RelationalRealRuntime.zeroReadoutsAtTwoPrecisions
#print axioms RelationalPerimeter.Tests.RelationalRealRuntime.oneReadoutsAtTwoPrecisions
#print axioms RelationalPerimeter.Tests.RelationalRealRuntime.sumHasExpectedValue
#print axioms RelationalPerimeter.Tests.RelationalRealRuntime.sumReadoutsAtTwoPrecisions
#print axioms RelationalPerimeter.Tests.RelationalRealRuntime.firstSumStep
#print axioms RelationalPerimeter.Tests.RelationalRealRuntime.secondSumStep
#print axioms RelationalPerimeter.Tests.RelationalRealRuntime.secondLeftUsesCurrentArchive
#print axioms RelationalPerimeter.Tests.RelationalRealRuntime.sourceDepthAfterTwo
#print axioms RelationalPerimeter.Tests.RelationalRealRuntime.arithmeticJournalContinues
#print axioms RelationalPerimeter.Tests.RelationalRealRuntime.archiveRetainsTwoEntries
#print axioms RelationalPerimeter.Tests.RelationalRealRuntime.archiveRetainsExactProduction
#print axioms RelationalPerimeter.Tests.RelationalRealRuntime.eventRetainsRealOperandFuture
#print axioms RelationalPerimeter.Tests.RelationalRealRuntime.richEventOwnsCurrentArchive
#print axioms RelationalPerimeter.Tests.RelationalRealRuntime.chronologicalRichEventsRemainDistinct
#print axioms RelationalPerimeter.Tests.RelationalRealRuntime.chronologicalAnswersCanCoincide
#print axioms RelationalPerimeter.Tests.RelationalRealRuntime.currentAnswersAgreeNumerically
#print axioms RelationalPerimeter.Tests.RelationalRealRuntime.sumCoherent
#print axioms RelationalPerimeter.Tests.RelationalRealRuntime.currentSumCoherent
#print axioms RelationalPerimeter.Tests.RelationalRealRuntime.nestedAssociativity
#print axioms RelationalPerimeter.Tests.RelationalRealRuntime.nestedFutures
#print axioms RelationalPerimeter.Tests.RelationalRealRuntime.query
#print axioms RelationalPerimeter.Tests.RelationalRealRuntime.twoExecutedFutures
#print axioms RelationalPerimeter.Tests.RelationalRealRuntime.congruence
#print axioms RelationalPerimeter.Tests.RelationalRealRuntime.zeroLaw
#print axioms RelationalPerimeter.Tests.RelationalRealRuntime.commutativeLaw
#print axioms RelationalPerimeter.Tests.RelationalRealRuntime.readoutAfterConstruction
#print axioms RelationalPerimeter.Tests.RelationalRealRuntime.presentationTransport
#print axioms RelationalPerimeter.Tests.RelationalRealRuntime.carrierTransport
#print axioms RelationalPerimeter.Tests.RelationalRealRuntime.runtimeRoundtrip
#print axioms RelationalPerimeter.Tests.RelationalRealRuntime.archiveNextProjects
#print axioms RelationalPerimeter.Tests.RelationalRealRuntime.archiveEventProjects
#print axioms RelationalPerimeter.Tests.RelationalRealRuntime.exactMemoryContract
#print axioms RelationalPerimeter.Tests.RelationalRealRuntime.executedRun
#print axioms RelationalPerimeter.Tests.RelationalRealRuntime.executedRunRetainsTwoPackets
#print axioms RelationalPerimeter.Tests.RelationalRealRuntime.executedRunReadsInstalledFinalTarget
#print axioms RelationalPerimeter.Tests.RelationalRealRuntime.executedRunHasExactContract
#print axioms RelationalPerimeter.Tests.RelationalRealRuntime.richContractProjectsToArchiveContract
#print axioms RelationalPerimeter.Tests.RelationalRealRuntime.wholeRunProjectsToLive
#print axioms RelationalPerimeter.Tests.RelationalRealRuntime.executedRunReachable
#print axioms RelationalPerimeter.Tests.RelationalRealRuntime.executedLiveRun
#print axioms RelationalPerimeter.Tests.RelationalRealRuntime.liveRunUsesProjectedFinalMemory
#print axioms RelationalPerimeter.Tests.RelationalRealRuntime.liveRunHasProjectedOutcome
#print axioms RelationalPerimeter.Tests.RelationalRealRuntime.archivedRuntimeBridge
#print axioms RelationalPerimeter.Tests.RelationalRealRuntime.liveStepHasSameCode
/- AXIOM_AUDIT_END -/
