import Tests.RelationalRealRuntime
import Tests.RelationalRealArithmetic

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace RelationalPerimeter.Tests.RelationalRealNegation
open StrongPerimetralTurning
open RelationalPerimeter.Constitution.Reals
open HeterogeneousRealRuntime RelationalRealAddition
open RelationalPerimeter.Constitution.Reals.RelationalRealNegation

variable (P : CircularPresentation) (baseDepth : Nat)

def negativeSum : Real P baseDepth := .neg (RelationalRealRuntime.sum P baseDepth)
def first (p : Nat) := executeReal (negativeSum P baseDepth) p
def second (p q : Nat) := executeAt (negativeSum P baseDepth) (first P baseDepth p).next q

theorem ownsCurrentSource (p q : Nat) :
    (second P baseDepth p q).resource.source =
      executeAt (RelationalRealRuntime.sum P baseDepth) (first P baseDepth p).next.source q := rfl

theorem receivedSourceIsOwnedStep (p : Nat) :
    (first P baseDepth p).resource.action.memory.continued.authorized.acted.searched.received.context =
      (first P baseDepth p).resource.source := (first P baseDepth p).resource.action.receivedContext_is_produced

theorem retainedActionConsumesSameSource (p : Nat) :
    (first P baseDepth p).resource.action.action.source = (first P baseDepth p).resource.source := by
  rw [(first P baseDepth p).resource.action.action.sourceExact,
    (first P baseDepth p).resource.action.searchResult_is_receivedContextOutput,
    (first P baseDepth p).resource.action.receivedContext_is_produced]
  rfl

theorem installedTargetIsSameAction (p : Nat) :
    (first P baseDepth p).code = (first P baseDepth p).resource.action.action.code ∧
      (first P baseDepth p).next.last = some (first P baseDepth p).resource.action.action.code ∧
      (first P baseDepth p).liveEvent.code = (first P baseDepth p).resource.action.action.code :=
  negationPacketSameTarget _

theorem currentJournalContinues (p q : Nat) :
    (second P baseDepth p q).next.journal.absoluteDepth = baseDepth + 12 := by
  change (second P baseDepth p q).resource.action.completedJournal.absoluteDepth = _
  rw [(second P baseDepth p q).resource.action.completed_absoluteDepth]
  change (first P baseDepth p).resource.action.completedJournal.absoluteDepth + 6 = _
  rw [(first P baseDepth p).resource.action.completed_absoluteDepth]
  exact Nat.add_assoc baseDepth 6 6

theorem chronologicalPacketsRetained (p q : Nat) :
    (second P baseDepth p q).next.retained.length = 2 := rfl

theorem eventOwnsCurrentPacket (p q : Nat) :
    (second P baseDepth p q).event.archive = (first P baseDepth p).next ∧
      (second P baseDepth p q).event.precision = q ∧
      (second P baseDepth p q).event.production = (second P baseDepth p q).resource :=
  negationRichEventOwnsProduction _

theorem richEventsRemainDistinct (p : Nat) :
    (first P baseDepth p).event ≠ (second P baseDepth p p).event := by
  intro same
  have lengths := congrArg (fun event => event.archive.retained.length) same
  change 0 = 1 at lengths
  cases lengths

theorem currentReadoutMatches (p q : Nat) :
    (second P baseDepth p q).code = readout (negativeSum P baseDepth) q := currentReadout _ _ _ _

def negativeThreeQuarters (p : Nat) :
    SameValue (readout (negativeSum P baseDepth) p) (⟨0, 3, 2⟩ : SignedDyadicCode) := by
  change SameValue (readout (.neg (RelationalRealRuntime.sum P baseDepth)) p) _
  rw [neg_readout_exact]
  exact (RelationalRealRuntime.sumHasExpectedValue P baseDepth p).neg

def twoPrecisions := (negativeThreeQuarters P baseDepth 0, negativeThreeQuarters P baseDepth 7)

def nonzeroNegatedBudget : Near 1 SignedDyadicCode.zero.neg RelationalRealArithmetic.half.neg :=
  RelationalRealArithmetic.halfError.neg

theorem dyadicNegationKeepsScale :
    (RelationalRealArithmetic.half.raise 3).neg = RelationalRealArithmetic.half.neg.raise 3 := rfl

def currentCoherence (p q accuracy : Nat) (hp : PrecisionExtension accuracy p) (hq : PrecisionExtension accuracy q) :
    Near accuracy (first P baseDepth p).code (second P baseDepth p q).code :=
  (coherent (negativeSum P baseDepth)).near accuracy p q (first P baseDepth p) (second P baseDepth p q) hp hq

def involution := RelationalRealAddition.neg_neg (negativeSum P baseDepth)
def inverseRight := RelationalRealAddition.add_neg (negativeSum P baseDepth)
def inverseLeft := RelationalRealAddition.neg_add (negativeSum P baseDepth)
def distributes := neg_sum (negativeSum P baseDepth) (RelationalRealRuntime.sum P baseDepth)
def negationCongruence := neg_congr (RelationalRealRuntime.nestedAssociativity P baseDepth)
def groupPackage := additiveGroupLaws P baseDepth
def groupFuturePackage := additiveGroupFutureLaws P baseDepth

def inverseFutures := (inverseRight P baseDepth).toFutures
def query (accuracy : Nat) : RuntimeCorrespondence.LimitQuery (inverseFutures P baseDepth).threshold :=
  ⟨accuracy, (inverseFutures P baseDepth).threshold accuracy, (inverseFutures P baseDepth).threshold accuracy,
    PrecisionExtension.refl _, PrecisionExtension.refl _⟩

def twoInverseFutures :=
  (inverseFutures P baseDepth).traces
    (environment (.add (negativeSum P baseDepth) (.neg (negativeSum P baseDepth)))).initialArchive
    (environment (zero P baseDepth)).initialArchive [query P baseDepth 0, query P baseDepth 4]

theorem allRichFuturesProject (p q : Nat) :
    projectOutcome (environment (negativeSum P baseDepth))
      (run (environment (negativeSum P baseDepth)) (environment (negativeSum P baseDepth)).initialArchive [p, q]).trace.outcome =
    (runLive (environment (negativeSum P baseDepth)).liveEnvironment
      ((environment (negativeSum P baseDepth)).project (environment (negativeSum P baseDepth)).initialArchive) [p, q]).outcome :=
  run_outcome_projects _ _ _

theorem exactMemoryOnlyAtFixedEnvironment {first second : (environment (negativeSum P baseDepth)).Memory} :
    first = second ↔ ConstitutiveSearch.ContinuationSignatures.FutureEquivalent
      (liveContract (environment (negativeSum P baseDepth))) first second := liveMinimality _

def presentationTransport := toPresentation_neg (negativeSum P baseDepth)
def carrierTransport := toCarrier_neg (negativeSum P baseDepth)
def presentationRealization := realization_neg (toPresentation (negativeSum P baseDepth)) (P := P) (baseDepth := baseDepth)
def carrierRealization := realization_carrier_neg (toCarrier (negativeSum P baseDepth)) (P := P) (baseDepth := baseDepth)
def roundtrip := real_roundtrip (.neg (.add (negativeSum P baseDepth) (RelationalRealRuntime.sum P baseDepth)))

end RelationalPerimeter.Tests.RelationalRealNegation

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Tests.RelationalRealNegation.negativeSum
#print axioms RelationalPerimeter.Tests.RelationalRealNegation.first
#print axioms RelationalPerimeter.Tests.RelationalRealNegation.second
#print axioms RelationalPerimeter.Tests.RelationalRealNegation.ownsCurrentSource
#print axioms RelationalPerimeter.Tests.RelationalRealNegation.receivedSourceIsOwnedStep
#print axioms RelationalPerimeter.Tests.RelationalRealNegation.retainedActionConsumesSameSource
#print axioms RelationalPerimeter.Tests.RelationalRealNegation.installedTargetIsSameAction
#print axioms RelationalPerimeter.Tests.RelationalRealNegation.currentJournalContinues
#print axioms RelationalPerimeter.Tests.RelationalRealNegation.chronologicalPacketsRetained
#print axioms RelationalPerimeter.Tests.RelationalRealNegation.eventOwnsCurrentPacket
#print axioms RelationalPerimeter.Tests.RelationalRealNegation.richEventsRemainDistinct
#print axioms RelationalPerimeter.Tests.RelationalRealNegation.currentReadoutMatches
#print axioms RelationalPerimeter.Tests.RelationalRealNegation.negativeThreeQuarters
#print axioms RelationalPerimeter.Tests.RelationalRealNegation.twoPrecisions
#print axioms RelationalPerimeter.Tests.RelationalRealNegation.nonzeroNegatedBudget
#print axioms RelationalPerimeter.Tests.RelationalRealNegation.dyadicNegationKeepsScale
#print axioms RelationalPerimeter.Tests.RelationalRealNegation.currentCoherence
#print axioms RelationalPerimeter.Tests.RelationalRealNegation.involution
#print axioms RelationalPerimeter.Tests.RelationalRealNegation.inverseRight
#print axioms RelationalPerimeter.Tests.RelationalRealNegation.inverseLeft
#print axioms RelationalPerimeter.Tests.RelationalRealNegation.distributes
#print axioms RelationalPerimeter.Tests.RelationalRealNegation.negationCongruence
#print axioms RelationalPerimeter.Tests.RelationalRealNegation.groupPackage
#print axioms RelationalPerimeter.Tests.RelationalRealNegation.groupFuturePackage
#print axioms RelationalPerimeter.Tests.RelationalRealNegation.inverseFutures
#print axioms RelationalPerimeter.Tests.RelationalRealNegation.query
#print axioms RelationalPerimeter.Tests.RelationalRealNegation.twoInverseFutures
#print axioms RelationalPerimeter.Tests.RelationalRealNegation.allRichFuturesProject
#print axioms RelationalPerimeter.Tests.RelationalRealNegation.exactMemoryOnlyAtFixedEnvironment
#print axioms RelationalPerimeter.Tests.RelationalRealNegation.presentationTransport
#print axioms RelationalPerimeter.Tests.RelationalRealNegation.carrierTransport
#print axioms RelationalPerimeter.Tests.RelationalRealNegation.presentationRealization
#print axioms RelationalPerimeter.Tests.RelationalRealNegation.carrierRealization
#print axioms RelationalPerimeter.Tests.RelationalRealNegation.roundtrip
/- AXIOM_AUDIT_END -/
