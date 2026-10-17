import Tests.RelationalRealNegation
import RelationalPerimeter.Constitution.Reals.RelationalRealMultiplicativeLaws

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace RelationalPerimeter.Tests.RelationalRealMultiplication
open StrongPerimetralTurning
open RelationalPerimeter.Constitution.Reals
open HeterogeneousRealRuntime RelationalRealAddition
open RelationalPerimeter.Constitution.Reals.RelationalRealMultiplication
variable (P : CircularPresentation) (baseDepth : Nat)

/-- Both roles alias the same real, but each probes and refines independently. -/
def square : Real P baseDepth := .mul (RelationalRealRuntime.sum P baseDepth) (RelationalRealRuntime.sum P baseDepth)
def first (p : Nat) := executeReal (square P baseDepth) p
def second (p q : Nat) := executeAt (square P baseDepth) (first P baseDepth p).next q

theorem currentProbes (p q : Nat) :
    (second P baseDepth p q).resource.leftProbe =
      executeAt (RelationalRealRuntime.sum P baseDepth) (first P baseDepth p).next.left 0 ∧
    (second P baseDepth p q).resource.rightProbe =
      executeAt (RelationalRealRuntime.sum P baseDepth) (first P baseDepth p).next.right 0 := ⟨rfl, rfl⟩

theorem exactProbeSuccessors (p q : Nat) :
    (second P baseDepth p q).resource.left =
      executeAt (RelationalRealRuntime.sum P baseDepth) (second P baseDepth p q).resource.leftProbe.next
        (productBudget (second P baseDepth p q).resource.leftProbe.code
          (second P baseDepth p q).resource.rightProbe.code q).leftPrecision ∧
    (second P baseDepth p q).resource.right =
      executeAt (RelationalRealRuntime.sum P baseDepth) (second P baseDepth p q).resource.rightProbe.next
        (productBudget (second P baseDepth p q).resource.leftProbe.code
          (second P baseDepth p q).resource.rightProbe.code q).rightPrecision := ⟨rfl, rfl⟩

theorem crossBudget (p : Nat) :
    (productBudget (first P baseDepth p).resource.leftProbe.code
      (first P baseDepth p).resource.rightProbe.code p).leftPrecision =
        p + 1 + probeAmplitude (first P baseDepth p).resource.rightProbe.code ∧
    (productBudget (first P baseDepth p).resource.leftProbe.code
      (first P baseDepth p).resource.rightProbe.code p).rightPrecision =
        p + 1 + probeAmplitude (first P baseDepth p).resource.leftProbe.code := ⟨rfl, rfl⟩

theorem ownedRefinementsAreReceived (p : Nat) :
    (first P baseDepth p).resource.action.memory.continued.authorized.acted.searched.received.context =
      ((first P baseDepth p).resource.left, (first P baseDepth p).resource.right) :=
  (first P baseDepth p).resource.action.receivedContext_is_produced

theorem actionConsumesOwnedRefinements (p : Nat) :
    (first P baseDepth p).resource.action.action.operands =
      ((first P baseDepth p).resource.left, (first P baseDepth p).resource.right) := by
  rw [(first P baseDepth p).resource.action.action.operandsExact,
    (first P baseDepth p).resource.action.searchResult_is_receivedContextOutput,
    (first P baseDepth p).resource.action.receivedContext_is_produced]
  rfl

theorem installedSameTarget (p : Nat) :
    (first P baseDepth p).code = (first P baseDepth p).resource.action.action.code ∧
      (first P baseDepth p).next.last = some (first P baseDepth p).resource.action.action.code ∧
      (first P baseDepth p).liveEvent.code = (first P baseDepth p).resource.action.action.code :=
  multiplicationPacketSameTarget _

theorem twoApplicationsPerRole (p q : Nat) :
    (first P baseDepth p).next.left.retained.length = 2 ∧
      (first P baseDepth p).next.right.retained.length = 2 ∧
      (second P baseDepth p q).next.left.retained.length = 4 ∧
      (second P baseDepth p q).next.right.retained.length = 4 := ⟨rfl, rfl, rfl, rfl⟩

theorem journalContinues (p q : Nat) : (second P baseDepth p q).next.journal.absoluteDepth = baseDepth + 12 := by
  change (second P baseDepth p q).resource.action.completedJournal.absoluteDepth = _
  rw [(second P baseDepth p q).resource.action.completed_absoluteDepth]
  change (first P baseDepth p).resource.action.completedJournal.absoluteDepth + 6 = _
  rw [(first P baseDepth p).resource.action.completed_absoluteDepth]
  exact Nat.add_assoc baseDepth 6 6

theorem retainedChronologically (p q : Nat) :
    (second P baseDepth p q).next.retained = (first P baseDepth p).next.retained ++
      [⟨(first P baseDepth p).next.left, (first P baseDepth p).next.right,
        (first P baseDepth p).next.journal, q, (second P baseDepth p q).resource⟩] := rfl

theorem richEventOwnsArchive (p q : Nat) :
    (second P baseDepth p q).event.archive = (first P baseDepth p).next ∧
      (second P baseDepth p q).event.production = (second P baseDepth p q).resource := ⟨rfl, rfl⟩

theorem richEventsDiscriminateHistory (p : Nat) : (first P baseDepth p).event ≠ (second P baseDepth p p).event := by
  intro same
  have h := congrArg (fun event => event.archive.retained.length) same
  change 0 = 1 at h
  cases h

def valueNineSixteenths (p : Nat) : SameValue (readout (square P baseDepth) p) ⟨9, 0, 4⟩ := by
  change SameValue (readout (.mul (RelationalRealRuntime.sum P baseDepth) (RelationalRealRuntime.sum P baseDepth)) p) _
  rw [mul_readout_exact]
  exact SameValue.mul (RelationalRealRuntime.sumHasExpectedValue P baseDepth _)
    (RelationalRealRuntime.sumHasExpectedValue P baseDepth _)

def cancelled : SignedDyadicCode := ⟨10000, 10000, 0⟩
def cancelledSameZero : SameValue cancelled SignedDyadicCode.zero := ⟨⟨0, 0, 0, rfl, rfl⟩, rfl⟩
def cancellationAmplitude : Amplitude 1 cancelled := Amplitude.fromProbe (cancelledSameZero.toNear 0)
theorem fineComponentsNotBoundedByAmplitude : ¬ (cancelled.positive + cancelled.negative ≤ probeAmplitude SignedDyadicCode.zero) := by
  decide

def nonzeroProductError : Near 0 (SignedDyadicCode.zero.mul RelationalRealArithmetic.half)
    (RelationalRealArithmetic.half.mul RelationalRealArithmetic.half) :=
  RelationalRealArithmetic.halfError.mulRight
    (Amplitude.fromProbe ((RelationalRealArithmetic.halfError.weaken ⟨1, rfl⟩).symm))

def coherence (p q : Nat) : Near 0 (first P baseDepth p).code (second P baseDepth p q).code :=
  (coherent (square P baseDepth)).near 0 p q _ _ ⟨p, Nat.zero_add _⟩ ⟨q, Nat.zero_add _⟩
theorem currentReply (p q : Nat) : (second P baseDepth p q).code = readout (square P baseDepth) q := currentReadout _ _ _ _

theorem projectedFutures (p q : Nat) :
    projectOutcome (environment (square P baseDepth))
      (run (environment (square P baseDepth)) (environment (square P baseDepth)).initialArchive [p, q]).trace.outcome =
      (runLive (environment (square P baseDepth)).liveEnvironment
        ((environment (square P baseDepth)).project (environment (square P baseDepth)).initialArchive) [p, q]).outcome :=
  run_outcome_projects _ _ _

theorem fixedEnvironmentMinimality {a b : (environment (square P baseDepth)).Memory} :
    a = b ↔ ConstitutiveSearch.ContinuationSignatures.FutureEquivalent
      (liveContract (environment (square P baseDepth))) a b := liveMinimality _

def lawPackage := multiplicativeLaws P baseDepth
def futureLawPackage := multiplicativeFutureLaws P baseDepth
def associativity := RelationalRealAddition.mul_assoc (square P baseDepth) (.neg (square P baseDepth)) (one P baseDepth)
def distributivity := RelationalRealAddition.mul_add (square P baseDepth) (.neg (square P baseDepth)) (one P baseDepth)
def congruence := mul_congr (RelationalRealAddition.neg_neg (square P baseDepth)) (mul_one (square P baseDepth))
def futureEquivalence := (RelationalRealAddition.mul_comm (square P baseDepth) (.neg (square P baseDepth))).toFutures
def query (p : Nat) : RuntimeCorrespondence.LimitQuery (futureEquivalence P baseDepth).threshold :=
  ⟨p, (futureEquivalence P baseDepth).threshold p, (futureEquivalence P baseDepth).threshold p,
    PrecisionExtension.refl _, PrecisionExtension.refl _⟩
def pairedCurrentFutures := (futureEquivalence P baseDepth).traces
  (environment (.mul (square P baseDepth) (.neg (square P baseDepth)))).initialArchive
  (environment (.mul (.neg (square P baseDepth)) (square P baseDepth))).initialArchive
  [query P baseDepth 0, query P baseDepth 2]
def presentationTransport := toPresentation_mul (square P baseDepth) (.neg (square P baseDepth))
def carrierTransport := toCarrier_mul (square P baseDepth) (.neg (square P baseDepth))
def presentationRealization := realization_mul (toPresentation (square P baseDepth)) (toPresentation (square P baseDepth)) (P := P) (baseDepth := baseDepth)
def carrierRealization := realization_carrier_mul (toCarrier (square P baseDepth)) (toCarrier (square P baseDepth)) (P := P) (baseDepth := baseDepth)

end RelationalPerimeter.Tests.RelationalRealMultiplication

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Tests.RelationalRealMultiplication.square
#print axioms RelationalPerimeter.Tests.RelationalRealMultiplication.first
#print axioms RelationalPerimeter.Tests.RelationalRealMultiplication.second
#print axioms RelationalPerimeter.Tests.RelationalRealMultiplication.currentProbes
#print axioms RelationalPerimeter.Tests.RelationalRealMultiplication.exactProbeSuccessors
#print axioms RelationalPerimeter.Tests.RelationalRealMultiplication.crossBudget
#print axioms RelationalPerimeter.Tests.RelationalRealMultiplication.ownedRefinementsAreReceived
#print axioms RelationalPerimeter.Tests.RelationalRealMultiplication.actionConsumesOwnedRefinements
#print axioms RelationalPerimeter.Tests.RelationalRealMultiplication.installedSameTarget
#print axioms RelationalPerimeter.Tests.RelationalRealMultiplication.twoApplicationsPerRole
#print axioms RelationalPerimeter.Tests.RelationalRealMultiplication.journalContinues
#print axioms RelationalPerimeter.Tests.RelationalRealMultiplication.retainedChronologically
#print axioms RelationalPerimeter.Tests.RelationalRealMultiplication.richEventOwnsArchive
#print axioms RelationalPerimeter.Tests.RelationalRealMultiplication.richEventsDiscriminateHistory
#print axioms RelationalPerimeter.Tests.RelationalRealMultiplication.valueNineSixteenths
#print axioms RelationalPerimeter.Tests.RelationalRealMultiplication.cancelled
#print axioms RelationalPerimeter.Tests.RelationalRealMultiplication.cancelledSameZero
#print axioms RelationalPerimeter.Tests.RelationalRealMultiplication.cancellationAmplitude
#print axioms RelationalPerimeter.Tests.RelationalRealMultiplication.fineComponentsNotBoundedByAmplitude
#print axioms RelationalPerimeter.Tests.RelationalRealMultiplication.nonzeroProductError
#print axioms RelationalPerimeter.Tests.RelationalRealMultiplication.coherence
#print axioms RelationalPerimeter.Tests.RelationalRealMultiplication.currentReply
#print axioms RelationalPerimeter.Tests.RelationalRealMultiplication.projectedFutures
#print axioms RelationalPerimeter.Tests.RelationalRealMultiplication.fixedEnvironmentMinimality
#print axioms RelationalPerimeter.Tests.RelationalRealMultiplication.lawPackage
#print axioms RelationalPerimeter.Tests.RelationalRealMultiplication.futureLawPackage
#print axioms RelationalPerimeter.Tests.RelationalRealMultiplication.associativity
#print axioms RelationalPerimeter.Tests.RelationalRealMultiplication.distributivity
#print axioms RelationalPerimeter.Tests.RelationalRealMultiplication.congruence
#print axioms RelationalPerimeter.Tests.RelationalRealMultiplication.futureEquivalence
#print axioms RelationalPerimeter.Tests.RelationalRealMultiplication.query
#print axioms RelationalPerimeter.Tests.RelationalRealMultiplication.pairedCurrentFutures
#print axioms RelationalPerimeter.Tests.RelationalRealMultiplication.presentationTransport
#print axioms RelationalPerimeter.Tests.RelationalRealMultiplication.carrierTransport
#print axioms RelationalPerimeter.Tests.RelationalRealMultiplication.presentationRealization
#print axioms RelationalPerimeter.Tests.RelationalRealMultiplication.carrierRealization
/- AXIOM_AUDIT_END -/
