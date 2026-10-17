import Tests.RelationalRealOrder
import RelationalPerimeter.Constitution.Reals.RelationalRealInverse

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace RelationalPerimeter.Tests.RelationalRealInverseRaccord
open StrongPerimetralTurning
open RelationalPerimeter.Constitution.Reals
open RuntimeCorrespondence HeterogeneousRealRuntime RelationalRealAddition
open RelationalPerimeter.Constitution.Reals.RelationalRealOrder RelationalRealInverse DyadicReciprocal
variable (P : CircularPresentation) (depth : Nat)

def positiveDomain : Apartness (one P depth) (zero P depth) := .backward (RelationalRealOrder.unitPositive P depth)
def real : Real P depth := inverse (one P depth) (positiveDomain P depth)
def first (p : Nat) := executeReal (real P depth) p
def second (p q : Nat) := executeAt (real P depth) (first P depth p).next q
theorem exactSourceAnchor : (environment (real P depth)).initialArchive.source =
    (RelationalRealOrder.unitPositive P depth).pair.right.next := rfl
theorem firstOwnsProduced (p : Nat) : (first P depth p).resource.sourceStep =
    executeAt (one P depth) (ReciprocalDomain.sourceSuccessor (positiveDomain P depth))
      (sourcePrecision (ReciprocalDomain.away (positiveDomain P depth)) p) :=
  (first P depth p).resource.source_is_produced
theorem continuationOwnsCurrent (p q : Nat) : (second P depth p q).resource.sourceStep =
    executeAt (one P depth) (first P depth p).next.source
      (sourcePrecision (ReciprocalDomain.away (positiveDomain P depth)) q) :=
  (second P depth p q).resource.source_is_produced
theorem retainsExactWitness (p : Nat) : (first P depth p).resource.owned.origin = positiveDomain P depth :=
  (first P depth p).resource.owned.originExact
theorem exactActionOperand (p : Nat) : (first P depth p).resource.action.action.operand =
    (first P depth p).resource.operand := by
  rw [(first P depth p).resource.action.action.operandExact,
    (first P depth p).resource.action.searchResult_is_receivedContextOutput,
    (first P depth p).resource.action.receivedContext_is_produced]
  rfl
theorem sameInstalledTarget (p : Nat) :
    (first P depth p).code = (first P depth p).resource.action.action.result.code ∧
      (first P depth p).next.last = some (first P depth p).resource.action.action.result.code ∧
      (first P depth p).liveEvent.code = (first P depth p).resource.action.action.result.code := packetSameTarget _
theorem nonemptyHistory (p q : Nat) : (first P depth p).next.retained.length = 1 ∧
    (second P depth p q).next.retained.length = 2 := ⟨rfl, rfl⟩
theorem currentJournal (p q : Nat) : (second P depth p q).next.journal.absoluteDepth = depth + 12 := by
  change (second P depth p q).resource.action.completedJournal.absoluteDepth = _
  rw [(second P depth p q).resource.action.completed_absoluteDepth]
  change (first P depth p).resource.action.completedJournal.absoluteDepth + 6 = _
  rw [(first P depth p).resource.action.completed_absoluteDepth]
  exact Nat.add_assoc depth 6 6
theorem chronology (p q : Nat) : (second P depth p q).next.retained = (first P depth p).next.retained ++
    [⟨(first P depth p).next.source, (first P depth p).next.journal, q, (second P depth p q).resource⟩] := rfl
def coherence (p q : Nat) : Near 0 (first P depth p).code (second P depth p q).code :=
  (coherent (real P depth)).near 0 p q _ _ ⟨p, Nat.zero_add _⟩ ⟨q, Nat.zero_add _⟩
theorem uniformCurrent (p : Nat) : (second P depth p p).code = (first P depth p).code := currentReadout _ _ _ _
def negativeDomain : Apartness (.neg (RelationalRealRuntime.sum P depth)) (zero P depth) :=
  .forward (RelationalRealOrder.negativeWitness P depth)
def negativeInverse := inverse (.neg (RelationalRealRuntime.sum P depth)) (negativeDomain P depth)
def negativeFirst (p : Nat) := executeReal (negativeInverse P depth) p
def negativeSecond (p q : Nat) := executeAt (negativeInverse P depth) (negativeFirst P depth p).next q
def negativeCoherence (p q : Nat) : Near 0 (negativeFirst P depth p).code (negativeSecond P depth p q).code :=
  (coherent (negativeInverse P depth)).near 0 p q _ _ ⟨p, Nat.zero_add _⟩ ⟨q, Nat.zero_add _⟩
theorem liveProjection (p q : Nat) : projectOutcome (environment (real P depth))
    (run (environment (real P depth)) (environment (real P depth)).initialArchive [p, q]).trace.outcome =
    (runLive (environment (real P depth)).liveEnvironment
      ((environment (real P depth)).project (environment (real P depth)).initialArchive) [p, q]).outcome :=
  run_outcome_projects _ _ _
theorem fixedLiveMinimality {a b : (environment (real P depth)).Memory} : a = b ↔
    ConstitutiveSearch.ContinuationSignatures.FutureEquivalent (liveContract (environment (real P depth))) a b :=
  liveMinimality _
def cancelledPositive := computeReciprocal .positive (⟨10001, 10000, 0⟩ : SignedDyadicCode) 2 (by decide)
def cancelledNegative := computeReciprocal .negative (⟨10000, 10001, 0⟩ : SignedDyadicCode) 2 (by decide)
theorem cancelledResults : cancelledPositive.code = (⟨4, 0, 2⟩ : SignedDyadicCode) ∧
    cancelledNegative.code = (⟨0, 4, 2⟩ : SignedDyadicCode) := ⟨rfl, rfl⟩

end RelationalPerimeter.Tests.RelationalRealInverseRaccord

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Tests.RelationalRealInverseRaccord.positiveDomain
#print axioms RelationalPerimeter.Tests.RelationalRealInverseRaccord.real
#print axioms RelationalPerimeter.Tests.RelationalRealInverseRaccord.first
#print axioms RelationalPerimeter.Tests.RelationalRealInverseRaccord.second
#print axioms RelationalPerimeter.Tests.RelationalRealInverseRaccord.exactSourceAnchor
#print axioms RelationalPerimeter.Tests.RelationalRealInverseRaccord.firstOwnsProduced
#print axioms RelationalPerimeter.Tests.RelationalRealInverseRaccord.continuationOwnsCurrent
#print axioms RelationalPerimeter.Tests.RelationalRealInverseRaccord.retainsExactWitness
#print axioms RelationalPerimeter.Tests.RelationalRealInverseRaccord.exactActionOperand
#print axioms RelationalPerimeter.Tests.RelationalRealInverseRaccord.sameInstalledTarget
#print axioms RelationalPerimeter.Tests.RelationalRealInverseRaccord.nonemptyHistory
#print axioms RelationalPerimeter.Tests.RelationalRealInverseRaccord.currentJournal
#print axioms RelationalPerimeter.Tests.RelationalRealInverseRaccord.chronology
#print axioms RelationalPerimeter.Tests.RelationalRealInverseRaccord.coherence
#print axioms RelationalPerimeter.Tests.RelationalRealInverseRaccord.uniformCurrent
#print axioms RelationalPerimeter.Tests.RelationalRealInverseRaccord.negativeDomain
#print axioms RelationalPerimeter.Tests.RelationalRealInverseRaccord.negativeInverse
#print axioms RelationalPerimeter.Tests.RelationalRealInverseRaccord.negativeFirst
#print axioms RelationalPerimeter.Tests.RelationalRealInverseRaccord.negativeSecond
#print axioms RelationalPerimeter.Tests.RelationalRealInverseRaccord.negativeCoherence
#print axioms RelationalPerimeter.Tests.RelationalRealInverseRaccord.liveProjection
#print axioms RelationalPerimeter.Tests.RelationalRealInverseRaccord.fixedLiveMinimality
#print axioms RelationalPerimeter.Tests.RelationalRealInverseRaccord.cancelledPositive
#print axioms RelationalPerimeter.Tests.RelationalRealInverseRaccord.cancelledNegative
#print axioms RelationalPerimeter.Tests.RelationalRealInverseRaccord.cancelledResults
/- AXIOM_AUDIT_END -/
