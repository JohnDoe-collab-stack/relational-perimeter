import Tests.RelationalRealCauchy
import RelationalPerimeter.Constitution.Reals.RelationalRealLimitUniqueness

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace RelationalPerimeter.Tests.RelationalRealLimitUniqueness
open StrongPerimetralTurning
open RelationalPerimeter.Constitution.Reals
open ProducedCompleteness RuntimeCorrespondence HeterogeneousRealRuntime RelationalRealAddition RelationalRealCauchy
open RelationalPerimeter.Constitution.Reals.RelationalRealLimitUniqueness

variable {P : CircularPresentation} {depth : Nat} (family : ExecutedCauchyFamily P depth)

/-- Different Real constructor, exactly the existing authoritative service. -/
def leafCertificate : CertifiedService P depth where
  service := environment (limitReal family)
  coherence := coherent (limitReal family)
  uniform archive p step := currentReadout (limitReal family) archive p step

def certifiedCandidate : LimitCandidate family where
  real := .certified (leafCertificate family)
  threshold := fun p => p
  converges := termLimitNear family

def firstCandidate := authoritative family
def firstPrevious := executeReal (firstCandidate family).real 1
def secondPrevious := executeReal (certifiedCandidate family).real 2
def termArchive := (RelationalRealCauchy.second family).next

def firstQuery : LimitQuery (uniquenessThreshold (firstCandidate family) (certifiedCandidate family)) :=
  ⟨0, 2, 3, .refl _, ⟨1, rfl⟩⟩
def secondQuery : LimitQuery (uniquenessThreshold (firstCandidate family) (certifiedCandidate family)) :=
  ⟨2, 7, 8, ⟨1, rfl⟩, ⟨2, rfl⟩⟩

def head := mediate (firstCandidate family) (certifiedCandidate family) (termArchive family)
  (firstPrevious family).next (secondPrevious family).next (firstQuery family)
def next := mediate (firstCandidate family) (certifiedCandidate family)
  (head family).termStep.next (head family).firstStep.next (head family).secondStep.next (secondQuery family)
def rich := produceTrace (firstCandidate family) (certifiedCandidate family) (termArchive family)
  (firstPrevious family).next (secondPrevious family).next [firstQuery family, secondQuery family]

theorem ownsArchives : (head family).archives =
    ⟨termArchive family, (firstPrevious family).next, (secondPrevious family).next⟩ :=
  (head family).archivesExact

theorem producedTerm : (head family).termStep = executeAt (termReal family (family.modulus 1))
    (termArchive family) 1 := (head family).termExact
theorem producedFirst : (head family).firstStep = executeAt (firstCandidate family).real
    (firstPrevious family).next 2 := (head family).firstExact
theorem producedSecond : (head family).secondStep = executeAt (certifiedCandidate family).real
    (secondPrevious family).next 3 := (head family).secondExact

theorem firstUsesSharedTerm : (head family).firstNear = (firstCandidate family).converges 1
    (family.modulus 1) 1 2 (head family).termStep (head family).firstStep
    (.refl _) (.refl _) (firstExtension _ _ (firstQuery family)) := (head family).firstNearExact
theorem secondUsesSharedTerm : (head family).secondNear = (certifiedCandidate family).converges 1
    (family.modulus 1) 1 3 (head family).termStep (head family).secondStep
    (.refl _) (.refl _) (secondExtension _ _ (firstQuery family)) := (head family).secondNearExact
theorem compositionStored : (head family).near =
    Near.compose (head family).firstNear.symm (head family).secondNear := (head family).nearExact

theorem continuesThree : (next family).archives =
    ⟨(head family).termStep.next, (head family).firstStep.next, (head family).secondStep.next⟩ :=
  (next family).archivesExact
theorem termChangesIndexButContinues : (next family).termStep =
    executeAt (termReal family (family.modulus 3)) (head family).termStep.next 3 := (next family).termExact

theorem richOwnsBoth : rich family = .step (head family)
    (.step (next family) (.done (next family).termStep.next (next family).firstStep.next (next family).secondStep.next)) := rfl
theorem richLength : (rich family).length = 2 := produceTrace_length _ _ _ _ _ _
theorem finalThree : (rich family).final =
    ⟨(next family).termStep.next, (next family).firstStep.next, (next family).secondStep.next⟩ := rfl

def projected := (rich family).toNumerical
theorem projectionReusesPackets : projected family =
    .step (head family).firstStep (head family).secondStep (head family).firstExact (head family).secondExact
      (head family).near
      (.step (next family).firstStep (next family).secondStep (next family).firstExact (next family).secondExact
        (next family).near (.done (next family).firstStep.next (next family).secondStep.next)) := rfl

theorem termJournalContinues : (head family).termStep.next.state.journal.absoluteDepth =
    (termArchive family).state.journal.absoluteDepth + 6 :=
  (head family).termStep.resource.execution.completed_absoluteDepth
theorem firstJournalContinues : (head family).firstStep.next.state.journal.absoluteDepth =
    (firstPrevious family).next.state.journal.absoluteDepth + 12 :=
  (head family).firstStep.resource.response.limit_depth
theorem secondJournalContinues : (head family).secondStep.next.state.journal.absoluteDepth =
    (secondPrevious family).next.state.journal.absoluteDepth + 12 :=
  (head family).secondStep.resource.response.limit_depth

def syntaxDistinct : (firstCandidate family).real = (certifiedCandidate family).real → Empty := by
  intro impossible
  cases impossible

def terminal := unique (firstCandidate family) (certifiedCandidate family)
def authoritativeAgainstCertified := authoritativeUnique (certifiedCandidate family)
def arbitraryHistories (first second : LimitCandidate family)
    (a : (environment first.real).Archive) (b : (environment second.real).Archive)
    (queries : List (LimitQuery (uniquenessThreshold first second))) :=
  (numericalFutures first second).traces a b queries
def currentFuture := (terminal family).2.traces
  (firstPrevious family).next (secondPrevious family).next [firstQuery family, secondQuery family]

def concrete := rich RelationalSequentialCompleteness.producedConstantFamily
theorem concreteIndices : RelationalSequentialCompleteness.producedConstantFamily.modulus 1 = 1 ∧
    RelationalSequentialCompleteness.producedConstantFamily.modulus 3 = 3 := ⟨rfl, rfl⟩

end RelationalPerimeter.Tests.RelationalRealLimitUniqueness

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Tests.RelationalRealLimitUniqueness.leafCertificate
#print axioms RelationalPerimeter.Tests.RelationalRealLimitUniqueness.certifiedCandidate
#print axioms RelationalPerimeter.Tests.RelationalRealLimitUniqueness.firstCandidate
#print axioms RelationalPerimeter.Tests.RelationalRealLimitUniqueness.firstPrevious
#print axioms RelationalPerimeter.Tests.RelationalRealLimitUniqueness.secondPrevious
#print axioms RelationalPerimeter.Tests.RelationalRealLimitUniqueness.termArchive
#print axioms RelationalPerimeter.Tests.RelationalRealLimitUniqueness.firstQuery
#print axioms RelationalPerimeter.Tests.RelationalRealLimitUniqueness.secondQuery
#print axioms RelationalPerimeter.Tests.RelationalRealLimitUniqueness.head
#print axioms RelationalPerimeter.Tests.RelationalRealLimitUniqueness.next
#print axioms RelationalPerimeter.Tests.RelationalRealLimitUniqueness.rich
#print axioms RelationalPerimeter.Tests.RelationalRealLimitUniqueness.ownsArchives
#print axioms RelationalPerimeter.Tests.RelationalRealLimitUniqueness.producedTerm
#print axioms RelationalPerimeter.Tests.RelationalRealLimitUniqueness.producedFirst
#print axioms RelationalPerimeter.Tests.RelationalRealLimitUniqueness.producedSecond
#print axioms RelationalPerimeter.Tests.RelationalRealLimitUniqueness.firstUsesSharedTerm
#print axioms RelationalPerimeter.Tests.RelationalRealLimitUniqueness.secondUsesSharedTerm
#print axioms RelationalPerimeter.Tests.RelationalRealLimitUniqueness.compositionStored
#print axioms RelationalPerimeter.Tests.RelationalRealLimitUniqueness.continuesThree
#print axioms RelationalPerimeter.Tests.RelationalRealLimitUniqueness.termChangesIndexButContinues
#print axioms RelationalPerimeter.Tests.RelationalRealLimitUniqueness.richOwnsBoth
#print axioms RelationalPerimeter.Tests.RelationalRealLimitUniqueness.richLength
#print axioms RelationalPerimeter.Tests.RelationalRealLimitUniqueness.finalThree
#print axioms RelationalPerimeter.Tests.RelationalRealLimitUniqueness.projected
#print axioms RelationalPerimeter.Tests.RelationalRealLimitUniqueness.projectionReusesPackets
#print axioms RelationalPerimeter.Tests.RelationalRealLimitUniqueness.termJournalContinues
#print axioms RelationalPerimeter.Tests.RelationalRealLimitUniqueness.firstJournalContinues
#print axioms RelationalPerimeter.Tests.RelationalRealLimitUniqueness.secondJournalContinues
#print axioms RelationalPerimeter.Tests.RelationalRealLimitUniqueness.syntaxDistinct
#print axioms RelationalPerimeter.Tests.RelationalRealLimitUniqueness.terminal
#print axioms RelationalPerimeter.Tests.RelationalRealLimitUniqueness.authoritativeAgainstCertified
#print axioms RelationalPerimeter.Tests.RelationalRealLimitUniqueness.arbitraryHistories
#print axioms RelationalPerimeter.Tests.RelationalRealLimitUniqueness.currentFuture
#print axioms RelationalPerimeter.Tests.RelationalRealLimitUniqueness.concrete
#print axioms RelationalPerimeter.Tests.RelationalRealLimitUniqueness.concreteIndices
/- AXIOM_AUDIT_END -/
