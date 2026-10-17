import RelationalPerimeter.Constitution.Reals.RelationalRealCauchy
import Tests.RelationalSequentialCompleteness

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace RelationalPerimeter.Tests.RelationalRealCauchy
open StrongPerimetralTurning
open RelationalPerimeter.Constitution.Reals
open ConstitutiveRuntime ProducedCompleteness RuntimeCorrespondence HeterogeneousRealRuntime RelationalRealAddition
open RelationalPerimeter.Constitution.Reals.RelationalRealCauchy
open ConstitutiveSearch.ContinuationSignatures

variable {P : CircularPresentation} {depth : Nat} (family : ExecutedCauchyFamily P depth)

def first := executeReal (termReal family (family.modulus 2)) 3
def second := executeAt (termReal family (family.modulus 2)) (first family).next 5
def later := executeAt (termReal family (family.modulus 2 + 1)) (second family).next 6
def limit := executeAt (limitReal family) (later family).next 7
def limitAgain := executeAt (limitReal family) (limit family).next 8

theorem currentRawSource : (second family).resource.execution =
    execute (sourceProgram family.producer) P (first family).next.state.journal
      { term := family.modulus 2, precision := 5 } := rfl

theorem preservesReachability : (second family).next.reachable =
    AuthoritativeRuntime.Reachable.rawSource (first family).next.reachable (second family).resource := rfl

theorem retainsRawExecution : (second family).next.state.memory =
    (first family).next.state.memory ++ [.rawSource (second family).resource.execution] := rfl

theorem currentJournal : (second family).next.state.journal =
    (second family).resource.execution.completedJournal := rfl

theorem termDepth : (second family).next.state.journal.absoluteDepth =
    (first family).next.state.journal.absoluteDepth + 6 :=
  (second family).resource.execution.completed_absoluteDepth

theorem limitDepth : (limit family).next.state.journal.absoluteDepth =
    (later family).next.state.journal.absoluteDepth + 12 :=
  (limit family).resource.response.limit_depth

theorem limitAgainDepth : (limitAgain family).next.state.journal.absoluteDepth =
    (limit family).next.state.journal.absoluteDepth + 12 :=
  (limitAgain family).resource.response.limit_depth

theorem sourceActionShared : (second family).code =
    (sourceProgram family.producer).actionCode (second family).resource.execution.action :=
  (second family).resource.execution.readout_is_storedAction

theorem richEventOwnsCurrent : (second family).event.archive = (first family).next ∧
    (second family).event.resource = (second family).resource := ⟨rfl, rfl⟩

theorem termProjection : (environment (termReal family (family.modulus 2))).project (second family).next =
    ((environment (termReal family (family.modulus 2))).liveStep
      ((environment (termReal family (family.modulus 2))).project (first family).next) 5).next :=
  (second family).nextProjection

theorem termEventProjection : (second family).liveEvent =
    ((environment (termReal family (family.modulus 2))).liveStep
      ((environment (termReal family (family.modulus 2))).project (first family).next) 5).event :=
  (second family).eventProjection

theorem termAnswerProjection : (environment (termReal family (family.modulus 2))).answer (second family).liveEvent =
    (second family).code := (second family).answerProjection

def currentCoherence : Near 2 (first family).code (second family).code :=
  (coherent (termReal family (family.modulus 2))).near 2 3 5
    (first family) (second family) ⟨1, rfl⟩ ⟨3, rfl⟩

def currentCauchy : Near 2 (second family).code (later family).code :=
  termsCauchy family 2 (family.modulus 2) (family.modulus 2 + 1) 5 6
    (second family) (later family) (.refl _) ⟨1, rfl⟩ ⟨3, rfl⟩ ⟨4, rfl⟩

def currentConvergence : Near 2 (later family).code (limit family).code :=
  termLimitNear family 2 (family.modulus 2 + 1) 6 7 (later family) (limit family)
    ⟨1, rfl⟩ ⟨4, rfl⟩ ⟨5, rfl⟩

theorem receivedLimitSource : (limit family).resource.response.limitProduction.source.execution =
    execute (sourceProgram family.producer) P (later family).next.state.journal
      (family.diagonalSourceAt 7).request := rfl

theorem receivedGrouping : (limit family).resource.response.limitProduction.execution =
    execute (LimitGrouping.program (limit family).resource.response.limitProduction.source) P
      (limit family).resource.response.limitProduction.source.completedJournal () := rfl

theorem limitInstallsOwnedTarget : (limit family).next.state.target =
    some (.limit (limit family).resource.response.limitProduction) := rfl

theorem limitStoresOwnedProduction : (limit family).next.state.memory =
    (later family).next.state.memory ++ [.limit (limit family).resource.response.limitProduction] := rfl

theorem limitReadoutFromOwnedAction : (limit family).code =
    (limit family).resource.response.limitProduction.execution.action.target.code :=
  (limitStepReadout (limit family)).trans
    (limit family).resource.response.limitProduction.readout_is_targetCode

def normalizedWitness := (limit family).resource.response.limitProduction.sourceNearTarget

theorem normalizedWitnessPreserved :
    HEq (limit family).resource.response.limitProduction.execution.action.consumedNearProduced
      (limit family).resource.response.limitProduction.execution.action.target.normalized.consumedNearTarget :=
  (limit family).resource.response.limitProduction.execution.action.consumedNearProduced_is_normalized

def samePrecision := executeAt (termReal family (family.modulus 2)) (second family).next 3
theorem uniformCurrent : (first family).code = (samePrecision family).code :=
  termUniform family (family.modulus 2) (first family) (samePrecision family)

def termLiveFirst := performRuntime (initialReal (termReal family (family.modulus 2))).live 3
def termLiveSecond := performRuntime (termLiveFirst family).next 5

def richFuture := run (environment (termReal family (family.modulus 2))) (first family).next [5, 7]

theorem richFutureProjects : projectOutcome (environment (termReal family (family.modulus 2)))
    (richFuture family).trace.outcome =
      (runLive (environment (termReal family (family.modulus 2))).liveEnvironment
        ((environment (termReal family (family.modulus 2))).project (first family).next) [5, 7]).outcome :=
  run_outcome_projects _ _ _

theorem minimalityAtFixedTerm {firstMemory secondMemory : AuthoritativeRuntime.ReducedState} :
    firstMemory = secondMemory ↔ FutureEquivalent (liveContract (termEnvironment family (family.modulus 2)))
      firstMemory secondMemory := liveMinimality (termEnvironment family (family.modulus 2))

def packet := internalCompleteness family
def packetCauchy := (packet family).cauchy 2 (family.modulus 2) (family.modulus 2 + 1) 5 6
  (second family) (later family) (.refl _) ⟨1, rfl⟩ ⟨3, rfl⟩ ⟨4, rfl⟩
def packetConvergence := (packet family).converges 2 (family.modulus 2 + 1) 6 7
  (later family) (limit family) ⟨1, rfl⟩ ⟨4, rfl⟩ ⟨5, rfl⟩

def composed := executeReal (.add (termReal family 0) (.mul (limitReal family) (termReal family 1))) 2

/-- Reuse the existing concrete executed-family fixture, not another production master. -/
def concrete := currentConvergence RelationalSequentialCompleteness.producedConstantFamily

end RelationalPerimeter.Tests.RelationalRealCauchy

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Tests.RelationalRealCauchy.first
#print axioms RelationalPerimeter.Tests.RelationalRealCauchy.second
#print axioms RelationalPerimeter.Tests.RelationalRealCauchy.later
#print axioms RelationalPerimeter.Tests.RelationalRealCauchy.limit
#print axioms RelationalPerimeter.Tests.RelationalRealCauchy.limitAgain
#print axioms RelationalPerimeter.Tests.RelationalRealCauchy.currentRawSource
#print axioms RelationalPerimeter.Tests.RelationalRealCauchy.preservesReachability
#print axioms RelationalPerimeter.Tests.RelationalRealCauchy.retainsRawExecution
#print axioms RelationalPerimeter.Tests.RelationalRealCauchy.currentJournal
#print axioms RelationalPerimeter.Tests.RelationalRealCauchy.termDepth
#print axioms RelationalPerimeter.Tests.RelationalRealCauchy.limitDepth
#print axioms RelationalPerimeter.Tests.RelationalRealCauchy.limitAgainDepth
#print axioms RelationalPerimeter.Tests.RelationalRealCauchy.sourceActionShared
#print axioms RelationalPerimeter.Tests.RelationalRealCauchy.richEventOwnsCurrent
#print axioms RelationalPerimeter.Tests.RelationalRealCauchy.termProjection
#print axioms RelationalPerimeter.Tests.RelationalRealCauchy.termEventProjection
#print axioms RelationalPerimeter.Tests.RelationalRealCauchy.termAnswerProjection
#print axioms RelationalPerimeter.Tests.RelationalRealCauchy.currentCoherence
#print axioms RelationalPerimeter.Tests.RelationalRealCauchy.currentCauchy
#print axioms RelationalPerimeter.Tests.RelationalRealCauchy.currentConvergence
#print axioms RelationalPerimeter.Tests.RelationalRealCauchy.receivedLimitSource
#print axioms RelationalPerimeter.Tests.RelationalRealCauchy.receivedGrouping
#print axioms RelationalPerimeter.Tests.RelationalRealCauchy.limitInstallsOwnedTarget
#print axioms RelationalPerimeter.Tests.RelationalRealCauchy.limitStoresOwnedProduction
#print axioms RelationalPerimeter.Tests.RelationalRealCauchy.limitReadoutFromOwnedAction
#print axioms RelationalPerimeter.Tests.RelationalRealCauchy.normalizedWitness
#print axioms RelationalPerimeter.Tests.RelationalRealCauchy.normalizedWitnessPreserved
#print axioms RelationalPerimeter.Tests.RelationalRealCauchy.samePrecision
#print axioms RelationalPerimeter.Tests.RelationalRealCauchy.uniformCurrent
#print axioms RelationalPerimeter.Tests.RelationalRealCauchy.termLiveFirst
#print axioms RelationalPerimeter.Tests.RelationalRealCauchy.termLiveSecond
#print axioms RelationalPerimeter.Tests.RelationalRealCauchy.richFuture
#print axioms RelationalPerimeter.Tests.RelationalRealCauchy.richFutureProjects
#print axioms RelationalPerimeter.Tests.RelationalRealCauchy.minimalityAtFixedTerm
#print axioms RelationalPerimeter.Tests.RelationalRealCauchy.packet
#print axioms RelationalPerimeter.Tests.RelationalRealCauchy.packetCauchy
#print axioms RelationalPerimeter.Tests.RelationalRealCauchy.packetConvergence
#print axioms RelationalPerimeter.Tests.RelationalRealCauchy.composed
#print axioms RelationalPerimeter.Tests.RelationalRealCauchy.concrete
/- AXIOM_AUDIT_END -/
