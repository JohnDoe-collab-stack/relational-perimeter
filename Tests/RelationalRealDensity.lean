import Tests.RelationalRealOrderedField
import RelationalPerimeter.Constitution.Reals.RelationalRealDensity

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace RelationalPerimeter.Tests.RelationalRealDensity
open StrongPerimetralTurning
open RelationalPerimeter.Constitution.Reals
open RuntimeCorrespondence HeterogeneousRealRuntime RelationalRealAddition RelationalRealOrder ConstitutiveRuntime
open RelationalPerimeter.Constitution.Reals.RelationalRealDensity DyadicDensity
variable (P : CircularPresentation) (depth : Nat)

def origin := RelationalRealOrderedField.translatedOrder P depth
def journal := (RelationalRealOrderedField.translated P depth).attempt.pair.left.resource.action.completedJournal
def density := produceDensity (origin P depth) (journal P depth)
def densityOrders := (density P depth).orders

theorem receivesOwnedWitness : (density P depth).action.memory.continued.authorized.acted.searched.received.context.value =
    origin P depth := densityReceivesWitness (density P depth).action

theorem densityTargetFromStored : (density P depth).target = dyadic P depth (density P depth).action.readout :=
  (density P depth).targetExact

theorem densityStoredSame : (density P depth).action.stored.value = (density P depth).action.action :=
  (density P depth).action.stored.exact

theorem sourceContinues : (density P depth).left.pair.left = executeAt (RelationalRealOrderedField.aliasLeft P depth)
    (origin P depth).pair.left.next ((origin P depth).accuracy + 6) := rfl

theorem targetReused : (density P depth).right.pair.left = executeAt (density P depth).target
    (density P depth).left.pair.right.next ((origin P depth).accuracy + 6) := rfl

theorem secondSourceContinues : (density P depth).right.pair.right = executeAt (RelationalRealOrderedField.shiftedRight P depth)
    (origin P depth).pair.right.next ((origin P depth).accuracy + 6) := rfl

theorem densityJournalContinues : (density P depth).action.completedJournal.relativeDepth =
    (journal P depth).relativeDepth + 6 := rfl

def densityAgain := produceDensity (origin P depth) (density P depth).action.completedJournal
theorem secondJournal : (densityAgain P depth).action.completedJournal.relativeDepth =
    (density P depth).action.completedJournal.relativeDepth + 6 := rfl

def densityPresentationLeft := (densityOrders P depth).1.toPresentation
def densityCarrierRight := (densityOrders P depth).2.toCarrier
def targetFirstLive := performRuntime (initialReal (density P depth).target).live 1
def targetSecondLive := performRuntime (targetFirstLive P depth).next 4

def bounds := produceNaturalBound (RelationalRealOrderedField.aliasLeft P depth)
  (origin P depth).pair.left.next (density P depth).action.completedJournal
def boundOrders := (bounds P depth).orders

theorem currentProbe : (bounds P depth).probe = executeAt (RelationalRealOrderedField.aliasLeft P depth)
    (origin P depth).pair.left.next 2 := rfl

theorem lowerContinuesProbe : (bounds P depth).lower.pair.right = executeAt (RelationalRealOrderedField.aliasLeft P depth)
    (bounds P depth).probe.next 5 := rfl

theorem upperContinuesLower : (bounds P depth).upper.pair.left = executeAt (RelationalRealOrderedField.aliasLeft P depth)
    (bounds P depth).lower.pair.right.next 5 := rfl

theorem boundsStoredSame : (bounds P depth).action.stored.value = (bounds P depth).action.action :=
  (bounds P depth).action.stored.exact

theorem upperNaturalFromProbe : (bounds P depth).action.stored.value.upper = (bounds P depth).probe.code.positive + 2 :=
  (bounds P depth).action.stored.value.upperExact
theorem lowerNaturalFromProbe : (bounds P depth).action.stored.value.lower = (bounds P depth).probe.code.negative + 2 :=
  (bounds P depth).action.stored.value.lowerExact

theorem upperRuntimeFromStored : (bounds P depth).upperTarget =
    dyadic P depth (naturalCode (bounds P depth).action.stored.value.upper) := (bounds P depth).upperExact
theorem lowerRuntimeFromStored : (bounds P depth).lowerTarget =
    dyadic P depth (negativeNaturalCode (bounds P depth).action.stored.value.lower) := (bounds P depth).lowerExact

theorem boundsJournalContinues : (bounds P depth).action.completedJournal.relativeDepth =
    (density P depth).action.completedJournal.relativeDepth + 6 := rfl

def negativeBounds := archimedean (.neg (RelationalRealOrderedField.sum P depth))
def cancelledBounds := archimedean (RelationalRealInverse.cancelled P depth)
def zeroBounds := archimedean (zero P depth)
def oneBounds := archimedean (one P depth)
def boundsPresentationUpper := (boundOrders P depth).2.toPresentation
def boundsCarrierLower := (boundOrders P depth).1.toCarrier

def halfUnit := bisect RelationalRealOrder.unitMargin
theorem halfUnitExact : halfUnit.code = ⟨2, 0, 2⟩ := rfl

def cancelledGap : StrictSeparation 1 (⟨200, 200, 3⟩ : SignedDyadicCode) ⟨1001, 1000, 0⟩ :=
  ⟨⟨4, 1, 4, rfl, rfl⟩, 3, rfl, by decide⟩
def cancelledMidpoint := bisect cancelledGap
def cancelledMargins := (cancelledMidpoint.leftMargin, cancelledMidpoint.rightMargin)

end RelationalPerimeter.Tests.RelationalRealDensity

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Tests.RelationalRealDensity.origin
#print axioms RelationalPerimeter.Tests.RelationalRealDensity.journal
#print axioms RelationalPerimeter.Tests.RelationalRealDensity.density
#print axioms RelationalPerimeter.Tests.RelationalRealDensity.densityOrders
#print axioms RelationalPerimeter.Tests.RelationalRealDensity.receivesOwnedWitness
#print axioms RelationalPerimeter.Tests.RelationalRealDensity.densityTargetFromStored
#print axioms RelationalPerimeter.Tests.RelationalRealDensity.densityStoredSame
#print axioms RelationalPerimeter.Tests.RelationalRealDensity.sourceContinues
#print axioms RelationalPerimeter.Tests.RelationalRealDensity.targetReused
#print axioms RelationalPerimeter.Tests.RelationalRealDensity.secondSourceContinues
#print axioms RelationalPerimeter.Tests.RelationalRealDensity.densityJournalContinues
#print axioms RelationalPerimeter.Tests.RelationalRealDensity.densityAgain
#print axioms RelationalPerimeter.Tests.RelationalRealDensity.secondJournal
#print axioms RelationalPerimeter.Tests.RelationalRealDensity.densityPresentationLeft
#print axioms RelationalPerimeter.Tests.RelationalRealDensity.densityCarrierRight
#print axioms RelationalPerimeter.Tests.RelationalRealDensity.targetFirstLive
#print axioms RelationalPerimeter.Tests.RelationalRealDensity.targetSecondLive
#print axioms RelationalPerimeter.Tests.RelationalRealDensity.bounds
#print axioms RelationalPerimeter.Tests.RelationalRealDensity.boundOrders
#print axioms RelationalPerimeter.Tests.RelationalRealDensity.currentProbe
#print axioms RelationalPerimeter.Tests.RelationalRealDensity.lowerContinuesProbe
#print axioms RelationalPerimeter.Tests.RelationalRealDensity.upperContinuesLower
#print axioms RelationalPerimeter.Tests.RelationalRealDensity.boundsStoredSame
#print axioms RelationalPerimeter.Tests.RelationalRealDensity.upperNaturalFromProbe
#print axioms RelationalPerimeter.Tests.RelationalRealDensity.lowerNaturalFromProbe
#print axioms RelationalPerimeter.Tests.RelationalRealDensity.upperRuntimeFromStored
#print axioms RelationalPerimeter.Tests.RelationalRealDensity.lowerRuntimeFromStored
#print axioms RelationalPerimeter.Tests.RelationalRealDensity.boundsJournalContinues
#print axioms RelationalPerimeter.Tests.RelationalRealDensity.negativeBounds
#print axioms RelationalPerimeter.Tests.RelationalRealDensity.cancelledBounds
#print axioms RelationalPerimeter.Tests.RelationalRealDensity.zeroBounds
#print axioms RelationalPerimeter.Tests.RelationalRealDensity.oneBounds
#print axioms RelationalPerimeter.Tests.RelationalRealDensity.boundsPresentationUpper
#print axioms RelationalPerimeter.Tests.RelationalRealDensity.boundsCarrierLower
#print axioms RelationalPerimeter.Tests.RelationalRealDensity.halfUnit
#print axioms RelationalPerimeter.Tests.RelationalRealDensity.halfUnitExact
#print axioms RelationalPerimeter.Tests.RelationalRealDensity.cancelledGap
#print axioms RelationalPerimeter.Tests.RelationalRealDensity.cancelledMidpoint
#print axioms RelationalPerimeter.Tests.RelationalRealDensity.cancelledMargins
/- AXIOM_AUDIT_END -/
