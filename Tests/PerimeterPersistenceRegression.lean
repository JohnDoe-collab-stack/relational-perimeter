import RelationalPerimeter

/-! Integration consumers of the existing producer, the operational residual,
and the completed readout surface. The closed checks follow actual generated
and concretely realized occurrences through several successive stages. -/
set_option genInjectivity false

namespace Tests.PerimeterPersistenceRegression
open StrongPerimetralTurning
open ConstitutiveSearch.PerimeterPersistence
open ConstitutiveSearch.OccurrencePersistence

theorem sameProducedHistory (P : CircularPresentation) (depth : Nat) :
    Iterated.iteratedHistory P depth =
      ConstitutiveSearch.ConstitutiveGeneration.iteratedHistory P depth := rfl

theorem nativeSuccessorSplit (P : CircularPresentation) (depth : Nat)
    (old : History.Occurrence
      (ConstitutiveSearch.ConstitutiveGeneration.iteratedHistory P depth).history) :
    (Iterated.successorOccurrenceSplit P depth).forward (.inl old) =
      History.Occurrence.earlier old :=
  ConstitutiveSearch.ConstitutiveGeneration.successorOccurrenceSplit_old P depth old

theorem sameConsumedResidual (P : CircularPresentation) :
    (canonicalConstitutiveAlignment P).fresh =
      (oneStepFaithfullyLabelledExtension P).newOccurrence
        (abstractTurningOfCircularPresentation P).uniqueResidualOccurrence.occurrence :=
  oneStepAlignmentFreshIsConsumedResidual P

private abbrev P := Example.examplePresentation
private abbrev A := Example.exampleConcreteAlgebra

def readoutAtThree :=
  (finiteConstitutivePersistenceRealization P A 3).realizeReadout
    (iteratedReadout (fun _ : OneStep.InitialFreeOccurrence P => 5)
      (((PUnit.unit, 10), 20), 30))

def retainedResidual :=
  (finiteConstitutivePersistenceRealization P A 1).extend
    (finiteConstitutivePersistenceRealization P A 3)
    (.step (.step (.refl 1))) (OneStep.oneStepResidualConcreteOccurrence P A)

def retainedSecondFresh :=
  (finiteConstitutivePersistenceRealization P A 2).extend
    (finiteConstitutivePersistenceRealization P A 3) (.step (.refl 2))
    ((finiteConstitutivePersistenceRealization P A 2).indexedSpoke.forward
      (IteratedCarrier.freshAtStep 1))

def thirdFresh :=
  (finiteConstitutivePersistenceRealization P A 3).indexedSpoke.forward
    (IteratedCarrier.freshAtStep 2)

theorem residualKeepsItsValue : readoutAtThree retainedResidual = 10 := rfl
theorem secondFreshKeepsItsValue : readoutAtThree retainedSecondFresh = 20 := rfl
theorem thirdFreshHasItsOwnValue : readoutAtThree thirdFresh = 30 := rfl

theorem retainedOccurrencesStayDistinct : retainedSecondFresh ≠ thirdFresh := by
  intro same
  have values := congrArg readoutAtThree same
  change 20 = 30 at values
  exact (by decide : (20 : Nat) ≠ 30) values

theorem readoutRoundTrip (value : NonClosingPosition P.perimeter → Nat)
    (position : NonClosingPosition P.perimeter) :
    (exactReadoutBus P A).toPerimeterReadout
      ((exactReadoutBus P A).toConcreteReadout value) position = value position :=
  ExactReadoutBus.toPerimeterReadout_toConcreteReadout (exactReadoutBus P A) value position

end Tests.PerimeterPersistenceRegression

/- AXIOM_AUDIT_BEGIN -/
#print axioms Tests.PerimeterPersistenceRegression.sameProducedHistory
#print axioms Tests.PerimeterPersistenceRegression.nativeSuccessorSplit
#print axioms Tests.PerimeterPersistenceRegression.sameConsumedResidual
#print axioms Tests.PerimeterPersistenceRegression.readoutAtThree
#print axioms Tests.PerimeterPersistenceRegression.retainedResidual
#print axioms Tests.PerimeterPersistenceRegression.retainedSecondFresh
#print axioms Tests.PerimeterPersistenceRegression.thirdFresh
#print axioms Tests.PerimeterPersistenceRegression.residualKeepsItsValue
#print axioms Tests.PerimeterPersistenceRegression.secondFreshKeepsItsValue
#print axioms Tests.PerimeterPersistenceRegression.thirdFreshHasItsOwnValue
#print axioms Tests.PerimeterPersistenceRegression.retainedOccurrencesStayDistinct
#print axioms Tests.PerimeterPersistenceRegression.readoutRoundTrip
/- AXIOM_AUDIT_END -/
