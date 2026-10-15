import RelationalPerimeter.Constitution.HeytingArithmetic.GodelTheoryProgression

/-!
# Perimetral-resource-driven Gödel history transitions

This module connects the exact production, certification and residual
occurrences of a Gödel perimetral participation to the next sound
theory-history stage.  The phase kernel is parametric: before specialization
to HA it receives only a function consuming a certified witness.  The ordered
protocol then preserves the target authorized at certification and exposes it
only after the residual resource completes the transition.

The module also records the proof-theoretic dependency created by the
extension.  Every target derivation of the source Gödel boundary uses the
newest history postulate; otherwise it erases to a forbidden source derivation.
This necessity is characterized exactly as source non-derivability.
-/

namespace RelationalPerimeter
namespace HeytingArithmetic

open StrongPerimetralTurning

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000

/-! ## Availability without a hidden witness index -/

inductive StageAvailablePerimeterResource
    (coding : GodelDiagonalSyntax)
    (unprovabilityFormula : coding.UnaryFormula)
    (interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula) : Type _
  | produced :
      ExecutedGodelSentenceProduction coding unprovabilityFormula ->
      StageAvailablePerimeterResource coding unprovabilityFormula interpretation
  | certified :
      ExecutedGodelWitness coding unprovabilityFormula interpretation ->
      StageAvailablePerimeterResource coding unprovabilityFormula interpretation
  | retained :
      ExecutedGodelWitness coding unprovabilityFormula interpretation ->
      StageAvailablePerimeterResource coding unprovabilityFormula interpretation

def forgetStageResourceWitnessIndex
    {coding : GodelDiagonalSyntax}
    {unprovabilityFormula : coding.UnaryFormula}
    {interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula}
    {witness :
      ExecutedGodelWitness coding unprovabilityFormula interpretation} :
    ArithmeticExecutedGodelPerimeterResource witness ->
      StageAvailablePerimeterResource coding unprovabilityFormula interpretation
  | .produced production => .produced production
  | .certified certifiedWitness => .certified certifiedWitness
  | .continued retainedWitness => .retained retainedWitness

def availableStageResourceOfReturnedImplicit
    (source : SoundGodelHistoryStage) :
    ReturnedImplicit (ArithmeticExecutedGodelPresentation source.execution) ->
      Option
        (StageAvailablePerimeterResource source.system.toGodelSyntax
          source.system.unprovabilityFormula
          source.system.toGodelInterpretation)
  | .source resource => some (forgetStageResourceWitnessIndex resource)
  | .formed _ => none

theorem productionOccurrenceReturnedImplicit_exact
    (source : SoundGodelHistoryStage)
    (participation : StagePerimetralParticipation source) :
    implicitRead participation.productionOccurrence.locatedStep.source =
      .source (.produced source.producedWitness.production) := by
  rw [participation.productionOccurrenceIsExact]
  exact
    (participation.labelled.extension.oldOccurrenceAgreement
      (arithmeticExecutedGodelProductionPosition
        source.producedWitness)).implicitReadoutExact

theorem certificationOccurrenceReturnedImplicit_exact
    (source : SoundGodelHistoryStage)
    (participation : StagePerimetralParticipation source) :
    implicitRead participation.certificationOccurrence.locatedStep.source =
      .source (.certified source.producedWitness) := by
  rw [participation.certificationOccurrenceIsExact]
  exact
    (participation.labelled.extension.oldOccurrenceAgreement
      (arithmeticExecutedGodelCertificationPosition
        source.producedWitness)).implicitReadoutExact

theorem residualOccurrenceReturnedImplicit_exact
    (source : SoundGodelHistoryStage)
    (participation : StagePerimetralParticipation source) :
    implicitRead
      (participation.labelled.extension.newOccurrence
        participation.residualOccurrence).locatedStep.source =
      .source (.continued source.producedWitness) := by
  let boundary :=
    finalBoundaryOccurrence participation.labelled participation.positive
  have residualExact :
      participation.residualOccurrence = boundary.continuationOccurrence :=
    participation.residualOccurrenceIsPositive.trans
      boundary.occurrenceIsCanonical.symm
  have embeddedLocatedStep :
      (participation.labelled.extension.newOccurrence
        participation.residualOccurrence).locatedStep =
      participation.residualOccurrence.locatedStep := by
    unfold PerimeterExtension.newOccurrence
    exact
      (locatedStep_transportOccurrence
        participation.labelled.extension.recompose
        (History.embedRightOccurrence
          (perimeterHistory
            (ArithmeticExecutedGodelPresentation source.execution))
          participation.residualOccurrence)).trans
        (History.locatedStep_embedRight
          (perimeterHistory
            (ArithmeticExecutedGodelPresentation source.execution))
          participation.residualOccurrence)
  rw [embeddedLocatedStep, residualExact]
  change implicitRead boundary.source = _
  exact
    (finalClosureInterpretation boundary).actualFreeStep_source_is_terminalImplicit

def productionOccurrenceAvailableResource
    (source : SoundGodelHistoryStage)
    (participation : StagePerimetralParticipation source) :=
  availableStageResourceOfReturnedImplicit source
    (implicitRead participation.productionOccurrence.locatedStep.source)

def certificationOccurrenceAvailableResource
    (source : SoundGodelHistoryStage)
    (participation : StagePerimetralParticipation source) :=
  availableStageResourceOfReturnedImplicit source
    (implicitRead participation.certificationOccurrence.locatedStep.source)

def residualOccurrenceAvailableResource
    (source : SoundGodelHistoryStage)
    (participation : StagePerimetralParticipation source) :=
  availableStageResourceOfReturnedImplicit source
    (implicitRead
      (participation.labelled.extension.newOccurrence
        participation.residualOccurrence).locatedStep.source)

theorem productionOccurrenceAvailableResource_exact
    (source : SoundGodelHistoryStage)
    (participation : StagePerimetralParticipation source) :
    productionOccurrenceAvailableResource source participation =
      some (.produced source.producedWitness.production) := by
  unfold productionOccurrenceAvailableResource
  rw [productionOccurrenceReturnedImplicit_exact]
  cases source
  rfl

theorem certificationOccurrenceAvailableResource_exact
    (source : SoundGodelHistoryStage)
    (participation : StagePerimetralParticipation source) :
    certificationOccurrenceAvailableResource source participation =
      some (.certified source.producedWitness) := by
  unfold certificationOccurrenceAvailableResource
  rw [certificationOccurrenceReturnedImplicit_exact]
  cases source
  rfl

theorem residualOccurrenceAvailableResource_exact
    (source : SoundGodelHistoryStage)
    (participation : StagePerimetralParticipation source) :
    residualOccurrenceAvailableResource source participation =
      some (.retained source.producedWitness) := by
  unfold residualOccurrenceAvailableResource
  rw [residualOccurrenceReturnedImplicit_exact]
  rfl

/-! ## A phase-sensitive parametric transition -/

inductive StageAdvanceState (TargetStage : Type) : Type
  | waiting : StageAdvanceState TargetStage
  | authorized (target : TargetStage) : StageAdvanceState TargetStage
  | retained (target : TargetStage) : StageAdvanceState TargetStage

def stageAdvanceKernel
    {coding : GodelDiagonalSyntax}
    {unprovabilityFormula : coding.UnaryFormula}
    {interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula}
    {TargetStage : Type}
    (extend :
      ExecutedGodelWitness coding unprovabilityFormula interpretation ->
        TargetStage) :
    StageAvailablePerimeterResource coding unprovabilityFormula interpretation ->
      StageAdvanceState TargetStage
  | .produced _ => .waiting
  | .certified witness => .authorized (extend witness)
  | .retained witness => .retained (extend witness)

def extendStageFromCertifiedWitness
    (source : SoundGodelHistoryStage)
    (witness :
      ExecutedGodelWitness source.system.toGodelSyntax
        source.system.unprovabilityFormula
        source.system.toGodelInterpretation) :
    SoundGodelHistoryStage :=
  { history := .extend source.history witness.production.sentence
    sound := source.sound.extend witness.trueWitness }

def stageAdvanceFromAvailableResource
    (source : SoundGodelHistoryStage) :
    StageAvailablePerimeterResource source.system.toGodelSyntax
      source.system.unprovabilityFormula
      source.system.toGodelInterpretation ->
      StageAdvanceState SoundGodelHistoryStage :=
  stageAdvanceKernel (extendStageFromCertifiedWitness source)

def stageAdvanceFromReturnedImplicit
    (source : SoundGodelHistoryStage)
    (readout :
      ReturnedImplicit (ArithmeticExecutedGodelPresentation source.execution)) :
    Option (StageAdvanceState SoundGodelHistoryStage) :=
  match availableStageResourceOfReturnedImplicit source readout with
  | none => none
  | some resource => some (stageAdvanceFromAvailableResource source resource)

theorem retainedResourceRemainsRetained
    (source : SoundGodelHistoryStage)
    (witness :
      ExecutedGodelWitness source.system.toGodelSyntax
        source.system.unprovabilityFormula
        source.system.toGodelInterpretation) :
    stageAdvanceFromAvailableResource source (.retained witness) =
      .retained (extendStageFromCertifiedWitness source witness) :=
  rfl

theorem productionOccurrenceWaits
    (source : SoundGodelHistoryStage)
    (participation : StagePerimetralParticipation source) :
    stageAdvanceFromReturnedImplicit source
      (implicitRead participation.productionOccurrence.locatedStep.source) =
        some (.waiting) := by
  rw [productionOccurrenceReturnedImplicit_exact]
  cases source
  rfl

theorem certificationOccurrenceAdvancesExactly
    (source : SoundGodelHistoryStage)
    (participation : StagePerimetralParticipation source) :
    stageAdvanceFromReturnedImplicit source
      (implicitRead participation.certificationOccurrence.locatedStep.source) =
        some (.authorized source.advance) := by
  rw [certificationOccurrenceReturnedImplicit_exact]
  cases source
  rfl

theorem residualOccurrenceRetainsExactly
    (source : SoundGodelHistoryStage)
    (participation : StagePerimetralParticipation source) :
    stageAdvanceFromReturnedImplicit source
      (implicitRead
        (participation.labelled.extension.newOccurrence
          participation.residualOccurrence).locatedStep.source) =
      some (.retained source.advance) := by
  rw [residualOccurrenceReturnedImplicit_exact]
  cases source
  rfl

/-! ## An ordered production-certification-residual protocol -/

structure StageTransitionProduction
    (coding : GodelDiagonalSyntax)
    (unprovabilityFormula : coding.UnaryFormula) : Type where
  production : ExecutedGodelSentenceProduction coding unprovabilityFormula

structure StageTransitionAuthorization
    (coding : GodelDiagonalSyntax)
    (unprovabilityFormula : coding.UnaryFormula)
    (interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula)
    (TargetStage : Type) : Type where
  production : ExecutedGodelSentenceProduction coding unprovabilityFormula
  certifiedWitness :
    ExecutedGodelWitness coding unprovabilityFormula interpretation
  target : TargetStage

structure StageTransitionCompletion
    (coding : GodelDiagonalSyntax)
    (unprovabilityFormula : coding.UnaryFormula)
    (interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula)
    (TargetStage : Type) : Type where
  production : ExecutedGodelSentenceProduction coding unprovabilityFormula
  certifiedWitness :
    ExecutedGodelWitness coding unprovabilityFormula interpretation
  retainedWitness :
    ExecutedGodelWitness coding unprovabilityFormula interpretation
  target : TargetStage

def consumeProducedStageResource
    {coding : GodelDiagonalSyntax}
    {unprovabilityFormula : coding.UnaryFormula}
    {interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula} :
    StageAvailablePerimeterResource coding unprovabilityFormula interpretation ->
    Option (StageTransitionProduction coding unprovabilityFormula)
  | .produced production => some ⟨production⟩
  | .certified _ => none
  | .retained _ => none

def consumeCertifiedStageResource
    {coding : GodelDiagonalSyntax}
    {unprovabilityFormula : coding.UnaryFormula}
    {interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula}
    {TargetStage : Type}
    (extend :
      ExecutedGodelWitness coding unprovabilityFormula interpretation ->
        TargetStage)
    (produced : StageTransitionProduction coding unprovabilityFormula) :
    StageAvailablePerimeterResource coding unprovabilityFormula interpretation ->
    Option
      (StageTransitionAuthorization coding unprovabilityFormula interpretation
        TargetStage)
  | .produced _ => none
  | .certified witness =>
      some ⟨produced.production, witness, extend witness⟩
  | .retained _ => none

def consumeRetainedStageResource
    {coding : GodelDiagonalSyntax}
    {unprovabilityFormula : coding.UnaryFormula}
    {interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula}
    {TargetStage : Type}
    (authorization :
      StageTransitionAuthorization coding unprovabilityFormula interpretation
        TargetStage) :
    StageAvailablePerimeterResource coding unprovabilityFormula interpretation ->
    Option
      (StageTransitionCompletion coding unprovabilityFormula interpretation
        TargetStage)
  | .produced _ => none
  | .certified _ => none
  | .retained witness =>
      some
        ⟨authorization.production, authorization.certifiedWitness, witness,
          authorization.target⟩

def runStageTransitionResources
    {coding : GodelDiagonalSyntax}
    {unprovabilityFormula : coding.UnaryFormula}
    {interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula}
    {TargetStage : Type}
    (extend :
      ExecutedGodelWitness coding unprovabilityFormula interpretation ->
        TargetStage)
    (production certification residual :
      Option
        (StageAvailablePerimeterResource coding unprovabilityFormula
          interpretation)) :
    Option
      (StageTransitionCompletion coding unprovabilityFormula interpretation
        TargetStage) := do
  let productionResource <- production
  let produced <- consumeProducedStageResource productionResource
  let certificationResource <- certification
  let authorization <-
    consumeCertifiedStageResource extend produced certificationResource
  let residualResource <- residual
  consumeRetainedStageResource authorization residualResource

theorem runStageTransitionResources_preservesPayloads
    {coding : GodelDiagonalSyntax}
    {unprovabilityFormula : coding.UnaryFormula}
    {interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula}
    {TargetStage : Type}
    (extend :
      ExecutedGodelWitness coding unprovabilityFormula interpretation ->
        TargetStage)
    (production :
      ExecutedGodelSentenceProduction coding unprovabilityFormula)
    (certified retained :
      ExecutedGodelWitness coding unprovabilityFormula interpretation) :
    runStageTransitionResources extend
        (some (.produced production))
        (some (.certified certified))
        (some (.retained retained)) =
      some ⟨production, certified, retained, extend certified⟩ :=
  rfl

def runCompletedStageTransition
    (source : SoundGodelHistoryStage)
    (participation : StagePerimetralParticipation source) :
    Option
      (StageTransitionCompletion source.system.toGodelSyntax
        source.system.unprovabilityFormula
        source.system.toGodelInterpretation SoundGodelHistoryStage) :=
  runStageTransitionResources (extendStageFromCertifiedWitness source)
    (productionOccurrenceAvailableResource source participation)
    (certificationOccurrenceAvailableResource source participation)
    (residualOccurrenceAvailableResource source participation)

theorem runCompletedStageTransition_exact
    (source : SoundGodelHistoryStage)
    (participation : StagePerimetralParticipation source) :
    runCompletedStageTransition source participation =
      some
        ⟨source.producedWitness.production, source.producedWitness,
          source.producedWitness, source.advance⟩ := by
  unfold runCompletedStageTransition runStageTransitionResources
  rw [productionOccurrenceAvailableResource_exact]
  rw [certificationOccurrenceAvailableResource_exact]
  rw [residualOccurrenceAvailableResource_exact]
  cases source
  rfl

def CompletedStageOutcome
    {coding : GodelDiagonalSyntax}
    {unprovabilityFormula : coding.UnaryFormula}
    {interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula}
    {TargetStage : Type}
    (outcome :
      Option
        (StageTransitionCompletion coding unprovabilityFormula interpretation
          TargetStage)) : Type :=
  Sigma fun completion :
      StageTransitionCompletion coding unprovabilityFormula interpretation
        TargetStage =>
    PLift (outcome = some completion)

def completedStageOutcome
    (source : SoundGodelHistoryStage)
    (participation : StagePerimetralParticipation source) :
    CompletedStageOutcome (runCompletedStageTransition source participation) := by
  match exactness : runCompletedStageTransition source participation with
  | none =>
      have impossible :
          (none :
              Option
                (StageTransitionCompletion source.system.toGodelSyntax
                  source.system.unprovabilityFormula
                  source.system.toGodelInterpretation
                  SoundGodelHistoryStage)) =
            some
              ⟨source.producedWitness.production, source.producedWitness,
                source.producedWitness, source.advance⟩ :=
        exactness.symm.trans
          (runCompletedStageTransition_exact source participation)
      cases impossible
  | some actual => exact ⟨actual, ⟨rfl⟩⟩

def completedStageTarget
    {source : SoundGodelHistoryStage}
    {participation : StagePerimetralParticipation source}
    (completion :
      CompletedStageOutcome (runCompletedStageTransition source participation)) :
    SoundGodelHistoryStage :=
  completion.1.target

theorem completedStageOutcome_target_eq_advance
    (source : SoundGodelHistoryStage)
    (participation : StagePerimetralParticipation source)
    (completion :
      CompletedStageOutcome (runCompletedStageTransition source participation)) :
    completedStageTarget completion = source.advance := by
  rcases completion with ⟨completed, ⟨completionExact⟩⟩
  have sameCompletion :
      some completed =
        some
          ⟨source.producedWitness.production, source.producedWitness,
            source.producedWitness, source.advance⟩ :=
    completionExact.symm.trans
      (runCompletedStageTransition_exact source participation)
  exact congrArg StageTransitionCompletion.target
    (Option.some.inj sameCompletion)

theorem completedStageTarget_eq_advance
    (source : SoundGodelHistoryStage)
    (participation : StagePerimetralParticipation source) :
    completedStageTarget (completedStageOutcome source participation) =
      source.advance :=
  completedStageOutcome_target_eq_advance source participation _

/-! ## Compatibility with the former certification-only target -/

def AuthorizedStageOutcome
    {TargetStage : Type}
    (outcome : Option (StageAdvanceState TargetStage)) : Type :=
  Sigma fun target : TargetStage =>
    PLift (outcome = some (.authorized target))

def authorizedStageOfOutcome
    {TargetStage : Type}
    (outcome : Option (StageAdvanceState TargetStage))
    (authorization : AuthorizedStageOutcome outcome) :
    TargetStage :=
  match outcome with
  | none => by cases authorization.2.down
  | some .waiting => by cases authorization.2.down
  | some (.authorized target) => target
  | some (.retained _) => by cases authorization.2.down

theorem authorizedStageOfOutcome_eq
    {TargetStage : Type}
    (outcome : Option (StageAdvanceState TargetStage))
    (authorization : AuthorizedStageOutcome outcome) :
    authorizedStageOfOutcome outcome authorization = authorization.1 := by
  rcases authorization with ⟨expected, ⟨exactness⟩⟩
  cases outcome with
  | none => cases exactness
  | some state =>
      cases state with
      | waiting => cases exactness
      | authorized actual =>
          cases exactness
          rfl
      | retained actual => cases exactness

def certificationStageOutcome
    (source : SoundGodelHistoryStage)
    (participation : StagePerimetralParticipation source) :
    AuthorizedStageOutcome
      (stageAdvanceFromReturnedImplicit source
        (implicitRead participation.certificationOccurrence.locatedStep.source)) :=
  ⟨source.advance,
    ⟨certificationOccurrenceAdvancesExactly source participation⟩⟩

def certifiedTarget
    (source : SoundGodelHistoryStage)
    (participation : StagePerimetralParticipation source) :
    SoundGodelHistoryStage :=
  authorizedStageOfOutcome
    (stageAdvanceFromReturnedImplicit source
      (implicitRead participation.certificationOccurrence.locatedStep.source))
    (certificationStageOutcome source participation)

theorem certifiedTarget_eq_advance
    (source : SoundGodelHistoryStage)
    (participation : StagePerimetralParticipation source) :
    certifiedTarget source participation = source.advance := by
  exact authorizedStageOfOutcome_eq _ _

/-! ## Proof dependence on the newest history postulate -/

theorem boolOrFalseLeft {left right : Bool}
    (combined : (left || right) = false) : left = false := by
  cases left <;> cases right <;> cases combined
  rfl

theorem boolOrFalseRight {left right : Bool}
    (combined : (left || right) = false) : right = false := by
  cases left <;> cases right <;> cases combined
  rfl

theorem boolOrFalseBoth {left right : Bool}
    (leftFalse : left = false)
    (rightFalse : right = false) : (left || right) = false := by
  cases left <;> cases right <;> cases leftFalse <;> cases rightFalse
  rfl

def historyDerivationUsesNewest
    {history : TheoryHistory}
    {newest : Sentence}
    {bound : Nat}
    {context : FormulaContext bound}
    {conclusion : ScopedFormula bound} :
    Derivation LogicMode.intuitionistic
      (TheoryHistory.extend history newest).theory context conclusion -> Bool
  | .theoryAxiom witness =>
      match witness with
      | .arithmetic _ => false
      | .added occurrence =>
          match occurrence with
          | .newest => true
          | .earlier _ => false
  | .hypothesis _ => false
  | .weaken _ proof => historyDerivationUsesNewest proof
  | .implicationIntroduction proof => historyDerivationUsesNewest proof
  | .implicationElimination implication argument =>
      historyDerivationUsesNewest implication ||
        historyDerivationUsesNewest argument
  | .conjunctionIntroduction left right =>
      historyDerivationUsesNewest left || historyDerivationUsesNewest right
  | .conjunctionEliminationLeft proof => historyDerivationUsesNewest proof
  | .conjunctionEliminationRight proof => historyDerivationUsesNewest proof
  | .disjunctionIntroductionLeft proof => historyDerivationUsesNewest proof
  | .disjunctionIntroductionRight proof => historyDerivationUsesNewest proof
  | .disjunctionElimination disjunction left right =>
      (historyDerivationUsesNewest disjunction ||
        historyDerivationUsesNewest left) ||
        historyDerivationUsesNewest right
  | .falsumElimination proof => historyDerivationUsesNewest proof
  | .universalIntroduction proof => historyDerivationUsesNewest proof
  | .universalElimination _ proof => historyDerivationUsesNewest proof
  | .existentialIntroduction _ proof => historyDerivationUsesNewest proof
  | .existentialElimination existence body =>
      historyDerivationUsesNewest existence || historyDerivationUsesNewest body
  | .equalityReflexivity _ => false
  | .equalitySymmetry proof => historyDerivationUsesNewest proof
  | .equalityTransitivity left right =>
      historyDerivationUsesNewest left || historyDerivationUsesNewest right
  | .equalitySubstitution _ equality body =>
      historyDerivationUsesNewest equality || historyDerivationUsesNewest body
  | .liftVariables proof => historyDerivationUsesNewest proof
  | .freeInstantiation _ proof => historyDerivationUsesNewest proof
  | .doubleNegationElimination _ proof => historyDerivationUsesNewest proof

def eraseNewestFreeDerivation
    {history : TheoryHistory}
    {newest : Sentence}
    {bound : Nat}
    {context : FormulaContext bound}
    {conclusion : ScopedFormula bound}
    (proof : Derivation LogicMode.intuitionistic
      (TheoryHistory.extend history newest).theory context conclusion)
    (unused : historyDerivationUsesNewest proof = false) :
    Derivation LogicMode.intuitionistic history.theory context conclusion :=
  match proof with
  | .theoryAxiom (.arithmetic arithmeticWitness) =>
      .theoryAxiom (.arithmetic arithmeticWitness)
  | .theoryAxiom (.added .newest) => by cases unused
  | .theoryAxiom (.added (.earlier previous)) =>
      .theoryAxiom (.added previous)
  | .hypothesis member => .hypothesis member
  | .weaken extra inner =>
      .weaken extra (eraseNewestFreeDerivation inner unused)
  | .implicationIntroduction inner =>
      .implicationIntroduction (eraseNewestFreeDerivation inner unused)
  | .implicationElimination implication argument =>
      .implicationElimination
        (eraseNewestFreeDerivation implication (boolOrFalseLeft unused))
        (eraseNewestFreeDerivation argument (boolOrFalseRight unused))
  | .conjunctionIntroduction left right =>
      .conjunctionIntroduction
        (eraseNewestFreeDerivation left (boolOrFalseLeft unused))
        (eraseNewestFreeDerivation right (boolOrFalseRight unused))
  | .conjunctionEliminationLeft inner =>
      .conjunctionEliminationLeft (eraseNewestFreeDerivation inner unused)
  | .conjunctionEliminationRight inner =>
      .conjunctionEliminationRight (eraseNewestFreeDerivation inner unused)
  | .disjunctionIntroductionLeft inner =>
      .disjunctionIntroductionLeft (eraseNewestFreeDerivation inner unused)
  | .disjunctionIntroductionRight inner =>
      .disjunctionIntroductionRight (eraseNewestFreeDerivation inner unused)
  | .disjunctionElimination disjunction left right =>
      let firstTwoFalse :
          (historyDerivationUsesNewest disjunction ||
            historyDerivationUsesNewest left) = false :=
        boolOrFalseLeft unused
      .disjunctionElimination
        (eraseNewestFreeDerivation disjunction
          (boolOrFalseLeft firstTwoFalse))
        (eraseNewestFreeDerivation left
          (boolOrFalseRight firstTwoFalse))
        (eraseNewestFreeDerivation right (boolOrFalseRight unused))
  | .falsumElimination inner =>
      .falsumElimination (eraseNewestFreeDerivation inner unused)
  | .universalIntroduction inner =>
      .universalIntroduction (eraseNewestFreeDerivation inner unused)
  | .universalElimination term inner =>
      .universalElimination term (eraseNewestFreeDerivation inner unused)
  | .existentialIntroduction term inner =>
      .existentialIntroduction term (eraseNewestFreeDerivation inner unused)
  | .existentialElimination existence body =>
      .existentialElimination
        (eraseNewestFreeDerivation existence (boolOrFalseLeft unused))
        (eraseNewestFreeDerivation body (boolOrFalseRight unused))
  | .equalityReflexivity term => .equalityReflexivity term
  | .equalitySymmetry inner =>
      .equalitySymmetry (eraseNewestFreeDerivation inner unused)
  | .equalityTransitivity left right =>
      .equalityTransitivity
        (eraseNewestFreeDerivation left (boolOrFalseLeft unused))
        (eraseNewestFreeDerivation right (boolOrFalseRight unused))
  | .equalitySubstitution body equality inner =>
      .equalitySubstitution body
        (eraseNewestFreeDerivation equality (boolOrFalseLeft unused))
        (eraseNewestFreeDerivation inner (boolOrFalseRight unused))
  | .liftVariables inner =>
      .liftVariables (eraseNewestFreeDerivation inner unused)
  | .freeInstantiation replacement inner =>
      .freeInstantiation replacement
        (eraseNewestFreeDerivation inner unused)
  | .doubleNegationElimination permission inner =>
      .doubleNegationElimination permission
        (eraseNewestFreeDerivation inner unused)

/-- A derivation transported from the source history never uses the postulate
newly added by the target history. -/
theorem historyDerivationPreserve_usesNewest_false
    {history : TheoryHistory}
    {newest : Sentence}
    {bound : Nat}
    {context : FormulaContext bound}
    {conclusion : ScopedFormula bound}
    (proof : Derivation LogicMode.intuitionistic history.theory
      context conclusion) :
    historyDerivationUsesNewest
        (historyDerivationPreserve (newest := newest) proof) = false := by
  induction proof with
  | theoryAxiom witness =>
      cases witness with
      | arithmetic _ => rfl
      | added _ => rfl
  | hypothesis _ => rfl
  | equalityReflexivity _ => rfl
  | weaken _ _ inductionHypothesis => exact inductionHypothesis
  | implicationIntroduction _ inductionHypothesis => exact inductionHypothesis
  | implicationElimination _ _ leftInduction rightInduction =>
      exact boolOrFalseBoth leftInduction rightInduction
  | conjunctionIntroduction _ _ leftInduction rightInduction =>
      exact boolOrFalseBoth leftInduction rightInduction
  | conjunctionEliminationLeft _ inductionHypothesis =>
      exact inductionHypothesis
  | conjunctionEliminationRight _ inductionHypothesis =>
      exact inductionHypothesis
  | disjunctionIntroductionLeft _ inductionHypothesis =>
      exact inductionHypothesis
  | disjunctionIntroductionRight _ inductionHypothesis =>
      exact inductionHypothesis
  | disjunctionElimination _ _ _ firstInduction secondInduction thirdInduction =>
      exact boolOrFalseBoth
        (boolOrFalseBoth firstInduction secondInduction) thirdInduction
  | falsumElimination _ inductionHypothesis => exact inductionHypothesis
  | universalIntroduction _ inductionHypothesis => exact inductionHypothesis
  | universalElimination _ _ inductionHypothesis => exact inductionHypothesis
  | existentialIntroduction _ _ inductionHypothesis => exact inductionHypothesis
  | existentialElimination _ _ leftInduction rightInduction =>
      exact boolOrFalseBoth leftInduction rightInduction
  | equalitySymmetry _ inductionHypothesis => exact inductionHypothesis
  | equalityTransitivity _ _ leftInduction rightInduction =>
      exact boolOrFalseBoth leftInduction rightInduction
  | equalitySubstitution _ _ _ leftInduction rightInduction =>
      exact boolOrFalseBoth leftInduction rightInduction
  | liftVariables _ inductionHypothesis => exact inductionHypothesis
  | freeInstantiation _ _ inductionHypothesis => exact inductionHypothesis
  | doubleNegationElimination _ _ inductionHypothesis =>
      exact inductionHypothesis

/-- For an arbitrary history and sentence, every derivation after adjoining
that sentence uses the newest postulate exactly when the source history did
not already derive it.  This theorem fixes the precise scope of the
`usesNewest` diagnostic; it is not advertised as additional Gödel content. -/
def BoundaryUsesNewestAfterExtension
    (history : TheoryHistory)
    (newest : Sentence) : Prop :=
  ∀ proof : Derivation LogicMode.intuitionistic
      (TheoryHistory.extend history newest).theory
      FormulaContext.nil newest.scopedFormula,
    historyDerivationUsesNewest proof = true

theorem boundaryUsesNewestAfterExtension_iff_sourceUnprovable
    (history : TheoryHistory)
    (newest : Sentence) :
    BoundaryUsesNewestAfterExtension history newest ↔
      ¬ HistoryProvable history newest := by
  constructor
  · intro necessity ⟨sourceProof⟩
    have contradiction := necessity (historyDerivationPreserve sourceProof)
    rw [historyDerivationPreserve_usesNewest_false] at contradiction
    cases contradiction
  · intro sourceUnprovable targetProof
    cases uses : historyDerivationUsesNewest targetProof with
    | false =>
        exact False.elim
          (sourceUnprovable ⟨eraseNewestFreeDerivation targetProof uses⟩)
    | true => rfl

theorem sourceBoundaryDerivationUsesNewest
    (source : SoundGodelHistoryStage)
    (proof : Derivation LogicMode.intuitionistic source.advance.history.theory
      FormulaContext.nil source.producedSentence.scopedFormula) :
    historyDerivationUsesNewest proof = true := by
  cases uses : historyDerivationUsesNewest proof with
  | false =>
      exact Empty.elim
        (source.producedNoProof
          (historyCheckedProofOfDerivation
            (eraseNewestFreeDerivation proof uses)))
  | true => rfl

theorem checkedSourceBoundaryDerivationUsesNewest
    (source : SoundGodelHistoryStage)
    (proof : CheckedSentenceProof Sentence.quote
      (historyProofCheck source.advance.history) source.producedSentence) :
    historyDerivationUsesNewest
        (historyDerivationOfCheckedProof source.advance.history proof) = true :=
  sourceBoundaryDerivationUsesNewest source
    (historyDerivationOfCheckedProof source.advance.history proof)

/-- At the successor of `source`, every derivation of the sentence produced at
`source` consumes the newest history postulate.  The characterization below
records that this statement is exactly source non-derivability. -/
def SourceBoundaryUsesNewestAtAdvance
    (source : SoundGodelHistoryStage) : Prop :=
  ∀ proof : Derivation LogicMode.intuitionistic source.advance.history.theory
      FormulaContext.nil source.producedSentence.scopedFormula,
    historyDerivationUsesNewest proof = true

theorem sourceBoundaryUsesNewestAtAdvance
    (source : SoundGodelHistoryStage) :
    SourceBoundaryUsesNewestAtAdvance source :=
  sourceBoundaryDerivationUsesNewest source

theorem sourceBoundaryUsesNewestAtAdvance_iff_sourceUnprovable
    (source : SoundGodelHistoryStage) :
    SourceBoundaryUsesNewestAtAdvance source ↔
      ¬ HistoryProvable source.history source.producedSentence :=
  boundaryUsesNewestAfterExtension_iff_sourceUnprovable
    source.history source.producedSentence

/-! ## A progression indexed by the completed perimetral target -/

def GodelHistoryProgressionAtTarget
    (source target : SoundGodelHistoryStage) : Type :=
  SourceSentenceUnprovableAtSource source ×
  SourceSentenceTruth source ×
  target.history.Contains source.producedSentence ×
  CheckedSentenceProof Sentence.quote
    (historyProofCheck target.history) source.producedSentence ×
  haTruth target.producedSentence ×
  (CheckedSentenceProof Sentence.quote
      (historyProofCheck target.history) target.producedSentence -> Empty) ×
  PLift (source.producedSentence ≠ target.producedSentence)

def godelHistoryProgressionAtCompletedTarget
    (source : SoundGodelHistoryStage)
    (participation : StagePerimetralParticipation source)
    (completion :
      CompletedStageOutcome
        (runCompletedStageTransition source participation)) :
    GodelHistoryProgressionAtTarget source
      (completedStageTarget completion) := by
  let target := completedStageTarget completion
  have targetExact : target = source.advance :=
    completedStageOutcome_target_eq_advance source participation completion
  have occurrence : target.history.Contains source.producedSentence := by
    rw [targetExact]
    exact source.sourceSentenceOccursAtAdvance
  have sourceProof :
      CheckedSentenceProof Sentence.quote
        (historyProofCheck target.history) source.producedSentence := by
    rw [targetExact]
    exact source.sourceSentenceProofAtAdvance
      source.sourceSentenceOccursAtAdvance
  have different : source.producedSentence ≠ target.producedSentence := by
    intro sameSentence
    exact Empty.elim
      (target.producedNoProof (sameSentence ▸ sourceProof))
  exact
    ⟨source.producedNoProof,
      source.producedTruth,
      occurrence,
      sourceProof,
      target.producedTruth,
      target.producedNoProof,
      ⟨different⟩⟩

/-! ## A tower whose successor is the completed target -/

def ParticipatingGodelHistoryStage : Type 1 :=
  Sigma fun stage : SoundGodelHistoryStage =>
    StagePerimetralParticipation stage

def rootParticipatingGodelHistoryStage :
    ParticipatingGodelHistoryStage :=
  ⟨rootGodelHistoryStage,
    rootGodelHistoryStage.perimetralParticipation⟩

def ParticipatingGodelHistoryStage.advance
    (source : ParticipatingGodelHistoryStage) :
    ParticipatingGodelHistoryStage :=
  let completion := completedStageOutcome source.1 source.2
  let target := completedStageTarget completion
  ⟨target, target.perimetralParticipation⟩

theorem ParticipatingGodelHistoryStage.advance_stage_eq
    (source : ParticipatingGodelHistoryStage) :
    source.advance.1 = source.1.advance :=
  completedStageTarget_eq_advance source.1 source.2

/-- The public result of one occurrence-driven history transition.  Its
completion is constructed by consuming production, certification and residual
readouts in order.  The arithmetic facts and the target participation are
indexed by the target extracted from that completion. -/
def CertifiedPerimetralGodelHistoryProgression
    (source : ParticipatingGodelHistoryStage) : Type 1 :=
  Sigma fun completion :
      CompletedStageOutcome
        (runCompletedStageTransition source.1 source.2) =>
    GodelHistoryProgressionAtTarget source.1
        (completedStageTarget completion) ×
      StagePerimetralParticipation (completedStageTarget completion)

def certifiedPerimetralGodelHistoryProgression
    (source : ParticipatingGodelHistoryStage) :
    CertifiedPerimetralGodelHistoryProgression source :=
  let completion := completedStageOutcome source.1 source.2
  ⟨completion,
    godelHistoryProgressionAtCompletedTarget source.1 source.2 completion,
    (completedStageTarget completion).perimetralParticipation⟩

def CertifiedPerimetralGodelHistoryProgression.progressionAtTarget
    {source : ParticipatingGodelHistoryStage}
    (result : CertifiedPerimetralGodelHistoryProgression source) :
    GodelHistoryProgressionAtTarget source.1
      (completedStageTarget result.1) :=
  result.2.1

def CertifiedPerimetralGodelHistoryProgression.progression
    {source : ParticipatingGodelHistoryStage}
    (result : CertifiedPerimetralGodelHistoryProgression source) :
    GodelHistoryProgression source.1 := by
  have targetExact :=
    completedStageOutcome_target_eq_advance source.1 source.2 result.1
  change GodelHistoryProgressionAtTarget source.1 source.1.advance
  rw [← targetExact]
  exact result.progressionAtTarget

theorem CertifiedPerimetralGodelHistoryProgression.sourceBoundaryUsesNewest
    {source : ParticipatingGodelHistoryStage}
    (_result : CertifiedPerimetralGodelHistoryProgression source) :
    SourceBoundaryUsesNewestAtAdvance source.1 :=
  sourceBoundaryUsesNewestAtAdvance source.1

def CertifiedPerimetralGodelHistoryProgression.target
    {source : ParticipatingGodelHistoryStage}
    (progression : CertifiedPerimetralGodelHistoryProgression source) :
    ParticipatingGodelHistoryStage :=
  ⟨completedStageTarget progression.1, progression.2.2⟩

theorem CertifiedPerimetralGodelHistoryProgression.target_stage_eq
    {source : ParticipatingGodelHistoryStage}
    (progression : CertifiedPerimetralGodelHistoryProgression source) :
    progression.target.1 = source.1.advance :=
  completedStageOutcome_target_eq_advance source.1 source.2 progression.1

theorem CertifiedPerimetralGodelHistoryProgression.sourceSentenceProofUsesNewest
    {source : ParticipatingGodelHistoryStage}
    (result : CertifiedPerimetralGodelHistoryProgression source) :
    historyDerivationUsesNewest
      (historyDerivationOfCheckedProof source.1.advance.history
        result.progression.sourceSentenceProvableAtTarget) = true :=
  result.sourceBoundaryUsesNewest _

theorem certifiedPerimetralGodelHistoryProgression_target_eq_advance
    (source : ParticipatingGodelHistoryStage) :
    (certifiedPerimetralGodelHistoryProgression source).target =
      source.advance :=
  rfl

def perimetralGodelHistoryStage : Nat -> ParticipatingGodelHistoryStage
  | 0 => rootParticipatingGodelHistoryStage
  | Nat.succ index =>
      (certifiedPerimetralGodelHistoryProgression
        (perimetralGodelHistoryStage index)).target

@[simp] theorem perimetralGodelHistoryStage_zero :
    perimetralGodelHistoryStage 0 = rootParticipatingGodelHistoryStage :=
  rfl

@[simp] theorem perimetralGodelHistoryStage_succ (index : Nat) :
    perimetralGodelHistoryStage (Nat.succ index) =
      (perimetralGodelHistoryStage index).advance :=
  rfl

theorem perimetralGodelHistoryStage_stage_eq
    (index : Nat) :
    (perimetralGodelHistoryStage index).1 = godelHistoryStage index := by
  induction index with
  | zero => rfl
  | succ previous ih =>
      change completedStageTarget
          (completedStageOutcome
            (perimetralGodelHistoryStage previous).1
            (perimetralGodelHistoryStage previous).2) =
        (godelHistoryStage previous).advance
      rw [completedStageTarget_eq_advance, ih]

def perimetralGodelHistoryProgressionAt
    (index : Nat) :
    CertifiedPerimetralGodelHistoryProgression
      (perimetralGodelHistoryStage index) :=
  certifiedPerimetralGodelHistoryProgression
    (perimetralGodelHistoryStage index)

theorem perimetralGodelHistoryStage_sourceBoundaryUsesNewest
    (index : Nat)
    (proof : Derivation LogicMode.intuitionistic
      (perimetralGodelHistoryStage index).1.advance.history.theory
      FormulaContext.nil
      (perimetralGodelHistoryStage index).1.producedSentence.scopedFormula) :
    historyDerivationUsesNewest proof = true :=
  sourceBoundaryDerivationUsesNewest
    (perimetralGodelHistoryStage index).1 proof

end HeytingArithmetic
end RelationalPerimeter

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.HeytingArithmetic.StageAvailablePerimeterResource
#print axioms RelationalPerimeter.HeytingArithmetic.forgetStageResourceWitnessIndex
#print axioms RelationalPerimeter.HeytingArithmetic.availableStageResourceOfReturnedImplicit
#print axioms RelationalPerimeter.HeytingArithmetic.productionOccurrenceReturnedImplicit_exact
#print axioms RelationalPerimeter.HeytingArithmetic.certificationOccurrenceReturnedImplicit_exact
#print axioms RelationalPerimeter.HeytingArithmetic.residualOccurrenceReturnedImplicit_exact
#print axioms RelationalPerimeter.HeytingArithmetic.productionOccurrenceAvailableResource
#print axioms RelationalPerimeter.HeytingArithmetic.certificationOccurrenceAvailableResource
#print axioms RelationalPerimeter.HeytingArithmetic.residualOccurrenceAvailableResource
#print axioms RelationalPerimeter.HeytingArithmetic.productionOccurrenceAvailableResource_exact
#print axioms RelationalPerimeter.HeytingArithmetic.certificationOccurrenceAvailableResource_exact
#print axioms RelationalPerimeter.HeytingArithmetic.residualOccurrenceAvailableResource_exact
#print axioms RelationalPerimeter.HeytingArithmetic.StageAdvanceState
#print axioms RelationalPerimeter.HeytingArithmetic.stageAdvanceKernel
#print axioms RelationalPerimeter.HeytingArithmetic.extendStageFromCertifiedWitness
#print axioms RelationalPerimeter.HeytingArithmetic.stageAdvanceFromAvailableResource
#print axioms RelationalPerimeter.HeytingArithmetic.stageAdvanceFromReturnedImplicit
#print axioms RelationalPerimeter.HeytingArithmetic.retainedResourceRemainsRetained
#print axioms RelationalPerimeter.HeytingArithmetic.productionOccurrenceWaits
#print axioms RelationalPerimeter.HeytingArithmetic.certificationOccurrenceAdvancesExactly
#print axioms RelationalPerimeter.HeytingArithmetic.residualOccurrenceRetainsExactly
#print axioms RelationalPerimeter.HeytingArithmetic.StageTransitionProduction
#print axioms RelationalPerimeter.HeytingArithmetic.StageTransitionAuthorization
#print axioms RelationalPerimeter.HeytingArithmetic.StageTransitionCompletion
#print axioms RelationalPerimeter.HeytingArithmetic.consumeProducedStageResource
#print axioms RelationalPerimeter.HeytingArithmetic.consumeCertifiedStageResource
#print axioms RelationalPerimeter.HeytingArithmetic.consumeRetainedStageResource
#print axioms RelationalPerimeter.HeytingArithmetic.runStageTransitionResources
#print axioms RelationalPerimeter.HeytingArithmetic.runStageTransitionResources_preservesPayloads
#print axioms RelationalPerimeter.HeytingArithmetic.runCompletedStageTransition
#print axioms RelationalPerimeter.HeytingArithmetic.runCompletedStageTransition_exact
#print axioms RelationalPerimeter.HeytingArithmetic.CompletedStageOutcome
#print axioms RelationalPerimeter.HeytingArithmetic.completedStageOutcome
#print axioms RelationalPerimeter.HeytingArithmetic.completedStageTarget
#print axioms RelationalPerimeter.HeytingArithmetic.completedStageTarget_eq_advance
#print axioms RelationalPerimeter.HeytingArithmetic.completedStageOutcome_target_eq_advance
#print axioms RelationalPerimeter.HeytingArithmetic.AuthorizedStageOutcome
#print axioms RelationalPerimeter.HeytingArithmetic.authorizedStageOfOutcome
#print axioms RelationalPerimeter.HeytingArithmetic.authorizedStageOfOutcome_eq
#print axioms RelationalPerimeter.HeytingArithmetic.certificationStageOutcome
#print axioms RelationalPerimeter.HeytingArithmetic.certifiedTarget
#print axioms RelationalPerimeter.HeytingArithmetic.certifiedTarget_eq_advance
#print axioms RelationalPerimeter.HeytingArithmetic.boolOrFalseLeft
#print axioms RelationalPerimeter.HeytingArithmetic.boolOrFalseRight
#print axioms RelationalPerimeter.HeytingArithmetic.boolOrFalseBoth
#print axioms RelationalPerimeter.HeytingArithmetic.historyDerivationUsesNewest
#print axioms RelationalPerimeter.HeytingArithmetic.eraseNewestFreeDerivation
#print axioms RelationalPerimeter.HeytingArithmetic.historyDerivationPreserve_usesNewest_false
#print axioms RelationalPerimeter.HeytingArithmetic.BoundaryUsesNewestAfterExtension
#print axioms RelationalPerimeter.HeytingArithmetic.boundaryUsesNewestAfterExtension_iff_sourceUnprovable
#print axioms RelationalPerimeter.HeytingArithmetic.sourceBoundaryDerivationUsesNewest
#print axioms RelationalPerimeter.HeytingArithmetic.checkedSourceBoundaryDerivationUsesNewest
#print axioms RelationalPerimeter.HeytingArithmetic.SourceBoundaryUsesNewestAtAdvance
#print axioms RelationalPerimeter.HeytingArithmetic.sourceBoundaryUsesNewestAtAdvance
#print axioms RelationalPerimeter.HeytingArithmetic.sourceBoundaryUsesNewestAtAdvance_iff_sourceUnprovable
#print axioms RelationalPerimeter.HeytingArithmetic.GodelHistoryProgressionAtTarget
#print axioms RelationalPerimeter.HeytingArithmetic.godelHistoryProgressionAtCompletedTarget
#print axioms RelationalPerimeter.HeytingArithmetic.ParticipatingGodelHistoryStage
#print axioms RelationalPerimeter.HeytingArithmetic.rootParticipatingGodelHistoryStage
#print axioms RelationalPerimeter.HeytingArithmetic.ParticipatingGodelHistoryStage.advance
#print axioms RelationalPerimeter.HeytingArithmetic.ParticipatingGodelHistoryStage.advance_stage_eq
#print axioms RelationalPerimeter.HeytingArithmetic.CertifiedPerimetralGodelHistoryProgression
#print axioms RelationalPerimeter.HeytingArithmetic.certifiedPerimetralGodelHistoryProgression
#print axioms RelationalPerimeter.HeytingArithmetic.CertifiedPerimetralGodelHistoryProgression.target
#print axioms RelationalPerimeter.HeytingArithmetic.CertifiedPerimetralGodelHistoryProgression.target_stage_eq
#print axioms RelationalPerimeter.HeytingArithmetic.CertifiedPerimetralGodelHistoryProgression.progressionAtTarget
#print axioms RelationalPerimeter.HeytingArithmetic.CertifiedPerimetralGodelHistoryProgression.progression
#print axioms RelationalPerimeter.HeytingArithmetic.CertifiedPerimetralGodelHistoryProgression.sourceBoundaryUsesNewest
#print axioms RelationalPerimeter.HeytingArithmetic.CertifiedPerimetralGodelHistoryProgression.sourceSentenceProofUsesNewest
#print axioms RelationalPerimeter.HeytingArithmetic.certifiedPerimetralGodelHistoryProgression_target_eq_advance
#print axioms RelationalPerimeter.HeytingArithmetic.perimetralGodelHistoryStage
#print axioms RelationalPerimeter.HeytingArithmetic.perimetralGodelHistoryStage_zero
#print axioms RelationalPerimeter.HeytingArithmetic.perimetralGodelHistoryStage_succ
#print axioms RelationalPerimeter.HeytingArithmetic.perimetralGodelHistoryStage_stage_eq
#print axioms RelationalPerimeter.HeytingArithmetic.perimetralGodelHistoryProgressionAt
#print axioms RelationalPerimeter.HeytingArithmetic.perimetralGodelHistoryStage_sourceBoundaryUsesNewest
/- AXIOM_AUDIT_END -/
