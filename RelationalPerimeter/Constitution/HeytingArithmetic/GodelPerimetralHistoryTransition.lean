import RelationalPerimeter.Constitution.HeytingArithmetic.GodelTheoryProgression

/-!
# Perimetral-resource-driven Gödel history transitions

This module connects the exact production and certification occurrences of a
Gödel perimetral participation to the next sound theory-history stage.  The
phase kernel is parametric: before specialization to HA it receives only a
function consuming a certified witness, so a produced resource cannot recover
that witness through the source stage.

The module also records the proof-theoretic dependency created by the
extension.  Every target derivation of the source Gödel boundary uses the
newest history postulate; otherwise it erases to a forbidden source derivation.
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

def occurrenceAdvanceNotFactorsThroughUnit
    (source : SoundGodelHistoryStage)
    (participation : StagePerimetralParticipation source)
    (factor : Unit -> Option (StageAdvanceState SoundGodelHistoryStage))
    (productionFactors :
      stageAdvanceFromReturnedImplicit source
        (implicitRead participation.productionOccurrence.locatedStep.source) =
          factor ())
    (certificationFactors :
      stageAdvanceFromReturnedImplicit source
        (implicitRead participation.certificationOccurrence.locatedStep.source) =
          factor ()) :
    Empty := by
  rw [productionOccurrenceWaits] at productionFactors
  rw [certificationOccurrenceAdvancesExactly] at certificationFactors
  have impossible :
      some (StageAdvanceState.waiting :
          StageAdvanceState SoundGodelHistoryStage) =
        some (.authorized source.advance) :=
    productionFactors.trans certificationFactors.symm
  cases impossible

/-! ## The target extracted from the authorized observation -/

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
`source` consumes the newest history postulate.  This is the proof-theoretic
necessity property used below; it is stronger than merely storing the
production and certification occurrences beside an unrelated progression. -/
def SourceBoundaryUsesNewestAtAdvance
    (source : SoundGodelHistoryStage) : Prop :=
  ∀ proof : Derivation LogicMode.intuitionistic source.advance.history.theory
      FormulaContext.nil source.producedSentence.scopedFormula,
    historyDerivationUsesNewest proof = true

theorem sourceBoundaryUsesNewestAtAdvance
    (source : SoundGodelHistoryStage) :
    SourceBoundaryUsesNewestAtAdvance source :=
  sourceBoundaryDerivationUsesNewest source

def StageOccurrenceAdvanceDoesNotFactorThroughUnit
    (source : SoundGodelHistoryStage)
    (participation : StagePerimetralParticipation source) : Type :=
  (factor : Unit -> Option (StageAdvanceState SoundGodelHistoryStage)) ->
  stageAdvanceFromReturnedImplicit source
      (implicitRead participation.productionOccurrence.locatedStep.source) =
    factor () ->
  stageAdvanceFromReturnedImplicit source
      (implicitRead participation.certificationOccurrence.locatedStep.source) =
    factor () ->
  Empty

def stageOccurrenceAdvanceDoesNotFactorThroughUnit
    (source : SoundGodelHistoryStage)
    (participation : StagePerimetralParticipation source) :
    StageOccurrenceAdvanceDoesNotFactorThroughUnit source participation :=
  occurrenceAdvanceNotFactorsThroughUnit source participation

/-! ## A tower whose successor is the authorized target -/

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
  let target := certifiedTarget source.1 source.2
  ⟨target, target.perimetralParticipation⟩

theorem ParticipatingGodelHistoryStage.advance_stage_eq
    (source : ParticipatingGodelHistoryStage) :
    source.advance.1 = source.1.advance :=
  certifiedTarget_eq_advance source.1 source.2

/-- The public result of one occurrence-driven history transition.  Its first
component is indexed by the target extracted from the certification readout;
the following components give compatibility, the full Gödel progression, and
the two dependency properties missing from the old product package.  The
product spelling keeps generated dependent recursors small. -/
def CertifiedPerimetralGodelHistoryProgression
    (source : ParticipatingGodelHistoryStage) : Type 1 :=
  StagePerimetralParticipation (certifiedTarget source.1 source.2) ×
  PLift (certifiedTarget source.1 source.2 = source.1.advance) ×
  GodelHistoryProgression source.1 ×
  PLift (SourceBoundaryUsesNewestAtAdvance source.1) ×
  StageOccurrenceAdvanceDoesNotFactorThroughUnit source.1 source.2

def certifiedPerimetralGodelHistoryProgression
    (source : ParticipatingGodelHistoryStage) :
    CertifiedPerimetralGodelHistoryProgression source :=
  let target := certifiedTarget source.1 source.2
  let targetParticipation := target.perimetralParticipation
  let progression := godelHistoryProgression source.1
  ⟨targetParticipation,
    ⟨certifiedTarget_eq_advance source.1 source.2⟩,
    progression,
    ⟨sourceBoundaryUsesNewestAtAdvance source.1⟩,
    stageOccurrenceAdvanceDoesNotFactorThroughUnit source.1 source.2⟩

def CertifiedPerimetralGodelHistoryProgression.progression
    {source : ParticipatingGodelHistoryStage}
    (result : CertifiedPerimetralGodelHistoryProgression source) :
    GodelHistoryProgression source.1 :=
  result.2.2.1

theorem CertifiedPerimetralGodelHistoryProgression.sourceBoundaryUsesNewest
    {source : ParticipatingGodelHistoryStage}
    (result : CertifiedPerimetralGodelHistoryProgression source) :
    SourceBoundaryUsesNewestAtAdvance source.1 :=
  result.2.2.2.1.down

def CertifiedPerimetralGodelHistoryProgression.phaseDoesNotFactorThroughUnit
    {source : ParticipatingGodelHistoryStage}
    (result : CertifiedPerimetralGodelHistoryProgression source) :
    StageOccurrenceAdvanceDoesNotFactorThroughUnit source.1 source.2 :=
  result.2.2.2.2

def CertifiedPerimetralGodelHistoryProgression.target
    {source : ParticipatingGodelHistoryStage}
    (progression : CertifiedPerimetralGodelHistoryProgression source) :
    ParticipatingGodelHistoryStage :=
  ⟨certifiedTarget source.1 source.2, progression.1⟩

theorem CertifiedPerimetralGodelHistoryProgression.target_stage_eq
    {source : ParticipatingGodelHistoryStage}
    (progression : CertifiedPerimetralGodelHistoryProgression source) :
    progression.target.1 = source.1.advance :=
  progression.2.1.down

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
      change certifiedTarget
          (perimetralGodelHistoryStage previous).1
          (perimetralGodelHistoryStage previous).2 =
        (godelHistoryStage previous).advance
      rw [certifiedTarget_eq_advance, ih]

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
#print axioms RelationalPerimeter.HeytingArithmetic.productionOccurrenceAvailableResource
#print axioms RelationalPerimeter.HeytingArithmetic.certificationOccurrenceAvailableResource
#print axioms RelationalPerimeter.HeytingArithmetic.productionOccurrenceAvailableResource_exact
#print axioms RelationalPerimeter.HeytingArithmetic.certificationOccurrenceAvailableResource_exact
#print axioms RelationalPerimeter.HeytingArithmetic.StageAdvanceState
#print axioms RelationalPerimeter.HeytingArithmetic.stageAdvanceKernel
#print axioms RelationalPerimeter.HeytingArithmetic.extendStageFromCertifiedWitness
#print axioms RelationalPerimeter.HeytingArithmetic.stageAdvanceFromAvailableResource
#print axioms RelationalPerimeter.HeytingArithmetic.stageAdvanceFromReturnedImplicit
#print axioms RelationalPerimeter.HeytingArithmetic.retainedResourceRemainsRetained
#print axioms RelationalPerimeter.HeytingArithmetic.productionOccurrenceWaits
#print axioms RelationalPerimeter.HeytingArithmetic.certificationOccurrenceAdvancesExactly
#print axioms RelationalPerimeter.HeytingArithmetic.occurrenceAdvanceNotFactorsThroughUnit
#print axioms RelationalPerimeter.HeytingArithmetic.AuthorizedStageOutcome
#print axioms RelationalPerimeter.HeytingArithmetic.authorizedStageOfOutcome
#print axioms RelationalPerimeter.HeytingArithmetic.authorizedStageOfOutcome_eq
#print axioms RelationalPerimeter.HeytingArithmetic.certificationStageOutcome
#print axioms RelationalPerimeter.HeytingArithmetic.certifiedTarget
#print axioms RelationalPerimeter.HeytingArithmetic.certifiedTarget_eq_advance
#print axioms RelationalPerimeter.HeytingArithmetic.boolOrFalseLeft
#print axioms RelationalPerimeter.HeytingArithmetic.boolOrFalseRight
#print axioms RelationalPerimeter.HeytingArithmetic.historyDerivationUsesNewest
#print axioms RelationalPerimeter.HeytingArithmetic.eraseNewestFreeDerivation
#print axioms RelationalPerimeter.HeytingArithmetic.sourceBoundaryDerivationUsesNewest
#print axioms RelationalPerimeter.HeytingArithmetic.checkedSourceBoundaryDerivationUsesNewest
#print axioms RelationalPerimeter.HeytingArithmetic.SourceBoundaryUsesNewestAtAdvance
#print axioms RelationalPerimeter.HeytingArithmetic.sourceBoundaryUsesNewestAtAdvance
#print axioms RelationalPerimeter.HeytingArithmetic.StageOccurrenceAdvanceDoesNotFactorThroughUnit
#print axioms RelationalPerimeter.HeytingArithmetic.stageOccurrenceAdvanceDoesNotFactorThroughUnit
#print axioms RelationalPerimeter.HeytingArithmetic.ParticipatingGodelHistoryStage
#print axioms RelationalPerimeter.HeytingArithmetic.rootParticipatingGodelHistoryStage
#print axioms RelationalPerimeter.HeytingArithmetic.ParticipatingGodelHistoryStage.advance
#print axioms RelationalPerimeter.HeytingArithmetic.ParticipatingGodelHistoryStage.advance_stage_eq
#print axioms RelationalPerimeter.HeytingArithmetic.CertifiedPerimetralGodelHistoryProgression
#print axioms RelationalPerimeter.HeytingArithmetic.certifiedPerimetralGodelHistoryProgression
#print axioms RelationalPerimeter.HeytingArithmetic.CertifiedPerimetralGodelHistoryProgression.target
#print axioms RelationalPerimeter.HeytingArithmetic.CertifiedPerimetralGodelHistoryProgression.target_stage_eq
#print axioms RelationalPerimeter.HeytingArithmetic.CertifiedPerimetralGodelHistoryProgression.progression
#print axioms RelationalPerimeter.HeytingArithmetic.CertifiedPerimetralGodelHistoryProgression.sourceBoundaryUsesNewest
#print axioms RelationalPerimeter.HeytingArithmetic.CertifiedPerimetralGodelHistoryProgression.phaseDoesNotFactorThroughUnit
#print axioms RelationalPerimeter.HeytingArithmetic.CertifiedPerimetralGodelHistoryProgression.sourceSentenceProofUsesNewest
#print axioms RelationalPerimeter.HeytingArithmetic.certifiedPerimetralGodelHistoryProgression_target_eq_advance
#print axioms RelationalPerimeter.HeytingArithmetic.perimetralGodelHistoryStage
#print axioms RelationalPerimeter.HeytingArithmetic.perimetralGodelHistoryStage_zero
#print axioms RelationalPerimeter.HeytingArithmetic.perimetralGodelHistoryStage_succ
#print axioms RelationalPerimeter.HeytingArithmetic.perimetralGodelHistoryStage_stage_eq
#print axioms RelationalPerimeter.HeytingArithmetic.perimetralGodelHistoryProgressionAt
#print axioms RelationalPerimeter.HeytingArithmetic.perimetralGodelHistoryStage_sourceBoundaryUsesNewest
/- AXIOM_AUDIT_END -/
