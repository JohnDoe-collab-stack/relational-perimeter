import RelationalPerimeter.Constitution.GodelDiagonalPerimetral

set_option linter.defProp false
set_option linter.checkUnivs false

/-!
# Object-arithmetic Gödel correspondence

The imported effective interface is deliberately representation-neutral.  To
make the Godel correspondence checkable without confusing a separate
equivalence datatype with an object-language theorem, the following bridge
fixes the ordinary first-order language of arithmetic.  Its terms contain
zero, successor, addition and multiplication; its formulas contain equality,
falsity, implication, conjunction, universal quantification and existential
quantification with constructive sigma semantics.  Arity is tracked in the
type, so sentences and unary formulas cannot be interchanged.

An arithmetic presentation below supplies executable numbering, numeral
substitution and proof checking.  Its diagonal law is not a semantic equality:
it is a checked proof of the object-language biconditional.  Soundness then
provides the two truth transports, while the proof calculus supplies the two
proof transports.  The historical interface keeps representation of
unprovability as an explicit hypothesis.  The strengthened R1 interface below
instead receives an object proof relation and its pointwise semantic
correctness, constructs provability and unprovability, and derives both
historical laws.  Neither interface receives truth or non-provability of the
produced Godel sentence; both are derived after adaptation to the executed
constitutive chain.
-/

namespace StrongPerimetralTurning

/-! ## Constitutive strengthening outside the foundational module

The historical executed link remains unchanged in `StrongPerimetralTurning`.
This module proves that every complete history of that link pins the canonical
exit, then builds a separate proof-relevant perimeter whose resources contain
the exact production and certified witness.  The arithmetic correspondence
below uses this strengthened presentation; it does not reinterpret the legacy
`Unit` presentation as evidence of global participation. -/

def arithmeticCanonicalExecutedGodelRegimeExit
    (coding : GodelDiagonalSyntax)
    (unprovabilityFormula : coding.UnaryFormula)
    (interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula) :
    ExecutedGodelRegimeExit coding unprovabilityFormula interpretation :=
  executeGodelRegimeExit coding unprovabilityFormula interpretation
    (certifyExecutedGodelWitness coding unprovabilityFormula interpretation
      (executeGodelSentenceProduction
        (executeGodelDiagonalProduction coding unprovabilityFormula)))

def ArithmeticExecutedGodelConstitutiveCanonical
    {coding : GodelDiagonalSyntax}
    {unprovabilityFormula : coding.UnaryFormula}
    {interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula} :
    ExecutedGodelConstitutiveState coding unprovabilityFormula interpretation →
      Prop
  | .received => True
  | .diagonalized diagonal =>
      diagonal =
        executeGodelDiagonalProduction coding unprovabilityFormula
  | .sentenceProduced production =>
      production =
        executeGodelSentenceProduction
          (executeGodelDiagonalProduction coding unprovabilityFormula)
  | .witnessProduced witness =>
      witness =
        certifyExecutedGodelWitness coding unprovabilityFormula interpretation
          (executeGodelSentenceProduction
            (executeGodelDiagonalProduction coding unprovabilityFormula))
  | .regimeExited exit =>
      exit =
        arithmeticCanonicalExecutedGodelRegimeExit coding
          unprovabilityFormula interpretation

theorem arithmeticExecutedGodelHistory_isCanonical
    {coding : GodelDiagonalSyntax}
    {unprovabilityFormula : coding.UnaryFormula}
    {interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula}
    {state :
      ExecutedGodelConstitutiveState coding unprovabilityFormula
        interpretation}
    (history :
      History (@ExecutedGodelConstitutiveStep coding unprovabilityFormula
        interpretation) .received state) :
    ArithmeticExecutedGodelConstitutiveCanonical state := by
  induction history with
  | root => trivial
  | extend _ step inductionHypothesis =>
      cases step with
      | diagonalize => rfl
      | selfApply diagonal =>
          simp only [ArithmeticExecutedGodelConstitutiveCanonical]
            at inductionHypothesis ⊢
          rw [inductionHypothesis]
      | certify production =>
          simp only [ArithmeticExecutedGodelConstitutiveCanonical]
            at inductionHypothesis ⊢
          rw [inductionHypothesis]
      | «continue» witness =>
          simp only [ArithmeticExecutedGodelConstitutiveCanonical]
            at inductionHypothesis ⊢
          rw [inductionHypothesis]
          rfl

theorem ExecutedGodelDiagonalPerimetralLink.arithmeticHistoryPinsExit
    {coding : GodelDiagonalSyntax}
    {unprovabilityFormula : coding.UnaryFormula}
    {interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula}
    (link :
      ExecutedGodelDiagonalPerimetralLink coding unprovabilityFormula
        interpretation) :
    link.exit =
      arithmeticCanonicalExecutedGodelRegimeExit coding
        unprovabilityFormula interpretation :=
  arithmeticExecutedGodelHistory_isCanonical link.history

/- The complete executed history contains more information than its terminal
   state.  This certificate extracts the actual `selfApply` and `certify`
   occurrences from that history, together with the resources carried by the
   intervening steps.  The occurrences are retained as data; their identity is
   not replaced by an equality between their outputs. -/
structure ArithmeticExecutedGodelHistoryOccurrences
    {coding : GodelDiagonalSyntax}
    {unprovabilityFormula : coding.UnaryFormula}
    {interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula}
    (link : ExecutedGodelDiagonalPerimetralLink coding unprovabilityFormula
      interpretation) : Type _ where
  diagonal : ExecutedGodelDiagonalProduction coding unprovabilityFormula
  production : ExecutedGodelSentenceProduction coding unprovabilityFormula
  witness : ExecutedGodelWitness coding unprovabilityFormula interpretation
  diagonalIsCanonical :
    diagonal = executeGodelDiagonalProduction coding unprovabilityFormula
  productionIsSelfApplication :
    production = executeGodelSentenceProduction diagonal
  witnessIsCertification :
    witness = certifyExecutedGodelWitness coding unprovabilityFormula
      interpretation production
  exitIsContinuation :
    link.exit = executeGodelRegimeExit coding unprovabilityFormula
      interpretation witness
  selfApplyOccurrence : History.Occurrence link.history
  selfApplyOccurrenceIsExact :
    selfApplyOccurrence.locatedStep =
      (⟨.diagonalized diagonal,
        .sentenceProduced (executeGodelSentenceProduction diagonal),
        .selfApply diagonal⟩ :
        History.LocatedStep
          (@ExecutedGodelConstitutiveStep coding unprovabilityFormula
            interpretation))
  certifyOccurrence : History.Occurrence link.history
  certifyOccurrenceIsExact :
    certifyOccurrence.locatedStep =
      (⟨.sentenceProduced production,
        .witnessProduced
          (certifyExecutedGodelWitness coding unprovabilityFormula
            interpretation production),
        .certify production⟩ :
        History.LocatedStep
          (@ExecutedGodelConstitutiveStep coding unprovabilityFormula
            interpretation))
  selfApplyNextCertify :
    History.OccurrenceNext selfApplyOccurrence certifyOccurrence

def ExecutedGodelDiagonalPerimetralLink.arithmeticHistoryOccurrences
    {coding : GodelDiagonalSyntax}
    {unprovabilityFormula : coding.UnaryFormula}
    {interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula}
    (link : ExecutedGodelDiagonalPerimetralLink coding unprovabilityFormula
      interpretation) :
    ArithmeticExecutedGodelHistoryOccurrences link := by
  cases link with
  | mk exit history =>
      cases history with
      | extend beforeContinue continueStep =>
          cases continueStep with
          | «continue» witness =>
              cases beforeContinue with
              | extend beforeCertify certifyStep =>
                  cases certifyStep with
                  | certify production =>
                      cases beforeCertify with
                      | extend beforeSelfApply selfApplyStep =>
                          cases selfApplyStep with
                          | selfApply diagonal =>
                              cases beforeSelfApply with
                              | extend beforeDiagonalize diagonalizeStep =>
                                  cases diagonalizeStep with
                                  | diagonalize =>
                                      cases beforeDiagonalize with
                                      | root =>
                                          exact
                                            { diagonal :=
                                                executeGodelDiagonalProduction
                                                  coding unprovabilityFormula
                                              production :=
                                                executeGodelSentenceProduction
                                                  (executeGodelDiagonalProduction
                                                    coding unprovabilityFormula)
                                              witness :=
                                                certifyExecutedGodelWitness
                                                  coding unprovabilityFormula
                                                  interpretation
                                                  (executeGodelSentenceProduction
                                                    (executeGodelDiagonalProduction
                                                      coding unprovabilityFormula))
                                              diagonalIsCanonical := rfl
                                              productionIsSelfApplication := rfl
                                              witnessIsCertification := rfl
                                              exitIsContinuation := rfl
                                              selfApplyOccurrence :=
                                                .earlier (.earlier .last)
                                              selfApplyOccurrenceIsExact := rfl
                                              certifyOccurrence :=
                                                .earlier .last
                                              certifyOccurrenceIsExact := rfl
                                              selfApplyNextCertify :=
                                                .earlier_earlier .previous_last }
                                      | extend _ impossible =>
                                          exact nomatch impossible

inductive ArithmeticExecutedGodelPerimeterResource
    {coding : GodelDiagonalSyntax}
    {unprovabilityFormula : coding.UnaryFormula}
    {interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula}
    (witness :
      ExecutedGodelWitness coding unprovabilityFormula interpretation) : Type _
  | produced
      (production :
        ExecutedGodelSentenceProduction coding unprovabilityFormula) :
      ArithmeticExecutedGodelPerimeterResource witness
  | certified
      (certifiedWitness :
        ExecutedGodelWitness coding unprovabilityFormula interpretation) :
      ArithmeticExecutedGodelPerimeterResource witness
  | continued
      (retainedWitness :
        ExecutedGodelWitness coding unprovabilityFormula interpretation) :
      ArithmeticExecutedGodelPerimeterResource witness

inductive ArithmeticExecutedGodelPerimeterCompatibility
    {coding : GodelDiagonalSyntax}
    {unprovabilityFormula : coding.UnaryFormula}
    {interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula}
    (witness :
      ExecutedGodelWitness coding unprovabilityFormula interpretation) :
    ArithmeticExecutedGodelPerimeterResource witness →
      ArithmeticExecutedGodelPerimeterResource witness → Type _
  | atResource (resource : ArithmeticExecutedGodelPerimeterResource witness) :
      ArithmeticExecutedGodelPerimeterCompatibility witness resource resource
  | productionToCertification :
      ArithmeticExecutedGodelPerimeterCompatibility witness
        (.produced witness.production) (.certified witness)
  | certificationToContinuation :
      ArithmeticExecutedGodelPerimeterCompatibility witness
        (.certified witness) (.continued witness)
  | continuationToProduction :
      ArithmeticExecutedGodelPerimeterCompatibility witness
        (.continued witness) (.produced witness.production)

def arithmeticExecutedGodelNode
    {coding : GodelDiagonalSyntax}
    {unprovabilityFormula : coding.UnaryFormula}
    {interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula}
    (witness :
      ExecutedGodelWitness coding unprovabilityFormula interpretation)
    (resource : ArithmeticExecutedGodelPerimeterResource witness) :
    LocalNode (ArithmeticExecutedGodelPerimeterResource witness)
      (ArithmeticExecutedGodelPerimeterResource witness)
      (ArithmeticExecutedGodelPerimeterCompatibility witness)
      (ExecutedGodelWitness coding unprovabilityFormula interpretation)
      (fun candidate => PLift (candidate = witness)) :=
  { explicit := resource
    implicit := resource
    difference := witness
    provenance := ⟨rfl⟩
    internallyCompatible := .atResource resource }

def arithmeticExecutedGodelPerimeter
    {coding : GodelDiagonalSyntax}
    {unprovabilityFormula : coding.UnaryFormula}
    {interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula}
    (witness :
      ExecutedGodelWitness coding unprovabilityFormula interpretation) :
    PerimeterSpine (ArithmeticExecutedGodelPerimeterCompatibility witness)
      (arithmeticExecutedGodelNode witness (.produced witness.production)) :=
  .advance
    (nextNode := arithmeticExecutedGodelNode witness (.certified witness))
    .productionToCertification
    (.advance
      (nextNode := arithmeticExecutedGodelNode witness (.continued witness))
      .certificationToContinuation
      (.boundary
        (arithmeticExecutedGodelNode witness (.continued witness))))

def arithmeticExecutedGodelProductionPosition
    {coding : GodelDiagonalSyntax}
    {unprovabilityFormula : coding.UnaryFormula}
    {interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula}
    (witness :
      ExecutedGodelWitness coding unprovabilityFormula interpretation) :
    NonClosingPosition (arithmeticExecutedGodelPerimeter witness) := by
  unfold arithmeticExecutedGodelPerimeter
  exact .here

def arithmeticExecutedGodelCertificationPosition
    {coding : GodelDiagonalSyntax}
    {unprovabilityFormula : coding.UnaryFormula}
    {interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula}
    (witness :
      ExecutedGodelWitness coding unprovabilityFormula interpretation) :
    NonClosingPosition (arithmeticExecutedGodelPerimeter witness) := by
  unfold arithmeticExecutedGodelPerimeter
  exact .later .here

def arithmeticExecutedGodelProductionPrecedesCertification
    {coding : GodelDiagonalSyntax}
    {unprovabilityFormula : coding.UnaryFormula}
    {interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula}
    (witness :
      ExecutedGodelWitness coding unprovabilityFormula interpretation) :
    NonClosingPrecedes (arithmeticExecutedGodelPerimeter witness)
      (arithmeticExecutedGodelProductionPosition witness)
      (arithmeticExecutedGodelCertificationPosition witness) := by
  unfold arithmeticExecutedGodelPerimeter
    arithmeticExecutedGodelProductionPosition
    arithmeticExecutedGodelCertificationPosition
  exact .here_later .here

def arithmeticExecutedGodelCircularPresentation
    {coding : GodelDiagonalSyntax}
    {unprovabilityFormula : coding.UnaryFormula}
    {interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula}
    (witness :
      ExecutedGodelWitness coding unprovabilityFormula interpretation) :
    CircularPresentation :=
  { Explicit := ArithmeticExecutedGodelPerimeterResource witness
    Implicit := ArithmeticExecutedGodelPerimeterResource witness
    Compatible := ArithmeticExecutedGodelPerimeterCompatibility witness
    Difference :=
      ExecutedGodelWitness coding unprovabilityFormula interpretation
    Provenance := fun candidate => PLift (candidate = witness)
    initialNode :=
      arithmeticExecutedGodelNode witness (.produced witness.production)
    perimeter := arithmeticExecutedGodelPerimeter witness
    perimeterPositive := by
      unfold arithmeticExecutedGodelPerimeter
      exact .here
    finalJunction := by
      unfold arithmeticExecutedGodelPerimeter
      exact .continuationToProduction
    Endpoint := Type _
    leftEndpoint := interpretation.Truth witness.production.sentence
    rightEndpoint := coding.Proof witness.production.sentence
    leftPole := fun candidate =>
      interpretation.Truth candidate.production.sentence
    rightPole := fun candidate => coding.Proof candidate.production.sentence
    initialLeftPole := rfl
    initialRightPole := rfl
    TotalLoop := ExecutedGodelTotalLoop witness
    closeFromIdentification := fun equality =>
      { identifiesProducedTruthAndProof := equality }
    loopContractsInitialDifference := fun loop =>
      loop.identifiesProducedTruthAndProof
    rejectInitialContraction := fun _ equality =>
      Empty.elim
        (witness.unprovable (Eq.mp equality witness.trueWitness)) }

/-! ## Causal participation and provenanced closure

The generic closure meaning remains unchanged.  The layer below records the
specific positive continuation produced by the strong turning certificate and
the exact final interpretation of that continuation.  Its refined contraction
does not choose the executed witness directly: it reads a candidate from the
historical provenance record and can identify that candidate with the produced
witness only by consuming the recorded provenance. -/

abbrev ArithmeticExecutedGodelPresentation
    {coding : GodelDiagonalSyntax}
    {unprovabilityFormula : coding.UnaryFormula}
    {interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula}
    (link : ExecutedGodelDiagonalPerimetralLink coding unprovabilityFormula
      interpretation) : CircularPresentation :=
  arithmeticExecutedGodelCircularPresentation link.exit.witness

def StrongPerimetralTurningCertificate.freelyGeneratedStrictContinuation
    {P : CircularPresentation}
    (turning : StrongPerimetralTurningCertificate P) :
    StrictConstitutivePrefix turning.deployment
      (appendGenerated turning.deployment
        turning.continuesFreelyBeyondPerimeter) :=
  { continuation :=
      { predecessor := turning.deployment.endpoint
        priorHistory := .root
        lastStep := turning.continuesFreelyBeyondPerimeter.2 }
    historyExact := rfl }

def recordedSourceProvenance
    {P : CircularPresentation}
    {difference : ReturnedDifference P}
    {candidate : P.Difference}
    (differenceExact : difference = .source candidate)
    (provenance : ReturnedProvenance P difference) :
    P.Provenance candidate := by
  cases differenceExact
  cases provenance with
  | source sourceProvenance => exact sourceProvenance

structure ArithmeticExecutedGodelCausalParticipation
    {coding : GodelDiagonalSyntax}
    {unprovabilityFormula : coding.UnaryFormula}
    {interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula}
    (link : ExecutedGodelDiagonalPerimetralLink coding unprovabilityFormula
      interpretation) : Type _ where
  historyPinsConsumedExit :
    link.exit = arithmeticCanonicalExecutedGodelRegimeExit coding
      unprovabilityFormula interpretation
  turning : StrongPerimetralTurningCertificate
    (ArithmeticExecutedGodelPresentation link)
  turningDeploymentIsPerimeter :
    turning.deployment =
      perimeterDeployment (ArithmeticExecutedGodelPresentation link)
  continuation : RootedGeneratedHistory
    (ArithmeticExecutedGodelPresentation link)
  continuationIsTurningExtension :
    continuation =
      appendGenerated turning.deployment
        turning.continuesFreelyBeyondPerimeter
  continuationIsCanonical :
    continuation =
      oneStepAfterPerimeter (ArithmeticExecutedGodelPresentation link)
  labelled : FaithfullyLabelledPerimeterExtension
    (ArithmeticExecutedGodelPresentation link) continuation
  positive : PositiveContinuation labelled.extension
  productionOccurrence : History.Occurrence continuation.history
  productionOccurrenceIsExact :
    productionOccurrence =
      labelled.extension.oldOccurrence
        (arithmeticExecutedGodelProductionPosition link.exit.witness)
  certificationOccurrence : History.Occurrence continuation.history
  certificationOccurrenceIsExact :
    certificationOccurrence =
      labelled.extension.oldOccurrence
        (arithmeticExecutedGodelCertificationPosition link.exit.witness)
  productionPrecedesCertification :
    History.OccurrencePrecedes productionOccurrence certificationOccurrence
  residualOccurrence : History.Occurrence labelled.continuation
  residualOccurrenceIsPositive :
    residualOccurrence =
      transportOccurrence positive.historyExact.symm
        positive.path.lastOccurrence
  residualDiffersFromProduction :
    labelled.extension.oldOccurrence
        (arithmeticExecutedGodelProductionPosition link.exit.witness) ≠
      labelled.extension.newOccurrence residualOccurrence
  residualDiffersFromCertification :
    labelled.extension.oldOccurrence
        (arithmeticExecutedGodelCertificationPosition link.exit.witness) ≠
      labelled.extension.newOccurrence residualOccurrence
  finalInterpretation : FinalClosureInterpretation
    (ArithmeticExecutedGodelPresentation link) continuation
  finalInterpretationIsCanonical :
    finalInterpretation =
      finalClosureInterpretation (finalBoundaryOccurrence labelled positive)

def ExecutedGodelDiagonalPerimetralLink.arithmeticCausalParticipation
    {coding : GodelDiagonalSyntax}
    {unprovabilityFormula : coding.UnaryFormula}
    {interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula}
    (link : ExecutedGodelDiagonalPerimetralLink coding unprovabilityFormula
      interpretation) :
    ArithmeticExecutedGodelCausalParticipation link := by
  let P := ArithmeticExecutedGodelPresentation link
  let turning := strongPerimetralTurning P
  let continuation := oneStepAfterPerimeter P
  let labelled := oneStepFaithfullyLabelledExtension P
  let positive := oneStepAfterPerimeter_positiveContinuation P
  let productionOccurrence :=
    labelled.extension.oldOccurrence
      (arithmeticExecutedGodelProductionPosition link.exit.witness)
  let certificationOccurrence :=
    labelled.extension.oldOccurrence
      (arithmeticExecutedGodelCertificationPosition link.exit.witness)
  let residualOccurrence :=
    transportOccurrence positive.historyExact.symm positive.path.lastOccurrence
  exact
    { historyPinsConsumedExit := link.arithmeticHistoryPinsExit
      turning := turning
      turningDeploymentIsPerimeter := rfl
      continuation := continuation
      continuationIsTurningExtension := rfl
      continuationIsCanonical := rfl
      labelled := labelled
      positive := positive
      productionOccurrence := productionOccurrence
      productionOccurrenceIsExact := rfl
      certificationOccurrence := certificationOccurrence
      certificationOccurrenceIsExact := rfl
      productionPrecedesCertification := by
        exact labelled.extension.toExactNonClosingRealization.preservesPrecedence
          (arithmeticExecutedGodelProductionPrecedesCertification
            link.exit.witness)
      residualOccurrence := residualOccurrence
      residualOccurrenceIsPositive := rfl
      residualDiffersFromProduction :=
        labelled.extension.old_new_occurrences_disjoint _ _
      residualDiffersFromCertification :=
        labelled.extension.old_new_occurrences_disjoint _ _
      finalInterpretation :=
        turning.finalInterpretationFromPositive labelled positive
      finalInterpretationIsCanonical := rfl }

/- A correspondence keeps the executed and perimetral occurrences as distinct
   data.  The two equalities below identify only the resources transmitted
   between them: the output of `selfApply` is the production at the first
   perimeter position, and the output of `certify` is the witness at the
   second position. -/
structure ArithmeticExecutedGodelOccurrenceCorrespondence
    {coding : GodelDiagonalSyntax}
    {unprovabilityFormula : coding.UnaryFormula}
    {interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula}
    {link : ExecutedGodelDiagonalPerimetralLink coding unprovabilityFormula
      interpretation}
    (participation : ArithmeticExecutedGodelCausalParticipation link) : Type _
    where
  executed : ArithmeticExecutedGodelHistoryOccurrences link
  productionOccurrenceIsExact :
    participation.productionOccurrence =
      participation.labelled.extension.oldOccurrence
        (arithmeticExecutedGodelProductionPosition link.exit.witness)
  certificationOccurrenceIsExact :
    participation.certificationOccurrence =
      participation.labelled.extension.oldOccurrence
        (arithmeticExecutedGodelCertificationPosition link.exit.witness)
  selfApplyConstitutesProduction :
    executed.production = link.exit.witness.production
  certifyConstitutesCertification :
    executed.witness = link.exit.witness
  executedSelfApplyNextCertify :
    History.OccurrenceNext executed.selfApplyOccurrence
      executed.certifyOccurrence
  perimetralProductionPrecedesCertification :
    History.OccurrencePrecedes participation.productionOccurrence
      participation.certificationOccurrence

def ArithmeticExecutedGodelCausalParticipation.executedOccurrenceCorrespondence
    {coding : GodelDiagonalSyntax}
    {unprovabilityFormula : coding.UnaryFormula}
    {interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula}
    {link : ExecutedGodelDiagonalPerimetralLink coding unprovabilityFormula
      interpretation}
    (participation : ArithmeticExecutedGodelCausalParticipation link) :
    ArithmeticExecutedGodelOccurrenceCorrespondence participation := by
  let executed := link.arithmeticHistoryOccurrences
  have witnessExact : executed.witness = link.exit.witness := by
    exact
      (congrArg ExecutedGodelRegimeExit.witness
        executed.exitIsContinuation).symm
  have certificationRetainsProduction :
      executed.witness.production = executed.production := by
    exact congrArg ExecutedGodelWitness.production
      executed.witnessIsCertification
  have productionExact :
      executed.production = link.exit.witness.production :=
    certificationRetainsProduction.symm.trans
      (congrArg ExecutedGodelWitness.production witnessExact)
  exact
    { executed := executed
      productionOccurrenceIsExact :=
        participation.productionOccurrenceIsExact
      certificationOccurrenceIsExact :=
        participation.certificationOccurrenceIsExact
      selfApplyConstitutesProduction := productionExact
      certifyConstitutesCertification := witnessExact
      executedSelfApplyNextCertify := executed.selfApplyNextCertify
      perimetralProductionPrecedesCertification :=
        participation.productionPrecedesCertification }

def ArithmeticExecutedGodelCausalParticipation.strictTurningContinuation
    {coding : GodelDiagonalSyntax}
    {unprovabilityFormula : coding.UnaryFormula}
    {interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula}
    {link : ExecutedGodelDiagonalPerimetralLink coding unprovabilityFormula
      interpretation}
    (participation : ArithmeticExecutedGodelCausalParticipation link) :
    StrictConstitutivePrefix
      (perimeterDeployment (ArithmeticExecutedGodelPresentation link))
      participation.continuation := by
  rw [participation.continuationIsTurningExtension]
  rw [← participation.turningDeploymentIsPerimeter]
  exact participation.turning.freelyGeneratedStrictContinuation

def ArithmeticExecutedGodelCausalParticipation.locallyExact
    {coding : GodelDiagonalSyntax}
    {unprovabilityFormula : coding.UnaryFormula}
    {interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula}
    {link : ExecutedGodelDiagonalPerimetralLink coding unprovabilityFormula
      interpretation}
    (participation : ArithmeticExecutedGodelCausalParticipation link) :
    ExactNonClosingRealization (ArithmeticExecutedGodelPresentation link)
      participation.continuation :=
  participation.labelled.extension.toExactNonClosingRealization

theorem ArithmeticExecutedGodelCausalParticipation.recordedDifferenceIsSource
    {coding : GodelDiagonalSyntax}
    {unprovabilityFormula : coding.UnaryFormula}
    {interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula}
    {link : ExecutedGodelDiagonalPerimetralLink coding unprovabilityFormula
      interpretation}
    (participation : ArithmeticExecutedGodelCausalParticipation link) :
    participation.finalInterpretation.provenanceRecord.recordedDifference =
      .source
        (ArithmeticExecutedGodelPresentation link).perimeter.finalNode.difference := by
  change differenceAtCursor participation.finalInterpretation.boundary.source.1 = _
  rw [participation.finalInterpretation.boundary.source_cursor_is_boundary]
  rfl

def ArithmeticExecutedGodelCausalParticipation.historicalProvenance
    {coding : GodelDiagonalSyntax}
    {unprovabilityFormula : coding.UnaryFormula}
    {interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula}
    {link : ExecutedGodelDiagonalPerimetralLink coding unprovabilityFormula
      interpretation}
    (participation : ArithmeticExecutedGodelCausalParticipation link) :
    (ArithmeticExecutedGodelPresentation link).Provenance
      (ArithmeticExecutedGodelPresentation link).perimeter.finalNode.difference :=
  recordedSourceProvenance participation.recordedDifferenceIsSource
    participation.finalInterpretation.provenanceRecord.recordedProvenance

structure ArithmeticExecutedGodelCausalContraction
    {coding : GodelDiagonalSyntax}
    {unprovabilityFormula : coding.UnaryFormula}
    {interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula}
    {link : ExecutedGodelDiagonalPerimetralLink coding unprovabilityFormula
      interpretation}
    (participation : ArithmeticExecutedGodelCausalParticipation link) where
  candidate : ExecutedGodelWitness coding unprovabilityFormula interpretation
  recordedDifferenceIsCandidate :
    participation.finalInterpretation.provenanceRecord.recordedDifference =
      .source candidate
  poleContraction :
    interpretation.Truth candidate.production.sentence =
      coding.Proof candidate.production.sentence

/- The diagnostic notion is independent of Gödel witnesses and perimetral
   presentations.  The causal closure below attaches this same sentence-local
   predicate to a produced history; tests can apply it unchanged to a decided
   sentence. -/
abbrev DirectedSemanticCompletenessAt
    {Sentence : Type}
    (Truth Proof : Sentence → Type)
    (sentence : Sentence) : Type :=
  Truth sentence → Proof sentence

/- The directed closure is the exact semantic-completeness obligation rejected
   by the produced fixed point.  Unlike the historical pole identification, it
   asks only for a proof producer at the candidate actually read from the final
   interpretation.  The recorded difference and its provenance remain part of
   the contraction, so the candidate cannot be replaced independently. -/
structure ArithmeticExecutedGodelDirectedContraction
    {coding : GodelDiagonalSyntax}
    {unprovabilityFormula : coding.UnaryFormula}
    {interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula}
    {link : ExecutedGodelDiagonalPerimetralLink coding unprovabilityFormula
      interpretation}
    (participation : ArithmeticExecutedGodelCausalParticipation link) where
  candidate : ExecutedGodelWitness coding unprovabilityFormula interpretation
  recordedDifferenceIsCandidate :
    participation.finalInterpretation.provenanceRecord.recordedDifference =
      .source candidate
  producedCompleteness :
    DirectedSemanticCompletenessAt interpretation.Truth coding.Proof
      candidate.production.sentence

abbrev ArithmeticExecutedGodelCausalClosureMeaning
    {coding : GodelDiagonalSyntax}
    {unprovabilityFormula : coding.UnaryFormula}
    {interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula}
    {link : ExecutedGodelDiagonalPerimetralLink coding unprovabilityFormula
      interpretation}
    (participation : ArithmeticExecutedGodelCausalParticipation link) :
    Type _ :=
  StrictConstitutivePrefix
      (perimeterDeployment (ArithmeticExecutedGodelPresentation link))
      participation.continuation →
    ArithmeticExecutedGodelCausalContraction participation

abbrev ArithmeticExecutedGodelDirectedClosureMeaning
    {coding : GodelDiagonalSyntax}
    {unprovabilityFormula : coding.UnaryFormula}
    {interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula}
    {link : ExecutedGodelDiagonalPerimetralLink coding unprovabilityFormula
      interpretation}
    (participation : ArithmeticExecutedGodelCausalParticipation link) :
    Type _ :=
  StrictConstitutivePrefix
      (perimeterDeployment (ArithmeticExecutedGodelPresentation link))
      participation.continuation →
    ArithmeticExecutedGodelDirectedContraction participation

def ArithmeticExecutedGodelCausalParticipation.circularClosureToCausalClosure
    {coding : GodelDiagonalSyntax}
    {unprovabilityFormula : coding.UnaryFormula}
    {interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula}
    {link : ExecutedGodelDiagonalPerimetralLink coding unprovabilityFormula
      interpretation}
    (participation : ArithmeticExecutedGodelCausalParticipation link) :
    CircularClosureMeaning (ArithmeticExecutedGodelPresentation link)
        participation.continuation →
      ArithmeticExecutedGodelCausalClosureMeaning participation := by
  intro closure strict
  let loop := closure strict
  let candidate :=
    (ArithmeticExecutedGodelPresentation link).perimeter.finalNode.difference
  have differenceExact :
      participation.finalInterpretation.provenanceRecord.recordedDifference =
        .source candidate :=
    participation.recordedDifferenceIsSource
  let provenance : PLift (candidate = link.exit.witness) :=
    recordedSourceProvenance differenceExact
      participation.finalInterpretation.provenanceRecord.recordedProvenance
  have contraction :
      interpretation.Truth candidate.production.sentence =
        coding.Proof candidate.production.sentence := by
    cases provenance.down
    exact loop.identifiesProducedTruthAndProof
  exact
    { candidate := candidate
      recordedDifferenceIsCandidate := differenceExact
      poleContraction := contraction }

def ArithmeticExecutedGodelCausalParticipation.causalClosureToCircularClosure
    {coding : GodelDiagonalSyntax}
    {unprovabilityFormula : coding.UnaryFormula}
    {interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula}
    {link : ExecutedGodelDiagonalPerimetralLink coding unprovabilityFormula
      interpretation}
    (participation : ArithmeticExecutedGodelCausalParticipation link) :
    ArithmeticExecutedGodelCausalClosureMeaning participation →
      CircularClosureMeaning (ArithmeticExecutedGodelPresentation link)
        participation.continuation := by
  intro closure strict
  rcases closure strict with ⟨candidate, differenceExact, contraction⟩
  have provenance : PLift (candidate = link.exit.witness) :=
    recordedSourceProvenance differenceExact
      participation.finalInterpretation.provenanceRecord.recordedProvenance
  cases provenance.down
  exact { identifiesProducedTruthAndProof := contraction }

def ArithmeticExecutedGodelCausalParticipation.causalClosureContraction
    {coding : GodelDiagonalSyntax}
    {unprovabilityFormula : coding.UnaryFormula}
    {interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula}
    {link : ExecutedGodelDiagonalPerimetralLink coding unprovabilityFormula
      interpretation}
    (participation : ArithmeticExecutedGodelCausalParticipation link)
    (closure : ArithmeticExecutedGodelCausalClosureMeaning participation) :
    ArithmeticExecutedGodelCausalContraction participation :=
  closure participation.strictTurningContinuation

def ArithmeticExecutedGodelCausalParticipation.causalClosureToDirectedClosure
    {coding : GodelDiagonalSyntax}
    {unprovabilityFormula : coding.UnaryFormula}
    {interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula}
    {link : ExecutedGodelDiagonalPerimetralLink coding unprovabilityFormula
      interpretation}
    (participation : ArithmeticExecutedGodelCausalParticipation link) :
    ArithmeticExecutedGodelCausalClosureMeaning participation →
      ArithmeticExecutedGodelDirectedClosureMeaning participation := by
  intro closure strict
  rcases closure strict with
    ⟨candidate, differenceExact, contraction⟩
  exact
    { candidate := candidate
      recordedDifferenceIsCandidate := differenceExact
      producedCompleteness := fun truthWitness =>
        Eq.mp contraction truthWitness }

def ArithmeticExecutedGodelCausalParticipation.directedClosureContraction
    {coding : GodelDiagonalSyntax}
    {unprovabilityFormula : coding.UnaryFormula}
    {interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula}
    {link : ExecutedGodelDiagonalPerimetralLink coding unprovabilityFormula
      interpretation}
    (participation : ArithmeticExecutedGodelCausalParticipation link)
    (closure : ArithmeticExecutedGodelDirectedClosureMeaning participation) :
    ArithmeticExecutedGodelDirectedContraction participation :=
  closure participation.strictTurningContinuation

def ArithmeticExecutedGodelCausalParticipation.directedClosureToProducedCompleteness
    {coding : GodelDiagonalSyntax}
    {unprovabilityFormula : coding.UnaryFormula}
    {interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula}
    {link : ExecutedGodelDiagonalPerimetralLink coding unprovabilityFormula
      interpretation}
    (participation : ArithmeticExecutedGodelCausalParticipation link) :
    ArithmeticExecutedGodelDirectedClosureMeaning participation →
      ExecutedGodelProducedCompleteness link.exit.witness := by
  intro closure truthWitness
  rcases participation.directedClosureContraction closure with
    ⟨candidate, differenceExact, completeness⟩
  have provenance : PLift (candidate = link.exit.witness) :=
    recordedSourceProvenance differenceExact
      participation.finalInterpretation.provenanceRecord.recordedProvenance
  cases provenance.down
  exact completeness truthWitness

def ArithmeticExecutedGodelCausalParticipation.causalClosureToProducedCompleteness
    {coding : GodelDiagonalSyntax}
    {unprovabilityFormula : coding.UnaryFormula}
    {interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula}
    {link : ExecutedGodelDiagonalPerimetralLink coding unprovabilityFormula
      interpretation}
    (participation : ArithmeticExecutedGodelCausalParticipation link) :
    ArithmeticExecutedGodelCausalClosureMeaning participation →
      ExecutedGodelProducedCompleteness link.exit.witness :=
  fun closure =>
    participation.directedClosureToProducedCompleteness
      (participation.causalClosureToDirectedClosure closure)

def ArithmeticExecutedGodelCausalParticipation.rejectDirectedClosure
    {coding : GodelDiagonalSyntax}
    {unprovabilityFormula : coding.UnaryFormula}
    {interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula}
    {link : ExecutedGodelDiagonalPerimetralLink coding unprovabilityFormula
      interpretation}
    (participation : ArithmeticExecutedGodelCausalParticipation link) :
    ArithmeticExecutedGodelDirectedClosureMeaning participation → Empty :=
  fun closure =>
    interpretation.fixedPoint_rejectsProducedCompleteness
      link.exit.witness.production.sentence link.exit.witness.fixedPoint
      (participation.directedClosureToProducedCompleteness closure)

def ArithmeticExecutedGodelCausalParticipation.rejectCausalClosure
    {coding : GodelDiagonalSyntax}
    {unprovabilityFormula : coding.UnaryFormula}
    {interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula}
    {link : ExecutedGodelDiagonalPerimetralLink coding unprovabilityFormula
      interpretation}
    (participation : ArithmeticExecutedGodelCausalParticipation link) :
    ArithmeticExecutedGodelCausalClosureMeaning participation → Empty :=
  fun closure =>
    participation.rejectDirectedClosure
      (participation.causalClosureToDirectedClosure closure)

def ArithmeticExecutedGodelCausalParticipation.rejectSpecifiedClosure
    {coding : GodelDiagonalSyntax}
    {unprovabilityFormula : coding.UnaryFormula}
    {interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula}
    {link : ExecutedGodelDiagonalPerimetralLink coding unprovabilityFormula
      interpretation}
    (participation : ArithmeticExecutedGodelCausalParticipation link) :
    CircularClosureMeaning (ArithmeticExecutedGodelPresentation link)
        participation.continuation → Empty :=
  fun closure =>
    participation.rejectCausalClosure
      (participation.circularClosureToCausalClosure closure)

structure ArithmeticExecutedGodelRegimeParticipation
    {coding : GodelDiagonalSyntax}
    {unprovabilityFormula : coding.UnaryFormula}
    {interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula}
    (witness :
      ExecutedGodelWitness coding unprovabilityFormula interpretation) where
  continuation :
    RootedGeneratedHistory
      (arithmeticExecutedGodelCircularPresentation witness)
  continuationIsCanonical :
    continuation =
      oneStepAfterPerimeter
        (arithmeticExecutedGodelCircularPresentation witness)
  locallyExact :
    ExactNonClosingRealization
      (arithmeticExecutedGodelCircularPresentation witness) continuation

def arithmeticExecutedGodelRegimeParticipation
    {coding : GodelDiagonalSyntax}
    {unprovabilityFormula : coding.UnaryFormula}
    {interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula}
    (witness :
      ExecutedGodelWitness coding unprovabilityFormula interpretation) :
    ArithmeticExecutedGodelRegimeParticipation witness :=
  { continuation :=
      oneStepAfterPerimeter
        (arithmeticExecutedGodelCircularPresentation witness)
    continuationIsCanonical := rfl
    locallyExact :=
      oneStepAfterPerimeter_nonClosingRealization
        (arithmeticExecutedGodelCircularPresentation witness) }

def ArithmeticExecutedGodelRegimeParticipation.globalClosureToProducedCompleteness
    {coding : GodelDiagonalSyntax}
    {unprovabilityFormula : coding.UnaryFormula}
    {interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula}
    {witness :
      ExecutedGodelWitness coding unprovabilityFormula interpretation}
    (participation : ArithmeticExecutedGodelRegimeParticipation witness) :
    CircularClosureMeaning
        (arithmeticExecutedGodelCircularPresentation witness)
        participation.continuation →
      ExecutedGodelProducedCompleteness witness := by
  intro closure
  have strictContinuation :
      StrictConstitutivePrefix
        (perimeterDeployment
          (arithmeticExecutedGodelCircularPresentation witness))
        participation.continuation := by
    rw [participation.continuationIsCanonical]
    exact
      oneStepAfterPerimeterStrict
        (arithmeticExecutedGodelCircularPresentation witness)
  exact (closure strictContinuation).toProducedCompleteness

structure ArithmeticExecutedGodelGlobalParticipation
    {coding : GodelDiagonalSyntax}
    {unprovabilityFormula : coding.UnaryFormula}
    {interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula}
    (link :
      ExecutedGodelDiagonalPerimetralLink coding unprovabilityFormula
        interpretation) : Type _ where
  historyPinsConsumedExit :
    link.exit =
      arithmeticCanonicalExecutedGodelRegimeExit coding
        unprovabilityFormula interpretation
  perimeterParticipation :
    ArithmeticExecutedGodelRegimeParticipation link.exit.witness
  productionPrecedesCertificationInContinuation :
    History.OccurrencePrecedes
      (perimeterParticipation.locallyExact.realize
        (arithmeticExecutedGodelProductionPosition link.exit.witness))
      (perimeterParticipation.locallyExact.realize
        (arithmeticExecutedGodelCertificationPosition link.exit.witness))
  globalClosureFactorsThroughProducedCompleteness :
    CircularClosureMeaning
        (arithmeticExecutedGodelCircularPresentation link.exit.witness)
        perimeterParticipation.continuation →
      ExecutedGodelProducedCompleteness link.exit.witness

def ExecutedGodelDiagonalPerimetralLink.arithmeticGlobalParticipation
    {coding : GodelDiagonalSyntax}
    {unprovabilityFormula : coding.UnaryFormula}
    {interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula}
    (link :
      ExecutedGodelDiagonalPerimetralLink coding unprovabilityFormula
        interpretation) :
    ArithmeticExecutedGodelGlobalParticipation link := by
  let perimeterParticipation :=
    arithmeticExecutedGodelRegimeParticipation link.exit.witness
  exact
    { historyPinsConsumedExit := link.arithmeticHistoryPinsExit
      perimeterParticipation := perimeterParticipation
      productionPrecedesCertificationInContinuation :=
        perimeterParticipation.locallyExact.preservesPrecedence
          (arithmeticExecutedGodelProductionPrecedesCertification
            link.exit.witness)
      globalClosureFactorsThroughProducedCompleteness :=
        perimeterParticipation.globalClosureToProducedCompleteness }

def ArithmeticExecutedGodelGlobalParticipation.rejectGlobalClosure
    {coding : GodelDiagonalSyntax}
    {unprovabilityFormula : coding.UnaryFormula}
    {interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula}
    {link :
      ExecutedGodelDiagonalPerimetralLink coding unprovabilityFormula
        interpretation}
    (participation : ArithmeticExecutedGodelGlobalParticipation link) :
    CircularClosureMeaning
        (arithmeticExecutedGodelCircularPresentation link.exit.witness)
        participation.perimeterParticipation.continuation → False :=
  fun closure =>
    Empty.elim
      (link.exit.witness.rejectProducedCompleteness
        (participation.globalClosureFactorsThroughProducedCompleteness
          closure))

def ArithmeticExecutedGodelGlobalParticipation.rejectTotalizingRegime
    {coding : GodelDiagonalSyntax}
    {unprovabilityFormula : coding.UnaryFormula}
    {interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula}
    {link :
      ExecutedGodelDiagonalPerimetralLink coding unprovabilityFormula
        interpretation}
    (participation : ArithmeticExecutedGodelGlobalParticipation link) :
    CircularRefinement
        (arithmeticExecutedGodelCircularPresentation link.exit.witness)
        participation.perimeterParticipation.continuation → False :=
  fun refinement =>
    participation.rejectGlobalClosure
      (circularRefinement_soundSpecification refinement).trajectory

inductive FirstOrderArithmeticTerm (arity : Nat) : Type where
  | variable : Fin arity → FirstOrderArithmeticTerm arity
  | zero : FirstOrderArithmeticTerm arity
  | successor :
      FirstOrderArithmeticTerm arity → FirstOrderArithmeticTerm arity
  | addition :
      FirstOrderArithmeticTerm arity →
        FirstOrderArithmeticTerm arity → FirstOrderArithmeticTerm arity
  | multiplication :
      FirstOrderArithmeticTerm arity →
        FirstOrderArithmeticTerm arity → FirstOrderArithmeticTerm arity

namespace FirstOrderArithmeticTerm

def numeral {arity : Nat} : Nat → FirstOrderArithmeticTerm arity
  | 0 => .zero
  | number + 1 => .successor (numeral number)

def evaluate
    {arity : Nat}
    (assignment : Nat → Nat) : FirstOrderArithmeticTerm arity → Nat
  | .variable index => assignment index.val
  | .zero => 0
  | .successor term => evaluate assignment term + 1
  | .addition left right =>
      evaluate assignment left + evaluate assignment right
  | .multiplication left right =>
      evaluate assignment left * evaluate assignment right

end FirstOrderArithmeticTerm

inductive FirstOrderArithmeticFormula : Nat → Type where
  | equal {arity : Nat} :
      FirstOrderArithmeticTerm arity →
        FirstOrderArithmeticTerm arity → FirstOrderArithmeticFormula arity
  | falsity {arity : Nat} : FirstOrderArithmeticFormula arity
  | implication {arity : Nat} :
      FirstOrderArithmeticFormula arity →
        FirstOrderArithmeticFormula arity → FirstOrderArithmeticFormula arity
  | conjunction {arity : Nat} :
      FirstOrderArithmeticFormula arity →
        FirstOrderArithmeticFormula arity → FirstOrderArithmeticFormula arity
  | universal {arity : Nat} :
      FirstOrderArithmeticFormula (arity + 1) →
        FirstOrderArithmeticFormula arity
  | existential {arity : Nat} :
      FirstOrderArithmeticFormula (arity + 1) →
        FirstOrderArithmeticFormula arity

namespace FirstOrderArithmeticFormula

def extendAssignment
    (value : Nat) (assignment : Nat → Nat) : Nat → Nat
  | 0 => value
  | previous + 1 => assignment previous

def unaryAssignment (value : Nat) : Nat → Nat :=
  extendAssignment value (fun _ => 0)

def binaryAssignment (first second : Nat) : Nat → Nat :=
  extendAssignment first (unaryAssignment second)

def Truth
    {arity : Nat}
    (assignment : Nat → Nat) : FirstOrderArithmeticFormula arity → Type
  | .equal left right =>
      PLift
        (FirstOrderArithmeticTerm.evaluate assignment left =
          FirstOrderArithmeticTerm.evaluate assignment right)
  | .falsity => Empty
  | .implication antecedent consequent =>
      Truth assignment antecedent → Truth assignment consequent
  | .conjunction left right => Truth assignment left × Truth assignment right
  | .universal body =>
      (value : Nat) →
        Truth (extendAssignment value assignment) body
  | .existential body =>
      Σ value : Nat, Truth (extendAssignment value assignment) body

def sentenceTruth (sentence : FirstOrderArithmeticFormula 0) : Type :=
  Truth (fun _ => 0) sentence

def biconditional
    (left right : FirstOrderArithmeticFormula 0) :
    FirstOrderArithmeticFormula 0 :=
  .conjunction (.implication left right) (.implication right left)

def negation
    {arity : Nat}
    (formula : FirstOrderArithmeticFormula arity) :
    FirstOrderArithmeticFormula arity :=
  .implication formula .falsity

def provabilityFormula
    (proofRelationFormula : FirstOrderArithmeticFormula 2) :
    FirstOrderArithmeticFormula 1 :=
  /- The new bound variable is index 0 (proof code); the previous free
     variable becomes index 1 (sentence code). -/
  .existential proofRelationFormula

def unprovabilityFormula
    (proofRelationFormula : FirstOrderArithmeticFormula 2) :
    FirstOrderArithmeticFormula 1 :=
  negation (provabilityFormula proofRelationFormula)

end FirstOrderArithmeticFormula

abbrev CheckedArithmeticProof
    (encodeSentence : FirstOrderArithmeticFormula 0 → Nat)
    (proofCheck : Nat → Nat → Bool)
    (sentence : FirstOrderArithmeticFormula 0) : Type :=
  CheckedSentenceProof encodeSentence proofCheck sentence

/- This is the exact soundness-based arithmetic hypothesis package used by
   the bridge.  It describes a proof calculus on the fixed first-order
   arithmetic language.  In particular, `diagonalIffProof` is an accepted
   derivation of an object formula, not a free-standing meta-equivalence. -/
structure EffectivelyPresentedSoundArithmeticTheory where
  encodeUnary : FirstOrderArithmeticFormula 1 → Nat
  decodeUnary : Nat → Option (FirstOrderArithmeticFormula 1)
  decodeUnary_encode :
    (formula : FirstOrderArithmeticFormula 1) →
      decodeUnary (encodeUnary formula) = some formula
  encodeSentence : FirstOrderArithmeticFormula 0 → Nat
  decodeSentence : Nat → Option (FirstOrderArithmeticFormula 0)
  decodeSentence_encode :
    (sentence : FirstOrderArithmeticFormula 0) →
      decodeSentence (encodeSentence sentence) = some sentence
  substituteNumeral :
    FirstOrderArithmeticFormula 1 → Nat → FirstOrderArithmeticFormula 0
  diagonalize :
    FirstOrderArithmeticFormula 1 → FirstOrderArithmeticFormula 1
  proofCheck : Nat → Nat → Bool
  diagonalIffProof :
    (target source : FirstOrderArithmeticFormula 1) →
      CheckedArithmeticProof encodeSentence proofCheck
        (FirstOrderArithmeticFormula.biconditional
          (substituteNumeral (diagonalize target) (encodeUnary source))
          (substituteNumeral target
            (encodeSentence (substituteNumeral source (encodeUnary source)))))
  iffProofForward :
    {left right : FirstOrderArithmeticFormula 0} →
      CheckedArithmeticProof encodeSentence proofCheck
        (FirstOrderArithmeticFormula.biconditional left right) →
      CheckedArithmeticProof encodeSentence proofCheck left →
      CheckedArithmeticProof encodeSentence proofCheck right
  iffProofBackward :
    {left right : FirstOrderArithmeticFormula 0} →
      CheckedArithmeticProof encodeSentence proofCheck
        (FirstOrderArithmeticFormula.biconditional left right) →
      CheckedArithmeticProof encodeSentence proofCheck right →
      CheckedArithmeticProof encodeSentence proofCheck left
  proofSound :
    {sentence : FirstOrderArithmeticFormula 0} →
      CheckedArithmeticProof encodeSentence proofCheck sentence →
        FirstOrderArithmeticFormula.sentenceTruth sentence
  unprovabilityFormula : FirstOrderArithmeticFormula 1
  representsUnprovabilityForward :
    (sentence : FirstOrderArithmeticFormula 0) →
      FirstOrderArithmeticFormula.sentenceTruth
        (substituteNumeral unprovabilityFormula (encodeSentence sentence)) →
      CheckedArithmeticProof encodeSentence proofCheck sentence → Empty
  representsUnprovabilityBackward :
    (sentence : FirstOrderArithmeticFormula 0) →
      (CheckedArithmeticProof encodeSentence proofCheck sentence → Empty) →
      FirstOrderArithmeticFormula.sentenceTruth
        (substituteNumeral unprovabilityFormula (encodeSentence sentence))

/- This R1 package makes the proof predicate explicit.  It receives semantic
   correctness of a binary object formula relative to the same Boolean proof
   checker used by `CheckedArithmeticProof`, semantic correctness of numeral
   substitution, and the ordinary logical strength needed to derive every
   reflexive closed equality.  It does not receive either historical
   unprovability law, nor any fact about the produced diagonal sentence. -/
structure SemanticallyDefinedProofArithmeticTheory where
  encodeUnary : FirstOrderArithmeticFormula 1 → Nat
  decodeUnary : Nat → Option (FirstOrderArithmeticFormula 1)
  decodeUnary_encode :
    (formula : FirstOrderArithmeticFormula 1) →
      decodeUnary (encodeUnary formula) = some formula
  encodeSentence : FirstOrderArithmeticFormula 0 → Nat
  decodeSentence : Nat → Option (FirstOrderArithmeticFormula 0)
  decodeSentence_encode :
    (sentence : FirstOrderArithmeticFormula 0) →
      decodeSentence (encodeSentence sentence) = some sentence
  substituteNumeral :
    FirstOrderArithmeticFormula 1 → Nat → FirstOrderArithmeticFormula 0
  substituteNumeralTruthForward :
    (formula : FirstOrderArithmeticFormula 1) →
      (value : Nat) →
        FirstOrderArithmeticFormula.sentenceTruth
            (substituteNumeral formula value) →
          FirstOrderArithmeticFormula.Truth
            (FirstOrderArithmeticFormula.unaryAssignment value) formula
  substituteNumeralTruthBackward :
    (formula : FirstOrderArithmeticFormula 1) →
      (value : Nat) →
        FirstOrderArithmeticFormula.Truth
            (FirstOrderArithmeticFormula.unaryAssignment value) formula →
          FirstOrderArithmeticFormula.sentenceTruth
            (substituteNumeral formula value)
  diagonalize :
    FirstOrderArithmeticFormula 1 → FirstOrderArithmeticFormula 1
  proofCheck : Nat → Nat → Bool
  diagonalIffProof :
    (target source : FirstOrderArithmeticFormula 1) →
      CheckedArithmeticProof encodeSentence proofCheck
        (FirstOrderArithmeticFormula.biconditional
          (substituteNumeral (diagonalize target) (encodeUnary source))
          (substituteNumeral target
            (encodeSentence (substituteNumeral source (encodeUnary source)))))
  iffProofForward :
    {left right : FirstOrderArithmeticFormula 0} →
      CheckedArithmeticProof encodeSentence proofCheck
        (FirstOrderArithmeticFormula.biconditional left right) →
      CheckedArithmeticProof encodeSentence proofCheck left →
      CheckedArithmeticProof encodeSentence proofCheck right
  iffProofBackward :
    {left right : FirstOrderArithmeticFormula 0} →
      CheckedArithmeticProof encodeSentence proofCheck
        (FirstOrderArithmeticFormula.biconditional left right) →
      CheckedArithmeticProof encodeSentence proofCheck right →
      CheckedArithmeticProof encodeSentence proofCheck left
  proofSound :
    {sentence : FirstOrderArithmeticFormula 0} →
      CheckedArithmeticProof encodeSentence proofCheck sentence →
        FirstOrderArithmeticFormula.sentenceTruth sentence
  equalityReflexivityProof :
    (term : FirstOrderArithmeticTerm 0) →
      CheckedArithmeticProof encodeSentence proofCheck
        (FirstOrderArithmeticFormula.equal term term)
  proofRelationFormula : FirstOrderArithmeticFormula 2
  proofRelationTruthForward :
    (proofCode sentenceCode : Nat) →
      FirstOrderArithmeticFormula.Truth
          (FirstOrderArithmeticFormula.binaryAssignment
            proofCode sentenceCode)
          proofRelationFormula →
        PLift (proofCheck proofCode sentenceCode = true)
  proofRelationTruthBackward :
    (proofCode sentenceCode : Nat) →
      PLift (proofCheck proofCode sentenceCode = true) →
        FirstOrderArithmeticFormula.Truth
          (FirstOrderArithmeticFormula.binaryAssignment
            proofCode sentenceCode)
          proofRelationFormula

def SemanticallyDefinedProofArithmeticTheory.provabilityFormula
    (theory : SemanticallyDefinedProofArithmeticTheory) :
    FirstOrderArithmeticFormula 1 :=
  FirstOrderArithmeticFormula.provabilityFormula
    theory.proofRelationFormula

def SemanticallyDefinedProofArithmeticTheory.unprovabilityFormula
    (theory : SemanticallyDefinedProofArithmeticTheory) :
    FirstOrderArithmeticFormula 1 :=
  FirstOrderArithmeticFormula.unprovabilityFormula
    theory.proofRelationFormula

def SemanticallyDefinedProofArithmeticTheory.checkedProof_implies_provabilityTruth
    (theory : SemanticallyDefinedProofArithmeticTheory)
    (sentence : FirstOrderArithmeticFormula 0) :
    CheckedArithmeticProof theory.encodeSentence theory.proofCheck sentence →
      FirstOrderArithmeticFormula.sentenceTruth
        (theory.substituteNumeral theory.provabilityFormula
          (theory.encodeSentence sentence)) := by
  intro proof
  rcases proof with ⟨proofCode, verification⟩
  exact
    theory.substituteNumeralTruthBackward
      theory.provabilityFormula (theory.encodeSentence sentence)
      ⟨proofCode,
        theory.proofRelationTruthBackward
          proofCode (theory.encodeSentence sentence) verification⟩

def SemanticallyDefinedProofArithmeticTheory.provabilityTruth_implies_checkedProof
    (theory : SemanticallyDefinedProofArithmeticTheory)
    (sentence : FirstOrderArithmeticFormula 0) :
    FirstOrderArithmeticFormula.sentenceTruth
        (theory.substituteNumeral theory.provabilityFormula
          (theory.encodeSentence sentence)) →
      CheckedArithmeticProof theory.encodeSentence theory.proofCheck
        sentence := by
  intro truthWitness
  have provabilityTruth :=
    theory.substituteNumeralTruthForward
      theory.provabilityFormula (theory.encodeSentence sentence) truthWitness
  rcases provabilityTruth with ⟨proofCode, relationTruth⟩
  exact
    ⟨proofCode,
      theory.proofRelationTruthForward
        proofCode (theory.encodeSentence sentence) relationTruth⟩

def SemanticallyDefinedProofArithmeticTheory.unprovabilityTruth_implies_noProof
    (theory : SemanticallyDefinedProofArithmeticTheory)
    (sentence : FirstOrderArithmeticFormula 0) :
    FirstOrderArithmeticFormula.sentenceTruth
        (theory.substituteNumeral theory.unprovabilityFormula
          (theory.encodeSentence sentence)) →
      CheckedArithmeticProof theory.encodeSentence theory.proofCheck sentence →
        Empty := by
  intro unprovabilitySentenceTruth proof
  have unprovabilityTruth :=
    theory.substituteNumeralTruthForward
      theory.unprovabilityFormula (theory.encodeSentence sentence)
      unprovabilitySentenceTruth
  have provabilitySentenceTruth :=
    theory.checkedProof_implies_provabilityTruth sentence proof
  have provabilityTruth :=
    theory.substituteNumeralTruthForward
      theory.provabilityFormula (theory.encodeSentence sentence)
      provabilitySentenceTruth
  exact unprovabilityTruth provabilityTruth

def SemanticallyDefinedProofArithmeticTheory.noProof_implies_unprovabilityTruth
    (theory : SemanticallyDefinedProofArithmeticTheory)
    (sentence : FirstOrderArithmeticFormula 0) :
    (CheckedArithmeticProof theory.encodeSentence theory.proofCheck sentence →
      Empty) →
    FirstOrderArithmeticFormula.sentenceTruth
      (theory.substituteNumeral theory.unprovabilityFormula
        (theory.encodeSentence sentence)) := by
  intro noProof
  apply theory.substituteNumeralTruthBackward
  intro provabilityTruth
  have provabilitySentenceTruth :=
    theory.substituteNumeralTruthBackward
      theory.provabilityFormula (theory.encodeSentence sentence)
      provabilityTruth
  exact
    noProof
      (theory.provabilityTruth_implies_checkedProof
        sentence provabilitySentenceTruth)

/- Semantic completeness at one sentence is the directed obligation used by
   the diagnostic closure below.  Keeping this predicate independent of the
   Gödel witness makes it possible to test the very same obligation at a
   decided sentence of the same theory. -/
abbrev ArithmeticSemanticCompletenessAt
    (theory : SemanticallyDefinedProofArithmeticTheory)
    (sentence : FirstOrderArithmeticFormula 0) : Type :=
  DirectedSemanticCompletenessAt
    FirstOrderArithmeticFormula.sentenceTruth
    (CheckedArithmeticProof theory.encodeSentence theory.proofCheck)
    sentence

abbrev arithmeticReflexiveZeroSentence : FirstOrderArithmeticFormula 0 :=
  .equal .zero .zero

def SemanticallyDefinedProofArithmeticTheory.reflexiveZeroTruth
    (_theory : SemanticallyDefinedProofArithmeticTheory) :
    FirstOrderArithmeticFormula.sentenceTruth
      arithmeticReflexiveZeroSentence :=
  ⟨rfl⟩

def SemanticallyDefinedProofArithmeticTheory.reflexiveZeroProof
    (theory : SemanticallyDefinedProofArithmeticTheory) :
    CheckedArithmeticProof theory.encodeSentence theory.proofCheck
      arithmeticReflexiveZeroSentence :=
  theory.equalityReflexivityProof .zero

def SemanticallyDefinedProofArithmeticTheory.reflexiveZeroCompleteness
    (theory : SemanticallyDefinedProofArithmeticTheory) :
    ArithmeticSemanticCompletenessAt theory
      arithmeticReflexiveZeroSentence :=
  fun _ => theory.reflexiveZeroProof

/- The exact arithmetic interface cannot be instantiated by the proofless
   countermodel used against the abstract Gödel adapter: reflexivity already
   supplies a checked derivation. -/
def SemanticallyDefinedProofArithmeticTheory.rejectProoflessChecker
    (theory : SemanticallyDefinedProofArithmeticTheory)
    (proofless :
      (proofCode sentenceCode : Nat) →
        theory.proofCheck proofCode sentenceCode = false) : Empty := by
  rcases theory.reflexiveZeroProof with ⟨proofCode, ⟨verification⟩⟩
  rw [proofless proofCode
    (theory.encodeSentence arithmeticReflexiveZeroSentence)] at verification
  cases verification

def SemanticallyDefinedProofArithmeticTheory.toEffectivelyPresentedSoundArithmeticTheory
    (theory : SemanticallyDefinedProofArithmeticTheory) :
    EffectivelyPresentedSoundArithmeticTheory :=
  { encodeUnary := theory.encodeUnary
    decodeUnary := theory.decodeUnary
    decodeUnary_encode := theory.decodeUnary_encode
    encodeSentence := theory.encodeSentence
    decodeSentence := theory.decodeSentence
    decodeSentence_encode := theory.decodeSentence_encode
    substituteNumeral := theory.substituteNumeral
    diagonalize := theory.diagonalize
    proofCheck := theory.proofCheck
    diagonalIffProof := theory.diagonalIffProof
    iffProofForward := theory.iffProofForward
    iffProofBackward := theory.iffProofBackward
    proofSound := theory.proofSound
    unprovabilityFormula := theory.unprovabilityFormula
    representsUnprovabilityForward :=
      theory.unprovabilityTruth_implies_noProof
    representsUnprovabilityBackward :=
      theory.noProof_implies_unprovabilityTruth }

def arithmeticEquivalenceCheck
    (theory : EffectivelyPresentedSoundArithmeticTheory)
    (certificateCode leftCode rightCode : Nat) : Bool :=
  match theory.decodeSentence leftCode with
  | none => false
  | some left =>
      match theory.decodeSentence rightCode with
      | none => false
      | some right =>
          theory.proofCheck certificateCode
            (theory.encodeSentence
              (FirstOrderArithmeticFormula.biconditional left right))

def EffectivelyPresentedSoundArithmeticTheory.equivalenceIsBiconditionalProof
    (theory : EffectivelyPresentedSoundArithmeticTheory)
    {left right : FirstOrderArithmeticFormula 0}
    (equivalence :
      CheckedSentenceEquivalence theory.encodeSentence
        (arithmeticEquivalenceCheck theory) left right) :
    CheckedArithmeticProof theory.encodeSentence theory.proofCheck
      (FirstOrderArithmeticFormula.biconditional left right) := by
  rcases equivalence with ⟨certificateCode, ⟨verification⟩⟩
  exact
    ⟨certificateCode, ⟨by
      simpa [arithmeticEquivalenceCheck,
        theory.decodeSentence_encode left,
        theory.decodeSentence_encode right] using verification⟩⟩

def EffectivelyPresentedSoundArithmeticTheory.toEffectiveGodelSystem
    (theory : EffectivelyPresentedSoundArithmeticTheory) :
    EffectivelyPresentedSoundGodelSystem :=
  { UnaryFormula := FirstOrderArithmeticFormula 1
    Sentence := FirstOrderArithmeticFormula 0
    encodeUnary := theory.encodeUnary
    decodeUnary := theory.decodeUnary
    decodeUnary_encode := theory.decodeUnary_encode
    encodeSentence := theory.encodeSentence
    decodeSentence := theory.decodeSentence
    decodeSentence_encode := theory.decodeSentence_encode
    substitute := theory.substituteNumeral
    diagonalize := theory.diagonalize
    proofCheck := theory.proofCheck
    equivalenceCheck := arithmeticEquivalenceCheck theory
    diagonalizeExact := by
      intro target source
      rcases theory.diagonalIffProof target source with
        ⟨certificateCode, ⟨verification⟩⟩
      exact
        ⟨certificateCode, ⟨by
          simpa [arithmeticEquivalenceCheck,
            theory.decodeSentence_encode] using verification⟩⟩
    proofForward := by
      intro left right equivalence proof
      exact theory.iffProofForward
        (theory.equivalenceIsBiconditionalProof equivalence) proof
    proofBackward := by
      intro left right equivalence proof
      exact theory.iffProofBackward
        (theory.equivalenceIsBiconditionalProof equivalence) proof
    Truth := FirstOrderArithmeticFormula.sentenceTruth
    proofSound := theory.proofSound
    equivalenceTruthForward := by
      intro left right equivalence leftTruth
      have biconditionalTruth :=
        theory.proofSound
          (theory.equivalenceIsBiconditionalProof equivalence)
      exact biconditionalTruth.1 leftTruth
    equivalenceTruthBackward := by
      intro left right equivalence rightTruth
      have biconditionalTruth :=
        theory.proofSound
          (theory.equivalenceIsBiconditionalProof equivalence)
      exact biconditionalTruth.2 rightTruth
    unprovabilityFormula := theory.unprovabilityFormula
    representsUnprovabilityForward :=
      theory.representsUnprovabilityForward
    representsUnprovabilityBackward :=
      theory.representsUnprovabilityBackward }

abbrev arithmeticGodelExecutedLink
    (theory : EffectivelyPresentedSoundArithmeticTheory) :=
  effectiveGodelExecutedLink theory.toEffectiveGodelSystem

structure ArithmeticGodelPerimetralCorrespondence
    (theory : EffectivelyPresentedSoundArithmeticTheory) where
  effective :
    EffectiveGodelPerimetralCorrespondence theory.toEffectiveGodelSystem
  diagonalCertificateIsObjectBiconditional :
    CheckedArithmeticProof theory.encodeSentence theory.proofCheck
      (FirstOrderArithmeticFormula.biconditional
        effective.execution.exit.witness.production.sentence
        (theory.substituteNumeral theory.unprovabilityFormula
          (theory.encodeSentence
            effective.execution.exit.witness.production.sentence)))
  producedSentenceIsTrueInStandardArithmeticSemantics :
    FirstOrderArithmeticFormula.sentenceTruth
      effective.execution.exit.witness.production.sentence
  producedSentenceHasNoCheckedDerivation :
    CheckedArithmeticProof theory.encodeSentence theory.proofCheck
      effective.execution.exit.witness.production.sentence → Empty
  producedSentenceRejectsSemanticCompleteness :
    ExecutedGodelProducedCompleteness
      effective.execution.exit.witness → Empty
  executedHistoryPinsTheConsumedExit :
    effective.execution.exit =
      arithmeticCanonicalExecutedGodelRegimeExit
        theory.toEffectiveGodelSystem.toGodelSyntax
        theory.unprovabilityFormula
        theory.toEffectiveGodelSystem.toGodelInterpretation
  executedGlobalParticipation :
    ArithmeticExecutedGodelGlobalParticipation effective.execution
  executedCausalParticipation :
    ArithmeticExecutedGodelCausalParticipation effective.execution
  causalContinuationMatchesLegacy :
    executedCausalParticipation.continuation =
      executedGlobalParticipation.perimeterParticipation.continuation
  affirmativeContinuationIsStrict :
    StrictConstitutivePrefix
      (perimeterDeployment
        (arithmeticExecutedGodelCircularPresentation
          effective.execution.exit.witness))
      executedGlobalParticipation.perimeterParticipation.continuation
  affirmativeContinuationIsLocallyExact :
    ExactNonClosingRealization
      (arithmeticExecutedGodelCircularPresentation
        effective.execution.exit.witness)
      executedGlobalParticipation.perimeterParticipation.continuation
  specifiedGlobalClosureFactorsThroughProducedCompleteness :
    CircularClosureMeaning
        (arithmeticExecutedGodelCircularPresentation
          effective.execution.exit.witness)
        executedGlobalParticipation.perimeterParticipation.continuation →
      ExecutedGodelProducedCompleteness
        effective.execution.exit.witness
  specifiedClosureToCausalClosure :
    CircularClosureMeaning
        (ArithmeticExecutedGodelPresentation effective.execution)
        executedCausalParticipation.continuation →
      ArithmeticExecutedGodelCausalClosureMeaning executedCausalParticipation
  causalClosureToDirectedClosure :
    ArithmeticExecutedGodelCausalClosureMeaning executedCausalParticipation →
      ArithmeticExecutedGodelDirectedClosureMeaning executedCausalParticipation
  causalClosureToSpecifiedClosure :
    ArithmeticExecutedGodelCausalClosureMeaning executedCausalParticipation →
      CircularClosureMeaning
        (ArithmeticExecutedGodelPresentation effective.execution)
        executedCausalParticipation.continuation
  directedClosureFactorsThroughProducedCompleteness :
    ArithmeticExecutedGodelDirectedClosureMeaning executedCausalParticipation →
      ExecutedGodelProducedCompleteness
        effective.execution.exit.witness
  directedClosureIsImpossible :
    ArithmeticExecutedGodelDirectedClosureMeaning executedCausalParticipation →
      Empty
  causalClosureFactorsThroughProducedCompleteness :
    ArithmeticExecutedGodelCausalClosureMeaning executedCausalParticipation →
      ExecutedGodelProducedCompleteness
        effective.execution.exit.witness
  causalClosureIsImpossible :
    ArithmeticExecutedGodelCausalClosureMeaning executedCausalParticipation →
      Empty
  specifiedGlobalClosureIsImpossible :
    CircularClosureMeaning
        (arithmeticExecutedGodelCircularPresentation
          effective.execution.exit.witness)
        executedGlobalParticipation.perimeterParticipation.continuation →
      False
  specifiedTotalizingRegimeIsImpossible :
    CircularRefinement
      (arithmeticExecutedGodelCircularPresentation
        effective.execution.exit.witness)
      executedGlobalParticipation.perimeterParticipation.continuation → False

structure SemanticallyDefinedArithmeticGodelPerimetralConclusion
    (theory : SemanticallyDefinedProofArithmeticTheory) where
  correspondence :
    ArithmeticGodelPerimetralCorrespondence
      theory.toEffectivelyPresentedSoundArithmeticTheory
  producedNegationHasNoCheckedDerivation :
    CheckedArithmeticProof theory.encodeSentence theory.proofCheck
        (FirstOrderArithmeticFormula.negation
          correspondence.effective.execution.exit.witness.production.sentence) →
      Empty
  producedSentenceIsNotAReflexiveEquality :
    (term : FirstOrderArithmeticTerm 0) →
      correspondence.effective.execution.exit.witness.production.sentence =
          FirstOrderArithmeticFormula.equal term term →
        Empty

/- This package compares the same directed semantic-completeness predicate at
   two sentences of one non-proofless arithmetic theory.  It is satisfied at
   the decided reflexive equality and rejected at the produced diagonal
   sentence, while retaining the positive constitutive correspondence. -/
structure SemanticallyDefinedArithmeticGodelDiagnostic
    (theory : SemanticallyDefinedProofArithmeticTheory) where
  conclusion : SemanticallyDefinedArithmeticGodelPerimetralConclusion theory
  decidedSentenceSupportsSemanticCompleteness :
    ArithmeticSemanticCompletenessAt theory
      arithmeticReflexiveZeroSentence
  producedSentenceRejectsSemanticCompleteness :
    ArithmeticSemanticCompletenessAt theory
        conclusion.correspondence.effective.execution.exit.witness.production.sentence →
      Empty
  producedContinuationRemainsStrict :
    StrictConstitutivePrefix
      (perimeterDeployment
        (arithmeticExecutedGodelCircularPresentation
          conclusion.correspondence.effective.execution.exit.witness))
      conclusion.correspondence.executedGlobalParticipation.perimeterParticipation.continuation

def arithmeticGodelPerimetralCorrespondence
    (theory : EffectivelyPresentedSoundArithmeticTheory) :
    ArithmeticGodelPerimetralCorrespondence theory := by
  let effective :=
    effectiveGodelPerimetralCorrespondence theory.toEffectiveGodelSystem
  let participation := effective.execution.arithmeticGlobalParticipation
  let causalParticipation :=
    effective.execution.arithmeticCausalParticipation
  have continuationMatches :
      causalParticipation.continuation =
        participation.perimeterParticipation.continuation := by
    rw [causalParticipation.continuationIsCanonical,
      participation.perimeterParticipation.continuationIsCanonical]
  let legacyClosureToCompleteness :
      CircularClosureMeaning
          (arithmeticExecutedGodelCircularPresentation
            effective.execution.exit.witness)
          participation.perimeterParticipation.continuation →
        ExecutedGodelProducedCompleteness
          effective.execution.exit.witness := by
    intro closure
    have causalContinuationClosure :
        CircularClosureMeaning
            (ArithmeticExecutedGodelPresentation effective.execution)
            causalParticipation.continuation := by
      rw [continuationMatches]
      exact closure
    exact causalParticipation.causalClosureToProducedCompleteness
      (causalParticipation.circularClosureToCausalClosure
        causalContinuationClosure)
  let legacyClosureRejected :
      CircularClosureMeaning
          (arithmeticExecutedGodelCircularPresentation
            effective.execution.exit.witness)
          participation.perimeterParticipation.continuation → False := by
    intro closure
    have causalContinuationClosure :
        CircularClosureMeaning
            (ArithmeticExecutedGodelPresentation effective.execution)
            causalParticipation.continuation := by
      rw [continuationMatches]
      exact closure
    exact Empty.elim
      (causalParticipation.rejectSpecifiedClosure causalContinuationClosure)
  exact
    { effective := effective
      diagonalCertificateIsObjectBiconditional :=
        theory.equivalenceIsBiconditionalProof
          effective.producedFixedPoint
      producedSentenceIsTrueInStandardArithmeticSemantics :=
        effective.producedSentenceIsTrue
      producedSentenceHasNoCheckedDerivation :=
        effective.producedSentenceIsUnprovable
      producedSentenceRejectsSemanticCompleteness :=
        effective.semanticCompletenessAtProducedSentenceIsImpossible
      executedHistoryPinsTheConsumedExit :=
        effective.execution.arithmeticHistoryPinsExit
      executedGlobalParticipation := participation
      executedCausalParticipation := causalParticipation
      causalContinuationMatchesLegacy := continuationMatches
      affirmativeContinuationIsStrict := by
        rw [participation.perimeterParticipation.continuationIsCanonical]
        exact
          oneStepAfterPerimeterStrict
            (arithmeticExecutedGodelCircularPresentation
              effective.execution.exit.witness)
      affirmativeContinuationIsLocallyExact :=
        participation.perimeterParticipation.locallyExact
      specifiedGlobalClosureFactorsThroughProducedCompleteness :=
        legacyClosureToCompleteness
      specifiedClosureToCausalClosure :=
        causalParticipation.circularClosureToCausalClosure
      causalClosureToDirectedClosure :=
        causalParticipation.causalClosureToDirectedClosure
      causalClosureToSpecifiedClosure :=
        causalParticipation.causalClosureToCircularClosure
      directedClosureFactorsThroughProducedCompleteness :=
        causalParticipation.directedClosureToProducedCompleteness
      directedClosureIsImpossible :=
        causalParticipation.rejectDirectedClosure
      causalClosureFactorsThroughProducedCompleteness :=
        causalParticipation.causalClosureToProducedCompleteness
      causalClosureIsImpossible :=
        causalParticipation.rejectCausalClosure
      specifiedGlobalClosureIsImpossible :=
        legacyClosureRejected
      specifiedTotalizingRegimeIsImpossible := fun refinement =>
        legacyClosureRejected
          (circularRefinement_soundSpecification refinement).trajectory }

abbrev SemanticallyDefinedArithmeticGodelPerimetralCorrespondence
    (theory : SemanticallyDefinedProofArithmeticTheory) :=
  ArithmeticGodelPerimetralCorrespondence
    theory.toEffectivelyPresentedSoundArithmeticTheory

def semanticallyDefinedArithmeticGodelPerimetralCorrespondence
    (theory : SemanticallyDefinedProofArithmeticTheory) :
    SemanticallyDefinedArithmeticGodelPerimetralCorrespondence theory :=
  arithmeticGodelPerimetralCorrespondence
    theory.toEffectivelyPresentedSoundArithmeticTheory

def semanticallyDefinedArithmeticGodelPerimetralConclusion
    (theory : SemanticallyDefinedProofArithmeticTheory) :
    SemanticallyDefinedArithmeticGodelPerimetralConclusion theory := by
  let correspondence :=
    semanticallyDefinedArithmeticGodelPerimetralCorrespondence theory
  refine
    { correspondence := correspondence
      producedNegationHasNoCheckedDerivation := ?_
      producedSentenceIsNotAReflexiveEquality := ?_ }
  · intro proof
    have negationTruth := theory.proofSound proof
    exact
      negationTruth
        correspondence.producedSentenceIsTrueInStandardArithmeticSemantics
  intro term equality
  apply correspondence.producedSentenceHasNoCheckedDerivation
  rw [equality]
  exact theory.equalityReflexivityProof term

def semanticallyDefinedArithmeticGodelDiagnostic
    (theory : SemanticallyDefinedProofArithmeticTheory) :
    SemanticallyDefinedArithmeticGodelDiagnostic theory := by
  let conclusion :=
    semanticallyDefinedArithmeticGodelPerimetralConclusion theory
  exact
    { conclusion := conclusion
      decidedSentenceSupportsSemanticCompleteness :=
        theory.reflexiveZeroCompleteness
      producedSentenceRejectsSemanticCompleteness :=
        conclusion.correspondence.producedSentenceRejectsSemanticCompleteness
      producedContinuationRemainsStrict :=
        conclusion.correspondence.affirmativeContinuationIsStrict }

end StrongPerimetralTurning

/- AXIOM_AUDIT_BEGIN -/
#print axioms StrongPerimetralTurning.arithmeticCanonicalExecutedGodelRegimeExit
#print axioms StrongPerimetralTurning.ArithmeticExecutedGodelConstitutiveCanonical
#print axioms StrongPerimetralTurning.arithmeticExecutedGodelHistory_isCanonical
#print axioms StrongPerimetralTurning.ExecutedGodelDiagonalPerimetralLink.arithmeticHistoryPinsExit
#print axioms StrongPerimetralTurning.ArithmeticExecutedGodelHistoryOccurrences
#print axioms StrongPerimetralTurning.ExecutedGodelDiagonalPerimetralLink.arithmeticHistoryOccurrences
#print axioms StrongPerimetralTurning.ArithmeticExecutedGodelPerimeterResource
#print axioms StrongPerimetralTurning.ArithmeticExecutedGodelPerimeterCompatibility
#print axioms StrongPerimetralTurning.arithmeticExecutedGodelNode
#print axioms StrongPerimetralTurning.arithmeticExecutedGodelPerimeter
#print axioms StrongPerimetralTurning.arithmeticExecutedGodelProductionPosition
#print axioms StrongPerimetralTurning.arithmeticExecutedGodelCertificationPosition
#print axioms StrongPerimetralTurning.arithmeticExecutedGodelProductionPrecedesCertification
#print axioms StrongPerimetralTurning.arithmeticExecutedGodelCircularPresentation
#print axioms StrongPerimetralTurning.ArithmeticExecutedGodelPresentation
#print axioms StrongPerimetralTurning.StrongPerimetralTurningCertificate.freelyGeneratedStrictContinuation
#print axioms StrongPerimetralTurning.recordedSourceProvenance
#print axioms StrongPerimetralTurning.ArithmeticExecutedGodelCausalParticipation
#print axioms StrongPerimetralTurning.ExecutedGodelDiagonalPerimetralLink.arithmeticCausalParticipation
#print axioms StrongPerimetralTurning.ArithmeticExecutedGodelOccurrenceCorrespondence
#print axioms StrongPerimetralTurning.ArithmeticExecutedGodelCausalParticipation.executedOccurrenceCorrespondence
#print axioms StrongPerimetralTurning.ArithmeticExecutedGodelCausalParticipation.strictTurningContinuation
#print axioms StrongPerimetralTurning.ArithmeticExecutedGodelCausalParticipation.locallyExact
#print axioms StrongPerimetralTurning.ArithmeticExecutedGodelCausalParticipation.recordedDifferenceIsSource
#print axioms StrongPerimetralTurning.ArithmeticExecutedGodelCausalParticipation.historicalProvenance
#print axioms StrongPerimetralTurning.ArithmeticExecutedGodelCausalContraction
#print axioms StrongPerimetralTurning.DirectedSemanticCompletenessAt
#print axioms StrongPerimetralTurning.ArithmeticExecutedGodelDirectedContraction
#print axioms StrongPerimetralTurning.ArithmeticExecutedGodelCausalClosureMeaning
#print axioms StrongPerimetralTurning.ArithmeticExecutedGodelDirectedClosureMeaning
#print axioms StrongPerimetralTurning.ArithmeticExecutedGodelCausalParticipation.circularClosureToCausalClosure
#print axioms StrongPerimetralTurning.ArithmeticExecutedGodelCausalParticipation.causalClosureToCircularClosure
#print axioms StrongPerimetralTurning.ArithmeticExecutedGodelCausalParticipation.causalClosureContraction
#print axioms StrongPerimetralTurning.ArithmeticExecutedGodelCausalParticipation.causalClosureToDirectedClosure
#print axioms StrongPerimetralTurning.ArithmeticExecutedGodelCausalParticipation.directedClosureContraction
#print axioms StrongPerimetralTurning.ArithmeticExecutedGodelCausalParticipation.directedClosureToProducedCompleteness
#print axioms StrongPerimetralTurning.ArithmeticExecutedGodelCausalParticipation.causalClosureToProducedCompleteness
#print axioms StrongPerimetralTurning.ArithmeticExecutedGodelCausalParticipation.rejectDirectedClosure
#print axioms StrongPerimetralTurning.ArithmeticExecutedGodelCausalParticipation.rejectCausalClosure
#print axioms StrongPerimetralTurning.ArithmeticExecutedGodelCausalParticipation.rejectSpecifiedClosure
#print axioms StrongPerimetralTurning.ArithmeticExecutedGodelRegimeParticipation
#print axioms StrongPerimetralTurning.arithmeticExecutedGodelRegimeParticipation
#print axioms StrongPerimetralTurning.ArithmeticExecutedGodelRegimeParticipation.globalClosureToProducedCompleteness
#print axioms StrongPerimetralTurning.ArithmeticExecutedGodelGlobalParticipation
#print axioms StrongPerimetralTurning.ExecutedGodelDiagonalPerimetralLink.arithmeticGlobalParticipation
#print axioms StrongPerimetralTurning.ArithmeticExecutedGodelGlobalParticipation.rejectGlobalClosure
#print axioms StrongPerimetralTurning.ArithmeticExecutedGodelGlobalParticipation.rejectTotalizingRegime
#print axioms StrongPerimetralTurning.FirstOrderArithmeticTerm
#print axioms StrongPerimetralTurning.FirstOrderArithmeticTerm.numeral
#print axioms StrongPerimetralTurning.FirstOrderArithmeticTerm.evaluate
#print axioms StrongPerimetralTurning.FirstOrderArithmeticFormula
#print axioms StrongPerimetralTurning.FirstOrderArithmeticFormula.extendAssignment
#print axioms StrongPerimetralTurning.FirstOrderArithmeticFormula.unaryAssignment
#print axioms StrongPerimetralTurning.FirstOrderArithmeticFormula.binaryAssignment
#print axioms StrongPerimetralTurning.FirstOrderArithmeticFormula.Truth
#print axioms StrongPerimetralTurning.FirstOrderArithmeticFormula.sentenceTruth
#print axioms StrongPerimetralTurning.FirstOrderArithmeticFormula.biconditional
#print axioms StrongPerimetralTurning.FirstOrderArithmeticFormula.negation
#print axioms StrongPerimetralTurning.FirstOrderArithmeticFormula.provabilityFormula
#print axioms StrongPerimetralTurning.FirstOrderArithmeticFormula.unprovabilityFormula
#print axioms StrongPerimetralTurning.CheckedArithmeticProof
#print axioms StrongPerimetralTurning.EffectivelyPresentedSoundArithmeticTheory
#print axioms StrongPerimetralTurning.SemanticallyDefinedProofArithmeticTheory
#print axioms StrongPerimetralTurning.SemanticallyDefinedProofArithmeticTheory.provabilityFormula
#print axioms StrongPerimetralTurning.SemanticallyDefinedProofArithmeticTheory.unprovabilityFormula
#print axioms StrongPerimetralTurning.SemanticallyDefinedProofArithmeticTheory.checkedProof_implies_provabilityTruth
#print axioms StrongPerimetralTurning.SemanticallyDefinedProofArithmeticTheory.provabilityTruth_implies_checkedProof
#print axioms StrongPerimetralTurning.SemanticallyDefinedProofArithmeticTheory.unprovabilityTruth_implies_noProof
#print axioms StrongPerimetralTurning.SemanticallyDefinedProofArithmeticTheory.noProof_implies_unprovabilityTruth
#print axioms StrongPerimetralTurning.ArithmeticSemanticCompletenessAt
#print axioms StrongPerimetralTurning.arithmeticReflexiveZeroSentence
#print axioms StrongPerimetralTurning.SemanticallyDefinedProofArithmeticTheory.reflexiveZeroTruth
#print axioms StrongPerimetralTurning.SemanticallyDefinedProofArithmeticTheory.reflexiveZeroProof
#print axioms StrongPerimetralTurning.SemanticallyDefinedProofArithmeticTheory.reflexiveZeroCompleteness
#print axioms StrongPerimetralTurning.SemanticallyDefinedProofArithmeticTheory.rejectProoflessChecker
#print axioms StrongPerimetralTurning.SemanticallyDefinedProofArithmeticTheory.toEffectivelyPresentedSoundArithmeticTheory
#print axioms StrongPerimetralTurning.arithmeticEquivalenceCheck
#print axioms StrongPerimetralTurning.EffectivelyPresentedSoundArithmeticTheory.equivalenceIsBiconditionalProof
#print axioms StrongPerimetralTurning.EffectivelyPresentedSoundArithmeticTheory.toEffectiveGodelSystem
#print axioms StrongPerimetralTurning.arithmeticGodelExecutedLink
#print axioms StrongPerimetralTurning.ArithmeticGodelPerimetralCorrespondence
#print axioms StrongPerimetralTurning.arithmeticGodelPerimetralCorrespondence
#print axioms StrongPerimetralTurning.SemanticallyDefinedArithmeticGodelPerimetralCorrespondence
#print axioms StrongPerimetralTurning.semanticallyDefinedArithmeticGodelPerimetralCorrespondence
#print axioms StrongPerimetralTurning.SemanticallyDefinedArithmeticGodelPerimetralConclusion
#print axioms StrongPerimetralTurning.semanticallyDefinedArithmeticGodelPerimetralConclusion
#print axioms StrongPerimetralTurning.SemanticallyDefinedArithmeticGodelDiagnostic
#print axioms StrongPerimetralTurning.semanticallyDefinedArithmeticGodelDiagnostic
/- AXIOM_AUDIT_END -/
