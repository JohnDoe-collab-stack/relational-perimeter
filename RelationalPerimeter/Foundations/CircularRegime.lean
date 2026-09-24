import RelationalPerimeter.Foundations.ResidualContinuation

/- The proposition-valued definitions below are intentionally transparent,
   and the independent input families intentionally keep distinct universes. -/
set_option linter.defProp false
set_option linter.checkUnivs false

namespace StrongPerimetralTurning

universe uE uI uK uD uP uN uEnd uLoop uA uB uV

/-! ## Core circular regime

This layer separates the structural regime data from the historical circular
refinement and supplies the direct core path.  The historical rich turning
wrapper remains available separately. -/

structure CoreCircularResidualContext
    (P : CircularPresentation)
    (history : RootedGeneratedHistory P) where
  extension : PerimeterExtension P history
  positive : PositiveContinuation extension

def coreCircularBoundaryType
    (P : CircularPresentation)
    (history : RootedGeneratedHistory P) : Type _ :=
  AbstractSegmentedTurning.CorePositiveResidualBoundary
    (perimetralBoundaryGenerator P)
    (fun _candidate => CoreCircularResidualContext P _candidate)
    (fun {_candidate} context =>
      History.Occurrence context.extension.continuation)
    (NonClosingPosition P.perimeter)
    (FinalRequirement P)
    (finalRequirementContractible P)
    history

def coreCircularPositiveResidualBoundary
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (extension : PerimeterExtension P history)
    (positive : PositiveContinuation extension)
    (core : SegmentedResidualRole.ResidualDeterminationCore
      (NonClosingPosition P.perimeter)
      (FinalRequirement P)
      (History.Occurrence extension.continuation)
      (finalRequirementContractible P)) :
    coreCircularBoundaryType P history :=
  { context := { extension := extension, positive := positive }
    strict :=
      { continuation := positive.path
        historyExact := by
          change History.append (perimeterHistory P)
            positive.path.toHistory = history.history
          rw [← positive.historyExact]
          exact extension.recompose }
    core := core
    positive :=
      { occurrence :=
          transportOccurrence positive.historyExact.symm
            positive.path.lastOccurrence } }

structure CoreResidualClosureInterpretation
    {P : CircularPresentation}
    (history : RootedGeneratedHistory P) where
  boundary : coreCircularBoundaryType P history
  residualOccurrence :
    History.Occurrence boundary.context.extension.continuation
  residualOccurrenceIsPositive :
    residualOccurrence = boundary.positive.occurrence
  residualLabelIsResidual :
    boundary.core.newLabel residualOccurrence =
      .inr (finalRequirementContractible P).center
  obstruction : PositiveClosureObstruction P

def coreInterpretResidual
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (boundary : coreCircularBoundaryType P history)
    (unique : SegmentedResidualRole.CoreUniqueResidualOccurrence
      boundary.core) :
    CoreResidualClosureInterpretation history :=
  { boundary := boundary
    residualOccurrence := unique.occurrence
    residualOccurrenceIsPositive :=
      (unique.unique boundary.positive.occurrence).symm
    residualLabelIsResidual := unique.labelIsResidual
    obstruction := P.positiveClosureObstruction }

structure CoreResidualClosureAttempt
    {P : CircularPresentation}
    (history : RootedGeneratedHistory P)
    (interpretation : CoreResidualClosureInterpretation history) where
  explicitTotalization : ExplicitTotalization P
  implicitTotalization : ImplicitTotalization P

def rejectCoreResidualClosureAttempt
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    {interpretation : CoreResidualClosureInterpretation history}
    (attempt : CoreResidualClosureAttempt history interpretation) : False :=
  interpretation.obstruction.rejectsContraction
    (explicitTotalizationContractsClosureDifference
      attempt.explicitTotalization).initialPoleContraction

def CoreCircularPositiveBranch
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (extension : PerimeterExtension P history)
    (positive : PositiveContinuation extension) : Type _ :=
    Σ core : SegmentedResidualRole.ResidualDeterminationCore
      (NonClosingPosition P.perimeter)
      (FinalRequirement P)
      (History.Occurrence extension.continuation)
      (finalRequirementContractible P),
    CoreResidualClosureAttempt
        _
        (coreInterpretResidual
        (coreCircularPositiveResidualBoundary extension positive core)
        (AbstractSegmentedTurning.CorePositiveResidualBoundary.uniqueResidualOccurrence
          (coreCircularPositiveResidualBoundary extension positive core)))

structure CoreCircularRefinement
    (P : CircularPresentation)
    (history : RootedGeneratedHistory P) where
  extension : PerimeterExtension P history
  positiveBranch :
    (positive : PositiveContinuation extension) →
      CoreCircularPositiveBranch extension positive

def identityCoreCircularRefinement (P : CircularPresentation) :
    CoreCircularRefinement P (perimeterDeployment P) :=
  { extension := identityPerimeterExtension P
    positiveBranch := fun positive =>
      False.elim (rootContinuation_not_positive P positive) }

def CircularRefinement.toCoreCircularRefinement
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (refinement : CircularRefinement P history) :
    CoreCircularRefinement P history :=
  { extension := refinement.extension
    positiveBranch := fun positive =>
      let richAttempt := refinement.realizesFinal positive
      let core :=
        refinement.toLabelled.toSegmentedResidualExtension
          |>.toResidualUniquenessKernel
          |>.toDeterminationCore
      ⟨core,
        { explicitTotalization := richAttempt.explicitTotalization
          implicitTotalization := richAttempt.implicitTotalization }⟩ }

theorem coreCircularRefinement_history_eq_perimeter
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (refinement : CoreCircularRefinement P history) :
    history = perimeterDeployment P := by
  cases History.appendRootOrPositive
      (perimeterHistory P) refinement.extension.continuation with
  | inl rootData =>
      rcases rootData with ⟨endpointEquality, continuationEquality⟩
      exact rootedGeneratedHistory_ext endpointEquality.down
        ((heq_of_eq refinement.extension.recompose.symm).trans
          continuationEquality.down)
  | inr positiveData =>
      rcases positiveData with ⟨positive, continuationEquality⟩
      let positiveContinuation : PositiveContinuation refinement.extension :=
        { path := positive
          historyExact := continuationEquality.down }
      rcases refinement.positiveBranch positiveContinuation with
        ⟨core, attempt⟩
      exact False.elim (rejectCoreResidualClosureAttempt attempt)

theorem circularRefinement_nonempty_iff_coreCircularRefinement_nonempty
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P} :
    Nonempty (CircularRefinement P history) ↔
      Nonempty (CoreCircularRefinement P history) := by
  constructor
  · rintro ⟨refinement⟩
    exact ⟨refinement.toCoreCircularRefinement⟩
  · rintro ⟨refinement⟩
    have historyEquality :=
      coreCircularRefinement_history_eq_perimeter refinement
    cases historyEquality
    exact ⟨identityCircularRefinement P⟩

/- Regime completeness by carrier classification: no operational field of
   `CircularRefinement` is reconstructed from the independent specification. -/
def circularSpecification_complete
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (satisfaction : CircularSpecificationSatisfaction P history) :
    CircularRefinement P history := by
  have historyEquality :
      history = perimeterDeployment P :=
    satisfaction.eq_perimeter
  cases historyEquality
  exact identityCircularRefinement P

def oneStepFaithfulLabelling
    (P : CircularPresentation) :
    FaithfulPerimeterLabelling P (oneStepAfterPerimeter P)
      (oneStepAfterPerimeter_is_extension P) :=
  { label := fun occurrence =>
      match occurrence with
      | .last => .inr .distinguished
      | .earlier earlier => .inl (occurrenceToRequirement P earlier)
    preservesNonClosingLabels := by
      intro position
      exact congrArg Sum.inl
        (requirementToOccurrence_toRequirement P position)
    requirementFaithful := by
      intro first second labelEquality
      cases first with
      | last =>
          cases second with
          | last => rfl
          | earlier earlier => cases labelEquality
      | earlier firstEarlier =>
          cases second with
          | last => cases labelEquality
          | earlier secondEarlier =>
              have positionEquality :
                  occurrenceToRequirement P firstEarlier =
                    occurrenceToRequirement P secondEarlier :=
                Sum.inl.inj labelEquality
              exact congrArg History.Occurrence.earlier
                ((occurrenceToRequirement_toOccurrence P firstEarlier).symm.trans
                  ((congrArg (requirementToOccurrence P) positionEquality).trans
                    (occurrenceToRequirement_toOccurrence P secondEarlier))) }

def oneStepFaithfullyLabelledExtension
    (P : CircularPresentation) :
    FaithfullyLabelledPerimeterExtension P (oneStepAfterPerimeter P) :=
  { extension := oneStepAfterPerimeter_is_extension P
    labelling := oneStepFaithfulLabelling P }

/- The one-step boundary occurrence is the segmented component of the
   abstract turning.  Circular closure data is absent from this adapter. -/
def oneStepSegmentedBoundary
    (P : CircularPresentation) :
    AbstractSegmentedTurning.SegmentedBoundary
      (perimetralBoundaryGenerator P)
      (NonClosingPosition P.perimeter)
      (FinalRequirement P)
      (History.Occurrence (perimeterHistory P))
      (History.Occurrence
        (oneStepFaithfullyLabelledExtension P).continuation)
      (History.Occurrence (oneStepAfterPerimeter P).history)
      (perimeterInternalRoleRealization P)
      (finalRequirementContractible P) :=
  let positive := oneStepAfterPerimeter_positiveContinuation P
  { extension :=
      (oneStepFaithfullyLabelledExtension P).toSegmentedResidualExtension
    positive :=
      { occurrence :=
          transportOccurrence positive.historyExact.symm
            positive.path.lastOccurrence } }

def oneStepResidualPositive
    (P : CircularPresentation) :
    SegmentedResidualRole.PositiveNewPart
      (History.Occurrence
        (oneStepFaithfullyLabelledExtension P).continuation) :=
  (oneStepAfterPerimeter_positiveContinuation P).toResidualPositive

/- This is the positive occurrence stored by the segmented boundary itself.
   The equality is exported so the residual result can be checked against the
   exact producer field rather than only against an adapter defined alongside
   it. -/
theorem oneStepResidualPositive_agrees_with_segmentedBoundary
    (P : CircularPresentation) :
    (oneStepResidualPositive P).occurrence =
      (oneStepSegmentedBoundary P).positive.occurrence :=
  rfl

def oneStepReconstructedInternalCompletion
    (P : CircularPresentation) :
    SegmentedResidualRole.ExactInternalCompletion
      ((oneStepFaithfullyLabelledExtension P).toSegmentedResidualExtension
        |>.toResidualUniquenessKernel) :=
  (oneStepFaithfullyLabelledExtension P).reconstructedInternalCompletion
    (oneStepAfterPerimeter_positiveContinuation P)

def oneStepReconstructedInternalRealization
    (P : CircularPresentation) :
    SegmentedResidualRole.ExactInternalRealization
      (NonClosingPosition P.perimeter)
      (History.Occurrence (perimeterHistory P)) :=
  (oneStepReconstructedInternalCompletion P).toExactInternalRealization

theorem oneStepReconstructed_roleToOccurrence_agrees
    (P : CircularPresentation)
    (position : NonClosingPosition P.perimeter) :
    (oneStepReconstructedInternalRealization P).roleToOccurrence position =
      requirementToOccurrence P position :=
  (oneStepFaithfullyLabelledExtension P)
    |>.reconstructed_roleToOccurrence_agrees
      (oneStepAfterPerimeter_positiveContinuation P) position

theorem oneStepReconstructed_occurrenceToRole_agrees
    (P : CircularPresentation)
    (occurrence : History.Occurrence (perimeterHistory P)) :
    (oneStepReconstructedInternalRealization P).occurrenceToRole occurrence =
      occurrenceToRequirement P occurrence :=
  (oneStepFaithfullyLabelledExtension P)
    |>.reconstructed_occurrenceToRole_agrees
      (oneStepAfterPerimeter_positiveContinuation P) occurrence

def oneStepWeakResidualOccurrence
    (P : CircularPresentation) :
    SegmentedResidualRole.KernelUniqueResidualOccurrence
      ((oneStepFaithfullyLabelledExtension P).toSegmentedResidualExtension
        |>.toResidualUniquenessKernel) :=
  SegmentedResidualRole.positiveKernel_hasUniqueResidualOccurrence
    ((oneStepFaithfullyLabelledExtension P).toSegmentedResidualExtension
      |>.toResidualUniquenessKernel)
    (oneStepResidualPositive P)

def oneStepPublicResidualOccurrence
    (P : CircularPresentation) :
    SegmentedResidualRole.UniqueResidualOccurrence
      (oneStepFaithfullyLabelledExtension P).toSegmentedResidualExtension :=
  SegmentedResidualRole.positiveExtension_hasUniqueResidualOccurrence
    (oneStepFaithfullyLabelledExtension P).toSegmentedResidualExtension
    (oneStepResidualPositive P)

theorem oneStepResidualOccurrence_agrees
    (P : CircularPresentation) :
    (oneStepWeakResidualOccurrence P).occurrence =
      (oneStepPublicResidualOccurrence P).occurrence :=
  rfl

theorem oneStepWeakResidualOccurrence_label_is_final
    (P : CircularPresentation) :
    let kernel :=
      (oneStepFaithfullyLabelledExtension P).toSegmentedResidualExtension
        |>.toResidualUniquenessKernel
    kernel.label
        (kernel.embedNew (oneStepWeakResidualOccurrence P).occurrence) =
      .inr FinalRequirement.distinguished :=
  (oneStepWeakResidualOccurrence P).labelIsResidual

theorem oneStepWeakResidualOccurrence_unique
    (P : CircularPresentation)
    (other : History.Occurrence
      (oneStepFaithfullyLabelledExtension P).continuation) :
    other = (oneStepWeakResidualOccurrence P).occurrence :=
  (oneStepWeakResidualOccurrence P).unique other

structure FinalJunctionRealization
    (P : CircularPresentation)
    (history : RootedGeneratedHistory P) where
  interpretation : FinalClosureInterpretation P history
  attempt : BilateralClosureAttemptAt interpretation

namespace FinalJunctionRealization

def toBilateralContractions
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (realization : FinalJunctionRealization P history) :
    realization.attempt.Contractions :=
  realization.attempt.contractions

def toExplicitContractedClosureDifference
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (realization : FinalJunctionRealization P history) :
    ContractedClosureDifference P :=
  realization.attempt.explicitContraction

def toImplicitContractedClosureDifference
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (realization : FinalJunctionRealization P history) :
    ContractedClosureDifference P :=
  realization.attempt.implicitContraction

def toContractedClosureDifference
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (realization : FinalJunctionRealization P history) :
    ContractedClosureDifference P :=
  realization.toExplicitContractedClosureDifference

def endpointEquality
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (realization : FinalJunctionRealization P history) :
    P.leftEndpoint = P.rightEndpoint :=
  realization.toContractedClosureDifference.endpointContraction

def toTotalLoop
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (realization : FinalJunctionRealization P history) : P.TotalLoop :=
  realization.toContractedClosureDifference.toTotalLoop

end FinalJunctionRealization

structure FinalLoopRealization
    (P : CircularPresentation)
    (history : RootedGeneratedHistory P) where
  witness : FinalJunctionRealization P history

def FinalJunctionRealization.toFinalLoopRealization
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (realization : FinalJunctionRealization P history) :
    FinalLoopRealization P history :=
  ⟨realization⟩

namespace FinalLoopRealization

def toTotalLoop
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
  (realization : FinalLoopRealization P history) : P.TotalLoop :=
  realization.witness.toTotalLoop

def toContractedClosureDifference
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (realization : FinalLoopRealization P history) :
    ContractedClosureDifference P :=
  realization.witness.toContractedClosureDifference

def endpointEquality
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (realization : FinalLoopRealization P history) :
    P.leftEndpoint = P.rightEndpoint :=
  realization.toContractedClosureDifference.endpointContraction

end FinalLoopRealization

structure FinalIdentification
    (P : CircularPresentation)
    (history : RootedGeneratedHistory P) where
  witness : FinalLoopRealization P history

namespace FinalLoopRealization

def toFinalIdentification
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (realization : FinalLoopRealization P history) :
    FinalIdentification P history :=
  ⟨realization⟩

end FinalLoopRealization

namespace FinalIdentification

def toTotalLoop
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (identification : FinalIdentification P history) : P.TotalLoop :=
  identification.witness.toTotalLoop

def toContractedClosureDifference
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (identification : FinalIdentification P history) :
    ContractedClosureDifference P :=
  identification.witness.toContractedClosureDifference

def endpointEquality
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (identification : FinalIdentification P history) :
    P.leftEndpoint = P.rightEndpoint :=
  identification.witness.endpointEquality

end FinalIdentification

def refinementOutcome
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (refinement : CircularRefinement P history) :
    PLift (history = perimeterDeployment P) ⊕
      FinalJunctionRealization P history := by
  cases History.appendRootOrPositive
      (perimeterHistory P) refinement.continuation with
  | inl rootData =>
      rcases rootData with ⟨endpointEquality, continuationEquality⟩
      apply Sum.inl
      exact ⟨rootedGeneratedHistory_ext endpointEquality.down
        ((heq_of_eq refinement.recompose.symm).trans
          continuationEquality.down)⟩
  | inr positiveData =>
      rcases positiveData with ⟨positive, continuationEquality⟩
      let positiveContinuation : PositiveContinuation refinement.extension :=
        { path := positive
          historyExact := continuationEquality.down }
      let boundary :=
        finalBoundaryOccurrence refinement.toLabelled positiveContinuation
      let interpretation := finalClosureInterpretation boundary
      exact .inr
        { interpretation := interpretation
          attempt := refinement.realizesFinal positiveContinuation }

def rejectFinalJunctionRealization
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (realization : FinalJunctionRealization P history) : False :=
  realization.attempt.rejectExplicit

def rejectFinalJunctionRealizationImplicit
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (realization : FinalJunctionRealization P history) : False :=
  realization.attempt.rejectImplicit

def rejectFinalLoopRealization
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (realization : FinalLoopRealization P history) : False :=
  rejectFinalJunctionRealization realization.witness

def rejectFinalIdentification
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (identification : FinalIdentification P history) : False :=
  rejectFinalLoopRealization identification.witness

/- A positive circular boundary context keeps the faithful segmented
   extension and the positive free continuation in the same dependent
   object.  No totalization is present at this level. -/
structure CircularResidualBoundaryContext
    (P : CircularPresentation)
    (history : RootedGeneratedHistory P) where
  labelled : FaithfullyLabelledPerimeterExtension P history
  positive : PositiveContinuation labelled.extension

def circularBoundaryNewOccurrence
    (P : CircularPresentation)
    {history : RootedGeneratedHistory P}
    (context : CircularResidualBoundaryContext P history) : Type _ :=
  History.Occurrence context.labelled.continuation

def circularBoundaryCombinedOccurrence
    (P : CircularPresentation)
    {history : RootedGeneratedHistory P}
    (_context : CircularResidualBoundaryContext P history) : Type _ :=
  History.Occurrence history.history

def circularPositiveResidualBoundary
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (refinement : CircularRefinement P history)
    (positive : PositiveContinuation refinement.extension) :
    AbstractSegmentedTurning.PositiveResidualBoundary
      (perimetralBoundaryGenerator P)
      (CircularResidualBoundaryContext P)
      (circularBoundaryNewOccurrence P)
      (circularBoundaryCombinedOccurrence P)
      (NonClosingPosition P.perimeter)
      (FinalRequirement P)
      (History.Occurrence (perimeterHistory P))
      (perimeterInternalRoleRealization P)
      (finalRequirementContractible P)
      history :=
  { context :=
      { labelled := refinement.toLabelled
        positive := positive }
    strict :=
      { continuation := positive.path
        historyExact := by
          change History.append (perimeterHistory P)
            positive.path.toHistory = history.history
          rw [← positive.historyExact]
          exact refinement.recompose }
    extension := refinement.toLabelled.toSegmentedResidualExtension
    positive :=
      { occurrence :=
          transportOccurrence positive.historyExact.symm
            positive.path.lastOccurrence } }

def analyzeCircularRefinementThroughResidual
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (refinement : CircularRefinement P history) :
    PLift (history = perimeterDeployment P) ⊕
      AbstractSegmentedTurning.PositiveResidualBoundary
        (perimetralBoundaryGenerator P)
        (CircularResidualBoundaryContext P)
        (circularBoundaryNewOccurrence P)
        (circularBoundaryCombinedOccurrence P)
        (NonClosingPosition P.perimeter)
        (FinalRequirement P)
        (History.Occurrence (perimeterHistory P))
        (perimeterInternalRoleRealization P)
        (finalRequirementContractible P)
        history := by
  cases History.appendRootOrPositive
      (perimeterHistory P) refinement.continuation with
  | inl rootData =>
      rcases rootData with ⟨endpointEquality, continuationEquality⟩
      apply Sum.inl
      exact ⟨rootedGeneratedHistory_ext endpointEquality.down
        ((heq_of_eq refinement.recompose.symm).trans
          continuationEquality.down)⟩
  | inr positiveData =>
      rcases positiveData with ⟨positive, continuationEquality⟩
      let positiveContinuation : PositiveContinuation refinement.extension :=
        { path := positive
          historyExact := continuationEquality.down }
      exact .inr
        (circularPositiveResidualBoundary refinement positiveContinuation)

/- The circular interpretation retains the boundary built from the unique
   residual occurrence and relates it to the canonical final-boundary view
   on which bilateral closure is attempted.  Thus the residual occurrence
   is not discarded when closure semantics is introduced. -/
structure ResidualFinalClosureInterpretation
    (P : CircularPresentation)
    (history : RootedGeneratedHistory P) where
  context : CircularResidualBoundaryContext P history
  segmentedExtension : SegmentedResidualRole.FaithfulExtension
    (NonClosingPosition P.perimeter)
    (FinalRequirement P)
    (History.Occurrence (perimeterHistory P))
    (History.Occurrence context.labelled.continuation)
    (History.Occurrence history.history)
    (perimeterInternalRoleRealization P)
    (finalRequirementContractible P)
  residualOccurrence : History.Occurrence context.labelled.continuation
  residualLabelIsFinal :
    segmentedExtension.label
        (segmentedExtension.embedNew residualOccurrence) =
      .inr (finalRequirementContractible P).center
  residualOccurrenceIsCanonical :
    residualOccurrence =
      transportOccurrence context.positive.historyExact.symm
        context.positive.path.lastOccurrence
  closure : FinalClosureInterpretation P history
  closureIsCanonical :
    closure =
      finalClosureInterpretation
        (finalBoundaryOccurrence context.labelled context.positive)
  residualOccurrenceIsClosureBoundary :
    context.labelled.newOccurrence residualOccurrence =
      closure.boundary.historyOccurrence

def interpretCircularResidual
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (boundary : AbstractSegmentedTurning.PositiveResidualBoundary
      (perimetralBoundaryGenerator P)
      (CircularResidualBoundaryContext P)
      (circularBoundaryNewOccurrence P)
      (circularBoundaryCombinedOccurrence P)
      (NonClosingPosition P.perimeter)
      (FinalRequirement P)
      (History.Occurrence (perimeterHistory P))
      (perimeterInternalRoleRealization P)
      (finalRequirementContractible P)
      history)
    (unique : SegmentedResidualRole.UniqueResidualOccurrence
      boundary.extension) :
    ResidualFinalClosureInterpretation P history :=
  let canonicalOccurrence :=
    transportOccurrence boundary.context.positive.historyExact.symm
      boundary.context.positive.path.lastOccurrence
  let canonicalBoundary :=
    finalBoundaryOccurrence boundary.context.labelled
      boundary.context.positive
  { context := boundary.context
    segmentedExtension := boundary.extension
    residualOccurrence := unique.occurrence
    residualLabelIsFinal := unique.labelIsResidual
    residualOccurrenceIsCanonical :=
      (unique.unique canonicalOccurrence).symm
    closure := finalClosureInterpretation canonicalBoundary
    closureIsCanonical := rfl
    residualOccurrenceIsClosureBoundary := by
      change boundary.context.labelled.newOccurrence unique.occurrence =
        boundary.context.labelled.newOccurrence canonicalOccurrence
      exact congrArg boundary.context.labelled.newOccurrence
        (unique.unique canonicalOccurrence).symm }

structure ResidualBilateralClosureAttempt
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (interpretation : ResidualFinalClosureInterpretation P history) where
  attempt : BilateralClosureAttemptAt interpretation.closure

theorem rejectResidualBilateralClosureAttempt
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (interpretation : ResidualFinalClosureInterpretation P history)
    (attempt : ResidualBilateralClosureAttempt interpretation) : False :=
  attempt.attempt.rejectExplicit

def circularResidualBranch
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (refinement : CircularRefinement P history)
    (positive : PositiveContinuation refinement.extension) :
    Σ boundary : AbstractSegmentedTurning.PositiveResidualBoundary
      (perimetralBoundaryGenerator P)
      (CircularResidualBoundaryContext P)
      (circularBoundaryNewOccurrence P)
      (circularBoundaryCombinedOccurrence P)
      (NonClosingPosition P.perimeter)
      (FinalRequirement P)
      (History.Occurrence (perimeterHistory P))
      (perimeterInternalRoleRealization P)
      (finalRequirementContractible P)
      history,
      ResidualBilateralClosureAttempt
        (interpretCircularResidual boundary
          boundary.uniqueResidualOccurrence) := by
  let boundary := circularPositiveResidualBoundary refinement positive
  refine ⟨boundary, ?_⟩
  refine ⟨?_⟩
  change BilateralClosureAttemptAt
    (finalClosureInterpretation
      (finalBoundaryOccurrence refinement.toLabelled positive))
  exact refinement.realizesFinal positive

def analyzeCircularRegimeWithResidualAttempt
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (refinement : CircularRefinement P history) :
    PLift (history = perimeterDeployment P) ⊕
      (Σ boundary : AbstractSegmentedTurning.PositiveResidualBoundary
        (perimetralBoundaryGenerator P)
        (CircularResidualBoundaryContext P)
        (circularBoundaryNewOccurrence P)
        (circularBoundaryCombinedOccurrence P)
        (NonClosingPosition P.perimeter)
        (FinalRequirement P)
        (History.Occurrence (perimeterHistory P))
        (perimeterInternalRoleRealization P)
        (finalRequirementContractible P)
        history,
        ResidualBilateralClosureAttempt
          (interpretCircularResidual boundary
            boundary.uniqueResidualOccurrence)) := by
  cases History.appendRootOrPositive
      (perimeterHistory P) refinement.continuation with
  | inl rootData =>
      rcases rootData with ⟨endpointEquality, continuationEquality⟩
      apply Sum.inl
      exact ⟨rootedGeneratedHistory_ext endpointEquality.down
        ((heq_of_eq refinement.recompose.symm).trans
          continuationEquality.down)⟩
  | inr positiveData =>
      rcases positiveData with ⟨positive, continuationEquality⟩
      let positiveContinuation : PositiveContinuation refinement.extension :=
        { path := positive
          historyExact := continuationEquality.down }
      exact .inr
        (circularResidualBranch refinement positiveContinuation)

/-! ## Direct core coupled circular regime

This is the production coupled path.  Its regime, interpretation, attempt,
and residual boundary are all core-level data; the historical rich regime is
not used to determine the residual occurrence. -/
def perimetralCoreCoupledRegime
    (P : CircularPresentation) :
    AbstractSegmentedTurning.CoreCoupledObstructedRegime
      (perimetralBoundaryGenerator P)
      (fun history => CoreCircularResidualContext P history)
      (fun {_history} context =>
        History.Occurrence context.extension.continuation)
      (NonClosingPosition P.perimeter)
      (FinalRequirement P)
      (finalRequirementContractible P) :=
  { Regime := CoreCircularRefinement P
    Interpretation := fun history => CoreResidualClosureInterpretation history
    Attempt := fun {history} interpretation =>
      CoreResidualClosureAttempt history interpretation
    canonicalRegime := identityCoreCircularRefinement P
    interpretResidual := fun boundary unique =>
      coreInterpretResidual boundary unique
    analyzeRegime := by
      intro candidate refinement
      cases History.appendRootOrPositive
          (perimeterHistory P) refinement.extension.continuation with
      | inl rootData =>
          rcases rootData with ⟨endpointEquality, continuationEquality⟩
          exact .inl ⟨rootedGeneratedHistory_ext endpointEquality.down
            ((heq_of_eq refinement.extension.recompose.symm).trans
              continuationEquality.down)⟩
      | inr positiveData =>
          rcases positiveData with ⟨positive, continuationEquality⟩
          let positiveContinuation : PositiveContinuation refinement.extension :=
            { path := positive
              historyExact := continuationEquality.down }
          rcases refinement.positiveBranch positiveContinuation with
            ⟨core, attempt⟩
          let boundary :=
            coreCircularPositiveResidualBoundary
              refinement.extension positiveContinuation core
          exact .inr ⟨boundary, attempt⟩
    rejectTotalization := by
      intro candidate interpretation attempt
      exact rejectCoreResidualClosureAttempt attempt }

theorem perimetralCoreCoupledInterpretation_occurrence
    (P : CircularPresentation)
    {history : RootedGeneratedHistory P}
    (boundary : coreCircularBoundaryType P history)
    (unique : SegmentedResidualRole.CoreUniqueResidualOccurrence
      boundary.core) :
    ((perimetralCoreCoupledRegime P).interpretResidual boundary unique).residualOccurrence =
      unique.occurrence := by
  rfl

def perimetralCoreObstructedRegime
    (P : CircularPresentation) :
    AbstractSegmentedTurning.ObstructedRegime
      (perimetralBoundaryGenerator P) :=
  (perimetralCoreCoupledRegime P).toObstructedRegime

def perimetralCoupledRegime
    (P : CircularPresentation) :
    AbstractSegmentedTurning.CoupledObstructedRegime
      (perimetralBoundaryGenerator P)
      (CircularResidualBoundaryContext P)
      (circularBoundaryNewOccurrence P)
      (circularBoundaryCombinedOccurrence P)
      (NonClosingPosition P.perimeter)
      (FinalRequirement P)
      (History.Occurrence (perimeterHistory P))
      (perimeterInternalRoleRealization P)
      (finalRequirementContractible P) :=
  { Regime := CircularRefinement P
    Interpretation := ResidualFinalClosureInterpretation P
    Attempt := ResidualBilateralClosureAttempt
    canonicalRegime := identityCircularRefinement P
    interpretResidual := interpretCircularResidual
    analyzeRegime := analyzeCircularRegimeWithResidualAttempt
    rejectTotalization := rejectResidualBilateralClosureAttempt }

/- A circular refinement has exactly the generic obstructed-regime shape:
   it is either the canonical perimeter or supplies a bilateral totalization
   attempt, and every such attempt is rejected. -/
def perimetralObstructedRegime
    (P : CircularPresentation) :
    AbstractSegmentedTurning.ObstructedRegime
      (perimetralBoundaryGenerator P) :=
  (perimetralCoupledRegime P).toObstructedRegime

def oneStepCoreTurning
    (P : CircularPresentation) :
    AbstractSegmentedTurning.CoreTurningConclusion
      (oneStepCoreSegmentedBoundary P)
      (perimetralCoreObstructedRegime P) :=
  AbstractSegmentedTurning.coreTurning
    (oneStepCoreSegmentedBoundary P)
    (perimetralCoreObstructedRegime P)

/- Reattach the direct core turning to the historical rich boundary type.  The
   occurrence and its uniqueness come from the core result; only the public
   rich label is checked at this boundary. -/
def oneStepCoreTurning_toPublic
    (P : CircularPresentation) :
    AbstractSegmentedTurning.TurningConclusion
      (oneStepSegmentedBoundary P)
      (perimetralCoreObstructedRegime P) :=
  let coreResult := oneStepCoreTurning P
  { uniqueResidualOccurrence :=
      { occurrence := coreResult.uniqueResidualOccurrence.occurrence
        labelIsResidual := by rfl
        unique := fun other =>
          coreResult.uniqueResidualOccurrence.unique other }
    exactRelativeClassification := coreResult.exactRelativeClassification
    generatedContinuation := coreResult.generatedContinuation
    continuationIsStrict := coreResult.continuationIsStrict
    continuationOutsideRegime := coreResult.continuationOutsideRegime
    noStrictRegimeExtension := coreResult.noStrictRegimeExtension
    totalizationRejected := coreResult.totalizationRejected }

def perimetralCoreCoupledTurning
    (P : CircularPresentation) :
    AbstractSegmentedTurning.CoreCoupledTurningConclusion
      (perimetralCoreCoupledRegime P) :=
  AbstractSegmentedTurning.coreCoupledTurning
    (perimetralCoreCoupledRegime P)

def historicalCoupledTurningOfCircularPresentation
    (P : CircularPresentation) :
    AbstractSegmentedTurning.CoupledTurningConclusion
      (perimetralCoupledRegime P) :=
  AbstractSegmentedTurning.coupledTurning (perimetralCoupledRegime P)

def coupledTurningOfCircularPresentation
    (P : CircularPresentation) :
    AbstractSegmentedTurning.CoreCoupledTurningConclusion
      (perimetralCoreCoupledRegime P) :=
  perimetralCoreCoupledTurning P

/- The historical rich turning remains available under an explicit name. -/
def historicalAbstractTurningOfCircularPresentation
    (P : CircularPresentation) :
    AbstractSegmentedTurning.TurningConclusion
      (oneStepSegmentedBoundary P)
      (perimetralObstructedRegime P) :=
  AbstractSegmentedTurning.abstractTurning
    (oneStepSegmentedBoundary P)
    (perimetralObstructedRegime P)

/- The whole circle-independent turning theorem is now instantiated by the
   direct core path, its residual occurrence, and its core obstructed regime. -/
def abstractTurningOfCircularPresentation
    (P : CircularPresentation) :
    AbstractSegmentedTurning.TurningConclusion
      (oneStepSegmentedBoundary P)
      (perimetralCoreObstructedRegime P) := by
  exact oneStepCoreTurning_toPublic P

theorem oneStepCoreResidualOccurrence_agrees_with_weak
    (P : CircularPresentation) :
    (oneStepCoreResidualOccurrence P).occurrence =
      (oneStepWeakResidualOccurrence P).occurrence :=
  rfl

theorem oneStepCoreResidualOccurrence_agrees_with_consumedTurning
    (P : CircularPresentation) :
    (oneStepCoreResidualOccurrence P).occurrence =
      ((abstractTurningOfCircularPresentation P).uniqueResidualOccurrence).occurrence :=
  rfl

/- The abstract turning consumes the same residual occurrence as the weak
   producer-facing construction.  This is a direct agreement with the
   published consumer, not an agreement between two new adapters. -/
theorem oneStepWeakResidualOccurrence_agrees_with_consumedTurning
    (P : CircularPresentation) :
    (oneStepWeakResidualOccurrence P).occurrence =
      (abstractTurningOfCircularPresentation P).uniqueResidualOccurrence.occurrence :=
  (oneStepCoreResidualOccurrence_agrees_with_weak P).symm.trans
    (oneStepCoreResidualOccurrence_agrees_with_consumedTurning P)

theorem noIntermediateRefinement
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (refinement : CircularRefinement P history) :
    history = perimeterDeployment P :=
  (historicalCoupledTurningOfCircularPresentation P).exactRelativeClassification
    |>.regimeImpliesEquality refinement

structure ExactCircularRefinementClassification
    (P : CircularPresentation)
    (history : RootedGeneratedHistory P) : Type _ where
  refinementImpliesEquality :
    CircularRefinement P history → history = perimeterDeployment P
  equalityBuildsRefinement :
    history = perimeterDeployment P → CircularRefinement P history

def exactCircularRefinementClassification
    (P : CircularPresentation)
    (history : RootedGeneratedHistory P) :
    ExactCircularRefinementClassification P history :=
  let classification :=
    (historicalCoupledTurningOfCircularPresentation P).exactRelativeClassification
  { refinementImpliesEquality :=
      classification.regimeImpliesEquality
    equalityBuildsRefinement :=
      classification.equalityBuildsRegime }

theorem oneStepAfterPerimeter_notCircularRefinement
    (P : CircularPresentation) :
    CircularRefinement P (oneStepAfterPerimeter P) → False :=
  (historicalCoupledTurningOfCircularPresentation P).continuationOutsideRegime

def strictRefinementProducesFinalJunctionRealization
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (strict : StrictConstitutivePrefix (perimeterDeployment P) history)
    (refinement : CircularRefinement P history) :
    FinalJunctionRealization P history := by
  cases refinementOutcome refinement with
  | inl equality => exact False.elim (strictPrefix_ne strict equality.down)
  | inr realization => exact realization

def strictRefinementProducesFinalLoopRealization
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (strict : StrictConstitutivePrefix (perimeterDeployment P) history)
    (refinement : CircularRefinement P history) :
    FinalLoopRealization P history :=
  FinalJunctionRealization.toFinalLoopRealization
    (strictRefinementProducesFinalJunctionRealization strict refinement)

def strictRefinementProducesFinalIdentification
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (strict : StrictConstitutivePrefix (perimeterDeployment P) history)
    (refinement : CircularRefinement P history) :
    FinalIdentification P history :=
  (strictRefinementProducesFinalLoopRealization strict refinement).toFinalIdentification

def strictRefinementProducesTotalLoop
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (strict : StrictConstitutivePrefix (perimeterDeployment P) history)
    (refinement : CircularRefinement P history) : P.TotalLoop :=
  (strictRefinementProducesFinalLoopRealization strict refinement).toTotalLoop

/- Soundness of the circular regime relative to the independent specification:
   the regime's perimeter extension supplies local exactness, while strict
   refinement closure supplies the trajectory obligation. -/
def circularRefinement_soundSpecification
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (refinement : CircularRefinement P history) :
    CircularSpecificationSatisfaction P history :=
  { «local» :=
      refinement.extension.toExactNonClosingRealization
    trajectory :=
      fun strict =>
        strictRefinementProducesTotalLoop strict refinement }

theorem noStrictSamePerimeterExtension
    (P : CircularPresentation) :
    (Σ history : RootedGeneratedHistory P,
      StrictConstitutivePrefix (perimeterDeployment P) history ×
        CircularRefinement P history) → False :=
  (historicalCoupledTurningOfCircularPresentation P).noStrictRegimeExtension

inductive PerimetrallyAdmissible
    (P : CircularPresentation) : RootedGeneratedHistory P → Type _
  | properPartial
      {history : RootedGeneratedHistory P} :
      FreePartialRealization P history → PerimetrallyAdmissible P history
  | samePerimeter
      {history : RootedGeneratedHistory P} :
      CircularRefinement P history → PerimetrallyAdmissible P history

def admissible_is_prefix_of_perimeter
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P} :
    PerimetrallyAdmissible P history →
      ConstitutivePrefix history (perimeterDeployment P)
  | .properPartial partialPath => partial_is_prefix_of_perimeter partialPath
  | .samePerimeter refinement => by
      cases noIntermediateRefinement refinement
      exact prefixReflexive _

structure StrongPerimetralTurningCertificate
    (P : CircularPresentation) where
  initialClosureObstruction : PositiveClosureObstruction P
  initialClosureObstructionIsCanonical :
    initialClosureObstruction = P.positiveClosureObstruction
  engender :
    (source : PositiveConstitution P) →
      Σ target : PositiveConstitution P, GeneratedStep source target
  obstructionTransportedByEveryStep :
    {source target : PositiveConstitution P} →
      (step : GeneratedStep source target) →
        target.2.1.1.inheritedClosureObstruction =
          source.2.1.1.inheritedClosureObstruction
  deployment : RootedGeneratedHistory P
  generatedOnly : GeneratedOnlyByFreeConstruction deployment
  terminalClosureObstructionIsInitial :
    deployment.terminalClosureObstruction = P.positiveClosureObstruction
  exactPerimeter : ExactPerimeterRealization P deployment
  absorbsPartial :
    {history : RootedGeneratedHistory P} →
      FreePartialRealization P history → ConstitutivePrefix history deployment
  noIntermediate :
    {history : RootedGeneratedHistory P} →
      CircularRefinement P history → history = deployment
  rejectsExplicitTotalization : ExplicitTotalization P → False
  rejectsImplicitTotalization : ImplicitTotalization P → False
  rejectsFinalJunction :
    {history : RootedGeneratedHistory P} →
      FinalJunctionRealization P history → False
  rejectsFinalJunctionImplicit :
    {history : RootedGeneratedHistory P} →
      FinalJunctionRealization P history → False
  finalBoundaryFromPositive :
    {history : RootedGeneratedHistory P} →
    (labelled : FaithfullyLabelledPerimeterExtension P history) →
    (positive : PositiveContinuation labelled.extension) →
      FinalBoundaryOccurrence P history
  finalInterpretationFromPositive :
    {history : RootedGeneratedHistory P} →
    (labelled : FaithfullyLabelledPerimeterExtension P history) →
    (positive : PositiveContinuation labelled.extension) →
      FinalClosureInterpretation P history
  rejectsExplicitAttemptAt :
    {history : RootedGeneratedHistory P} →
    {interpretation : FinalClosureInterpretation P history} →
      BilateralClosureAttemptAt interpretation → False
  rejectsImplicitAttemptAt :
    {history : RootedGeneratedHistory P} →
    {interpretation : FinalClosureInterpretation P history} →
      BilateralClosureAttemptAt interpretation → False
  noStrictSamePerimeter :
    (Σ history : RootedGeneratedHistory P,
      StrictConstitutivePrefix deployment history ×
        CircularRefinement P history) → False
  continuesFreelyBeyondPerimeter :
    Σ target : PositiveConstitution P,
      GeneratedStep deployment.endpoint target

def strongPerimetralTurning
    (P : CircularPresentation) : StrongPerimetralTurningCertificate P :=
  { initialClosureObstruction := P.positiveClosureObstruction
    initialClosureObstructionIsCanonical := rfl
    engender := generate
    obstructionTransportedByEveryStep :=
      GeneratedStep.inheritedClosureObstructionExact
    deployment := perimeterDeployment P
    generatedOnly := perimeterDeployment_generatedOnly P
    terminalClosureObstructionIsInitial :=
      RootedGeneratedHistory.terminalClosureObstruction_is_initial _
    exactPerimeter := perimeterRealization P
    absorbsPartial := partial_is_prefix_of_perimeter
    noIntermediate := noIntermediateRefinement
    rejectsExplicitTotalization := explicitTotalizationRejected
    rejectsImplicitTotalization := implicitTotalizationRejected
    rejectsFinalJunction := rejectFinalJunctionRealization
    rejectsFinalJunctionImplicit := rejectFinalJunctionRealizationImplicit
    finalBoundaryFromPositive := finalBoundaryOccurrence
    finalInterpretationFromPositive := fun labelled positive =>
      finalClosureInterpretation
        (finalBoundaryOccurrence labelled positive)
    rejectsExplicitAttemptAt := BilateralClosureAttemptAt.rejectExplicit
    rejectsImplicitAttemptAt := BilateralClosureAttemptAt.rejectImplicit
    noStrictSamePerimeter := noStrictSamePerimeterExtension P
    continuesFreelyBeyondPerimeter :=
      generate (perimeterDeployment P).endpoint }


end StrongPerimetralTurning

/- AXIOM_AUDIT_BEGIN -/
#print axioms StrongPerimetralTurning.CoreCircularResidualContext
#print axioms StrongPerimetralTurning.StrongPerimetralTurningCertificate
#print axioms StrongPerimetralTurning.strongPerimetralTurning
/- AXIOM_AUDIT_END -/
