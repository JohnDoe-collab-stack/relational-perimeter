# Independent source excerpts

Map: labyrinth/knowledge.json

## th.residual — SegmentedResidualRole.ResidualDeterminationCore.occurrences_unique  SegmentedResidualRole.lean:136  ```lean
theorem occurrences_unique
    {InternalRole : Type uInternal}
    {ResidualRole : Type uResidual}
    {NewOccurrence : Type uNew}
    {residual : ContractibleRole ResidualRole}
    (core : ResidualDeterminationCore
      InternalRole ResidualRole NewOccurrence residual)
    (first second : NewOccurrence) :
    first = second := by
  have sameLabel :
      core.newLabel first = core.newLabel second :=
    (core.label_is_residual first).trans
      (core.label_is_residual second).symm
  exact core.newLabelInjective sameLabel

```

## th.residual — SegmentedResidualRole.positiveCore_hasUniqueResidualOccurrence  SegmentedResidualRole.lean:167  ```lean
def positiveCore_hasUniqueResidualOccurrence
    {InternalRole : Type uInternal}
    {ResidualRole : Type uResidual}
    {NewOccurrence : Type uNew}
    {residual : ContractibleRole ResidualRole}
    (core : ResidualDeterminationCore
      InternalRole ResidualRole NewOccurrence residual)
    (positive : PositiveNewPart NewOccurrence) :
    CoreUniqueResidualOccurrence core :=
  { occurrence := positive.occurrence
    labelIsResidual := core.label_is_residual positive.occurrence
    unique := fun other => core.occurrences_unique other positive.occurrence }

```

## th.internal-reconstruction — SegmentedResidualRole.ResidualUniquenessKernel.toExactInternalCompletion_of_positive  SegmentedResidualRole.lean:595  ```lean
def toExactInternalCompletion_of_positive
    {InternalRole : Type uInternal}
    {ResidualRole : Type uResidual}
    {OldOccurrence : Type uOld}
    {NewOccurrence : Type uNew}
    {ExtendedOccurrence : Type uExtended}
    {residual : ContractibleRole ResidualRole}
    (kernel : ResidualUniquenessKernel
      InternalRole ResidualRole OldOccurrence NewOccurrence
      ExtendedOccurrence residual)
    (positive : PositiveNewPart NewOccurrence)
    (embedOldInjective : Function.Injective kernel.embedOld) :
    ExactInternalCompletion kernel :=
  ExactReconstructionConditions.toExactInternalCompletion
    { oldLabelsInternal := kernel.oldLabelsInternal_of_positive positive
      embedOldInjective := embedOldInjective }

```

## th.abstract-exit — AbstractSegmentedTurning.ObstructedRegime.exactClassification  AbstractSegmentedTurning.lean:352  ```lean
def exactClassification
    {Carrier : Type uCarrier}
    {Extension : Carrier → Carrier → Type uExtension}
    {generator : BoundaryGenerator Carrier Extension}
    (obstructed : ObstructedRegime generator) :
    ExactRegimeClassification generator.boundary obstructed.Regime :=
  { regimeImpliesEquality := by
      intro candidate regime
      cases obstructed.classifyOrTotalize regime with
      | inl equality => exact equality.down
      | inr totalized =>
          exact False.elim
            (obstructed.rejectTotalization totalized.1 totalized.2)
    equalityBuildsRegime := by
      intro candidate equality
      cases equality
      exact obstructed.canonicalRegime }

```

## th.abstract-exit — AbstractSegmentedTurning.ObstructedRegime.continuation_outside_regime  AbstractSegmentedTurning.lean:370  ```lean
theorem continuation_outside_regime
    {Carrier : Type uCarrier}
    {Extension : Carrier → Carrier → Type uExtension}
    {generator : BoundaryGenerator Carrier Extension}
    (obstructed : ObstructedRegime generator) :
    obstructed.Regime generator.continuation → False := by
  intro regime
  exact generator.continuation_ne_boundary
    (obstructed.exactClassification.regimeImpliesEquality regime)

```

## th.transport-backward — ExactTypeTransport.backward_eq_of_forward_eq  ExactTypeTransport.lean:101  ```lean
theorem backward_eq_of_forward_eq
    {Source : Type uSource}
    {Target : Type uTarget}
    (first second : ExactTypeTransport Source Target)
    (forwardAgreement :
      (source : Source) → first.forward source = second.forward source)
    (target : Target) :
    first.backward target = second.backward target := by
  calc
    first.backward target =
      first.backward (second.forward (second.backward target)) := by
        rw [second.backwardForward]
    _ = first.backward (first.forward (second.backward target)) := by
        rw [forwardAgreement (second.backward target)]
    _ = second.backward target := first.forwardBackward _

```

## th.perimeter-exact — StrongPerimetralTurning.occurrenceToRequirement_toOccurrence  StrongPerimetralTurning.lean:3197  ```lean
theorem occurrenceToRequirement_toOccurrence
    (P : CircularPresentation)
    (occurrence : History.Occurrence (perimeterHistory P)) :
    requirementToOccurrence P (occurrenceToRequirement P occurrence) =
      occurrence :=
  deployOccurrence_position_roundTrip P P.perimeter
    FreeConstitution.root BoundaryDifference.initial occurrence

```

## th.perimeter-exact — StrongPerimetralTurning.requirementToOccurrence_toRequirement  StrongPerimetralTurning.lean:3205  ```lean
theorem requirementToOccurrence_toRequirement
    (P : CircularPresentation)
    (position : NonClosingPosition P.perimeter) :
    occurrenceToRequirement P (requirementToOccurrence P position) =
      position :=
  deployPosition_occurrence_roundTrip P P.perimeter
    FreeConstitution.root BoundaryDifference.initial position

/- These maps only reindex a supplied readout along the already established
   perimeter/occurrence correspondence.  They add no values and assert no
   semantic adequacy of the supplied readout. -/
```

## th.rooted-structure — StrongPerimetralTurning.ExactNonClosingRealization.realize_injective  StrongPerimetralTurning.lean:4040  ```lean
theorem realize_injective
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (realization : ExactNonClosingRealization P history) :
    Function.Injective realization.realize := by
  intro first second equality
  have canonicalFirst :=
    (canonicalRequirementAgreement P first).locatedStepExact
  have canonicalSecond :=
    (canonicalRequirementAgreement P second).locatedStepExact
  have realizedFirst := (realization.agreement first).locatedStepExact
  have realizedSecond := (realization.agreement second).locatedStepExact
  have realizedAgree :
      (realization.realize first).locatedStep =
        (realization.realize second).locatedStep :=
    congrArg (fun occurrence => occurrence.locatedStep) equality
  have stepsAgree :
      (requirementToOccurrence P first).locatedStep =
        (requirementToOccurrence P second).locatedStep :=
    canonicalFirst.trans
      ((realizedFirst.symm.trans (realizedAgree.trans realizedSecond)).trans
        canonicalSecond.symm)
  rcases History.OccurrencePrecedes.trichotomy
      (requirementToOccurrence P first)
      (requirementToOccurrence P second) with
    occurrenceEquality | forward | backward
  · exact requirementToOccurrence_injective P occurrenceEquality
  · rcases forward.sourceCursorFuture with ⟨future⟩
    exact False.elim
      (CursorFuture.irreflexive _
        (congrArg
          (fun step : History.LocatedStep (@GeneratedStep P) => step.source.1)
          stepsAgree ▸ future))
  · rcases backward.sourceCursorFuture with ⟨future⟩
    exact False.elim
      (CursorFuture.irreflexive _
        (congrArg
          (fun step : History.LocatedStep (@GeneratedStep P) => step.source.1)
          stepsAgree ▸ future))

/- A locally exact realization inside a genuine generated history must preserve
   the structural precedence of the perimeter.  The proof excludes reversed
   chronology by composing the two strict cursor futures into an impossible
   cursor loop. -/
```

## th.rooted-structure — StrongPerimetralTurning.ExactNonClosingRealization.preservesPrecedence  StrongPerimetralTurning.lean:4084  ```lean
theorem preservesPrecedence
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (realization : ExactNonClosingRealization P history)
    {first second : NonClosingPosition P.perimeter}
    (precedes : NonClosingPrecedes P.perimeter first second) :
    History.OccurrencePrecedes
      (realization.realize first) (realization.realize second) := by
  rcases History.OccurrencePrecedes.trichotomy
      (realization.realize first) (realization.realize second) with
    equality | forward | backward
  · have positionEquality : first = second :=
      realization.realize_injective equality
    exact False.elim (precedes.ne positionEquality)
  · exact forward
  · rcases precedes.sourceCursorFuture with ⟨canonicalForward⟩
    rcases backward.sourceCursorFuture with ⟨realizedBackward⟩
    have firstCursorExact := (realization.agreement first).sourceCursorExact
    have secondCursorExact := (realization.agreement second).sourceCursorExact
    have forwardRealized : CursorFuture P
        (realization.realize first).locatedStep.source.1
        (realization.realize second).locatedStep.source.1 :=
      firstCursorExact.symm ▸ secondCursorExact.symm ▸ canonicalForward
    exact False.elim
      (CursorFuture.irreflexive _
        (forwardRealized.trans realizedBackward))

/- Canonically adjacent requirements are realized by immediately adjacent
   occurrences in a genuine generated history.  Any positive gap would become
   a strict cursor future from a cursor to itself after transporting the exact
   endpoint data. -/
```

## th.rooted-structure — StrongPerimetralTurning.ExactNonClosingRealization.preservesNext  StrongPerimetralTurning.lean:4115  ```lean
theorem preservesNext
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (realization : ExactNonClosingRealization P history)
    {first second : NonClosingPosition P.perimeter}
    (next : NonClosingNext P.perimeter first second) :
    History.OccurrenceNext
      (realization.realize first) (realization.realize second) := by
  have occurrencePrecedes : History.OccurrencePrecedes
      (realization.realize first) (realization.realize second) :=
    realization.preservesPrecedence next.toPrecedes
  rcases occurrencePrecedes.next_or_positiveGap with immediate | gap
  · exact immediate
  · rcases gap with ⟨future⟩
    have canonicalEndpointEquality :=
      NonClosingNext.target_eq_source next
        FreeConstitution.root BoundaryDifference.initial
    have endpointEquality :
        (realization.realize first).locatedStep.target =
          (realization.realize second).locatedStep.source :=
      (realization.agreement first).targetStateExact.trans
        (canonicalEndpointEquality.trans
          (realization.agreement second).sourceStateExact.symm)
    have cursorEquality := congrArg Sigma.fst endpointEquality
    have futureLoop : CursorFuture P
        (realization.realize second).locatedStep.source.1
        (realization.realize second).locatedStep.source.1 :=
      cursorEquality ▸ future
    exact False.elim (CursorFuture.irreflexive _ futureLoop)

/- The canonical perimeter occurrences can be read inside any exact local
   realization without introducing a second realization structure. -/
```

## th.factorization — StrongPerimetralTurning.ExactNonClosingRealization.toPerimeterExtension  StrongPerimetralTurning.lean:4654  ```lean
def toPerimeterExtension
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (realization : ExactNonClosingRealization P history) :
    PerimeterExtension P history := by
  let factor :=
    factorDeployRemainingFromExactOccurrences P P.perimeter
      FreeConstitution.root BoundaryDifference.initial history.endpoint
      history.history realization.realize realization.realize_injective
      (fun position => (realization.agreement position).locatedStepExact)
  exact
      { continuation := factor.1
        recompose := factor.2.down }

```

## th.positive-continuation — StrongPerimetralTurning.oneStepAfterPerimeterStrict  StrongPerimetralTurning.lean:2705  ```lean
def oneStepAfterPerimeterStrict
    (P : CircularPresentation) :
    StrictConstitutivePrefix
      (perimeterDeployment P) (oneStepAfterPerimeter P) :=
  { continuation :=
      { predecessor := perimeterEndpoint P
        priorHistory := .root
        lastStep := (generate_after_perimeter P).2 }
    historyExact := rfl }

```

## th.positive-continuation — StrongPerimetralTurning.oneStepAfterPerimeter_ne  StrongPerimetralTurning.lean:2715  ```lean
theorem oneStepAfterPerimeter_ne
    (P : CircularPresentation) :
    oneStepAfterPerimeter P ≠ perimeterDeployment P :=
  fun equality => strictPrefix_ne (oneStepAfterPerimeterStrict P) equality

/- The canonical perimeter and its freely generated successor instantiate the
   circle-independent boundary generator. -/
```

## th.no-return — StrongPerimetralTurning.positiveGeneratedHistory_source_ne_target  StrongPerimetralTurning.lean:2556  ```lean
theorem positiveGeneratedHistory_source_ne_target
    {P : CircularPresentation}
    {source target : PositiveConstitution P}
    (positive : History.Positive (@GeneratedStep P) source target) :
    source ≠ target := by
  intro equality
  have cursorEquality : source.1 = target.1 := congrArg Sigma.fst equality
  exact positiveCursorAdvance_irreflexive
    (cast
      (congrArg (PositiveCursorAdvance P source.1) cursorEquality.symm)
      (positiveGeneratedHistory_cursorAdvance positive))


/- A generated history whose endpoints are equal cannot contain any step
   occurrence.  The root case has no occurrences by construction.  Any
   extended history determines a positive history, whose endpoints are forced
   to be distinct by generated cursor advance. -/
```

## th.labelled-residual — StrongPerimetralTurning.FaithfullyLabelledPerimeterExtension.newOccurrence_label_is_final  StrongPerimetralTurning.lean:5211  ```lean
theorem newOccurrence_label_is_final
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (labelled : FaithfullyLabelledPerimeterExtension P history)
    (occurrence : History.Occurrence labelled.continuation) :
    labelled.label (labelled.newOccurrence occurrence) =
      .inr .distinguished :=
  labelled.toSegmentedResidualExtension
    |>.newOccurrence_label_is_residual occurrence

```

## th.labelled-residual — StrongPerimetralTurning.FaithfullyLabelledPerimeterExtension.continuation_occurrences_unique  StrongPerimetralTurning.lean:5221  ```lean
theorem continuation_occurrences_unique
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (labelled : FaithfullyLabelledPerimeterExtension P history)
    (first second : History.Occurrence labelled.continuation) :
    first = second :=
  labelled.toSegmentedResidualExtension
    |>.newOccurrences_unique first second

```

## th.circular-classification — StrongPerimetralTurning.exactCircularRefinementClassification  StrongPerimetralTurning.lean:6853  ```lean
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

```

## th.circular-classification — StrongPerimetralTurning.oneStepAfterPerimeter_notCircularRefinement  StrongPerimetralTurning.lean:6864  ```lean
theorem oneStepAfterPerimeter_notCircularRefinement
    (P : CircularPresentation) :
    CircularRefinement P (oneStepAfterPerimeter P) → False :=
  (historicalCoupledTurningOfCircularPresentation P).continuationOutsideRegime

```

## th.specification — StrongPerimetralTurning.circularRefinement_soundSpecification  StrongPerimetralTurning.lean:6906  ```lean
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

```

## th.specification — StrongPerimetralTurning.circularSpecification_complete  StrongPerimetralTurning.lean:6086  ```lean
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

```

## th.turning — StrongPerimetralTurning.strongPerimetralTurning  StrongPerimetralTurning.lean:7001  ```lean
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

/-! ## Derived structural length

`Nat` enters only here, after the constitutive boundary and its maximality have
already been proved.  It measures an already constituted history; it does not
generate either the perimeter or its deployment. -/

```

## th.numeric-readout — StrongPerimetralTurning.admissible_length_le_perimeter  StrongPerimetralTurning.lean:7138  ```lean
theorem admissible_length_le_perimeter
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (admissible : PerimetrallyAdmissible P history) :
    history.history.length ≤ (perimeterDeployment P).history.length :=
  prefix_length_le (admissible_is_prefix_of_perimeter admissible)

```

## th.concrete-interpretation — StrongPerimetralTurning.exactlyInterpretHistory  StrongPerimetralTurning.lean:7607  ```lean
def exactlyInterpretHistory
    {P : CircularPresentation}
    (A : ConcreteContinuationAlgebra P)
    {source target : PositiveConstitution P}
    (history : GeneratedHistory source target) :
    ExactHistoryInterpretation A history (A.realizeHistory history) :=
  { forwardOccurrence := concreteForwardOccurrence A history
    backwardOccurrence := concreteBackwardOccurrence A history
    forwardBackward := concreteBackwardForward A history
    backwardForward := concreteForwardBackward A history
    occurrenceAgreement := concreteOccurrenceAgreement A history }

/-! ## Typed regime-exit diagnostics

The exact concrete interpretation and the circular-refinement regime are kept
as distinct type families on the same rooted-history carrier. The perimetral
structures below compose the abstract diagnostic with the additional positive
witness explaining its geometric origin. -/

```

## th.separator-order — StrongPerimetralTurning.Example.permutedExample_not_order_preserved  StrongPerimetralTurning.lean:8161  ```lean
theorem permutedExample_not_order_preserved :
    ¬ SemanticOrderPreserved permutedExampleRealization := by
  intro preserved
  have forward :=
    preserved exampleP1 exampleP2 exampleP1_precedes_exampleP2
  change
    (permutedExampleRealization.realize exampleP1).val <
      (permutedExampleRealization.realize exampleP2).val
    at forward
  exact Nat.lt_asymm forward permutedExample_reverses_first_two

/-! ### Experimental interleaving separator -/

/- These two extra occurrences are genuine locally generated steps beyond the
   perimeter.  They are constructed without a `History`, so their insertion in
   the semantic trace does not reintroduce global composability. -/
```

## th.separator-bridge — StrongPerimetralTurning.Example.interleavedExample_order_preserved  StrongPerimetralTurning.lean:8284  ```lean
def interleavedExample_order_preserved :
    SemanticOrderPreserved interleavedExampleRealization := by
  intro first second precedes
  cases precedes with
  | here_later position =>
      cases position with
      | here =>
          change 0 < 2
          exact Nat.zero_lt_succ 1
      | later position =>
          cases position with
          | here =>
              change 0 < 4
              exact Nat.zero_lt_succ 3
          | later impossible => nomatch impossible
  | later_later precedes =>
      cases precedes with
      | here_later position =>
          cases position with
          | here =>
              change 2 < 4
              exact Nat.succ_lt_succ
                (Nat.succ_lt_succ (Nat.zero_lt_succ 1))
          | later impossible => nomatch impossible
      | later_later precedes =>
          cases precedes with
          | here_later impossible => nomatch impossible
          | later_later deeper => cases deeper


```

## th.separator-bridge — StrongPerimetralTurning.Example.interleavedExample_no_effective_bridge_p1_p2  StrongPerimetralTurning.lean:8356  ```lean
theorem interleavedExample_no_effective_bridge_p1_p2 :
    EffectiveConstitutiveBridge
      interleavedExampleTrace
      (interleavedExampleRealization.realize exampleP1)
      (interleavedExampleRealization.realize exampleP2) → False := by
  intro effective
  exact effectiveBridge_between_empty_of_next
    interleavedExampleRealization
    exampleP1_next_exampleP2
    effective
    interleavedExample_extra1_between

/- Symmetrically, `extra2` cannot be exactly an occurrence of a generated
   constitutive bridge between p2 and p3. -/
```

## th.separator-injectivity — FoundationalSeparators.weakened_core_does_not_force_uniqueness  labyrinth/probes/FoundationalSeparators.lean.in:33  ```lean
theorem weakened_core_does_not_force_uniqueness :
    ¬ ((first second : Bool) → first = second) := by
  intro unique
  exact new_occurrences_distinct (unique false true)

/- Independent spot check of the referee's old-carrier counterexample.
   This variant uses Option Unit as its extended carrier and places the role at true. -/
```

## th.separator-injectivity — FoundationalSeparators.residual_label_not_injective  labyrinth/probes/FoundationalSeparators.lean.in:27  ```lean
theorem residual_label_not_injective :
    ¬ Function.Injective constantResidualLabel := by
  intro injective
  exact new_occurrences_distinct (@injective false true rfl)

/- Contractibility and exclusion of internal labels do not replace injectivity. -/
```

## th.separator-transport — FoundationalSeparators.swap_does_not_preserve_order  labyrinth/probes/FoundationalSeparators.lean.in:80  ```lean
theorem swap_does_not_preserve_order :
    ¬ Before (swapTransport.forward false) (swapTransport.forward true) := by
  intro reversed
  cases reversed

/- A presentation index does not by itself give the bare final role extra data. -/
```

## th.final-role-carrier — FoundationalSeparators.finalRoleUnitTransport  labyrinth/probes/FoundationalSeparators.lean.in:86  ```lean
def finalRoleUnitTransport (P : StrongPerimetralTurning.CircularPresentation) :
    ExactTypeTransport (StrongPerimetralTurning.FinalRequirement P) Unit :=
  { forward := fun _ => ()
    backward := fun _ => .distinguished
    forwardBackward := fun role => by cases role; rfl
    backwardForward := fun point => by cases point; rfl }

```

## th.separator-old-completion — FoundationReferee.collapsedOld_no_exact_completion  research/agents/referee-foundations/IndependentProbes.lean.in:35  ```lean
theorem collapsedOld_no_exact_completion :
    ExactInternalCompletion collapsedOldKernel → False := by
  intro completion
  have impossible := completion.occurrenceRoundTrip true
  exact Bool.noConfusion impossible

-- Removing label injectivity permits two distinct new occurrences.
```

## th.separator-old-completion — FoundationalSeparators.positive_kernel_does_not_force_internal_completion  labyrinth/probes/FoundationalSeparators.lean.in:65  ```lean
theorem positive_kernel_does_not_force_internal_completion :
    SegmentedResidualRole.ExactInternalCompletion collapsedOldOptionKernel → False := by
  intro completion
  have impossible : (true : Bool) = false := completion.occurrenceRoundTrip false
  cases impossible

```

## th.positive-split — StrongPerimetralTurning.PositiveCircularPresentation  RelationalPerimeter/Constitution/PositivePresentation.lean:18  ```lean
structure PositiveCircularPresentation where
  Explicit : Type uE
  Implicit : Type uI
  Compatible : Implicit → Explicit → Type uK
  Difference : Type uD
  Provenance : Difference → Type uP
  initialNode : LocalNode Explicit Implicit Compatible Difference Provenance
  perimeter : PerimeterSpine Compatible initialNode
  perimeterPositive : NonClosingPosition perimeter
  finalJunction : Compatible perimeter.finalNode.implicit initialNode.explicit

/- The initial difference has endpoint readings without imposing their separation. -/
```

## th.positive-split — StrongPerimetralTurning.CircularClosureObstruction.endpointsSeparated  RelationalPerimeter/Constitution/PositivePresentation.lean:62  ```lean
theorem endpointsSeparated
    {P : PositiveCircularPresentation} {boundary : EndpointBoundary P}
    (obstruction : CircularClosureObstruction P boundary) :
    boundary.leftEndpoint ≠ boundary.rightEndpoint :=
  fun equality => obstruction.rejectTotalLoop
    (obstruction.closeFromIdentification equality)

```

## th.positive-split — RelationalPerimeter.Constitution.Examples.identifiedBoundary_no_obstruction  RelationalPerimeter/Constitution/Examples.lean:46  ```lean
theorem identifiedBoundary_no_obstruction :
    CircularClosureObstruction positive identifiedBoundary → False :=
  CircularClosureObstruction.noObstructionOfIdentifiedEndpoints identifiedBoundary_eq

```

## th.positive-split — RelationalPerimeter.Constitution.Examples.same_positive_data  RelationalPerimeter/Constitution/Examples.lean:68  ```lean
theorem same_positive_data : obstructed.toPositiveCircularPresentation = positive := rfl

/- A raw witnessed chain can repeat its node values. This does not identify
   occurrences or generated cursors in the historical free execution. -/
```

## th.circular-bridge — StrongPerimetralTurning.CircularPresentation.positive_roundTrip  RelationalPerimeter/Constitution/CircularPresentationBridge.lean:48  ```lean
theorem positive_roundTrip
    (positive : PositiveCircularPresentation)
    (boundary : EndpointBoundary positive)
    (obstruction : CircularClosureObstruction positive boundary) :
    (ofPositive positive boundary obstruction).toPositiveCircularPresentation = positive :=
  rfl

```

## th.circular-bridge — StrongPerimetralTurning.CircularPresentation.boundary_roundTrip  RelationalPerimeter/Constitution/CircularPresentationBridge.lean:55  ```lean
theorem boundary_roundTrip
    (positive : PositiveCircularPresentation)
    (boundary : EndpointBoundary positive)
    (obstruction : CircularClosureObstruction positive boundary) :
    (ofPositive positive boundary obstruction).endpointBoundary = boundary := by
  cases boundary
  rfl

```

## th.circular-bridge — StrongPerimetralTurning.CircularPresentation.obstruction_roundTrip  RelationalPerimeter/Constitution/CircularPresentationBridge.lean:63  ```lean
theorem obstruction_roundTrip
    (positive : PositiveCircularPresentation)
    (boundary : EndpointBoundary positive)
    (obstruction : CircularClosureObstruction positive boundary) :
    (ofPositive positive boundary obstruction).closureObstruction = obstruction := by
  cases boundary
  cases obstruction
  rfl

```

## th.circular-bridge — StrongPerimetralTurning.CircularPresentation.historical_roundTrip  RelationalPerimeter/Constitution/CircularPresentationBridge.lean:72  ```lean
theorem historical_roundTrip (P : CircularPresentation) :
    ofPositive P.toPositiveCircularPresentation P.endpointBoundary P.closureObstruction = P := by
  cases P
  rfl

```

## th.boundary-extraction — RelationalPerimeter.Constitution.closingBoundary  RelationalPerimeter/Constitution/BoundaryTransport.lean:31  ```lean
def closingBoundary (P : StrongPerimetralTurning.PositiveCircularPresentation) :
    ConstitutiveBoundary :=
  { Explicit := P.Explicit
    Implicit := P.Implicit
    Compatible := P.Compatible
    source := P.perimeter.finalNode.implicit
    target := P.initialNode.explicit
    junction := P.finalJunction
    Difference := P.Difference
    Provenance := P.Provenance
    difference := P.initialNode.difference
    provenance := P.initialNode.provenance }

/- Exactness of the five carriers is deliberately separate from preservation
   of the three indices and of the two distinguished witnesses. -/
```

## th.boundary-extraction — PositiveFoundationReferee.extractedBoundaryReadsExactData  research/agents/referee-positive-foundations/IndependentProbes.lean.in:145  ```lean
theorem extractedBoundaryReadsExactData (P : PositiveCircularPresentation) :
    (closingBoundary P).junction = P.finalJunction ∧
    (closingBoundary P).provenance = P.initialNode.provenance := ⟨rfl, rfl⟩

-- Contractibility does not prevent the exact transport of fibres across boundaries.
```

## th.boundary-calculus — RelationalPerimeter.Constitution.BoundaryTransport.reverse  RelationalPerimeter/Constitution/BoundaryTransport.lean:79  ```lean
def reverse {B C : ConstitutiveBoundary} (transport : BoundaryTransport B C) :
    BoundaryTransport C B :=
  { explicit := transport.explicit.reverse
    implicit := transport.implicit.reverse
    difference := transport.difference.reverse
    junction := transport.junction.reverse
    provenance := transport.provenance.reverse
    sourceExact :=
      (congrArg transport.implicit.backward transport.sourceExact.symm).trans
        (transport.implicit.forwardBackward B.source)
    targetExact :=
      (congrArg transport.explicit.backward transport.targetExact.symm).trans
        (transport.explicit.forwardBackward B.target)
    differenceExact :=
      (congrArg transport.difference.backward transport.differenceExact.symm).trans
        (transport.difference.forwardBackward B.difference)
    junctionExact :=
      (congrArg transport.junction.backward transport.junctionExact.symm).trans
        (transport.junction.forwardBackward B.junction)
    provenanceExact :=
      (congrArg transport.provenance.backward transport.provenanceExact.symm).trans
        (transport.provenance.forwardBackward B.provenance) }

```

## th.boundary-calculus — RelationalPerimeter.Constitution.BoundaryTransport.compose  RelationalPerimeter/Constitution/BoundaryTransport.lean:102  ```lean
def compose {B C D : ConstitutiveBoundary}
    (first : BoundaryTransport B C) (second : BoundaryTransport C D) :
    BoundaryTransport B D :=
  { explicit := first.explicit.compose second.explicit
    implicit := first.implicit.compose second.implicit
    difference := first.difference.compose second.difference
    junction := first.junction.compose second.junction
    provenance := first.provenance.compose second.provenance
    sourceExact :=
      (congrArg second.implicit.forward first.sourceExact).trans second.sourceExact
    targetExact :=
      (congrArg second.explicit.forward first.targetExact).trans second.targetExact
    differenceExact :=
      (congrArg second.difference.forward first.differenceExact).trans second.differenceExact
    junctionExact :=
      (congrArg second.junction.forward first.junctionExact).trans second.junctionExact
    provenanceExact :=
      (congrArg second.provenance.forward first.provenanceExact).trans second.provenanceExact }

/- Pointwise laws quantify over all five selected carriers. They require no
   equality of structures containing functions. -/
```

## th.boundary-calculus — RelationalPerimeter.Constitution.BoundaryTransport.identity_left  RelationalPerimeter/Constitution/BoundaryTransport.lean:133  ```lean
theorem identity_left {B C : ConstitutiveBoundary} (transport : BoundaryTransport B C) :
    ForwardAgreement ((identity B).compose transport).toBoundaryCarrierTransport
      transport.toBoundaryCarrierTransport :=
  ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl⟩

```

## th.boundary-calculus — RelationalPerimeter.Constitution.BoundaryTransport.identity_right  RelationalPerimeter/Constitution/BoundaryTransport.lean:138  ```lean
theorem identity_right {B C : ConstitutiveBoundary} (transport : BoundaryTransport B C) :
    ForwardAgreement (transport.compose (identity C)).toBoundaryCarrierTransport
      transport.toBoundaryCarrierTransport :=
  ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl⟩

```

## th.boundary-calculus — RelationalPerimeter.Constitution.BoundaryTransport.compose_associative  RelationalPerimeter/Constitution/BoundaryTransport.lean:143  ```lean
theorem compose_associative {B C D E : ConstitutiveBoundary}
    (first : BoundaryTransport B C) (second : BoundaryTransport C D)
    (third : BoundaryTransport D E) :
    ForwardAgreement ((first.compose second).compose third).toBoundaryCarrierTransport
      (first.compose (second.compose third)).toBoundaryCarrierTransport :=
  ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl⟩

```

## th.boundary-calculus — RelationalPerimeter.Constitution.BoundaryTransport.reverse_left  RelationalPerimeter/Constitution/BoundaryTransport.lean:150  ```lean
theorem reverse_left {B C : ConstitutiveBoundary} (transport : BoundaryTransport B C) :
    ForwardAgreement (transport.compose transport.reverse).toBoundaryCarrierTransport
      (identity B).toBoundaryCarrierTransport :=
  ⟨transport.explicit.forwardBackward, transport.implicit.forwardBackward,
    transport.difference.forwardBackward, transport.junction.forwardBackward,
    transport.provenance.forwardBackward⟩

```

## th.boundary-calculus — RelationalPerimeter.Constitution.BoundaryTransport.reverse_right  RelationalPerimeter/Constitution/BoundaryTransport.lean:157  ```lean
theorem reverse_right {B C : ConstitutiveBoundary} (transport : BoundaryTransport B C) :
    ForwardAgreement (transport.reverse.compose transport).toBoundaryCarrierTransport
      (identity C).toBoundaryCarrierTransport :=
  ⟨transport.explicit.backwardForward, transport.implicit.backwardForward,
    transport.difference.backwardForward, transport.junction.backwardForward,
    transport.provenance.backwardForward⟩

```

## th.boundary-calculus — RelationalPerimeter.Constitution.BoundaryTransport.backward_of_forward  RelationalPerimeter/Constitution/BoundaryTransport.lean:185  ```lean
theorem backward_of_forward {B C : ConstitutiveBoundary}
    {first second : BoundaryCarrierTransport B C}
    (agreement : ForwardAgreement first second) : BackwardAgreement first second :=
  ⟨ExactTypeTransport.backward_eq_of_forward_eq _ _ agreement.explicit,
    ExactTypeTransport.backward_eq_of_forward_eq _ _ agreement.implicit,
    ExactTypeTransport.backward_eq_of_forward_eq _ _ agreement.difference,
    ExactTypeTransport.backward_eq_of_forward_eq _ _ agreement.junction,
    ExactTypeTransport.backward_eq_of_forward_eq _ _ agreement.provenance⟩

```

## th.equipped-role — RelationalPerimeter.Constitution.EquippedFinalRole.canonical  RelationalPerimeter/Constitution/BoundaryTransport.lean:232  ```lean
def canonical (B : ConstitutiveBoundary) : EquippedFinalRole B := ⟨B.junction, rfl⟩

```

## th.equipped-role — RelationalPerimeter.Constitution.EquippedFinalRole.unique  RelationalPerimeter/Constitution/BoundaryTransport.lean:228  ```lean
theorem unique {B : ConstitutiveBoundary} (first second : EquippedFinalRole B) :
    first = second :=
  ext (first.witnessExact.trans second.witnessExact.symm)

```

## th.equipped-role — RelationalPerimeter.Constitution.EquippedFinalRole.source_preserved  RelationalPerimeter/Constitution/BoundaryTransport.lean:246  ```lean
theorem source_preserved {B C : ConstitutiveBoundary}
    (map : BoundaryTransport B C) (role : EquippedFinalRole B) :
    map.implicit.forward role.source = (role.transport map).source := map.sourceExact

```

## th.equipped-role — RelationalPerimeter.Constitution.EquippedFinalRole.target_preserved  RelationalPerimeter/Constitution/BoundaryTransport.lean:250  ```lean
theorem target_preserved {B C : ConstitutiveBoundary}
    (map : BoundaryTransport B C) (role : EquippedFinalRole B) :
    map.explicit.forward role.target = (role.transport map).target := map.targetExact

```

## th.equipped-role — RelationalPerimeter.Constitution.EquippedFinalRole.provenance_preserved  RelationalPerimeter/Constitution/BoundaryTransport.lean:254  ```lean
theorem provenance_preserved {B C : ConstitutiveBoundary}
    (map : BoundaryTransport B C) (role : EquippedFinalRole B) :
    map.provenance.forward role.provenance = (role.transport map).provenance := map.provenanceExact

```

## th.equipped-role — RelationalPerimeter.Constitution.EquippedFinalRole.transport_identity  RelationalPerimeter/Constitution/BoundaryTransport.lean:258  ```lean
theorem transport_identity {B : ConstitutiveBoundary} (role : EquippedFinalRole B) :
    role.transport (BoundaryTransport.identity B) = role := by
  cases role
  rfl

```

## th.equipped-role — RelationalPerimeter.Constitution.EquippedFinalRole.transport_compose  RelationalPerimeter/Constitution/BoundaryTransport.lean:263  ```lean
theorem transport_compose {B C D : ConstitutiveBoundary}
    (first : BoundaryTransport B C) (second : BoundaryTransport C D)
    (role : EquippedFinalRole B) :
    (role.transport first).transport second = role.transport (first.compose second) := rfl

```

## th.equipped-role — RelationalPerimeter.Constitution.EquippedFinalRole.exactTransport  RelationalPerimeter/Constitution/BoundaryTransport.lean:280  ```lean
def exactTransport {B C : ConstitutiveBoundary} (map : BoundaryTransport B C) :
    ExactTypeTransport (EquippedFinalRole B) (EquippedFinalRole C) :=
  { forward := fun role => role.transport map
    backward := fun role => role.transport map.reverse
    forwardBackward := fun role => transport_reverse map role
    backwardForward := fun role => transport_reverse_right map role }

```

## th.separator-closing-witness — RelationalPerimeter.Constitution.Examples.closingSwap_preserves_indices  RelationalPerimeter/Constitution/Examples.lean:89  ```lean
theorem closingSwap_preserves_indices :
    closingSwap.implicit.forward boundary.source = boundary.source ∧
    closingSwap.explicit.forward boundary.target = boundary.target ∧
    closingSwap.difference.forward boundary.difference = boundary.difference :=
  ⟨rfl, rfl, rfl⟩

```

## th.separator-closing-witness — RelationalPerimeter.Constitution.Examples.closingSwap_cannot_lift  RelationalPerimeter/Constitution/Examples.lean:100  ```lean
theorem closingSwap_cannot_lift
    (rich : BoundaryTransport boundary boundary)
    (sameCarriers : rich.toBoundaryCarrierTransport = closingSwap) : False := by
  have agreement := congrArg
    (fun carrier : BoundaryCarrierTransport boundary boundary =>
      carrier.junction.forward boundary.junction) sameCarriers
  exact closingSwap_does_not_preserve_witness
    (agreement.symm.trans rich.junctionExact)

```

## th.separator-provenance-witness — PositiveFoundationReferee.swapProvenanceOnly  research/agents/referee-positive-foundations/IndependentProbes.lean.in:115  ```lean
def swapProvenanceOnly : BoundaryCarrierTransport (boolBoundary false) (boolBoundary false) where
  explicit := ExactTypeTransport.reflexive _
  implicit := ExactTypeTransport.reflexive _
  difference := ExactTypeTransport.reflexive _
  junction := ExactTypeTransport.reflexive _
  provenance := flip

```

## th.separator-provenance-witness — PositiveFoundationReferee.provenanceSwapCannotEnrich  research/agents/referee-positive-foundations/IndependentProbes.lean.in:130  ```lean
theorem provenanceSwapCannotEnrich
    (rich : BoundaryTransport (boolBoundary false) (boolBoundary false))
    (givenMap : rich.toBoundaryCarrierTransport = swapProvenanceOnly) : False := by
  have preservation := rich.provenanceExact
  change rich.toBoundaryCarrierTransport.provenance.forward false = false at preservation
  rw [givenMap] at preservation
  exact Bool.noConfusion preservation

-- A generic direct reconstruction check, independent of the author's roundTrip theorem.
```

## th.separator-positive-recurrence — RelationalPerimeter.Constitution.Examples.raw_node_return  RelationalPerimeter/Constitution/Examples.lean:72  ```lean
theorem raw_node_return : positive.perimeter.finalNode = positive.initialNode := rfl

```

## th.separator-positive-recurrence — PositiveFoundationReferee.repeatedRawNode  research/agents/referee-positive-foundations/IndependentProbes.lean.in:47  ```lean
theorem repeatedRawNode : circle.perimeter.finalNode = circle.initialNode := rfl

```

## th.closing-shape-bridge — RelationalPerimeter.Constitution.ConstitutiveBoundary.toClosingBoundaryShape  RelationalPerimeter/Constitution/ClosingBoundary.lean:62  ```lean
def toClosingBoundaryShape (B : ConstitutiveBoundary) : ClosingBoundaryShape :=
  { Explicit := B.Explicit
    Implicit := B.Implicit
    Compatible := B.Compatible
    source := B.source
    target := B.target
    Difference := B.Difference
    Provenance := B.Provenance
    difference := B.difference
    provenance := B.provenance }

```

## th.closing-shape-bridge — RelationalPerimeter.Constitution.PointedClosingBoundary.toConstitutiveBoundary  RelationalPerimeter/Constitution/ClosingBoundary.lean:83  ```lean
def toConstitutiveBoundary {B : ClosingBoundaryShape} (pointed : PointedClosingBoundary B) :
    ConstitutiveBoundary :=
  { Explicit := B.Explicit
    Implicit := B.Implicit
    Compatible := B.Compatible
    source := B.source
    target := B.target
    junction := pointed.junction
    Difference := B.Difference
    Provenance := B.Provenance
    difference := B.difference
    provenance := B.provenance }

```

## th.closing-shape-bridge — RelationalPerimeter.Constitution.PointedClosingBoundary.shape_roundTrip  RelationalPerimeter/Constitution/ClosingBoundary.lean:96  ```lean
theorem shape_roundTrip {B : ClosingBoundaryShape} (pointed : PointedClosingBoundary B) :
    pointed.toConstitutiveBoundary.toClosingBoundaryShape = B := rfl

```

## th.closing-shape-bridge — RelationalPerimeter.Constitution.PointedClosingBoundary.pointing_roundTrip  RelationalPerimeter/Constitution/ClosingBoundary.lean:99  ```lean
theorem pointing_roundTrip {B : ClosingBoundaryShape} (pointed : PointedClosingBoundary B) :
    pointed.toConstitutiveBoundary.toPointedClosingBoundary = pointed := by
  cases pointed
  rfl

/- The role remains an inhabited singleton over each fixed pointing. These views
   do not identify two pointings with different closing witnesses. -/
```

## th.closing-shape-bridge — RelationalPerimeter.Constitution.ConstitutiveBoundary.boundary_roundTrip  RelationalPerimeter/Constitution/ClosingBoundary.lean:123  ```lean
theorem boundary_roundTrip (B : ConstitutiveBoundary) :
    B.toPointedClosingBoundary.toConstitutiveBoundary = B := rfl

```

## th.closing-pointing-exact — RelationalPerimeter.Constitution.ClosingBoundaryShape.pointingTransport  RelationalPerimeter/Constitution/ClosingBoundary.lean:41  ```lean
def pointingTransport (B : ClosingBoundaryShape) :
    ExactTypeTransport (ClosingWitness B) (PointedClosingBoundary B) :=
  { forward := B.point
    backward := fun pointed => pointed.junction
    forwardBackward := fun _ => rfl
    backwardForward := fun pointed => by cases pointed; rfl }

```

## th.closing-pointing-exact — RelationalPerimeter.Constitution.ClosingBoundaryShape.nonempty_pointed_iff  RelationalPerimeter/Constitution/ClosingBoundary.lean:48  ```lean
theorem nonempty_pointed_iff (B : ClosingBoundaryShape) :
    Nonempty (PointedClosingBoundary B) ↔ Nonempty (ClosingWitness B) :=
  ⟨fun ⟨pointed⟩ => ⟨pointed.junction⟩, fun ⟨junction⟩ => ⟨B.point junction⟩⟩

```

## th.closing-pointing-exact — RelationalPerimeter.Constitution.ClosingBoundaryShape.noPointingOfEmpty  RelationalPerimeter/Constitution/ClosingBoundary.lean:52  ```lean
theorem noPointingOfEmpty (B : ClosingBoundaryShape)
    (empty : ClosingWitness B → False) : Nonempty (PointedClosingBoundary B) → False :=
  fun inhabited => by
    obtain ⟨pointed⟩ := inhabited
    exact empty pointed.junction

```

## th.closing-empty — RelationalPerimeter.Constitution.ClosingBoundaryShape.noFinalRoleOfEmpty  RelationalPerimeter/Constitution/ClosingBoundary.lean:136  ```lean
theorem noFinalRoleOfEmpty (B : ClosingBoundaryShape)
    (empty : ClosingWitness B → False) :
    (∃ pointed : PointedClosingBoundary B, Nonempty pointed.FinalRole) → False :=
  fun inhabited => by
    obtain ⟨junction⟩ := B.nonempty_finalRole_iff.mp inhabited
    exact empty junction

```

## th.closing-empty — RelationalPerimeter.Constitution.ClosingBoundaryExamples.empty_no_pointing  RelationalPerimeter/Constitution/ClosingBoundaryExamples.lean:31  ```lean
theorem empty_no_pointing : Nonempty (PointedClosingBoundary emptyShape) → False :=
  emptyShape.noPointingOfEmpty empty_has_no_junction

```

## th.closing-empty — RelationalPerimeter.Constitution.ClosingBoundaryExamples.empty_no_final_role  RelationalPerimeter/Constitution/ClosingBoundaryExamples.lean:34  ```lean
theorem empty_no_final_role :
    (∃ pointed : PointedClosingBoundary emptyShape, Nonempty pointed.FinalRole) → False :=
  emptyShape.noFinalRoleOfEmpty empty_has_no_junction

```

## th.closing-empty — RelationalPerimeter.Constitution.ClosingBoundaryExamples.empty_not_from_constitutive  RelationalPerimeter/Constitution/ClosingBoundaryExamples.lean:38  ```lean
theorem empty_not_from_constitutive
    (boundary : ConstitutiveBoundary.{0, 0, 0, 0, 0})
    (sameShape : boundary.toClosingBoundaryShape = emptyShape) : False := by
  have inhabited := boundary.shape_fibre_nonempty
  rw [sameShape] at inhabited
  obtain ⟨junction⟩ := inhabited
  exact empty_has_no_junction junction

```

## th.closing-role-choice — RelationalPerimeter.Constitution.PointedClosingBoundary.finalRole  RelationalPerimeter/Constitution/ClosingBoundary.lean:109  ```lean
def finalRole {B : ClosingBoundaryShape} (pointed : PointedClosingBoundary B) :
    pointed.FinalRole := EquippedFinalRole.canonical _

```

## th.closing-role-choice — RelationalPerimeter.Constitution.PointedClosingBoundary.finalRole_unique  RelationalPerimeter/Constitution/ClosingBoundary.lean:112  ```lean
theorem finalRole_unique {B : ClosingBoundaryShape} (pointed : PointedClosingBoundary B)
    (first second : pointed.FinalRole) : first = second :=
  EquippedFinalRole.unique first second

```

## th.closing-role-choice — RelationalPerimeter.Constitution.PointedClosingBoundary.finalRole_junction  RelationalPerimeter/Constitution/ClosingBoundary.lean:116  ```lean
theorem finalRole_junction {B : ClosingBoundaryShape} (pointed : PointedClosingBoundary B)
    (role : pointed.FinalRole) : role.witness = pointed.junction := role.witnessExact

```

## th.closing-role-choice — RelationalPerimeter.Constitution.ClosingBoundaryShape.nonempty_finalRole_iff  RelationalPerimeter/Constitution/ClosingBoundary.lean:130  ```lean
theorem nonempty_finalRole_iff (B : ClosingBoundaryShape) :
    (∃ pointed : PointedClosingBoundary B, Nonempty pointed.FinalRole) ↔
      Nonempty (ClosingWitness B) :=
  ⟨fun ⟨pointed, _⟩ => ⟨pointed.junction⟩,
    fun ⟨junction⟩ => ⟨B.point junction, ⟨(B.point junction).finalRole⟩⟩⟩

```

## th.closing-choice-multiplicity — RelationalPerimeter.Constitution.ClosingBoundaryExamples.unit_fibre_unique  RelationalPerimeter/Constitution/ClosingBoundaryExamples.lean:50  ```lean
theorem unit_fibre_unique (first second : ClosingWitness unitShape) : first = second := by
  cases first
  cases second
  rfl

```

## th.closing-choice-multiplicity — RelationalPerimeter.Constitution.ClosingBoundaryExamples.bool_pointings_distinct  RelationalPerimeter/Constitution/ClosingBoundaryExamples.lean:70  ```lean
theorem bool_pointings_distinct : falsePointing ≠ truePointing := by
  intro equality
  have witnesses := congrArg (fun pointed : PointedClosingBoundary boolShape =>
    pointed.junction) equality
  exact bool_witnesses_distinct witnesses

```

## th.closing-choice-multiplicity — RelationalPerimeter.Constitution.ClosingBoundaryExamples.bool_per_choice_role_unique  RelationalPerimeter/Constitution/ClosingBoundaryExamples.lean:84  ```lean
theorem bool_per_choice_role_unique (pointed : PointedClosingBoundary boolShape)
    (first second : pointed.FinalRole) : first = second :=
  pointed.finalRole_unique first second

```

## th.closing-choice-multiplicity — RelationalPerimeter.Constitution.ClosingBoundaryExamples.bool_closing_fibre_not_unique  RelationalPerimeter/Constitution/ClosingBoundaryExamples.lean:95  ```lean
theorem bool_closing_fibre_not_unique :
    (∀ first second : ClosingWitness boolShape, first = second) → False :=
  fun unique => bool_witnesses_distinct (unique false true)

```

## th.positive-formation-deployment — RelationalPerimeter.Constitution.PositiveFormation  RelationalPerimeter/Constitution/PositiveGeneration.lean:70  ```lean
structure PositiveFormation where
  Explicit : Type uE
  Implicit : Type uI
  Compatible : Implicit → Explicit → Type uK
  Difference : Type uD
  Provenance : Difference → Type uP
  State : Type uS
  node : State → LocalNode Explicit Implicit Compatible Difference Provenance
  Step : State → State → Type uStep
  compatibility : {source target : State} → Step source target →
    Compatible (node source).implicit (node target).explicit

```

## th.positive-formation-deployment — RelationalPerimeter.Constitution.PositiveHistory.deploy_start  RelationalPerimeter/Constitution/PositiveGeneration.lean:128  ```lean
theorem deploy_start {source target : F.State} (history : PositiveHistory F source target) :
    history.deploy.startNode = F.node source := rfl

```

## th.positive-formation-deployment — RelationalPerimeter.Constitution.PositiveHistory.deploy_final  RelationalPerimeter/Constitution/PositiveGeneration.lean:131  ```lean
theorem deploy_final {source target : F.State} (history : PositiveHistory F source target) :
    history.deploy.finalNode = F.node target := by
  induction history with
  | nil => rfl
  | cons step tail inductionHypothesis => exact inductionHypothesis

```

## th.positive-formation-deployment — RelationalPerimeter.Constitution.PositiveHistory.deploy_link_exact  RelationalPerimeter/Constitution/PositiveGeneration.lean:207  ```lean
theorem deploy_link_exact {source target : F.State} (history : PositiveHistory F source target)
    (occurrence : Occurrence history) :
    history.deploy.linkAt (history.toPosition occurrence) = history.linkAt occurrence := by
  induction occurrence with
  | here => rfl
  | later occurrence inductionHypothesis => exact inductionHypothesis

```

## th.positive-history-composition — RelationalPerimeter.Constitution.PositiveHistory.nil_append  RelationalPerimeter/Constitution/PositiveGeneration.lean:105  ```lean
theorem nil_append {source target : F.State} (history : PositiveHistory F source target) :
    (PositiveHistory.nil : PositiveHistory F source source).append history = history := rfl

```

## th.positive-history-composition — RelationalPerimeter.Constitution.PositiveHistory.append_nil  RelationalPerimeter/Constitution/PositiveGeneration.lean:108  ```lean
theorem append_nil {source target : F.State} (history : PositiveHistory F source target) :
    history.append .nil = history := by
  induction history with
  | nil => rfl
  | cons step tail inductionHypothesis =>
      exact congrArg (PositiveHistory.cons step) inductionHypothesis

```

## th.positive-history-composition — RelationalPerimeter.Constitution.PositiveHistory.append_associative  RelationalPerimeter/Constitution/PositiveGeneration.lean:115  ```lean
theorem append_associative {a b c d : F.State} (first : PositiveHistory F a b)
    (second : PositiveHistory F b c) (third : PositiveHistory F c d) :
    (first.append second).append third = first.append (second.append third) := by
  induction first with
  | nil => rfl
  | cons step tail inductionHypothesis =>
      exact congrArg (PositiveHistory.cons step) (inductionHypothesis second)

```

## th.positive-history-composition — RelationalPerimeter.Constitution.PositiveHistory.deploy_append  RelationalPerimeter/Constitution/PositiveGeneration.lean:137  ```lean
theorem deploy_append {a b c : F.State} (first : PositiveHistory F a b)
    (second : PositiveHistory F b c) :
    (first.append second).deploy =
      first.deploy.appendAlong first.deploy_final second.deploy := by
  induction first with
  | nil => rfl
  | cons step tail inductionHypothesis =>
      exact congrArg (PerimeterSpine.advance (F.compatibility step)) (inductionHypothesis second)

```

## th.positive-occurrence-positions — RelationalPerimeter.Constitution.PositiveHistory.nil_noOccurrence  RelationalPerimeter/Constitution/PositiveGeneration.lean:152  ```lean
theorem nil_noOccurrence (state : F.State) :
    Occurrence (.nil : PositiveHistory F state state) → False := fun occurrence => nomatch occurrence

```

## th.positive-occurrence-positions — RelationalPerimeter.Constitution.PositiveHistory.here_ne_later  RelationalPerimeter/Constitution/PositiveGeneration.lean:155  ```lean
theorem here_ne_later {a b c : F.State} {step : F.Step a b}
    {tail : PositiveHistory F b c} (occurrence : Occurrence tail) :
    (Occurrence.here : Occurrence (.cons step tail)) ≠ .later occurrence := by
  intro equality
  cases equality

```

## th.positive-occurrence-positions — RelationalPerimeter.Constitution.PositiveHistory.positionTransport  RelationalPerimeter/Constitution/PositiveGeneration.lean:194  ```lean
def positionTransport {source target : F.State} (history : PositiveHistory F source target) :
    ExactTypeTransport (Occurrence history) (NonClosingPosition history.deploy) :=
  { forward := history.toPosition
    backward := history.fromPosition
    forwardBackward := history.position_occurrence_return
    backwardForward := history.occurrence_position_return }

```

## th.positive-explicit-closing — RelationalPerimeter.Constitution.PositiveHistory.boundary_source_exact  RelationalPerimeter/Constitution/PositiveGeneration.lean:226  ```lean
theorem boundary_source_exact {source target : F.State}
    (history : PositiveHistory F source target) :
    history.boundaryShape.source = (F.node target).implicit :=
  congrArg LocalNode.implicit history.deploy_final

```

## th.positive-explicit-closing — RelationalPerimeter.Constitution.PositiveHistory.toCircular_initial  RelationalPerimeter/Constitution/PositiveGeneration.lean:244  ```lean
theorem toCircular_initial {source target : F.State} (history : PositiveHistory F source target)
    (positive : Occurrence history) (junction : ClosingWitness history.boundaryShape) :
    (history.toCircular positive junction).initialNode = F.node source := rfl

```

## th.positive-explicit-closing — RelationalPerimeter.Constitution.PositiveHistory.toCircular_deployment  RelationalPerimeter/Constitution/PositiveGeneration.lean:248  ```lean
theorem toCircular_deployment {source target : F.State} (history : PositiveHistory F source target)
    (positive : Occurrence history) (junction : ClosingWitness history.boundaryShape) :
    (history.toCircular positive junction).perimeter = history.deploy := rfl

```

## th.positive-explicit-closing — RelationalPerimeter.Constitution.PositiveHistory.toCircular_junction  RelationalPerimeter/Constitution/PositiveGeneration.lean:252  ```lean
theorem toCircular_junction {source target : F.State} (history : PositiveHistory F source target)
    (positive : Occurrence history) (junction : ClosingWitness history.boundaryShape) :
    (history.toCircular positive junction).finalJunction = junction := rfl

```

## th.positive-explicit-closing — RelationalPerimeter.Constitution.PositiveHistory.toCircular_boundary  RelationalPerimeter/Constitution/PositiveGeneration.lean:256  ```lean
theorem toCircular_boundary {source target : F.State} (history : PositiveHistory F source target)
    (positive : Occurrence history) (junction : ClosingWitness history.boundaryShape) :
    closingBoundary (history.toCircular positive junction) =
      (history.boundaryShape.point junction).toConstitutiveBoundary := rfl

```

## th.positive-generated-historical-bridge — RelationalPerimeter.Constitution.PositiveHistory.historical_positive  RelationalPerimeter/Constitution/PositiveGenerationBridge.lean:24  ```lean
theorem historical_positive (history : PositiveHistory F source target)
    (positive : Occurrence history) (junction : ClosingWitness history.boundaryShape)
    (endpoints : EndpointBoundary (history.toCircular positive junction))
    (obstruction : CircularClosureObstruction (history.toCircular positive junction) endpoints) :
    (history.toHistorical positive junction endpoints obstruction).toPositiveCircularPresentation =
      history.toCircular positive junction :=
  CircularPresentation.positive_roundTrip _ _ _

```

## th.positive-generated-historical-bridge — RelationalPerimeter.Constitution.PositiveHistory.historical_endpoints  RelationalPerimeter/Constitution/PositiveGenerationBridge.lean:32  ```lean
theorem historical_endpoints (history : PositiveHistory F source target)
    (positive : Occurrence history) (junction : ClosingWitness history.boundaryShape)
    (endpoints : EndpointBoundary (history.toCircular positive junction))
    (obstruction : CircularClosureObstruction (history.toCircular positive junction) endpoints) :
    (history.toHistorical positive junction endpoints obstruction).endpointBoundary = endpoints :=
  CircularPresentation.boundary_roundTrip _ _ _

```

## th.positive-generated-historical-bridge — RelationalPerimeter.Constitution.PositiveHistory.historical_obstruction  RelationalPerimeter/Constitution/PositiveGenerationBridge.lean:39  ```lean
theorem historical_obstruction (history : PositiveHistory F source target)
    (positive : Occurrence history) (junction : ClosingWitness history.boundaryShape)
    (endpoints : EndpointBoundary (history.toCircular positive junction))
    (obstruction : CircularClosureObstruction (history.toCircular positive junction) endpoints) :
    (history.toHistorical positive junction endpoints obstruction).closureObstruction = obstruction :=
  CircularPresentation.obstruction_roundTrip _ _ _

```

## th.positive-generated-historical-bridge — RelationalPerimeter.Constitution.PositiveHistory.historical_deployment  RelationalPerimeter/Constitution/PositiveGenerationBridge.lean:46  ```lean
theorem historical_deployment (history : PositiveHistory F source target)
    (positive : Occurrence history) (junction : ClosingWitness history.boundaryShape)
    (endpoints : EndpointBoundary (history.toCircular positive junction))
    (obstruction : CircularClosureObstruction (history.toCircular positive junction) endpoints) :
    (history.toHistorical positive junction endpoints obstruction).perimeter = history.deploy := rfl

```

## th.positive-successor-choice — RelationalPerimeter.Constitution.ChosenPositiveContinuation.walk  RelationalPerimeter/Constitution/PositiveGeneration.lean:270  ```lean
def walk {F : PositiveFormation} (choice : ChosenPositiveContinuation F)
    (source : F.State) : Nat → Σ target : F.State, PositiveHistory F source target
  | 0 => ⟨source, .nil⟩
  | count + 1 =>
      let tail := choice.walk (choice.successor source) count
      ⟨tail.1, .cons (choice.step source) tail.2⟩

```

## th.positive-successor-choice — RelationalPerimeter.Constitution.ChosenPositiveContinuation.walk_successor_positive  RelationalPerimeter/Constitution/PositiveGeneration.lean:277  ```lean
def walk_successor_positive {F : PositiveFormation} (choice : ChosenPositiveContinuation F)
    (source : F.State) (count : Nat) :
    PositiveHistory.Occurrence (choice.walk source (count + 1)).2 := .here

```

## th.positive-successor-choice — RelationalPerimeter.Constitution.PositiveGenerationExamples.branching_targets_distinct  RelationalPerimeter/Constitution/PositiveGenerationExamples.lean:129  ```lean
theorem branching_targets_distinct :
    leftHistory.deploy.finalNode.explicit ≠ rightHistory.deploy.finalNode.explicit :=
  fun equality => Bool.noConfusion equality

```

## th.positive-successor-choice — RelationalPerimeter.Constitution.PositiveGenerationExamples.chosen_successors_distinct  RelationalPerimeter/Constitution/PositiveGenerationExamples.lean:141  ```lean
theorem chosen_successors_distinct :
    leftContinuation.successor false ≠ rightContinuation.successor false :=
  fun equality => Bool.noConfusion equality

```

## th.positive-successor-choice — RelationalPerimeter.Constitution.PositiveGenerationExamples.directed_no_global_continuation  RelationalPerimeter/Constitution/PositiveGenerationExamples.lean:52  ```lean
theorem directed_no_global_continuation
    (choice : ChosenPositiveContinuation directedFormation) : False := by
  have step := choice.step true
  cases step

```

## th.separator-generated-unclosed — RelationalPerimeter.Constitution.PositiveGenerationExamples.directedPositive  RelationalPerimeter/Constitution/PositiveGenerationExamples.lean:43  ```lean
def directedPositive : PositiveHistory.Occurrence directedHistory := .here

```

## th.separator-generated-unclosed — RelationalPerimeter.Constitution.PositiveGenerationExamples.directed_closing_empty  RelationalPerimeter/Constitution/PositiveGenerationExamples.lean:45  ```lean
theorem directed_closing_empty : ClosingWitness directedHistory.boundaryShape → False :=
  fun junction => nomatch junction

```

## th.separator-generated-unclosed — RelationalPerimeter.Constitution.PositiveGenerationExamples.directed_no_pointing  RelationalPerimeter/Constitution/PositiveGenerationExamples.lean:48  ```lean
theorem directed_no_pointing :
    Nonempty (PointedClosingBoundary directedHistory.boundaryShape) → False :=
  directedHistory.boundaryShape.noPointingOfEmpty directed_closing_empty

```

## th.separator-repeated-positive-occurrences — RelationalPerimeter.Constitution.PositiveGenerationExamples.raw_nodes_repeat  RelationalPerimeter/Constitution/PositiveGenerationExamples.lean:159  ```lean
theorem raw_nodes_repeat :
    (repeatedHistory.linkAt firstOccurrence).source =
      (repeatedHistory.linkAt secondOccurrence).source := rfl

```

## th.separator-repeated-positive-occurrences — RelationalPerimeter.Constitution.PositiveGenerationExamples.repeated_occurrences_distinct  RelationalPerimeter/Constitution/PositiveGenerationExamples.lean:163  ```lean
theorem repeated_occurrences_distinct : firstOccurrence ≠ secondOccurrence :=
  PositiveHistory.here_ne_later .here

```

## th.separator-repeated-positive-occurrences — RelationalPerimeter.Constitution.PositiveGenerationExamples.repeated_positions_distinct  RelationalPerimeter/Constitution/PositiveGenerationExamples.lean:166  ```lean
theorem repeated_positions_distinct :
    repeatedHistory.toPosition firstOccurrence ≠ repeatedHistory.toPosition secondOccurrence := by
  intro equality
  have recovered := congrArg repeatedHistory.fromPosition equality
  exact repeated_occurrences_distinct recovered

```

## th.separator-repeated-positive-occurrences — RelationalPerimeter.Constitution.PositiveGenerationExamples.repeated_step_witnesses_distinct  RelationalPerimeter/Constitution/PositiveGenerationExamples.lean:172  ```lean
theorem repeated_step_witnesses_distinct :
    (repeatedHistory.linkAt firstOccurrence).compatibility ≠
      (repeatedHistory.linkAt secondOccurrence).compatibility :=
  fun equality => Bool.noConfusion equality

```

## th.signature-fibre-transport — RelationalPerimeter.Constitution.ConstitutiveSignatureTransport.compatibility_return  RelationalPerimeter/Constitution/SignatureTransport.lean:92  ```lean
theorem compatibility_return (map : ConstitutiveSignatureTransport S T)
    (i : S.Implicit) (e : S.Explicit) (w : S.Compatible i e) :
    (map.compatibility i e).backward ((map.compatibility i e).forward w) = w :=
  (map.compatibility i e).forwardBackward w

```

## th.signature-fibre-transport — RelationalPerimeter.Constitution.ConstitutiveSignatureTransport.compatibility_return_target  RelationalPerimeter/Constitution/SignatureTransport.lean:97  ```lean
theorem compatibility_return_target (map : ConstitutiveSignatureTransport S T)
    (i : S.Implicit) (e : S.Explicit)
    (w : T.Compatible (map.implicit.forward i) (map.explicit.forward e)) :
    (map.compatibility i e).forward ((map.compatibility i e).backward w) = w :=
  (map.compatibility i e).backwardForward w

```

## th.signature-fibre-transport — RelationalPerimeter.Constitution.ConstitutiveSignatureTransport.provenance_return  RelationalPerimeter/Constitution/SignatureTransport.lean:103  ```lean
theorem provenance_return (map : ConstitutiveSignatureTransport S T)
    (d : S.Difference) (w : S.Provenance d) :
    (map.provenance d).backward ((map.provenance d).forward w) = w :=
  (map.provenance d).forwardBackward w

```

## th.signature-fibre-transport — RelationalPerimeter.Constitution.ConstitutiveSignatureTransport.provenance_return_target  RelationalPerimeter/Constitution/SignatureTransport.lean:108  ```lean
theorem provenance_return_target (map : ConstitutiveSignatureTransport S T)
    (d : S.Difference) (w : T.Provenance (map.difference.forward d)) :
    (map.provenance d).forward ((map.provenance d).backward w) = w :=
  (map.provenance d).backwardForward w

```

## th.signature-calculus — RelationalPerimeter.Constitution.ConstitutiveSignatureTransport.identity_left_compatibility  RelationalPerimeter/Constitution/SignatureTransport.lean:145  ```lean
theorem identity_left_compatibility (map : ConstitutiveSignatureTransport S T)
    (i : S.Implicit) (e : S.Explicit) (w : S.Compatible i e) :
    (((identity S).compose map).compatibility i e).forward w =
      (map.compatibility i e).forward w := rfl

```

## th.signature-calculus — RelationalPerimeter.Constitution.ConstitutiveSignatureTransport.identity_right_compatibility  RelationalPerimeter/Constitution/SignatureTransport.lean:150  ```lean
theorem identity_right_compatibility (map : ConstitutiveSignatureTransport S T)
    (i : S.Implicit) (e : S.Explicit) (w : S.Compatible i e) :
    ((map.compose (identity T)).compatibility i e).forward w =
      (map.compatibility i e).forward w := rfl

```

## th.signature-calculus — RelationalPerimeter.Constitution.ConstitutiveSignatureTransport.identity_left_provenance  RelationalPerimeter/Constitution/SignatureTransport.lean:155  ```lean
theorem identity_left_provenance (map : ConstitutiveSignatureTransport S T)
    (d : S.Difference) (w : S.Provenance d) :
    (((identity S).compose map).provenance d).forward w = (map.provenance d).forward w := rfl

```

## th.signature-calculus — RelationalPerimeter.Constitution.ConstitutiveSignatureTransport.identity_right_provenance  RelationalPerimeter/Constitution/SignatureTransport.lean:159  ```lean
theorem identity_right_provenance (map : ConstitutiveSignatureTransport S T)
    (d : S.Difference) (w : S.Provenance d) :
    ((map.compose (identity T)).provenance d).forward w = (map.provenance d).forward w := rfl

```

## th.signature-calculus — RelationalPerimeter.Constitution.ConstitutiveSignatureTransport.compose_associative_compatibility  RelationalPerimeter/Constitution/SignatureTransport.lean:163  ```lean
theorem compose_associative_compatibility {V : ConstitutiveSignature}
    (first : ConstitutiveSignatureTransport S T) (second : ConstitutiveSignatureTransport T U)
    (third : ConstitutiveSignatureTransport U V) (i : S.Implicit) (e : S.Explicit)
    (w : S.Compatible i e) :
    (((first.compose second).compose third).compatibility i e).forward w =
      ((first.compose (second.compose third)).compatibility i e).forward w := rfl

```

## th.signature-calculus — RelationalPerimeter.Constitution.ConstitutiveSignatureTransport.compose_associative_provenance  RelationalPerimeter/Constitution/SignatureTransport.lean:170  ```lean
theorem compose_associative_provenance {V : ConstitutiveSignature}
    (first : ConstitutiveSignatureTransport S T) (second : ConstitutiveSignatureTransport T U)
    (third : ConstitutiveSignatureTransport U V) (d : S.Difference) (w : S.Provenance d) :
    (((first.compose second).compose third).provenance d).forward w =
      ((first.compose (second.compose third)).provenance d).forward w := rfl

```

## th.signature-calculus — RelationalPerimeter.Constitution.ConstitutiveSignatureTransport.reverse_compatibility_return  RelationalPerimeter/Constitution/SignatureTransport.lean:194  ```lean
theorem reverse_compatibility_return (map : ConstitutiveSignatureTransport S T)
    (i : S.Implicit) (e : S.Explicit) (w : S.Compatible i e) :
    (S.compatibilityReindex (map.implicit.forwardBackward i) (map.explicit.forwardBackward e)).forward
      ((map.reverse.compatibility (map.implicit.forward i) (map.explicit.forward e)).forward
        ((map.compatibility i e).forward w)) = w := by
  simp only [reverse, compatibilityAt, ExactTypeTransport.compose, ExactTypeTransport.reverse]
  exact (map.compatibility_backward_reindex (map.implicit.forwardBackward i)
    (map.explicit.forwardBackward e) ((map.compatibility i e).forward w)).trans
      ((map.compatibility i e).forwardBackward w)

```

## th.signature-calculus — RelationalPerimeter.Constitution.ConstitutiveSignatureTransport.reverse_provenance_return  RelationalPerimeter/Constitution/SignatureTransport.lean:204  ```lean
theorem reverse_provenance_return (map : ConstitutiveSignatureTransport S T)
    (d : S.Difference) (w : S.Provenance d) :
    (S.provenanceReindex (map.difference.forwardBackward d)).forward
      ((map.reverse.provenance (map.difference.forward d)).forward ((map.provenance d).forward w)) = w := by
  simp only [reverse, provenanceAt, ExactTypeTransport.compose, ExactTypeTransport.reverse]
  exact (map.provenance_backward_reindex (map.difference.forwardBackward d)
    ((map.provenance d).forward w)).trans ((map.provenance d).forwardBackward w)

```

## th.signature-calculus — RelationalPerimeter.Constitution.ConstitutiveSignatureTransport.reverse_compatibility_return_target  RelationalPerimeter/Constitution/SignatureTransport.lean:212  ```lean
theorem reverse_compatibility_return_target (map : ConstitutiveSignatureTransport S T)
    (i : T.Implicit) (e : T.Explicit) (w : T.Compatible i e) :
    (map.compatibilityAt (map.implicit.backwardForward i) (map.explicit.backwardForward e)).forward
      ((map.reverse.compatibility i e).forward w) = w :=
  (map.compatibilityAt (map.implicit.backwardForward i) (map.explicit.backwardForward e)).backwardForward w

```

## th.signature-calculus — RelationalPerimeter.Constitution.ConstitutiveSignatureTransport.reverse_provenance_return_target  RelationalPerimeter/Constitution/SignatureTransport.lean:218  ```lean
theorem reverse_provenance_return_target (map : ConstitutiveSignatureTransport S T)
    (d : T.Difference) (w : T.Provenance d) :
    (map.provenanceAt (map.difference.backwardForward d)).forward
      ((map.reverse.provenance d).forward w) = w :=
  (map.provenanceAt (map.difference.backwardForward d)).backwardForward w

```

## th.signature-boundary-restriction — RelationalPerimeter.Constitution.ConstitutiveSignatureTransport.restrict  RelationalPerimeter/Constitution/SignatureTransport.lean:251  ```lean
def restrict {B C : ConstitutiveBoundary}
    (map : ConstitutiveSignatureTransport B.signature C.signature)
    (sourceExact : map.implicit.forward B.source = C.source)
    (targetExact : map.explicit.forward B.target = C.target)
    (differenceExact : map.difference.forward B.difference = C.difference)
    (junctionExact : (map.compatibilityAt sourceExact targetExact).forward B.junction = C.junction)
    (provenanceExact : (map.provenanceAt differenceExact).forward B.provenance = C.provenance) :
    BoundaryTransport B C :=
  { toBoundaryCarrierTransport := map.restrictCarriers sourceExact targetExact differenceExact
    sourceExact := sourceExact
    targetExact := targetExact
    differenceExact := differenceExact
    junctionExact := junctionExact
    provenanceExact := provenanceExact }

```

## th.signature-boundary-restriction — RelationalPerimeter.Constitution.ConstitutiveSignatureTransport.restrict_junction_forward  RelationalPerimeter/Constitution/SignatureTransport.lean:266  ```lean
theorem restrict_junction_forward {B C : ConstitutiveBoundary}
    (map : ConstitutiveSignatureTransport B.signature C.signature)
    (hs : map.implicit.forward B.source = C.source)
    (ht : map.explicit.forward B.target = C.target)
    (hd : map.difference.forward B.difference = C.difference)
    (w : B.Compatible B.source B.target) :
    (map.restrictCarriers hs ht hd).junction.forward w = (map.compatibilityAt hs ht).forward w := rfl

```

## th.signature-boundary-restriction — RelationalPerimeter.Constitution.ConstitutiveSignatureTransport.restrict_provenance_backward  RelationalPerimeter/Constitution/SignatureTransport.lean:274  ```lean
theorem restrict_provenance_backward {B C : ConstitutiveBoundary}
    (map : ConstitutiveSignatureTransport B.signature C.signature)
    (hs : map.implicit.forward B.source = C.source)
    (ht : map.explicit.forward B.target = C.target)
    (hd : map.difference.forward B.difference = C.difference)
    (w : C.Provenance C.difference) :
    (map.restrictCarriers hs ht hd).provenance.backward w = (map.provenanceAt hd).backward w := rfl

```

## th.signature-boundary-restriction — RelationalPerimeter.Constitution.SignatureTransportExamples.selectedRestriction  RelationalPerimeter/Constitution/SignatureTransportExamples.lean:99  ```lean
def selectedRestriction : BoundaryTransport selectedBoundary movedBoundary :=
  flip.restrict (B := selectedBoundary) (C := movedBoundary) rfl rfl rfl rfl rfl

```

## th.signature-spine-transport — RelationalPerimeter.Constitution.ConstitutiveSignatureTransport.mapSpine_final  RelationalPerimeter/Constitution/SpineTransport.lean:24  ```lean
theorem mapSpine_final (map : ConstitutiveSignatureTransport S T) {node : S.Node}
    (spine : PerimeterSpine S.Compatible node) :
    (map.mapSpine spine).finalNode = map.mapNode spine.finalNode := by
  induction spine with
  | boundary => rfl
  | advance witness tail inductionHypothesis => exact inductionHypothesis

```

## th.signature-spine-transport — RelationalPerimeter.Constitution.ConstitutiveSignatureTransport.mapSpine_append  RelationalPerimeter/Constitution/SpineTransport.lean:31  ```lean
theorem mapSpine_append (map : ConstitutiveSignatureTransport S T) {node : S.Node}
    (first : PerimeterSpine S.Compatible node)
    (second : PerimeterSpine S.Compatible first.finalNode) :
    map.mapSpine (first.append second) =
      (map.mapSpine first).appendAlong (map.mapSpine_final first) (map.mapSpine second) := by
  induction first with
  | boundary => rfl
  | @advance node nextNode witness tail inductionHypothesis =>
      exact congrArg (PerimeterSpine.advance (node := map.mapNode node) (nextNode := map.mapNode nextNode)
        ((map.compatibility node.implicit nextNode.explicit).forward witness)) (inductionHypothesis second)

```

## th.signature-spine-transport — RelationalPerimeter.Constitution.ConstitutiveSignatureTransport.mapSpine_link  RelationalPerimeter/Constitution/SpineTransport.lean:156  ```lean
theorem mapSpine_link (map : ConstitutiveSignatureTransport S T) {node : S.Node}
    (spine : PerimeterSpine S.Compatible node) (position : NonClosingPosition spine) :
    (map.mapSpine spine).linkAt (map.mapPosition spine position) = map.mapLink (spine.linkAt position) := by
  induction position with
  | here => rfl
  | later position inductionHypothesis => exact inductionHypothesis

```

## th.signature-position-order — RelationalPerimeter.Constitution.ConstitutiveSignatureTransport.positionTransport  RelationalPerimeter/Constitution/SpineTransport.lean:75  ```lean
def positionTransport (map : ConstitutiveSignatureTransport S T) {node : S.Node}
    (spine : PerimeterSpine S.Compatible node) :
    ExactTypeTransport (NonClosingPosition spine) (NonClosingPosition (map.mapSpine spine)) :=
  { forward := map.mapPosition spine
    backward := map.restorePosition spine
    forwardBackward := map.position_return spine
    backwardForward := map.position_return_target spine }

```

## th.signature-position-order — RelationalPerimeter.Constitution.ConstitutiveSignatureTransport.precedes_iff  RelationalPerimeter/Constitution/SpineTransport.lean:128  ```lean
theorem precedes_iff (map : ConstitutiveSignatureTransport S T) {node : S.Node}
    (spine : PerimeterSpine S.Compatible node) (first second : NonClosingPosition spine) :
    NonClosingPrecedes (map.mapSpine spine) (map.mapPosition spine first) (map.mapPosition spine second) ↔
      NonClosingPrecedes spine first second := by
  constructor
  · intro relation
    have restored := map.restorePrecedes spine relation
    rw [map.position_return, map.position_return] at restored
    exact restored
  · exact map.mapPrecedes

```

## th.signature-position-order — RelationalPerimeter.Constitution.ConstitutiveSignatureTransport.next_iff  RelationalPerimeter/Constitution/SpineTransport.lean:139  ```lean
theorem next_iff (map : ConstitutiveSignatureTransport S T) {node : S.Node}
    (spine : PerimeterSpine S.Compatible node) (first second : NonClosingPosition spine) :
    NonClosingNext (map.mapSpine spine) (map.mapPosition spine first) (map.mapPosition spine second) ↔
      NonClosingNext spine first second := by
  constructor
  · intro relation
    have restored := map.restoreNext spine relation
    rw [map.position_return, map.position_return] at restored
    exact restored
  · exact map.mapNext

```

## th.signature-formation-histories — RelationalPerimeter.Constitution.PositiveFormation.transport  RelationalPerimeter/Constitution/FormationTransport.lean:28  ```lean
abbrev transport (F : PositiveFormation) {target : ConstitutiveSignature}
    (change : ConstitutiveSignatureTransport F.signature target) : PositiveFormation :=
  { Explicit := target.Explicit
    Implicit := target.Implicit
    Compatible := target.Compatible
    Difference := target.Difference
    Provenance := target.Provenance
    State := F.State
    node := fun state => change.mapNode (F.node state)
    Step := F.Step
    compatibility := fun {source target} step =>
      (change.compatibility (F.node source).implicit (F.node target).explicit).forward
        (F.compatibility step) }

```

## th.signature-formation-histories — RelationalPerimeter.Constitution.PositiveHistory.signatureTransport  RelationalPerimeter/Constitution/FormationTransport.lean:131  ```lean
def signatureTransport (change : ConstitutiveSignatureTransport F.signature target)
    (source terminal : F.State) :
    ExactTypeTransport (PositiveHistory F source terminal)
      (PositiveHistory (F.transport change) source terminal) :=
  { forward := transportSignature change
    backward := restoreSignature change
    forwardBackward := transport_restore change
    backwardForward := restore_transport change }

```

## th.signature-formation-histories — RelationalPerimeter.Constitution.PositiveHistory.occurrenceSignatureTransport  RelationalPerimeter/Constitution/FormationTransport.lean:208  ```lean
def occurrenceSignatureTransport
    (change : ConstitutiveSignatureTransport F.signature target)
    {source terminal : F.State} (history : PositiveHistory F source terminal) :
    ExactTypeTransport (Occurrence history) (Occurrence (history.transportSignature change)) :=
  { forward := history.transportOccurrence change
    backward := history.restoreOccurrence change
    forwardBackward := history.transport_restore_occurrence change
    backwardForward := history.restore_transport_occurrence change }

```

## th.signature-formation-operations — RelationalPerimeter.Constitution.PositiveHistory.transport_append  RelationalPerimeter/Constitution/FormationTransport.lean:140  ```lean
theorem transport_append (change : ConstitutiveSignatureTransport F.signature target)
    {source middle terminal : F.State} (first : PositiveHistory F source middle)
    (second : PositiveHistory F middle terminal) :
    (first.append second).transportSignature change =
      (first.transportSignature change).append (second.transportSignature change) := by
  induction first with
  | nil => rfl
  | cons step tail inductionHypothesis =>
      exact congrArg (PositiveHistory.cons (F := F.transport change) step)
        (inductionHypothesis second)

```

## th.signature-formation-operations — RelationalPerimeter.Constitution.PositiveHistory.transport_deploy  RelationalPerimeter/Constitution/FormationTransport.lean:151  ```lean
theorem transport_deploy (change : ConstitutiveSignatureTransport F.signature target)
    {source terminal : F.State} (history : PositiveHistory F source terminal) :
    (history.transportSignature change).deploy = change.mapSpine history.deploy := by
  induction history with
  | nil => rfl
  | @cons source middle terminal step tail inductionHypothesis =>
      exact congrArg (PerimeterSpine.advance
        (node := (F.transport change).node source)
        (nextNode := (F.transport change).node middle)
        ((change.compatibility (F.node source).implicit (F.node middle).explicit).forward
          (F.compatibility step))) inductionHypothesis

```

## th.signature-formation-operations — RelationalPerimeter.Constitution.PositiveHistory.transport_position  RelationalPerimeter/Constitution/FormationTransport.lean:217  ```lean
theorem transport_position
    (change : ConstitutiveSignatureTransport F.signature target)
    {source terminal : F.State} (history : PositiveHistory F source terminal)
    (occurrence : Occurrence history) :
    history.transport_deploy change ▸
        (history.transportSignature change).toPosition (history.transportOccurrence change occurrence) =
      change.mapPosition history.deploy (history.toPosition occurrence) := by
  induction occurrence with
  | @here source middle terminal step tail =>
      exact PositionReindex.cast_here (S := target) (tail.transport_deploy change)
  | @later source middle terminal step tail occurrence inductionHypothesis =>
      change (congrArg (PerimeterSpine.advance
        (node := (F.transport change).node source)
        (nextNode := (F.transport change).node middle)
        ((change.compatibility (F.node source).implicit (F.node middle).explicit).forward
          (F.compatibility step))) (tail.transport_deploy change)) ▸
          (NonClosingPosition.later ((tail.transportSignature change).toPosition
            (tail.transportOccurrence change occurrence))) =
        NonClosingPosition.later (change.mapPosition tail.deploy (tail.toPosition occurrence))
      exact (PositionReindex.cast_later (S := target) (tail.transport_deploy change)
        ((tail.transportSignature change).toPosition
          (tail.transportOccurrence change occurrence))).trans
        (congrArg NonClosingPosition.later inductionHypothesis)

```

## th.signature-formation-operations — RelationalPerimeter.Constitution.ChosenPositiveContinuation.transport_walk  RelationalPerimeter/Constitution/FormationTransport.lean:309  ```lean
theorem transport_walk {F : PositiveFormation} {target : ConstitutiveSignature}
    (change : ConstitutiveSignatureTransport F.signature target)
    (choice : ChosenPositiveContinuation F) (source : F.State) (count : Nat) :
    (choice.transportSignature change).walk source count =
      let original := choice.walk source count
      ⟨original.1, original.2.transportSignature change⟩ := by
  induction count generalizing source with
  | zero => rfl
  | succ count inductionHypothesis =>
      simp only [walk]
      rw [inductionHypothesis]
      rfl

```

## th.signature-closing-transport — RelationalPerimeter.Constitution.PositiveHistory.closingSignatureTransport  RelationalPerimeter/Constitution/ClosingTransport.lean:18  ```lean
def closingSignatureTransport (map : ConstitutiveSignatureTransport F.signature T)
    {source terminal : F.State} (history : PositiveHistory F source terminal) :
    ExactTypeTransport (ClosingWitness history.boundaryShape)
      (ClosingWitness (history.transportSignature map).boundaryShape) :=
  map.compatibilityAt (history.transport_closing_source map) rfl

```

## th.signature-closing-transport — RelationalPerimeter.Constitution.PositiveHistory.circularBoundaryTransport  RelationalPerimeter/Constitution/ClosingTransport.lean:45  ```lean
def circularBoundaryTransport (map : ConstitutiveSignatureTransport F.signature T)
    {source terminal : F.State} (history : PositiveHistory F source terminal)
    (positive : Occurrence history) (junction : ClosingWitness history.boundaryShape) :
    BoundaryTransport (closingBoundary (history.toCircular positive junction))
      (closingBoundary (history.transportedCircular map positive junction)) :=
  map.restrict
    (B := closingBoundary (history.toCircular positive junction))
    (C := closingBoundary (history.transportedCircular map positive junction))
    (history.transport_closing_source map) rfl rfl rfl rfl

```

## th.signature-closing-transport — RelationalPerimeter.Constitution.PositiveHistory.circular_junction_preserved  RelationalPerimeter/Constitution/ClosingTransport.lean:55  ```lean
theorem circular_junction_preserved (map : ConstitutiveSignatureTransport F.signature T)
    {source terminal : F.State} (history : PositiveHistory F source terminal)
    (positive : Occurrence history) (junction : ClosingWitness history.boundaryShape) :
    (history.circularBoundaryTransport map positive junction).junction.forward junction =
      (history.transportedCircular map positive junction).finalJunction :=
  (history.circularBoundaryTransport map positive junction).junctionExact

```

## th.signature-closing-transport — RelationalPerimeter.Constitution.PositiveHistory.circular_provenance_preserved  RelationalPerimeter/Constitution/ClosingTransport.lean:62  ```lean
theorem circular_provenance_preserved (map : ConstitutiveSignatureTransport F.signature T)
    {source terminal : F.State} (history : PositiveHistory F source terminal)
    (positive : Occurrence history) (junction : ClosingWitness history.boundaryShape) :
    (history.circularBoundaryTransport map positive junction).provenance.forward (F.node source).provenance =
      (history.transportedCircular map positive junction).initialNode.provenance :=
  (history.circularBoundaryTransport map positive junction).provenanceExact

```

## th.separator-sort-fibres — RelationalPerimeter.Constitution.SignatureTransportExamples.same_explicit_sorts  RelationalPerimeter/Constitution/SignatureTransportExamples.lean:27  ```lean
theorem same_explicit_sorts : inhabitedSignature.Explicit = emptySignature.Explicit := rfl

```

## th.separator-sort-fibres — RelationalPerimeter.Constitution.SignatureTransportExamples.no_family_transport_nonempty  RelationalPerimeter/Constitution/SignatureTransportExamples.lean:37  ```lean
theorem no_family_transport_nonempty :
    Nonempty (ConstitutiveSignatureTransport inhabitedSignature emptySignature) → False :=
  fun ⟨transport⟩ => no_family_transport transport

```

## th.equipped-circular-classification — RelationalPerimeter.Constitution.EquippedInteriorRole.positionTransport  RelationalPerimeter/Constitution/CircularRoles.lean:42  ```lean
def positionTransport (P : PositiveCircularPresentation) :
    ExactTypeTransport (NonClosingPosition P.perimeter) (EquippedInteriorRole P) :=
  { forward := canonical P
    backward := fun role => role.position
    forwardBackward := fun _ => rfl
    backwardForward := canonical_return }

```

## th.equipped-circular-classification — RelationalPerimeter.Constitution.EquippedInteriorRole.occurrence_link_readout  RelationalPerimeter/Constitution/CircularRoles.lean:66  ```lean
theorem occurrence_link_readout {F : PositiveFormation} {source terminal : F.State}
    (history : PositiveHistory F source terminal) (positive : PositiveHistory.Occurrence history)
    (junction : ClosingWitness history.boundaryShape) (occurrence : PositiveHistory.Occurrence history) :
    (ofOccurrence history positive junction occurrence).link = history.linkAt occurrence :=
  history.deploy_link_exact occurrence

```

## th.equipped-circular-classification — RelationalPerimeter.Constitution.CircularRole.classificationTransport  RelationalPerimeter/Constitution/CircularRoles.lean:108  ```lean
def classificationTransport (P : PositiveCircularPresentation) :
    ExactTypeTransport (CircularRole P) (NonClosingPosition P.perimeter ⊕ Unit) :=
  { forward := classify
    backward := assemble P
    forwardBackward := assemble_classify
    backwardForward := classify_assemble }

```

## th.equipped-circular-classification — RelationalPerimeter.Constitution.CircularRole.exhaustive  RelationalPerimeter/Constitution/CircularRoles.lean:115  ```lean
theorem exhaustive (role : CircularRole P) :
    (∃ position, role = .interior (EquippedInteriorRole.canonical P position)) ∨
      role = .final (EquippedFinalRole.canonical (closingBoundary P)) := by
  cases role with
  | interior role => exact .inl ⟨role.position, congrArg CircularRole.interior role.canonical_return.symm⟩
  | final role => exact .inr (congrArg CircularRole.final (EquippedFinalRole.unique _ _))

```

## th.equipped-circular-classification — RelationalPerimeter.Constitution.CircularRole.branches_distinct  RelationalPerimeter/Constitution/CircularRoles.lean:122  ```lean
theorem branches_distinct (interior : EquippedInteriorRole P)
    (final : EquippedFinalRole (closingBoundary P)) :
    (CircularRole.interior interior : CircularRole P) ≠ .final final := by
  intro equality
  cases equality

```

## th.final-role-no-occurrence — RelationalPerimeter.Constitution.CircularRole.generatedPosition  RelationalPerimeter/Constitution/CircularRoles.lean:128  ```lean
def generatedPosition : CircularRole P → Option (NonClosingPosition P.perimeter)
  | .interior role => .some role.position
  | .final _ => .none

```

## th.final-role-no-occurrence — RelationalPerimeter.Constitution.CircularRole.final_not_interior_position  RelationalPerimeter/Constitution/CircularRoles.lean:138  ```lean
theorem final_not_interior_position (role : EquippedFinalRole (closingBoundary P))
    (position : NonClosingPosition P.perimeter) :
    generatedPosition (.final role) ≠ .some position := by
  intro equality
  cases equality

```

## th.final-role-no-occurrence — RelationalPerimeter.Constitution.HistoricalRoleBridge.final_not_realized  RelationalPerimeter/Constitution/HistoricalRoleBridge.lean:59  ```lean
theorem final_not_realized {P : CircularPresentation} {history : RootedGeneratedHistory P}
    (realization : ExactNonClosingRealization P history)
    (role : EquippedFinalRole (closingBoundary P.toPositiveCircularPresentation)) :
    realizeRole realization (.final role) = .none := rfl

```

## th.equipped-historical-role-bridge — RelationalPerimeter.Constitution.HistoricalRoleBridge.finalRequirementTransport  RelationalPerimeter/Constitution/HistoricalRoleBridge.lean:8  ```lean
def finalRequirementTransport (P : CircularPresentation) :
    ExactTypeTransport (FinalRequirement P)
      (EquippedFinalRole (closingBoundary P.toPositiveCircularPresentation)) :=
  { forward := fun _ => EquippedFinalRole.canonical _
    backward := fun _ => .distinguished
    forwardBackward := fun marker => by cases marker; rfl
    backwardForward := fun role => EquippedFinalRole.unique _ role }

```

## th.equipped-historical-role-bridge — RelationalPerimeter.Constitution.HistoricalRoleBridge.marker_junction_readout  RelationalPerimeter/Constitution/HistoricalRoleBridge.lean:16  ```lean
theorem marker_junction_readout (P : CircularPresentation) (marker : FinalRequirement P) :
    ((finalRequirementTransport P).forward marker).witness = P.finalJunction := rfl

```

## th.equipped-historical-role-bridge — RelationalPerimeter.Constitution.HistoricalRoleBridge.requirementTransport  RelationalPerimeter/Constitution/HistoricalRoleBridge.lean:19  ```lean
def requirementTransport (P : CircularPresentation) :
    ExactTypeTransport (CircularRequirement P) (CircularRole P.toPositiveCircularPresentation) :=
  { forward := fun requirement => match requirement with
      | .inl position => .interior (EquippedInteriorRole.canonical _ position)
      | .inr marker => .final ((finalRequirementTransport P).forward marker)
    backward := fun role => match role with
      | .interior role => .inl role.position
      | .final role => .inr ((finalRequirementTransport P).backward role)
    forwardBackward := fun requirement => by
      cases requirement with
      | inl => rfl
      | inr marker => exact congrArg Sum.inr ((finalRequirementTransport P).forwardBackward marker)
    backwardForward := fun role => by
      cases role with
      | interior role => exact congrArg CircularRole.interior role.canonical_return
      | final role => exact congrArg CircularRole.final ((finalRequirementTransport P).backwardForward role) }

```

## th.equipped-historical-role-bridge — RelationalPerimeter.Constitution.HistoricalRoleBridge.realization_readout  RelationalPerimeter/Constitution/HistoricalRoleBridge.lean:41  ```lean
def realization_readout {P : CircularPresentation} {history : RootedGeneratedHistory P}
    (realization : ExactNonClosingRealization P history)
    (role : EquippedInteriorRole P.toPositiveCircularPresentation) :
    RequirementOccurrenceAgreement P history role.position (realizeInterior realization role) :=
  realization.agreement role.position

```

## th.equipped-historical-role-bridge — RelationalPerimeter.Constitution.HistoricalRoleBridge.realization_injective  RelationalPerimeter/Constitution/HistoricalRoleBridge.lean:47  ```lean
theorem realization_injective {P : CircularPresentation} {history : RootedGeneratedHistory P}
    (realization : ExactNonClosingRealization P history)
    {first second : EquippedInteriorRole P.toPositiveCircularPresentation}
    (sameOccurrence : realizeInterior realization first = realizeInterior realization second) :
    first = second := EquippedInteriorRole.ext (realization.realize_injective sameOccurrence)

```

## th.equipped-interior-role-transport — RelationalPerimeter.Constitution.PositiveHistory.interiorRoleTransport  RelationalPerimeter/Constitution/CircularRoleTransport.lean:64  ```lean
def interiorRoleTransport (map : ConstitutiveSignatureTransport F.signature T)
    {source terminal : F.State} (history : PositiveHistory F source terminal)
    (positive : Occurrence history) (junction : ClosingWitness history.boundaryShape) :
    ExactTypeTransport (EquippedInteriorRole (history.toCircular positive junction))
      (EquippedInteriorRole (history.transportedCircular map positive junction)) :=
  ((EquippedInteriorRole.positionTransport (history.toCircular positive junction)).reverse.compose
    (history.circularPositionTransport map)).compose
    (EquippedInteriorRole.positionTransport (history.transportedCircular map positive junction))

```

## th.equipped-interior-role-transport — RelationalPerimeter.Constitution.PositiveHistory.interior_position_preserved  RelationalPerimeter/Constitution/CircularRoleTransport.lean:73  ```lean
theorem interior_position_preserved (map : ConstitutiveSignatureTransport F.signature T)
    {source terminal : F.State} (history : PositiveHistory F source terminal)
    (positive : Occurrence history) (junction : ClosingWitness history.boundaryShape)
    (role : EquippedInteriorRole (history.toCircular positive junction)) :
    history.transport_deploy map ▸
        ((history.interiorRoleTransport map positive junction).forward role).position =
      map.mapPosition history.deploy role.position :=
  history.circular_position_preserved map role.position

```

## th.equipped-interior-role-transport — RelationalPerimeter.Constitution.PositiveHistory.interior_link_preserved  RelationalPerimeter/Constitution/CircularRoleTransport.lean:82  ```lean
theorem interior_link_preserved (map : ConstitutiveSignatureTransport F.signature T)
    {source terminal : F.State} (history : PositiveHistory F source terminal)
    (positive : Occurrence history) (junction : ClosingWitness history.boundaryShape)
    (role : EquippedInteriorRole (history.toCircular positive junction)) :
    ((history.interiorRoleTransport map positive junction).forward role).link =
      map.mapLink role.link := by
  let transported := (history.interiorRoleTransport map positive junction).forward role
  have castLink : (history.transportSignature map).deploy.linkAt transported.position =
      (map.mapSpine history.deploy).linkAt
        (history.transport_deploy map ▸ transported.position) :=
    (PositionReindex.link_cast (S := T) (history.transport_deploy map) transported.position).symm
  have positionLink : (map.mapSpine history.deploy).linkAt
        (history.transport_deploy map ▸ transported.position) =
      (map.mapSpine history.deploy).linkAt (map.mapPosition history.deploy role.position) :=
    congrArg ((map.mapSpine history.deploy).linkAt)
      (history.interior_position_preserved map positive junction role)
  exact transported.linkExact.trans (castLink.trans (positionLink.trans
    ((map.mapSpine_link history.deploy role.position).trans
      (congrArg map.mapLink role.linkExact.symm))))

```

## th.equipped-final-role-full-transport — RelationalPerimeter.Constitution.PositiveHistory.finalRoleTransport  RelationalPerimeter/Constitution/CircularRoleTransport.lean:134  ```lean
def finalRoleTransport (map : ConstitutiveSignatureTransport F.signature T)
    {source terminal : F.State} (history : PositiveHistory F source terminal)
    (positive : Occurrence history) (junction : ClosingWitness history.boundaryShape) :
    ExactTypeTransport (EquippedFinalRole (closingBoundary (history.toCircular positive junction)))
      (EquippedFinalRole (closingBoundary (history.transportedCircular map positive junction))) :=
  EquippedFinalRole.exactTransport (history.circularBoundaryTransport map positive junction)

```

## th.equipped-final-role-full-transport — RelationalPerimeter.Constitution.PositiveHistory.final_witness_preserved  RelationalPerimeter/Constitution/CircularRoleTransport.lean:141  ```lean
theorem final_witness_preserved (map : ConstitutiveSignatureTransport F.signature T)
    {source terminal : F.State} (history : PositiveHistory F source terminal)
    (positive : Occurrence history) (junction : ClosingWitness history.boundaryShape)
    (role : EquippedFinalRole (closingBoundary (history.toCircular positive junction))) :
    ((history.finalRoleTransport map positive junction).forward role).witness =
      (history.circularBoundaryTransport map positive junction).junction.forward role.witness := rfl

```

## th.equipped-final-role-full-transport — RelationalPerimeter.Constitution.PositiveHistory.final_source_preserved  RelationalPerimeter/Constitution/CircularRoleTransport.lean:148  ```lean
theorem final_source_preserved (map : ConstitutiveSignatureTransport F.signature T)
    {source terminal : F.State} (history : PositiveHistory F source terminal)
    (positive : Occurrence history) (junction : ClosingWitness history.boundaryShape)
    (role : EquippedFinalRole (closingBoundary (history.toCircular positive junction))) :
    map.implicit.forward role.source =
      ((history.finalRoleTransport map positive junction).forward role).source :=
  EquippedFinalRole.source_preserved (history.circularBoundaryTransport map positive junction) role

```

## th.equipped-final-role-full-transport — RelationalPerimeter.Constitution.PositiveHistory.final_target_preserved  RelationalPerimeter/Constitution/CircularRoleTransport.lean:156  ```lean
theorem final_target_preserved (map : ConstitutiveSignatureTransport F.signature T)
    {source terminal : F.State} (history : PositiveHistory F source terminal)
    (positive : Occurrence history) (junction : ClosingWitness history.boundaryShape)
    (role : EquippedFinalRole (closingBoundary (history.toCircular positive junction))) :
    map.explicit.forward role.target =
      ((history.finalRoleTransport map positive junction).forward role).target :=
  EquippedFinalRole.target_preserved (history.circularBoundaryTransport map positive junction) role

```

## th.equipped-final-role-full-transport — RelationalPerimeter.Constitution.PositiveHistory.final_difference_preserved  RelationalPerimeter/Constitution/CircularRoleTransport.lean:164  ```lean
theorem final_difference_preserved (map : ConstitutiveSignatureTransport F.signature T)
    {source terminal : F.State} (history : PositiveHistory F source terminal)
    (positive : Occurrence history) (junction : ClosingWitness history.boundaryShape) :
    map.difference.forward (closingBoundary (history.toCircular positive junction)).difference =
      (closingBoundary (history.transportedCircular map positive junction)).difference :=
  (history.circularBoundaryTransport map positive junction).differenceExact

```

## th.equipped-final-role-full-transport — RelationalPerimeter.Constitution.PositiveHistory.final_provenance_preserved  RelationalPerimeter/Constitution/CircularRoleTransport.lean:171  ```lean
theorem final_provenance_preserved (map : ConstitutiveSignatureTransport F.signature T)
    {source terminal : F.State} (history : PositiveHistory F source terminal)
    (positive : Occurrence history) (junction : ClosingWitness history.boundaryShape)
    (role : EquippedFinalRole (closingBoundary (history.toCircular positive junction))) :
    (history.circularBoundaryTransport map positive junction).provenance.forward role.provenance =
      ((history.finalRoleTransport map positive junction).forward role).provenance :=
  EquippedFinalRole.provenance_preserved (history.circularBoundaryTransport map positive junction) role

```

## th.equipped-role-classification-commutes — RelationalPerimeter.Constitution.PositiveHistory.circularRoleTransport  RelationalPerimeter/Constitution/CircularRoleTransport.lean:179  ```lean
def circularRoleTransport (map : ConstitutiveSignatureTransport F.signature T)
    {source terminal : F.State} (history : PositiveHistory F source terminal)
    (positive : Occurrence history) (junction : ClosingWitness history.boundaryShape) :
    ExactTypeTransport (CircularRole (history.toCircular positive junction))
      (CircularRole (history.transportedCircular map positive junction)) :=
  { forward := fun role => match role with
      | .interior role => .interior ((history.interiorRoleTransport map positive junction).forward role)
      | .final role => .final ((history.finalRoleTransport map positive junction).forward role)
    backward := fun role => match role with
      | .interior role => .interior ((history.interiorRoleTransport map positive junction).backward role)
      | .final role => .final ((history.finalRoleTransport map positive junction).backward role)
    forwardBackward := by
      intro role
      cases role with
      | interior role =>
          exact congrArg CircularRole.interior
            ((history.interiorRoleTransport map positive junction).forwardBackward role)
      | final role =>
          exact congrArg CircularRole.final
            ((history.finalRoleTransport map positive junction).forwardBackward role)
    backwardForward := by
      intro role
      cases role with
      | interior role =>
          exact congrArg CircularRole.interior
            ((history.interiorRoleTransport map positive junction).backwardForward role)
      | final role =>
          exact congrArg CircularRole.final
            ((history.finalRoleTransport map positive junction).backwardForward role) }

```

## th.equipped-role-classification-commutes — RelationalPerimeter.Constitution.PositiveHistory.circular_interior_preserved  RelationalPerimeter/Constitution/CircularRoleTransport.lean:209  ```lean
theorem circular_interior_preserved (map : ConstitutiveSignatureTransport F.signature T)
    {source terminal : F.State} (history : PositiveHistory F source terminal)
    (positive : Occurrence history) (junction : ClosingWitness history.boundaryShape)
    (role : EquippedInteriorRole (history.toCircular positive junction)) :
    (history.circularRoleTransport map positive junction).forward (.interior role) =
      .interior ((history.interiorRoleTransport map positive junction).forward role) := rfl

```

## th.equipped-role-classification-commutes — RelationalPerimeter.Constitution.PositiveHistory.circular_final_preserved  RelationalPerimeter/Constitution/CircularRoleTransport.lean:216  ```lean
theorem circular_final_preserved (map : ConstitutiveSignatureTransport F.signature T)
    {source terminal : F.State} (history : PositiveHistory F source terminal)
    (positive : Occurrence history) (junction : ClosingWitness history.boundaryShape)
    (role : EquippedFinalRole (closingBoundary (history.toCircular positive junction))) :
    (history.circularRoleTransport map positive junction).forward (.final role) =
      .final ((history.finalRoleTransport map positive junction).forward role) := rfl

```

## th.equipped-role-classification-commutes — RelationalPerimeter.Constitution.PositiveHistory.circular_classification_commutes  RelationalPerimeter/Constitution/CircularRoleTransport.lean:239  ```lean
theorem circular_classification_commutes (map : ConstitutiveSignatureTransport F.signature T)
    {source terminal : F.State} (history : PositiveHistory F source terminal)
    (positive : Occurrence history) (junction : ClosingWitness history.boundaryShape)
    (role : CircularRole (history.toCircular positive junction)) :
    CircularRole.classify ((history.circularRoleTransport map positive junction).forward role) =
      Sum.map (history.circularPositionTransport map).forward id
        (CircularRole.classify role) := by
  cases role <;> rfl

```

## th.equipped-role-classification-commutes — RelationalPerimeter.Constitution.PositiveHistory.circular_generated_position_commutes  RelationalPerimeter/Constitution/CircularRoleTransport.lean:248  ```lean
theorem circular_generated_position_commutes (map : ConstitutiveSignatureTransport F.signature T)
    {source terminal : F.State} (history : PositiveHistory F source terminal)
    (positive : Occurrence history) (junction : ClosingWitness history.boundaryShape)
    (role : CircularRole (history.toCircular positive junction)) :
    CircularRole.generatedPosition ((history.circularRoleTransport map positive junction).forward role) =
      Option.map (history.circularPositionTransport map).forward
        (CircularRole.generatedPosition role) := by
  cases role <;> rfl

```

## th.separator-relative-role-grammar — RelationalPerimeter.Constitution.CircularRolesExamples.unpointed_empty_no_final  RelationalPerimeter/Constitution/CircularRolesExamples.lean:32  ```lean
theorem unpointed_empty_no_final :
    (∃ pointing : PointedClosingBoundary ClosingBoundaryExamples.emptyShape,
      Nonempty pointing.FinalRole) → False := ClosingBoundaryExamples.empty_no_final_role

```

## th.separator-relative-role-grammar — RelationalPerimeter.Constitution.CircularRolesExamples.chosen_witnesses_distinct  RelationalPerimeter/Constitution/CircularRolesExamples.lean:22  ```lean
theorem chosen_witnesses_distinct : falseFinal.witness ≠ trueFinal.witness := by
  intro equality
  cases equality

```

## th.separator-relative-role-grammar — RelationalPerimeter.Constitution.CircularRolesExamples.no_exhaustiveness_of_larger_type  RelationalPerimeter/Constitution/CircularRolesExamples.lean:64  ```lean
theorem no_exhaustiveness_of_larger_type :
    (∀ extended : ExtendedRole falsePresentation, ∃ role : CircularRole falsePresentation,
      extended = .inl role) → False := by
  intro exhaustive
  obtain ⟨role, equality⟩ := exhaustive exterior
  exact exterior_outside_declared_grammar role equality.symm

```
