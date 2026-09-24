import RelationalPerimeter.Foundations.PerimeterRealization

/- The proposition-valued definitions below are intentionally transparent,
   and the independent input families intentionally keep distinct universes. -/
set_option linter.defProp false
set_option linter.checkUnivs false

namespace StrongPerimetralTurning

universe uE uI uK uD uP uN uEnd uLoop uA uB uV

/-! ## Faithful refinements and the final junction -/

def transportOccurrence
    {State : Type uA}
    {Step : State → State → Type uB}
    {source target : State}
    {first second : History Step source target}
    (equality : first = second) :
    History.Occurrence first → History.Occurrence second := by
  cases equality
  exact id

theorem transportOccurrence_injective
    {State : Type uA}
    {Step : State → State → Type uB}
    {source target : State}
    {first second : History Step source target}
    (equality : first = second) :
    Function.Injective (transportOccurrence equality) := by
  cases equality
  intro left right same
  exact same

theorem locatedStep_transportOccurrence
    {State : Type uA}
    {Step : State → State → Type uB}
    {source target : State}
    {first second : History Step source target}
    (equality : first = second)
    (occurrence : History.Occurrence first) :
    (transportOccurrence equality occurrence).locatedStep =
      occurrence.locatedStep := by
  cases equality
  rfl

namespace History

/- An occurrence whose located step is exactly a generated step from the
   source of the history determines an initial one-step factorization.  The
   proof recurses on occurrence data.  A nonempty prefix before that occurrence
   would be a positive generated history returning to the same source. -/
def factorInitialGeneratedStep
    {P : CircularPresentation}
    {source middle target : PositiveConstitution P}
    (history : GeneratedHistory source target)
    (step : GeneratedStep source middle)
    (occurrence : History.Occurrence history)
    (locatedStepExact :
      occurrence.locatedStep =
        (⟨source, middle, step⟩ : History.LocatedStep (@GeneratedStep P))) :
    Σ continuation : GeneratedHistory middle target,
      { recompose : History.append (.extend .root step) continuation = history //
        transportOccurrence recompose
          (History.embedLeftOccurrence
            (.last : History.Occurrence (.extend .root step))
            continuation) = occurrence } :=
  match occurrence with
  | @Occurrence.last _ _ _ _ _ prior lastStep => by
      cases locatedStepExact
      cases prior with
      | root =>
          exact ⟨.root, ⟨rfl, rfl⟩⟩
      | extend priorHistory previousStep =>
          let positive : History.Positive (@GeneratedStep P) source source :=
            ⟨_, priorHistory, previousStep⟩
          exact False.elim
            (positiveGeneratedHistory_source_ne_target positive rfl)
  | @Occurrence.earlier _ _ _ _ _ prior lastStep earlier => by
      rcases factorInitialGeneratedStep prior step earlier locatedStepExact with
        ⟨continuation, ⟨recompose, occurrenceExact⟩⟩
      cases recompose
      exact ⟨.extend continuation lastStep, ⟨rfl,
        congrArg
          (fun occurrence =>
            History.Occurrence.earlier (step := lastStep) occurrence)
          occurrenceExact⟩⟩

/- Once the initial step has been factored, any distinct occurrence belongs to
   the right-hand continuation.  Classification is performed on occurrence
   data, while the inequality is used only to eliminate the impossible old
   branch. -/
def extractRightOccurrenceAfterSingle
    {State : Type uA}
    {Step : State → State → Type uB}
    {source middle target : State}
    (firstStep : Step source middle)
    (continuation : History Step middle target)
    {history : History Step source target}
    (recompose :
      History.append (.extend .root firstStep) continuation = history)
    (occurrence : History.Occurrence history)
    (notFirst :
      transportOccurrence recompose
        (History.embedLeftOccurrence
          (.last : History.Occurrence (.extend .root firstStep)) continuation) ≠
        occurrence) :
    Σ newOccurrence : History.Occurrence continuation,
      PLift (transportOccurrence recompose
        (History.embedRightOccurrence
          (.extend .root firstStep) newOccurrence) = occurrence) := by
  cases recompose
  cases History.classifyAppendOccurrence
      (.extend .root firstStep) continuation occurrence with
  | inl oldData =>
      rcases oldData with ⟨oldOccurrence, reconstruction⟩
      cases oldOccurrence with
      | last => exact False.elim (notFirst reconstruction.down)
      | earlier impossible => exact nomatch impossible
  | inr newData =>
      rcases newData with ⟨newOccurrence, reconstruction⟩
      exact ⟨newOccurrence, ⟨reconstruction.down⟩⟩

end History

/- Recursive structural factorization of a canonical perimeter deployment from
   exact, injective occurrences inside a genuine generated history.  No
   numerical rank or length is used. -/
def factorDeployRemainingFromExactOccurrences
    (P : CircularPresentation)
    {node : LocalNode
      P.Explicit P.Implicit P.Compatible P.Difference P.Provenance} :
    (remaining : PerimeterSpine P.Compatible node) →
    (data : FreeConstitution P (.within remaining)) →
    (difference : BoundaryDifference P data) →
    (target : PositiveConstitution P) →
    (history : GeneratedHistory
      (positiveAtRemaining P remaining data difference) target) →
    (realize : NonClosingPosition remaining → History.Occurrence history) →
    Function.Injective realize →
    ((position : NonClosingPosition remaining) →
      (realize position).locatedStep =
        positionLocatedStep P data difference position) →
    Σ continuation : GeneratedHistory
        (deployRemaining P remaining data difference).1 target,
      PLift (History.append
        (deployRemaining P remaining data difference).2 continuation = history
      )
  | .boundary node, data, difference, target, history,
      _realize, _realizeInjective, _locatedStepExact =>
      ⟨history, ⟨History.root_append history⟩⟩
  | .advance compatible tail, data, difference, target, history,
      realize, realizeInjective, locatedStepExact => by
      let source :=
        positiveAtRemaining P (.advance compatible tail) data difference
      let next := canonicalTarget source
      have firstLocatedStepExact :
          (realize (.here : NonClosingPosition (.advance compatible tail))).locatedStep =
            (⟨source, next, generatedStepOfFreeK source⟩ :
              History.LocatedStep (@GeneratedStep P)) := by
        have exactAtFirst := locatedStepExact
          (.here : NonClosingPosition (.advance compatible tail))
        dsimp [positionLocatedStep, positionSourceState,
          positionSourceStateAux, positionTargetState, source, next] at exactAtFirst
        exact exactAtFirst
      rcases History.factorInitialGeneratedStep history
          (generatedStepOfFreeK source) (realize .here) firstLocatedStepExact with
        ⟨afterFirst, ⟨firstRecompose, firstOccurrenceExact⟩⟩
      have laterNotFirst (position : NonClosingPosition tail) :
          transportOccurrence firstRecompose
            (History.embedLeftOccurrence
              (.last : History.Occurrence
                (.extend .root (generatedStepOfFreeK source))) afterFirst) ≠
              realize (.later position) := by
        intro equality
        have realizedEquality : realize .here = realize (.later position) :=
          firstOccurrenceExact.symm.trans equality
        have positionEquality := realizeInjective realizedEquality
        cases positionEquality
      let tailOccurrenceData := fun position : NonClosingPosition tail =>
        History.extractRightOccurrenceAfterSingle
          (generatedStepOfFreeK source) afterFirst firstRecompose
          (realize (.later position)) (laterNotFirst position)
      let tailRealize :
          NonClosingPosition tail → History.Occurrence afterFirst :=
        fun position => (tailOccurrenceData position).1
      have tailRealizeInjective : Function.Injective tailRealize := by
        intro first second equality
        have embeddedEquality :
            transportOccurrence firstRecompose
              (History.embedRightOccurrence
                (.extend .root (generatedStepOfFreeK source))
                (tailRealize first)) =
            transportOccurrence firstRecompose
              (History.embedRightOccurrence
                (.extend .root (generatedStepOfFreeK source))
                (tailRealize second)) :=
          congrArg
            (fun occurrence =>
              transportOccurrence firstRecompose
                (History.embedRightOccurrence
                  (.extend .root (generatedStepOfFreeK source)) occurrence))
            equality
        have realizedEquality :
            realize (.later first) = realize (.later second) :=
            (tailOccurrenceData first).2.down.symm.trans
            (embeddedEquality.trans (tailOccurrenceData second).2.down)
        exact NonClosingPosition.later.inj
          (realizeInjective realizedEquality)
      have tailLocatedStepExact
          (position : NonClosingPosition tail) :
          (tailRealize position).locatedStep =
            positionLocatedStep P next.2.1 next.2.2 position := by
        have reconstructed := (tailOccurrenceData position).2.down
        calc
          (tailRealize position).locatedStep
              = (History.embedRightOccurrence
                  (.extend .root (generatedStepOfFreeK source))
                  (tailRealize position)).locatedStep :=
                (History.locatedStep_embedRight
                  (.extend .root (generatedStepOfFreeK source))
                  (tailRealize position)).symm
          _ = (transportOccurrence firstRecompose
                (History.embedRightOccurrence
                  (.extend .root (generatedStepOfFreeK source))
                  (tailRealize position))).locatedStep :=
                (locatedStep_transportOccurrence firstRecompose
                  (History.embedRightOccurrence
                    (.extend .root (generatedStepOfFreeK source))
                    (tailRealize position))).symm
          _ = (realize (.later position)).locatedStep :=
                congrArg
                  (fun occurrence : History.Occurrence history =>
                    occurrence.locatedStep) reconstructed
          _ = positionLocatedStep P data difference (.later position) :=
                locatedStepExact (.later position)
          _ = positionLocatedStep P next.2.1 next.2.2 position := by
                rfl
      rcases factorDeployRemainingFromExactOccurrences P tail
          next.2.1 next.2.2 target afterFirst tailRealize
          tailRealizeInjective tailLocatedStepExact with
        ⟨continuation, tailRecompose⟩
      refine ⟨continuation, ⟨?_⟩⟩
      change History.append
          (History.append
            (.extend .root (generatedStepOfFreeK source))
            (deployRemaining P tail next.2.1 next.2.2).2)
          continuation = history
      calc
        History.append
            (History.append
              (.extend .root (generatedStepOfFreeK source))
              (deployRemaining P tail next.2.1 next.2.2).2)
            continuation
            = History.append
                (.extend .root (generatedStepOfFreeK source))
                (History.append
                  (deployRemaining P tail next.2.1 next.2.2).2
                  continuation) :=
              History.append_associative _ _ _
        _ = History.append
              (.extend .root (generatedStepOfFreeK source)) afterFirst :=
            congrArg
              (History.append
                (.extend .root (generatedStepOfFreeK source)))
              tailRecompose.down
        _ = history := firstRecompose

structure PerimeterExtension
    (P : CircularPresentation)
    (history : RootedGeneratedHistory P) where
  continuation :
    GeneratedHistory (perimeterEndpoint P) history.endpoint
  recompose :
    History.append (perimeterHistory P) continuation = history.history

namespace ExactNonClosingRealization

/- Exact local realization inside a genuine rooted generated history is already
   enough to reconstruct the canonical perimeter as an initial extension. -/
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

end ExactNonClosingRealization

namespace PerimeterExtension

def oldOccurrence
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (extension : PerimeterExtension P history)
    (position : NonClosingPosition P.perimeter) :
    History.Occurrence history.history :=
  transportOccurrence extension.recompose
    (History.embedLeftOccurrence
      (requirementToOccurrence P position) extension.continuation)

def newOccurrence
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (extension : PerimeterExtension P history)
    (occurrence : History.Occurrence extension.continuation) :
    History.Occurrence history.history :=
  transportOccurrence extension.recompose
    (History.embedRightOccurrence (perimeterHistory P) occurrence)

def oldOccurrenceAgreement
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (extension : PerimeterExtension P history)
    (position : NonClosingPosition P.perimeter) :
    RequirementOccurrenceAgreement P history position
      (extension.oldOccurrence position) := by
  refine ⟨?_⟩
  exact congrArg
    (fun located : History.LocatedStep (@GeneratedStep P) => located.source.1)
    ((locatedStep_transportOccurrence extension.recompose
        (History.embedLeftOccurrence
          (requirementToOccurrence P position) extension.continuation)).trans
      ((History.locatedStep_embedLeft
        (requirementToOccurrence P position) extension.continuation).trans
          (canonicalRequirementAgreement P position).locatedStepExact))

theorem oldOccurrence_injective
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (extension : PerimeterExtension P history) :
    Function.Injective extension.oldOccurrence := by
  intro first second equality
  have embeddedEquality :=
    transportOccurrence_injective extension.recompose equality
  have canonicalEquality :=
    History.embedLeftOccurrence_injective extension.continuation embeddedEquality
  exact requirementToOccurrence_injective P canonicalEquality

def toExactNonClosingRealization
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (extension : PerimeterExtension P history) :
    ExactNonClosingRealization P history :=
  { realize := extension.oldOccurrence
    agreement := extension.oldOccurrenceAgreement }

theorem old_new_occurrences_disjoint
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (extension : PerimeterExtension P history)
    (position : NonClosingPosition P.perimeter)
    (occurrence : History.Occurrence extension.continuation) :
    extension.oldOccurrence position ≠ extension.newOccurrence occurrence := by
  intro equality
  have beforeTransport :=
    transportOccurrence_injective extension.recompose equality
  exact History.leftRightDisjoint
    (requirementToOccurrence P position) occurrence beforeTransport

end PerimeterExtension

def identityPerimeterExtension (P : CircularPresentation) :
    PerimeterExtension P (perimeterDeployment P) :=
  { continuation := .root
    recompose := rfl }

def oneStepAfterPerimeter_is_extension (P : CircularPresentation) :
    PerimeterExtension P (oneStepAfterPerimeter P) :=
  { continuation := .extend .root (generate_after_perimeter P).2
    recompose := rfl }

/-! ## Direct circular residual-determination core

This is the core consumed by the canonical one-step construction.  Its label
is defined directly on the exactly-one continuation occurrence; no rich
perimeter realization or residual-labelling adapter is involved. -/
def oneStepResidualDeterminationCore
    (P : CircularPresentation) :
    SegmentedResidualRole.ResidualDeterminationCore
      (NonClosingPosition P.perimeter)
      (FinalRequirement P)
      (History.Occurrence
        (oneStepAfterPerimeter_is_extension P).continuation)
      (finalRequirementContractible P) := by
  let exactlyOne :
      History.ExactlyOne
        (oneStepAfterPerimeter_is_extension P).continuation := by
    change History.ExactlyOne
      (.extend .root (generate_after_perimeter P).2)
    exact .single (generate_after_perimeter P).2
  refine
    { newLabel := fun _ => .inr .distinguished
      newLabelInjective := ?_
      noInternalReuse := ?_ }
  · intro first second _
    exact (exactlyOne.occurrence_unique first).trans
      (exactlyOne.occurrence_unique second).symm
  · intro occurrence role equality
    cases equality

def oneStepCorePositive
    (P : CircularPresentation) :
    SegmentedResidualRole.PositiveNewPart
      (History.Occurrence
        (oneStepAfterPerimeter_is_extension P).continuation) :=
  { occurrence := .last }

def oneStepCoreResidualOccurrence
    (P : CircularPresentation) :
    SegmentedResidualRole.CoreUniqueResidualOccurrence
      (oneStepResidualDeterminationCore P) :=
  SegmentedResidualRole.positiveCore_hasUniqueResidualOccurrence
    (oneStepResidualDeterminationCore P)
    (oneStepCorePositive P)

def oneStepCoreSegmentedBoundary
    (P : CircularPresentation) :
    AbstractSegmentedTurning.CoreSegmentedBoundary
      (perimetralBoundaryGenerator P)
      (NonClosingPosition P.perimeter)
      (FinalRequirement P)
      (History.Occurrence
        (oneStepAfterPerimeter_is_extension P).continuation)
      (finalRequirementContractible P) :=
  { core := oneStepResidualDeterminationCore P
    positive := oneStepCorePositive P }

def oneStepAfterPerimeter_nonClosingRealization
    (P : CircularPresentation) :
    ExactNonClosingRealization P (oneStepAfterPerimeter P) :=
  (oneStepAfterPerimeter_is_extension P).toExactNonClosingRealization

/-! ## Independent circular specification -/

/- `CircularClosureMeaning` states the trajectory-level closure obligation
   independently of `CircularRefinement`: every strict constitutive extension
   of the canonical perimeter deployment must determine a total loop. -/
abbrev CircularClosureMeaning
    (P : CircularPresentation)
    (history : RootedGeneratedHistory P) : Type _ :=
  StrictConstitutivePrefix (perimeterDeployment P) history → P.TotalLoop

/- The canonical deployment satisfies the closure meaning because there is no
   strict constitutive prefix from it to itself. -/
def perimeterDeployment_closureMeaning
    (P : CircularPresentation) :
    CircularClosureMeaning P (perimeterDeployment P) :=
  fun strict =>
    False.elim (strictPrefix_ne strict rfl)

/- The freely generated one-step continuation fails the independent closure
   meaning directly: its canonical strict continuation would force a total
   loop, which the presentation rejects. -/
theorem oneStepAfterPerimeter_notClosureMeaning
    (P : CircularPresentation) :
    CircularClosureMeaning P (oneStepAfterPerimeter P) → False :=
  fun meaning =>
    P.rejectTotalLoop (meaning (oneStepAfterPerimeterStrict P))

/- Satisfaction of the independent circular specification has exactly two
   primitive components: minimal local exactness and trajectory closure. -/
structure CircularSpecificationSatisfaction
    (P : CircularPresentation)
    (history : RootedGeneratedHistory P) where
  «local» : ExactNonClosingRealization P history
  trajectory : CircularClosureMeaning P history

/- Positive canonical model of the independent specification. -/
def perimeterDeployment_specificationSatisfaction
    (P : CircularPresentation) :
    CircularSpecificationSatisfaction P (perimeterDeployment P) :=
  { «local» := (identityPerimeterExtension P).toExactNonClosingRealization
    trajectory := perimeterDeployment_closureMeaning P }

/- Negative canonical model: local exactness remains available, but the
   trajectory component of the same independent specification is impossible. -/
theorem oneStepAfterPerimeter_notSpecificationSatisfaction
    (P : CircularPresentation) :
    CircularSpecificationSatisfaction P (oneStepAfterPerimeter P) → False :=
  fun satisfaction =>
    oneStepAfterPerimeter_notClosureMeaning P satisfaction.trajectory

/- Carrier completeness of the independent specification: any satisfying rooted
   generated history is necessarily the canonical perimeter deployment.  The
   local component reconstructs a perimeter extension.  A positive suffix is
   excluded directly by the independent trajectory meaning and the total-loop
   obstruction. -/
theorem CircularSpecificationSatisfaction.eq_perimeter
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (satisfaction : CircularSpecificationSatisfaction P history) :
    history = perimeterDeployment P := by
  let extension : PerimeterExtension P history :=
    satisfaction.«local».toPerimeterExtension
  cases History.appendRootOrPositive
      (perimeterHistory P) extension.continuation with
  | inl rootData =>
      rcases rootData with ⟨endpointEquality, continuationEquality⟩
      exact rootedGeneratedHistory_ext endpointEquality.down
        ((heq_of_eq extension.recompose.symm).trans
          continuationEquality.down)
  | inr positiveData =>
      rcases positiveData with ⟨positive, continuationEquality⟩
      let strict :
          StrictConstitutivePrefix (perimeterDeployment P) history :=
        { continuation := positive
          historyExact := by
            exact
              (congrArg
                (History.append (perimeterHistory P))
                continuationEquality.down.symm).trans extension.recompose }
      exact False.elim
        (P.rejectTotalLoop (satisfaction.trajectory strict))

/-! ## Experimental semantic traces -/

/- `SemanticTrace` deliberately forgets global composability while retaining
   the complete located data of every generated step.  Occurrences are list
   positions, so equal located steps may still occur at distinct indices. -/
structure SemanticTrace
    (P : CircularPresentation) where
  steps : List (History.LocatedStep (@GeneratedStep P))

namespace SemanticTrace

abbrev Occurrence
    {P : CircularPresentation}
    (trace : SemanticTrace P) : Type :=
  Fin trace.steps.length

def locatedStep
    {P : CircularPresentation}
    (trace : SemanticTrace P)
    (occurrence : trace.Occurrence) :
    History.LocatedStep (@GeneratedStep P) :=
  trace.steps.get occurrence

end SemanticTrace

/- Experimental counterpart of `RequirementOccurrenceAgreement`.  It keeps
   only the exact local semantic content and does not assume a generated
   history, a circular labelling, or any regime structure. -/
structure LocatedRequirementAgreement
    (P : CircularPresentation)
    (position : NonClosingPosition P.perimeter)
    (located : History.LocatedStep (@GeneratedStep P)) where
  locatedStepExact :
    located =
      positionLocatedStep P FreeConstitution.root
        BoundaryDifference.initial position

/- Experimental exact local coverage.  Injectivity preserves occurrence
   individuation, while no global composability or ordering constraint is
   imposed beyond the explicit list positions of the semantic trace. -/
structure SemanticExactNonClosingRealization
    (P : CircularPresentation)
    (trace : SemanticTrace P) where
  realize :
    NonClosingPosition P.perimeter → trace.Occurrence
  realize_injective :
    Function.Injective realize
  agreement :
    (position : NonClosingPosition P.perimeter) →
      LocatedRequirementAgreement P position
        (trace.locatedStep (realize position))

/- Order preservation adds exactly one constraint to the experimental local
   realization: structural precedence in the perimeter must be reflected by
   the order of occurrence indices in the semantic trace. -/
def SemanticOrderPreserved
    {P : CircularPresentation}
    {trace : SemanticTrace P}
    (realization : SemanticExactNonClosingRealization P trace) :
    Prop :=
  ∀ first second,
    NonClosingPrecedes P.perimeter first second →
      realization.realize first < realization.realize second


namespace SemanticTrace

/- Occurrences strictly between two trace positions.  The subtype preserves
   occurrence individuation independently of the located-step reading. -/
abbrev Between
    {P : CircularPresentation}
    (trace : SemanticTrace P)
    (left right : trace.Occurrence) : Type :=
  { occurrence : trace.Occurrence //
      left < occurrence ∧ occurrence < right }

end SemanticTrace

/- Exact participation of the positionally intermediate occurrences in one
   generated constitutive bridge.  Exactness is occurrence-level first, with
   located-step agreement supplied afterwards. -/
structure ExactSemanticBridgeSegment
    {P : CircularPresentation}
    (trace : SemanticTrace P)
    (left right : trace.Occurrence)
    {source target : PositiveConstitution P}
    (bridge : GeneratedHistory source target) where
  forwardOccurrence :
    trace.Between left right → History.Occurrence bridge
  backwardOccurrence :
    History.Occurrence bridge → trace.Between left right
  forwardBackward :
    (occurrence : trace.Between left right) →
      backwardOccurrence (forwardOccurrence occurrence) = occurrence
  backwardForward :
    (occurrence : History.Occurrence bridge) →
      forwardOccurrence (backwardOccurrence occurrence) = occurrence
  locatedStepAgreement :
    (occurrence : trace.Between left right) →
      trace.locatedStep occurrence.1 =
        (forwardOccurrence occurrence).locatedStep

/- A constitutively effective bridge is not merely a generated history with
   matching endpoints.  Its generated occurrences must correspond exactly to
   all occurrences strictly between the two selected semantic-trace indices. -/
structure EffectiveConstitutiveBridge
    {P : CircularPresentation}
    (trace : SemanticTrace P)
    (left right : trace.Occurrence) where
  leftBeforeRight : left < right
  bridge :
    GeneratedHistory
      (trace.locatedStep left).target
      (trace.locatedStep right).source
  exactSegment :
    ExactSemanticBridgeSegment trace left right bridge

/- Between canonically adjacent requirements, an exact constitutive bridge has
   no intermediate occurrences.  Positional interleaving alone therefore does
   not establish constitutive participation. -/
theorem bridgeParticipation_between_empty_of_next
    {P : CircularPresentation}
    {trace : SemanticTrace P}
    (realization : SemanticExactNonClosingRealization P trace)
    {first second : NonClosingPosition P.perimeter}
    (next : NonClosingNext P.perimeter first second)
    (bridge : GeneratedHistory
      (trace.locatedStep (realization.realize first)).target
      (trace.locatedStep (realization.realize second)).source)
    (participates :
      trace.Between (realization.realize first) (realization.realize second) →
        History.Occurrence bridge) :
    trace.Between (realization.realize first) (realization.realize second) →
      False := by
  let firstCanonical :=
    positionLocatedStep P FreeConstitution.root
      BoundaryDifference.initial first
  let secondCanonical :=
    positionLocatedStep P FreeConstitution.root
      BoundaryDifference.initial second
  have firstExact := (realization.agreement first).locatedStepExact
  have secondExact := (realization.agreement second).locatedStepExact
  have canonicalEndpointEquality :
      firstCanonical.target = secondCanonical.source :=
    NonClosingNext.target_eq_source next
      FreeConstitution.root BoundaryDifference.initial
  have endpointEquality :
      (trace.locatedStep (realization.realize first)).target =
        (trace.locatedStep (realization.realize second)).source :=
    (congrArg
      (fun located : History.LocatedStep (@GeneratedStep P) => located.target)
      firstExact).trans
      (canonicalEndpointEquality.trans
        (congrArg
          (fun located : History.LocatedStep (@GeneratedStep P) => located.source)
          secondExact).symm)
  intro between
  exact generatedHistory_equalEndpoints_noOccurrence
    bridge endpointEquality (participates between)


/- The strong exact bridge statement is a direct corollary of the minimal
   participation theorem. -/
theorem effectiveBridge_between_empty_of_next
    {P : CircularPresentation}
    {trace : SemanticTrace P}
    (realization : SemanticExactNonClosingRealization P trace)
    {first second : NonClosingPosition P.perimeter}
    (next : NonClosingNext P.perimeter first second)
    (effective : EffectiveConstitutiveBridge trace
      (realization.realize first) (realization.realize second)) :
    trace.Between (realization.realize first) (realization.realize second) →
      False :=
  bridgeParticipation_between_empty_of_next realization next
    effective.bridge effective.exactSegment.forwardOccurrence


structure FaithfulPerimeterLabelling
    (P : CircularPresentation)
    (history : RootedGeneratedHistory P)
    (extension : PerimeterExtension P history) where
  label : History.Occurrence history.history → CircularRequirement P
  preservesNonClosingLabels :
    (position : NonClosingPosition P.perimeter) →
      label (extension.oldOccurrence position) = .inl position
  requirementFaithful :
    (first second : History.Occurrence history.history) →
      label first = label second → first = second

/- This weak positive layer contains only the constitutive extension and its
   faithful circular labelling.  It deliberately precedes every semantic
   realization and every totalization. -/
structure FaithfullyLabelledPerimeterExtension
    (P : CircularPresentation)
    (history : RootedGeneratedHistory P) where
  extension : PerimeterExtension P history
  labelling : FaithfulPerimeterLabelling P history extension

namespace FaithfullyLabelledPerimeterExtension

def continuation
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (labelled : FaithfullyLabelledPerimeterExtension P history) :
    GeneratedHistory (perimeterEndpoint P) history.endpoint :=
  labelled.extension.continuation

def label
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (labelled : FaithfullyLabelledPerimeterExtension P history) :
    History.Occurrence history.history → CircularRequirement P :=
  labelled.labelling.label

def oldOccurrence
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (labelled : FaithfullyLabelledPerimeterExtension P history)
    (position : NonClosingPosition P.perimeter) :
    History.Occurrence history.history :=
  labelled.extension.oldOccurrence position

def newOccurrence
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (labelled : FaithfullyLabelledPerimeterExtension P history)
    (occurrence : History.Occurrence labelled.continuation) :
    History.Occurrence history.history :=
  labelled.extension.newOccurrence occurrence

def preservesNonClosingLabels
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (labelled : FaithfullyLabelledPerimeterExtension P history)
    (position : NonClosingPosition P.perimeter) :
    labelled.label (labelled.oldOccurrence position) = .inl position :=
  labelled.labelling.preservesNonClosingLabels position

def requirementFaithful
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (labelled : FaithfullyLabelledPerimeterExtension P history)
    (first second : History.Occurrence history.history) :
    labelled.label first = labelled.label second → first = second :=
  labelled.labelling.requirementFaithful first second

theorem old_new_occurrences_disjoint
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (labelled : FaithfullyLabelledPerimeterExtension P history)
    (position : NonClosingPosition P.perimeter)
    (occurrence : History.Occurrence labelled.continuation) :
    labelled.oldOccurrence position ≠ labelled.newOccurrence occurrence :=
  labelled.extension.old_new_occurrences_disjoint position occurrence

/- Every faithfully labelled perimeter extension instantiates the abstract
   segmented residual-role interface. -/
def toSegmentedResidualExtension
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (labelled : FaithfullyLabelledPerimeterExtension P history) :
    SegmentedResidualRole.FaithfulExtension
      (NonClosingPosition P.perimeter)
      (FinalRequirement P)
      (History.Occurrence (perimeterHistory P))
      (History.Occurrence labelled.continuation)
      (History.Occurrence history.history)
      (perimeterInternalRoleRealization P)
      (finalRequirementContractible P) :=
  { embedOld := fun occurrence =>
      transportOccurrence labelled.extension.recompose
        (History.embedLeftOccurrence occurrence labelled.continuation)
    embedNew := labelled.newOccurrence
    oldNewDisjoint := by
      intro oldOccurrence newOccurrence equality
      have beforeTransport :=
        transportOccurrence_injective
          labelled.extension.recompose equality
      exact History.leftRightDisjoint
        oldOccurrence newOccurrence beforeTransport
    embedNewInjective := by
      intro first second equality
      have beforeTransport :=
        transportOccurrence_injective
          labelled.extension.recompose equality
      exact History.embedRightOccurrence_injective
        (perimeterHistory P) beforeTransport
    label := labelled.label
    preservesInternal := labelled.preservesNonClosingLabels
    labelFaithful := labelled.requirementFaithful }

theorem segmentedResidualExtension_embedOld_injective
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (labelled : FaithfullyLabelledPerimeterExtension P history) :
    Function.Injective labelled.toSegmentedResidualExtension.embedOld := by
  intro first second equality
  have embeddedEquality :=
    transportOccurrence_injective labelled.extension.recompose equality
  exact History.embedLeftOccurrence_injective
    labelled.continuation embeddedEquality

theorem newOccurrence_cannotReuseNonClosingRequirement
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (labelled : FaithfullyLabelledPerimeterExtension P history)
    (occurrence : History.Occurrence labelled.continuation)
    (position : NonClosingPosition P.perimeter)
    (labelEquality :
      labelled.label (labelled.newOccurrence occurrence) = .inl position) :
    False :=
  labelled.toSegmentedResidualExtension
    |>.newOccurrence_cannotReuseInternalRole
      occurrence position labelEquality

theorem newOccurrence_label_is_final
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (labelled : FaithfullyLabelledPerimeterExtension P history)
    (occurrence : History.Occurrence labelled.continuation) :
    labelled.label (labelled.newOccurrence occurrence) =
      .inr .distinguished :=
  labelled.toSegmentedResidualExtension
    |>.newOccurrence_label_is_residual occurrence

theorem continuation_occurrences_unique
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (labelled : FaithfullyLabelledPerimeterExtension P history)
    (first second : History.Occurrence labelled.continuation) :
    first = second :=
  labelled.toSegmentedResidualExtension
    |>.newOccurrences_unique first second

end FaithfullyLabelledPerimeterExtension

structure PositiveContinuation
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (extension : PerimeterExtension P history) where
  path : History.Positive
    (@GeneratedStep P) (perimeterEndpoint P) history.endpoint
  historyExact : extension.continuation = path.toHistory

namespace PositiveContinuation

def toResidualPositive
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    {labelled : FaithfullyLabelledPerimeterExtension P history}
    (positive : PositiveContinuation labelled.extension) :
    SegmentedResidualRole.PositiveNewPart
      (History.Occurrence labelled.continuation) :=
  { occurrence :=
      transportOccurrence positive.historyExact.symm
        positive.path.lastOccurrence }

end PositiveContinuation

namespace FaithfullyLabelledPerimeterExtension

def reconstructedInternalCompletion
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (labelled : FaithfullyLabelledPerimeterExtension P history)
    (positive : PositiveContinuation labelled.extension) :
    SegmentedResidualRole.ExactInternalCompletion
      labelled.toSegmentedResidualExtension.toResidualUniquenessKernel :=
  labelled.toSegmentedResidualExtension.reconstructInternalCompletion
    positive.toResidualPositive

theorem reconstructed_roleToOccurrence_agrees
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (labelled : FaithfullyLabelledPerimeterExtension P history)
    (positive : PositiveContinuation labelled.extension)
    (position : NonClosingPosition P.perimeter) :
    (labelled.reconstructedInternalCompletion positive
      |>.toExactInternalRealization).roleToOccurrence position =
        requirementToOccurrence P position :=
  labelled.toSegmentedResidualExtension
    |>.reconstructed_roleToOccurrence_agrees
      positive.toResidualPositive position

theorem reconstructed_occurrenceToRole_agrees
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (labelled : FaithfullyLabelledPerimeterExtension P history)
    (positive : PositiveContinuation labelled.extension)
    (occurrence : History.Occurrence (perimeterHistory P)) :
    (labelled.reconstructedInternalCompletion positive).occurrenceToRole
        occurrence = occurrenceToRequirement P occurrence :=
  labelled.toSegmentedResidualExtension
    |>.reconstructed_occurrenceToRole_agrees
      positive.toResidualPositive occurrence

end FaithfullyLabelledPerimeterExtension

def oneStepAfterPerimeter_positiveContinuation
    (P : CircularPresentation) :
    PositiveContinuation (oneStepAfterPerimeter_is_extension P) :=
  { path :=
      { predecessor := perimeterEndpoint P
        priorHistory := .root
        lastStep := (generate_after_perimeter P).2 }
    historyExact := rfl }

def History.exactlyOneOfPositiveAndUnique
    {State : Type uA}
    {Step : State → State → Type uB}
    {source target : State}
    (positive : History.Positive Step source target)
    (unique :
      (first second : History.Occurrence positive.toHistory) →
        first = second) :
    History.ExactlyOne positive.toHistory := by
  cases positive with
  | mk predecessor priorHistory lastStep =>
      cases priorHistory with
      | root => exact .single lastStep
      | extend previous penultimateStep =>
          have impossible := unique
            (.last : History.Occurrence
              (.extend (.extend previous penultimateStep) lastStep))
            (.earlier (.last : History.Occurrence
              (.extend previous penultimateStep)))
          cases impossible

def positiveContinuation_exactlyOne
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (labelled : FaithfullyLabelledPerimeterExtension P history)
    (positive : PositiveContinuation labelled.extension) :
    History.ExactlyOne labelled.continuation :=
  let pathExactlyOne : History.ExactlyOne positive.path.toHistory :=
    History.exactlyOneOfPositiveAndUnique positive.path fun first second =>
      transportOccurrence_injective positive.historyExact.symm
        (labelled.continuation_occurrences_unique
          (transportOccurrence positive.historyExact.symm first)
          (transportOccurrence positive.historyExact.symm second))
  cast
    (congrArg
      (fun continuation => History.ExactlyOne continuation)
      positive.historyExact.symm)
    pathExactlyOne

theorem rootContinuation_not_positive
    (P : CircularPresentation) :
    PositiveContinuation (identityPerimeterExtension P) → False := by
  intro positive
  have equality := positive.historyExact
  cases positive.path with
  | mk predecessor priorHistory lastStep =>
      cases equality

structure FinalBoundaryOccurrence
    (P : CircularPresentation)
    (history : RootedGeneratedHistory P) where
  labelled : FaithfullyLabelledPerimeterExtension P history
  positive : PositiveContinuation labelled.extension
  continuationOccurrence : History.Occurrence labelled.continuation
  occurrenceIsCanonical :
    continuationOccurrence =
      transportOccurrence positive.historyExact.symm
        positive.path.lastOccurrence
  labelIsFinal :
    labelled.label (labelled.newOccurrence continuationOccurrence) =
      .inr .distinguished

def finalBoundaryOccurrence
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (labelled : FaithfullyLabelledPerimeterExtension P history)
    (positive : PositiveContinuation labelled.extension) :
    FinalBoundaryOccurrence P history :=
  let occurrence :=
    transportOccurrence positive.historyExact.symm
      positive.path.lastOccurrence
  { labelled := labelled
    positive := positive
    continuationOccurrence := occurrence
    occurrenceIsCanonical := rfl
    labelIsFinal := labelled.newOccurrence_label_is_final occurrence }

namespace FinalBoundaryOccurrence

def historyOccurrence
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (boundary : FinalBoundaryOccurrence P history) :
    History.Occurrence history.history :=
  boundary.labelled.newOccurrence boundary.continuationOccurrence

def locatedStep
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (boundary : FinalBoundaryOccurrence P history) :
    History.LocatedStep (@GeneratedStep P) :=
  boundary.continuationOccurrence.locatedStep

def source
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (boundary : FinalBoundaryOccurrence P history) :
    PositiveConstitution P :=
  boundary.locatedStep.source

def target
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (boundary : FinalBoundaryOccurrence P history) :
    PositiveConstitution P :=
  boundary.locatedStep.target

def step
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (boundary : FinalBoundaryOccurrence P history) :
    GeneratedStep boundary.source boundary.target :=
  boundary.locatedStep.step

def step_is_generatedStep
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (boundary : FinalBoundaryOccurrence P history) :
    GeneratedStep boundary.source boundary.target :=
  boundary.step

def continuationExactlyOne
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (boundary : FinalBoundaryOccurrence P history) :
    History.ExactlyOne boundary.labelled.continuation :=
  positiveContinuation_exactlyOne boundary.labelled boundary.positive

theorem uniqueContinuationOccurrence
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (boundary : FinalBoundaryOccurrence P history)
    (occurrence : History.Occurrence boundary.labelled.continuation) :
    occurrence = boundary.continuationOccurrence :=
  boundary.labelled.continuation_occurrences_unique
    occurrence boundary.continuationOccurrence

theorem source_is_perimeterEndpoint
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (boundary : FinalBoundaryOccurrence P history) :
    boundary.source = perimeterEndpoint P :=
  boundary.continuationExactlyOne.locatedStep_source
    boundary.continuationOccurrence

theorem target_is_historyEndpoint
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (boundary : FinalBoundaryOccurrence P history) :
    boundary.target = history.endpoint :=
  boundary.continuationExactlyOne.locatedStep_target
    boundary.continuationOccurrence

theorem target_is_canonicalTarget
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (boundary : FinalBoundaryOccurrence P history) :
    boundary.target = canonicalTarget (perimeterEndpoint P) := by
  exact boundary.step.formedByFreeLayer.trans
    (congrArg canonicalTarget boundary.source_is_perimeterEndpoint)

theorem source_cursor_is_boundary
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (boundary : FinalBoundaryOccurrence P history) :
    boundary.source.1 = .within (.boundary P.perimeter.finalNode) :=
  (congrArg Sigma.fst boundary.source_is_perimeterEndpoint).trans
    (perimeterEndpoint_cursor_boundary P)

theorem target_cursor_is_beyond_first
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (boundary : FinalBoundaryOccurrence P history) :
    boundary.target.1 = .beyond .first := by
  exact (congrArg Sigma.fst boundary.target_is_canonicalTarget).trans
    (generate_after_perimeter_is_beyond P)

theorem compatibility_is_leaveBoundary
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (boundary : FinalBoundaryOccurrence P history) :
    HEq boundary.step.compatibility
      (ReturnedCompatible.leaveBoundary P.perimeter.finalNode) := by
  have exactCompatibility := boundary.step.compatibilityWitnessExact
  exact exactCompatibility.trans (by
    rw [boundary.source_cursor_is_boundary]
    rfl)

end FinalBoundaryOccurrence

/- The interpretation keeps the actual free boundary step and the invoked
   circular junction in one positive witness without identifying them.  It
   also records the exact formation, provenance and transported obstruction
   carried by the actual occurrence. -/
structure FinalClosureInterpretation
    (P : CircularPresentation)
    (history : RootedGeneratedHistory P) where
  boundary : FinalBoundaryOccurrence P history
  actualStepCompatibility :
    ReturnedCompatible P
      (implicitRead boundary.source)
      (explicitRead boundary.target)
  actualStepCompatibilityIsExact :
    actualStepCompatibility = boundary.step.compatibility
  junction : FinalJunctionCompatibility P
  junctionIsDistinguished : junction = P.finalJunction
  formationRecord : FormationRecord P boundary.target.2.1
  formationRecordIsStepExact :
    formationRecord = boundary.step.currentFormationRecord
  provenanceRecord :
    HistoricalProvenanceRecord P
      boundary.source boundary.target.2.1
  provenanceRecordIsStepExact :
    provenanceRecord = boundary.step.sourceProvenanceInscribedInTarget
  sourceObstruction : PositiveClosureObstruction P
  sourceObstructionIsExact :
    sourceObstruction =
      boundary.source.2.1.1.inheritedClosureObstruction
  targetObstruction : PositiveClosureObstruction P
  targetObstructionIsExact :
    targetObstruction =
      boundary.target.2.1.1.inheritedClosureObstruction
  targetObstructionIsInherited : targetObstruction = sourceObstruction
  targetObstructionIsInitial :
    targetObstruction = P.positiveClosureObstruction

def finalClosureInterpretation
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (boundary : FinalBoundaryOccurrence P history) :
    FinalClosureInterpretation P history :=
  { boundary := boundary
    actualStepCompatibility := boundary.step.compatibility
    actualStepCompatibilityIsExact := rfl
    junction := P.finalJunction
    junctionIsDistinguished := rfl
    formationRecord := boundary.step.currentFormationRecord
    formationRecordIsStepExact := rfl
    provenanceRecord := boundary.step.sourceProvenanceInscribedInTarget
    provenanceRecordIsStepExact := rfl
    sourceObstruction :=
      boundary.source.2.1.1.inheritedClosureObstruction
    sourceObstructionIsExact := rfl
    targetObstruction :=
      boundary.target.2.1.1.inheritedClosureObstruction
    targetObstructionIsExact := rfl
    targetObstructionIsInherited :=
      boundary.step.inheritedClosureObstructionExact
    targetObstructionIsInitial :=
      (congrArg
        (fun state : PositiveConstitution P =>
          state.2.1.1.inheritedClosureObstruction)
        boundary.target_is_historyEndpoint).trans
        (RootedGeneratedHistory.terminalClosureObstruction_is_initial history) }

namespace FinalClosureInterpretation

def actualFreeStep
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (interpretation : FinalClosureInterpretation P history) :
    GeneratedStep interpretation.boundary.source
      interpretation.boundary.target :=
  interpretation.boundary.step

def invokedFinalJunction
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (interpretation : FinalClosureInterpretation P history) :
    FinalJunctionCompatibility P :=
  interpretation.junction

theorem sourceObstructionIsInitial
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (interpretation : FinalClosureInterpretation P history) :
    interpretation.sourceObstruction = P.positiveClosureObstruction :=
  interpretation.targetObstructionIsInherited.symm.trans
    interpretation.targetObstructionIsInitial

theorem actualFreeStep_source_is_terminalImplicit
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (interpretation : FinalClosureInterpretation P history) :
    implicitRead interpretation.boundary.source =
      .source P.perimeter.finalNode.implicit := by
  rw [interpretation.boundary.source_is_perimeterEndpoint]
  change implicitAt (perimeterEndpoint P).1 = _
  rw [perimeterEndpoint_cursor_boundary]
  rfl

theorem actualFreeStep_target_is_freeExplicit
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (interpretation : FinalClosureInterpretation P history) :
    explicitRead interpretation.boundary.target =
      .formed (.beyond .first) := by
  change explicitAt interpretation.boundary.target.1 = _
  rw [interpretation.boundary.target_cursor_is_beyond_first]
  rfl

def invokedFinalJunction_source
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (_interpretation : FinalClosureInterpretation P history) : P.Implicit :=
  P.perimeter.finalNode.implicit

def invokedFinalJunction_target
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (_interpretation : FinalClosureInterpretation P history) : P.Explicit :=
  P.initialNode.explicit

theorem invokedFinalJunction_source_is_terminalImplicit
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (interpretation : FinalClosureInterpretation P history) :
    interpretation.invokedFinalJunction_source =
      P.perimeter.finalNode.implicit :=
  rfl

theorem invokedFinalJunction_target_is_initialExplicit
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (interpretation : FinalClosureInterpretation P history) :
    interpretation.invokedFinalJunction_target =
      P.initialNode.explicit :=
  rfl

end FinalClosureInterpretation

structure ConstitutiveClosureAttachment
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (interpretation : FinalClosureInterpretation P history) where
  formationRecord :
    FormationRecord P interpretation.boundary.target.2.1
  formationRecordIsExact :
    formationRecord = interpretation.formationRecord
  provenanceRecord :
    HistoricalProvenanceRecord P
      interpretation.boundary.source
      interpretation.boundary.target.2.1
  provenanceRecordIsExact :
    provenanceRecord = interpretation.provenanceRecord
  obstruction : PositiveClosureObstruction P
  obstructionIsExact : obstruction = interpretation.targetObstruction

def ConstitutiveClosureAttachment.canonical
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (interpretation : FinalClosureInterpretation P history) :
    ConstitutiveClosureAttachment interpretation :=
  { formationRecord := interpretation.formationRecord
    formationRecordIsExact := rfl
    provenanceRecord := interpretation.provenanceRecord
    provenanceRecordIsExact := rfl
    obstruction := interpretation.targetObstruction
    obstructionIsExact := rfl }

namespace ConstitutiveClosureAttachment

theorem formationRecordIsStepExact
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    {interpretation : FinalClosureInterpretation P history}
    (attachment : ConstitutiveClosureAttachment interpretation) :
    attachment.formationRecord =
      interpretation.boundary.step.currentFormationRecord :=
  attachment.formationRecordIsExact.trans
    interpretation.formationRecordIsStepExact

theorem provenanceRecordIsStepExact
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    {interpretation : FinalClosureInterpretation P history}
    (attachment : ConstitutiveClosureAttachment interpretation) :
    attachment.provenanceRecord =
      interpretation.boundary.step.sourceProvenanceInscribedInTarget :=
  attachment.provenanceRecordIsExact.trans
    interpretation.provenanceRecordIsStepExact

theorem obstructionIsInitial
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    {interpretation : FinalClosureInterpretation P history}
    (attachment : ConstitutiveClosureAttachment interpretation) :
    attachment.obstruction = P.positiveClosureObstruction :=
  attachment.obstructionIsExact.trans
    interpretation.targetObstructionIsInitial

end ConstitutiveClosureAttachment

structure BilateralClosureAttemptAt
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (interpretation : FinalClosureInterpretation P history) where
  attachment : ConstitutiveClosureAttachment interpretation
  explicitTotalization : ExplicitTotalization P
  implicitTotalization : ImplicitTotalization P

namespace BilateralClosureAttemptAt

def explicitContraction
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    {interpretation : FinalClosureInterpretation P history}
    (attempt : BilateralClosureAttemptAt interpretation) :
    ContractedClosureDifference P :=
  { difference := P.initialNode.difference
    isInitialDifference := rfl
    provenance := attempt.attachment.obstruction.provenance
    poleContraction :=
      (explicitTotalizationContractsClosureDifference
        attempt.explicitTotalization).poleContraction }

def implicitContraction
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    {interpretation : FinalClosureInterpretation P history}
    (attempt : BilateralClosureAttemptAt interpretation) :
    ContractedClosureDifference P :=
  { difference := P.initialNode.difference
    isInitialDifference := rfl
    provenance := attempt.attachment.obstruction.provenance
    poleContraction :=
      (implicitTotalizationContractsClosureDifference
        attempt.implicitTotalization).poleContraction }

structure Contractions
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    {interpretation : FinalClosureInterpretation P history}
    (attempt : BilateralClosureAttemptAt interpretation) where
  explicitSide : ContractedClosureDifference P
  explicitSideIsDerived : explicitSide = attempt.explicitContraction
  implicitSide : ContractedClosureDifference P
  implicitSideIsDerived : implicitSide = attempt.implicitContraction

def contractions
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    {interpretation : FinalClosureInterpretation P history}
    (attempt : BilateralClosureAttemptAt interpretation) :
    attempt.Contractions :=
  { explicitSide := attempt.explicitContraction
    explicitSideIsDerived := rfl
    implicitSide := attempt.implicitContraction
    implicitSideIsDerived := rfl }

def rejectExplicit
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    {interpretation : FinalClosureInterpretation P history}
    (attempt : BilateralClosureAttemptAt interpretation) : False :=
  attempt.attachment.obstruction.rejectsContraction
    attempt.explicitContraction.initialPoleContraction

def rejectImplicit
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    {interpretation : FinalClosureInterpretation P history}
    (attempt : BilateralClosureAttemptAt interpretation) : False :=
  attempt.attachment.obstruction.rejectsContraction
    attempt.implicitContraction.initialPoleContraction

end BilateralClosureAttemptAt

structure CircularRefinement
    (P : CircularPresentation)
    (history : RootedGeneratedHistory P) where
  extension : PerimeterExtension P history
  labelling : FaithfulPerimeterLabelling P history extension
  realizesNonClosing :
    (occurrence : History.Occurrence history.history) →
    (position : NonClosingPosition P.perimeter) →
    labelling.label occurrence = .inl position →
      RequirementOccurrenceAgreement P history position occurrence
  realizesFinal :
    (positive : PositiveContinuation extension) →
      BilateralClosureAttemptAt
        (finalClosureInterpretation
          (finalBoundaryOccurrence
            { extension := extension, labelling := labelling }
            positive))

namespace CircularRefinement

def toLabelled
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (refinement : CircularRefinement P history) :
    FaithfullyLabelledPerimeterExtension P history :=
  { extension := refinement.extension
    labelling := refinement.labelling }

def continuation
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (refinement : CircularRefinement P history) :
    GeneratedHistory (perimeterEndpoint P) history.endpoint :=
  refinement.extension.continuation

def recompose
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (refinement : CircularRefinement P history) :
    History.append (perimeterHistory P) refinement.continuation =
      history.history :=
  refinement.extension.recompose

def label
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (refinement : CircularRefinement P history) :
    History.Occurrence history.history → CircularRequirement P :=
  refinement.labelling.label

def preservesNonClosingLabels
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (refinement : CircularRefinement P history)
    (position : NonClosingPosition P.perimeter) :
    refinement.label (refinement.extension.oldOccurrence position) =
      .inl position :=
  refinement.labelling.preservesNonClosingLabels position

def requirementFaithful
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (refinement : CircularRefinement P history)
    (first second : History.Occurrence history.history) :
    refinement.label first = refinement.label second → first = second :=
  refinement.labelling.requirementFaithful first second

def oldOccurrence
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (refinement : CircularRefinement P history)
    (position : NonClosingPosition P.perimeter) :
    History.Occurrence history.history :=
  refinement.extension.oldOccurrence position

def newOccurrence
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (refinement : CircularRefinement P history)
    (occurrence : History.Occurrence refinement.continuation) :
    History.Occurrence history.history :=
  refinement.extension.newOccurrence occurrence

theorem old_new_occurrences_disjoint
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (refinement : CircularRefinement P history)
    (position : NonClosingPosition P.perimeter)
    (occurrence : History.Occurrence refinement.continuation) :
    refinement.oldOccurrence position ≠
      refinement.newOccurrence occurrence := by
  exact refinement.extension.old_new_occurrences_disjoint position occurrence

theorem newOccurrence_cannotReuseNonClosingRequirement
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (refinement : CircularRefinement P history)
    (newOccurrence : History.Occurrence refinement.continuation)
    (position : NonClosingPosition P.perimeter)
    (labelEquality :
      refinement.label (refinement.newOccurrence newOccurrence) =
        .inl position) : False := by
  exact refinement.toLabelled.newOccurrence_cannotReuseNonClosingRequirement
    newOccurrence position labelEquality

end CircularRefinement

def identityCircularRefinement (P : CircularPresentation) :
    CircularRefinement P (perimeterDeployment P) :=
  { extension := identityPerimeterExtension P
    labelling :=
      { label := fun occurrence =>
          .inl (occurrenceToRequirement P occurrence)
        preservesNonClosingLabels := by
          intro position
          exact congrArg Sum.inl
            (requirementToOccurrence_toRequirement P position)
        requirementFaithful := by
          intro first second labelEquality
          have positionEquality :
              occurrenceToRequirement P first =
                occurrenceToRequirement P second :=
            Sum.inl.inj labelEquality
          exact (occurrenceToRequirement_toOccurrence P first).symm.trans
            ((congrArg (requirementToOccurrence P) positionEquality).trans
              (occurrenceToRequirement_toOccurrence P second)) }
    realizesNonClosing := by
      intro occurrence position labelEquality
      have positionEquality :
          occurrenceToRequirement P occurrence = position :=
        Sum.inl.inj labelEquality
      cases positionEquality
      have roundTrip := occurrenceToRequirement_toOccurrence P occurrence
      exact RequirementOccurrenceAgreement.transportOccurrence roundTrip
        (canonicalRequirementAgreement P _)
    realizesFinal := fun positive =>
      False.elim (rootContinuation_not_positive P positive) }


end StrongPerimetralTurning

/- AXIOM_AUDIT_BEGIN -/
#print axioms StrongPerimetralTurning.CircularSpecificationSatisfaction
#print axioms StrongPerimetralTurning.FinalClosureInterpretation
#print axioms StrongPerimetralTurning.CircularRefinement
/- AXIOM_AUDIT_END -/
