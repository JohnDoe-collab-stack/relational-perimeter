import RelationalPerimeter.Foundations.FreeConstitution

/- The proposition-valued definitions below are intentionally transparent,
   and the independent input families intentionally keep distinct universes. -/
set_option linter.defProp false
set_option linter.checkUnivs false

namespace StrongPerimetralTurning

universe uE uI uK uD uP uN uEnd uLoop uA uB uV

/-! ## Proof-relevant histories -/

inductive History
    {State : Type uA}
    (Step : State → State → Type uB) : State → State → Type _
  | root : History Step a a
  | extend : History Step a b → Step b c → History Step a c

namespace History

def append
    {State : Type uA}
    {Step : State → State → Type uB}
    {a b c : State} :
    History Step a b → History Step b c → History Step a c
  | firstHistory, .root => firstHistory
  | firstHistory, .extend continuation step =>
      .extend (append firstHistory continuation) step

def appendRootExact
    {State : Type uA}
    {Step : State → State → Type uB}
    {a b : State}
    (history : History Step a b) :
    append history (.root : History Step b b) = history :=
  rfl

def appendExtendExact
    {State : Type uA}
    {Step : State → State → Type uB}
    {a b c d : State}
    (firstHistory : History Step a b)
    (continuation : History Step b c)
    (step : Step c d) :
    append firstHistory (.extend continuation step) =
      .extend (append firstHistory continuation) step :=
  rfl

@[simp] theorem append_root
    {State : Type uA}
    {Step : State → State → Type uB}
    {a b : State}
    (history : History Step a b) :
    append history (.root : History Step b b) = history := rfl

theorem root_append
    {State : Type uA}
    {Step : State → State → Type uB}
    {a b : State}
    (history : History Step a b) :
    append (.root : History Step a a) history = history := by
  induction history with
  | root => rfl
  | extend history step ih =>
      change History.extend (append .root history) step = .extend history step
      rw [ih]

theorem append_associative
    {State : Type uA}
    {Step : State → State → Type uB}
    {a b c d : State}
    (first : History Step a b)
    (second : History Step b c)
    (third : History Step c d) :
    append (append first second) third =
      append first (append second third) := by
  induction third with
  | root => rfl
  | extend third step ih =>
      change History.extend (append (append first second) third) step =
        History.extend (append first (append second third)) step
      rw [ih]

inductive Occurrence
    {State : Type uA}
    {Step : State → State → Type uB} :
    {a b : State} → History Step a b → Type _
  | last
      {a b c : State}
      {history : History Step a b}
      {step : Step b c} : Occurrence (.extend history step)
  | earlier
      {a b c : State}
      {history : History Step a b}
      {step : Step b c} :
      Occurrence history → Occurrence (.extend history step)

/- An occurrence readout is deliberately only a post-constitutive assignment
   of values to occurrences already carried by one history.  The codomain is
   arbitrary, but no inhabitant, injectivity, faithfulness, or compatibility
   law is supplied by this abbreviation.  Such properties must be stated
   separately; the readout neither creates nor identifies occurrences.

   Conceptually, occurrences and their exact correspondences form a structural
   bus onto which independent readouts can be connected after constitution. -/
abbrev OccurrenceReadout
    {State : Type uA}
    {Step : State → State → Type uB}
    {source target : State}
    (history : History Step source target)
    (Value : Type uV) : Type _ :=
  Occurrence history → Value

/- Structural chronology of step occurrences in one history.  This relation
   carries only precedence information and introduces no numerical rank. -/
inductive OccurrencePrecedes
    {State : Type uA}
    {Step : State → State → Type uB} :
    {a b : State} →
    {history : History Step a b} →
    Occurrence history →
    Occurrence history →
    Prop
  | earlier_last
      {a b c : State}
      {history : History Step a b}
      {step : Step b c}
      (occurrence : Occurrence history) :
      OccurrencePrecedes
        (history := .extend history step)
        (.earlier occurrence)
        .last
  | earlier_earlier
      {a b c : State}
      {history : History Step a b}
      {step : Step b c}
      {first second : Occurrence history} :
      OccurrencePrecedes first second →
      OccurrencePrecedes
        (history := .extend history step)
        (.earlier first)
        (.earlier second)

/- Immediate chronology of step occurrences.  It records that the second
   occurrence is the very next generated step after the first. -/
inductive OccurrenceNext
    {State : Type uA}
    {Step : State → State → Type uB} :
    {a b : State} →
    {history : History Step a b} →
    Occurrence history →
    Occurrence history →
    Prop
  | previous_last
      {a b c d : State}
      {history : History Step a b}
      {previousStep : Step b c}
      {lastStep : Step c d} :
      OccurrenceNext
        (history := .extend (.extend history previousStep) lastStep)
        (.earlier (.last : Occurrence (.extend history previousStep)))
        .last
  | earlier_earlier
      {a b c : State}
      {history : History Step a b}
      {step : Step b c}
      {first second : Occurrence history} :
      OccurrenceNext first second →
      OccurrenceNext
        (history := .extend history step)
        (.earlier first)
        (.earlier second)

namespace OccurrenceNext

theorem toPrecedes
    {State : Type uA}
    {Step : State → State → Type uB}
    {a b : State}
    {history : History Step a b}
    {first second : Occurrence history}
    (next : OccurrenceNext first second) :
    OccurrencePrecedes first second := by
  induction next with
  | previous_last => exact .earlier_last .last
  | earlier_earlier _ inductionHypothesis =>
      exact .earlier_earlier inductionHypothesis

end OccurrenceNext

namespace OccurrencePrecedes

theorem ne
    {State : Type uA}
    {Step : State → State → Type uB}
    {a b : State}
    {history : History Step a b}
    {first second : Occurrence history}
    (precedes : OccurrencePrecedes first second) : first ≠ second := by
  induction precedes with
  | earlier_last _ =>
      intro equality
      cases equality
  | earlier_earlier _ inductionHypothesis =>
      intro equality
      exact inductionHypothesis (Occurrence.earlier.inj equality)

theorem trichotomy
    {State : Type uA}
    {Step : State → State → Type uB}
    {a b : State}
    {history : History Step a b}
    (first second : Occurrence history) :
    first = second ∨
      OccurrencePrecedes first second ∨
        OccurrencePrecedes second first := by
  induction first with
  | last =>
      cases second with
      | last => exact Or.inl rfl
      | earlier second =>
          exact Or.inr (Or.inr (.earlier_last second))
  | earlier first inductionHypothesis =>
      cases second with
      | last =>
          exact Or.inr (Or.inl (.earlier_last first))
      | earlier second =>
          rcases inductionHypothesis second with
            equality | precedes | follows
          · exact Or.inl (congrArg Occurrence.earlier equality)
          · exact Or.inr (Or.inl (.earlier_earlier precedes))
          · exact Or.inr (Or.inr (.earlier_earlier follows))

end OccurrencePrecedes

/- An exactly-one history is characterized structurally, before any numerical
   length is available: it is one extension of the root history. -/
inductive ExactlyOne
    {State : Type uA}
    {Step : State → State → Type uB}
    {source target : State} :
    History Step source target → Type _
  | single (step : Step source target) :
      ExactlyOne (.extend .root step)

structure LocatedStep
    {State : Type uA}
    (Step : State → State → Type uB) where
  source : State
  target : State
  step : Step source target

def Occurrence.locatedStep
    {State : Type uA}
    {Step : State → State → Type uB}
    {a b : State}
    {history : History Step a b} :
    Occurrence history → LocatedStep Step
  | .last (step := step) => ⟨_, _, step⟩
  | .earlier occurrence => occurrence.locatedStep

def Occurrence.gapAt
    {State : Type uA}
    {Step : State → State → Type uB}
    {source target : State}
    {history : History Step source target}
    (occurrence : Occurrence history) :
    Step occurrence.locatedStep.source occurrence.locatedStep.target :=
  occurrence.locatedStep.step

namespace ExactlyOne

def step
    {State : Type uA}
    {Step : State → State → Type uB}
    {source target : State}
    {history : History Step source target}
    (one : ExactlyOne history) : Step source target :=
  match one with
  | .single step => step

def canonicalOccurrence
    {State : Type uA}
    {Step : State → State → Type uB}
    {source target : State}
    {history : History Step source target}
    (one : ExactlyOne history) : Occurrence history :=
  match one with
  | .single _ => .last

theorem occurrence_unique
    {State : Type uA}
    {Step : State → State → Type uB}
    {source target : State}
    {history : History Step source target}
    (one : ExactlyOne history)
    (occurrence : Occurrence history) :
    occurrence = one.canonicalOccurrence := by
  cases one with
  | single step =>
      cases occurrence with
      | last => rfl
      | earlier impossible => cases impossible

theorem locatedStep_source
    {State : Type uA}
    {Step : State → State → Type uB}
    {source target : State}
    {history : History Step source target}
    (one : ExactlyOne history)
    (occurrence : Occurrence history) :
    occurrence.locatedStep.source = source := by
  cases one with
  | single step =>
      cases occurrence with
      | last => rfl
      | earlier impossible => cases impossible

theorem locatedStep_target
    {State : Type uA}
    {Step : State → State → Type uB}
    {source target : State}
    {history : History Step source target}
    (one : ExactlyOne history)
    (occurrence : Occurrence history) :
    occurrence.locatedStep.target = target := by
  cases one with
  | single step =>
      cases occurrence with
      | last => rfl
      | earlier impossible => cases impossible

end ExactlyOne

def embedLeftOccurrence
    {State : Type uA}
    {Step : State → State → Type uB}
    {a b c : State}
    {firstHistory : History Step a b}
    (occurrence : Occurrence firstHistory)
    (continuation : History Step b c) :
    Occurrence (append firstHistory continuation) :=
  match continuation with
  | .root => occurrence
  | .extend continuation _ =>
      .earlier (embedLeftOccurrence occurrence continuation)

theorem embedLeftOccurrence_injective
    {State : Type uA}
    {Step : State → State → Type uB}
    {a b c : State}
    {firstHistory : History Step a b}
    (continuation : History Step b c) :
    Function.Injective
      (fun occurrence : Occurrence firstHistory =>
        embedLeftOccurrence occurrence continuation) := by
  induction continuation with
  | root =>
      intro first second equality
      exact equality
  | extend continuation step inductionHypothesis =>
      intro first second equality
      exact inductionHypothesis (Occurrence.earlier.inj equality)

def embedRightOccurrence
    {State : Type uA}
    {Step : State → State → Type uB}
    {a b c : State}
    (firstHistory : History Step a b)
    {continuation : History Step b c} :
    Occurrence continuation → Occurrence (append firstHistory continuation)
  | @Occurrence.last _ _ _ _ _ history step =>
      (.last : Occurrence (.extend (append firstHistory history) step))
  | @Occurrence.earlier _ _ _ _ _ history step occurrence =>
      .earlier (embedRightOccurrence firstHistory occurrence)

theorem leftRightDisjoint
    {State : Type uA}
    {Step : State → State → Type uB}
    {a b c : State}
    {firstHistory : History Step a b}
    (oldOccurrence : Occurrence firstHistory)
    {continuation : History Step b c}
    (newOccurrence : Occurrence continuation) :
    embedLeftOccurrence oldOccurrence continuation ≠
      embedRightOccurrence firstHistory newOccurrence := by
  induction newOccurrence with
  | last =>
      intro equality
      cases equality
  | earlier occurrence ih =>
      intro equality
      exact ih (Occurrence.earlier.inj equality)

def splitAppendOccurrenceAux
    {State : Type uA}
    {Step : State → State → Type uB}
    {a b c : State}
    (firstHistory : History Step a b) :
    (continuation : History Step b c) →
    Occurrence (append firstHistory continuation) →
      Occurrence firstHistory ⊕ Occurrence continuation
  | .root, occurrence =>
      .inl occurrence
  | .extend previous _step, occurrence =>
      match occurrence with
      | .last => .inr .last
      | .earlier earlier =>
          match splitAppendOccurrenceAux firstHistory previous earlier with
          | .inl old => .inl old
          | .inr new => .inr (.earlier new)

def splitAppendOccurrence
    {State : Type uA}
    {Step : State → State → Type uB}
    {a b c : State}
    {firstHistory : History Step a b}
    {continuation : History Step b c} :
    Occurrence (append firstHistory continuation) →
      Occurrence firstHistory ⊕ Occurrence continuation :=
  splitAppendOccurrenceAux firstHistory continuation

def classifyAppendOccurrence
    {State : Type uA}
    {Step : State → State → Type uB}
    {a b c : State}
    (firstHistory : History Step a b) :
    (continuation : History Step b c) →
    (occurrence : Occurrence (append firstHistory continuation)) →
    (Σ old : Occurrence firstHistory,
      PLift (embedLeftOccurrence old continuation = occurrence)) ⊕
      (Σ new : Occurrence continuation,
        PLift (embedRightOccurrence firstHistory new = occurrence))
  | .root, occurrence => .inl ⟨occurrence, ⟨rfl⟩⟩
  | .extend continuation step, occurrence =>
      match occurrence with
      | .last =>
          .inr ⟨(.last : Occurrence (.extend continuation step)), ⟨rfl⟩⟩
      | .earlier occurrence =>
          match classifyAppendOccurrence firstHistory continuation occurrence with
          | .inl ⟨old, reconstruction⟩ =>
              .inl ⟨old,
                ⟨congrArg Occurrence.earlier reconstruction.down⟩⟩
          | .inr ⟨new, reconstruction⟩ =>
              .inr ⟨Occurrence.earlier new,
                ⟨congrArg Occurrence.earlier reconstruction.down⟩⟩

theorem embedRightOccurrence_injective
    {State : Type uA}
    {Step : State → State → Type uB}
    {a b c : State}
    (firstHistory : History Step a b)
    {continuation : History Step b c} :
    Function.Injective (embedRightOccurrence firstHistory :
      Occurrence continuation → Occurrence (append firstHistory continuation)) := by
  intro first
  induction first with
  | last =>
      intro second equality
      cases second with
      | last => rfl
      | earlier earlier => cases equality
  | earlier first inductionHypothesis =>
      intro second equality
      cases second with
      | last => cases equality
      | earlier second =>
          exact congrArg Occurrence.earlier
            (inductionHypothesis (Occurrence.earlier.inj equality))

theorem locatedStep_embedLeft
    {State : Type uA}
    {Step : State → State → Type uB}
    {a b c : State}
    {firstHistory : History Step a b}
    (occurrence : Occurrence firstHistory)
    (continuation : History Step b c) :
    (embedLeftOccurrence occurrence continuation).locatedStep =
      occurrence.locatedStep := by
  induction continuation with
  | root => rfl
  | extend continuation step inductionHypothesis =>
      exact inductionHypothesis

theorem locatedStep_embedRight
    {State : Type uA}
    {Step : State → State → Type uB}
    {a b c : State}
    (firstHistory : History Step a b)
    {continuation : History Step b c}
    (occurrence : Occurrence continuation) :
    (embedRightOccurrence firstHistory occurrence).locatedStep =
      occurrence.locatedStep := by
  induction occurrence with
  | last => rfl
  | earlier occurrence inductionHypothesis =>
      exact inductionHypothesis
inductive Vertex
    {State : Type uA}
    {Step : State → State → Type uB} :
    {a b : State} → History Step a b → Type _
  | root : Vertex (.root : History Step a a)
  | earlier : Vertex history → Vertex (.extend history step)
  | final : Vertex (.extend history step)

def initialVertex
    {State : Type uA}
    {Step : State → State → Type uB}
    {a b : State}
    (history : History Step a b) : Vertex history :=
  match history with
  | .root => .root
  | .extend previous _ => .earlier (initialVertex previous)

def finalVertex
    {State : Type uA}
    {Step : State → State → Type uB}
    {a b : State}
    (history : History Step a b) : Vertex history :=
  match history with
  | .root => .root
  | .extend _ _ => .final

def vertexAppendLeft
    {State : Type uA}
    {Step : State → State → Type uB}
    {source middle target : State}
    {firstHistory : History Step source middle}
    (vertex : Vertex firstHistory)
    (continuation : History Step middle target) :
    Vertex (append firstHistory continuation) :=
  match continuation with
  | .root => vertex
  | .extend previous _ =>
      .earlier (vertexAppendLeft vertex previous)

def vertexAppendRight
    {State : Type uA}
    {Step : State → State → Type uB}
    {source middle target : State}
    (firstHistory : History Step source middle)
    {continuation : History Step middle target} :
    Vertex continuation → Vertex (append firstHistory continuation) :=
  match continuation with
  | .root => fun _ => finalVertex firstHistory
  | .extend _previous _ => fun vertex =>
      match vertex with
      | .earlier previousVertex =>
          .earlier (vertexAppendRight firstHistory previousVertex)
      | .final => .final

def vertex_append_left := @vertexAppendLeft

def vertex_append_right := @vertexAppendRight

structure Positive
    {State : Type uA}
    (Step : State → State → Type uB)
    (a b : State) where
  predecessor : State
  priorHistory : History Step a predecessor
  lastStep : Step predecessor b

def Positive.toHistory
    {State : Type uA}
    {Step : State → State → Type uB}
    {a b : State}
    (positive : Positive Step a b) : History Step a b :=
  .extend positive.priorHistory positive.lastStep

def Positive.lastOccurrence
    {State : Type uA}
    {Step : State → State → Type uB}
    {a b : State}
    (positive : Positive Step a b) : Occurrence positive.toHistory :=
  .last

inductive View
    {State : Type uA}
    {Step : State → State → Type uB}
    {a : State} : {b : State} → History Step a b → Type _
  | root : View (.root : History Step a a)
  | positive {b : State} (path : Positive Step a b) : View path.toHistory

def view
    {State : Type uA}
    {Step : State → State → Type uB}
    {a b : State}
    (history : History Step a b) : View history := by
  cases history with
  | root => exact .root
  | extend priorHistory step =>
      exact .positive ⟨_, priorHistory, step⟩

def rootOrPositive
    {State : Type uA}
    {Step : State → State → Type uB}
    {source target : State}
    (history : History Step source target) :
    (PLift (target = source) ×
      PLift (HEq history (.root : History Step source source))) ⊕
      (Σ positive : History.Positive Step source target,
        PLift (history = positive.toHistory)) :=
  match history with
  | .root => .inl ⟨⟨rfl⟩, ⟨HEq.rfl⟩⟩
  | .extend priorHistory step =>
      .inr ⟨⟨_, priorHistory, step⟩, ⟨rfl⟩⟩

def appendRootOrPositive
    {State : Type uA}
    {Step : State → State → Type uB}
    {source middle target : State}
    (firstHistory : History Step source middle)
    (continuation : History Step middle target) :
    (PLift (target = middle) ×
      PLift (HEq (append firstHistory continuation) firstHistory)) ⊕
      (Σ positive : History.Positive Step middle target,
        PLift (continuation = positive.toHistory)) :=
  match continuation with
  | .root => .inl ⟨⟨rfl⟩, ⟨HEq.rfl⟩⟩
  | .extend priorHistory step =>
      .inr ⟨⟨_, priorHistory, step⟩, ⟨rfl⟩⟩

end History

abbrev GeneratedHistory
    {P : CircularPresentation}
    (source target : PositiveConstitution P) :=
  History (@GeneratedStep P) source target

theorem generatedHistory_preservesClosureObstruction
    {P : CircularPresentation}
    {source target : PositiveConstitution P}
    (history : GeneratedHistory source target) :
    target.2.1.1.inheritedClosureObstruction =
      source.2.1.1.inheritedClosureObstruction := by
  induction history with
  | root => rfl
  | extend prior step inductionHypothesis =>
      exact step.inheritedClosureObstructionExact.trans inductionHypothesis

structure RootedGeneratedHistory (P : CircularPresentation) where
  endpoint : PositiveConstitution P
  history : GeneratedHistory (initialPositive P) endpoint

/-! ## Occurrence-indexed normative adequacy -/

universe uSpec uAdequacy uRegime uFaithful

/- Normative adequacy is indexed by complete step occurrences.  No projection to
   source, target, cursor, or any returned reading is built into this layer. -/
structure NormativeAdequacy
    (P : CircularPresentation) where
  AlignmentSpec :
    Type uSpec
  RegimeAdequateAtOccurrence :
    AlignmentSpec →
    (R : RootedGeneratedHistory P → Type uRegime) →
    (H : RootedGeneratedHistory P) →
    History.Occurrence H.history →
    Type uAdequacy

/- `AdequateAlong` covers exactly the step occurrences carried by the history.
   The root history has no occurrences, so this type is vacuously inhabited
   there. Any normative obligation on the initial constitution is a separate
   notion and is deliberately not encoded here. -/
abbrev AdequateAlong
    {P : CircularPresentation}
    (N : NormativeAdequacy P)
    (S : N.AlignmentSpec)
    (R : RootedGeneratedHistory P → Type uRegime)
    (H : RootedGeneratedHistory P) : Type _ :=
  (occurrence : History.Occurrence H.history) →
    N.RegimeAdequateAtOccurrence S R H occurrence

/- A regime exit becomes specification-relative only by composing the existing
   typed diagnostic with adequacy witnesses for every step occurrence of the
   same candidate.  The `RegimeExit` kernel is intentionally unchanged. -/
structure SpecRelativeHistoryExit
    {P : CircularPresentation}
    (N : NormativeAdequacy P)
    (S : N.AlignmentSpec)
    (R : RootedGeneratedHistory P → Type uRegime)
    (Faithful : RootedGeneratedHistory P → Type uFaithful) where
  exit :
    AbstractSegmentedTurning.RegimeExit Faithful R
  adequacy :
    AdequateAlong N S R exit.candidate

def RootedGeneratedHistory.terminalClosureObstruction
    {P : CircularPresentation}
    (history : RootedGeneratedHistory P) : PositiveClosureObstruction P :=
  history.endpoint.2.1.1.inheritedClosureObstruction

theorem RootedGeneratedHistory.terminalClosureObstruction_is_initial
    {P : CircularPresentation}
    (history : RootedGeneratedHistory P) :
    history.terminalClosureObstruction = P.positiveClosureObstruction :=
  (generatedHistory_preservesClosureObstruction history.history).trans
    FreeConstitution.root_inheritedClosureObstruction_exact

theorem rootedGeneratedHistory_ext
    {P : CircularPresentation}
    {first second : RootedGeneratedHistory P}
    (endpointEquality : first.endpoint = second.endpoint)
    (historyEquality : HEq first.history second.history) : first = second := by
  cases first with
  | mk firstEndpoint firstHistory =>
      cases second with
      | mk secondEndpoint secondHistory =>
          cases endpointEquality
          have exactHistory : firstHistory = secondHistory := eq_of_heq historyEquality
          cases exactHistory
          rfl

def rootedHistoryRoot (P : CircularPresentation) : RootedGeneratedHistory P :=
  ⟨initialPositive P, .root⟩

def appendRooted
    {P : CircularPresentation}
    (rooted : RootedGeneratedHistory P)
    {target : PositiveConstitution P}
    (continuation : GeneratedHistory rooted.endpoint target) :
    RootedGeneratedHistory P :=
  ⟨target, History.append rooted.history continuation⟩

def appendGenerated
    {P : CircularPresentation}
    (rooted : RootedGeneratedHistory P)
    (generated :
      Σ target : PositiveConstitution P,
        GeneratedStep rooted.endpoint target) :
    RootedGeneratedHistory P :=
  appendRooted rooted (.extend .root generated.2)

def preserveHistoricalProvenanceIntoCanonicalTarget
    {P : CircularPresentation}
    {origin source : PositiveConstitution P} :
    HistoricalProvenanceRecord P origin source.2.1 →
      HistoricalProvenanceRecord P origin (canonicalTarget source).2.1 := by
  intro record
  change HistoricalProvenanceRecord P origin
    (FreeConstitution.formed source.2.1 source.2.2
      (canonicalFreeLayer source))
  exact .preserved record

def preserveHistoricalProvenanceAlongStep
    {P : CircularPresentation}
    {origin source target : PositiveConstitution P}
    (step : GeneratedStep source target) :
    HistoricalProvenanceRecord P origin source.2.1 →
      HistoricalProvenanceRecord P origin target.2.1 := by
  intro record
  cases step.formedByFreeLayer
  exact preserveHistoricalProvenanceIntoCanonicalTarget record

def preserveHistoricalProvenanceAlongHistory
    {P : CircularPresentation}
    {origin source target : PositiveConstitution P} :
    GeneratedHistory source target →
    HistoricalProvenanceRecord P origin source.2.1 →
      HistoricalProvenanceRecord P origin target.2.1
  | .root, record => record
  | .extend history step, record =>
      preserveHistoricalProvenanceAlongStep step
        (preserveHistoricalProvenanceAlongHistory history record)

def preserveFormationRecordAlongStep
    {P : CircularPresentation}
    {source target : PositiveConstitution P}
    (step : GeneratedStep source target) :
    FormationRecord P source.2.1 → FormationRecord P target.2.1 := by
  intro record
  cases step.formedByFreeLayer
  change FormationRecord P
    (FreeConstitution.formed source.2.1 source.2.2
      (canonicalFreeLayer source))
  exact .preserved record

def preserveFormationRecordAlongHistory
    {P : CircularPresentation}
    {source target : PositiveConstitution P} :
    GeneratedHistory source target →
      FormationRecord P source.2.1 → FormationRecord P target.2.1
  | .root, record => record
  | .extend history step, record =>
      preserveFormationRecordAlongStep step
        (preserveFormationRecordAlongHistory history record)

theorem current_ne_preserved
    {P : CircularPresentation}
    {cursor : PerimeterCursor P}
    {previous : FreeConstitution P cursor}
    {difference : BoundaryDifference P previous}
    {layer : FreeK P previous difference}
    (record : FormationRecord P previous) :
    (FormationRecord.current : FormationRecord P
      (FreeConstitution.formed previous difference layer)) ≠
      FormationRecord.preserved record := by
  intro equality
  cases equality

inductive FreshFormationRecord
    (P : CircularPresentation)
    (source : PositiveConstitution P) :
    PositiveConstitution P → Type _
  | after
      {predecessor : PositiveConstitution P}
      {target : PositiveConstitution P}
      (priorHistory : GeneratedHistory source predecessor)
      (lastStep : GeneratedStep predecessor target) :
      FreshFormationRecord P source target

namespace FreshFormationRecord

def predecessor
    {P : CircularPresentation}
    {source target : PositiveConstitution P} :
    FreshFormationRecord P source target → PositiveConstitution P
  | .after (predecessor := predecessor) _ _ => predecessor

def priorHistory
    {P : CircularPresentation}
    {source target : PositiveConstitution P}
    (fresh : FreshFormationRecord P source target) :
    GeneratedHistory source fresh.predecessor := by
  cases fresh with
  | after priorHistory _ => exact priorHistory

def freshRecord
    {P : CircularPresentation}
    {source target : PositiveConstitution P} :
    FreshFormationRecord P source target → FormationRecord P target.2.1
  | .after _ lastStep => by
      cases lastStep.formedByFreeLayer
      exact lastStep.freshBoundaryDifference.freshRecord

def lastStep
    {P : CircularPresentation}
    {source target : PositiveConstitution P}
    (fresh : FreshFormationRecord P source target) :
    GeneratedStep fresh.predecessor target := by
  cases fresh with
  | after _ lastStep => exact lastStep

theorem notFromPredecessor
    {P : CircularPresentation}
    {source target : PositiveConstitution P}
    (fresh : FreshFormationRecord P source target)
    (oldRecord : FormationRecord P fresh.predecessor.2.1) :
  fresh.freshRecord ≠
      preserveFormationRecordAlongStep fresh.lastStep oldRecord := by
  cases fresh with
  | after priorHistory lastStep =>
      cases lastStep.formedByFreeLayer
      exact lastStep.freshBoundaryDifference.notPreservedOld oldRecord

theorem notFromSource
    {P : CircularPresentation}
    {source target : PositiveConstitution P}
    (fresh : FreshFormationRecord P source target)
    (oldRecord : FormationRecord P source.2.1) :
    fresh.freshRecord ≠
      preserveFormationRecordAlongStep fresh.lastStep
        (preserveFormationRecordAlongHistory fresh.priorHistory oldRecord) :=
  fresh.notFromPredecessor _

end FreshFormationRecord

def positiveGeneratedHistory_hasFreshFormation
    {P : CircularPresentation}
    {source target : PositiveConstitution P}
    (positive : History.Positive (@GeneratedStep P) source target) :
    FreshFormationRecord P source target := by
  exact .after positive.priorHistory positive.lastStep

theorem rootedHistoryEq
    {P : CircularPresentation}
    {first second : RootedGeneratedHistory P}
    (endpointEquality : first.endpoint = second.endpoint)
    (historyEquality : HEq first.history second.history) :
    first = second := by
  cases first with
  | mk firstEndpoint firstHistory =>
      cases second with
      | mk secondEndpoint secondHistory =>
          cases endpointEquality
          cases historyEquality
          rfl

structure ConstitutivePrefix
    {P : CircularPresentation}
    (first second : RootedGeneratedHistory P) : Type _ where
  continuation : GeneratedHistory first.endpoint second.endpoint
  historyExact :
    History.append first.history continuation = second.history

structure StrictConstitutivePrefix
    {P : CircularPresentation}
    (first second : RootedGeneratedHistory P) : Type _ where
  continuation : History.Positive
    (@GeneratedStep P) first.endpoint second.endpoint
  historyExact :
    History.append first.history continuation.toHistory = second.history

def prefixReflexive
    {P : CircularPresentation}
    (history : RootedGeneratedHistory P) :
    ConstitutivePrefix history history := ⟨.root, rfl⟩

def prefixTransitive
    {P : CircularPresentation}
    {first second third : RootedGeneratedHistory P} :
    ConstitutivePrefix first second →
    ConstitutivePrefix second third →
    ConstitutivePrefix first third := by
  rintro ⟨left, leftEquality⟩ ⟨right, rightEquality⟩
  refine ⟨History.append left right, ?_⟩
  rw [← History.append_associative, leftEquality, rightEquality]

def generatedStepCursorAdvance
    {P : CircularPresentation}
    {source target : PositiveConstitution P}
    (step : GeneratedStep source target) :
    CursorAdvance P source.1 target.1 := by
  cases step.formedByFreeLayer
  exact cursorAdvanceGraph source.1

inductive CursorReach (P : CircularPresentation) :
    PerimeterCursor P → PerimeterCursor P → Type _
  | root : CursorReach P cursor cursor
  | extend :
      CursorReach P source middle →
      CursorAdvance P middle target →
      CursorReach P source target

def CursorReach.followedByStep
    {P : CircularPresentation}
    {source middle target : PerimeterCursor P} :
    CursorReach P source middle → CursorAdvance P middle target →
      PositiveCursorAdvance P source target
  | .root, step => .one step
  | .extend previous last, step =>
      .followedBy (previous.followedByStep last) step

def CursorReach.trans
    {P : CircularPresentation}
    {source middle target : PerimeterCursor P} :
    CursorReach P source middle → CursorReach P middle target →
      CursorReach P source target
  | left, .root => left
  | left, .extend previous last =>
      .extend (CursorReach.trans left previous) last

def CursorFuture.transReach
    {P : CircularPresentation}
    {source middle target : PerimeterCursor P}
    (future : CursorFuture P source middle) :
    CursorReach P middle target → CursorFuture P source target
  | .root => future
  | .extend previous last =>
      (future.transReach previous).trans last.toFuture

def generatedHistoryCursorReach
    {P : CircularPresentation}
    {source target : PositiveConstitution P} :
    GeneratedHistory source target → CursorReach P source.1 target.1
  | .root => .root
  | .extend history step =>
      .extend (generatedHistoryCursorReach history)
        (generatedStepCursorAdvance step)

def occurrenceSource_to_historyEndpoint_future
    {P : CircularPresentation}
    {source target : PositiveConstitution P}
    : (history : GeneratedHistory source target) →
    (occurrence : History.Occurrence history) →
      CursorFuture P occurrence.locatedStep.source.1 target.1
  | .root, occurrence => nomatch occurrence
  | .extend _history step, .last =>
      (generatedStepCursorAdvance step).toFuture
  | .extend history step, .earlier earlier =>
      (occurrenceSource_to_historyEndpoint_future history earlier).trans
        (generatedStepCursorAdvance step).toFuture

def occurrenceTarget_to_historyEndpoint_reach
    {P : CircularPresentation}
    {source target : PositiveConstitution P}
    : (history : GeneratedHistory source target) →
    (occurrence : History.Occurrence history) →
      CursorReach P occurrence.locatedStep.target.1 target.1
  | .root, occurrence => nomatch occurrence
  | .extend _history step, .last => .root
  | .extend history step, .earlier earlier =>
      .extend (occurrenceTarget_to_historyEndpoint_reach history earlier)
        (generatedStepCursorAdvance step)

namespace History.OccurrencePrecedes

private def earlierLast_next_or_positiveGap
    {P : CircularPresentation}
    {source target nextTarget : PositiveConstitution P}
    : (history : GeneratedHistory source target) →
    (step : GeneratedStep target nextTarget) →
    (occurrence : History.Occurrence history) →
    History.OccurrenceNext
        (.earlier occurrence)
        (.last : History.Occurrence (.extend history step)) ∨
      Nonempty (CursorFuture P
        occurrence.locatedStep.target.1
        (History.Occurrence.last : History.Occurrence
          (.extend history step)).locatedStep.source.1)
  | .root, _step, occurrence => nomatch occurrence
  | .extend _history _previousStep, step, .last => Or.inl .previous_last
  | .extend history previousStep, _step, .earlier earlier =>
      Or.inr ⟨
        ((occurrenceTarget_to_historyEndpoint_reach history earlier).followedByStep
          (generatedStepCursorAdvance previousStep)).toFuture⟩

theorem sourceCursorFuture
    {P : CircularPresentation}
    {source target : PositiveConstitution P}
    {history : GeneratedHistory source target}
    {first second : History.Occurrence history}
    (precedes : History.OccurrencePrecedes first second) :
    Nonempty (CursorFuture P
      first.locatedStep.source.1 second.locatedStep.source.1) := by
  induction precedes with
  | earlier_last occurrence =>
      exact ⟨occurrenceSource_to_historyEndpoint_future _ occurrence⟩
  | earlier_earlier _ inductionHypothesis =>
      exact inductionHypothesis

theorem next_or_positiveGap
    {P : CircularPresentation}
    {source target : PositiveConstitution P}
    {history : GeneratedHistory source target}
    {first second : History.Occurrence history}
    (precedes : History.OccurrencePrecedes first second) :
    History.OccurrenceNext first second ∨
      Nonempty (CursorFuture P
        first.locatedStep.target.1 second.locatedStep.source.1) := by
  induction precedes with
  | earlier_last occurrence =>
      exact earlierLast_next_or_positiveGap _ _ occurrence
  | earlier_earlier _ inductionHypothesis =>
      rcases inductionHypothesis with next | gap
      · exact Or.inl (.earlier_earlier next)
      · exact Or.inr gap

end History.OccurrencePrecedes

def positiveGeneratedHistory_cursorAdvance
    {P : CircularPresentation}
    {source target : PositiveConstitution P}
    (positive : History.Positive (@GeneratedStep P) source target) :
    PositiveCursorAdvance P source.1 target.1 :=
  (generatedHistoryCursorReach positive.priorHistory).followedByStep
    (generatedStepCursorAdvance positive.lastStep)

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
theorem generatedHistory_equalEndpoints_noOccurrence
    {P : CircularPresentation}
    {source target : PositiveConstitution P}
    (history : GeneratedHistory source target)
    (endpointEquality : source = target) :
    History.Occurrence history → False := by
  cases history with
  | root =>
      intro occurrence
      exact nomatch occurrence
  | extend priorHistory step =>
      intro _occurrence
      let positive : History.Positive (@GeneratedStep P) source target :=
        { predecessor := _
          priorHistory := priorHistory
          lastStep := step }
      exact positiveGeneratedHistory_source_ne_target positive endpointEquality


theorem append_positive_ne
    {P : CircularPresentation}
    (history : RootedGeneratedHistory P)
    {target : PositiveConstitution P}
    (positive : History.Positive
      (@GeneratedStep P) history.endpoint target) :
    appendRooted history positive.toHistory ≠ history := by
  intro equality
  have endpointEquality : target = history.endpoint :=
    congrArg RootedGeneratedHistory.endpoint equality
  exact positiveGeneratedHistory_source_ne_target positive endpointEquality.symm

theorem strictPrefix_ne
    {P : CircularPresentation}
    {first second : RootedGeneratedHistory P}
    (strict : StrictConstitutivePrefix first second) : second ≠ first := by
  intro equality
  have appendedEqualsSecond :
      appendRooted first strict.1.toHistory = second :=
    rootedHistoryEq rfl (heq_of_eq strict.2)
  exact append_positive_ne first strict.1
    (appendedEqualsSecond.trans equality)


end StrongPerimetralTurning

/- AXIOM_AUDIT_BEGIN -/
#print axioms StrongPerimetralTurning.History
#print axioms StrongPerimetralTurning.RootedGeneratedHistory
#print axioms StrongPerimetralTurning.strictPrefix_ne
/- AXIOM_AUDIT_END -/
