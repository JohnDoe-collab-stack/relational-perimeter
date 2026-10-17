import RelationalPerimeter.Constitution.Reals.HeterogeneousRealRuntime
import RelationalPerimeter.Constitution.Reals.DyadicArithmetic

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!+# Executed relational opposite

One current-archive source Step is produced and received by a six-phase
program. Its single action negates that Step's owned response, and its store
retains that action. The rich archive continues both the source archive and
the arithmetic journal. The live callback captures only the compact source
environment; projection laws, not a second rich execution, justify forgetting
the arithmetic history. No presentation or external real is used here.
-/

namespace RelationalPerimeter.Constitution.Reals.RelationalRealNegation
open StrongPerimetralTurning ConstitutiveRuntime HeterogeneousRealRuntime
open ConstitutiveSearch.ContinuationSignatures

variable {P : CircularPresentation} {baseDepth : Nat}

structure NegationAction {Source : Type} (readSource : Source → SignedDyadicCode)
    (searched : Source) where
  private mk ::
  source : Source
  sourceExact : source = searched
  code : SignedDyadicCode
  codeExact : code = (readSource source).neg

structure NegationStored {Source : Type} {readSource : Source → SignedDyadicCode}
    {searched : Source} (acted : NegationAction readSource searched) where
  private mk ::
  action : NegationAction readSource searched
  actionExact : action = acted

def negationProgram {Source : Type} (source : Source)
    (readSource : Source → SignedDyadicCode) (precision : Nat) : Program Unit where
  ReceivedContext _ := Source
  SearchResult _ := Source
  ActionResult _ searched := NegationAction readSource searched
  Accepted _ searched acted := SameValue acted.code (readSource searched).neg
  Authorization _ _ _ _ := Unit
  Decomposition _ _ _ _ _ := Source
  Continuation _ _ _ _ _ _ := Source
  Stored _ _ acted := NegationStored acted
  stamp _ := .limit precision
  receive _ := source
  search _ received := received
  act _ searched := ⟨searched, rfl, (readSource searched).neg, rfl⟩
  preserves _ searched acted := by
    have exact : acted.code = (readSource searched).neg := by
      rw [acted.codeExact, acted.sourceExact]
    exact Eq.rec (motive := fun target _ => SameValue acted.code target)
      (SameValue.refl acted.code) exact
  authorize _ _ _ _ := ()
  decompose _ searched _ _ _ := searched
  resume _ _ _ _ _ decomposed := decomposed
  store _ _ acted _ _ _ _ := ⟨acted, rfl⟩
  actionCode acted := acted.code
  read stored := stored.action.code
  readStoredExact stored := congrArg NegationAction.code stored.actionExact

theorem negationProgram_readout {Source : Type} (source : Source)
    (readSource : Source → SignedDyadicCode) (precision : Nat)
    {journal : Journal P baseDepth}
    (executed : ExecutedRequest (negationProgram source readSource precision) P journal ()) :
    executed.readout = (readSource source).neg := by
  rw [executed.readout_is_storedAction]
  change executed.action.code = _
  rw [executed.action.codeExact, executed.action.sourceExact,
    executed.searchResult_is_receivedContextOutput, executed.receivedContext_is_produced]
  rfl

structure NegationProduction (sourceEnvironment : Service P baseDepth)
    (sourceArchive : sourceEnvironment.Archive) (journal : Journal P baseDepth)
    (precision : Nat) where
  private mk ::
  source : Step sourceEnvironment sourceArchive precision
  action : ExecutedRequest (negationProgram source Step.code precision) P journal ()

def produceNegation (source : Service P baseDepth) (archive : source.Archive)
    (journal : Journal P baseDepth) (precision : Nat) :
    NegationProduction source archive journal precision :=
  let step := perform source archive precision
  let action := execute (negationProgram step Step.code precision) P journal ()
  ⟨step, action⟩

def NegationProduction.code {source : Service P baseDepth} {archive : source.Archive}
    {journal : Journal P baseDepth} {p : Nat}
    (production : NegationProduction source archive journal p) : SignedDyadicCode :=
  production.action.memory.stored.action.code

theorem NegationProduction.readoutExact {source : Service P baseDepth} {archive : source.Archive}
    {journal : Journal P baseDepth} {p : Nat}
    (production : NegationProduction source archive journal p) :
    production.code = production.source.code.neg :=
  negationProgram_readout _ _ _ production.action

abbrev RetainedNegation (source : Service P baseDepth) :=
  (archive : source.Archive) × (journal : Journal P baseDepth) × (p : Nat) ×
    NegationProduction source archive journal p

structure NegationArchive (sourceEnvironment : Service P baseDepth) where
  private mk ::
  source : sourceEnvironment.Archive
  journal : Journal P baseDepth
  retained : List (RetainedNegation sourceEnvironment)
  last : Option SignedDyadicCode

/-- Start one negation occurrence from the received source archive.  The
caller cannot prescribe a result or retained history. -/
def seedNegationArchive {source : Service P baseDepth}
    (sourceArchive : source.Archive) : NegationArchive source :=
  ⟨sourceArchive, Journal.root P baseDepth, [], none⟩

structure NegationMemory (source : LiveEnvironment) where
  source : source.Memory
  last : Option SignedDyadicCode

theorem NegationMemory.extensionality {source : LiveEnvironment}
    {first second : NegationMemory source} (sameSource : first.source = second.source)
    (sameLast : first.last = second.last) : first = second := by
  cases first; cases second; cases sameSource; cases sameLast; rfl

structure NegationLiveEvent (source : LiveEnvironment) where
  source : Outcome source.Event source.Read
  code : SignedDyadicCode

theorem NegationLiveEvent.extensionality {source : LiveEnvironment}
    {first second : NegationLiveEvent source} (sameSource : first.source = second.source)
    (sameCode : first.code = second.code) : first = second := by
  cases first; cases second; cases sameSource; cases sameCode; rfl

def NegationArchive.project {source : Service P baseDepth} (archive : NegationArchive source) :
    NegationMemory source.liveEnvironment := ⟨source.project archive.source, archive.last⟩

structure NegationRichEvent (source : Service P baseDepth) where
  archive : NegationArchive source
  precision : Nat
  production : NegationProduction source archive.source archive.journal precision

def negationNext {source : Service P baseDepth} (archive : NegationArchive source) {p : Nat}
    (production : NegationProduction source archive.source archive.journal p) : NegationArchive source :=
  ⟨production.source.next, production.action.completedJournal,
    archive.retained ++ [⟨archive.source, archive.journal, p, production⟩], some production.code⟩

def negationEvent {source : Service P baseDepth} (archive : NegationArchive source) {p : Nat}
    (production : NegationProduction source archive.source archive.journal p) : NegationRichEvent source :=
  ⟨archive, p, production⟩

def NegationRichEvent.project {source : Service P baseDepth} (event : NegationRichEvent source) :
    NegationLiveEvent source.liveEnvironment :=
  ⟨projectOutcome source (sourceFuture event.production.source), event.production.code⟩

def negationLiveStep (source : LiveEnvironment) (memory : NegationMemory source) (p : Nat) :
    LiveStep (NegationMemory source) (NegationLiveEvent source) :=
  let step := source.step memory.source p
  let code := (source.answer step.event).neg
  ⟨⟨step.next, some code⟩, ⟨liveFuture source memory.source p step, code⟩⟩

theorem negationCodeProjection {source : Service P baseDepth} (archive : NegationArchive source) {p : Nat}
    (production : NegationProduction source archive.source archive.journal p) :
    production.code = (negationLiveStep source.liveEnvironment archive.project p).event.code := by
  rw [production.readoutExact, ← production.source.answerProjection, production.source.eventProjection]
  rfl

theorem negationNextProjection {source : Service P baseDepth} (archive : NegationArchive source) {p : Nat}
    (production : NegationProduction source archive.source archive.journal p) :
    (negationNext archive production).project =
      (negationLiveStep source.liveEnvironment archive.project p).next := by
  apply NegationMemory.extensionality
  · exact production.source.nextProjection
  · exact congrArg some (negationCodeProjection archive production)

theorem negationEventProjection {source : Service P baseDepth} (archive : NegationArchive source) {p : Nat}
    (production : NegationProduction source archive.source archive.journal p) :
    (negationEvent archive production).project =
      (negationLiveStep source.liveEnvironment archive.project p).event := by
  apply NegationLiveEvent.extensionality
  · exact sourceFuture_projects production.source
  · exact negationCodeProjection archive production

theorem negationMemorySeparates (source : LiveEnvironment) (first second : NegationMemory source)
    (p : Nat) (readExact : first.last = second.last)
    (eventExact : (negationLiveStep source first p).event = (negationLiveStep source second p).event) :
    first = second := by
  apply NegationMemory.extensionality
  · have same := congrArg NegationLiveEvent.source eventExact
    exact source.separates first.source second.source p
      (congrArg outcomeRead same) (Option.some.inj (congrArg outcomeEvent same))
  · exact readExact

def negEnvironment (source : Service P baseDepth) : Service P baseDepth where
  Archive := NegationArchive source
  Memory := NegationMemory source.liveEnvironment
  Event := NegationLiveEvent source.liveEnvironment
  RichEvent := NegationRichEvent source
  Read := Option SignedDyadicCode
  Resource archive p := NegationProduction source archive.source archive.journal p
  initialArchive := seedNegationArchive source.initialArchive
  execute archive p := produceNegation source archive.source archive.journal p
  next {archive} {p} production := negationNext archive production
  richEvent {archive} {p} production := negationEvent archive production
  code {archive} {p} production := production.code
  readArchive archive := archive.last
  project := NegationArchive.project
  projectEvent := NegationRichEvent.project
  readLive := NegationMemory.last
  liveStep := negationLiveStep source.liveEnvironment
  answer := NegationLiveEvent.code
  nextExact archive p := negationNextProjection archive (produceNegation source archive.source archive.journal p)
  eventExact archive p := negationEventProjection archive (produceNegation source archive.source archive.journal p)
  readExact _ := rfl
  answerExact _ := rfl
  separates := negationMemorySeparates source.liveEnvironment

theorem negationPacketSameTarget {source : Service P baseDepth} {archive : NegationArchive source} {p : Nat}
    (step : Step (negEnvironment source) archive p) :
    step.code = step.resource.action.action.code ∧
      step.next.last = some step.resource.action.action.code ∧
      step.liveEvent.code = step.resource.action.action.code := by
  have exact : step.code = step.resource.action.action.code := step.resource.action.readout_is_storedAction
  exact ⟨exact, congrArg some exact, exact⟩

theorem negationRichEventOwnsProduction {source : Service P baseDepth} {archive : NegationArchive source} {p : Nat}
    (step : Step (negEnvironment source) archive p) :
    step.event.archive = archive ∧ step.event.precision = p ∧ step.event.production = step.resource :=
  ⟨rfl, rfl, rfl⟩

theorem negationRichEventReflectsArchive {source : Service P baseDepth}
    {first second : NegationArchive source} (p : Nat)
    (same : (richContract (negEnvironment source)).event first p =
      (richContract (negEnvironment source)).event second p) : first = second :=
  congrArg NegationRichEvent.archive same

end RelationalPerimeter.Constitution.Reals.RelationalRealNegation

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealNegation.NegationAction
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealNegation.NegationStored
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealNegation.negationProgram
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealNegation.negationProgram_readout
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealNegation.NegationProduction
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealNegation.produceNegation
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealNegation.NegationProduction.code
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealNegation.NegationProduction.readoutExact
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealNegation.RetainedNegation
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealNegation.NegationArchive
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealNegation.seedNegationArchive
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealNegation.NegationMemory
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealNegation.NegationMemory.extensionality
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealNegation.NegationLiveEvent
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealNegation.NegationLiveEvent.extensionality
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealNegation.NegationArchive.project
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealNegation.NegationRichEvent
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealNegation.negationNext
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealNegation.negationEvent
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealNegation.NegationRichEvent.project
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealNegation.negationLiveStep
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealNegation.negationCodeProjection
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealNegation.negationNextProjection
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealNegation.negationEventProjection
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealNegation.negationMemorySeparates
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealNegation.negEnvironment
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealNegation.negationPacketSameTarget
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealNegation.negationRichEventOwnsProduction
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealNegation.negationRichEventReflectsArchive
/- AXIOM_AUDIT_END -/
