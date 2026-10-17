import RelationalPerimeter.Constitution.Reals.HeterogeneousRealRuntime
import RelationalPerimeter.Constitution.Reals.DyadicArithmetic
import RelationalPerimeter.Constitution.Reals.RelationalRealNegation
import RelationalPerimeter.Constitution.Reals.RelationalRealMultiplication
import RelationalPerimeter.Constitution.Reals.EffectiveCauchyReal

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# A closed additive runtime

The executable tree is the environment, not a presentation extracted from it.
A sum produces both child resources at successor precision exactly once, then
executes one six-phase addition program. Its received context owns those same
resources; the action reads them and the store retains the action's one target.
Each operand receives its current native archive and continues the next archive
from that very step. The arithmetic action continues its own current journal;
its actual resource is retained chronologically in the composite archive. The
live contract forgets that journal, by the journal-independent readout proof.
-/

namespace RelationalPerimeter.Constitution.Reals.RelationalRealAddition
open StrongPerimetralTurning
open ConstitutiveRuntime
open RuntimeCorrespondence
open HeterogeneousRealRuntime
open RelationalRealNegation
open RelationalRealMultiplication

variable {P : CircularPresentation} {baseDepth : Nat}

structure AdditionAction {Left Right : Type} (readLeft : Left → SignedDyadicCode)
    (readRight : Right → SignedDyadicCode) (searched : Left × Right) where
  private mk ::
  operands : Left × Right
  operandsExact : operands = searched
  code : SignedDyadicCode
  codeExact : code = (readLeft operands.1).add (readRight operands.2)

structure AdditionStored {Left Right : Type} {readLeft : Left → SignedDyadicCode}
    {readRight : Right → SignedDyadicCode} {searched : Left × Right}
    (acted : AdditionAction readLeft readRight searched) where
  private mk ::
  action : AdditionAction readLeft readRight searched
  actionExact : action = acted

/-- Resources are received before search; the single arithmetic action reads them. -/
def additionProgram {Left Right : Type} (left : Left) (right : Right)
    (readLeft : Left → SignedDyadicCode) (readRight : Right → SignedDyadicCode)
    (precision : Nat) : Program Unit where
  ReceivedContext _ := Left × Right
  SearchResult _ := Left × Right
  ActionResult _ searched := AdditionAction readLeft readRight searched
  Accepted _ searched acted :=
    SameValue acted.code ((readLeft searched.1).add (readRight searched.2))
  Authorization _ _ _ _ := Unit
  Decomposition _ _ _ _ _ := Left × Right
  Continuation _ _ _ _ _ _ := Left × Right
  Stored _ _ acted := AdditionStored acted
  stamp _ := .limit precision
  receive _ := ⟨left, right⟩
  search _ received := received
  act _ searched :=
    ⟨searched, rfl, (readLeft searched.1).add (readRight searched.2), rfl⟩
  preserves _ searched acted := by
    have exact : acted.code = (readLeft searched.1).add (readRight searched.2) := by
      rw [acted.codeExact, acted.operandsExact]
    exact Eq.rec (motive := fun target _ => SameValue acted.code target)
      (SameValue.refl acted.code) exact
  authorize _ _ _ _ := ()
  decompose _ searched _ _ _ := searched
  resume _ _ _ _ _ decomposed := decomposed
  store _ _ acted _ _ _ _ := ⟨acted, rfl⟩
  actionCode acted := acted.code
  read stored := stored.action.code
  readStoredExact stored := congrArg AdditionAction.code stored.actionExact

theorem additionProgram_readout {Left Right : Type} (left : Left) (right : Right)
    (readLeft : Left → SignedDyadicCode) (readRight : Right → SignedDyadicCode)
    (precision : Nat) {journal : Journal P baseDepth}
    (executed : ExecutedRequest (additionProgram left right readLeft readRight precision) P journal ()) :
    executed.readout = (readLeft left).add (readRight right) := by
  rw [executed.readout_is_storedAction]
  change executed.action.code = _
  rw [executed.action.codeExact, executed.action.operandsExact]
  rw [executed.searchResult_is_receivedContextOutput, executed.receivedContext_is_produced]
  rfl

/-- The two current-archive sub-pas are owned before the arithmetic action. -/
structure AdditionProduction (leftEnvironment rightEnvironment : Service P baseDepth)
    (leftArchive : leftEnvironment.Archive) (rightArchive : rightEnvironment.Archive)
    (journal : Journal P baseDepth) (precision : Nat) where
  private mk ::
  left : Step leftEnvironment leftArchive (Nat.succ precision)
  right : Step rightEnvironment rightArchive (Nat.succ precision)
  action : ExecutedRequest
    (additionProgram left right Step.code Step.code precision)
    P journal ()

def produceAddition (left right : Service P baseDepth)
    (leftArchive : left.Archive) (rightArchive : right.Archive) (journal : Journal P baseDepth) (precision : Nat) :
    AdditionProduction left right leftArchive rightArchive journal precision :=
  let first := perform left leftArchive (Nat.succ precision)
  let second := perform right rightArchive (Nat.succ precision)
  let action := execute (additionProgram first second Step.code Step.code precision)
    P journal ()
  ⟨first, second, action⟩

theorem produceAddition_left (left right : Service P baseDepth)
    (leftArchive : left.Archive) (rightArchive : right.Archive) (journal : Journal P baseDepth) (precision : Nat) :
    (produceAddition left right leftArchive rightArchive journal precision).left =
      perform left leftArchive (Nat.succ precision) := rfl

theorem produceAddition_right (left right : Service P baseDepth)
    (leftArchive : left.Archive) (rightArchive : right.Archive) (journal : Journal P baseDepth) (precision : Nat) :
    (produceAddition left right leftArchive rightArchive journal precision).right =
      perform right rightArchive (Nat.succ precision) := rfl

def AdditionProduction.code {left right : Service P baseDepth}
    {leftArchive : left.Archive} {rightArchive : right.Archive} {journal : Journal P baseDepth} {precision : Nat}
    (production : AdditionProduction left right leftArchive rightArchive journal precision) : SignedDyadicCode :=
  production.action.memory.stored.action.code

theorem AdditionProduction.readoutExact {left right : Service P baseDepth}
    {leftArchive : left.Archive} {rightArchive : right.Archive} {journal : Journal P baseDepth} {precision : Nat}
    (production : AdditionProduction left right leftArchive rightArchive journal precision) :
    production.code = production.left.code.add production.right.code :=
  additionProgram_readout _ _ _ _ _ production.action

abbrev RetainedAddition (left right : Service P baseDepth) :=
  (leftArchive : left.Archive) × (rightArchive : right.Archive) ×
    (journal : Journal P baseDepth) × (precision : Nat) × AdditionProduction left right leftArchive rightArchive journal precision

structure AdditionArchive (leftEnvironment rightEnvironment : Service P baseDepth) where
  private mk ::
  left : leftEnvironment.Archive
  right : rightEnvironment.Archive
  journal : Journal P baseDepth
  retained : List (RetainedAddition leftEnvironment rightEnvironment)
  last : Option SignedDyadicCode

/-- Start one composite addition occurrence from the two received child
archives.  No composite event, result, or retained history can be supplied by
the caller. -/
def seedAdditionArchive {left right : Service P baseDepth}
    (leftArchive : left.Archive) (rightArchive : right.Archive) :
    AdditionArchive left right :=
  ⟨leftArchive, rightArchive, Journal.root P baseDepth, [], none⟩

def AdditionArchive.project {left right : Service P baseDepth}
    (archive : AdditionArchive left right) : CompositeMemory left.liveEnvironment right.liveEnvironment :=
  ⟨left.project archive.left, right.project archive.right, archive.last⟩

/-- A rich addition event owns its complete incoming archive and exact production. -/
structure AdditionRichEvent (left right : Service P baseDepth) where
  archive : AdditionArchive left right
  precision : Nat
  production : AdditionProduction left right archive.left archive.right archive.journal precision

def additionNext {left right : Service P baseDepth} (archive : AdditionArchive left right) {p : Nat}
    (production : AdditionProduction left right archive.left archive.right archive.journal p) : AdditionArchive left right :=
  ⟨production.left.next, production.right.next, production.action.completedJournal,
    archive.retained ++ [⟨archive.left, archive.right, archive.journal, p, production⟩], some production.code⟩

def additionEvent {left right : Service P baseDepth} (archive : AdditionArchive left right) {p : Nat}
    (production : AdditionProduction left right archive.left archive.right archive.journal p) :
    AdditionRichEvent left right := ⟨archive, p, production⟩

def AdditionRichEvent.project {left right : Service P baseDepth} (event : AdditionRichEvent left right) :
    CompositeLiveEvent left.liveEnvironment right.liveEnvironment :=
  ⟨projectOutcome left (sourceFuture event.production.left),
    projectOutcome right (sourceFuture event.production.right), event.production.code⟩

/-- Executable live specification; the authoritative producer never calls it beside its own run. -/
def additionLiveStep (left right : LiveEnvironment) (memory : CompositeMemory left right) (p : Nat) :
    LiveStep (CompositeMemory left right) (CompositeLiveEvent left right) :=
  let first := left.step memory.left (Nat.succ p)
  let second := right.step memory.right (Nat.succ p)
  let code := (left.answer first.event).add (right.answer second.event)
  ⟨⟨first.next, second.next, some code⟩,
    ⟨liveFuture left memory.left (Nat.succ p) first,
      liveFuture right memory.right (Nat.succ p) second, code⟩⟩

theorem additionCodeProjection {left right : Service P baseDepth} (archive : AdditionArchive left right) {p : Nat}
    (production : AdditionProduction left right archive.left archive.right archive.journal p) :
    production.code =
      (additionLiveStep left.liveEnvironment right.liveEnvironment archive.project p).event.code := by
  rw [production.readoutExact, ← production.left.answerProjection, ← production.right.answerProjection,
    production.left.eventProjection, production.right.eventProjection]
  rfl

theorem additionNextProjection {left right : Service P baseDepth} (archive : AdditionArchive left right) {p : Nat}
    (production : AdditionProduction left right archive.left archive.right archive.journal p) :
    (additionNext archive production).project =
      (additionLiveStep left.liveEnvironment right.liveEnvironment archive.project p).next := by
  apply CompositeMemory.extensionality
  · exact production.left.nextProjection
  · exact production.right.nextProjection
  · exact congrArg some (additionCodeProjection archive production)

theorem additionEventProjection {left right : Service P baseDepth} (archive : AdditionArchive left right) {p : Nat}
    (production : AdditionProduction left right archive.left archive.right archive.journal p) :
    (additionEvent archive production).project =
      (additionLiveStep left.liveEnvironment right.liveEnvironment archive.project p).event := by
  apply CompositeLiveEvent.extensionality
  · exact sourceFuture_projects production.left
  · exact sourceFuture_projects production.right
  · exact additionCodeProjection archive production

theorem additionMemorySeparates (left right : LiveEnvironment)
    (first second : CompositeMemory left right) (p : Nat) (readExact : first.last = second.last)
    (eventExact : (additionLiveStep left right first p).event = (additionLiveStep left right second p).event) :
    first = second :=
  compositeMemorySeparates p readExact
    (congrArg CompositeLiveEvent.left eventExact) (congrArg CompositeLiveEvent.right eventExact)

def addEnvironment (left right : Service P baseDepth) : Service P baseDepth where
  Archive := AdditionArchive left right
  Memory := CompositeMemory left.liveEnvironment right.liveEnvironment
  Event := CompositeLiveEvent left.liveEnvironment right.liveEnvironment
  RichEvent := AdditionRichEvent left right
  Read := Option SignedDyadicCode
  Resource archive p := AdditionProduction left right archive.left archive.right archive.journal p
  initialArchive := seedAdditionArchive left.initialArchive right.initialArchive
  execute archive p := produceAddition left right archive.left archive.right archive.journal p
  next {archive} {p} production := additionNext archive production
  richEvent {archive} {p} production := additionEvent archive production
  code {archive} {p} production := production.code
  readArchive archive := archive.last
  project := AdditionArchive.project
  projectEvent := AdditionRichEvent.project
  readLive := CompositeMemory.last
  liveStep := additionLiveStep left.liveEnvironment right.liveEnvironment
  answer := CompositeLiveEvent.code
  nextExact archive p := additionNextProjection archive (produceAddition left right archive.left archive.right archive.journal p)
  eventExact archive p := additionEventProjection archive (produceAddition left right archive.left archive.right archive.journal p)
  readExact _ := rfl
  answerExact _ := rfl
  separates := additionMemorySeparates left.liveEnvironment right.liveEnvironment

/-- Code, installed target and event read the same retained action; no new run occurs. -/
theorem additionPacketSameTarget {left right : Service P baseDepth} {archive : AdditionArchive left right} {precision : Nat}
    (step : Step (addEnvironment left right) archive precision) :
    step.code = step.resource.action.action.code ∧
      step.next.last = some step.resource.action.action.code ∧
      step.liveEvent.code = step.resource.action.action.code := by
  have exact : step.code = step.resource.action.action.code :=
    step.resource.action.readout_is_storedAction
  exact ⟨exact, congrArg some exact, exact⟩

/-- The rich event owns this exact archive, precision and produced packet. -/
theorem additionRichEventOwnsProduction {left right : Service P baseDepth}
    {archive : AdditionArchive left right} {precision : Nat}
    (step : Step (addEnvironment left right) archive precision) :
    step.event.archive = archive ∧ step.event.precision = precision ∧
      step.event.production = step.resource := ⟨rfl, rfl, rfl⟩

/-- One rich event still determines its exact incoming archive; this is deliberately false of its live projection. -/
theorem additionRichEventReflectsArchive {left right : Service P baseDepth}
    {first second : AdditionArchive left right} (precision : Nat)
    (same : (richContract (addEnvironment left right)).event first precision =
      (richContract (addEnvironment left right)).event second precision) : first = second := by
  exact congrArg AdditionRichEvent.archive same

/-- Coherence compares the actual retained replies at arbitrary current archives. -/
structure Coherent (service : Service P baseDepth) where
  near : {firstArchive secondArchive : service.Archive} → (coarse first second : Nat) →
    (firstStep : Step service firstArchive first) → (secondStep : Step service secondArchive second) →
    PrecisionExtension coarse first → PrecisionExtension coarse second →
    Near coarse firstStep.code secondStep.code

/-- An externally supplied certificate is a received relational input, not an
endogenous construction. Concrete extensions must derive these two laws from
their actual producer, including the current-archive Steps it owns. -/
structure CertifiedService (P : CircularPresentation) (baseDepth : Nat) where
  service : Service P baseDepth
  coherence : Coherent service
  uniform : (archive : service.Archive) → (p : Nat) → (step : Step service archive p) →
    step.code = (canonicalStep service p).code

/-- A common closed carrier. Nested sums are executable operands themselves.
The explicit Type 1 sort is required to own a heterogeneous Service, whose
archive/memory/event types are data. The previous four constructors remain. -/
inductive Real (P : CircularPresentation) (baseDepth : Nat) : Type 1 where
  | leaf (real : RuntimeReal P baseDepth)
  | add (left right : Real P baseDepth)
  | neg (source : Real P baseDepth)
  | mul (left right : Real P baseDepth)
  | certified (certificate : CertifiedService P baseDepth)

def environment : Real P baseDepth → Service P baseDepth
  | .leaf real => HeterogeneousRealRuntime.leaf real
  | .add left right => addEnvironment (environment left) (environment right)
  | .neg source => negEnvironment (environment source)
  | .mul left right => mulEnvironment (environment left) (environment right)
  | .certified certificate => certificate.service

def zero (P : CircularPresentation) (baseDepth : Nat) : Real P baseDepth :=
  .leaf (constantRuntime P baseDepth SignedDyadicCode.zero)
def one (P : CircularPresentation) (baseDepth : Nat) : Real P baseDepth :=
  .leaf (constantRuntime P baseDepth SignedDyadicCode.one)

def executeAt (real : Real P baseDepth) (archive : (environment real).Archive) (precision : Nat) :
    Step (environment real) archive precision := perform (environment real) archive precision

def executeReal (real : Real P baseDepth) (precision : Nat) :
    Step (environment real) (environment real).initialArchive precision := canonicalStep (environment real) precision

def initialReal (real : Real P baseDepth) : HeterogeneousRealRuntime.ArchivedExecution P baseDepth :=
  initialArchiveExecution (environment real)

/-- This is a read of the produced/installed packet, defined after its execution. -/
def readout (real : Real P baseDepth) (precision : Nat) : SignedDyadicCode :=
  (executeReal real precision).code

theorem add_readout_exact (left right : Real P baseDepth) (precision : Nat) :
    readout (.add left right) precision =
      (readout left (Nat.succ precision)).add (readout right (Nat.succ precision)) :=
  AdditionProduction.readoutExact (produceAddition (environment left) (environment right)
    (environment left).initialArchive (environment right).initialArchive (Journal.root P baseDepth) precision)

def add_readout (left right : Real P baseDepth) (precision : Nat) :
    SameValue (readout (.add left right) precision)
      ((readout left (Nat.succ precision)).add (readout right (Nat.succ precision))) := by
  rw [add_readout_exact]
  exact SameValue.refl _

theorem neg_readout_exact (source : Real P baseDepth) (precision : Nat) :
    readout (.neg source) precision = (readout source precision).neg :=
  NegationProduction.readoutExact (produceNegation (environment source)
    (environment source).initialArchive (Journal.root P baseDepth) precision)

def neg_readout (source : Real P baseDepth) (precision : Nat) :
    SameValue (readout (.neg source) precision) (readout source precision).neg := by
  rw [neg_readout_exact]
  exact SameValue.refl _

theorem currentReadout : (real : Real P baseDepth) → (archive : (environment real).Archive) → (p : Nat) →
    (step : Step (environment real) archive p) → step.code = readout real p
  | .leaf real, archive, p, step => leafCurrentReadout real archive p step
  | .add left right, archive, p, step => by
      dsimp only [environment, addEnvironment] at archive step
      change step.resource.code = readout (.add left right) p
      rw [AdditionProduction.readoutExact, add_readout_exact,
        currentReadout left archive.left (Nat.succ p) step.resource.left,
        currentReadout right archive.right (Nat.succ p) step.resource.right]
  | .neg source, archive, p, step => by
      dsimp only [environment, negEnvironment] at archive step
      change step.resource.code = readout (.neg source) p
      rw [NegationProduction.readoutExact, neg_readout_exact,
        currentReadout source archive.source p step.resource.source]
  | .mul left right, archive, p, step => by
      dsimp only [environment, mulEnvironment] at archive step
      let canonical := produceMultiplication (environment left) (environment right)
        (environment left).initialArchive (environment right).initialArchive (Journal.root P baseDepth) p
      change step.resource.code = canonical.code
      rw [MultiplicationProduction.readoutExact, MultiplicationProduction.readoutExact,
        currentReadout left _ _ step.resource.left, currentReadout right _ _ step.resource.right,
        currentReadout left _ _ canonical.left, currentReadout right _ _ canonical.right,
        currentReadout left _ _ step.resource.leftProbe, currentReadout right _ _ step.resource.rightProbe]
      rfl

  | .certified certificate, archive, p, step => certificate.uniform archive p step

theorem mul_readout_exact (left right : Real P baseDepth) (p : Nat) :
    readout (.mul left right) p =
      (readout left (p + 1 + probeAmplitude (readout right 0))).mul
        (readout right (p + 1 + probeAmplitude (readout left 0))) := by
  let production := produceMultiplication (environment left) (environment right)
    (environment left).initialArchive (environment right).initialArchive (Journal.root P baseDepth) p
  change production.code = _
  rw [MultiplicationProduction.readoutExact, currentReadout left _ _ production.left,
    currentReadout right _ _ production.right]
  rfl

def leafCoherent (real : RuntimeReal P baseDepth) : Coherent (HeterogeneousRealRuntime.leaf real) where
  near := by
    intro firstArchive secondArchive coarse first second firstStep secondStep firstBeyond secondBeyond
    dsimp only [HeterogeneousRealRuntime.leaf] at firstArchive secondArchive firstStep secondStep
    let left := firstStep.resource.response.limitProduction
    let right := secondStep.resource.response.limitProduction
    have responseReadout (state : AuthoritativeRuntime.Runtime real.family) (precision : Nat)
        (response : AuthoritativeRuntime.ExecutedResponse real.family state (.limit precision)) :
        response.readout = response.limitProduction.readout := by
      rcases response with ⟨resource⟩
      cases resource
      rfl
    change Near coarse firstStep.resource.response.readout secondStep.resource.response.readout
    rw [responseReadout, responseReadout]
    change Near coarse left.readout right.readout
    rw [left.readout_is_source, right.readout_is_source]
    exact real.family.cauchy coarse left.sourceAt.request right.sourceAt.request
      (by rw [left.sourceAtExact]; exact real.family.modulusMonotone firstBeyond)
      (by rw [right.sourceAtExact]; exact real.family.modulusMonotone secondBeyond)
      (by rw [left.sourceAtExact]; exact firstBeyond)
      (by rw [right.sourceAtExact]; exact secondBeyond)
      left.source.execution right.source.execution

def additionCoherent {left right : Service P baseDepth} (leftCoherent : Coherent left) (rightCoherent : Coherent right) :
    Coherent (addEnvironment left right) where
  near := by
    intro firstArchive secondArchive coarse first second firstStep secondStep firstBeyond secondBeyond
    dsimp only [addEnvironment] at firstArchive secondArchive firstStep secondStep
    change Near coarse firstStep.resource.code secondStep.resource.code
    rw [AdditionProduction.readoutExact, AdditionProduction.readoutExact]
    exact Near.add
      (leftCoherent.near (Nat.succ coarse) (Nat.succ first) (Nat.succ second)
        firstStep.resource.left secondStep.resource.left firstBeyond.succ secondBeyond.succ)
      (rightCoherent.near (Nat.succ coarse) (Nat.succ first) (Nat.succ second)
        firstStep.resource.right secondStep.resource.right firstBeyond.succ secondBeyond.succ)

def multiplicationCoherent (left right : Real P baseDepth)
    (lc : Coherent (environment left)) (rc : Coherent (environment right)) :
    Coherent (mulEnvironment (environment left) (environment right)) where
  near := by
    intro fa sa coarse first second fs ss fb sb
    dsimp only [mulEnvironment] at fa sa fs ss
    let x := fs.resource
    let y := ss.resource
    have lp : x.leftProbe.code = y.leftProbe.code :=
      (currentReadout left _ _ x.leftProbe).trans (currentReadout left _ _ y.leftProbe).symm
    have rp : x.rightProbe.code = y.rightProbe.code :=
      (currentReadout right _ _ x.rightProbe).trans (currentReadout right _ _ y.rightProbe).symm
    have lext : PrecisionExtension (coarse + 1 + probeAmplitude x.rightProbe.code)
        (productBudget y.leftProbe.code y.rightProbe.code second).leftPrecision := by
      change PrecisionExtension _ (second + 1 + probeAmplitude y.rightProbe.code)
      rw [← rp]
      exact sb.succ.add (PrecisionExtension.refl _)
    have rext : PrecisionExtension (coarse + 1 + probeAmplitude x.leftProbe.code)
        (productBudget y.leftProbe.code y.rightProbe.code second).rightPrecision := by
      change PrecisionExtension _ (second + 1 + probeAmplitude y.leftProbe.code)
      rw [← lp]
      exact sb.succ.add (PrecisionExtension.refl _)
    change Near coarse x.code y.code
    rw [MultiplicationProduction.readoutExact, MultiplicationProduction.readoutExact]
    exact Near.mul
      (lc.near _ _ _ x.left y.left (fb.succ.add (PrecisionExtension.refl _)) lext)
      (rc.near _ _ _ x.right y.right (fb.succ.add (PrecisionExtension.refl _)) rext)
      (Amplitude.fromProbe (rc.near 0 _ 0 x.right x.rightProbe ⟨_, Nat.zero_add _⟩ (PrecisionExtension.refl 0)))
      (Amplitude.fromProbe (lc.near 0 _ 0 y.left x.leftProbe ⟨_, Nat.zero_add _⟩ (PrecisionExtension.refl 0)))

def coherent : (real : Real P baseDepth) → Coherent (environment real)
  | .certified certificate => certificate.coherence
  | .leaf real => leafCoherent real
  | .add left right => additionCoherent (coherent left) (coherent right)
  | .mul left right => multiplicationCoherent left right (coherent left) (coherent right)
  | .neg source => {
      near := by
        intro firstArchive secondArchive coarse first second firstStep secondStep firstBeyond secondBeyond
        dsimp only [environment, negEnvironment] at firstArchive secondArchive firstStep secondStep
        change Near coarse firstStep.resource.code secondStep.resource.code
        rw [NegationProduction.readoutExact, NegationProduction.readoutExact]
        exact ((coherent source).near coarse first second
          firstStep.resource.source secondStep.resource.source firstBeyond secondBeyond).neg }

def readoutsNear (real : Real P baseDepth) (coarse first second : Nat)
    (firstBeyond : PrecisionExtension coarse first) (secondBeyond : PrecisionExtension coarse second) :
    Near coarse (readout real first) (readout real second) :=
  (coherent real).near coarse first second (executeReal real first) (executeReal real second) firstBeyond secondBeyond

/-- Positive numerical equivalence; no equality of trees, occurrences or resources. -/
structure Equivalent (first second : Real P baseDepth) where
  threshold : Nat → Nat
  near : (precision leftResponse rightResponse : Nat) →
    PrecisionExtension (threshold precision) leftResponse →
    PrecisionExtension (threshold precision) rightResponse →
    Near precision (readout first leftResponse) (readout second rightResponse)

def Equivalent.refl (real : Real P baseDepth) : Equivalent real real where
  threshold := fun precision => precision
  near := readoutsNear real

def Equivalent.symm {first second : Real P baseDepth} (same : Equivalent first second) :
    Equivalent second first where
  threshold := same.threshold
  near := fun p l r hl hr => (same.near p r l hr hl).symm

def Equivalent.trans {first middle last : Real P baseDepth}
    (left : Equivalent first middle) (right : Equivalent middle last) : Equivalent first last where
  threshold := fun p => left.threshold (Nat.succ p) + right.threshold (Nat.succ p)
  near := by
    intro p l r hl hr
    let a := left.threshold (Nat.succ p)
    let b := right.threshold (Nat.succ p)
    exact Near.compose
      (left.near (Nat.succ p) l (a + b) ((PrecisionExtension.first a b).trans hl)
        (PrecisionExtension.first a b))
      (right.near (Nat.succ p) (a + b) r (PrecisionExtension.second a b)
        ((PrecisionExtension.second a b).trans hr))

def Equivalent.ofExact {first second : Real P baseDepth}
    (same : (p : Nat) → SameValue (readout first p) (readout second p)) : Equivalent first second where
  threshold := fun p => p
  near := fun p l r hl hr => Near.ofSameLeft (same l) (readoutsNear second p l r hl hr)

/-- Each node owns the exact two produced transition packets and continues their next memories. -/
inductive NumericalTrace (first second : Real P baseDepth) (threshold : Nat → Nat) :
    (environment first).Archive → (environment second).Archive → List (LimitQuery threshold) → Type
  | done (firstArchive : (environment first).Archive) (secondArchive : (environment second).Archive) :
      NumericalTrace first second threshold firstArchive secondArchive []
  | step {firstArchive : (environment first).Archive} {secondArchive : (environment second).Archive}
      {query : LimitQuery threshold}
      {remaining : List (LimitQuery threshold)}
      (firstStep : Step (environment first) firstArchive query.leftResponse)
      (secondStep : Step (environment second) secondArchive query.rightResponse)
      (firstExact : firstStep = executeAt first firstArchive query.leftResponse)
      (secondExact : secondStep = executeAt second secondArchive query.rightResponse)
      (near : Near query.accuracy firstStep.code secondStep.code)
      (later : NumericalTrace first second threshold firstStep.next secondStep.next remaining) :
      NumericalTrace first second threshold firstArchive secondArchive (query :: remaining)

/--
All finite precision-query traces, paired beyond the numerical threshold,
from arbitrary current archives.  This compares the produced answers by Near;
it does not equate rich events, live events, reads, archives or environments,
and is not FutureEquivalent for any of the three exact-memory contracts.
-/
structure NumericalFutureEquivalent (first second : Real P baseDepth) where
  threshold : Nat → Nat
  traces : (firstArchive : (environment first).Archive) → (secondArchive : (environment second).Archive) →
    (queries : List (LimitQuery threshold)) → NumericalTrace first second threshold firstArchive secondArchive queries

def pairTraces {first second : Real P baseDepth} (same : Equivalent first second) :
    (firstArchive : (environment first).Archive) → (secondArchive : (environment second).Archive) →
    (queries : List (LimitQuery same.threshold)) → NumericalTrace first second same.threshold firstArchive secondArchive queries
  | firstArchive, secondArchive, [] => .done firstArchive secondArchive
  | firstArchive, secondArchive, query :: remaining =>
      let firstStep := executeAt first firstArchive query.leftResponse
      let secondStep := executeAt second secondArchive query.rightResponse
      .step firstStep secondStep rfl rfl
        (by
          rw [currentReadout first firstArchive query.leftResponse firstStep,
            currentReadout second secondArchive query.rightResponse secondStep]
          exact same.near query.accuracy query.leftResponse query.rightResponse query.leftBeyond query.rightBeyond)
        (pairTraces same firstStep.next secondStep.next remaining)

def Equivalent.toFutures {first second : Real P baseDepth} (same : Equivalent first second) :
    NumericalFutureEquivalent first second := ⟨same.threshold, pairTraces same⟩

def NumericalFutureEquivalent.toEquivalent {first second : Real P baseDepth}
    (same : NumericalFutureEquivalent first second) : Equivalent first second where
  threshold := same.threshold
  near := by
    intro p l r hl hr
    have paired := same.traces (environment first).initialArchive (environment second).initialArchive [⟨p, l, r, hl, hr⟩]
    cases paired with
    | step firstStep secondStep firstExact secondExact near later =>
        rw [firstExact, secondExact] at near
        exact near

def numericalFutureCorrespondence (first second : Real P baseDepth) :
    (Equivalent first second → NumericalFutureEquivalent first second) ×
    (NumericalFutureEquivalent first second → Equivalent first second) :=
  ⟨Equivalent.toFutures, NumericalFutureEquivalent.toEquivalent⟩

def add_congr {a b c d : Real P baseDepth} (first : Equivalent a c) (second : Equivalent b d) :
    Equivalent (.add a b) (.add c d) where
  threshold := fun p => first.threshold (Nat.succ p) + second.threshold (Nat.succ p)
  near := by
    intro p l r hl hr
    rw [add_readout_exact, add_readout_exact]
    let x := first.threshold (Nat.succ p)
    let y := second.threshold (Nat.succ p)
    exact Near.add
      (first.near (Nat.succ p) (Nat.succ l) (Nat.succ r)
        (((PrecisionExtension.first x y).trans hl).trans (PrecisionExtension.next l))
        (((PrecisionExtension.first x y).trans hr).trans (PrecisionExtension.next r)))
      (second.near (Nat.succ p) (Nat.succ l) (Nat.succ r)
        (((PrecisionExtension.second x y).trans hl).trans (PrecisionExtension.next l))
        (((PrecisionExtension.second x y).trans hr).trans (PrecisionExtension.next r)))

def constant_readout (code : SignedDyadicCode) (p : Nat) :
    SameValue (readout (.leaf (constantRuntime P baseDepth code)) p) code :=
  constantRuntimeReadoutSameValue P baseDepth code
    ((constantRuntime P baseDepth code).stepAt p)

def zero_add (real : Real P baseDepth) : Equivalent (.add (zero P baseDepth) real) real where
  threshold := fun p => p
  near := by
    intro p l r hl hr
    rw [add_readout_exact]
    exact Near.ofSameLeft
      ((SameValue.add (constant_readout SignedDyadicCode.zero (Nat.succ l)) (SameValue.refl _)).trans
        (SignedDyadicCode.zero_add _))
      (readoutsNear real p (Nat.succ l) r (hl.trans (PrecisionExtension.next l)) hr)

def add_zero (real : Real P baseDepth) : Equivalent (.add real (zero P baseDepth)) real where
  threshold := fun p => p
  near := by
    intro p l r hl hr
    rw [add_readout_exact]
    exact Near.ofSameLeft
      ((SameValue.add (SameValue.refl _) (constant_readout SignedDyadicCode.zero (Nat.succ l))).trans
        (SignedDyadicCode.add_zero _))
      (readoutsNear real p (Nat.succ l) r (hl.trans (PrecisionExtension.next l)) hr)

def add_comm (left right : Real P baseDepth) : Equivalent (.add left right) (.add right left) where
  threshold := fun p => p
  near := by
    intro p l r hl hr
    rw [add_readout_exact, add_readout_exact]
    exact Near.ofSameRight
      (Near.add (readoutsNear left (Nat.succ p) (Nat.succ l) (Nat.succ r) hl.succ hr.succ)
        (readoutsNear right (Nat.succ p) (Nat.succ l) (Nat.succ r) hl.succ hr.succ))
      (SignedDyadicCode.add_comm _ _)

def add_assoc (a b c : Real P baseDepth) : Equivalent (.add (.add a b) c) (.add a (.add b c)) where
  threshold := fun p => Nat.succ (Nat.succ p)
  near := by
    intro p l r hl hr
    rw [add_readout_exact, add_readout_exact, add_readout_exact, add_readout_exact]
    let firstExtra := (PrecisionExtension.next l).trans (PrecisionExtension.next (Nat.succ l))
    let secondExtra := (PrecisionExtension.next r).trans (PrecisionExtension.next (Nat.succ r))
    have firstNear := readoutsNear a (Nat.succ (Nat.succ p))
      (Nat.succ (Nat.succ l)) (Nat.succ r) (hl.trans firstExtra) (hr.trans (PrecisionExtension.next r))
    have middleNear := readoutsNear b (Nat.succ (Nat.succ p))
      (Nat.succ (Nat.succ l)) (Nat.succ (Nat.succ r)) (hl.trans firstExtra) (hr.trans secondExtra)
    have lastNear := readoutsNear c (Nat.succ p) (Nat.succ l) (Nat.succ (Nat.succ r))
      (((PrecisionExtension.next (Nat.succ p)).trans hl).trans (PrecisionExtension.next l))
      (((PrecisionExtension.next (Nat.succ p)).trans hr).trans secondExtra)
    exact Near.ofSameRight (Near.add (Near.add firstNear middleNear) lastNear)
      (SignedDyadicCode.add_assoc _ _ _)

/-- A concrete package of the additive laws, all at numerical behavioral equivalence. -/
structure AdditiveLaws (P : CircularPresentation) (baseDepth : Nat) where
  zeroLeft : (x : Real P baseDepth) → Equivalent (.add (zero P baseDepth) x) x
  zeroRight : (x : Real P baseDepth) → Equivalent (.add x (zero P baseDepth)) x
  commutative : (x y : Real P baseDepth) → Equivalent (.add x y) (.add y x)
  associative : (x y z : Real P baseDepth) → Equivalent (.add (.add x y) z) (.add x (.add y z))
  congruent : {a b c d : Real P baseDepth} → Equivalent a c → Equivalent b d → Equivalent (.add a b) (.add c d)

def additiveLaws (P : CircularPresentation) (baseDepth : Nat) : AdditiveLaws P baseDepth :=
  ⟨zero_add, add_zero, add_comm, add_assoc, add_congr⟩

structure AdditiveFutureLaws (P : CircularPresentation) (baseDepth : Nat) where
  zeroLeft : (x : Real P baseDepth) → NumericalFutureEquivalent (.add (zero P baseDepth) x) x
  zeroRight : (x : Real P baseDepth) → NumericalFutureEquivalent (.add x (zero P baseDepth)) x
  commutative : (x y : Real P baseDepth) → NumericalFutureEquivalent (.add x y) (.add y x)
  associative : (x y z : Real P baseDepth) →
    NumericalFutureEquivalent (.add (.add x y) z) (.add x (.add y z))
  congruent : {a b c d : Real P baseDepth} → NumericalFutureEquivalent a c → NumericalFutureEquivalent b d →
    NumericalFutureEquivalent (.add a b) (.add c d)

def additiveFutureLaws (P : CircularPresentation) (baseDepth : Nat) : AdditiveFutureLaws P baseDepth :=
  ⟨fun x => (zero_add x).toFutures, fun x => (add_zero x).toFutures,
    fun x y => (add_comm x y).toFutures, fun x y z => (add_assoc x y z).toFutures,
    fun first second => (add_congr first.toEquivalent second.toEquivalent).toFutures⟩

def neg_congr {first second : Real P baseDepth} (same : Equivalent first second) :
    Equivalent (.neg first) (.neg second) where
  threshold := same.threshold
  near := by
    intro p l r hl hr
    rw [neg_readout_exact, neg_readout_exact]
    exact (same.near p l r hl hr).neg

def neg_neg (real : Real P baseDepth) : Equivalent (.neg (.neg real)) real :=
  Equivalent.ofExact (fun p => by
    rw [neg_readout_exact, neg_readout_exact, SignedDyadicCode.neg_neg_exact]
    exact SameValue.refl _)

def add_neg (real : Real P baseDepth) : Equivalent (.add real (.neg real)) (zero P baseDepth) :=
  Equivalent.ofExact (fun p => by
    rw [add_readout_exact, neg_readout_exact]
    exact (SignedDyadicCode.add_neg _).trans (constant_readout SignedDyadicCode.zero p).symm)

def neg_add (real : Real P baseDepth) : Equivalent (.add (.neg real) real) (zero P baseDepth) :=
  Equivalent.ofExact (fun p => by
    rw [add_readout_exact, neg_readout_exact]
    exact (SignedDyadicCode.neg_add _).trans (constant_readout SignedDyadicCode.zero p).symm)

def neg_sum (left right : Real P baseDepth) :
    Equivalent (.neg (.add left right)) (.add (.neg left) (.neg right)) :=
  Equivalent.ofExact (fun p => by
    rw [neg_readout_exact, add_readout_exact, add_readout_exact,
      neg_readout_exact, neg_readout_exact, SignedDyadicCode.neg_add_exact]
    exact SameValue.refl _)

/-- Group laws concern numerical equivalence, never equality of rich trees. -/
structure AdditiveGroupLaws (P : CircularPresentation) (baseDepth : Nat) where
  additive : AdditiveLaws P baseDepth
  negCongruent : {x y : Real P baseDepth} → Equivalent x y → Equivalent (.neg x) (.neg y)
  involutive : (x : Real P baseDepth) → Equivalent (.neg (.neg x)) x
  inverseRight : (x : Real P baseDepth) → Equivalent (.add x (.neg x)) (zero P baseDepth)
  inverseLeft : (x : Real P baseDepth) → Equivalent (.add (.neg x) x) (zero P baseDepth)
  negSum : (x y : Real P baseDepth) → Equivalent (.neg (.add x y)) (.add (.neg x) (.neg y))

def additiveGroupLaws (P : CircularPresentation) (baseDepth : Nat) : AdditiveGroupLaws P baseDepth :=
  ⟨additiveLaws P baseDepth, neg_congr, neg_neg, add_neg, neg_add, neg_sum⟩

structure AdditiveGroupFutureLaws (P : CircularPresentation) (baseDepth : Nat) where
  additive : AdditiveFutureLaws P baseDepth
  negCongruent : {x y : Real P baseDepth} → NumericalFutureEquivalent x y →
    NumericalFutureEquivalent (.neg x) (.neg y)
  involutive : (x : Real P baseDepth) → NumericalFutureEquivalent (.neg (.neg x)) x
  inverseRight : (x : Real P baseDepth) → NumericalFutureEquivalent (.add x (.neg x)) (zero P baseDepth)
  inverseLeft : (x : Real P baseDepth) → NumericalFutureEquivalent (.add (.neg x) x) (zero P baseDepth)
  negSum : (x y : Real P baseDepth) → NumericalFutureEquivalent (.neg (.add x y)) (.add (.neg x) (.neg y))

def additiveGroupFutureLaws (P : CircularPresentation) (baseDepth : Nat) : AdditiveGroupFutureLaws P baseDepth :=
  ⟨additiveFutureLaws P baseDepth, fun same => (neg_congr same.toEquivalent).toFutures,
    fun x => (neg_neg x).toFutures, fun x => (add_neg x).toFutures,
    fun x => (neg_add x).toFutures, fun x y => (neg_sum x y).toFutures⟩

/-! Numerical presentations and carriers appear only downstream of the runtime. -/

def toPresentation (real : Real P baseDepth) : EffectiveDyadicPresentation :=
  ⟨readout real, readoutsNear real⟩

def addPresentation (left right : EffectiveDyadicPresentation) : EffectiveDyadicPresentation where
  approximation p := (left.approximation (Nat.succ p)).add (right.approximation (Nat.succ p))
  coherent := fun p l r hl hr => Near.add
    (left.coherent (Nat.succ p) (Nat.succ l) (Nat.succ r) hl.succ hr.succ)
    (right.coherent (Nat.succ p) (Nat.succ l) (Nat.succ r) hl.succ hr.succ)

def toPresentation_add (left right : Real P baseDepth) :
    EffectiveDyadicPresentation.Equivalent (toPresentation (.add left right))
      (addPresentation (toPresentation left) (toPresentation right)) where
  responseThreshold := fun p => p
  near := by
    intro p l r hl hr
    change Near p (readout (.add left right) l) _
    rw [add_readout_exact]
    exact (addPresentation (toPresentation left) (toPresentation right)).coherent p l r hl hr

def equivalentPresentation (first second : Real P baseDepth) :
    (Equivalent first second → EffectiveDyadicPresentation.Equivalent (toPresentation first) (toPresentation second)) ×
    (EffectiveDyadicPresentation.Equivalent (toPresentation first) (toPresentation second) → Equivalent first second) :=
  ⟨fun same => ⟨same.threshold, same.near⟩, fun same => ⟨same.responseThreshold, same.near⟩⟩

def ofPresentation (P : CircularPresentation) (baseDepth : Nat) (presentation : EffectiveDyadicPresentation) :
    Real P baseDepth := .leaf (presentationToRuntime P baseDepth presentation)

theorem ofPresentation_readout (presentation : EffectiveDyadicPresentation) (p : Nat) :
    readout (ofPresentation P baseDepth presentation) p = presentation.approximation p :=
  presentation_roundtrip_readout_exact P baseDepth p presentation

def real_roundtrip (real : Real P baseDepth) : Equivalent (ofPresentation P baseDepth (toPresentation real)) real :=
  Equivalent.ofExact (fun p => by rw [ofPresentation_readout]; exact SameValue.refl _)

def realization_add (left right : EffectiveDyadicPresentation) :
    Equivalent (.add (ofPresentation P baseDepth left) (ofPresentation P baseDepth right))
      (ofPresentation P baseDepth (addPresentation left right)) :=
  Equivalent.ofExact (fun p => by
    rw [add_readout_exact, ofPresentation_readout, ofPresentation_readout, ofPresentation_readout]
    exact SameValue.refl _)

def toCarrier (real : Real P baseDepth) : EffectiveCauchyReal.Carrier :=
  EffectiveCauchyReal.ofPresentation (toPresentation real)

def addCarrier (left right : EffectiveCauchyReal.Carrier) : EffectiveCauchyReal.Carrier :=
  EffectiveCauchyReal.ofPresentation
    (addPresentation (EffectiveCauchyReal.toPresentation left) (EffectiveCauchyReal.toPresentation right))

def toCarrier_add (left right : Real P baseDepth) :
    EffectiveCauchyReal.Equivalent (toCarrier (.add left right)) (addCarrier (toCarrier left) (toCarrier right)) :=
  EffectiveCauchyReal.presentationEquivalentToCarrier (toPresentation_add left right)

def equivalentCarrier (first second : Real P baseDepth) :
    (Equivalent first second → EffectiveCauchyReal.Equivalent (toCarrier first) (toCarrier second)) ×
    (EffectiveCauchyReal.Equivalent (toCarrier first) (toCarrier second) → Equivalent first second) :=
  ⟨fun same => EffectiveCauchyReal.presentationEquivalentToCarrier ((equivalentPresentation first second).1 same),
    fun same => (equivalentPresentation first second).2 (EffectiveCauchyReal.carrierEquivalentToPresentation same)⟩

def ofCarrier (P : CircularPresentation) (baseDepth : Nat) (carrier : EffectiveCauchyReal.Carrier) :
    Real P baseDepth := ofPresentation P baseDepth (EffectiveCauchyReal.toPresentation carrier)

def carrier_roundtrip (carrier : EffectiveCauchyReal.Carrier) :
    EffectiveCauchyReal.Equivalent (toCarrier (ofCarrier P baseDepth carrier)) carrier where
  firstThreshold := (EffectiveCauchyReal.carrier_runtime_roundtrip_equivalent P baseDepth carrier).firstThreshold
  secondThreshold := (EffectiveCauchyReal.carrier_runtime_roundtrip_equivalent P baseDepth carrier).secondThreshold
  near := (EffectiveCauchyReal.carrier_runtime_roundtrip_equivalent P baseDepth carrier).near

def realization_carrier_add (left right : EffectiveCauchyReal.Carrier) :
    Equivalent (.add (ofCarrier P baseDepth left) (ofCarrier P baseDepth right))
      (ofCarrier P baseDepth (addCarrier left right)) :=
  Equivalent.ofExact (fun p => by
    unfold ofCarrier
    rw [add_readout_exact, ofPresentation_readout, ofPresentation_readout, ofPresentation_readout]
    exact SameValue.refl _)

def leafCorrespondence (first second : RuntimeReal P baseDepth) :
    (RuntimeReadoutEquivalent first second → Equivalent (.leaf first) (.leaf second)) ×
    (Equivalent (.leaf first) (.leaf second) → RuntimeReadoutEquivalent first second) :=
  ⟨fun same => ⟨same.responseThreshold, same.near⟩, fun same => ⟨same.threshold, same.near⟩⟩

def negPresentation (source : EffectiveDyadicPresentation) : EffectiveDyadicPresentation where
  approximation p := (source.approximation p).neg
  coherent := fun p l r hl hr => (source.coherent p l r hl hr).neg

def toPresentation_neg (source : Real P baseDepth) :
    EffectiveDyadicPresentation.Equivalent (toPresentation (.neg source))
      (negPresentation (toPresentation source)) where
  responseThreshold := fun p => p
  near := by
    intro p l r hl hr
    change Near p (readout (.neg source) l) (readout source r).neg
    rw [neg_readout_exact]
    exact (readoutsNear source p l r hl hr).neg

def realization_neg (source : EffectiveDyadicPresentation) :
    Equivalent (.neg (ofPresentation P baseDepth source))
      (ofPresentation P baseDepth (negPresentation source)) :=
  Equivalent.ofExact (fun p => by
    rw [neg_readout_exact, ofPresentation_readout, ofPresentation_readout]
    exact SameValue.refl _)

def negCarrier (source : EffectiveCauchyReal.Carrier) : EffectiveCauchyReal.Carrier :=
  EffectiveCauchyReal.ofPresentation (negPresentation (EffectiveCauchyReal.toPresentation source))

def toCarrier_neg (source : Real P baseDepth) :
    EffectiveCauchyReal.Equivalent (toCarrier (.neg source)) (negCarrier (toCarrier source)) :=
  EffectiveCauchyReal.presentationEquivalentToCarrier (toPresentation_neg source)

def realization_carrier_neg (source : EffectiveCauchyReal.Carrier) :
    Equivalent (.neg (ofCarrier P baseDepth source)) (ofCarrier P baseDepth (negCarrier source)) :=
  Equivalent.ofExact (fun p => by
    unfold ofCarrier
    rw [neg_readout_exact, ofPresentation_readout, ofPresentation_readout]
    exact SameValue.refl _)

end RelationalPerimeter.Constitution.Reals.RelationalRealAddition

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealAddition.mul_readout_exact
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealAddition.multiplicationCoherent
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealAddition.neg_readout_exact
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealAddition.neg_readout
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealAddition.neg_congr
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealAddition.neg_neg
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealAddition.add_neg
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealAddition.neg_add
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealAddition.neg_sum
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealAddition.AdditiveGroupLaws
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealAddition.additiveGroupLaws
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealAddition.AdditiveGroupFutureLaws
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealAddition.additiveGroupFutureLaws
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealAddition.negPresentation
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealAddition.toPresentation_neg
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealAddition.realization_neg
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealAddition.negCarrier
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealAddition.toCarrier_neg
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealAddition.realization_carrier_neg
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealAddition.AdditionAction
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealAddition.AdditionStored
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealAddition.additionProgram
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealAddition.additionProgram_readout
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealAddition.AdditionProduction
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealAddition.produceAddition
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealAddition.produceAddition_left
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealAddition.produceAddition_right
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealAddition.AdditionProduction.code
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealAddition.AdditionProduction.readoutExact
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealAddition.RetainedAddition
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealAddition.AdditionArchive
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealAddition.seedAdditionArchive
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealAddition.AdditionArchive.project
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealAddition.AdditionRichEvent
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealAddition.AdditionRichEvent.project
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealAddition.additionNext
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealAddition.additionEvent
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealAddition.additionLiveStep
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealAddition.additionCodeProjection
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealAddition.additionNextProjection
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealAddition.additionEventProjection
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealAddition.additionMemorySeparates
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealAddition.additionCoherent
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealAddition.addEnvironment
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealAddition.additionPacketSameTarget
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealAddition.additionRichEventOwnsProduction
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealAddition.additionRichEventReflectsArchive
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealAddition.Real
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealAddition.CertifiedService
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealAddition.environment
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealAddition.zero
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealAddition.one
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealAddition.executeAt
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealAddition.executeReal
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealAddition.initialReal
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealAddition.readout
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealAddition.add_readout_exact
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealAddition.add_readout
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealAddition.Coherent
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealAddition.leafCoherent
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealAddition.coherent
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealAddition.readoutsNear
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealAddition.currentReadout
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealAddition.Equivalent
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealAddition.Equivalent.refl
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealAddition.Equivalent.symm
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealAddition.Equivalent.trans
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealAddition.Equivalent.ofExact
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealAddition.NumericalTrace
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealAddition.NumericalFutureEquivalent
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealAddition.pairTraces
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealAddition.Equivalent.toFutures
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealAddition.NumericalFutureEquivalent.toEquivalent
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealAddition.numericalFutureCorrespondence
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealAddition.add_congr
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealAddition.constant_readout
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealAddition.zero_add
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealAddition.add_zero
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealAddition.add_comm
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealAddition.add_assoc
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealAddition.AdditiveLaws
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealAddition.additiveLaws
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealAddition.AdditiveFutureLaws
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealAddition.additiveFutureLaws
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealAddition.toPresentation
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealAddition.addPresentation
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealAddition.toPresentation_add
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealAddition.equivalentPresentation
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealAddition.ofPresentation
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealAddition.ofPresentation_readout
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealAddition.real_roundtrip
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealAddition.realization_add
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealAddition.toCarrier
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealAddition.addCarrier
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealAddition.toCarrier_add
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealAddition.equivalentCarrier
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealAddition.ofCarrier
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealAddition.carrier_roundtrip
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealAddition.realization_carrier_add
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealAddition.leafCorrespondence
/- AXIOM_AUDIT_END -/
