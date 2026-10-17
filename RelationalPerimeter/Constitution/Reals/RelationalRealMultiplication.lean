import RelationalPerimeter.Constitution.Reals.HeterogeneousRealRuntime
import RelationalPerimeter.Constitution.Reals.DyadicMultiplication

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Probe, refine, act: relational multiplication

The two finite amplitude probes run from the current archives. Each refinement
then runs from its own probe's exact successor, at a precision computed from
the opposite probe. The action owns the two resulting resources, not readouts
extracted from a presentation. Its single target is stored and reused.
-/
namespace RelationalPerimeter.Constitution.Reals.RelationalRealMultiplication
open StrongPerimetralTurning ConstitutiveRuntime RuntimeCorrespondence HeterogeneousRealRuntime
open ConstitutiveSearch.ContinuationSignatures
variable {P : CircularPresentation} {baseDepth : Nat}

structure ProductBudget where
  leftAmplitude : Nat
  rightAmplitude : Nat
  leftPrecision : Nat
  rightPrecision : Nat

def productBudget (leftProbe rightProbe : SignedDyadicCode) (precision : Nat) : ProductBudget :=
  let leftBound := probeAmplitude leftProbe
  let rightBound := probeAmplitude rightProbe
  ⟨leftBound, rightBound, precision + 1 + rightBound, precision + 1 + leftBound⟩

structure MultiplicationAction {Left Right : Type} (readLeft : Left → SignedDyadicCode)
    (readRight : Right → SignedDyadicCode) (searched : Left × Right) where
  private mk ::
  operands : Left × Right
  operandsExact : operands = searched
  code : SignedDyadicCode
  codeExact : code = (readLeft operands.1).mul (readRight operands.2)

structure MultiplicationStored {Left Right : Type} {readLeft : Left → SignedDyadicCode}
    {readRight : Right → SignedDyadicCode} {searched : Left × Right}
    (acted : MultiplicationAction readLeft readRight searched) where
  private mk ::
  action : MultiplicationAction readLeft readRight searched
  actionExact : action = acted

def multiplicationProgram {Left Right : Type} (left : Left) (right : Right)
    (readLeft : Left → SignedDyadicCode) (readRight : Right → SignedDyadicCode)
    (precision : Nat) : Program Unit where
  ReceivedContext _ := Left × Right
  SearchResult _ := Left × Right
  ActionResult _ searched := MultiplicationAction readLeft readRight searched
  Accepted _ searched acted := SameValue acted.code ((readLeft searched.1).mul (readRight searched.2))
  Authorization _ _ _ _ := Unit
  Decomposition _ _ _ _ _ := Left × Right
  Continuation _ _ _ _ _ _ := Left × Right
  Stored _ _ acted := MultiplicationStored acted
  stamp _ := .limit precision
  receive _ := ⟨left, right⟩
  search _ received := received
  act _ searched := ⟨searched, rfl, (readLeft searched.1).mul (readRight searched.2), rfl⟩
  preserves _ searched acted := by
    have exact : acted.code = (readLeft searched.1).mul (readRight searched.2) := by
      rw [acted.codeExact, acted.operandsExact]
    exact Eq.rec (motive := fun target _ => SameValue acted.code target)
      (SameValue.refl acted.code) exact
  authorize _ _ _ _ := ()
  decompose _ searched _ _ _ := searched
  resume _ _ _ _ _ decomposed := decomposed
  store _ _ acted _ _ _ _ := ⟨acted, rfl⟩
  actionCode acted := acted.code
  read stored := stored.action.code
  readStoredExact stored := congrArg MultiplicationAction.code stored.actionExact

theorem multiplicationProgram_readout {Left Right : Type} (left : Left) (right : Right)
    (readLeft : Left → SignedDyadicCode) (readRight : Right → SignedDyadicCode)
    (precision : Nat) {journal : Journal P baseDepth}
    (executed : ExecutedRequest (multiplicationProgram left right readLeft readRight precision) P journal ()) :
    executed.readout = (readLeft left).mul (readRight right) := by
  rw [executed.readout_is_storedAction]
  change executed.action.code = _
  rw [executed.action.codeExact, executed.action.operandsExact,
    executed.searchResult_is_receivedContextOutput, executed.receivedContext_is_produced]
  rfl

/-- Phase order is in the types: neither initial archives nor same-code resources
can replace either probe's exact successor archive. Roles remain distinct. -/
structure MultiplicationProduction (leftEnvironment rightEnvironment : Service P baseDepth)
    (leftArchive : leftEnvironment.Archive) (rightArchive : rightEnvironment.Archive)
    (journal : Journal P baseDepth) (precision : Nat) where
  private mk ::
  leftProbe : Step leftEnvironment leftArchive 0
  rightProbe : Step rightEnvironment rightArchive 0
  left : Step leftEnvironment leftProbe.next (productBudget leftProbe.code rightProbe.code precision).leftPrecision
  right : Step rightEnvironment rightProbe.next (productBudget leftProbe.code rightProbe.code precision).rightPrecision
  action : ExecutedRequest (multiplicationProgram left right Step.code Step.code precision) P journal ()

def produceMultiplication (left right : Service P baseDepth)
    (leftArchive : left.Archive) (rightArchive : right.Archive) (journal : Journal P baseDepth) (precision : Nat) :
    MultiplicationProduction left right leftArchive rightArchive journal precision :=
  let leftProbe := perform left leftArchive 0
  let rightProbe := perform right rightArchive 0
  let budget := productBudget leftProbe.code rightProbe.code precision
  let first := perform left leftProbe.next budget.leftPrecision
  let second := perform right rightProbe.next budget.rightPrecision
  let action := execute (multiplicationProgram first second Step.code Step.code precision) P journal ()
  ⟨leftProbe, rightProbe, first, second, action⟩

def MultiplicationProduction.code {left right : Service P baseDepth}
    {la : left.Archive} {ra : right.Archive} {journal : Journal P baseDepth} {p : Nat}
    (production : MultiplicationProduction left right la ra journal p) : SignedDyadicCode :=
  production.action.memory.stored.action.code

theorem MultiplicationProduction.readoutExact {left right : Service P baseDepth}
    {la : left.Archive} {ra : right.Archive} {journal : Journal P baseDepth} {p : Nat}
    (production : MultiplicationProduction left right la ra journal p) :
    production.code = production.left.code.mul production.right.code :=
  multiplicationProgram_readout _ _ _ _ _ production.action

abbrev RetainedMultiplication (left right : Service P baseDepth) :=
  (la : left.Archive) × (ra : right.Archive) × (journal : Journal P baseDepth) ×
    (p : Nat) × MultiplicationProduction left right la ra journal p

structure MultiplicationArchive (leftEnvironment rightEnvironment : Service P baseDepth) where
  left : leftEnvironment.Archive
  right : rightEnvironment.Archive
  journal : Journal P baseDepth
  retained : List (RetainedMultiplication leftEnvironment rightEnvironment)
  last : Option SignedDyadicCode

def MultiplicationArchive.project {left right : Service P baseDepth} (a : MultiplicationArchive left right) :
    CompositeMemory left.liveEnvironment right.liveEnvironment := ⟨left.project a.left, right.project a.right, a.last⟩

structure MultiplicationRichEvent (left right : Service P baseDepth) where
  archive : MultiplicationArchive left right
  precision : Nat
  production : MultiplicationProduction left right archive.left archive.right archive.journal precision

structure MultiplicationLiveEvent (left right : LiveEnvironment) where
  leftProbe : Outcome left.Event left.Read
  rightProbe : Outcome right.Event right.Read
  left : Outcome left.Event left.Read
  right : Outcome right.Event right.Read
  code : SignedDyadicCode

theorem MultiplicationLiveEvent.extensionality {left right : LiveEnvironment}
    {a b : MultiplicationLiveEvent left right}
    (lp : a.leftProbe = b.leftProbe) (rp : a.rightProbe = b.rightProbe)
    (l : a.left = b.left) (r : a.right = b.right) (c : a.code = b.code) : a = b := by
  cases a; cases b; cases lp; cases rp; cases l; cases r; cases c; rfl

def multiplicationNext {left right : Service P baseDepth} (archive : MultiplicationArchive left right) {p : Nat}
    (production : MultiplicationProduction left right archive.left archive.right archive.journal p) :
    MultiplicationArchive left right :=
  ⟨production.left.next, production.right.next, production.action.completedJournal,
    archive.retained ++ [⟨archive.left, archive.right, archive.journal, p, production⟩], some production.code⟩

def MultiplicationRichEvent.project {left right : Service P baseDepth} (e : MultiplicationRichEvent left right) :
    MultiplicationLiveEvent left.liveEnvironment right.liveEnvironment :=
  ⟨projectOutcome left (sourceFuture e.production.leftProbe), projectOutcome right (sourceFuture e.production.rightProbe),
    projectOutcome left (sourceFuture e.production.left), projectOutcome right (sourceFuture e.production.right), e.production.code⟩

def multiplicationLiveStep (left right : LiveEnvironment) (memory : CompositeMemory left right) (p : Nat) :
    LiveStep (CompositeMemory left right) (MultiplicationLiveEvent left right) :=
  let leftProbe := left.step memory.left 0
  let rightProbe := right.step memory.right 0
  let budget := productBudget (left.answer leftProbe.event) (right.answer rightProbe.event) p
  let first := left.step leftProbe.next budget.leftPrecision
  let second := right.step rightProbe.next budget.rightPrecision
  let code := (left.answer first.event).mul (right.answer second.event)
  ⟨⟨first.next, second.next, some code⟩,
    ⟨liveFuture left memory.left 0 leftProbe, liveFuture right memory.right 0 rightProbe,
      liveFuture left leftProbe.next budget.leftPrecision first,
      liveFuture right rightProbe.next budget.rightPrecision second, code⟩⟩

theorem stepCodeProjection {s : Service P baseDepth} {a : s.Archive} {p : Nat} (step : Step s a p) :
    step.code = s.answer (s.liveStep (s.project a) p).event :=
  step.answerProjection.symm.trans (congrArg s.answer step.eventProjection)

theorem multiplicationCodeProjection {left right : Service P baseDepth} (a : MultiplicationArchive left right) {p : Nat}
    (production : MultiplicationProduction left right a.left a.right a.journal p) :
    production.code = (multiplicationLiveStep left.liveEnvironment right.liveEnvironment a.project p).event.code := by
  rw [production.readoutExact, stepCodeProjection production.left, stepCodeProjection production.right,
    production.leftProbe.nextProjection, production.rightProbe.nextProjection,
    stepCodeProjection production.leftProbe, stepCodeProjection production.rightProbe]
  rfl

theorem multiplicationNextProjection {left right : Service P baseDepth} (a : MultiplicationArchive left right) {p : Nat}
    (production : MultiplicationProduction left right a.left a.right a.journal p) :
    (multiplicationNext a production).project =
      (multiplicationLiveStep left.liveEnvironment right.liveEnvironment a.project p).next := by
  apply CompositeMemory.extensionality
  · apply production.left.nextProjection.trans
    rw [production.leftProbe.nextProjection, stepCodeProjection production.leftProbe,
      stepCodeProjection production.rightProbe]
    rfl
  · apply production.right.nextProjection.trans
    rw [production.rightProbe.nextProjection, stepCodeProjection production.leftProbe,
      stepCodeProjection production.rightProbe]
    rfl
  · exact congrArg some (multiplicationCodeProjection a production)

theorem multiplicationEventProjection {left right : Service P baseDepth} (a : MultiplicationArchive left right) {p : Nat}
    (production : MultiplicationProduction left right a.left a.right a.journal p) :
    (MultiplicationRichEvent.mk a p production).project =
      (multiplicationLiveStep left.liveEnvironment right.liveEnvironment a.project p).event := by
  apply MultiplicationLiveEvent.extensionality
  · exact sourceFuture_projects production.leftProbe
  · exact sourceFuture_projects production.rightProbe
  · apply (sourceFuture_projects production.left).trans
    rw [production.leftProbe.nextProjection, stepCodeProjection production.leftProbe,
      stepCodeProjection production.rightProbe]
    rfl
  · apply (sourceFuture_projects production.right).trans
    rw [production.rightProbe.nextProjection, stepCodeProjection production.leftProbe,
      stepCodeProjection production.rightProbe]
    rfl
  · exact multiplicationCodeProjection a production

theorem multiplicationMemorySeparates (left right : LiveEnvironment) (a b : CompositeMemory left right) (p : Nat)
    (last : a.last = b.last)
    (events : (multiplicationLiveStep left right a p).event = (multiplicationLiveStep left right b p).event) : a = b := by
  apply CompositeMemory.extensionality
  · have h := congrArg MultiplicationLiveEvent.leftProbe events
    exact left.separates a.left b.left 0 (congrArg outcomeRead h) (Option.some.inj (congrArg outcomeEvent h))
  · have h := congrArg MultiplicationLiveEvent.rightProbe events
    exact right.separates a.right b.right 0 (congrArg outcomeRead h) (Option.some.inj (congrArg outcomeEvent h))
  · exact last

def mulEnvironment (left right : Service P baseDepth) : Service P baseDepth where
  Archive := MultiplicationArchive left right
  Memory := CompositeMemory left.liveEnvironment right.liveEnvironment
  Event := MultiplicationLiveEvent left.liveEnvironment right.liveEnvironment
  RichEvent := MultiplicationRichEvent left right
  Read := Option SignedDyadicCode
  Resource a p := MultiplicationProduction left right a.left a.right a.journal p
  initialArchive := ⟨left.initialArchive, right.initialArchive, Journal.root P baseDepth, [], none⟩
  execute a p := produceMultiplication left right a.left a.right a.journal p
  next {a} {p} production := multiplicationNext a production
  richEvent {a} {p} production := ⟨a, p, production⟩
  code {a} {p} production := production.code
  readArchive := MultiplicationArchive.last
  project := MultiplicationArchive.project
  projectEvent := MultiplicationRichEvent.project
  readLive := CompositeMemory.last
  liveStep := multiplicationLiveStep left.liveEnvironment right.liveEnvironment
  answer := MultiplicationLiveEvent.code
  nextExact a p := multiplicationNextProjection a (produceMultiplication left right a.left a.right a.journal p)
  eventExact a p := multiplicationEventProjection a (produceMultiplication left right a.left a.right a.journal p)
  readExact _ := rfl
  answerExact _ := rfl
  separates := multiplicationMemorySeparates left.liveEnvironment right.liveEnvironment

theorem multiplicationPacketSameTarget {left right : Service P baseDepth} {a : MultiplicationArchive left right} {p : Nat}
    (step : Step (mulEnvironment left right) a p) :
    step.code = step.resource.action.action.code ∧ step.next.last = some step.resource.action.action.code ∧
      step.liveEvent.code = step.resource.action.action.code := by
  have h : step.code = step.resource.action.action.code := step.resource.action.readout_is_storedAction
  exact ⟨h, congrArg some h, h⟩

theorem multiplicationRichEventReflectsArchive {left right : Service P baseDepth}
    {a b : MultiplicationArchive left right} (p : Nat)
    (same : (richContract (mulEnvironment left right)).event a p =
      (richContract (mulEnvironment left right)).event b p) : a = b :=
  congrArg MultiplicationRichEvent.archive same

end RelationalPerimeter.Constitution.Reals.RelationalRealMultiplication

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealMultiplication.ProductBudget
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealMultiplication.productBudget
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealMultiplication.MultiplicationAction
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealMultiplication.MultiplicationStored
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealMultiplication.multiplicationProgram
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealMultiplication.multiplicationProgram_readout
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealMultiplication.MultiplicationProduction
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealMultiplication.produceMultiplication
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealMultiplication.MultiplicationProduction.code
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealMultiplication.MultiplicationProduction.readoutExact
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealMultiplication.RetainedMultiplication
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealMultiplication.MultiplicationArchive
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealMultiplication.MultiplicationArchive.project
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealMultiplication.MultiplicationRichEvent
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealMultiplication.MultiplicationLiveEvent
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealMultiplication.MultiplicationLiveEvent.extensionality
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealMultiplication.multiplicationNext
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealMultiplication.MultiplicationRichEvent.project
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealMultiplication.multiplicationLiveStep
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealMultiplication.stepCodeProjection
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealMultiplication.multiplicationCodeProjection
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealMultiplication.multiplicationNextProjection
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealMultiplication.multiplicationEventProjection
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealMultiplication.multiplicationMemorySeparates
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealMultiplication.mulEnvironment
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealMultiplication.multiplicationPacketSameTarget
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealMultiplication.multiplicationRichEventReflectsArchive
/- AXIOM_AUDIT_END -/
