import RelationalPerimeter.Constitution.Reals.ReciprocalDomain

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Executed unary reciprocal service

The rich route retains the original executed apartness and transports its
margin to each current source Step. One action produces one division packet
and stored target. The live route retains only the compact native environment
and the computational direction/away parameters. Its zero-denominator branch
is outside the rich image, performs no division, and carries no inverse law.
-/
namespace RelationalPerimeter.Constitution.Reals.ReciprocalRuntime
open StrongPerimetralTurning ConstitutiveRuntime HeterogeneousRealRuntime RelationalRealAddition
open RelationalRealOrder DyadicReciprocal
open ConstitutiveSearch.ContinuationSignatures
variable {P : CircularPresentation} {baseDepth : Nat}

structure Operand (source : Real P baseDepth) (witness : Apartness source (zero P baseDepth))
    (archive : (environment source).Archive) (precision : Nat) where
  private mk ::
  origin : Apartness source (zero P baseDepth)
  originExact : origin = witness
  source : Step (environment source) archive (sourcePrecision (ReciprocalDomain.away witness) precision)
  nonzero : NonzeroCode (ReciprocalDomain.direction witness) (ReciprocalDomain.away witness) source.code

structure Action {source : Real P baseDepth} {witness : Apartness source (zero P baseDepth)}
    {archive : (environment source).Archive} {p : Nat} (searched : Operand source witness archive p) where
  private mk ::
  operand : Operand source witness archive p
  operandExact : operand = searched
  result : ReciprocalResult (ReciprocalDomain.direction witness) operand.source.code (roundingPrecision p)

structure Stored {source : Real P baseDepth} {witness : Apartness source (zero P baseDepth)}
    {archive : (environment source).Archive} {p : Nat} {searched : Operand source witness archive p}
    (acted : Action searched) where
  private mk ::
  action : Action searched
  actionExact : action = acted

def program {source : Real P baseDepth} {witness : Apartness source (zero P baseDepth)}
    {archive : (environment source).Archive} {p : Nat} (operand : Operand source witness archive p) : Program Unit where
  ReceivedContext _ := Operand source witness archive p
  SearchResult _ := Operand source witness archive p
  ActionResult _ searched := Action searched
  Accepted _ _ acted := CrossNear (roundingPrecision p) acted.result.division.quotient (powerOfTwo (roundingPrecision p))
    (powerOfTwo acted.operand.source.code.scale) (magnitude (ReciprocalDomain.direction witness) acted.operand.source.code)
  Authorization _ _ _ _ := Unit
  Decomposition _ _ _ _ _ := Operand source witness archive p
  Continuation _ _ _ _ _ _ := Operand source witness archive p
  Stored _ _ acted := Stored acted
  stamp _ := .limit p
  receive _ := operand
  search _ received := received
  act _ searched :=
    let result := computeReciprocal (ReciprocalDomain.direction witness) searched.source.code
      (roundingPrecision p) searched.nonzero.positive
    ⟨searched, rfl, result⟩
  preserves _ _ acted := acted.result.division.rounding
  authorize _ _ _ _ := ()
  decompose _ _ acted _ _ := acted.operand
  resume _ _ _ _ _ decomposed := decomposed
  store _ _ acted _ _ _ _ := ⟨acted, rfl⟩
  actionCode acted := acted.result.code
  read stored := stored.action.result.code
  readStoredExact stored := congrArg (fun a => a.result.code) stored.actionExact

structure Production (source : Real P baseDepth) (witness : Apartness source (zero P baseDepth))
    (archive : (environment source).Archive) (journal : Journal P baseDepth) (precision : Nat) where
  private mk ::
  operand : Operand source witness archive precision
  action : ExecutedRequest (program operand) P journal ()

def produce (source : Real P baseDepth) (witness : Apartness source (zero P baseDepth))
    (archive : (environment source).Archive) (journal : Journal P baseDepth) (precision : Nat) :
    Production source witness archive journal precision :=
  let step := executeAt source archive (sourcePrecision (ReciprocalDomain.away witness) precision)
  let separated := ReciprocalDomain.nonzero witness step (sourceBeyondAway _ _)
  let operand : Operand source witness archive precision := ⟨witness, rfl, step, separated⟩
  let action := execute (program operand) P journal ()
  ⟨operand, action⟩

namespace Production
variable {source : Real P baseDepth} {witness : Apartness source (zero P baseDepth)}
  {archive : (environment source).Archive} {journal : Journal P baseDepth} {p : Nat}
def owned (production : Production source witness archive journal p) : Operand source witness archive p :=
  production.action.memory.stored.action.operand
def sourceStep (production : Production source witness archive journal p) :
    Step (environment source) archive (sourcePrecision (ReciprocalDomain.away witness) p) := production.owned.source
def nonzero (production : Production source witness archive journal p) :
    NonzeroCode (ReciprocalDomain.direction witness) (ReciprocalDomain.away witness) production.sourceStep.code :=
  production.owned.nonzero
def result (production : Production source witness archive journal p) :
    ReciprocalResult (ReciprocalDomain.direction witness) production.sourceStep.code (roundingPrecision p) :=
  production.action.memory.stored.action.result
def code (production : Production source witness archive journal p) : SignedDyadicCode := production.result.code
theorem source_is_produced (production : Production source witness archive journal p) :
    production.sourceStep = production.operand.source := by
  change production.action.memory.stored.action.operand.source = _
  rw [production.action.memory.stored.actionExact]
  change production.action.action.operand.source = _
  rw [production.action.action.operandExact, production.action.searchResult_is_receivedContextOutput,
    production.action.receivedContext_is_produced]
  rfl
theorem code_is_action (production : Production source witness archive journal p) :
    production.code = production.action.action.result.code :=
  production.action.readout_is_storedAction
end Production

abbrev Retained (source : Real P baseDepth) (witness : Apartness source (zero P baseDepth)) :=
  (archive : (environment source).Archive) × (journal : Journal P baseDepth) × (p : Nat) × Production source witness archive journal p
structure Archive (realSource : Real P baseDepth) (witness : Apartness realSource (zero P baseDepth)) where
  private mk ::
  source : (environment realSource).Archive
  journal : Journal P baseDepth
  retained : List (Retained realSource witness)
  last : Option SignedDyadicCode
structure Memory (source : LiveEnvironment) where
  source : source.Memory
  last : Option SignedDyadicCode
theorem Memory.extensionality {source : LiveEnvironment} {first second : Memory source}
    (sameSource : first.source = second.source) (sameLast : first.last = second.last) : first = second := by
  cases first; cases second; cases sameSource; cases sameLast; rfl
structure LiveEvent (source : LiveEnvironment) where
  source : Outcome source.Event source.Read
  code : SignedDyadicCode
theorem LiveEvent.extensionality {source : LiveEnvironment} {first second : LiveEvent source}
    (sameSource : first.source = second.source) (sameCode : first.code = second.code) : first = second := by
  cases first; cases second; cases sameSource; cases sameCode; rfl
def Archive.project {source : Real P baseDepth} {witness : Apartness source (zero P baseDepth)}
    (archive : Archive source witness) : Memory (environment source).liveEnvironment :=
  ⟨(environment source).project archive.source, archive.last⟩
structure RichEvent (source : Real P baseDepth) (witness : Apartness source (zero P baseDepth)) where
  archive : Archive source witness
  precision : Nat
  production : Production source witness archive.source archive.journal precision
def next {source : Real P baseDepth} {witness : Apartness source (zero P baseDepth)}
    (archive : Archive source witness) {p : Nat} (production : Production source witness archive.source archive.journal p) :
    Archive source witness :=
  ⟨production.sourceStep.next, production.action.completedJournal,
    archive.retained ++ [⟨archive.source, archive.journal, p, production⟩], some production.code⟩
def event {source : Real P baseDepth} {witness : Apartness source (zero P baseDepth)}
    (archive : Archive source witness) {p : Nat} (production : Production source witness archive.source archive.journal p) :
    RichEvent source witness := ⟨archive, p, production⟩
def RichEvent.project {source : Real P baseDepth} {witness : Apartness source (zero P baseDepth)}
    (event : RichEvent source witness) : LiveEvent (environment source).liveEnvironment :=
  ⟨projectOutcome (environment source) (sourceFuture event.production.sourceStep), event.production.code⟩

/-- Total on abstract live states. The rejected denominator branch constructs
no division packet and has no reciprocal law. It is impossible on rich images. -/
def liveCode (direction : Direction) (code : SignedDyadicCode) (p : Nat) : SignedDyadicCode :=
  if positive : 0 < magnitude direction code then
    (computeReciprocal direction code (roundingPrecision p) positive).code
  else signedCode direction 0 (roundingPrecision p)
theorem liveCode_exact {direction : Direction} {code : SignedDyadicCode} {p : Nat}
    (positive : 0 < magnitude direction code) (result : ReciprocalResult direction code (roundingPrecision p)) :
    liveCode direction code p = result.code := by
  rw [liveCode, dif_pos positive]
  exact ReciprocalResult.sameCode _ result rfl
def liveStep (source : LiveEnvironment) (direction : Direction) (away : Nat) (memory : Memory source) (p : Nat) :
    LiveStep (Memory source) (LiveEvent source) :=
  let step := source.step memory.source (sourcePrecision away p)
  let code := liveCode direction (source.answer step.event) p
  ⟨⟨step.next, some code⟩, ⟨liveFuture source memory.source (sourcePrecision away p) step, code⟩⟩

theorem codeProjection {source : Real P baseDepth} {witness : Apartness source (zero P baseDepth)}
    (archive : Archive source witness) {p : Nat} (production : Production source witness archive.source archive.journal p) :
    production.code = (liveStep (environment source).liveEnvironment (ReciprocalDomain.direction witness)
      (ReciprocalDomain.away witness) archive.project p).event.code := by
  have sourceExact : (environment source).answer
      (((environment source).liveStep ((environment source).project archive.source)
        (sourcePrecision (ReciprocalDomain.away witness) p)).event) = production.sourceStep.code :=
    (congrArg (environment source).answer production.sourceStep.eventProjection).symm.trans
      production.sourceStep.answerProjection
  exact ((congrArg (fun code => liveCode (ReciprocalDomain.direction witness) code p) sourceExact).trans
    (liveCode_exact production.nonzero.positive production.result)).symm
theorem nextProjection {source : Real P baseDepth} {witness : Apartness source (zero P baseDepth)}
    (archive : Archive source witness) {p : Nat} (production : Production source witness archive.source archive.journal p) :
    (next archive production).project = (liveStep (environment source).liveEnvironment (ReciprocalDomain.direction witness)
      (ReciprocalDomain.away witness) archive.project p).next := by
  apply Memory.extensionality
  · exact production.sourceStep.nextProjection
  · exact congrArg some (codeProjection archive production)
theorem eventProjection {source : Real P baseDepth} {witness : Apartness source (zero P baseDepth)}
    (archive : Archive source witness) {p : Nat} (production : Production source witness archive.source archive.journal p) :
    (event archive production).project = (liveStep (environment source).liveEnvironment (ReciprocalDomain.direction witness)
      (ReciprocalDomain.away witness) archive.project p).event := by
  apply LiveEvent.extensionality
  · exact sourceFuture_projects production.sourceStep
  · exact codeProjection archive production
theorem memorySeparates (source : LiveEnvironment) (direction : Direction) (away : Nat)
    (first second : Memory source) (p : Nat) (sameRead : first.last = second.last)
    (sameEvent : (liveStep source direction away first p).event = (liveStep source direction away second p).event) :
    first = second := by
  apply Memory.extensionality
  · have h := congrArg LiveEvent.source sameEvent
    exact source.separates first.source second.source (sourcePrecision away p)
      (congrArg outcomeRead h) (Option.some.inj (congrArg outcomeEvent h))
  · exact sameRead

def inverseEnvironment (source : Real P baseDepth) (witness : Apartness source (zero P baseDepth)) : Service P baseDepth where
  Archive := Archive source witness
  Memory := Memory (environment source).liveEnvironment
  Event := LiveEvent (environment source).liveEnvironment
  RichEvent := RichEvent source witness
  Read := Option SignedDyadicCode
  Resource archive p := Production source witness archive.source archive.journal p
  initialArchive := ⟨ReciprocalDomain.sourceSuccessor witness, Journal.root P baseDepth, [], none⟩
  execute archive p := produce source witness archive.source archive.journal p
  next {archive} {p} production := next archive production
  richEvent {archive} {p} production := event archive production
  code {archive} {p} production := production.code
  readArchive archive := archive.last
  project := Archive.project
  projectEvent := RichEvent.project
  readLive := Memory.last
  liveStep := liveStep (environment source).liveEnvironment (ReciprocalDomain.direction witness) (ReciprocalDomain.away witness)
  answer := LiveEvent.code
  nextExact archive p := nextProjection archive (produce source witness archive.source archive.journal p)
  eventExact archive p := eventProjection archive (produce source witness archive.source archive.journal p)
  readExact _ := rfl
  answerExact _ := rfl
  separates := memorySeparates (environment source).liveEnvironment (ReciprocalDomain.direction witness) (ReciprocalDomain.away witness)

def inverseCoherent (source : Real P baseDepth) (witness : Apartness source (zero P baseDepth)) :
    Coherent (inverseEnvironment source witness) where
  near := by
    intro fa sa p first second fs ss fb sb
    dsimp only [inverseEnvironment] at fa sa fs ss
    exact reciprocalNear fs.resource.nonzero ss.resource.nonzero fs.resource.result ss.resource.result
      ((coherent source).near (sourcePrecision (ReciprocalDomain.away witness) p) _ _ fs.resource.sourceStep ss.resource.sourceStep
        (fb.succ.succ.add (PrecisionExtension.refl _)) (sb.succ.succ.add (PrecisionExtension.refl _))) fb sb

theorem inverseUniform (source : Real P baseDepth) (witness : Apartness source (zero P baseDepth))
    {firstArchive secondArchive : (inverseEnvironment source witness).Archive} {p : Nat}
    (first : Step (inverseEnvironment source witness) firstArchive p)
    (second : Step (inverseEnvironment source witness) secondArchive p) : first.code = second.code := by
  dsimp only [inverseEnvironment] at firstArchive secondArchive first second
  exact first.resource.result.sameCode second.resource.result
    ((currentReadout source _ _ first.resource.sourceStep).trans (currentReadout source _ _ second.resource.sourceStep).symm)

end RelationalPerimeter.Constitution.Reals.ReciprocalRuntime

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Constitution.Reals.ReciprocalRuntime.Operand
#print axioms RelationalPerimeter.Constitution.Reals.ReciprocalRuntime.Action
#print axioms RelationalPerimeter.Constitution.Reals.ReciprocalRuntime.Stored
#print axioms RelationalPerimeter.Constitution.Reals.ReciprocalRuntime.program
#print axioms RelationalPerimeter.Constitution.Reals.ReciprocalRuntime.Production
#print axioms RelationalPerimeter.Constitution.Reals.ReciprocalRuntime.produce
#print axioms RelationalPerimeter.Constitution.Reals.ReciprocalRuntime.Production.owned
#print axioms RelationalPerimeter.Constitution.Reals.ReciprocalRuntime.Production.sourceStep
#print axioms RelationalPerimeter.Constitution.Reals.ReciprocalRuntime.Production.nonzero
#print axioms RelationalPerimeter.Constitution.Reals.ReciprocalRuntime.Production.result
#print axioms RelationalPerimeter.Constitution.Reals.ReciprocalRuntime.Production.code
#print axioms RelationalPerimeter.Constitution.Reals.ReciprocalRuntime.Production.source_is_produced
#print axioms RelationalPerimeter.Constitution.Reals.ReciprocalRuntime.Production.code_is_action
#print axioms RelationalPerimeter.Constitution.Reals.ReciprocalRuntime.Retained
#print axioms RelationalPerimeter.Constitution.Reals.ReciprocalRuntime.Archive
#print axioms RelationalPerimeter.Constitution.Reals.ReciprocalRuntime.Memory
#print axioms RelationalPerimeter.Constitution.Reals.ReciprocalRuntime.Memory.extensionality
#print axioms RelationalPerimeter.Constitution.Reals.ReciprocalRuntime.LiveEvent
#print axioms RelationalPerimeter.Constitution.Reals.ReciprocalRuntime.LiveEvent.extensionality
#print axioms RelationalPerimeter.Constitution.Reals.ReciprocalRuntime.Archive.project
#print axioms RelationalPerimeter.Constitution.Reals.ReciprocalRuntime.RichEvent
#print axioms RelationalPerimeter.Constitution.Reals.ReciprocalRuntime.next
#print axioms RelationalPerimeter.Constitution.Reals.ReciprocalRuntime.event
#print axioms RelationalPerimeter.Constitution.Reals.ReciprocalRuntime.RichEvent.project
#print axioms RelationalPerimeter.Constitution.Reals.ReciprocalRuntime.liveCode
#print axioms RelationalPerimeter.Constitution.Reals.ReciprocalRuntime.liveCode_exact
#print axioms RelationalPerimeter.Constitution.Reals.ReciprocalRuntime.liveStep
#print axioms RelationalPerimeter.Constitution.Reals.ReciprocalRuntime.codeProjection
#print axioms RelationalPerimeter.Constitution.Reals.ReciprocalRuntime.nextProjection
#print axioms RelationalPerimeter.Constitution.Reals.ReciprocalRuntime.eventProjection
#print axioms RelationalPerimeter.Constitution.Reals.ReciprocalRuntime.memorySeparates
#print axioms RelationalPerimeter.Constitution.Reals.ReciprocalRuntime.inverseEnvironment
#print axioms RelationalPerimeter.Constitution.Reals.ReciprocalRuntime.inverseCoherent
#print axioms RelationalPerimeter.Constitution.Reals.ReciprocalRuntime.inverseUniform
/- AXIOM_AUDIT_END -/
