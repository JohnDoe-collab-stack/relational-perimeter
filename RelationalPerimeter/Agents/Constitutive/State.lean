import RelationalPerimeter.Agents.Constitutive.ProducedEvidence

/-! The rich specification retains the original profile and constituted past.
The runtime memory has only the received requirement, live engine and targets. -/
set_option genInjectivity false
set_option maxHeartbeats 2000000
namespace ConstitutiveSearch.Agent
open EndogenousDecomposition
open Resources

structure Memory : Type 3 where
  requirement : Requirement
  live : LiveContinuation.Memory
  register : List AnswerTarget

def normalizedRegister {input : Nat} (master : UnifiedMaster.Instance input)
    (profile : RoleOccurrenceProfile master.roles) : List AnswerTarget :=
  let source := master.source profile
  initialTargets master.reduction source.output (ProducedContinuation.output_accepted source)
    ((ProducedContinuation.output_is_executed source).trans (master.normalization.target_exact profile))

def start {input : Nat} (master : UnifiedMaster.Instance input)
    (requirement : Requirement) (profile : RoleOccurrenceProfile master.roles) : Memory :=
  ⟨requirement, LiveContinuation.project master.cursor, normalizedRegister master profile⟩

theorem start_register_length {input : Nat} (master : UnifiedMaster.Instance input)
    (requirement : Requirement) (profile : RoleOccurrenceProfile master.roles) :
    (start master requirement profile).register.length = resolutionLength input :=
  initialTargets_length _ _ _ _

/- This support belongs only to the rich specification. Its targets are
produced from the actual normalization and live head through typed ports.
The runtime register remains source-free. -/
structure TargetBundle (register : List AnswerTarget) : Type 3 where
  values : Values (fun _ : AnswerTarget => AnswerTarget) register
  exact : ∀ {target} (ref : Ref register target), Resources.read values ref = target

def bundleTargets : (register : List AnswerTarget) → TargetBundle register
  | [] => ⟨PUnit.unit, fun ref => nomatch ref⟩
  | target :: rest =>
      let tail := bundleTargets rest
      ⟨(target, tail.values), fun ref => match ref with
        | .here => rfl
        | .prior old => tail.exact old⟩

structure HistoricalProduction (cursor : MasterResources.Cursor) : Type 3 where
  private mk ::
  resources : (support : Support MasterResources.Value cursor.headSupport.kinds) ×
    Support.Extension cursor.support support
  exact : resources = cursor.headResources

def HistoricalProduction.produce (cursor : MasterResources.Cursor) : HistoricalProduction cursor :=
  ⟨cursor.headResources, rfl⟩

def HistoricalProduction.production {cursor : MasterResources.Cursor}
    (produced : HistoricalProduction cursor) : LiveContinuation.Production (LiveContinuation.project cursor) :=
  let head := (produced.resources.1.read .here).down
  ⟨⟨head.stage, head.run⟩, head.production.decomposition⟩

def HistoricalProduction.next {cursor : MasterResources.Cursor}
    (produced : HistoricalProduction cursor) : MasterResources.Cursor :=
  (MasterResources.continueWithReferences produced.resources.1 .here
    (.prior (.prior (.prior (.prior cursor.fresh))))).1

theorem HistoricalProduction.production_exact {cursor : MasterResources.Cursor}
    (produced : HistoricalProduction cursor) : produced.production = LiveContinuation.sourceProduction cursor := by
  obtain ⟨resources, exact⟩ := produced
  cases exact
  rfl

theorem HistoricalProduction.next_exact {cursor : MasterResources.Cursor}
    (produced : HistoricalProduction cursor) : produced.next = cursor.next := by
  obtain ⟨resources, exact⟩ := produced
  cases exact
  rfl

inductive HistoricalKind : Type 3 where
  | initialization (input : Nat)
  | bundle (register : List AnswerTarget)
  | cursor
  | production (cursor : MasterResources.Cursor)
  | target

def HistoricalValue : HistoricalKind → Type 3
  | .initialization input => (master : UnifiedMaster.Instance input) × RoleOccurrenceProfile master.roles
  | .bundle register => TargetBundle register
  | .cursor => MasterResources.Cursor
  | .production cursor => HistoricalProduction cursor
  | .target => AnswerTarget

def normalizationProducer {input : Nat} {kinds : List HistoricalKind}
    (arguments : Ref kinds (.initialization input)) : Producer HistoricalValue kinds where
  inputKinds := [.initialization input]
  inputs := .cons arguments .nil
  outputKind := fun args => .bundle (normalizedRegister args.1.1 args.1.2)
  operation := fun args => bundleTargets (normalizedRegister args.1.1 args.1.2)

def initialCursorProducer {input : Nat} {kinds : List HistoricalKind}
    (arguments : Ref kinds (.initialization input)) : Producer HistoricalValue kinds where
  inputKinds := [.initialization input]
  inputs := .cons arguments .nil
  outputKind := fun _ => .cursor
  operation := fun args => args.1.1.cursor

def componentProducer {register : List AnswerTarget} {kinds : List HistoricalKind}
    (bundle : Ref kinds (.bundle register)) {target : AnswerTarget}
    (component : Ref register target) : Producer HistoricalValue kinds where
  inputKinds := [.bundle register]
  inputs := .cons bundle .nil
  outputKind := fun _ => .target
  operation := fun args => Resources.read (Value := fun _ : AnswerTarget => AnswerTarget) args.1.values component

def historicalProductionProducer {kinds : List HistoricalKind}
    (cursor : Ref kinds .cursor) : Producer HistoricalValue kinds where
  inputKinds := [.cursor]
  inputs := .cons cursor .nil
  outputKind := fun args => .production args.1
  operation := fun args => HistoricalProduction.produce args.1

def producedTargetProducer {cursor : MasterResources.Cursor} {kinds : List HistoricalKind}
    (production : Ref kinds (.production cursor)) : Producer HistoricalValue kinds where
  inputKinds := [.production cursor]
  inputs := .cons production .nil
  outputKind := fun _ => .target
  operation := fun args => resumedTarget args.1.production

def followingCursorProducer {cursor : MasterResources.Cursor} {kinds : List HistoricalKind}
    (production : Ref kinds (.production cursor)) : Producer HistoricalValue kinds where
  inputKinds := [.production cursor]
  inputs := .cons production .nil
  outputKind := fun _ => .cursor
  operation := fun args => args.1.next

structure RegisterRealization (register : List AnswerTarget) (cursor : MasterResources.Cursor) : Type 3 where
  private mk ::
  kinds : List HistoricalKind
  support : Support HistoricalValue kinds
  cursorRef : Ref kinds .cursor
  cursorExact : support.read cursorRef = cursor
  reference : {target : AnswerTarget} → Ref register target → Ref kinds .target
  reads : ∀ {target} (ref : Ref register target), support.read (reference ref) = target
  injective : ∀ {target} (one two : Ref register target), reference one = reference two → one = two

/- Install tail first, then produce the head from its material bundle port.
This returns the actual extension of the input support alongside the rows. -/
def installTargets {all : List AnswerTarget} :
    (register : List AnswerTarget) → {kinds : List HistoricalKind} →
    (support : Support HistoricalValue kinds) → (bundle : Ref kinds (.bundle all)) →
    ({target : AnswerTarget} → Ref register target → Ref all target) →
    (cursorRef : Ref kinds .cursor) →
    (realization : RegisterRealization register (support.read cursorRef)) ×
      Support.Extension support realization.support
  | [], _, support, _, _, cursorRef =>
      ⟨⟨_, support, cursorRef, rfl, (fun ref => nomatch ref), (fun ref => nomatch ref),
          (fun ref => nomatch ref)⟩,
        .identity support⟩
  | target :: rest, _, support, bundle, select, cursorRef =>
      let tail := installTargets rest support bundle (fun ref => select (.prior ref)) cursorRef
      let producer := componentProducer (tail.2.references bundle) (select .here)
      let formed := tail.1.support.extend producer
      let transport := Support.Extension.produced tail.1.support producer
      let reference : {item : AnswerTarget} → Ref (target :: rest) item → Ref formed.kinds .target :=
        fun {item} ref => match ref with
        | .here => .here
        | .prior old => transport.references (tail.1.reference old)
      let reads : ∀ {item} (ref : Ref (target :: rest) item), formed.read (reference ref) = item :=
        fun {item} ref => match ref with
        | .here =>
            (congrArg (fun value : HistoricalValue (.bundle all) =>
              Resources.read (Value := fun _ : AnswerTarget => AnswerTarget)
                value.values (select .here)) (tail.2.reads bundle)).trans
                ((support.read bundle).exact (select .here))
        | .prior old => (transport.reads (tail.1.reference old)).trans (tail.1.reads old)
      let injective : ∀ {item} (one two : Ref (target :: rest) item), reference one = reference two → one = two := by
        intro item one two same
        cases one with
        | here => cases two with
          | here => rfl
          | prior old => cases same
        | prior first => cases two with
          | here => cases same
          | prior second =>
              exact congrArg Ref.prior (tail.1.injective first second
                (transport.injective _ _ same))
      ⟨⟨_, formed, transport.references tail.1.cursorRef,
          (transport.reads tail.1.cursorRef).trans tail.1.cursorExact, reference, reads, injective⟩,
        tail.2.compose transport⟩

def initialRegisterRealization {input : Nat} (master : UnifiedMaster.Instance input)
    (profile : RoleOccurrenceProfile master.roles) :
    RegisterRealization (normalizedRegister master profile) master.cursor :=
  let initial : Support HistoricalValue [.initialization input] := .given ((⟨master, profile⟩), PUnit.unit)
  let normalized := initial.extend (normalizationProducer .here)
  let cursored := normalized.extend (initialCursorProducer (.prior .here))
  (installTargets (normalizedRegister master profile) cursored (.prior .here) id .here).1

def appendReference {register : List AnswerTarget} {target : AnswerTarget} {kinds : List HistoricalKind}
    (old : {item : AnswerTarget} → Ref register item → Ref kinds .target)
    (fresh : Ref kinds .target) : {item : AnswerTarget} → Ref (register ++ [target]) item → Ref kinds .target :=
  match register with
  | [] => fun ref => match ref with | .here => fresh
  | _ :: _rest => fun ref => match ref with
    | .here => old .here
    | .prior prior => appendReference (fun ref => old (.prior ref)) fresh prior

theorem appendReference_old {register : List AnswerTarget} {target : AnswerTarget}
    {kinds : List HistoricalKind} (old : {item : AnswerTarget} → Ref register item → Ref kinds .target)
    (fresh : Ref kinds .target) {item} (ref : Ref register item) :
    appendReference old fresh (extendReference [target] ref) = old ref := by
  induction ref with
  | here => rfl
  | prior ref ih => exact ih (fun ref => old (.prior ref))

theorem appendReference_reads {register : List AnswerTarget} {target : AnswerTarget}
    {kinds : List HistoricalKind} (support : Support HistoricalValue kinds)
    (old : {item : AnswerTarget} → Ref register item → Ref kinds .target)
    (fresh : Ref kinds .target) (oldReads : ∀ {item} (ref : Ref register item), support.read (old ref) = item)
    (freshRead : support.read fresh = target) :
    ∀ {item} (ref : Ref (register ++ [target]) item), support.read (appendReference old fresh ref) = item := by
  induction register with
  | nil =>
      intro item ref
      cases ref with
      | here => exact freshRead
      | prior impossible => cases impossible
  | cons head rest ih =>
      intro item ref
      cases ref with
      | here => exact oldReads .here
      | prior prior => exact ih (fun ref => old (.prior ref)) (fun ref => oldReads (.prior ref)) prior

theorem appendReference_avoids {register : List AnswerTarget} {target item : AnswerTarget}
    {kinds : List HistoricalKind} (old : {item : AnswerTarget} → Ref register item → Ref kinds .target)
    (fresh blocked : Ref kinds .target)
    (oldApart : ∀ (ref : Ref register item), old ref ≠ blocked) (freshApart : fresh ≠ blocked) :
    ∀ (ref : Ref (register ++ [target]) item), appendReference old fresh ref ≠ blocked := by
  induction register with
  | nil =>
      intro ref
      cases ref with
      | here => exact freshApart
      | prior impossible => cases impossible
  | cons head rest ih =>
      intro ref
      cases ref with
      | here => exact oldApart .here
      | prior prior => exact ih (fun ref => old (.prior ref)) (fun ref => oldApart (.prior ref)) prior

theorem appendReference_injective {register : List AnswerTarget} {target : AnswerTarget}
    {kinds : List HistoricalKind} (old : {item : AnswerTarget} → Ref register item → Ref kinds .target)
    (fresh : Ref kinds .target)
    (oldInjective : ∀ {item} (one two : Ref register item), old one = old two → one = two)
    (apart : ∀ {item} (ref : Ref register item), old ref ≠ fresh) :
    ∀ {item} (one two : Ref (register ++ [target]) item),
      appendReference old fresh one = appendReference old fresh two → one = two := by
  induction register with
  | nil =>
      intro item one two same
      cases one with
      | here => cases two with
        | here => rfl
        | prior impossible => cases impossible
      | prior impossible => cases impossible
  | cons head rest ih =>
      have noHead : ∀ (ref : Ref (rest ++ [target]) head),
          appendReference (fun ref => old (.prior ref)) fresh ref ≠ old .here :=
        appendReference_avoids _ fresh (old .here)
          (fun ref same => by have impossible := oldInjective (.prior ref) .here same; cases impossible)
          (fun same => apart .here same.symm)
      intro item one two same
      cases one with
      | here => cases two with
        | here => rfl
        | prior other => exact False.elim (noHead other same.symm)
      | prior first => cases two with
        | here => exact False.elim (noHead first same)
        | prior second =>
            exact congrArg Ref.prior
              (ih (fun ref => old (.prior ref))
                (fun a b eq => prior_injective a b (oldInjective (.prior a) (.prior b) eq))
                (fun ref => apart (.prior ref)) first second same)

def RegisterRealization.advance {register : List AnswerTarget} {cursor : MasterResources.Cursor}
    (old : RegisterRealization register cursor) :
    (realization : RegisterRealization
      (register ++ [resumedTarget (LiveContinuation.sourceProduction cursor)]) cursor.next) ×
      Support.Extension old.support realization.support :=
  let produced := old.support.extend (historicalProductionProducer old.cursorRef)
  let actual : Ref produced.kinds (.production cursor) :=
    Eq.ndrec (motive := fun current => Ref produced.kinds (.production current)) Ref.here old.cursorExact
  let answered := produced.extend (producedTargetProducer actual)
  let continued := answered.extend (followingCursorProducer (.prior actual))
  let transport := ((Support.Extension.produced old.support (historicalProductionProducer old.cursorRef)).compose
    (Support.Extension.produced produced (producedTargetProducer actual))).compose
      (Support.Extension.produced answered (followingCursorProducer (.prior actual)))
  let oldReference := fun {item} (ref : Ref register item) => transport.references (old.reference ref)
  let newReference : Ref continued.kinds .target := .prior .here
  let newRead : continued.read newReference = resumedTarget (LiveContinuation.sourceProduction cursor) := by
    change resumedTarget (produced.read actual).production = _
    exact (congrArg resumedTarget (produced.read actual).production_exact)
  let oldReads := fun {item} (ref : Ref register item) => (transport.reads (old.reference ref)).trans (old.reads ref)
  let oldInjective := fun {item} (one two : Ref register item) same =>
    old.injective one two (transport.injective _ _ same)
  let apart : ∀ {item} (ref : Ref register item), oldReference ref ≠ newReference := by
    intro item ref same
    change Ref.prior (Ref.prior (Ref.prior (old.reference ref))) = Ref.prior Ref.here at same
    have impossible := prior_injective _ _ same
    cases impossible
  ⟨⟨_, continued, .here, (produced.read actual).next_exact,
      appendReference oldReference newReference,
      appendReference_reads continued oldReference newReference oldReads newRead,
      appendReference_injective oldReference newReference oldInjective apart⟩, transport⟩

theorem RegisterRealization.advance_old {register : List AnswerTarget} {cursor : MasterResources.Cursor}
    (old : RegisterRealization register cursor) {target} (ref : Ref register target) :
    old.advance.1.reference (extendReference [resumedTarget (LiveContinuation.sourceProduction cursor)] ref) =
      old.advance.2.references (old.reference ref) :=
  appendReference_old _ _ ref

theorem RegisterRealization.advance_position {register : List AnswerTarget} {cursor : MasterResources.Cursor}
    (old : RegisterRealization register cursor) {target} (ref : Ref register target) :
    (old.advance.1.reference (extendReference [resumedTarget (LiveContinuation.sourceProduction cursor)] ref)).position =
      (old.reference ref).position + old.advance.2.added :=
  (congrArg Ref.position (old.advance_old ref)).trans (old.advance.2.positions (old.reference ref))

def gatherTargets : (register : List AnswerTarget) →
    ({target : AnswerTarget} → Ref register target → AnswerTarget) → List AnswerTarget
  | [], _ => []
  | _ :: rest, reader => reader .here :: gatherTargets rest (fun ref => reader (.prior ref))

theorem gatherTargets_exact : ∀ (register : List AnswerTarget)
    (reader : {target : AnswerTarget} → Ref register target → AnswerTarget),
    (∀ {target} (ref : Ref register target), reader ref = target) → gatherTargets register reader = register
  | [], _, _ => rfl
  | head :: rest, reader, exactRead =>
      (congrArg (fun value => value :: gatherTargets rest (fun ref => reader (.prior ref)))
        (exactRead .here)).trans
          (congrArg (List.cons head)
            (gatherTargets_exact rest (fun ref => reader (.prior ref)) (fun ref => exactRead (.prior ref))))

def RegisterRealization.materialRegister {register : List AnswerTarget} {cursor : MasterResources.Cursor}
    (realization : RegisterRealization register cursor) : List AnswerTarget :=
  gatherTargets register (fun ref => realization.support.read (realization.reference ref))

theorem RegisterRealization.materialRegister_exact {register : List AnswerTarget}
    {cursor : MasterResources.Cursor} (realization : RegisterRealization register cursor) :
    realization.materialRegister = register :=
  gatherTargets_exact _ _ realization.reads

inductive History {input : Nat} (master : UnifiedMaster.Instance input)
    (profile : RoleOccurrenceProfile master.roles) : Type 3 where
  | initial : History master profile
  | step (past : History master profile) : History master profile

def History.cursor {input : Nat} {master : UnifiedMaster.Instance input}
    {profile : RoleOccurrenceProfile master.roles} : History master profile → MasterResources.Cursor
  | .initial => master.cursor
  | .step past => past.cursor.next

def History.targets {input : Nat} {master : UnifiedMaster.Instance input}
    {profile : RoleOccurrenceProfile master.roles} : History master profile → List AnswerTarget
  | .initial => normalizedRegister master profile
  | .step past =>
      past.targets ++ [resumedTarget (LiveContinuation.sourceProduction past.cursor)]

def History.realization {input : Nat} {master : UnifiedMaster.Instance input}
    {profile : RoleOccurrenceProfile master.roles} :
    (history : History master profile) → RegisterRealization history.targets history.cursor
  | .initial => initialRegisterRealization master profile
  | .step past => past.realization.advance.1

theorem History.handle_transport {input : Nat} {master : UnifiedMaster.Instance input}
    {profile : RoleOccurrenceProfile master.roles} (past : History master profile)
    {target} (ref : Ref past.targets target) :
    (History.step past).realization.reference
      (extendReference [resumedTarget (LiveContinuation.sourceProduction past.cursor)] ref) =
    past.realization.advance.2.references (past.realization.reference ref) :=
  past.realization.advance_old ref

/-- The actual rich support extensions, including the head formation, not an
ordinal-preserving surrogate for positions in the growing support. -/
def cursorReferences (cursor : MasterResources.Cursor) :
    Support.Extension cursor.support cursor.next.support :=
  let head := cursor.headResources
  let next := MasterResources.continueWithReferences head.1 .here
    (.prior (.prior (.prior (.prior cursor.fresh))))
  head.2.compose next.2

def History.references {input : Nat} {master : UnifiedMaster.Instance input}
    {profile : RoleOccurrenceProfile master.roles} (history : History master profile) :
    Support.Extension master.cursor.support history.cursor.support :=
  match history with
  | .initial => .identity master.cursor.support
  | .step past => past.references.compose (cursorReferences past.cursor)

structure Source {input : Nat} (master : UnifiedMaster.Instance input) : Type 3 where
  requirement : Requirement
  profile : RoleOccurrenceProfile master.roles
  history : History master profile

def Source.cursor {input : Nat} {master : UnifiedMaster.Instance input} (source : Source master) :=
  source.history.cursor

def sourceStart {input : Nat} (master : UnifiedMaster.Instance input)
    (requirement : Requirement) (profile : RoleOccurrenceProfile master.roles) : Source master :=
  ⟨requirement, profile, .initial⟩

def project {input : Nat} {master : UnifiedMaster.Instance input} (source : Source master) : Memory :=
  ⟨source.requirement, LiveContinuation.project source.cursor, source.history.targets⟩

theorem initialize_from_master_exact {input : Nat} (master : UnifiedMaster.Instance input)
    (requirement : Requirement) (profile : RoleOccurrenceProfile master.roles) :
    project (sourceStart master requirement profile) = start master requirement profile := rfl

theorem initialTargets_congr {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    {roles : RelationalConstitutiveRoleHistory run} {program : RoleIndexedProgram roles}
    (reduction : ExecutedRoleReductionHistory program)
    {one two : ExecutedOperationalTargetProfile reduction} (same : one = two)
    (first : RoleSemantics.TargetAccept reduction one) (second : RoleSemantics.TargetAccept reduction two)
    (firstExact : one = retainedExecutedOperationalTargetProfile reduction)
    (secondExact : two = retainedExecutedOperationalTargetProfile reduction) :
    initialTargets reduction one first firstExact = initialTargets reduction two second secondExact := by
  cases same
  rfl

theorem agent_memory_factors_through_output {input : Nat} (master : UnifiedMaster.Instance input)
    (requirement : Requirement) (left right : RoleOccurrenceProfile master.roles)
    (same : master.normalization.target left = master.normalization.target right) :
    start master requirement left = start master requirement right := by
  have sameOutputs : (master.source left).output = (master.source right).output :=
    (ProducedContinuation.output_is_executed (master.source left)).trans
      (same.trans (ProducedContinuation.output_is_executed (master.source right)).symm)
  exact congrArg (fun register => Memory.mk requirement (LiveContinuation.project master.cursor) register)
    (initialTargets_congr master.reduction sameOutputs _ _ _ _)

end ConstitutiveSearch.Agent
/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Agent.normalizedRegister
#print axioms ConstitutiveSearch.Agent.start
#print axioms ConstitutiveSearch.Agent.start_register_length
#print axioms ConstitutiveSearch.Agent.TargetBundle
#print axioms ConstitutiveSearch.Agent.bundleTargets
#print axioms ConstitutiveSearch.Agent.HistoricalProduction
#print axioms ConstitutiveSearch.Agent.HistoricalProduction.produce
#print axioms ConstitutiveSearch.Agent.HistoricalProduction.production
#print axioms ConstitutiveSearch.Agent.HistoricalProduction.next
#print axioms ConstitutiveSearch.Agent.HistoricalProduction.production_exact
#print axioms ConstitutiveSearch.Agent.HistoricalProduction.next_exact
#print axioms ConstitutiveSearch.Agent.normalizationProducer
#print axioms ConstitutiveSearch.Agent.initialCursorProducer
#print axioms ConstitutiveSearch.Agent.componentProducer
#print axioms ConstitutiveSearch.Agent.historicalProductionProducer
#print axioms ConstitutiveSearch.Agent.producedTargetProducer
#print axioms ConstitutiveSearch.Agent.followingCursorProducer
#print axioms ConstitutiveSearch.Agent.RegisterRealization
#print axioms ConstitutiveSearch.Agent.installTargets
#print axioms ConstitutiveSearch.Agent.initialRegisterRealization
#print axioms ConstitutiveSearch.Agent.appendReference
#print axioms ConstitutiveSearch.Agent.appendReference_old
#print axioms ConstitutiveSearch.Agent.appendReference_reads
#print axioms ConstitutiveSearch.Agent.appendReference_avoids
#print axioms ConstitutiveSearch.Agent.appendReference_injective
#print axioms ConstitutiveSearch.Agent.RegisterRealization.advance
#print axioms ConstitutiveSearch.Agent.RegisterRealization.advance_old
#print axioms ConstitutiveSearch.Agent.RegisterRealization.advance_position
#print axioms ConstitutiveSearch.Agent.RegisterRealization.materialRegister
#print axioms ConstitutiveSearch.Agent.RegisterRealization.materialRegister_exact
#print axioms ConstitutiveSearch.Agent.gatherTargets
#print axioms ConstitutiveSearch.Agent.gatherTargets_exact
#print axioms ConstitutiveSearch.Agent.History.targets
#print axioms ConstitutiveSearch.Agent.History.realization
#print axioms ConstitutiveSearch.Agent.History.handle_transport
#print axioms ConstitutiveSearch.Agent.History.cursor
#print axioms ConstitutiveSearch.Agent.cursorReferences
#print axioms ConstitutiveSearch.Agent.History.references
#print axioms ConstitutiveSearch.Agent.sourceStart
#print axioms ConstitutiveSearch.Agent.project
#print axioms ConstitutiveSearch.Agent.initialize_from_master_exact
#print axioms ConstitutiveSearch.Agent.initialTargets_congr
#print axioms ConstitutiveSearch.Agent.agent_memory_factors_through_output
/- AXIOM_AUDIT_END -/
