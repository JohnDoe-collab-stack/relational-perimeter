import RelationalPerimeter.Constitution.Resources.ConstructedSupport
import RelationalPerimeter.Computation.ConstitutiveSearch.EndogenousDecomposition.CausalOperationalExecution

/-!
# Typed resources of the authoritative executed head

The source is read through an earlier reference. Discovery creates the index
of the discovered resource from that read. Application reads that discovery;
decomposition reads the application and the already constituted prefix.
No completed tail is an input. The old head is an erasure specification only.
-/
set_option genInjectivity false
set_option maxHeartbeats 2000000
namespace ConstitutiveSearch.EndogenousDecomposition
namespace MasterResources
open Resources

inductive Kind : Type 3 where
  | source (depth : Nat) (assignment : SequentialAssignment depth)
  | prefix {depth : Nat} {assignment : SequentialAssignment depth}
      (state : ThreadedConstitutiveState depth assignment)
  | fresh {depth : Nat} {assignment : SequentialAssignment depth}
      (state : ThreadedConstitutiveState depth assignment)
  | discovery {depth : Nat} {assignment : SequentialAssignment depth}
      (state : ThreadedConstitutiveState depth assignment)
  | application {depth : Nat} {assignment : SequentialAssignment depth}
      (state : ThreadedConstitutiveState depth assignment)
  | decomposition {depth : Nat} {assignment : SequentialAssignment depth}
      (state : ThreadedConstitutiveState depth assignment)
      (context : ConstitutedOperationalPrefix (causalStateOfThreadedState state))
      (built : ConstructedThreadedStageRun state)
  | head {depth : Nat} {assignment : SequentialAssignment depth}
      (state : ThreadedConstitutiveState depth assignment)
      (context : ConstitutedOperationalPrefix (causalStateOfThreadedState state))

def Value : Kind → Type 3
  | .source depth assignment => ULift.{3} (ThreadedConstitutiveState depth assignment)
  | .prefix state => ULift.{3} (ConstitutedOperationalPrefix (causalStateOfThreadedState state))
  | .fresh state => ULift.{3} (PLift (ThreadedStateFreshForNext state))
  | .discovery state => ULift.{3} {run : ThreadedNextDiscoveryRun _ state // run = runThreadedNextDiscovery state}
  | .application state => ULift.{3} (ConstructedThreadedStageRun state)
  | .decomposition _ context built =>
      ULift.{3} (ExecutedStageOperationalProduction context (causalStageOfThreadedStage built.run))
  | .head state context => ULift.{3} (CausalOperationalHead state context)

def discover {depth : Nat} {assignment : SequentialAssignment depth}
    {context : List Kind} (source : Ref context (.source depth assignment)) : Producer Value context where
  inputKinds := [.source depth assignment]
  inputs := .cons source .nil
  outputKind := fun args => .discovery args.1.down
  operation := fun args => ⟨⟨runThreadedNextDiscovery args.1.down, rfl⟩⟩

def applyStage {depth : Nat} {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment} {context : List Kind}
    (discovery : Ref context (.discovery state)) (fresh : Ref context (.fresh state)) :
    Producer Value context where
  inputKinds := [.discovery state, .fresh state]
  inputs := .cons discovery (.cons fresh .nil)
  outputKind := fun _ => .application state
  operation := fun args => ⟨buildFromExecutedDiscovery state args.2.1.down.down
      args.1.down.val args.1.down.property⟩

def decompose {depth : Nat} {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment} {context : List Kind}
    (past : Ref context (.prefix state)) (application : Ref context (.application state)) :
    Producer Value context where
  inputKinds := [.prefix state, .application state]
  inputs := .cons past (.cons application .nil)
  outputKind := fun args => .decomposition state args.1.down args.2.1.down
  operation := fun args => ⟨prefixLocalOperationalProducer args.1.down
      (causalStageOfThreadedStage args.2.1.down.run)⟩

def assemble {depth : Nat} {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {past : ConstitutedOperationalPrefix (causalStateOfThreadedState state)}
    {built : ConstructedThreadedStageRun state} {context : List Kind}
    (production : Ref context (.decomposition state past built)) : Producer Value context where
  inputKinds := [.decomposition state past built]
  inputs := .cons production .nil
  outputKind := fun _ => .head state past
  operation := fun args => ⟨⟨built.stage, built.run, args.1.down⟩⟩

def initialSupport {depth : Nat} {assignment : SequentialAssignment depth}
    (state : ThreadedConstitutiveState depth assignment)
    (context : ConstitutedOperationalPrefix (causalStateOfThreadedState state))
    (fresh : ThreadedStateFreshForNext state) :
    Support Value [.fresh state, .prefix state, .source depth assignment] :=
  .given (⟨⟨fresh⟩⟩, ⟨context⟩, ⟨state⟩, PUnit.unit)

def headSupport {depth : Nat} {assignment : SequentialAssignment depth}
    (state : ThreadedConstitutiveState depth assignment)
    (context : ConstitutedOperationalPrefix (causalStateOfThreadedState state))
    (fresh : ThreadedStateFreshForNext state) :=
  let initial := initialSupport state context fresh
  let discovered := initial.extend (discover (.prior (.prior .here)))
  let applied := discovered.extend (applyStage .here (.prior .here))
  let decomposed := applied.extend (decompose (.prior (.prior (.prior .here))) .here)
  decomposed.extend (assemble .here)

def head {depth : Nat} {assignment : SequentialAssignment depth}
    (state : ThreadedConstitutiveState depth assignment)
    (context : ConstitutedOperationalPrefix (causalStateOfThreadedState state))
    (fresh : ThreadedStateFreshForNext state) : CausalOperationalHead state context :=
  let support := headSupport state context fresh
  (support.read .here).down

theorem head_exact {depth : Nat} {assignment : SequentialAssignment depth}
    (state : ThreadedConstitutiveState depth assignment)
    (context : ConstitutedOperationalPrefix (causalStateOfThreadedState state))
    (fresh : ThreadedStateFreshForNext state) :
    head state context fresh = executeCausalOperationalHead state context fresh := rfl

/-- A cursor owns a constituted support, not a cache of unrelated answers. -/
structure Cursor : Type 3 where
  depth : Nat
  assignment : SequentialAssignment depth
  kinds : List Kind
  support : Support Value kinds
  source : Ref kinds (.source depth assignment)
  past : Ref kinds (.prefix (support.read source).down)
  fresh : Ref kinds (.fresh (support.read source).down)

def Cursor.state (cursor : Cursor) := (cursor.support.read cursor.source).down
def Cursor.context (cursor : Cursor) := (cursor.support.read cursor.past).down
theorem Cursor.freshness (cursor : Cursor) : ThreadedStateFreshForNext cursor.state :=
  (cursor.support.read cursor.fresh).down.down

def initialCursor {depth : Nat} {assignment : SequentialAssignment depth}
    (state : ThreadedConstitutiveState depth assignment)
    (context : ConstitutedOperationalPrefix (causalStateOfThreadedState state))
    (fresh : ThreadedStateFreshForNext state) : Cursor :=
  ⟨depth, assignment, _, initialSupport state context fresh,
    .prior (.prior .here), .prior .here, .here⟩

def Cursor.headSupport (cursor : Cursor) :=
  let discovered := cursor.support.extend (discover cursor.source)
  let applied := discovered.extend (applyStage .here (.prior cursor.fresh))
  let decomposed := applied.extend (decompose (.prior (.prior cursor.past)) .here)
  decomposed.extend (assemble .here)

/-- The same four productions, with their reference transport built alongside
the values. No old head is recomputed to obtain this transport. -/
def Cursor.headResources (cursor : Cursor) :
    (support : Support Value cursor.headSupport.kinds) ×
      Support.Extension cursor.support support :=
  let discovery := discover cursor.source
  let discovered := cursor.support.extend discovery
  let application := applyStage .here (.prior cursor.fresh)
  let applied := discovered.extend application
  let decomposition := decompose (.prior (.prior cursor.past)) .here
  let decomposed := applied.extend decomposition
  let assembly := assemble .here
  let assembled := decomposed.extend assembly
  ⟨assembled, (((Support.Extension.produced cursor.support discovery).compose
    (Support.Extension.produced discovered application)).compose
    (Support.Extension.produced applied decomposition)).compose
    (Support.Extension.produced decomposed assembly)⟩

def Cursor.head (cursor : Cursor) : CausalOperationalHead cursor.state cursor.context :=
  let support := cursor.headSupport
  (support.read .here).down

theorem cursor_head_exact (cursor : Cursor) : cursor.head =
    executeCausalOperationalHead cursor.state cursor.context cursor.freshness := rfl

def headNextSource {depth : Nat} {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {past : ConstitutedOperationalPrefix (causalStateOfThreadedState state)} {context : List Kind}
    (head : Ref context (.head state past)) : Producer Value context where
  inputKinds := [.head state past]
  inputs := .cons head .nil
  outputKind := fun args => .source (depth + 1) args.1.down.stage.next
  operation := fun args => ⟨args.1.down.run.nextRun.next⟩

def headNextPrefix {depth : Nat} {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {past : ConstitutedOperationalPrefix (causalStateOfThreadedState state)} {context : List Kind}
    (head : Ref context (.head state past)) : Producer Value context where
  inputKinds := [.head state past]
  inputs := .cons head .nil
  outputKind := fun args => .prefix args.1.down.run.nextRun.next
  operation := fun args => ⟨args.1.down.production.nextContext⟩

def headNextFresh {depth : Nat} {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {past : ConstitutedOperationalPrefix (causalStateOfThreadedState state)} {context : List Kind}
    (head : Ref context (.head state past)) (fresh : Ref context (.fresh state)) :
    Producer Value context where
  inputKinds := [.head state past, .fresh state]
  inputs := .cons head (.cons fresh .nil)
  outputKind := fun args => .fresh args.1.down.run.nextRun.next
  operation := fun args => ⟨⟨args.1.down.run.nextRun.fresh args.2.1.down.down⟩⟩

def continueFrom {depth : Nat} {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {past : ConstitutedOperationalPrefix (causalStateOfThreadedState state)} {context : List Kind}
    (support : Support Value context) (head : Ref context (.head state past))
    (fresh : Ref context (.fresh state)) : Cursor :=
  let prefixed := support.extend (headNextPrefix head)
  let sourced := prefixed.extend (headNextSource (.prior head))
  let freshened := sourced.extend (headNextFresh (.prior (.prior head)) (.prior (.prior fresh)))
  ⟨depth + 1, (support.read head).down.stage.next, _, freshened,
    .prior .here, .prior (.prior .here), .here⟩

def Cursor.next (cursor : Cursor) : Cursor :=
  continueFrom cursor.headSupport .here (.prior (.prior (.prior (.prior cursor.fresh))))

/-- Extend exactly the supplied head support and return its old-reference map. -/
def continueWithReferences {depth : Nat} {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {past : ConstitutedOperationalPrefix (causalStateOfThreadedState state)} {context : List Kind}
    (support : Support Value context) (head : Ref context (.head state past))
    (fresh : Ref context (.fresh state)) :
    (next : Cursor) × Support.Extension support next.support :=
  let prefixProducer := headNextPrefix head
  let prefixed := support.extend prefixProducer
  let sourceProducer := headNextSource (.prior head)
  let sourced := prefixed.extend sourceProducer
  let freshProducer := headNextFresh (.prior (.prior head)) (.prior (.prior fresh))
  let freshened := sourced.extend freshProducer
  let next : Cursor := ⟨depth + 1, (support.read head).down.stage.next, _, freshened,
    .prior .here, .prior (.prior .here), .here⟩
  ⟨next, ((Support.Extension.produced support prefixProducer).compose
    (Support.Extension.produced prefixed sourceProducer)).compose
    (Support.Extension.produced sourced freshProducer)⟩

structure Result (count : Nat) (start : Cursor) : Type 3 where
  history : CausalOperationalExecutionHistory (_count := count) start.state start.context
  finish : Cursor
  references : Support.Extension start.support finish.support

def executeWithReferences : (count : Nat) → (cursor : Cursor) → Result count cursor
  | 0, cursor => ⟨.nil cursor.state cursor.context, cursor, .identity cursor.support⟩
  | count + 1, cursor =>
      let resources := cursor.headResources
      let produced := (resources.1.read .here).down
      let next := continueWithReferences resources.1 .here
        (.prior (.prior (.prior (.prior cursor.fresh))))
      let rest := executeWithReferences count next.1
      ⟨.step produced.stage produced.run produced.production rest.history, rest.finish,
        (resources.2.compose next.2).compose rest.references⟩

theorem cursor_next_state (cursor : Cursor) :
    cursor.next.state = cursor.head.run.nextRun.next := rfl

theorem cursor_next_context (cursor : Cursor) :
    cursor.next.context = cursor.head.production.nextContext := rfl

def execute (count : Nat) (cursor : Cursor) :
    CausalOperationalExecutionHistory (_count := count) cursor.state cursor.context × Cursor :=
  let result := executeWithReferences count cursor
  (result.history, result.finish)

theorem executeWithReferences_exact (count : Nat) (cursor : Cursor) :
    ((executeWithReferences count cursor).history, (executeWithReferences count cursor).finish) =
      execute count cursor := rfl

set_option maxHeartbeats 0 in
/-- Expose the recursive boundary without reducing discovery internals. -/
theorem execute_succ (count : Nat) (cursor : Cursor) :
    execute (count + 1) cursor =
      let resources := cursor.headResources
      let produced := (resources.1.read .here).down
      let next := (continueWithReferences resources.1 .here
        (.prior (.prior (.prior (.prior cursor.fresh))))).1
      (CausalOperationalExecutionHistory.step produced.stage produced.run
        produced.production (execute count next).1, (execute count next).2) := rfl

/-- The dependent boundary of a stored history. Reading it never discovers or
executes an old stage. -/
structure Boundary : Type 3 where
  depth : Nat
  assignment : SequentialAssignment depth
  state : ThreadedConstitutiveState depth assignment
  context : ConstitutedOperationalPrefix (causalStateOfThreadedState state)

def Cursor.boundary (cursor : Cursor) : Boundary :=
  ⟨cursor.depth, cursor.assignment, cursor.state, cursor.context⟩

def HistoryAt (boundary : Boundary) (count : Nat) : Type 3 :=
  CausalOperationalExecutionHistory (_count := count) boundary.state boundary.context

def transportHistory {first second : Boundary} {count : Nat} (same : first = second)
    (history : HistoryAt first count) : HistoryAt second count :=
  Eq.ndrec (motive := fun boundary => HistoryAt boundary count) history same

def endpoint : {depth count : Nat} → {assignment : SequentialAssignment depth} →
    {state : ThreadedConstitutiveState depth assignment} →
    {context : ConstitutedOperationalPrefix (causalStateOfThreadedState state)} →
    CausalOperationalExecutionHistory (_count := count) state context → Boundary
  | depth, _, assignment, _, _, .nil state context => ⟨depth, assignment, state, context⟩
  | _, _, _, _, _, .step _ _ _ tail => endpoint tail

theorem transportHistory_endpoint {first second : Boundary} {count : Nat} (same : first = second)
    (history : HistoryAt first count) : endpoint (transportHistory same history) = endpoint history := by
  cases same
  rfl

theorem execute_endpoint (count : Nat) (cursor : Cursor) :
    endpoint (execute count cursor).1 = (execute count cursor).2.boundary := by
  induction count generalizing cursor with
  | zero => rfl
  | succ count ih => exact ih cursor.next

theorem executeWithReferences_endpoint (count : Nat) (cursor : Cursor) :
    endpoint (executeWithReferences count cursor).history =
      (executeWithReferences count cursor).finish.boundary := by
  have agreement := executeWithReferences_exact count cursor
  have histories := congrArg Prod.fst agreement
  have cursors := congrArg Prod.snd agreement
  exact (congrArg endpoint histories).trans ((execute_endpoint count cursor).trans
    (congrArg Cursor.boundary cursors).symm)

/-- Positive origin of a stored prefix and its complete resource cursor.
An endpoint agreement alone does not establish this resource provenance. -/
structure ProducedPrefix {depth count : Nat} {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {context : ConstitutedOperationalPrefix (causalStateOfThreadedState state)}
    (origin : Cursor)
    (history : CausalOperationalExecutionHistory (_count := count) state context)
    (cursor : Cursor) : Type 3 where
  originBoundary : origin.boundary = (⟨depth, assignment, state, context⟩ : Boundary)
  historyExact : HEq history (executeWithReferences count origin).history
  cursorExact : cursor = (executeWithReferences count origin).finish

/-- Read the designated index, never choose another origin with the same boundary. -/
def ProducedPrefix.origin {depth count : Nat} {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {context : ConstitutedOperationalPrefix (causalStateOfThreadedState state)}
    {start : Cursor} {history : CausalOperationalExecutionHistory (_count := count) state context}
    {cursor : Cursor} (_prefix : ProducedPrefix start history cursor) : Cursor := start

theorem execute_finish_append (extra count : Nat) (cursor : Cursor) :
    (executeWithReferences extra (executeWithReferences count cursor).finish).finish =
      (executeWithReferences (extra + count) cursor).finish := by
  induction count generalizing cursor with
  | zero => rfl
  | succ count ih => exact ih cursor.next

/-- Resource cardinality is used only to separate complete origins with the
same operational boundary, not as a computation-cost model. -/
theorem cursor_next_resource_length (cursor : Cursor) :
    cursor.next.kinds.length = cursor.kinds.length + 7 := rfl

theorem execute_finish_resource_length (count : Nat) (cursor : Cursor) :
    (executeWithReferences count cursor).finish.kinds.length = cursor.kinds.length + 7 * count := by
  induction count generalizing cursor with
  | zero => rfl
  | succ count ih =>
    change (executeWithReferences count cursor.next).finish.kinds.length = _
    rw [ih cursor.next, cursor_next_resource_length, Nat.mul_succ,
      Nat.add_assoc, Nat.add_comm 7 (7 * count)]

set_option maxHeartbeats 2000000 in
theorem execute_erases (count : Nat) (cursor : Cursor) :
    (execute count cursor).1 = executeCausalOperationalExecutionHistory count
      cursor.state cursor.context cursor.freshness := by
  induction count generalizing cursor with
  | zero => rfl
  | succ count ih =>
    change CausalOperationalExecutionHistory.step cursor.head.stage cursor.head.run
      cursor.head.production (execute count cursor.next).1 = _
    rw [ih cursor.next]
    rfl

end MasterResources
end ConstitutiveSearch.EndogenousDecomposition
/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.EndogenousDecomposition.MasterResources.Kind
#print axioms ConstitutiveSearch.EndogenousDecomposition.MasterResources.Value
#print axioms ConstitutiveSearch.EndogenousDecomposition.MasterResources.discover
#print axioms ConstitutiveSearch.EndogenousDecomposition.MasterResources.applyStage
#print axioms ConstitutiveSearch.EndogenousDecomposition.MasterResources.decompose
#print axioms ConstitutiveSearch.EndogenousDecomposition.MasterResources.assemble
#print axioms ConstitutiveSearch.EndogenousDecomposition.MasterResources.initialSupport
#print axioms ConstitutiveSearch.EndogenousDecomposition.MasterResources.headSupport
#print axioms ConstitutiveSearch.EndogenousDecomposition.MasterResources.head
#print axioms ConstitutiveSearch.EndogenousDecomposition.MasterResources.head_exact
#print axioms ConstitutiveSearch.EndogenousDecomposition.MasterResources.Cursor
#print axioms ConstitutiveSearch.EndogenousDecomposition.MasterResources.initialCursor
#print axioms ConstitutiveSearch.EndogenousDecomposition.MasterResources.Cursor.headSupport
#print axioms ConstitutiveSearch.EndogenousDecomposition.MasterResources.Cursor.head
#print axioms ConstitutiveSearch.EndogenousDecomposition.MasterResources.cursor_head_exact
#print axioms ConstitutiveSearch.EndogenousDecomposition.MasterResources.Cursor.next
#print axioms ConstitutiveSearch.EndogenousDecomposition.MasterResources.headNextSource
#print axioms ConstitutiveSearch.EndogenousDecomposition.MasterResources.headNextPrefix
#print axioms ConstitutiveSearch.EndogenousDecomposition.MasterResources.headNextFresh
#print axioms ConstitutiveSearch.EndogenousDecomposition.MasterResources.continueFrom
#print axioms ConstitutiveSearch.EndogenousDecomposition.MasterResources.cursor_next_state
#print axioms ConstitutiveSearch.EndogenousDecomposition.MasterResources.cursor_next_context
#print axioms ConstitutiveSearch.EndogenousDecomposition.MasterResources.execute
#print axioms ConstitutiveSearch.EndogenousDecomposition.MasterResources.execute_erases
#print axioms ConstitutiveSearch.EndogenousDecomposition.MasterResources.Cursor.headResources
#print axioms ConstitutiveSearch.EndogenousDecomposition.MasterResources.continueWithReferences
#print axioms ConstitutiveSearch.EndogenousDecomposition.MasterResources.Result
#print axioms ConstitutiveSearch.EndogenousDecomposition.MasterResources.executeWithReferences
#print axioms ConstitutiveSearch.EndogenousDecomposition.MasterResources.executeWithReferences_exact
#print axioms ConstitutiveSearch.EndogenousDecomposition.MasterResources.execute_succ
#print axioms ConstitutiveSearch.EndogenousDecomposition.MasterResources.Boundary
#print axioms ConstitutiveSearch.EndogenousDecomposition.MasterResources.Cursor.boundary
#print axioms ConstitutiveSearch.EndogenousDecomposition.MasterResources.HistoryAt
#print axioms ConstitutiveSearch.EndogenousDecomposition.MasterResources.transportHistory
#print axioms ConstitutiveSearch.EndogenousDecomposition.MasterResources.transportHistory_endpoint
#print axioms ConstitutiveSearch.EndogenousDecomposition.MasterResources.endpoint
#print axioms ConstitutiveSearch.EndogenousDecomposition.MasterResources.execute_endpoint
#print axioms ConstitutiveSearch.EndogenousDecomposition.MasterResources.executeWithReferences_endpoint
#print axioms ConstitutiveSearch.EndogenousDecomposition.MasterResources.ProducedPrefix
#print axioms ConstitutiveSearch.EndogenousDecomposition.MasterResources.ProducedPrefix.origin
#print axioms ConstitutiveSearch.EndogenousDecomposition.MasterResources.execute_finish_append
#print axioms ConstitutiveSearch.EndogenousDecomposition.MasterResources.cursor_next_resource_length
#print axioms ConstitutiveSearch.EndogenousDecomposition.MasterResources.execute_finish_resource_length
/- AXIOM_AUDIT_END -/
