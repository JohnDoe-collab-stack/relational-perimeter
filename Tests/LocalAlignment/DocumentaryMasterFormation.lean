import Tests.LocalAlignment.DocumentaryMasterOperations
import RelationalPerimeter.Computation.ConstitutiveSearch.EndogenousDecomposition.VariableMasterExecution

/-! Positive recipe formation for the existing master resource executor.
Capture consumes the actual retained values. Restoration rebuilds the same
formation using recipes without applying past operations. This typed payload
still has higher-order master values and environments; it is not a master byte
checkpoint. Every finite existing master continuation closes this recipe class. -/
set_option genInjectivity false
set_option maxHeartbeats 4000000
namespace ConstitutiveSearch.Agent.Local.Documentary.MasterFormation
open Resources EndogenousDecomposition MasterOperations

inductive Formed : {kinds : List MasterResources.Kind} →
    Support MasterResources.Value kinds → Type 3 where
  | given {kinds} (values : Values MasterResources.Value kinds) : Formed (.given values)
  | produced {kinds support} (prior : @Formed kinds support) (operation : Operation kinds) :
      Formed (support.extend operation.producer)

/-- No historical operation result is computed by this constructor. The stored
value and agreement are supplied by the actual captured support. -/
inductive Tree : {kinds : List MasterResources.Kind} →
    Values MasterResources.Value kinds → Type 3 where
  | given {kinds} (values : Values MasterResources.Value kinds) : Tree values
  | step {kinds} {priorValues : Values MasterResources.Value kinds}
      (prior : Tree priorValues) (operation : Operation kinds)
      (value : MasterResources.Value (operation.producer.outputKind
        (operation.producer.arguments priorValues)))
      (actual : value = operation.producer.operation
        (operation.producer.arguments priorValues)) :
      Tree (kinds := operation.producer.outputKind
        (operation.producer.arguments priorValues) :: kinds) (value, priorValues)

def Tree.formation {kinds values} (tree : @Tree kinds values) :
    Formation MasterResources.Value values := by
  cases tree with
  | given values => exact .given values
  | step prior operation value actual =>
      cases actual
      exact .produced prior.formation operation.producer

def captureFrom {kinds} (support : Support MasterResources.Value kinds)
    (formed : Formed support) (copy : Values MasterResources.Value kinds)
    (same : copy = support.values) : Tree support.values := by
  cases formed with
  | given values => exact same ▸ Tree.given copy
  | @produced priorKinds previous prior operation =>
      let retained := captureFrom previous prior copy.2 (congrArg Prod.snd same)
      let headExact := congrArg Prod.fst same
      exact Eq.ndrec
        (motive := fun value => Tree
          (kinds := operation.producer.outputKind
            (operation.producer.arguments previous.values) :: priorKinds)
          (value, previous.values))
        (Tree.step retained operation copy.1 headExact) headExact

def captureTree {kinds} (support : Support MasterResources.Value kinds)
    (formed : Formed support) : Tree support.values :=
  captureFrom support formed support.values rfl

theorem capture_formation {kinds} (support : Support MasterResources.Value kinds)
    (formed : Formed support) : (captureTree support formed).formation = support.formation := by
  have general : ∀ (copy : Values MasterResources.Value kinds) (same : copy = support.values),
      (captureFrom support formed copy same).formation = support.formation := by
    induction formed with
    | given values => intro copy same; cases same; rfl
    | produced prior operation ih =>
        intro copy same
        cases same
        change Formation.produced (captureFrom _ prior _ rfl).formation operation.producer = _
        rw [ih]
        rfl
  exact general support.values rfl

structure ResourceData (kinds : List MasterResources.Kind) where
  values : Values MasterResources.Value kinds
  tree : Tree values

def resources {kinds} (support : Support MasterResources.Value kinds)
    (formed : Formed support) : ResourceData kinds :=
  ⟨support.values, captureTree support formed⟩

def ResourceData.restore {kinds} (data : ResourceData kinds) :
    Support MasterResources.Value kinds := ⟨data.values, data.tree.formation⟩

theorem resources_exact {kinds} (support : Support MasterResources.Value kinds)
    (formed : Formed support) : (resources support formed).restore = support := by
  cases support with
  | mk values formation =>
      change Support.mk values (captureTree _ formed).formation = _
      rw [capture_formation]

def Tree.records {kinds values} (tree : @Tree kinds values) : List Record := by
  cases tree with
  | given _ => exact []
  | step prior operation _ _ => exact prior.records ++ [operation.record]

def Formed.records {kinds support} : @Formed kinds support → List Record
  | .given _ => []
  | .produced prior operation => prior.records ++ [operation.record]

theorem capture_records {kinds} (support : Support MasterResources.Value kinds)
    (formed : Formed support) : (captureTree support formed).records = formed.records := by
  have general : ∀ (copy : Values MasterResources.Value kinds) (same : copy = support.values),
      (captureFrom support formed copy same).records = formed.records := by
    induction formed with
    | given values => intro copy same; cases same; rfl
    | produced prior operation ih =>
        intro copy same
        cases same
        change (captureFrom _ prior _ rfl).records ++ [operation.record] =
          prior.records ++ [operation.record]
        exact congrArg (fun records => records ++ [operation.record]) (ih _ rfl)
  exact general support.values rfl

structure CursorData : Type 3 where
  depth : Nat
  assignment : SequentialAssignment depth
  kinds : List MasterResources.Kind
  resources : ResourceData kinds
  source : Ref kinds (.source depth assignment)
  past : Ref kinds (.prefix (resources.restore.read source).down)
  fresh : Ref kinds (.fresh (resources.restore.read source).down)

def cursor (before : MasterResources.Cursor) (formed : Formed before.support) : CursorData :=
  ⟨before.depth, before.assignment, before.kinds, resources before.support formed,
    before.source, before.past, before.fresh⟩

def CursorData.restore (data : CursorData) : MasterResources.Cursor :=
  ⟨data.depth, data.assignment, data.kinds, data.resources.restore,
    data.source, data.past, data.fresh⟩

theorem cursor_exact (before : MasterResources.Cursor) (formed : Formed before.support) :
    (cursor before formed).restore = before := by
  cases before with
  | mk depth assignment kinds support source past fresh =>
      cases support with
      | mk values formation =>
          dsimp only [cursor, CursorData.restore, resources, ResourceData.restore]
          rw [capture_formation]

theorem all_cursor_consumers (before : MasterResources.Cursor) (formed : Formed before.support)
    {Result : Type u} (future : MasterResources.Cursor → Result) :
    future (cursor before formed).restore = future before :=
  congrArg future (cursor_exact before formed)

theorem future_heads (before : MasterResources.Cursor) (formed : Formed before.support) (count : Nat) :
    HEq (MasterResources.executeWithReferences count (cursor before formed).restore)
      (MasterResources.executeWithReferences count before) := by
  rw [cursor_exact]

def initial_formed {depth assignment} (state : ThreadedConstitutiveState depth assignment)
    (past : ConstitutedOperationalPrefix (causalStateOfThreadedState state))
    (fresh : ThreadedStateFreshForNext state) :
    Formed (MasterResources.initialCursor state past fresh).support := .given _

/-- The four recipes use exactly the ports of the existing executed head. -/
def head_formed (before : MasterResources.Cursor) (formed : Formed before.support) :
    Formed before.headSupport :=
  let discovered := Formed.produced formed (.discover before.source)
  let applied := Formed.produced discovered (.applyStage .here (.prior before.fresh))
  let decomposed := Formed.produced applied (.decompose (.prior (.prior before.past)) .here)
  Formed.produced decomposed (.assemble .here)

/-- Extend the supplied head support, not an independently rebuilt head. -/
def continue_formed {depth assignment} {state : ThreadedConstitutiveState depth assignment}
    {past : ConstitutedOperationalPrefix (causalStateOfThreadedState state)} {kinds}
    (support : Support MasterResources.Value kinds) (formed : Formed support)
    (head : Ref kinds (.head state past)) (fresh : Ref kinds (.fresh state)) :
    Formed (MasterResources.continueWithReferences support head fresh).1.support :=
  let prefixed := Formed.produced formed (.nextPrefix head)
  let sourced := Formed.produced prefixed (.nextSource (.prior head))
  Formed.produced sourced (.nextFresh (.prior (.prior head)) (.prior (.prior fresh)))

def next_formed (before : MasterResources.Cursor) (formed : Formed before.support) :
    Formed (VariableMaster.nextCursor before).support :=
  continue_formed before.headSupport (head_formed before formed) .here
    (.prior (.prior (.prior (.prior before.fresh))))

def executed_formed : (count : Nat) → (before : MasterResources.Cursor) →
    Formed before.support → Formed (MasterResources.executeWithReferences count before).finish.support
  | 0, _, formed => formed
  | count + 1, before, formed => executed_formed count before.next (next_formed before formed)

end ConstitutiveSearch.Agent.Local.Documentary.MasterFormation
/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Agent.Local.Documentary.MasterFormation.Formed
#print axioms ConstitutiveSearch.Agent.Local.Documentary.MasterFormation.Tree
#print axioms ConstitutiveSearch.Agent.Local.Documentary.MasterFormation.Tree.formation
#print axioms ConstitutiveSearch.Agent.Local.Documentary.MasterFormation.captureFrom
#print axioms ConstitutiveSearch.Agent.Local.Documentary.MasterFormation.captureTree
#print axioms ConstitutiveSearch.Agent.Local.Documentary.MasterFormation.capture_formation
#print axioms ConstitutiveSearch.Agent.Local.Documentary.MasterFormation.ResourceData
#print axioms ConstitutiveSearch.Agent.Local.Documentary.MasterFormation.resources
#print axioms ConstitutiveSearch.Agent.Local.Documentary.MasterFormation.ResourceData.restore
#print axioms ConstitutiveSearch.Agent.Local.Documentary.MasterFormation.resources_exact
#print axioms ConstitutiveSearch.Agent.Local.Documentary.MasterFormation.Tree.records
#print axioms ConstitutiveSearch.Agent.Local.Documentary.MasterFormation.Formed.records
#print axioms ConstitutiveSearch.Agent.Local.Documentary.MasterFormation.capture_records
#print axioms ConstitutiveSearch.Agent.Local.Documentary.MasterFormation.CursorData
#print axioms ConstitutiveSearch.Agent.Local.Documentary.MasterFormation.cursor
#print axioms ConstitutiveSearch.Agent.Local.Documentary.MasterFormation.CursorData.restore
#print axioms ConstitutiveSearch.Agent.Local.Documentary.MasterFormation.cursor_exact
#print axioms ConstitutiveSearch.Agent.Local.Documentary.MasterFormation.all_cursor_consumers
#print axioms ConstitutiveSearch.Agent.Local.Documentary.MasterFormation.future_heads
#print axioms ConstitutiveSearch.Agent.Local.Documentary.MasterFormation.initial_formed
#print axioms ConstitutiveSearch.Agent.Local.Documentary.MasterFormation.head_formed
#print axioms ConstitutiveSearch.Agent.Local.Documentary.MasterFormation.continue_formed
#print axioms ConstitutiveSearch.Agent.Local.Documentary.MasterFormation.next_formed
#print axioms ConstitutiveSearch.Agent.Local.Documentary.MasterFormation.executed_formed
/- AXIOM_AUDIT_END -/
