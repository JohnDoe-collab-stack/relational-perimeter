import RelationalPerimeter.Computation.ConstitutiveSearch.EndogenousDecomposition.MasterResourceExecution

/-! A materialized typed payload for the full retained master. Restoration uses
stored values and stored producers; it never applies a historical operation.
The payload still contains typed higher-order data. It is not a byte codec. -/
set_option genInjectivity false
set_option maxHeartbeats 3000000
namespace ConstitutiveSearch.Agent.Local.Documentary.MasterPayload
open Resources EndogenousDecomposition
universe u v

inductive Tree {Kind : Type u} (Value : Kind → Type v) :
    {kinds : List Kind} → Values Value kinds → Type (max u v) where
  | given {kinds} (values : Values Value kinds) : Tree Value values
  | step {kinds} {priorValues : Values Value kinds}
      (prior : Tree Value priorValues) (producer : Producer Value kinds)
      (value : Value (producer.outputKind (producer.arguments priorValues)))
      (actual : value = producer.operation (producer.arguments priorValues)) :
      Tree Value (kinds := producer.outputKind (producer.arguments priorValues) :: kinds) (value, priorValues)

def Tree.formation {Kind : Type u} {Value : Kind → Type v} {kinds}
    {values : Values Value kinds} (tree : Tree Value values) : Formation Value values := by
  cases tree with
  | given values => exact .given values
  | step prior producer value actual =>
      cases actual
      exact .produced prior.formation producer

def captureFrom {Kind : Type u} {Value : Kind → Type v} {kinds}
    (values : Values Value kinds) (formation : Formation Value values)
    (copy : Values Value kinds) (same : copy = values) : Tree Value values := by
  cases formation with
  | given values => exact same ▸ Tree.given copy
  | @produced priorKinds priorValues prior producer =>
      let previous := captureFrom priorValues prior copy.2 (congrArg Prod.snd same)
      let headExact := congrArg Prod.fst same
      exact Eq.ndrec
        (motive := fun value => Tree Value
          (kinds := producer.outputKind (producer.arguments priorValues) :: priorKinds) (value, priorValues))
        (Tree.step previous producer copy.1 headExact) headExact

def captureTree {Kind : Type u} {Value : Kind → Type v} {kinds}
    (values : Values Value kinds) (formation : Formation Value values) : Tree Value values :=
  captureFrom values formation values rfl

theorem capture_formation {Kind : Type u} {Value : Kind → Type v} {kinds}
    (values : Values Value kinds) (formation : Formation Value values) :
    (captureTree values formation).formation = formation := by
  have general : ∀ (copy : Values Value kinds) (same : copy = values),
      (captureFrom values formation copy same).formation = formation := by
    induction formation with
    | given values => intro copy same; cases same; rfl
    | produced prior producer ih =>
        intro copy same
        cases same
        change Formation.produced (captureFrom _ prior _ rfl).formation producer = _
        rw [ih]
  exact general values rfl

structure ResourceData {Kind : Type u} (Value : Kind → Type v) (kinds : List Kind) where
  values : Values Value kinds
  tree : Tree Value values

def resources {Kind : Type u} {Value : Kind → Type v} {kinds}
    (support : Support Value kinds) : ResourceData Value kinds :=
  ⟨support.values, captureTree support.values support.formation⟩

def ResourceData.restore {Kind : Type u} {Value : Kind → Type v} {kinds}
    (data : ResourceData Value kinds) : Support Value kinds := ⟨data.values, data.tree.formation⟩

theorem resources_exact {Kind : Type u} {Value : Kind → Type v} {kinds}
    (support : Support Value kinds) : (resources support).restore = support := by
  cases support with
  | mk values formation =>
      change Support.mk values (captureTree values formation).formation = _
      rw [capture_formation]

/-- Complete resource data and all three dependent ports. Neither a depth nor
an operational boundary can stand in for this payload. -/
structure CursorData : Type 3 where
  depth : Nat
  assignment : SequentialAssignment depth
  kinds : List MasterResources.Kind
  resources : ResourceData MasterResources.Value kinds
  source : Ref kinds (.source depth assignment)
  past : Ref kinds (.prefix (resources.restore.read source).down)
  fresh : Ref kinds (.fresh (resources.restore.read source).down)

def cursor (before : MasterResources.Cursor) : CursorData :=
  let data := resources before.support
  ⟨before.depth, before.assignment, before.kinds, data, before.source, before.past, before.fresh⟩

def CursorData.restore (data : CursorData) : MasterResources.Cursor :=
  ⟨data.depth, data.assignment, data.kinds, data.resources.restore, data.source, data.past, data.fresh⟩

theorem cursor_exact (before : MasterResources.Cursor) : (cursor before).restore = before := by
  cases before with
  | mk depth assignment kinds support source past fresh =>
      cases support with
      | mk values formation =>
          dsimp only [cursor, CursorData.restore, resources, ResourceData.restore]
          rw [capture_formation]

theorem all_cursor_consumers (before : MasterResources.Cursor) {Result : Type u}
    (future : MasterResources.Cursor → Result) : future (cursor before).restore = future before :=
  congrArg future (cursor_exact before)

theorem future_heads (before : MasterResources.Cursor) (count : Nat) :
    HEq (MasterResources.executeWithReferences count (cursor before).restore)
      (MasterResources.executeWithReferences count before) := by
  rw [cursor_exact]

end ConstitutiveSearch.Agent.Local.Documentary.MasterPayload
/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Agent.Local.Documentary.MasterPayload.Tree
#print axioms ConstitutiveSearch.Agent.Local.Documentary.MasterPayload.Tree.formation
#print axioms ConstitutiveSearch.Agent.Local.Documentary.MasterPayload.captureFrom
#print axioms ConstitutiveSearch.Agent.Local.Documentary.MasterPayload.captureTree
#print axioms ConstitutiveSearch.Agent.Local.Documentary.MasterPayload.capture_formation
#print axioms ConstitutiveSearch.Agent.Local.Documentary.MasterPayload.ResourceData
#print axioms ConstitutiveSearch.Agent.Local.Documentary.MasterPayload.resources
#print axioms ConstitutiveSearch.Agent.Local.Documentary.MasterPayload.ResourceData.restore
#print axioms ConstitutiveSearch.Agent.Local.Documentary.MasterPayload.resources_exact
#print axioms ConstitutiveSearch.Agent.Local.Documentary.MasterPayload.CursorData
#print axioms ConstitutiveSearch.Agent.Local.Documentary.MasterPayload.cursor
#print axioms ConstitutiveSearch.Agent.Local.Documentary.MasterPayload.CursorData.restore
#print axioms ConstitutiveSearch.Agent.Local.Documentary.MasterPayload.cursor_exact
#print axioms ConstitutiveSearch.Agent.Local.Documentary.MasterPayload.all_cursor_consumers
#print axioms ConstitutiveSearch.Agent.Local.Documentary.MasterPayload.future_heads
/- AXIOM_AUDIT_END -/
