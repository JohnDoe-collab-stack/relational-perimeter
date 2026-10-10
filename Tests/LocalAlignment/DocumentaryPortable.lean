import Tests.LocalAlignment.DocumentarySnapshot

/-! First-order records for the canonical quotation/binary-rule store language.
Loading validates saved values and constructs formation witnesses directly. The
general higher-order master cursor is outside this record language. -/
set_option genInjectivity false
set_option maxHeartbeats 2000000
namespace ConstitutiveSearch.Agent.Local.Documentary.Portable
open Resources Program

inductive Node : Type where
  | quotation (source : Nat) (value : Int)
  | derived (rule left right : Nat) (value : Int)

inductive Error : Type where
  | sourceMissing | sourceForbidden | ruleMissing | ruleForbidden
  | premiseMissing | valueChanged

def recordKind : Deduction.Kind → Int → Node
  | .quotation item, value => .quotation item.position value
  | .derived _ rule _ left _ right, value => .derived rule left right value

def recordValues : (kinds : List Deduction.Kind) → Values Deduction.Value kinds → List Node
  | [], _ => []
  | kind :: rest, values => recordKind kind values.1 :: recordValues rest values.2

/-- Recording reads the actual resource tuple, including distinct occurrence
positions. Exact formation recovery additionally requires the canonical-layer
certificate; it is not asserted for arbitrary resource producers. -/
def record {context sources contract policy}
    (store : @Deduction.Store context sources contract policy) : List Node :=
  recordValues store.1 store.2.resources.values

def restoreQuotation {context sources contract policy kinds}
    (old : @Deduction.Knowledge context sources contract policy kinds)
    (output : Output sources contract) (saved : Int)
    (same : saved = Int.ofNat output.item.passage.value) :
    Deduction.Knowledge sources contract policy (.quotation output.item :: kinds) where
  resources := ⟨(saved, old.resources.values), by
    rw [same]
    exact .produced old.resources.formation (Deduction.quotationProducer output)⟩
  valid := fun ref => match ref with
    | .here => same.symm ▸ Deduction.Justified.quotation output.item output.evidence
    | .prior prior => old.valid prior

theorem restoreQuotation_value {context sources contract policy kinds}
    (old : @Deduction.Knowledge context sources contract policy kinds)
    (output : Output sources contract) (saved : Int) (same : saved = Int.ofNat output.item.passage.value) :
    (restoreQuotation old output saved same).resources.read .here = saved := rfl

theorem restoreQuotation_previous {context sources contract policy kinds kind}
    (old : @Deduction.Knowledge context sources contract policy kinds)
    (output : Output sources contract) (saved : Int) (same : saved = Int.ofNat output.item.passage.value)
    (prior : Ref kinds kind) :
    (restoreQuotation old output saved same).resources.read (.prior prior) = old.resources.read prior := rfl

def restoreDerived {context sources contract policy kinds left right}
    (old : @Deduction.Knowledge context sources contract policy kinds)
    (request : Deduction.Request policy) (permission : Ref policy.allowed request.2.position)
    (leftRef : Ref kinds left) (rightRef : Ref kinds right) (saved : Int)
    (same : saved = Deduction.evaluate request.1.operation (old.resources.read leftRef) (old.resources.read rightRef)) :
    Deduction.Knowledge sources contract policy (Deduction.derivedKind request leftRef rightRef :: kinds) where
  resources := ⟨(saved, old.resources.values), by
    rw [same]
    exact .produced old.resources.formation (Deduction.producer request leftRef rightRef)⟩
  valid := fun ref => match ref with
    | .here => same.symm ▸ Deduction.Justified.derived request permission leftRef.position rightRef.position
        (old.valid leftRef) (old.valid rightRef)
    | .prior prior => old.valid prior

theorem restoreDerived_value {context sources contract policy kinds left right}
    (old : @Deduction.Knowledge context sources contract policy kinds)
    (request : Deduction.Request policy) (permission : Ref policy.allowed request.2.position)
    (leftRef : Ref kinds left) (rightRef : Ref kinds right) (saved : Int)
    (same : saved = Deduction.evaluate request.1.operation (old.resources.read leftRef) (old.resources.read rightRef)) :
    (restoreDerived old request permission leftRef rightRef saved same).resources.read .here = saved := rfl

theorem restoreDerived_previous {context sources contract policy kinds left right kind}
    (old : @Deduction.Knowledge context sources contract policy kinds)
    (request : Deduction.Request policy) (permission : Ref policy.allowed request.2.position)
    (leftRef : Ref kinds left) (rightRef : Ref kinds right) (saved : Int)
    (same : saved = Deduction.evaluate request.1.operation (old.resources.read leftRef) (old.resources.read rightRef))
    (prior : Ref kinds kind) :
    (restoreDerived old request permission leftRef rightRef saved same).resources.read (.prior prior) = old.resources.read prior := rfl

def require {α : Type u} (error : Error) : Option α → Except Error α
  | none => .error error
  | some value => .ok value

def loadNode {context} (sources : Support SourceValue context) (contract : Contract) (policy : Deduction.Policy)
    (old : Deduction.Store sources contract policy) : Node → Except Error (Deduction.Store sources contract policy)
  | .quotation source saved => do
      let origin ← require .sourceMissing (Adaptive.locate context source)
      let permission ← require .sourceForbidden (resolvePermission contract.allowed origin.2.position)
      let item := sourceCitation sources origin
      let output : Output sources contract := ⟨item, ⟨⟨origin, rfl, rfl, rfl⟩, permission⟩⟩
      if same : saved = Int.ofNat item.passage.value then
        return ⟨.quotation item :: old.1, restoreQuotation old.2 output saved same⟩
      else throw .valueChanged
  | .derived rule left right saved => do
      let request ← require .ruleMissing (Adaptive.locate policy.rules rule)
      let permission ← require .ruleForbidden (resolvePermission policy.allowed request.2.position)
      let leftRef ← require .premiseMissing (Adaptive.locate old.1 left)
      let rightRef ← require .premiseMissing (Adaptive.locate old.1 right)
      if same : saved = Deduction.evaluate request.1.operation (old.2.resources.read leftRef.2) (old.2.resources.read rightRef.2) then
        return ⟨Deduction.derivedKind request leftRef.2 rightRef.2 :: old.1,
          restoreDerived old.2 request permission leftRef.2 rightRef.2 saved same⟩
      else throw .valueChanged

/-- Newest node first on the wire; premises refer to the earlier saved tuple.
No resource-producing operation is called by this restoration function. -/
def loadStore {context} (sources : Support SourceValue context) (contract : Contract) (policy : Deduction.Policy) :
    List Node → Except Error (Deduction.Store sources contract policy)
  | [] => .ok ⟨[], Deduction.empty sources contract policy⟩
  | node :: rest => do
      let old ← loadStore sources contract policy rest
      loadNode sources contract policy old node

structure Bound {context sources contract policy}
    (store : @Deduction.Store context sources contract policy) (spec : Specification) where
  occurrence : Occurrence store
  meets : Holds spec occurrence.1 (store.2.resources.read occurrence.2)

def loadBound {context sources contract policy}
    (store : @Deduction.Store context sources contract policy) (spec : Specification) (position : Nat) :
    Option (Bound store spec) := do
  let found ← Adaptive.locate store.1 position
  match holdsDecision spec found.1 (store.2.resources.read found.2) with
  | .isTrue correct => some ⟨found, correct⟩
  | .isFalse _ => none

inductive Table {context sources contract policy}
    (store : @Deduction.Store context sources contract policy) : List Specification → Type where
  | nil : Table store []
  | cons {spec rest} (head : Bound store spec) (tail : Table store rest) : Table store (spec :: rest)

def Table.read {context sources contract policy store slots spec}
    (table : @Table context sources contract policy store slots) (slot : Ref slots spec) : Bound store spec :=
  match table, slot with
  | .cons head _, .here => head
  | .cons _ tail, .prior prior => tail.read prior

def Table.positions {context sources contract policy store slots}
    (table : @Table context sources contract policy store slots) : List Nat :=
  match table with
  | .nil => []
  | .cons head tail => head.occurrence.2.position :: tail.positions

def loadTable {context sources contract policy}
    (store : @Deduction.Store context sources contract policy) :
    (slots : List Specification) → List Nat → Option (Table store slots)
  | [], [] => some .nil
  | [], _ :: _ => none
  | _ :: _, [] => none
  | spec :: rest, position :: positions => do
      let head ← loadBound store spec position
      let tail ← loadTable store rest positions
      return .cons head tail

def Table.frame {context sources contract policy store slots}
    (table : @Table context sources contract policy store slots) (dossier : Dossier.State sources contract) :
    Frame sources contract policy slots := ⟨dossier, store, fun slot => some (table.read slot).occurrence⟩

def Table.complete {context sources contract policy store slots}
    (table : @Table context sources contract policy store slots) (dossier : Dossier.State sources contract) :
    Complete (table.frame dossier) := fun slot => ⟨(table.read slot).occurrence, rfl, (table.read slot).meets⟩

/-- A single remaining conclusion: the actual execution is stored alongside its
positive delivered occurrence. Completion consumes that same action. -/
structure Finished {context sources contract policy}
    (old : @Deduction.Store context sources contract policy)
    (request : Deduction.Request policy) (left right : Occurrence old) (demand : Deduction.Demand) where
  decision : Deduction.Decision old.2 request left.2 right.2
  actual : decision = Deduction.execute old.2 request left.2 right.2
  store : Deduction.Store sources contract policy
  output : Bound store (.conclusion demand)
  incorporated : store = decision.result.1

def finish {context sources contract policy leftSpec rightSpec}
    (old : @Deduction.Store context sources contract policy) (request : Deduction.Request policy)
    (left : Bound old leftSpec) (right : Bound old rightSpec) (demand : Deduction.Demand)
    (compatible : Compatible policy request leftSpec rightSpec demand) :
    Finished old request left.occurrence right.occurrence demand :=
  match actual : Deduction.execute old.2 request left.occurrence.2 right.occurrence.2 with
  | .refused absent => False.elim (resolvePermission_none policy.allowed request.2.position absent compatible.permission)
  | .accepted action permission =>
      let produced := Deduction.incorporateDerived action permission
      let correct := compatible.law left.occurrence.1 right.occurrence.1
        left.occurrence.2.position right.occurrence.2.position
        (old.2.resources.read left.occurrence.2) (old.2.resources.read right.occurrence.2) left.meets right.meets
      ⟨.accepted action permission, actual.symm,
        ⟨Deduction.derivedKind request left.occurrence.2 right.occurrence.2 :: old.1, produced⟩,
        ⟨⟨Deduction.derivedKind request left.occurrence.2 right.occurrence.2, .here⟩,
          action.value.symm ▸ correct⟩, rfl⟩

theorem finish_meets {context sources contract policy leftSpec rightSpec}
    (old : @Deduction.Store context sources contract policy) (request : Deduction.Request policy)
    (left : Bound old leftSpec) (right : Bound old rightSpec) (demand : Deduction.Demand)
    (compatible : Compatible policy request leftSpec rightSpec demand) :
    Holds (.conclusion demand) (finish old request left right demand compatible).output.occurrence.1
      ((finish old request left right demand compatible).store.2.resources.read
        (finish old request left right demand compatible).output.occurrence.2) :=
  (finish old request left right demand compatible).output.meets

end ConstitutiveSearch.Agent.Local.Documentary.Portable
/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Portable.Node
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Portable.Error
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Portable.recordKind
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Portable.recordValues
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Portable.record
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Portable.restoreQuotation
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Portable.restoreQuotation_value
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Portable.restoreQuotation_previous
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Portable.restoreDerived
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Portable.restoreDerived_value
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Portable.restoreDerived_previous
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Portable.require
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Portable.loadNode
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Portable.loadStore
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Portable.Bound
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Portable.loadBound
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Portable.Table
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Portable.Table.read
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Portable.Table.positions
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Portable.loadTable
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Portable.Table.frame
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Portable.Table.complete
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Portable.Finished
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Portable.finish
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Portable.finish_meets
/- AXIOM_AUDIT_END -/
