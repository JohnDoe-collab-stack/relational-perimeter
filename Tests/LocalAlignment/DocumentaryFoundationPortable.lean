import Tests.LocalAlignment.DocumentaryControlCodec
import RelationalPerimeter.Computation.ConstitutiveGeneration

/-! A constructor codec for the complete free constitution. The code follows
the retained root/formed constructors, rather than asking a generator to
produce a constitution from its depth. Exactness includes the dependent
boundary, compatible formation term, obstruction and provenance fields. -/
set_option genInjectivity false
set_option maxHeartbeats 4000000
namespace ConstitutiveSearch.Agent.Local.Documentary.FoundationPortable
open StrongPerimetralTurning
open ControlCodec

inductive Tree where
  | root
  | formed (prior : Tree)
deriving DecidableEq

def Tree.level : Tree → Nat
  | .root => 0
  | .formed prior => prior.level + 1

theorem level_injective (left right : Tree) (same : left.level = right.level) : left = right := by
  induction left generalizing right with
  | root =>
      cases right with
      | root => rfl
      | formed right => exact False.elim (Nat.noConfusion same)
  | formed left ih =>
      cases right with
      | root => exact False.elim (Nat.noConfusion same)
      | formed right => exact congrArg Tree.formed (ih right (Nat.succ.inj same))

/-- Constructor interpretation only: no call to the historical generator. -/
def extendFields {P : CircularPresentation} (prior : PositiveConstitution P) :
    PositiveConstitution P :=
  let layer : FreeKCore P prior.1 prior.2.1.1 :=
    { formationTerm := .admissible (successorCompatibleExplicitation prior.1)
      formationTermIsSuccessor := rfl
      integratedClosureObstruction := prior.2.1.1.inheritedClosureObstruction
      integratedClosureObstructionIsCurrent := rfl
      integratedProvenance := provenanceAtCursor prior.1
      integratedProvenanceIsCurrent := rfl }
  ⟨advanceCursor prior.1,
    ⟨.afterFormation prior.2.1.1 layer.formationTerm layer.formationTermIsSuccessor,
      .formed prior.2.1.2 layer⟩, .exact⟩

def materialize (P : CircularPresentation) : Tree → PositiveConstitution P
  | .root => ⟨.within P.perimeter, ⟨.initial P.positiveClosureObstruction, .root⟩, .exact⟩
  | .formed prior => extendFields (materialize P prior)

/-- The recursion reads the actual retained formation constructors. -/
def coreTree {P : CircularPresentation} :
    {cursor : PerimeterCursor P} → {difference : BoundaryDifferenceCode P cursor} →
      FreeConstitutionCore P cursor difference → Tree
  | _, _, .root => .root
  | _, _, .formed prior _layer => .formed (coreTree prior)

def capture {P : CircularPresentation} (value : PositiveConstitution P) : Tree :=
  coreTree value.2.1.2

theorem core_level {P : CircularPresentation} {cursor difference}
    (core : FreeConstitutionCore P cursor difference) :
    (coreTree core).level = ConstitutiveGeneration.formationDepth core := by
  induction core with
  | root => rfl
  | formed prior layer ih => exact congrArg Nat.succ ih

theorem capture_level {P : CircularPresentation} (value : PositiveConstitution P) :
    (capture value).level = ConstitutiveGeneration.positiveDepth value := core_level value.2.1.2

theorem core_exact {P : CircularPresentation} {cursor difference}
    (core : FreeConstitutionCore P cursor difference) :
    materialize P (coreTree core) =
      (⟨cursor, ⟨difference, core⟩, .exact⟩ : PositiveConstitution P) := by
  induction core with
  | root => rfl
  | @formed cursor difference prior layer ih =>
      cases layer with
      | mk term termExact obstruction obstructionExact provenance provenanceExact =>
          cases termExact
          cases obstructionExact
          cases provenanceExact
          change extendFields (materialize P (coreTree prior)) =
            extendFields (⟨cursor, ⟨difference, prior⟩, .exact⟩ : PositiveConstitution P)
          exact congrArg extendFields ih

theorem capture_exact {P : CircularPresentation} (value : PositiveConstitution P) :
    materialize P (capture value) = value := by
  rcases value with ⟨cursor, ⟨difference, core⟩, boundary⟩
  cases boundary
  exact core_exact core

theorem capture_materialized (P : CircularPresentation) (tree : Tree) :
    capture (materialize P tree) = tree := by
  induction tree with
  | root => rfl
  | formed prior ih =>
      change Tree.formed (capture (materialize P prior)) = Tree.formed prior
      exact congrArg Tree.formed ih

def treeWords : Tree → Words
  | .root => [0]
  | .formed prior => 1 :: treeWords prior

def readTree : Words → Option (Tree × Words)
  | [] => none
  | word :: tail => match word with
    | .negSucc _ => none
    | .ofNat tag => match tag with
      | 0 => some (.root, tail)
      | 1 => do
          let (prior, rest) ← readTree tail
          return (.formed prior, rest)
      | _ + 2 => none

theorem tree_exact (tree : Tree) (tail : Words) :
    readTree (treeWords tree ++ tail) = some (tree, tail) := by
  induction tree with
  | root => rfl
  | formed prior ih =>
      change (do let (prior, rest) ← readTree (treeWords prior ++ tail)
                 pure (Tree.formed prior, rest)) = _
      rw [ih]
      rfl

def treeCodec : Codec Tree := ⟨treeWords, readTree, tree_exact⟩

def envelope : Codec Tree :=
  (natural.product (natural.product treeCodec)).via
    (fun tree => (90, 1, tree))
    (fun data => match data.1 with
      | 90 => match data.2.1 with | 1 => some data.2.2 | _ => none
      | _ => none)
    (fun _ => rfl)

def save {P : CircularPresentation} (value : PositiveConstitution P) : List UInt8 :=
  bytes (envelope.words (capture value))

def load (input : List UInt8) : Option Tree := do
  let words ← fromBytes input
  let (tree, tail) ← envelope.read words
  match tail with | [] => some tree | _ :: _ => none

def restore (P : CircularPresentation) (input : List UInt8) : Option (PositiveConstitution P) :=
  (load input).map (materialize P)

theorem byte_roundtrip {P : CircularPresentation} (value : PositiveConstitution P) :
    load (save value) = some (capture value) := by
  unfold load save
  rw [bytes_exact]
  dsimp only [Bind.bind, Option.bind]
  have actual := envelope.exact (capture value) []
  rw [PortableCheckpoint.append_empty] at actual
  rw [actual]

theorem restored_exact {P : CircularPresentation} (value : PositiveConstitution P) :
    restore P (save value) = some value := by
  unfold restore
  rw [byte_roundtrip]
  change some (materialize P (capture value)) = _
  rw [capture_exact]

theorem all_consumers {P : CircularPresentation} (value : PositiveConstitution P)
    {Result : Type u} (future : PositiveConstitution P → Result) :
    (restore P (save value)).map future = some (future value) := by
  rw [restored_exact]
  rfl

end ConstitutiveSearch.Agent.Local.Documentary.FoundationPortable

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Agent.Local.Documentary.FoundationPortable.Tree
#print axioms ConstitutiveSearch.Agent.Local.Documentary.FoundationPortable.Tree.level
#print axioms ConstitutiveSearch.Agent.Local.Documentary.FoundationPortable.level_injective
#print axioms ConstitutiveSearch.Agent.Local.Documentary.FoundationPortable.extendFields
#print axioms ConstitutiveSearch.Agent.Local.Documentary.FoundationPortable.materialize
#print axioms ConstitutiveSearch.Agent.Local.Documentary.FoundationPortable.coreTree
#print axioms ConstitutiveSearch.Agent.Local.Documentary.FoundationPortable.capture
#print axioms ConstitutiveSearch.Agent.Local.Documentary.FoundationPortable.core_level
#print axioms ConstitutiveSearch.Agent.Local.Documentary.FoundationPortable.capture_level
#print axioms ConstitutiveSearch.Agent.Local.Documentary.FoundationPortable.core_exact
#print axioms ConstitutiveSearch.Agent.Local.Documentary.FoundationPortable.capture_exact
#print axioms ConstitutiveSearch.Agent.Local.Documentary.FoundationPortable.capture_materialized
#print axioms ConstitutiveSearch.Agent.Local.Documentary.FoundationPortable.treeWords
#print axioms ConstitutiveSearch.Agent.Local.Documentary.FoundationPortable.readTree
#print axioms ConstitutiveSearch.Agent.Local.Documentary.FoundationPortable.tree_exact
#print axioms ConstitutiveSearch.Agent.Local.Documentary.FoundationPortable.treeCodec
#print axioms ConstitutiveSearch.Agent.Local.Documentary.FoundationPortable.envelope
#print axioms ConstitutiveSearch.Agent.Local.Documentary.FoundationPortable.save
#print axioms ConstitutiveSearch.Agent.Local.Documentary.FoundationPortable.load
#print axioms ConstitutiveSearch.Agent.Local.Documentary.FoundationPortable.restore
#print axioms ConstitutiveSearch.Agent.Local.Documentary.FoundationPortable.byte_roundtrip
#print axioms ConstitutiveSearch.Agent.Local.Documentary.FoundationPortable.restored_exact
#print axioms ConstitutiveSearch.Agent.Local.Documentary.FoundationPortable.all_consumers
/- AXIOM_AUDIT_END -/
