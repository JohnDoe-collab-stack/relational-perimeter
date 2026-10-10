import Tests.LocalAlignment.DocumentaryPortable

/-! A deliberately restricted physical checkpoint schema: the received fixture
after all three quotations, with one sum task remaining. It does not restore a
master cursor or promise later quotations or arbitrary adaptive continuations. -/
set_option genInjectivity false
set_option maxHeartbeats 2000000
namespace ConstitutiveSearch.Agent.Local.Documentary.PortableCheckpoint
open Resources Program Portable

def context : List SourceKey := [⟨0, 2, 0⟩, ⟨1, 1, 0⟩, ⟨1, 2, 0⟩]
def sources : Support SourceValue context := .given
  (⟨7, 42, "La mesure certifiee est 42."⟩, ⟨7, 42, "La mesure certifiee est 42."⟩,
    ⟨7, 43, "La mesure revisee est 43."⟩, PUnit.unit)
def contract : Contract := ⟨[1, 2]⟩
def policy : Deduction.Policy := ⟨[⟨101, .difference⟩, ⟨102, .sum⟩, ⟨101, .difference⟩], [0, 1]⟩
def difference : Deduction.Request policy := ⟨⟨101, .difference⟩, .here⟩
def sum : Deduction.Request policy := ⟨⟨102, .sum⟩, .prior .here⟩
def baseline : Specification := .quotation ⟨7, 42, some 1⟩
def revision : Specification := .quotation ⟨7, 43, some 2⟩
def delta : Specification := .conclusion ⟨1, some 0, some [1, 2]⟩
def demand : Deduction.Demand := ⟨2, some 1, some [1, 2, 1, 2]⟩
def slots : List Specification := [baseline, delta, revision, baseline]

def compatible : Compatible policy sum delta delta demand :=
  ⟨.prior .here, fun left right lp rp lv rv leftMeets rightMeets =>
    ⟨by rw [leftMeets.1, rightMeets.1]; rfl, rfl, by
      change left.origins ++ right.origins = [1, 2, 1, 2]
      rw [leftMeets.2.2, rightMeets.2.2]
      rfl⟩⟩

structure Saved where
  version : Nat
  schema : Nat
  round : Nat
  depth : Nat
  nodes : List Node
  bindings : List Nat
  task : Nat

structure Loaded where
  store : Deduction.Store sources contract policy
  table : Table store slots
  round : Nat
  depth : Nat

def captureBindings {store} : (slots : List Specification) →
    ({spec : Specification} → Ref slots spec → Option (Occurrence (store : Deduction.Store sources contract policy))) →
    Option (List Nat)
  | [], _ => some []
  | _ :: rest, bindings => do
      let head ← bindings .here
      let tail ← captureBindings rest (fun slot => bindings (.prior slot))
      return head.2.position :: tail

def save (frame : Frame sources contract policy slots) (round : Nat) : Option Saved := do
  let bindings ← captureBindings slots frame.bindings
  return ⟨1, 1, round, frame.dossier.cursor.depth, record frame.store, bindings, 1⟩

inductive LoadError where
  | version | schema | boundary | task | store (reason : Portable.Error) | bindings

def load (saved : Saved) : Except LoadError Loaded := do
  if saved.version != 1 then throw .version
  if saved.schema != 1 then throw .schema
  if saved.round != 4 || saved.depth != 3 || saved.nodes.length != 4 then throw .boundary
  if saved.task != 1 then throw .task
  let store ← (loadStore sources contract policy saved.nodes).mapError LoadError.store
  match loadTable store slots saved.bindings with
  | none => throw .bindings
  | some table => return ⟨store, table, saved.round, saved.depth⟩

def resume (loaded : Loaded) : Finished loaded.store sum
    (loaded.table.read (.prior .here)).occurrence (loaded.table.read (.prior .here)).occurrence demand :=
  finish loaded.store sum (loaded.table.read (.prior .here)) (loaded.table.read (.prior .here)) demand compatible

theorem continuation_value (loaded : Loaded) :
    (resume loaded).store.2.resources.read (resume loaded).output.occurrence.2 = 2 :=
  (resume loaded).output.meets.1

theorem continuation_origins (loaded : Loaded) :
    (resume loaded).output.occurrence.1.origins = [1, 2, 1, 2] :=
  (resume loaded).output.meets.2.2

def integerParts : Int → List String
  | .ofNat n => [Nat.repr n]
  | .negSucc n => ["-", Nat.repr (n + 1)]

def positionsParts : List Nat → List String
  | [] => []
  | [position] => [Nat.repr position]
  | position :: next :: rest => Nat.repr position :: "," :: positionsParts (next :: rest)

def sourceParts : List (Output sources contract) → List String
  | [] => []
  | output :: rest =>
      ["[document=", Nat.repr output.item.source.document, " version=", Nat.repr output.item.source.version,
      " excerpt=", Nat.repr output.item.source.excerpt, " position=", Nat.repr output.item.position, "] ",
      output.item.passage.text, "\n"] ++ sourceParts rest

def renderBytes : List String → List UInt8
  | [] => []
  | part :: rest => part.toUTF8.data.toList ++ renderBytes rest

def render (store : Deduction.Store sources contract policy) (output : Bound store (.conclusion demand)) : ByteArray :=
  let evidence := store.2.valid output.occurrence.2
  ⟨(renderBytes (["Dossier documentaire\nConclusion : "] ++ integerParts (store.2.resources.read output.occurrence.2) ++
    ["\nOccurrence : ", Nat.repr output.occurrence.2.position, "\nOrigines : "] ++ positionsParts output.occurrence.1.origins ++
    ["\nRegles : "] ++ positionsParts evidence.rules ++ ["\nSources :\n"] ++ sourceParts evidence.sources)).toArray⟩

def nodeWords : Node → List Int
  | .quotation source value => [0, Int.ofNat source, value]
  | .derived rule left right value => [1, Int.ofNat rule, Int.ofNat left, Int.ofNat right, value]

def nodesWords : List Node → List Int
  | [] => []
  | node :: rest => nodeWords node ++ nodesWords rest

def natural : Int → Option Nat
  | .ofNat n => some n
  | .negSucc _ => none

def readNode : List Int → Option (Node × List Int)
  | [] => none
  | tag :: rest => match tag with
    | .negSucc _ => none
    | .ofNat n => match n with
      | 0 => match rest with
        | source :: value :: tail => do return (.quotation (← natural source) value, tail)
        | [] => none
        | [_] => none
      | 1 => match rest with
        | rule :: left :: right :: value :: tail => do
            return (.derived (← natural rule) (← natural left) (← natural right) value, tail)
        | [] => none
        | [_] => none
        | [_, _] => none
        | [_, _, _] => none
      | _ + 2 => none

def readNodes : Nat → List Int → Option (List Node × List Int)
  | 0, rest => some ([], rest)
  | n + 1, words => do
      let (node, rest) ← readNode words
      let (nodes, tail) ← readNodes n rest
      return (node :: nodes, tail)

theorem nodes_roundtrip (nodes : List Node) (tail : List Int) :
    readNodes nodes.length (nodesWords nodes ++ tail) = some (nodes, tail) := by
  induction nodes with
  | nil => rfl
  | cons node rest ih =>
      cases node with
      | quotation source value =>
          change (do let (nodes, last) ← readNodes rest.length (nodesWords rest ++ tail)
                     pure (Node.quotation source value :: nodes, last)) = _
          rw [ih]
          rfl
      | derived rule left right value =>
          change (do let (nodes, last) ← readNodes rest.length (nodesWords rest ++ tail)
                     pure (Node.derived rule left right value :: nodes, last)) = _
          rw [ih]
          rfl

def bindingWords : List Nat → List Int
  | [] => []
  | position :: rest => Int.ofNat position :: bindingWords rest

def readBindings : Nat → List Int → Option (List Nat × List Int)
  | 0, rest => some ([], rest)
  | _ + 1, [] => none
  | n + 1, word :: rest => do
      let position ← natural word
      let (positions, tail) ← readBindings n rest
      return (position :: positions, tail)

theorem bindings_roundtrip (positions : List Nat) (tail : List Int) :
    readBindings positions.length (bindingWords positions ++ tail) = some (positions, tail) := by
  induction positions with
  | nil => rfl
  | cons position rest ih =>
      change (do let (positions, last) ← readBindings rest.length (bindingWords rest ++ tail)
                 pure (position :: positions, last)) = _
      rw [ih]
      rfl

def words (saved : Saved) : List Int :=
  [Int.ofNat saved.version, Int.ofNat saved.schema, Int.ofNat saved.round, Int.ofNat saved.depth,
    Int.ofNat saved.task, Int.ofNat saved.nodes.length, Int.ofNat saved.bindings.length] ++
    nodesWords saved.nodes ++ bindingWords saved.bindings

def fromWords : List Int → Option Saved
  | version :: schema :: round :: depth :: task :: count :: bindings :: rest => do
      let version ← natural version
      let schema ← natural schema
      let round ← natural round
      let depth ← natural depth
      let task ← natural task
      let count ← natural count
      let bindings ← natural bindings
      let (nodes, rest) ← readNodes count rest
      let (positions, tail) ← readBindings bindings rest
      match tail with
      | [] => return ⟨version, schema, round, depth, nodes, positions, task⟩
      | _ :: _ => none
  | [] => none
  | [_] => none
  | [_, _] => none
  | [_, _, _] => none
  | [_, _, _, _] => none
  | [_, _, _, _, _] => none
  | [_, _, _, _, _, _] => none

theorem append_empty {α : Type u} (xs : List α) : xs ++ [] = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => exact congrArg (List.cons x) ih

theorem append_associative {α : Type u} (xs ys zs : List α) : (xs ++ ys) ++ zs = xs ++ (ys ++ zs) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => exact congrArg (List.cons x) ih

theorem words_roundtrip (saved : Saved) : fromWords (words saved) = some saved := by
  cases saved with
  | mk version schema round depth nodes bindings task =>
      unfold words fromWords
      change (do let (nodes, rest) ← readNodes nodes.length (nodesWords nodes ++ bindingWords bindings)
                 let (positions, tail) ← readBindings bindings.length rest
                 match tail with
                 | [] => pure (Saved.mk version schema round depth nodes positions task)
                 | _ :: _ => none) = _
      rw [nodes_roundtrip]
      change (do let (positions, tail) ← readBindings bindings.length (bindingWords bindings)
                 match tail with
                 | [] => pure (Saved.mk version schema round depth nodes positions task)
                 | _ :: _ => none) = _
      have parsed := bindings_roundtrip bindings []
      rw [append_empty] at parsed
      rw [parsed]
      rfl

def unary : Nat → List Nat
  | 0 => [2]
  | n + 1 => 1 :: unary n

def readUnary : List Nat → Option (Nat × List Nat)
  | [] => none
  | 0 :: _ => none
  | 1 :: rest => do let (n, tail) ← readUnary rest; return (n + 1, tail)
  | 2 :: rest => some (0, rest)
  | (_ + 3) :: _ => none

theorem unary_roundtrip (n : Nat) (tail : List Nat) : readUnary (unary n ++ tail) = some (n, tail) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change (do let (n, tail) ← readUnary (unary n ++ tail); pure (n + 1, tail)) = _
      rw [ih]
      rfl

def wordBytes : Int → List Nat
  | .ofNat n => 0 :: unary n
  | .negSucc n => 1 :: unary n

def readWord : List Nat → Option (Int × List Nat)
  | [] => none
  | 0 :: rest => do let (n, tail) ← readUnary rest; return (Int.ofNat n, tail)
  | 1 :: rest => do let (n, tail) ← readUnary rest; return (Int.negSucc n, tail)
  | (_ + 2) :: _ => none

theorem word_roundtrip (value : Int) (tail : List Nat) : readWord (wordBytes value ++ tail) = some (value, tail) := by
  cases value with
  | ofNat n =>
      change (do let (n, tail) ← readUnary (unary n ++ tail); pure (Int.ofNat n, tail)) = _
      rw [unary_roundtrip]
      rfl
  | negSucc n =>
      change (do let (n, tail) ← readUnary (unary n ++ tail); pure (Int.negSucc n, tail)) = _
      rw [unary_roundtrip]
      rfl

def bodyBytes : List Int → List Nat
  | [] => []
  | value :: rest => wordBytes value ++ bodyBytes rest

def readBody : Nat → List Nat → Option (List Int × List Nat)
  | 0, rest => some ([], rest)
  | n + 1, bytes => do
      let (value, tail) ← readWord bytes
      let (rest, last) ← readBody n tail
      return (value :: rest, last)

theorem body_roundtrip (values : List Int) (tail : List Nat) :
    readBody values.length (bodyBytes values ++ tail) = some (values, tail) := by
  induction values with
  | nil => rfl
  | cons value rest ih =>
      change readBody (rest.length + 1) ((wordBytes value ++ bodyBytes rest) ++ tail) = _
      rw [append_associative]
      change (do let (value, tail) ← readWord (wordBytes value ++ (bodyBytes rest ++ tail))
                 let (rest, last) ← readBody rest.length tail
                 pure (value :: rest, last)) = _
      rw [word_roundtrip]
      change (do let (rest, last) ← readBody rest.length (bodyBytes rest ++ tail)
                 pure (value :: rest, last)) = _
      rw [ih]
      rfl

/-- Byte alphabet 0,1,2; sign and length are explicit. Unary encoding keeps this
first reference codec small and constructively auditable; it is not a storage
efficiency claim. -/
def encode (saved : Saved) : List Nat :=
  wordBytes (Int.ofNat (words saved).length) ++ bodyBytes (words saved)

def decode (bytes : List Nat) : Option Saved := do
  let (size, rest) ← readWord bytes
  let size ← natural size
  let (words, tail) ← readBody size rest
  match tail with
  | [] => fromWords words
  | _ :: _ => none

theorem codec_roundtrip (saved : Saved) : decode (encode saved) = some saved := by
  unfold decode encode
  rw [word_roundtrip]
  change (do let (words, tail) ← readBody (words saved).length (bodyBytes (words saved))
             match tail with
             | [] => fromWords words
             | _ :: _ => none) = _
  have parsed := body_roundtrip (words saved) []
  rw [append_empty] at parsed
  rw [parsed]
  exact words_roundtrip saved

def Alphabet : List Nat → Prop
  | [] => True
  | value :: rest => (value = 0 ∨ value = 1 ∨ value = 2) ∧ Alphabet rest

theorem alphabet_append (left right : List Nat) (first : Alphabet left) (last : Alphabet right) :
    Alphabet (left ++ right) := by
  induction left with
  | nil => exact last
  | cons value rest ih => exact ⟨first.1, ih first.2⟩

theorem unary_alphabet (value : Nat) : Alphabet (unary value) := by
  induction value with
  | zero => exact ⟨Or.inr (Or.inr rfl), True.intro⟩
  | succ value ih => exact ⟨Or.inr (Or.inl rfl), ih⟩

theorem word_alphabet (value : Int) : Alphabet (wordBytes value) := by
  cases value with
  | ofNat n => exact ⟨Or.inl rfl, unary_alphabet n⟩
  | negSucc n => exact ⟨Or.inr (Or.inl rfl), unary_alphabet n⟩

theorem body_alphabet (values : List Int) : Alphabet (bodyBytes values) := by
  induction values with
  | nil => exact True.intro
  | cons value rest ih => exact alphabet_append _ _ (word_alphabet value) ih

theorem encode_alphabet (saved : Saved) : Alphabet (encode saved) :=
  alphabet_append _ _ (word_alphabet _) (body_alphabet _)

def toBytes : List Nat → List UInt8
  | [] => []
  | value :: rest => UInt8.ofNat value :: toBytes rest

def fromBytes : List UInt8 → List Nat
  | [] => []
  | value :: rest => value.toNat :: fromBytes rest

theorem alphabet_byte_roundtrip (values : List Nat) (valid : Alphabet values) :
    fromBytes (toBytes values) = values := by
  induction values with
  | nil => rfl
  | cons value rest ih =>
      have byte : (UInt8.ofNat value).toNat = value := by
        cases valid.1 with
        | inl zero => rw [zero]; rfl
        | inr other => cases other with
          | inl one => rw [one]; rfl
          | inr two => rw [two]; rfl
      change (UInt8.ofNat value).toNat :: fromBytes (toBytes rest) = value :: rest
      rw [byte, ih valid.2]

theorem physical_byte_codec_roundtrip (saved : Saved) :
    decode (fromBytes (toBytes (encode saved))) = some saved := by
  rw [alphabet_byte_roundtrip _ (encode_alphabet saved)]
  exact codec_roundtrip saved

end ConstitutiveSearch.Agent.Local.Documentary.PortableCheckpoint
/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableCheckpoint.context
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableCheckpoint.sources
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableCheckpoint.contract
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableCheckpoint.policy
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableCheckpoint.difference
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableCheckpoint.sum
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableCheckpoint.baseline
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableCheckpoint.revision
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableCheckpoint.delta
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableCheckpoint.demand
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableCheckpoint.slots
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableCheckpoint.compatible
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableCheckpoint.Saved
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableCheckpoint.Loaded
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableCheckpoint.captureBindings
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableCheckpoint.save
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableCheckpoint.LoadError
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableCheckpoint.load
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableCheckpoint.resume
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableCheckpoint.continuation_value
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableCheckpoint.continuation_origins
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableCheckpoint.integerParts
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableCheckpoint.positionsParts
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableCheckpoint.sourceParts
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableCheckpoint.renderBytes
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableCheckpoint.render
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableCheckpoint.nodeWords
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableCheckpoint.nodesWords
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableCheckpoint.natural
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableCheckpoint.readNode
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableCheckpoint.readNodes
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableCheckpoint.nodes_roundtrip
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableCheckpoint.bindingWords
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableCheckpoint.readBindings
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableCheckpoint.bindings_roundtrip
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableCheckpoint.words
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableCheckpoint.fromWords
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableCheckpoint.append_empty
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableCheckpoint.append_associative
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableCheckpoint.words_roundtrip
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableCheckpoint.unary
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableCheckpoint.readUnary
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableCheckpoint.unary_roundtrip
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableCheckpoint.wordBytes
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableCheckpoint.readWord
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableCheckpoint.word_roundtrip
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableCheckpoint.bodyBytes
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableCheckpoint.readBody
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableCheckpoint.body_roundtrip
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableCheckpoint.encode
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableCheckpoint.decode
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableCheckpoint.codec_roundtrip
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableCheckpoint.Alphabet
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableCheckpoint.alphabet_append
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableCheckpoint.unary_alphabet
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableCheckpoint.word_alphabet
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableCheckpoint.body_alphabet
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableCheckpoint.encode_alphabet
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableCheckpoint.toBytes
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableCheckpoint.fromBytes
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableCheckpoint.alphabet_byte_roundtrip
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableCheckpoint.physical_byte_codec_roundtrip
/- AXIOM_AUDIT_END -/
