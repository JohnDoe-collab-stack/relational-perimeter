import Tests.LocalAlignment.DocumentaryMemory
import Tests.LocalAlignment.DocumentaryPortableCheckpoint

/-! First-order control codecs. Codecs preserve exact values and unconsumed tails.
The finite task language and summaries have closed codecs. Contexts require an
explicit codec; Nat and finite lists/options/products are realized below.
This module encodes no master resource or documentary store. -/
set_option genInjectivity false
set_option maxHeartbeats 3000000
namespace ConstitutiveSearch.Agent.Local.Documentary.ControlCodec
open Resources Program Adaptive
abbrev Words := List Int

structure Codec (α : Type) where
  words : α → Words
  read : Words → Option (α × Words)
  exact : ∀ value tail, read (words value ++ tail) = some (value, tail)

def integer : Codec Int :=
  ⟨fun value => [value], fun input => match input with
    | [] => none | value :: tail => some (value, tail), fun _ _ => rfl⟩

def natural : Codec Nat :=
  ⟨fun value => [Int.ofNat value], fun input => match input with
    | [] => none
    | word :: tail => match word with
      | .ofNat value => some (value, tail)
      | .negSucc _ => none, fun _ _ => rfl⟩

def Codec.product {α β : Type} (left : Codec α) (right : Codec β) : Codec (α × β) where
  words := fun value => left.words value.1 ++ right.words value.2
  read := fun input => do
    let (first, tail) ← left.read input
    let (last, rest) ← right.read tail
    return ((first, last), rest)
  exact := by
    intro value tail
    rw [PortableCheckpoint.append_associative, left.exact]
    change (do let (last, rest) ← right.read (right.words value.2 ++ tail)
               pure ((value.1, last), rest)) = _
    rw [right.exact]
    rfl

def Codec.optional {α : Type} (codec : Codec α) : Codec (Option α) where
  words := fun value => match value with | none => [0] | some value => 1 :: codec.words value
  read := fun input => match input with
    | [] => none
    | word :: tail => match word with
      | .negSucc _ => none
      | .ofNat tag => match tag with
        | 0 => some (none, tail)
        | 1 => do let (value, rest) ← codec.read tail; return (some value, rest)
        | _ + 2 => none
  exact := by
    intro value tail
    cases value with
    | none => rfl
    | some value =>
        change (do let (value, rest) ← codec.read (codec.words value ++ tail)
                   pure (some value, rest)) = _
        rw [codec.exact]
        rfl

def writeList {α : Type} (codec : Codec α) : List α → Words
  | [] => []
  | value :: rest => codec.words value ++ writeList codec rest

def readList {α : Type} (codec : Codec α) : Nat → Words → Option (List α × Words)
  | 0, tail => some ([], tail)
  | count + 1, input => do
      let (value, tail) ← codec.read input
      let (rest, last) ← readList codec count tail
      return (value :: rest, last)

theorem list_exact {α : Type} (codec : Codec α) (values : List α) (tail : Words) :
    readList codec values.length (writeList codec values ++ tail) = some (values, tail) := by
  induction values with
  | nil => rfl
  | cons value rest ih =>
      change readList codec (rest.length + 1) ((codec.words value ++ writeList codec rest) ++ tail) = _
      rw [PortableCheckpoint.append_associative]
      change (do let (value, tail) ← codec.read (codec.words value ++ (writeList codec rest ++ tail))
                 let (rest, last) ← readList codec rest.length tail
                 pure (value :: rest, last)) = _
      rw [codec.exact]
      change (do let (rest, last) ← readList codec rest.length (writeList codec rest ++ tail)
                 pure (value :: rest, last)) = _
      rw [ih]
      rfl

def Codec.list {α : Type} (codec : Codec α) : Codec (List α) where
  words := fun values => Int.ofNat values.length :: writeList codec values
  read := fun input => do
    let (count, tail) ← natural.read input
    readList codec count tail
  exact := by
    intro values tail
    exact list_exact codec values tail

def Codec.via {α β : Type} (codec : Codec β) (encode : α → β)
    (decode : β → Option α) (correct : ∀ value, decode (encode value) = some value) : Codec α where
  words := fun value => codec.words (encode value)
  read := fun input => do
    let (value, tail) ← codec.read input
    let restored ← decode value
    return (restored, tail)
  exact := by
    intro value tail
    rw [codec.exact]
    change (do let restored ← decode (encode value); pure (restored, tail)) = _
    rw [correct]
    rfl

theorem Codec.injective {α : Type} (codec : Codec α) {left right : α}
    (same : codec.words left = codec.words right) : left = right := by
  have both := (codec.exact left []).symm.trans
    ((congrArg (fun input => codec.read (input ++ [])) same).trans (codec.exact right []))
  exact congrArg Prod.fst (Option.some.inj both)

def Codec.equality {α : Type} (codec : Codec α) : DecidableEq α :=
  fun left right => match decEq (codec.words left) (codec.words right) with
    | .isTrue same => .isTrue (codec.injective same)
    | .isFalse different => .isFalse (fun same => different (congrArg codec.words same))

def demand : Codec Documentary.Demand :=
  (natural.product (natural.product natural.optional)).via
    (fun value => (value.key, value.value, value.origin))
    (fun value => some ⟨value.1, value.2.1, value.2.2⟩)
    (fun value => by cases value; rfl)

def deductionDemand : Codec Deduction.Demand :=
  (integer.product (natural.optional.product natural.list.optional)).via
    (fun value => (value.value, value.rulePosition, value.origins))
    (fun value => some ⟨value.1, value.2.1, value.2.2⟩)
    (fun value => by cases value; rfl)

def specification : Codec Specification where
  words := fun value => match value with
    | .quotation value => 0 :: demand.words value
    | .conclusion value => 1 :: deductionDemand.words value
  read := fun input => match input with
    | [] => none
    | word :: tail => match word with
      | .negSucc _ => none
      | .ofNat tag => match tag with
        | 0 => do let (value, rest) ← demand.read tail; return (.quotation value, rest)
        | 1 => do let (value, rest) ← deductionDemand.read tail; return (.conclusion value, rest)
        | _ + 2 => none
  exact := by
    intro value tail
    cases value with
    | quotation value =>
        change (do let (value, rest) ← demand.read (demand.words value ++ tail)
                   pure (Specification.quotation value, rest)) = _
        rw [demand.exact]; rfl
    | conclusion value =>
        change (do let (value, rest) ← deductionDemand.read (deductionDemand.words value ++ tail)
                   pure (Specification.conclusion value, rest)) = _
        rw [deductionDemand.exact]; rfl

def route : Codec Route :=
  natural.via (fun value => match value with
    | .matched => 0 | .reversed => 1 | .absent => 2
    | .invalid => 3 | .inspected => 4 | .diverted => 5)
    (fun value => match value with
    | 0 => some .matched | 1 => some .reversed | 2 => some .absent
    | 3 => some .invalid | 4 => some .inspected | 5 => some .diverted | _ => none)
    (fun value => by cases value <;> rfl)

def event : Codec Program.Event :=
  natural.via (fun value => match value with
    | .quoted => 0 | .derived => 1 | .refused => 2 | .missing => 3)
    (fun value => match value with
    | 0 => some .quoted | 1 => some .derived | 2 => some .refused | 3 => some .missing | _ => none)
    (fun value => by cases value <;> rfl)

def readout : Codec Readout :=
  (natural.product (integer.product natural.list)).via
    (fun value => (value.position, value.value, value.origins))
    (fun value => some ⟨value.1, value.2.1, value.2.2⟩)
    (fun value => by cases value; rfl)

def summary : Codec Summary :=
  (route.product (event.list.product readout.optional)).via
    (fun value => (value.route, value.events, value.inspection))
    (fun value => some ⟨value.1, value.2.1, value.2.2⟩)
    (fun value => by cases value; rfl)

inductive Command where
  | quotation (demand : Documentary.Demand) (left right : Nat)
  | conclusion (rule left right : Nat) (demand : Deduction.Demand)

def quotationFields := demand.product (natural.product natural)
def conclusionFields := natural.product (natural.product (natural.product deductionDemand))

def command : Codec Command where
  words := fun value => match value with
    | .quotation d left right => 0 :: quotationFields.words (d, left, right)
    | .conclusion rule left right d => 1 :: conclusionFields.words (rule, left, right, d)
  read := fun input => match input with
    | [] => none
    | word :: tail => match word with
      | .negSucc _ => none
      | .ofNat tag => match tag with
        | 0 => do
            let (fields, rest) ← quotationFields.read tail
            return (.quotation fields.1 fields.2.1 fields.2.2, rest)
        | 1 => do
            let (fields, rest) ← conclusionFields.read tail
            return (.conclusion fields.1 fields.2.1 fields.2.2.1 fields.2.2.2, rest)
        | _ + 2 => none
  exact := by
    intro value tail
    cases value with
    | quotation d left right =>
        change (do let (fields, rest) ← quotationFields.read
                     (quotationFields.words (d, left, right) ++ tail)
                   pure (Command.quotation fields.1 fields.2.1 fields.2.2, rest)) = _
        rw [quotationFields.exact]; rfl
    | conclusion rule left right d =>
        change (do let (fields, rest) ← conclusionFields.read
                     (conclusionFields.words (rule, left, right, d) ++ tail)
                   pure (Command.conclusion fields.1 fields.2.1 fields.2.2.1 fields.2.2.2, rest)) = _
        rw [conclusionFields.exact]; rfl

structure Raw (Context : Type) where
  slots : List Specification
  bindings : List (Option Nat)
  remaining : List Command
  context : Context
  round : Nat
  last : Option Summary

def raw {Context : Type} (codec : Codec Context) : Codec (Raw Context) :=
  (specification.list.product (natural.optional.list.product
    (command.list.product (codec.product (natural.product summary.optional))))).via
    (fun value => (value.slots, value.bindings, value.remaining, value.context, value.round, value.last))
    (fun value => some ⟨value.1, value.2.1, value.2.2.1, value.2.2.2.1,
      value.2.2.2.2.1, value.2.2.2.2.2⟩)
    (fun value => by cases value; rfl)

def envelope {Context : Type} (codec : Codec Context) : Codec (Raw Context) where
  words := fun value => [1, 4] ++ (raw codec).words value
  read := fun input => do
    let (version, tail) ← natural.read input
    let (schema, rest) ← natural.read tail
    if version == 1 && schema == 4 then (raw codec).read rest else none
  exact := fun value tail => (raw codec).exact value tail

def bytes (words : Words) : List UInt8 :=
  PortableCheckpoint.toBytes
    (PortableCheckpoint.wordBytes (Int.ofNat words.length) ++ PortableCheckpoint.bodyBytes words)

def fromBytes (input : List UInt8) : Option Words := do
  let (length, rest) ← PortableCheckpoint.readWord (PortableCheckpoint.fromBytes input)
  let count ← PortableCheckpoint.natural length
  let (words, tail) ← PortableCheckpoint.readBody count rest
  match tail with | [] => some words | _ :: _ => none

theorem bytes_exact (words : Words) : fromBytes (bytes words) = some words := by
  unfold bytes fromBytes
  rw [PortableCheckpoint.alphabet_byte_roundtrip _
    (PortableCheckpoint.alphabet_append _ _
      (PortableCheckpoint.word_alphabet _) (PortableCheckpoint.body_alphabet _))]
  rw [PortableCheckpoint.word_roundtrip]
  change (do let (words, tail) ← PortableCheckpoint.readBody words.length (PortableCheckpoint.bodyBytes words)
             match tail with | [] => some words | _ :: _ => none) = _
  have parsed := PortableCheckpoint.body_roundtrip words []
  rw [PortableCheckpoint.append_empty] at parsed
  rw [parsed]
  rfl

def save {Context : Type} (codec : Codec Context) (value : Raw Context) : List UInt8 :=
  bytes ((envelope codec).words value)

def load {Context : Type} (codec : Codec Context) (input : List UInt8) : Option (Raw Context) := do
  let words ← fromBytes input
  let (value, tail) ← (envelope codec).read words
  match tail with | [] => some value | _ :: _ => none

theorem byte_roundtrip {Context : Type} (codec : Codec Context) (value : Raw Context) :
    load codec (save codec value) = some value := by
  unfold load save
  rw [bytes_exact]
  have parsed := (envelope codec).exact value []
  rw [PortableCheckpoint.append_empty] at parsed
  change (do let (value, tail) ← (envelope codec).read ((envelope codec).words value)
             match tail with | [] => some value | _ :: _ => none) = _
  rw [parsed]
  rfl

end ConstitutiveSearch.Agent.Local.Documentary.ControlCodec

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlCodec.Words
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlCodec.Codec
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlCodec.integer
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlCodec.natural
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlCodec.Codec.product
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlCodec.Codec.optional
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlCodec.writeList
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlCodec.readList
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlCodec.list_exact
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlCodec.Codec.list
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlCodec.Codec.via
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlCodec.Codec.injective
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlCodec.Codec.equality
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlCodec.demand
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlCodec.deductionDemand
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlCodec.specification
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlCodec.route
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlCodec.event
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlCodec.readout
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlCodec.summary
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlCodec.Command
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlCodec.quotationFields
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlCodec.conclusionFields
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlCodec.command
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlCodec.Raw
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlCodec.raw
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlCodec.envelope
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlCodec.bytes
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlCodec.fromBytes
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlCodec.bytes_exact
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlCodec.save
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlCodec.load
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlCodec.byte_roundtrip
/- AXIOM_AUDIT_END -/
