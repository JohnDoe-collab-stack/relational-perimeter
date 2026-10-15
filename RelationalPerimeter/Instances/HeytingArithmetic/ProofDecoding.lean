import RelationalPerimeter.Instances.HeytingArithmetic.ProofCoding

/-!
# Constructive decoding of proof archives

All decoders are total and return `Option`.  Scoping evidence is recomputed
from raw syntax; it is never trusted from an encoded proof.  This module is
the data-level inverse required before defining a Boolean proof checker.
-/

namespace RelationalPerimeter
namespace HeytingArithmetic

/-! ## Scoped syntax decoders -/

theorem ScopedTerm.eq_of_raw_eq
    {bound : Nat}
    {left right : ScopedTerm bound}
    (sameRaw : left.raw = right.raw) : left = right := by
  cases left with
  | mk leftRaw leftScoped =>
      cases right with
      | mk rightRaw rightScoped =>
          cases sameRaw
          rfl

theorem ScopedFormula.eq_of_raw_eq
    {bound : Nat}
    {left right : ScopedFormula bound}
    (sameRaw : left.raw = right.raw) : left = right := by
  cases left with
  | mk leftRaw leftScoped =>
      cases right with
      | mk rightRaw rightScoped =>
          cases sameRaw
          rfl

def RawTerm.wellScopedDecision
    (bound : Nat) : (term : RawTerm) -> Decidable (term.WellScoped bound)
  | RawTerm.bvar index => by
      change Decidable (index < bound)
      infer_instance
  | RawTerm.zero => isTrue trivial
  | RawTerm.succ term => RawTerm.wellScopedDecision bound term
  | RawTerm.add left right =>
      match RawTerm.wellScopedDecision bound left with
      | isFalse leftNotScoped =>
          isFalse (fun evidence => leftNotScoped evidence.1)
      | isTrue leftScoped =>
          match RawTerm.wellScopedDecision bound right with
          | isFalse rightNotScoped =>
              isFalse (fun evidence => rightNotScoped evidence.2)
          | isTrue rightScoped =>
              isTrue (And.intro leftScoped rightScoped)
  | RawTerm.mul left right =>
      match RawTerm.wellScopedDecision bound left with
      | isFalse leftNotScoped =>
          isFalse (fun evidence => leftNotScoped evidence.1)
      | isTrue leftScoped =>
          match RawTerm.wellScopedDecision bound right with
          | isFalse rightNotScoped =>
              isFalse (fun evidence => rightNotScoped evidence.2)
          | isTrue rightScoped =>
              isTrue (And.intro leftScoped rightScoped)

def RawFormula.wellScopedDecision
    (bound : Nat) :
    (formula : RawFormula) -> Decidable (formula.WellScoped bound)
  | RawFormula.falsum => isTrue trivial
  | RawFormula.equal left right =>
      match RawTerm.wellScopedDecision bound left with
      | isFalse leftNotScoped =>
          isFalse (fun evidence => leftNotScoped evidence.1)
      | isTrue leftScoped =>
          match RawTerm.wellScopedDecision bound right with
          | isFalse rightNotScoped =>
              isFalse (fun evidence => rightNotScoped evidence.2)
          | isTrue rightScoped =>
              isTrue (And.intro leftScoped rightScoped)
  | RawFormula.conj left right =>
      match RawFormula.wellScopedDecision bound left with
      | isFalse leftNotScoped =>
          isFalse (fun evidence => leftNotScoped evidence.1)
      | isTrue leftScoped =>
          match RawFormula.wellScopedDecision bound right with
          | isFalse rightNotScoped =>
              isFalse (fun evidence => rightNotScoped evidence.2)
          | isTrue rightScoped =>
              isTrue (And.intro leftScoped rightScoped)
  | RawFormula.disj left right =>
      match RawFormula.wellScopedDecision bound left with
      | isFalse leftNotScoped =>
          isFalse (fun evidence => leftNotScoped evidence.1)
      | isTrue leftScoped =>
          match RawFormula.wellScopedDecision bound right with
          | isFalse rightNotScoped =>
              isFalse (fun evidence => rightNotScoped evidence.2)
          | isTrue rightScoped =>
              isTrue (And.intro leftScoped rightScoped)
  | RawFormula.impl left right =>
      match RawFormula.wellScopedDecision bound left with
      | isFalse leftNotScoped =>
          isFalse (fun evidence => leftNotScoped evidence.1)
      | isTrue leftScoped =>
          match RawFormula.wellScopedDecision bound right with
          | isFalse rightNotScoped =>
              isFalse (fun evidence => rightNotScoped evidence.2)
          | isTrue rightScoped =>
              isTrue (And.intro leftScoped rightScoped)
  | RawFormula.all body =>
      RawFormula.wellScopedDecision (Nat.succ bound) body
  | RawFormula.ex body =>
      RawFormula.wellScopedDecision (Nat.succ bound) body

instance rawTermWellScopedDecidable (bound : Nat) (term : RawTerm) :
    Decidable (term.WellScoped bound) :=
  RawTerm.wellScopedDecision bound term

instance rawFormulaWellScopedDecidable (bound : Nat) (formula : RawFormula) :
    Decidable (formula.WellScoped bound) :=
  RawFormula.wellScopedDecision bound formula

def decodeScopedTerm (bound code : Nat) : Option (ScopedTerm bound) :=
  match decodeTerm code with
  | none => none
  | some term =>
      if h : term.WellScoped bound then
        some { raw := term, isScoped := h }
      else
        none

def decodeScopedFormula (bound code : Nat) : Option (ScopedFormula bound) :=
  match decodeFormula code with
  | none => none
  | some formula =>
      if h : formula.WellScoped bound then
        some { raw := formula, isScoped := h }
      else
        none

theorem decodeScopedTerm_code
    {bound : Nat}
    (term : ScopedTerm bound) :
    decodeScopedTerm bound term.raw.code = some term := by
  cases term with
  | mk raw isScoped =>
      unfold decodeScopedTerm
      rw [decodeTerm_code]
      change
        (if h : raw.WellScoped bound then
            some ({ raw := raw, isScoped := h } : ScopedTerm bound)
          else none) =
          some ({ raw := raw, isScoped := isScoped } : ScopedTerm bound)
      rw [dif_pos isScoped]

theorem decodeScopedFormula_code
    {bound : Nat}
    (formula : ScopedFormula bound) :
    decodeScopedFormula bound formula.raw.code = some formula := by
  cases formula with
  | mk raw isScoped =>
      unfold decodeScopedFormula
      rw [decodeFormula_code]
      change
        (if h : raw.WellScoped bound then
            some ({ raw := raw, isScoped := h } : ScopedFormula bound)
          else none) =
          some ({ raw := raw, isScoped := isScoped } : ScopedFormula bound)
      rw [dif_pos isScoped]

/-! ## Context decoder -/

def decodeFormulaContextFuel
    (bound : Nat) : Nat -> Nat -> Option (FormulaContext bound)
  | 0, 0 => some FormulaContext.nil
  | 0, Nat.succ _encoded => none
  | Nat.succ _fuel, 0 => some FormulaContext.nil
  | Nat.succ fuel, Nat.succ encoded =>
      let components := natUnpair encoded
      return FormulaContext.cons
        (← decodeScopedFormula bound components.1)
        (← decodeFormulaContextFuel bound fuel components.2)

def decodeFormulaContext (bound code : Nat) :
    Option (FormulaContext bound) :=
  decodeFormulaContextFuel bound code code

theorem decodeFormulaContextFuel_quote
    {bound : Nat}
    (context : FormulaContext bound)
    (fuel : Nat)
    (bounded : context.quote <= fuel) :
    decodeFormulaContextFuel bound fuel context.quote = some context := by
  induction context generalizing fuel with
  | nil =>
      cases fuel <;> rfl
  | cons head tail inductionHypothesis =>
      cases fuel with
      | zero => exact (Nat.not_succ_le_zero _ bounded).elim
      | succ fuel =>
          have tailBound : tail.quote <= fuel := by
            have pairedBound : natPair head.raw.code tail.quote <= fuel :=
              Nat.le_of_succ_le_succ bounded
            exact Nat.le_trans
              (natPair_right_le head.raw.code tail.quote) pairedBound
          rw [FormulaContext.quote, decodeFormulaContextFuel,
            natUnpair_pair, decodeScopedFormula_code]
          rw [inductionHypothesis fuel tailBound]
          rfl

theorem decodeFormulaContext_quote
    {bound : Nat}
    (context : FormulaContext bound) :
    decodeFormulaContext bound context.quote = some context :=
  decodeFormulaContextFuel_quote context context.quote
    (Nat.le_refl context.quote)

/-! ## Proof-line decoder -/

def decodeProofLine (code : Nat) : Option ProofLine :=
  let first := natUnpair code
  let second := natUnpair first.2
  let third := natUnpair second.2
  let fourth := natUnpair third.2
  let fifth := natUnpair fourth.2
  do
    let rule <- decodeProofRuleTag first.1
    let premises <- decodeNatList fifth.1
    let parameters <- decodeNatList fifth.2
    pure
      { rule := rule
        bound := second.1
        contextCode := third.1
        conclusionCode := fourth.1
        premises := premises
        parameters := parameters }

theorem decodeProofLine_quote (line : ProofLine) :
    decodeProofLine line.quote = some line := by
  unfold decodeProofLine ProofLine.quote
  rw [natUnpair_pair]
  dsimp only
  rw [natUnpair_pair]
  dsimp only
  rw [natUnpair_pair]
  dsimp only
  rw [natUnpair_pair]
  dsimp only
  rw [natUnpair_pair]
  dsimp only
  rw [decodeProofRuleTag_code, decodeNatList_quote,
    decodeNatList_quote]
  rfl

/-! ## Numeric archive header -/

/-- The exact three numeric components trusted by the beta reader. -/
structure ProofArchiveHeader where
  lineCount : Nat
  dividend : Nat
  coefficient : Nat

def ProofArchiveHeader.quote (header : ProofArchiveHeader) : Nat :=
  natPair header.lineCount (natPair header.dividend header.coefficient)

def decodeProofArchiveHeader (code : Nat) : ProofArchiveHeader :=
  let outer := natUnpair code
  let beta := natUnpair outer.2
  { lineCount := outer.1
    dividend := beta.1
    coefficient := beta.2 }

def ProofArchive.header (archive : ProofArchive) : ProofArchiveHeader :=
  { lineCount := archive.lineCount
    dividend := archive.betaDividend
    coefficient := archive.betaCoefficient }

theorem ProofArchive.header_quote (archive : ProofArchive) :
    archive.header.quote = archive.quote := rfl

theorem decodeProofArchiveHeader_quote (header : ProofArchiveHeader) :
    decodeProofArchiveHeader header.quote = header := by
  cases header with
  | mk lineCount dividend coefficient =>
      unfold decodeProofArchiveHeader ProofArchiveHeader.quote
      rw [natUnpair_pair]
      dsimp only
      rw [natUnpair_pair]

theorem decodeProofArchiveHeader_archiveQuote (archive : ProofArchive) :
    decodeProofArchiveHeader archive.quote = archive.header := by
  rw [← archive.header_quote]
  exact decodeProofArchiveHeader_quote archive.header

def ProofArchiveHeader.lineCode
    (header : ProofArchiveHeader)
    (index : Nat) : Nat :=
  betaComponent header.dividend header.coefficient index

theorem ProofArchiveHeader.lineCode_of_archive
    (archive : ProofArchive)
    (index : Nat)
    (bounded : index < archive.lineCount) :
    archive.header.lineCode index = archive.lineCode index bounded :=
  archive.betaLookup_lineCode index bounded

end HeytingArithmetic
end RelationalPerimeter

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.HeytingArithmetic.decodeScopedFormula_code
#print axioms RelationalPerimeter.HeytingArithmetic.decodeFormulaContext_quote
#print axioms RelationalPerimeter.HeytingArithmetic.decodeProofLine_quote
#print axioms RelationalPerimeter.HeytingArithmetic.decodeProofArchiveHeader_archiveQuote
#print axioms RelationalPerimeter.HeytingArithmetic.ProofArchiveHeader.lineCode_of_archive
/- AXIOM_AUDIT_END -/
