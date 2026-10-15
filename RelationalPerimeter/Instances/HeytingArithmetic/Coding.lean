import RelationalPerimeter.Instances.HeytingArithmetic.Substitution

/-!
# Constructive computable Goedel coding

Pairing, unpairing, encoding, and decoding are implemented locally.  Decoders
recurse on explicit fuel, so no well-founded or classical infrastructure is
hidden in the coding layer.
-/

namespace RelationalPerimeter
namespace HeytingArithmetic

/-! ## Local prefix pairing -/

/-- Structural doubling. -/
def natDouble : Nat -> Nat
  | 0 => 0
  | Nat.succ value => Nat.succ (Nat.succ (natDouble value))

/-- Every natural is below its structural double. -/
theorem nat_le_natDouble (value : Nat) : value <= natDouble value := by
  induction value with
  | zero => exact Nat.le_refl 0
  | succ value inductionHypothesis =>
      exact Nat.succ_le_succ (Nat.le_trans inductionHypothesis
        (Nat.le_succ (natDouble value)))

/-- Prefix pairing: the first component is a chain of odd markers. -/
def natPair : Nat -> Nat -> Nat
  | 0, payload => natDouble payload
  | Nat.succ tag, payload => Nat.succ (natDouble (natPair tag payload))

/-- The first component is bounded by its pair. -/
theorem natPair_left_le (tag payload : Nat) : tag <= natPair tag payload := by
  induction tag with
  | zero => exact Nat.zero_le (natPair 0 payload)
  | succ tag inductionHypothesis =>
      change Nat.succ tag <= Nat.succ (natDouble (natPair tag payload))
      exact Nat.succ_le_succ
        (Nat.le_trans inductionHypothesis
          (nat_le_natDouble (natPair tag payload)))

/-- The payload is bounded by its pair. -/
theorem natPair_right_le (tag payload : Nat) : payload <= natPair tag payload := by
  induction tag with
  | zero => exact nat_le_natDouble payload
  | succ tag inductionHypothesis =>
      change payload <= Nat.succ (natDouble (natPair tag payload))
      exact Nat.le_trans inductionHypothesis
        (Nat.le_trans
          (nat_le_natDouble (natPair tag payload))
          (Nat.le_succ (natDouble (natPair tag payload))))

/-- Split a natural into its parity bit and structural half. -/
def paritySplit : Nat -> Bool × Nat
  | 0 => (false, 0)
  | Nat.succ 0 => (true, 0)
  | Nat.succ (Nat.succ value) =>
      let previous := paritySplit value
      (previous.1, Nat.succ previous.2)

/-- Splitting a structural double returns its payload. -/
theorem paritySplit_natDouble (value : Nat) :
    paritySplit (natDouble value) = (false, value) := by
  induction value with
  | zero => rfl
  | succ value inductionHypothesis =>
      change
        (let previous := paritySplit (natDouble value);
          (previous.1, Nat.succ previous.2)) =
            (false, Nat.succ value)
      rw [inductionHypothesis]

/-- Splitting an odd marker returns the preceding paired code. -/
theorem paritySplit_succ_natDouble (value : Nat) :
    paritySplit (Nat.succ (natDouble value)) = (true, value) := by
  induction value with
  | zero => rfl
  | succ value inductionHypothesis =>
      change
        (let previous := paritySplit (Nat.succ (natDouble value));
          (previous.1, Nat.succ previous.2)) =
            (true, Nat.succ value)
      rw [inductionHypothesis]

/-- Fuelled inverse of prefix pairing. -/
def natUnpairFuel : Nat -> Nat -> Nat × Nat
  | 0, code => (0, code)
  | Nat.succ fuel, code =>
      match paritySplit code with
      | (false, payload) => (0, payload)
      | (true, rest) =>
          let components := natUnpairFuel fuel rest
          (Nat.succ components.1, components.2)

/-- Sufficient fuel recovers both paired components. -/
theorem natUnpairFuel_natPair_of_lt
    (tag payload fuel : Nat)
    (enough : tag < fuel) :
    natUnpairFuel fuel (natPair tag payload) = (tag, payload) := by
  induction tag generalizing fuel with
  | zero =>
      cases fuel with
      | zero => exact (Nat.not_lt_zero 0 enough).elim
      | succ fuel =>
          change
            (match paritySplit (natDouble payload) with
              | (false, decoded) => (0, decoded)
              | (true, rest) =>
                  let components := natUnpairFuel fuel rest
                  (Nat.succ components.1, components.2)) =
              (0, payload)
          rw [paritySplit_natDouble]
  | succ tag inductionHypothesis =>
      cases fuel with
      | zero => exact (Nat.not_lt_zero (Nat.succ tag) enough).elim
      | succ fuel =>
          have smaller : tag < fuel := Nat.lt_of_succ_lt_succ enough
          change
            (match paritySplit
                (Nat.succ (natDouble (natPair tag payload))) with
              | (false, decoded) => (0, decoded)
              | (true, rest) =>
                  let components := natUnpairFuel fuel rest
                  (Nat.succ components.1, components.2)) =
              (Nat.succ tag, payload)
          rw [paritySplit_succ_natDouble]
          change
            (Nat.succ (natUnpairFuel fuel (natPair tag payload)).1,
              (natUnpairFuel fuel (natPair tag payload)).2) =
                (Nat.succ tag, payload)
          rw [inductionHypothesis fuel smaller]

/-- Total local unpairing. -/
def natUnpair (code : Nat) : Nat × Nat :=
  natUnpairFuel (Nat.succ code) code

/-- Local unpairing is a left inverse of local pairing. -/
theorem natUnpair_pair (tag payload : Nat) :
    natUnpair (natPair tag payload) = (tag, payload) :=
  natUnpairFuel_natPair_of_lt
    tag payload (Nat.succ (natPair tag payload))
    (Nat.lt_succ_of_le (natPair_left_le tag payload))

/-! ## Term coding -/

/-- Structural code of a bare arithmetic term; zero is reserved for failure. -/
def RawTerm.code : RawTerm -> Nat
  | RawTerm.bvar index => Nat.succ (natPair 0 index)
  | RawTerm.zero => Nat.succ (natPair 1 0)
  | RawTerm.succ term => Nat.succ (natPair 2 term.code)
  | RawTerm.add left right =>
      Nat.succ (natPair 3 (natPair left.code right.code))
  | RawTerm.mul left right =>
      Nat.succ (natPair 4 (natPair left.code right.code))

/-- Fuelled total decoder for term codes. -/
def decodeTermFuel : Nat -> Nat -> Option RawTerm
  | 0, _code => none
  | Nat.succ _fuel, 0 => none
  | Nat.succ fuel, Nat.succ encoded =>
      let components := natUnpair encoded
      match components.1 with
      | 0 => some (RawTerm.bvar components.2)
      | 1 => some RawTerm.zero
      | 2 => return RawTerm.succ (← decodeTermFuel fuel components.2)
      | 3 =>
          let children := natUnpair components.2
          return RawTerm.add
            (← decodeTermFuel fuel children.1)
            (← decodeTermFuel fuel children.2)
      | 4 =>
          let children := natUnpair components.2
          return RawTerm.mul
            (← decodeTermFuel fuel children.1)
            (← decodeTermFuel fuel children.2)
      | _ => none

/-- A term code is always positive. -/
theorem RawTerm.code_pos (term : RawTerm) : 0 < term.code := by
  cases term <;> exact Nat.zero_lt_succ _

/-- Enough fuel decodes every freshly encoded term. -/
theorem decodeTermFuel_code
    (term : RawTerm)
    (fuel : Nat)
    (bounded : term.code <= fuel) :
    decodeTermFuel fuel term.code = some term := by
  induction term generalizing fuel with
  | bvar index =>
      cases fuel with
      | zero => exact (Nat.not_succ_le_zero _ bounded).elim
      | succ fuel =>
          change
            decodeTermFuel (Nat.succ fuel)
                (Nat.succ (natPair 0 index)) =
              some (RawTerm.bvar index)
          rw [decodeTermFuel, natUnpair_pair]
          rfl
  | zero =>
      cases fuel with
      | zero => exact (Nat.not_succ_le_zero _ bounded).elim
      | succ fuel =>
          change
            decodeTermFuel (Nat.succ fuel)
                (Nat.succ (natPair 1 0)) =
              some RawTerm.zero
          rw [decodeTermFuel, natUnpair_pair]
          rfl
  | succ term inductionHypothesis =>
      cases fuel with
      | zero => exact (Nat.not_succ_le_zero _ bounded).elim
      | succ fuel =>
          have outerBound : natPair 2 term.code <= fuel :=
            Nat.le_of_succ_le_succ bounded
          have childBound : term.code <= fuel :=
            Nat.le_trans (natPair_right_le 2 term.code) outerBound
          change
            decodeTermFuel (Nat.succ fuel)
                (Nat.succ (natPair 2 term.code)) =
              some (RawTerm.succ term)
          rw [decodeTermFuel, natUnpair_pair]
          rw [inductionHypothesis fuel childBound]
          rfl
  | add left right leftHypothesis rightHypothesis =>
      cases fuel with
      | zero => exact (Nat.not_succ_le_zero _ bounded).elim
      | succ fuel =>
          have outerBound : natPair 3 (natPair left.code right.code) <= fuel :=
            Nat.le_of_succ_le_succ bounded
          have payloadBound : natPair left.code right.code <= fuel :=
            Nat.le_trans
              (natPair_right_le 3 (natPair left.code right.code)) outerBound
          have leftBound : left.code <= fuel :=
            Nat.le_trans (natPair_left_le left.code right.code) payloadBound
          have rightBound : right.code <= fuel :=
            Nat.le_trans (natPair_right_le left.code right.code) payloadBound
          change
            decodeTermFuel (Nat.succ fuel)
                (Nat.succ
                  (natPair 3 (natPair left.code right.code))) =
              some (RawTerm.add left right)
          rw [decodeTermFuel, natUnpair_pair, natUnpair_pair]
          change
            (do
              let decodedLeft <- decodeTermFuel fuel left.code
              let decodedRight <- decodeTermFuel fuel right.code
              return RawTerm.add decodedLeft decodedRight) =
                some (RawTerm.add left right)
          rw [leftHypothesis fuel leftBound, rightHypothesis fuel rightBound]
          rfl
  | mul left right leftHypothesis rightHypothesis =>
      cases fuel with
      | zero => exact (Nat.not_succ_le_zero _ bounded).elim
      | succ fuel =>
          have outerBound : natPair 4 (natPair left.code right.code) <= fuel :=
            Nat.le_of_succ_le_succ bounded
          have payloadBound : natPair left.code right.code <= fuel :=
            Nat.le_trans
              (natPair_right_le 4 (natPair left.code right.code)) outerBound
          have leftBound : left.code <= fuel :=
            Nat.le_trans (natPair_left_le left.code right.code) payloadBound
          have rightBound : right.code <= fuel :=
            Nat.le_trans (natPair_right_le left.code right.code) payloadBound
          change
            decodeTermFuel (Nat.succ fuel)
                (Nat.succ
                  (natPair 4 (natPair left.code right.code))) =
              some (RawTerm.mul left right)
          rw [decodeTermFuel, natUnpair_pair, natUnpair_pair]
          change
            (do
              let decodedLeft <- decodeTermFuel fuel left.code
              let decodedRight <- decodeTermFuel fuel right.code
              return RawTerm.mul decodedLeft decodedRight) =
                some (RawTerm.mul left right)
          rw [leftHypothesis fuel leftBound, rightHypothesis fuel rightBound]
          rfl

/-- Total decoder for term codes. -/
def decodeTerm (code : Nat) : Option RawTerm :=
  decodeTermFuel code code

/-- Term decoding is a left inverse of term coding. -/
theorem decodeTerm_code (term : RawTerm) :
    decodeTerm term.code = some term :=
  decodeTermFuel_code term term.code (Nat.le_refl term.code)

/-- Term codes are injective. -/
theorem RawTerm.code_injective : Function.Injective RawTerm.code := by
  intro left right sameCode
  have decoded : decodeTerm left.code = decodeTerm right.code :=
    congrArg decodeTerm sameCode
  rw [decodeTerm_code left, decodeTerm_code right] at decoded
  exact Option.some.inj decoded

/-! ## Formula coding -/

/-- Structural code of a bare formula; zero is reserved for failure. -/
def RawFormula.code : RawFormula -> Nat
  | RawFormula.falsum => Nat.succ (natPair 0 0)
  | RawFormula.equal left right =>
      Nat.succ (natPair 1 (natPair left.code right.code))
  | RawFormula.conj left right =>
      Nat.succ (natPair 2 (natPair left.code right.code))
  | RawFormula.disj left right =>
      Nat.succ (natPair 3 (natPair left.code right.code))
  | RawFormula.impl left right =>
      Nat.succ (natPair 4 (natPair left.code right.code))
  | RawFormula.all body => Nat.succ (natPair 5 body.code)
  | RawFormula.ex body => Nat.succ (natPair 6 body.code)

/-- Fuelled total decoder for formula codes. -/
def decodeFormulaFuel : Nat -> Nat -> Option RawFormula
  | 0, _code => none
  | Nat.succ _fuel, 0 => none
  | Nat.succ fuel, Nat.succ encoded =>
      let components := natUnpair encoded
      match components.1 with
      | 0 => some RawFormula.falsum
      | 1 =>
          let children := natUnpair components.2
          return RawFormula.equal
            (← decodeTerm children.1)
            (← decodeTerm children.2)
      | 2 =>
          let children := natUnpair components.2
          return RawFormula.conj
            (← decodeFormulaFuel fuel children.1)
            (← decodeFormulaFuel fuel children.2)
      | 3 =>
          let children := natUnpair components.2
          return RawFormula.disj
            (← decodeFormulaFuel fuel children.1)
            (← decodeFormulaFuel fuel children.2)
      | 4 =>
          let children := natUnpair components.2
          return RawFormula.impl
            (← decodeFormulaFuel fuel children.1)
            (← decodeFormulaFuel fuel children.2)
      | 5 => return RawFormula.all (← decodeFormulaFuel fuel components.2)
      | 6 => return RawFormula.ex (← decodeFormulaFuel fuel components.2)
      | _ => none

/-- A formula code is always positive. -/
theorem RawFormula.code_pos (formula : RawFormula) : 0 < formula.code := by
  cases formula <;> exact Nat.zero_lt_succ _

/-- Enough fuel decodes every freshly encoded formula. -/
theorem decodeFormulaFuel_code
    (formula : RawFormula)
    (fuel : Nat)
    (bounded : formula.code <= fuel) :
    decodeFormulaFuel fuel formula.code = some formula := by
  induction formula generalizing fuel with
  | falsum =>
      cases fuel with
      | zero => exact (Nat.not_succ_le_zero _ bounded).elim
      | succ fuel =>
          change
            decodeFormulaFuel (Nat.succ fuel)
                (Nat.succ (natPair 0 0)) =
              some RawFormula.falsum
          rw [decodeFormulaFuel, natUnpair_pair]
          rfl
  | equal left right =>
      cases fuel with
      | zero => exact (Nat.not_succ_le_zero _ bounded).elim
      | succ fuel =>
          change
            decodeFormulaFuel (Nat.succ fuel)
                (Nat.succ
                  (natPair 1 (natPair left.code right.code))) =
              some (RawFormula.equal left right)
          rw [decodeFormulaFuel, natUnpair_pair, natUnpair_pair]
          change
            (do
              let decodedLeft <- decodeTerm left.code
              let decodedRight <- decodeTerm right.code
              return RawFormula.equal decodedLeft decodedRight) =
                some (RawFormula.equal left right)
          rw [decodeTerm_code left, decodeTerm_code right]
          rfl
  | conj left right leftHypothesis rightHypothesis =>
      cases fuel with
      | zero => exact (Nat.not_succ_le_zero _ bounded).elim
      | succ fuel =>
          have outerBound : natPair 2 (natPair left.code right.code) <= fuel :=
            Nat.le_of_succ_le_succ bounded
          have payloadBound : natPair left.code right.code <= fuel :=
            Nat.le_trans
              (natPair_right_le 2 (natPair left.code right.code)) outerBound
          have leftBound : left.code <= fuel :=
            Nat.le_trans (natPair_left_le left.code right.code) payloadBound
          have rightBound : right.code <= fuel :=
            Nat.le_trans (natPair_right_le left.code right.code) payloadBound
          change
            decodeFormulaFuel (Nat.succ fuel)
                (Nat.succ
                  (natPair 2 (natPair left.code right.code))) =
              some (RawFormula.conj left right)
          rw [decodeFormulaFuel, natUnpair_pair, natUnpair_pair]
          change
            (do
              let decodedLeft <- decodeFormulaFuel fuel left.code
              let decodedRight <- decodeFormulaFuel fuel right.code
              return RawFormula.conj decodedLeft decodedRight) =
                some (RawFormula.conj left right)
          rw [leftHypothesis fuel leftBound, rightHypothesis fuel rightBound]
          rfl
  | disj left right leftHypothesis rightHypothesis =>
      cases fuel with
      | zero => exact (Nat.not_succ_le_zero _ bounded).elim
      | succ fuel =>
          have outerBound : natPair 3 (natPair left.code right.code) <= fuel :=
            Nat.le_of_succ_le_succ bounded
          have payloadBound : natPair left.code right.code <= fuel :=
            Nat.le_trans
              (natPair_right_le 3 (natPair left.code right.code)) outerBound
          have leftBound : left.code <= fuel :=
            Nat.le_trans (natPair_left_le left.code right.code) payloadBound
          have rightBound : right.code <= fuel :=
            Nat.le_trans (natPair_right_le left.code right.code) payloadBound
          change
            decodeFormulaFuel (Nat.succ fuel)
                (Nat.succ
                  (natPair 3 (natPair left.code right.code))) =
              some (RawFormula.disj left right)
          rw [decodeFormulaFuel, natUnpair_pair, natUnpair_pair]
          change
            (do
              let decodedLeft <- decodeFormulaFuel fuel left.code
              let decodedRight <- decodeFormulaFuel fuel right.code
              return RawFormula.disj decodedLeft decodedRight) =
                some (RawFormula.disj left right)
          rw [leftHypothesis fuel leftBound, rightHypothesis fuel rightBound]
          rfl
  | impl left right leftHypothesis rightHypothesis =>
      cases fuel with
      | zero => exact (Nat.not_succ_le_zero _ bounded).elim
      | succ fuel =>
          have outerBound : natPair 4 (natPair left.code right.code) <= fuel :=
            Nat.le_of_succ_le_succ bounded
          have payloadBound : natPair left.code right.code <= fuel :=
            Nat.le_trans
              (natPair_right_le 4 (natPair left.code right.code)) outerBound
          have leftBound : left.code <= fuel :=
            Nat.le_trans (natPair_left_le left.code right.code) payloadBound
          have rightBound : right.code <= fuel :=
            Nat.le_trans (natPair_right_le left.code right.code) payloadBound
          change
            decodeFormulaFuel (Nat.succ fuel)
                (Nat.succ
                  (natPair 4 (natPair left.code right.code))) =
              some (RawFormula.impl left right)
          rw [decodeFormulaFuel, natUnpair_pair, natUnpair_pair]
          change
            (do
              let decodedLeft <- decodeFormulaFuel fuel left.code
              let decodedRight <- decodeFormulaFuel fuel right.code
              return RawFormula.impl decodedLeft decodedRight) =
                some (RawFormula.impl left right)
          rw [leftHypothesis fuel leftBound, rightHypothesis fuel rightBound]
          rfl
  | all body inductionHypothesis =>
      cases fuel with
      | zero => exact (Nat.not_succ_le_zero _ bounded).elim
      | succ fuel =>
          have outerBound : natPair 5 body.code <= fuel :=
            Nat.le_of_succ_le_succ bounded
          have bodyBound : body.code <= fuel :=
            Nat.le_trans (natPair_right_le 5 body.code) outerBound
          change
            decodeFormulaFuel (Nat.succ fuel)
                (Nat.succ (natPair 5 body.code)) =
              some (RawFormula.all body)
          rw [decodeFormulaFuel, natUnpair_pair]
          rw [inductionHypothesis fuel bodyBound]
          rfl
  | ex body inductionHypothesis =>
      cases fuel with
      | zero => exact (Nat.not_succ_le_zero _ bounded).elim
      | succ fuel =>
          have outerBound : natPair 6 body.code <= fuel :=
            Nat.le_of_succ_le_succ bounded
          have bodyBound : body.code <= fuel :=
            Nat.le_trans (natPair_right_le 6 body.code) outerBound
          change
            decodeFormulaFuel (Nat.succ fuel)
                (Nat.succ (natPair 6 body.code)) =
              some (RawFormula.ex body)
          rw [decodeFormulaFuel, natUnpair_pair]
          rw [inductionHypothesis fuel bodyBound]
          rfl

/-- Total decoder for formula codes. -/
def decodeFormula (code : Nat) : Option RawFormula :=
  decodeFormulaFuel code code

/-- Formula decoding is a left inverse of formula coding. -/
theorem decodeFormula_code (formula : RawFormula) :
    decodeFormula formula.code = some formula :=
  decodeFormulaFuel_code formula formula.code (Nat.le_refl formula.code)

/-- Formula codes are injective. -/
theorem RawFormula.code_injective : Function.Injective RawFormula.code := by
  intro left right sameCode
  have decoded : decodeFormula left.code = decodeFormula right.code :=
    congrArg decodeFormula sameCode
  rw [decodeFormula_code left, decodeFormula_code right] at decoded
  exact Option.some.inj decoded

/-- Goedel quotation of a closed sentence. -/
def Sentence.quote (sentence : Sentence) : Nat := sentence.raw.code

/-- Quotation is injective on proof-carrying closed sentences. -/
theorem Sentence.quote_injective : Function.Injective Sentence.quote := by
  intro left right sameQuote
  apply Sentence.eq_of_raw_eq
  exact RawFormula.code_injective sameQuote

/-- Equality of quotations is exactly equality of sentences. -/
theorem Sentence.quote_eq_quote_iff (left right : Sentence) :
    left.quote = right.quote ↔ left = right := by
  constructor
  · intro sameQuote
    exact Sentence.quote_injective sameQuote
  · intro sameSentence
    cases sameSentence
    rfl

end HeytingArithmetic
end RelationalPerimeter

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.HeytingArithmetic.paritySplit_natDouble
#print axioms RelationalPerimeter.HeytingArithmetic.paritySplit_succ_natDouble
#print axioms RelationalPerimeter.HeytingArithmetic.natUnpairFuel_natPair_of_lt
#print axioms RelationalPerimeter.HeytingArithmetic.natUnpair_pair
#print axioms RelationalPerimeter.HeytingArithmetic.decodeTermFuel_code
#print axioms RelationalPerimeter.HeytingArithmetic.decodeTerm
#print axioms RelationalPerimeter.HeytingArithmetic.decodeTerm_code
#print axioms RelationalPerimeter.HeytingArithmetic.RawTerm.code_injective
#print axioms RelationalPerimeter.HeytingArithmetic.decodeFormulaFuel_code
#print axioms RelationalPerimeter.HeytingArithmetic.decodeFormula
#print axioms RelationalPerimeter.HeytingArithmetic.decodeFormula_code
#print axioms RelationalPerimeter.HeytingArithmetic.RawFormula.code_injective
#print axioms RelationalPerimeter.HeytingArithmetic.Sentence.quote_injective
/- AXIOM_AUDIT_END -/
