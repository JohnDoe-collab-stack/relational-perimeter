import RelationalPerimeter.Constitution.HeytingArithmetic.PrimitiveRecursiveControl

/-!
# Primitive-recursive inverse components for prefix pairing

The inverse is organized without nested recursion.  A first primitive
recursion iterates structural halving.  A second recursion advances a tag
counter only while the remainder selected by that counter is odd.  This gives
two ordinary primitive-recursive programs for the components of `natUnpair`.
-/

namespace RelationalPerimeter
namespace HeytingArithmetic

/-- Iterated structural halving. -/
def natIterateHalf : Nat -> Nat -> Nat
  | 0, code => code
  | Nat.succ iterations, code => natHalf (natIterateHalf iterations code)

/-- Apply structural halving to the previous recursion result. -/
def PRFunction.halfOfPrevious : PRFunction 3 :=
  PRFunction.composition
    PRFunction.half
    (PRFunctionVector.singleton
      (PRFunction.projection 3 1
        (Nat.succ_lt_succ (Nat.zero_lt_succ 1))))

/-- Primitive-recursive iteration of structural halving. -/
def PRFunction.iterateHalf : PRFunction 2 :=
  PRFunction.primitiveRecursion
    PRFunction.identity
    PRFunction.halfOfPrevious

/-- The explicit iterator computes `natIterateHalf`. -/
theorem PRFunction.iterateHalf_evaluates (iterations code : Nat) :
    PRFunction.Evaluates
      PRFunction.iterateHalf
      (NatVector.cons iterations
        (NatVector.cons code NatVector.nil))
      (natIterateHalf iterations code) := by
  induction iterations with
  | zero =>
      exact PRFunction.Evaluates.primitiveZero
        (PRFunction.Evaluates.projection
          0
          (Nat.zero_lt_succ 0)
          (NatVector.cons code NatVector.nil))
  | succ iterations inductionHypothesis =>
      apply PRFunction.Evaluates.primitiveSucc inductionHypothesis
      apply PRFunction.Evaluates.composition
      · apply PRFunctionVector.Evaluates.cons
        · exact PRFunction.Evaluates.projection
            1
            (Nat.succ_lt_succ (Nat.zero_lt_succ 1))
            (NatVector.cons iterations
              (NatVector.cons (natIterateHalf iterations code)
                (NatVector.cons code NatVector.nil)))
        · exact PRFunctionVector.Evaluates.nil
            (NatVector.cons iterations
              (NatVector.cons (natIterateHalf iterations code)
                (NatVector.cons code NatVector.nil)))
      · exact PRFunction.half_evaluates
          (natIterateHalf iterations code)

/-- Remainder selected by the current tag counter in an unpairing step. -/
def PRFunction.unpairCurrentRemainder : PRFunction 3 :=
  PRFunction.composition
    PRFunction.iterateHalf
    (PRFunctionVector.cons
      (PRFunction.projection 3 1
        (Nat.succ_lt_succ (Nat.zero_lt_succ 1)))
      (PRFunctionVector.singleton
        (PRFunction.projection 3 2
          (Nat.succ_lt_succ
            (Nat.succ_lt_succ (Nat.zero_lt_succ 0))))))

/-- Parity of the remainder selected by the current tag counter. -/
def PRFunction.unpairCurrentParity : PRFunction 3 :=
  PRFunction.composition
    PRFunction.parityBit
    (PRFunctionVector.singleton PRFunction.unpairCurrentRemainder)

/-- Successor of the current tag counter in an unpairing step. -/
def PRFunction.successorOfUnpairCounter : PRFunction 3 :=
  PRFunction.composition
    PRFunction.successor
    (PRFunctionVector.singleton
      (PRFunction.projection 3 1
        (Nat.succ_lt_succ (Nat.zero_lt_succ 1))))

/-- One bounded unpair-left step. -/
def PRFunction.unpairLeftStep : PRFunction 3 :=
  PRFunction.composition
    PRFunction.ifZero
    (PRFunctionVector.cons
      PRFunction.unpairCurrentParity
      (PRFunctionVector.cons
        (PRFunction.projection 3 1
          (Nat.succ_lt_succ (Nat.zero_lt_succ 1)))
        (PRFunctionVector.singleton PRFunction.successorOfUnpairCounter)))

/-- Fuelled semantic left-component computation. -/
def natUnpairLeftFuel : Nat -> Nat -> Nat
  | 0, _code => 0
  | Nat.succ fuel, code =>
      natIfZero
        (natParityBit
          (natIterateHalf (natUnpairLeftFuel fuel code) code))
        (natUnpairLeftFuel fuel code)
        (Nat.succ (natUnpairLeftFuel fuel code))

/-- Primitive-recursive fuelled left component of prefix unpairing. -/
def PRFunction.unpairLeftFuel : PRFunction 2 :=
  PRFunction.primitiveRecursion
    PRFunction.zero
    PRFunction.unpairLeftStep

/-- The explicit fuelled program computes `natUnpairLeftFuel`. -/
theorem PRFunction.unpairLeftFuel_evaluates (fuel code : Nat) :
    PRFunction.Evaluates
      PRFunction.unpairLeftFuel
      (NatVector.cons fuel
        (NatVector.cons code NatVector.nil))
      (natUnpairLeftFuel fuel code) := by
  induction fuel with
  | zero =>
      exact PRFunction.Evaluates.primitiveZero
        (PRFunction.Evaluates.zero
          (NatVector.cons code NatVector.nil))
  | succ fuel inductionHypothesis =>
      apply PRFunction.Evaluates.primitiveSucc inductionHypothesis
      apply PRFunction.Evaluates.composition
      · apply PRFunctionVector.Evaluates.cons
        · apply PRFunction.Evaluates.composition
          · apply PRFunctionVector.Evaluates.cons
            · apply PRFunction.Evaluates.composition
              · apply PRFunctionVector.Evaluates.cons
                · exact PRFunction.Evaluates.projection
                    1
                    (Nat.succ_lt_succ (Nat.zero_lt_succ 1))
                    (NatVector.cons fuel
                      (NatVector.cons (natUnpairLeftFuel fuel code)
                        (NatVector.cons code NatVector.nil)))
                · apply PRFunctionVector.Evaluates.cons
                  · exact PRFunction.Evaluates.projection
                      2
                      (Nat.succ_lt_succ
                        (Nat.succ_lt_succ (Nat.zero_lt_succ 0)))
                      (NatVector.cons fuel
                        (NatVector.cons (natUnpairLeftFuel fuel code)
                          (NatVector.cons code NatVector.nil)))
                  · exact PRFunctionVector.Evaluates.nil
                      (NatVector.cons fuel
                        (NatVector.cons (natUnpairLeftFuel fuel code)
                          (NatVector.cons code NatVector.nil)))
              · exact PRFunction.iterateHalf_evaluates
                  (natUnpairLeftFuel fuel code)
                  code
            · exact PRFunctionVector.Evaluates.nil
                (NatVector.cons fuel
                  (NatVector.cons (natUnpairLeftFuel fuel code)
                    (NatVector.cons code NatVector.nil)))
          · exact PRFunction.parityBit_evaluates
              (natIterateHalf (natUnpairLeftFuel fuel code) code)
        · apply PRFunctionVector.Evaluates.cons
          · exact PRFunction.Evaluates.projection
              1
              (Nat.succ_lt_succ (Nat.zero_lt_succ 1))
              (NatVector.cons fuel
                (NatVector.cons (natUnpairLeftFuel fuel code)
                  (NatVector.cons code NatVector.nil)))
          · apply PRFunctionVector.Evaluates.cons
            · apply PRFunction.Evaluates.composition
              · apply PRFunctionVector.Evaluates.cons
                · exact PRFunction.Evaluates.projection
                    1
                    (Nat.succ_lt_succ (Nat.zero_lt_succ 1))
                    (NatVector.cons fuel
                      (NatVector.cons (natUnpairLeftFuel fuel code)
                        (NatVector.cons code NatVector.nil)))
                · exact PRFunctionVector.Evaluates.nil
                    (NatVector.cons fuel
                      (NatVector.cons (natUnpairLeftFuel fuel code)
                        (NatVector.cons code NatVector.nil)))
              · exact PRFunction.Evaluates.successor
                  (NatVector.cons
                    (natUnpairLeftFuel fuel code) NatVector.nil)
            · exact PRFunctionVector.Evaluates.nil
                (NatVector.cons fuel
                  (NatVector.cons (natUnpairLeftFuel fuel code)
                    (NatVector.cons code NatVector.nil)))
      · exact PRFunction.ifZero_evaluates
          (natParityBit
            (natIterateHalf (natUnpairLeftFuel fuel code) code))
          (natUnpairLeftFuel fuel code)
          (Nat.succ (natUnpairLeftFuel fuel code))

/-- Total semantic left component, with code-sized fuel. -/
def natUnpairLeft (code : Nat) : Nat :=
  natUnpairLeftFuel (Nat.succ code) code

/-- Feed successor and identity into the fuelled left-component program. -/
def PRFunction.unpairLeft : PRFunction 1 :=
  PRFunction.composition
    PRFunction.unpairLeftFuel
    (PRFunctionVector.cons
      PRFunction.successor
      (PRFunctionVector.singleton PRFunction.identity))

/-- The explicit total left-component program computes `natUnpairLeft`. -/
theorem PRFunction.unpairLeft_evaluates (code : Nat) :
    PRFunction.Evaluates
      PRFunction.unpairLeft
      (NatVector.cons code NatVector.nil)
      (natUnpairLeft code) := by
  apply PRFunction.Evaluates.composition
  · apply PRFunctionVector.Evaluates.cons
    · exact PRFunction.Evaluates.successor
        (NatVector.cons code NatVector.nil)
    · apply PRFunctionVector.Evaluates.cons
      · exact PRFunction.Evaluates.projection
          0
          (Nat.zero_lt_succ 0)
          (NatVector.cons code NatVector.nil)
      · exact PRFunctionVector.Evaluates.nil
          (NatVector.cons code NatVector.nil)
  · exact PRFunction.unpairLeftFuel_evaluates (Nat.succ code) code

/-- Semantic right component selected after the odd-prefix count. -/
def natUnpairRight (code : Nat) : Nat :=
  natHalf (natIterateHalf (natUnpairLeft code) code)

/-- Remainder selected by the total left-component program. -/
def PRFunction.unpairRemainder : PRFunction 1 :=
  PRFunction.composition
    PRFunction.iterateHalf
    (PRFunctionVector.cons
      PRFunction.unpairLeft
      (PRFunctionVector.singleton PRFunction.identity))

/-- Primitive-recursive right component of prefix unpairing. -/
def PRFunction.unpairRight : PRFunction 1 :=
  PRFunction.composition
    PRFunction.half
    (PRFunctionVector.singleton PRFunction.unpairRemainder)

/-- The explicit total right-component program computes `natUnpairRight`. -/
theorem PRFunction.unpairRight_evaluates (code : Nat) :
    PRFunction.Evaluates
      PRFunction.unpairRight
      (NatVector.cons code NatVector.nil)
      (natUnpairRight code) := by
  apply PRFunction.Evaluates.composition
  · apply PRFunctionVector.Evaluates.cons
    · apply PRFunction.Evaluates.composition
      · apply PRFunctionVector.Evaluates.cons
        · exact PRFunction.unpairLeft_evaluates code
        · apply PRFunctionVector.Evaluates.cons
          · exact PRFunction.Evaluates.projection
              0
              (Nat.zero_lt_succ 0)
              (NatVector.cons code NatVector.nil)
          · exact PRFunctionVector.Evaluates.nil
              (NatVector.cons code NatVector.nil)
      · exact PRFunction.iterateHalf_evaluates (natUnpairLeft code) code
    · exact PRFunctionVector.Evaluates.nil
        (NatVector.cons code NatVector.nil)
  · exact PRFunction.half_evaluates
      (natIterateHalf (natUnpairLeft code) code)

/-! ## Correctness on prefix pairs -/

/-- One outer halving step can be moved before the remaining iterations. -/
theorem natIterateHalf_succ (iterations code : Nat) :
    natIterateHalf (Nat.succ iterations) code =
      natIterateHalf iterations (natHalf code) := by
  induction iterations with
  | zero => rfl
  | succ iterations inductionHypothesis =>
      change
        natHalf (natIterateHalf (Nat.succ iterations) code) =
          natHalf (natIterateHalf iterations (natHalf code))
      rw [inductionHypothesis]

/-- Iterating half through a known prefix removes exactly that prefix. -/
theorem natIterateHalf_pair_prefix (markers rest payload : Nat) :
    natIterateHalf markers (natPair (markers + rest) payload) =
      natPair rest payload := by
  induction markers with
  | zero =>
      rw [Nat.zero_add]
      change natPair rest payload = natPair rest payload
      rfl
  | succ markers inductionHypothesis =>
      rw [Nat.succ_add]
      rw [natIterateHalf_succ]
      change
        natIterateHalf markers
          (natHalf
            (Nat.succ
              (natDouble (natPair (markers + rest) payload)))) =
          natPair rest payload
      rw [natHalf_succ_natDouble]
      exact inductionHypothesis

/-- Before the even payload is reached, each unit of fuel consumes one marker. -/
theorem natUnpairLeftFuel_pair_prefix
    (fuel rest payload : Nat) :
    natUnpairLeftFuel fuel (natPair (fuel + rest) payload) = fuel := by
  induction fuel generalizing rest payload with
  | zero => rfl
  | succ fuel inductionHypothesis =>
      rw [Nat.succ_add, ← Nat.add_succ]
      change
        natIfZero
          (natParityBit
            (natIterateHalf
              (natUnpairLeftFuel fuel
                (natPair (fuel + Nat.succ rest) payload))
              (natPair (fuel + Nat.succ rest) payload)))
          (natUnpairLeftFuel fuel
            (natPair (fuel + Nat.succ rest) payload))
          (Nat.succ
            (natUnpairLeftFuel fuel
              (natPair (fuel + Nat.succ rest) payload))) =
            Nat.succ fuel
      rw [inductionHypothesis (Nat.succ rest) payload]
      rw [natIterateHalf_pair_prefix fuel (Nat.succ rest) payload]
      change
        natIfZero
          (natParityBit
            (Nat.succ (natDouble (natPair rest payload))))
          fuel
          (Nat.succ fuel) = Nat.succ fuel
      rw [natParityBit_succ_natDouble]
      rfl

/-- Once the payload is reached, additional fuel leaves the tag unchanged. -/
theorem natUnpairLeftFuel_pair_extra
    (tag extra payload : Nat) :
    natUnpairLeftFuel (tag + extra) (natPair tag payload) = tag := by
  induction extra with
  | zero =>
      rw [Nat.add_zero]
      have prefixResult :=
        natUnpairLeftFuel_pair_prefix tag 0 payload
      rw [Nat.add_zero] at prefixResult
      exact prefixResult
  | succ extra inductionHypothesis =>
      rw [Nat.add_succ]
      change
        natIfZero
          (natParityBit
            (natIterateHalf
              (natUnpairLeftFuel (tag + extra) (natPair tag payload))
              (natPair tag payload)))
          (natUnpairLeftFuel (tag + extra) (natPair tag payload))
          (Nat.succ
            (natUnpairLeftFuel (tag + extra) (natPair tag payload))) =
            tag
      rw [inductionHypothesis]
      have stripped := natIterateHalf_pair_prefix tag 0 payload
      rw [Nat.add_zero] at stripped
      rw [stripped]
      change
        natIfZero
          (natParityBit (natDouble payload))
          tag
          (Nat.succ tag) = tag
      rw [natParityBit_natDouble]
      rfl

/-- Any fuel bound at least as large as the tag recovers the left component. -/
theorem natExistsEqAddOfLe
    {left right : Nat}
    (bounded : left <= right) :
    ∃ extra : Nat, right = left + extra := by
  induction bounded with
  | refl =>
      exact ⟨0, (Nat.add_zero left).symm⟩
  | @step upper _ inductionHypothesis =>
      cases inductionHypothesis with
      | intro extra equality =>
          exact ⟨Nat.succ extra, by
            rw [equality, Nat.add_succ]⟩

/-- Any fuel bound at least as large as the tag recovers the left component. -/
theorem natUnpairLeftFuel_pair_of_le
    (tag payload fuel : Nat)
    (enough : tag <= fuel) :
    natUnpairLeftFuel fuel (natPair tag payload) = tag := by
  cases natExistsEqAddOfLe enough with
  | intro extra equality =>
      exact equality.symm ▸
        natUnpairLeftFuel_pair_extra tag extra payload

/-- The total left-component program recovers the tag of every prefix pair. -/
theorem natUnpairLeft_pair (tag payload : Nat) :
    natUnpairLeft (natPair tag payload) = tag :=
  natUnpairLeftFuel_pair_of_le
    tag
    payload
    (Nat.succ (natPair tag payload))
    (Nat.le_trans
      (natPair_left_le tag payload)
      (Nat.le_succ (natPair tag payload)))

/-- The total right-component program recovers the payload of every prefix pair. -/
theorem natUnpairRight_pair (tag payload : Nat) :
    natUnpairRight (natPair tag payload) = payload := by
  change
    natHalf
      (natIterateHalf
        (natUnpairLeft (natPair tag payload))
        (natPair tag payload)) = payload
  rw [natUnpairLeft_pair]
  have stripped := natIterateHalf_pair_prefix tag 0 payload
  rw [Nat.add_zero] at stripped
  rw [stripped]
  exact natHalf_natDouble payload

/-! ## Canonical decomposition of every natural -/

theorem nat_even_or_odd :
    (code : Nat) ->
      (Exists fun payload => code = natDouble payload) \/
      (Exists fun payload => code = Nat.succ (natDouble payload))
  | 0 => Or.inl (Exists.intro 0 rfl)
  | 1 => Or.inr (Exists.intro 0 rfl)
  | Nat.succ (Nat.succ code) => by
      cases nat_even_or_odd code with
      | inl even =>
          cases even with
          | intro payload equality =>
              apply Or.inl
              exact Exists.intro (Nat.succ payload) (by
                rw [equality]
                rfl)
      | inr odd =>
          cases odd with
          | intro payload equality =>
              apply Or.inr
              exact Exists.intro (Nat.succ payload) (by
                rw [equality]
                rfl)

/-- Prefix pairing is constructively surjective. -/
theorem natPair_surjective (code : Nat) :
    Exists fun components : Nat × Nat =>
      code = natPair components.1 components.2 := by
  induction code using Nat.strongRecOn with
  | ind code inductionHypothesis =>
      cases nat_even_or_odd code with
      | inl even =>
          cases even with
          | intro payload equality =>
              exact Exists.intro (0, payload) equality
      | inr odd =>
          cases odd with
          | intro rest equality =>
              have smaller : rest < code := by
                rw [equality]
                exact Nat.lt_succ_of_le (nat_le_natDouble rest)
              cases inductionHypothesis rest smaller with
              | intro components restEquality =>
                  exact Exists.intro
                    (Nat.succ components.1, components.2) (by
                      rw [equality, restEquality]
                      rfl)

/-- The two primitive-recursive components recompose every natural exactly. -/
theorem natPair_unpairLeft_unpairRight (code : Nat) :
    natPair (natUnpairLeft code) (natUnpairRight code) = code := by
  cases natPair_surjective code with
  | intro components equality =>
      rw [equality, natUnpairLeft_pair, natUnpairRight_pair]

theorem natUnpair_eq_unpairComponents (code : Nat) :
    natUnpair code = (natUnpairLeft code, natUnpairRight code) := by
  cases natPair_surjective code with
  | intro components equality =>
      rw [equality, natUnpair_pair, natUnpairLeft_pair,
        natUnpairRight_pair]

/-- The left-component program executes directly to a paired tag. -/
theorem PRFunction.unpairLeft_pair_evaluates (tag payload : Nat) :
    PRFunction.Evaluates
      PRFunction.unpairLeft
      (NatVector.cons (natPair tag payload) NatVector.nil)
      tag := by
  have evaluation := PRFunction.unpairLeft_evaluates (natPair tag payload)
  rw [natUnpairLeft_pair] at evaluation
  exact evaluation

/-- The right-component program executes directly to a paired payload. -/
theorem PRFunction.unpairRight_pair_evaluates (tag payload : Nat) :
    PRFunction.Evaluates
      PRFunction.unpairRight
      (NatVector.cons (natPair tag payload) NatVector.nil)
      payload := by
  have evaluation := PRFunction.unpairRight_evaluates (natPair tag payload)
  rw [natUnpairRight_pair] at evaluation
  exact evaluation

end HeytingArithmetic
end RelationalPerimeter

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.HeytingArithmetic.PRFunction.iterateHalf
#print axioms RelationalPerimeter.HeytingArithmetic.PRFunction.iterateHalf_evaluates
#print axioms RelationalPerimeter.HeytingArithmetic.PRFunction.unpairLeftFuel
#print axioms RelationalPerimeter.HeytingArithmetic.PRFunction.unpairLeftFuel_evaluates
#print axioms RelationalPerimeter.HeytingArithmetic.PRFunction.unpairLeft
#print axioms RelationalPerimeter.HeytingArithmetic.PRFunction.unpairLeft_evaluates
#print axioms RelationalPerimeter.HeytingArithmetic.PRFunction.unpairRight
#print axioms RelationalPerimeter.HeytingArithmetic.PRFunction.unpairRight_evaluates
#print axioms RelationalPerimeter.HeytingArithmetic.natIterateHalf_succ
#print axioms RelationalPerimeter.HeytingArithmetic.natIterateHalf_pair_prefix
#print axioms RelationalPerimeter.HeytingArithmetic.natExistsEqAddOfLe
#print axioms RelationalPerimeter.HeytingArithmetic.natUnpairLeftFuel_pair_of_le
#print axioms RelationalPerimeter.HeytingArithmetic.natUnpairLeft_pair
#print axioms RelationalPerimeter.HeytingArithmetic.natUnpairRight_pair
#print axioms RelationalPerimeter.HeytingArithmetic.natPair_surjective
#print axioms RelationalPerimeter.HeytingArithmetic.natPair_unpairLeft_unpairRight
#print axioms RelationalPerimeter.HeytingArithmetic.natUnpair_eq_unpairComponents
#print axioms RelationalPerimeter.HeytingArithmetic.PRFunction.unpairLeft_pair_evaluates
#print axioms RelationalPerimeter.HeytingArithmetic.PRFunction.unpairRight_pair_evaluates
/- AXIOM_AUDIT_END -/
