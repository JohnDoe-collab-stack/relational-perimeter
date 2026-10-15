import RelationalPerimeter.Instances.HeytingArithmetic.PrimitiveRecursiveEvaluation

/-!
# Quantifier-blind primitive-recursive code transformation

The program in this module scans every code up to the input code.  A
newest-first trace stores, for each code, both its transformed term reading and
its transformed formula reading.  Genuine syntax only refers to strictly
smaller child codes, so every constructor can retrieve its transformed
children from the already built trace.

This first course-of-values construction deliberately does not track De Bruijn
depth under quantifiers.  It is retained as reusable trace infrastructure and
as a rejected comparison point.  The capture-avoiding substitution used by
diagonalization is the stack machine in `SubstitutionMachine.lean` and
`PrimitiveRecursiveSubstitutionMachine.lean`.
-/

namespace RelationalPerimeter
namespace HeytingArithmetic

/-! ## Evaluator specifications for the derived program library -/

/-- Any positive evaluation identifies the structural evaluator's result. -/
theorem PRFunction.run_eq_of_evaluates
    {arity : Nat}
    {program : PRFunction arity}
    {inputs : NatVector arity}
    {output : Nat}
    (evaluation : PRFunction.Evaluates program inputs output) :
    program.run inputs = output :=
  PRFunction.evaluates_unique (program.run_evaluates inputs) evaluation

@[simp] theorem PRFunction.run_constant
    (arity value : Nat)
    (inputs : NatVector arity) :
    (PRFunction.constant arity value).run inputs = value :=
  PRFunction.run_eq_of_evaluates
    (PRFunction.constant_evaluates arity value inputs)

@[simp] theorem PRFunction.run_ifZero
    (selector whenZero whenPositive : Nat) :
    PRFunction.ifZero.run
        (NatVector.cons selector
          (NatVector.cons whenZero
            (NatVector.cons whenPositive NatVector.nil))) =
      natIfZero selector whenZero whenPositive :=
  PRFunction.run_eq_of_evaluates
    (PRFunction.ifZero_evaluates selector whenZero whenPositive)

@[simp] theorem PRFunction.run_equalBit (left right : Nat) :
    PRFunction.equalBit.run
        (NatVector.cons left
          (NatVector.cons right NatVector.nil)) =
      natEqualBit left right :=
  PRFunction.run_eq_of_evaluates
    (PRFunction.equalBit_evaluates left right)

@[simp] theorem PRFunction.run_pair (left right : Nat) :
    PRFunction.pair.run
        (NatVector.cons left
          (NatVector.cons right NatVector.nil)) =
      natPair left right :=
  PRFunction.run_eq_of_evaluates
    (PRFunction.pair_evaluates left right)

@[simp] theorem PRFunction.run_unpairLeft (code : Nat) :
    PRFunction.unpairLeft.run
        (NatVector.cons code NatVector.nil) =
      natUnpairLeft code :=
  PRFunction.run_eq_of_evaluates
    (PRFunction.unpairLeft_evaluates code)

@[simp] theorem PRFunction.run_unpairRight (code : Nat) :
    PRFunction.unpairRight.run
        (NatVector.cons code NatVector.nil) =
      natUnpairRight code :=
  PRFunction.run_eq_of_evaluates
    (PRFunction.unpairRight_evaluates code)

@[simp] theorem PRFunction.run_traceLookupCode
    (current child history : Nat) :
    PRFunction.traceLookupCode.run
        (NatVector.cons current
          (NatVector.cons child
            (NatVector.cons history NatVector.nil))) =
      natTraceLookupCode current child history :=
  PRFunction.run_eq_of_evaluates
    (PRFunction.traceLookupCode_evaluates current child history)

@[simp] theorem PRFunction.run_taggedUnaryCode
    (tag payload : Nat) :
    (PRFunction.taggedUnaryCode tag).run
        (NatVector.cons payload NatVector.nil) =
      Nat.succ (natPair tag payload) :=
  PRFunction.run_eq_of_evaluates
    (PRFunction.taggedUnaryCode_evaluates tag payload)

@[simp] theorem PRFunction.run_taggedBinaryCode
    (tag left right : Nat) :
    (PRFunction.taggedBinaryCode tag).run
        (NatVector.cons left
          (NatVector.cons right NatVector.nil)) =
      Nat.succ (natPair tag (natPair left right)) :=
  PRFunction.run_eq_of_evaluates
    (PRFunction.taggedBinaryCode_evaluates tag left right)

@[simp] theorem PRFunction.run_numeralCode (value : Nat) :
    PRFunction.numeralCode.run
        (NatVector.cons value NatVector.nil) =
      (RawTerm.numeral value).code :=
  PRFunction.run_eq_of_evaluates
    (PRFunction.numeralCode_evaluates value)

/-!
The syntax constructors are named aliases of the generic tagged-code
programs.  Export their execution equations explicitly so downstream proofs
never depend on how aggressively Lean unfolds those aliases.
-/

@[simp] theorem PRFunction.run_termZeroCode
    (arity : Nat) (inputs : NatVector arity) :
    (PRFunction.termZeroCode arity).run inputs = RawTerm.zero.code :=
  PRFunction.run_constant arity RawTerm.zero.code inputs

@[simp] theorem PRFunction.run_termSuccessorCode (payload : Nat) :
    PRFunction.termSuccessorCode.run
        (NatVector.cons payload NatVector.nil) =
      Nat.succ (natPair 2 payload) :=
  PRFunction.run_taggedUnaryCode 2 payload

@[simp] theorem PRFunction.run_termAddCode (left right : Nat) :
    PRFunction.termAddCode.run
        (NatVector.cons left (NatVector.cons right NatVector.nil)) =
      Nat.succ (natPair 3 (natPair left right)) :=
  PRFunction.run_taggedBinaryCode 3 left right

@[simp] theorem PRFunction.run_termMultiplyCode (left right : Nat) :
    PRFunction.termMultiplyCode.run
        (NatVector.cons left (NatVector.cons right NatVector.nil)) =
      Nat.succ (natPair 4 (natPair left right)) :=
  PRFunction.run_taggedBinaryCode 4 left right

@[simp] theorem PRFunction.run_falsumCode
    (arity : Nat) (inputs : NatVector arity) :
    (PRFunction.falsumCode arity).run inputs = RawFormula.falsum.code :=
  PRFunction.run_constant arity RawFormula.falsum.code inputs

@[simp] theorem PRFunction.run_formulaEqualCode (left right : Nat) :
    PRFunction.formulaEqualCode.run
        (NatVector.cons left (NatVector.cons right NatVector.nil)) =
      Nat.succ (natPair 1 (natPair left right)) :=
  PRFunction.run_taggedBinaryCode 1 left right

@[simp] theorem PRFunction.run_formulaConjunctionCode (left right : Nat) :
    PRFunction.formulaConjunctionCode.run
        (NatVector.cons left (NatVector.cons right NatVector.nil)) =
      Nat.succ (natPair 2 (natPair left right)) :=
  PRFunction.run_taggedBinaryCode 2 left right

@[simp] theorem PRFunction.run_formulaDisjunctionCode (left right : Nat) :
    PRFunction.formulaDisjunctionCode.run
        (NatVector.cons left (NatVector.cons right NatVector.nil)) =
      Nat.succ (natPair 3 (natPair left right)) :=
  PRFunction.run_taggedBinaryCode 3 left right

@[simp] theorem PRFunction.run_formulaImplicationCode (left right : Nat) :
    PRFunction.formulaImplicationCode.run
        (NatVector.cons left (NatVector.cons right NatVector.nil)) =
      Nat.succ (natPair 4 (natPair left right)) :=
  PRFunction.run_taggedBinaryCode 4 left right

@[simp] theorem PRFunction.run_formulaUniversalCode (body : Nat) :
    PRFunction.formulaUniversalCode.run
        (NatVector.cons body NatVector.nil) =
      Nat.succ (natPair 5 body) :=
  PRFunction.run_taggedUnaryCode 5 body

@[simp] theorem PRFunction.run_formulaExistentialCode (body : Nat) :
    PRFunction.formulaExistentialCode.run
        (NatVector.cons body NatVector.nil) =
      Nat.succ (natPair 6 body) :=
  PRFunction.run_taggedUnaryCode 6 body

/-! ## Generic program-level selection -/

/-- Select between two programs with a numeric zero selector. -/
def PRFunction.select
    {arity : Nat}
    (selector whenZero whenPositive : PRFunction arity) :
    PRFunction arity :=
  PRFunction.composition PRFunction.ifZero
    (PRFunctionVector.cons selector
      (PRFunctionVector.cons whenZero
        (PRFunctionVector.singleton whenPositive)))

/-- The generic selector has exactly the numeric zero-test semantics. -/
@[simp] theorem PRFunction.run_select
    {arity : Nat}
    (selector whenZero whenPositive : PRFunction arity)
    (inputs : NatVector arity) :
    (PRFunction.select selector whenZero whenPositive).run inputs =
      natIfZero
        (selector.run inputs)
        (whenZero.run inputs)
        (whenPositive.run inputs) := by
  apply PRFunction.run_eq_of_evaluates
  apply PRFunction.Evaluates.composition
  · exact PRFunctionVector.Evaluates.cons
      (selector.run_evaluates inputs)
      (PRFunctionVector.Evaluates.cons
        (whenZero.run_evaluates inputs)
        (PRFunctionVector.Evaluates.cons
          (whenPositive.run_evaluates inputs)
          (PRFunctionVector.Evaluates.nil inputs)))
  · exact PRFunction.ifZero_evaluates
      (selector.run inputs)
      (whenZero.run inputs)
      (whenPositive.run inputs)

/-- Select `whenEqual` exactly when `tag` equals the fixed natural tag. -/
def PRFunction.selectTag
    {arity : Nat}
    (tag : PRFunction arity)
    (expected : Nat)
    (whenEqual otherwise : PRFunction arity) :
    PRFunction arity :=
  PRFunction.select
    (PRFunction.composition PRFunction.equalBit
      (PRFunctionVector.cons tag
        (PRFunctionVector.singleton
          (PRFunction.constant arity expected))))
    otherwise
    whenEqual

/-- Fixed-tag selection is the equality-bit zero test. -/
@[simp] theorem PRFunction.run_selectTag
    {arity : Nat}
    (tag : PRFunction arity)
    (expected : Nat)
    (whenEqual otherwise : PRFunction arity)
    (inputs : NatVector arity) :
    (PRFunction.selectTag tag expected whenEqual otherwise).run inputs =
      natIfZero
        (natEqualBit (tag.run inputs) expected)
        (otherwise.run inputs)
        (whenEqual.run inputs) := by
  rw [PRFunction.selectTag, PRFunction.run_select]
  rw [PRFunction.run_composition,
    PRFunctionVector.run_cons,
    PRFunctionVector.run_singleton,
    PRFunction.run_constant,
    PRFunction.run_equalBit]

/-! ## One course-of-values substitution step -/

/-- Counter, previous trace, and substituted numeral are the step inputs. -/
def PRFunction.substitutionCounter : PRFunction 3 :=
  PRFunction.projection 3 0 (Nat.zero_lt_succ 2)

def PRFunction.substitutionHistory : PRFunction 3 :=
  PRFunction.projection 3 1
    (Nat.succ_lt_succ (Nat.zero_lt_succ 1))

def PRFunction.substitutionValue : PRFunction 3 :=
  PRFunction.projection 3 2
    (Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.zero_lt_succ 0)))

/-- The code processed by a step is the successor of its recursion counter. -/
def PRFunction.substitutionCurrentCode : PRFunction 3 :=
  PRFunction.composition PRFunction.successor
    (PRFunctionVector.singleton PRFunction.substitutionCounter)

/-- Outer syntax tag and payload of the current positive code. -/
def PRFunction.substitutionTag : PRFunction 3 :=
  PRFunction.composition PRFunction.unpairLeft
    (PRFunctionVector.singleton PRFunction.substitutionCounter)

def PRFunction.substitutionPayload : PRFunction 3 :=
  PRFunction.composition PRFunction.unpairRight
    (PRFunctionVector.singleton PRFunction.substitutionCounter)

/-- Left and right children of a binary syntax payload. -/
def PRFunction.substitutionPayloadLeft : PRFunction 3 :=
  PRFunction.composition PRFunction.unpairLeft
    (PRFunctionVector.singleton PRFunction.substitutionPayload)

def PRFunction.substitutionPayloadRight : PRFunction 3 :=
  PRFunction.composition PRFunction.unpairRight
    (PRFunctionVector.singleton PRFunction.substitutionPayload)

/-- Retrieve the earlier trace entry associated with a computed child code. -/
def PRFunction.substitutionLookup
    (child : PRFunction 3) :
    PRFunction 3 :=
  PRFunction.composition PRFunction.traceLookupCode
    (PRFunctionVector.cons PRFunction.substitutionCurrentCode
      (PRFunctionVector.cons child
        (PRFunctionVector.singleton PRFunction.substitutionHistory)))

/-- Read the transformed term or formula component of an earlier entry. -/
def PRFunction.substitutionTermLookup
    (child : PRFunction 3) :
    PRFunction 3 :=
  PRFunction.composition PRFunction.unpairLeft
    (PRFunctionVector.singleton (PRFunction.substitutionLookup child))

def PRFunction.substitutionFormulaLookup
    (child : PRFunction 3) :
    PRFunction 3 :=
  PRFunction.composition PRFunction.unpairRight
    (PRFunctionVector.singleton (PRFunction.substitutionLookup child))

/-- Rebuild unary and binary syntax nodes inside the three-input step context. -/
def PRFunction.substitutionUnary
    (constructor : PRFunction 1)
    (child : PRFunction 3) :
    PRFunction 3 :=
  PRFunction.composition constructor (PRFunctionVector.singleton child)

def PRFunction.substitutionBinary
    (constructor : PRFunction 2)
    (left right : PRFunction 3) :
    PRFunction 3 :=
  PRFunction.composition constructor
    (PRFunctionVector.cons left (PRFunctionVector.singleton right))

/-- Term reading of the current code after numeral substitution. -/
def PRFunction.substitutionTermAt : PRFunction 3 :=
  PRFunction.selectTag PRFunction.substitutionTag 0
    (PRFunction.composition PRFunction.numeralCode
      (PRFunctionVector.singleton PRFunction.substitutionValue))
    (PRFunction.selectTag PRFunction.substitutionTag 1
      (PRFunction.termZeroCode 3)
      (PRFunction.selectTag PRFunction.substitutionTag 2
        (PRFunction.substitutionUnary
          PRFunction.termSuccessorCode
          (PRFunction.substitutionTermLookup
            PRFunction.substitutionPayload))
        (PRFunction.selectTag PRFunction.substitutionTag 3
          (PRFunction.substitutionBinary
            PRFunction.termAddCode
            (PRFunction.substitutionTermLookup
              PRFunction.substitutionPayloadLeft)
            (PRFunction.substitutionTermLookup
              PRFunction.substitutionPayloadRight))
          (PRFunction.selectTag PRFunction.substitutionTag 4
            (PRFunction.substitutionBinary
              PRFunction.termMultiplyCode
              (PRFunction.substitutionTermLookup
                PRFunction.substitutionPayloadLeft)
              (PRFunction.substitutionTermLookup
                PRFunction.substitutionPayloadRight))
            (PRFunction.termZeroCode 3)))))

/-- Formula reading of the current code after numeral substitution. -/
def PRFunction.substitutionFormulaAt : PRFunction 3 :=
  PRFunction.selectTag PRFunction.substitutionTag 0
    (PRFunction.falsumCode 3)
    (PRFunction.selectTag PRFunction.substitutionTag 1
      (PRFunction.substitutionBinary
        PRFunction.formulaEqualCode
        (PRFunction.substitutionTermLookup
          PRFunction.substitutionPayloadLeft)
        (PRFunction.substitutionTermLookup
          PRFunction.substitutionPayloadRight))
      (PRFunction.selectTag PRFunction.substitutionTag 2
        (PRFunction.substitutionBinary
          PRFunction.formulaConjunctionCode
          (PRFunction.substitutionFormulaLookup
            PRFunction.substitutionPayloadLeft)
          (PRFunction.substitutionFormulaLookup
            PRFunction.substitutionPayloadRight))
        (PRFunction.selectTag PRFunction.substitutionTag 3
          (PRFunction.substitutionBinary
            PRFunction.formulaDisjunctionCode
            (PRFunction.substitutionFormulaLookup
              PRFunction.substitutionPayloadLeft)
            (PRFunction.substitutionFormulaLookup
              PRFunction.substitutionPayloadRight))
          (PRFunction.selectTag PRFunction.substitutionTag 4
            (PRFunction.substitutionBinary
              PRFunction.formulaImplicationCode
              (PRFunction.substitutionFormulaLookup
                PRFunction.substitutionPayloadLeft)
              (PRFunction.substitutionFormulaLookup
                PRFunction.substitutionPayloadRight))
            (PRFunction.selectTag PRFunction.substitutionTag 5
              (PRFunction.substitutionUnary
                PRFunction.formulaUniversalCode
                (PRFunction.substitutionFormulaLookup
                  PRFunction.substitutionPayload))
              (PRFunction.selectTag PRFunction.substitutionTag 6
                (PRFunction.substitutionUnary
                  PRFunction.formulaExistentialCode
                  (PRFunction.substitutionFormulaLookup
                    PRFunction.substitutionPayload))
                (PRFunction.falsumCode 3)))))))

/-- Pair both readings into the trace entry for the current code. -/
def PRFunction.substitutionEntry : PRFunction 3 :=
  PRFunction.substitutionBinary
    PRFunction.pair
    PRFunction.substitutionTermAt
    PRFunction.substitutionFormulaAt

/-- Build the course-of-values trace up to the supplied code. -/
def PRFunction.substitutionTrace : PRFunction 2 :=
  PRFunction.traceBuilder PRFunction.substitutionEntry

/-- Read the transformed formula component of the newest trace entry. -/
def PRFunction.substitutionResult : PRFunction 2 :=
  PRFunction.composition PRFunction.unpairRight
    (PRFunctionVector.singleton
      (PRFunction.composition PRFunction.unpairLeft
        (PRFunctionVector.singleton PRFunction.substitutionTrace)))

/--
Quantifier-blind self-substitution prototype.  This is not the diagonal
substitution exported by the arithmetic Tarski instance.
-/
def PRFunction.quantifierBlindDiagonalSubstitutionPrototype : PRFunction 1 :=
  PRFunction.composition PRFunction.substitutionResult
    (PRFunctionVector.cons PRFunction.identity
      (PRFunctionVector.singleton PRFunction.identity))

/-! ## Numeric trace computed by the program -/

@[simp] theorem PRFunction.run_substitutionCounter
    (counter history value : Nat) :
    PRFunction.substitutionCounter.run
        (NatVector.cons counter
          (NatVector.cons history (NatVector.cons value NatVector.nil))) =
      counter := rfl

@[simp] theorem PRFunction.run_substitutionHistory
    (counter history value : Nat) :
    PRFunction.substitutionHistory.run
        (NatVector.cons counter
          (NatVector.cons history (NatVector.cons value NatVector.nil))) =
      history := rfl

@[simp] theorem PRFunction.run_substitutionValue
    (counter history value : Nat) :
    PRFunction.substitutionValue.run
        (NatVector.cons counter
          (NatVector.cons history (NatVector.cons value NatVector.nil))) =
      value := rfl

@[simp] theorem PRFunction.run_substitutionCurrentCode
    (counter history value : Nat) :
    PRFunction.substitutionCurrentCode.run
        (NatVector.cons counter
          (NatVector.cons history
            (NatVector.cons value NatVector.nil))) =
      Nat.succ counter := rfl

@[simp] theorem PRFunction.run_substitutionTag
    (counter history value : Nat) :
    PRFunction.substitutionTag.run
        (NatVector.cons counter
          (NatVector.cons history
            (NatVector.cons value NatVector.nil))) =
      natUnpairLeft counter := by
  change PRFunction.unpairLeft.run
      (NatVector.cons counter NatVector.nil) = _
  exact PRFunction.run_unpairLeft counter

@[simp] theorem PRFunction.run_substitutionPayload
    (counter history value : Nat) :
    PRFunction.substitutionPayload.run
        (NatVector.cons counter
          (NatVector.cons history
            (NatVector.cons value NatVector.nil))) =
      natUnpairRight counter := by
  change PRFunction.unpairRight.run
      (NatVector.cons counter NatVector.nil) = _
  exact PRFunction.run_unpairRight counter

@[simp] theorem PRFunction.run_substitutionPayloadLeft
    (counter history value : Nat) :
    PRFunction.substitutionPayloadLeft.run
        (NatVector.cons counter
          (NatVector.cons history
            (NatVector.cons value NatVector.nil))) =
      natUnpairLeft (natUnpairRight counter) := by
  change PRFunction.unpairLeft.run
      (NatVector.cons
        (PRFunction.substitutionPayload.run
          (NatVector.cons counter
            (NatVector.cons history
              (NatVector.cons value NatVector.nil))))
        NatVector.nil) = _
  rw [PRFunction.run_substitutionPayload,
    PRFunction.run_unpairLeft]

@[simp] theorem PRFunction.run_substitutionPayloadRight
    (counter history value : Nat) :
    PRFunction.substitutionPayloadRight.run
        (NatVector.cons counter
          (NatVector.cons history
            (NatVector.cons value NatVector.nil))) =
      natUnpairRight (natUnpairRight counter) := by
  change PRFunction.unpairRight.run
      (NatVector.cons
        (PRFunction.substitutionPayload.run
          (NatVector.cons counter
            (NatVector.cons history
              (NatVector.cons value NatVector.nil))))
        NatVector.nil) = _
  rw [PRFunction.run_substitutionPayload,
    PRFunction.run_unpairRight]

@[simp] theorem PRFunction.run_substitutionLookup
    (child : PRFunction 3)
    (counter history value : Nat) :
    (PRFunction.substitutionLookup child).run
        (NatVector.cons counter
          (NatVector.cons history
            (NatVector.cons value NatVector.nil))) =
      natTraceLookupCode
        (Nat.succ counter)
        (child.run
          (NatVector.cons counter
            (NatVector.cons history
              (NatVector.cons value NatVector.nil))))
        history := by
  change PRFunction.traceLookupCode.run
      (NatVector.cons
        (PRFunction.substitutionCurrentCode.run
          (NatVector.cons counter
            (NatVector.cons history
              (NatVector.cons value NatVector.nil))))
        (NatVector.cons
          (child.run
            (NatVector.cons counter
              (NatVector.cons history
                (NatVector.cons value NatVector.nil))))
          (NatVector.cons
            (PRFunction.substitutionHistory.run
              (NatVector.cons counter
                (NatVector.cons history
                  (NatVector.cons value NatVector.nil))))
            NatVector.nil))) = _
  rw [PRFunction.run_substitutionCurrentCode,
    PRFunction.run_substitutionHistory,
    PRFunction.run_traceLookupCode]

@[simp] theorem PRFunction.run_substitutionTermLookup
    (child : PRFunction 3)
    (counter history value : Nat) :
    (PRFunction.substitutionTermLookup child).run
        (NatVector.cons counter
          (NatVector.cons history
            (NatVector.cons value NatVector.nil))) =
      natUnpairLeft
        (natTraceLookupCode
          (Nat.succ counter)
          (child.run
            (NatVector.cons counter
              (NatVector.cons history
                (NatVector.cons value NatVector.nil))))
          history) := by
  change PRFunction.unpairLeft.run
      (NatVector.cons
        ((PRFunction.substitutionLookup child).run
          (NatVector.cons counter
            (NatVector.cons history
              (NatVector.cons value NatVector.nil))))
        NatVector.nil) = _
  rw [PRFunction.run_substitutionLookup,
    PRFunction.run_unpairLeft]

@[simp] theorem PRFunction.run_substitutionFormulaLookup
    (child : PRFunction 3)
    (counter history value : Nat) :
    (PRFunction.substitutionFormulaLookup child).run
        (NatVector.cons counter
          (NatVector.cons history
            (NatVector.cons value NatVector.nil))) =
      natUnpairRight
        (natTraceLookupCode
          (Nat.succ counter)
          (child.run
            (NatVector.cons counter
              (NatVector.cons history
                (NatVector.cons value NatVector.nil))))
          history) := by
  change PRFunction.unpairRight.run
      (NatVector.cons
        ((PRFunction.substitutionLookup child).run
          (NatVector.cons counter
            (NatVector.cons history
              (NatVector.cons value NatVector.nil))))
        NatVector.nil) = _
  rw [PRFunction.run_substitutionLookup,
    PRFunction.run_unpairRight]

@[simp] theorem PRFunction.run_substitutionUnary
    (constructor : PRFunction 1)
    (child : PRFunction 3)
    (counter history value : Nat) :
    (PRFunction.substitutionUnary constructor child).run
        (NatVector.cons counter
          (NatVector.cons history
            (NatVector.cons value NatVector.nil))) =
      constructor.run
        (NatVector.cons
          (child.run
            (NatVector.cons counter
              (NatVector.cons history
                (NatVector.cons value NatVector.nil))))
          NatVector.nil) := rfl

@[simp] theorem PRFunction.run_substitutionBinary
    (constructor : PRFunction 2)
    (left right : PRFunction 3)
    (counter history value : Nat) :
    (PRFunction.substitutionBinary constructor left right).run
        (NatVector.cons counter
          (NatVector.cons history
            (NatVector.cons value NatVector.nil))) =
      constructor.run
        (NatVector.cons
          (left.run
            (NatVector.cons counter
              (NatVector.cons history
                (NatVector.cons value NatVector.nil))))
          (NatVector.cons
            (right.run
              (NatVector.cons counter
                (NatVector.cons history
                  (NatVector.cons value NatVector.nil))))
            NatVector.nil)) := rfl

/-- Newest-first numeric trace of all entries up to a code. -/
def substitutionTraceValue : Nat -> Nat -> Nat
  | 0, _value => 0
  | Nat.succ counter, value =>
      natPair
        (PRFunction.substitutionEntry.run
          (NatVector.cons counter
            (NatVector.cons (substitutionTraceValue counter value)
              (NatVector.cons value NatVector.nil))))
        (substitutionTraceValue counter value)

/-- Numeric entry generated for one positive code. -/
def substitutionEntryAt (code value : Nat) : Nat :=
  match code with
  | 0 => 0
  | Nat.succ counter =>
      PRFunction.substitutionEntry.run
        (NatVector.cons counter
          (NatVector.cons (substitutionTraceValue counter value)
            (NatVector.cons value NatVector.nil)))

/-- The trace definition exposes the named entry at its newest position. -/
theorem substitutionTraceValue_succ (counter value : Nat) :
    substitutionTraceValue (Nat.succ counter) value =
      natPair
        (substitutionEntryAt (Nat.succ counter) value)
        (substitutionTraceValue counter value) :=
  rfl

/-- Lookup by newest-first offset recovers every positive trace entry. -/
theorem substitutionTraceValue_lookup
    (code offset value : Nat)
    (positive : 0 < code) :
    natTraceLookup offset
        (substitutionTraceValue (code + offset) value) =
      substitutionEntryAt code value := by
  induction offset with
  | zero =>
      rw [Nat.add_zero]
      cases code with
      | zero => exact (Nat.lt_irrefl 0 positive).elim
      | succ code =>
          rw [substitutionTraceValue_succ,
            natTraceLookup_zero_pair]
  | succ offset inductionHypothesis =>
      rw [Nat.add_succ]
      change natTraceLookup (Nat.succ offset)
          (substitutionTraceValue (Nat.succ (code + offset)) value) = _
      rw [substitutionTraceValue_succ, natTraceLookup_succ_pair]
      exact inductionHypothesis

/--
Cancel a left additive prefix from truncated subtraction without importing
the proposition-extensional arithmetic normalization theorem.
-/
theorem natAddSubCancelLeftForSubstitution (left right : Nat) :
    (left + right) - left = right := by
  induction left with
  | zero =>
      rw [Nat.zero_add, Nat.sub_zero]
  | succ left inductionHypothesis =>
      rw [Nat.succ_add, Nat.add_one, Nat.succ_sub_succ_eq_sub]
      exact inductionHypothesis

/-- Absolute child-code lookup recovers the corresponding earlier entry. -/
theorem substitutionTraceValue_lookupCode
    (current child value : Nat)
    (childPositive : 0 < child)
    (childEarlier : child < current) :
    natTraceLookupCode current child
        (substitutionTraceValue current.pred value) =
      substitutionEntryAt child value := by
  have bounded : child <= current.pred :=
    Nat.le_pred_of_lt childEarlier
  cases natExistsEqAddOfLe bounded with
  | intro offset equality =>
      have lookup :=
        substitutionTraceValue_lookup child offset value childPositive
      have offsetEquality :
          (child + offset) - child = offset :=
        natAddSubCancelLeftForSubstitution child offset
      have lookupAtSum :
          natTraceLookup ((child + offset) - child)
              (substitutionTraceValue (child + offset) value) =
            substitutionEntryAt child value :=
        Eq.mp
          (congrArg
            (fun index =>
              natTraceLookup index
                  (substitutionTraceValue (child + offset) value) =
                substitutionEntryAt child value)
            offsetEquality.symm)
          lookup
      exact
        Eq.mp
          (congrArg
            (fun code =>
              natTraceLookup (code - child)
                  (substitutionTraceValue code value) =
                substitutionEntryAt child value)
            equality.symm)
          lookupAtSum

/-- The explicit trace-builder program computes the named numeric trace. -/
theorem PRFunction.run_substitutionTrace (code value : Nat) :
    PRFunction.substitutionTrace.run
        (NatVector.cons code
          (NatVector.cons value NatVector.nil)) =
      substitutionTraceValue code value := by
  induction code with
  | zero => rfl
  | succ code inductionHypothesis =>
      change
        (PRFunction.prependToPrevious
          PRFunction.substitutionEntry).run
            (NatVector.cons code
              (NatVector.cons
                (PRFunction.substitutionTrace.run
                  (NatVector.cons code
                    (NatVector.cons value NatVector.nil)))
                (NatVector.cons value NatVector.nil))) = _
      rw [inductionHypothesis]
      simp only [PRFunction.prependToPrevious,
        PRFunction.run_composition,
        PRFunctionVector.run_cons,
        PRFunctionVector.run_singleton,
        PRFunction.run_projection,
        PRFunction.run_pair]
      rfl

/-! ## Correctness on genuine term and formula codes -/

/-- One entry is exactly the pair of its term and formula readings. -/
theorem PRFunction.run_substitutionEntry
    (counter history value : Nat) :
    PRFunction.substitutionEntry.run
        (NatVector.cons counter
          (NatVector.cons history
            (NatVector.cons value NatVector.nil))) =
      natPair
        (PRFunction.substitutionTermAt.run
          (NatVector.cons counter
            (NatVector.cons history
              (NatVector.cons value NatVector.nil))))
        (PRFunction.substitutionFormulaAt.run
          (NatVector.cons counter
            (NatVector.cons history
              (NatVector.cons value NatVector.nil)))) := by
  change PRFunction.pair.run
      (NatVector.cons
        (PRFunction.substitutionTermAt.run
          (NatVector.cons counter
            (NatVector.cons history
              (NatVector.cons value NatVector.nil))))
        (NatVector.cons
          (PRFunction.substitutionFormulaAt.run
            (NatVector.cons counter
              (NatVector.cons history
                (NatVector.cons value NatVector.nil))))
          NatVector.nil)) = _
  rw [PRFunction.run_pair]

/-- The two unpaired entry components are the corresponding program readings. -/
theorem substitutionEntryAt_termComponent
    (counter value : Nat) :
    natUnpairLeft (substitutionEntryAt (Nat.succ counter) value) =
      PRFunction.substitutionTermAt.run
        (NatVector.cons counter
            (NatVector.cons (substitutionTraceValue counter value)
              (NatVector.cons value NatVector.nil))) := by
  unfold substitutionEntryAt
  change natUnpairLeft
      (PRFunction.substitutionEntry.run
        (NatVector.cons counter
          (NatVector.cons (substitutionTraceValue counter value)
            (NatVector.cons value NatVector.nil)))) = _
  rw [PRFunction.run_substitutionEntry, natUnpairLeft_pair]

theorem substitutionEntryAt_formulaComponent
    (counter value : Nat) :
    natUnpairRight (substitutionEntryAt (Nat.succ counter) value) =
      PRFunction.substitutionFormulaAt.run
        (NatVector.cons counter
            (NatVector.cons (substitutionTraceValue counter value)
              (NatVector.cons value NatVector.nil))) := by
  unfold substitutionEntryAt
  change natUnpairRight
      (PRFunction.substitutionEntry.run
        (NatVector.cons counter
          (NatVector.cons (substitutionTraceValue counter value)
            (NatVector.cons value NatVector.nil)))) = _
  rw [PRFunction.run_substitutionEntry, natUnpairRight_pair]

/-- Bound-variable codes select the numeral replacement branch. -/
theorem PRFunction.run_substitutionTermAt_bvar
    (index history value : Nat) :
    PRFunction.substitutionTermAt.run
        (NatVector.cons (natPair 0 index)
          (NatVector.cons history
            (NatVector.cons value NatVector.nil))) =
      (RawTerm.numeral value).code := by
  rw [PRFunction.substitutionTermAt,
    PRFunction.run_selectTag,
    PRFunction.run_substitutionTag,
    natUnpairLeft_pair]
  change
    (PRFunction.composition PRFunction.numeralCode
      (PRFunctionVector.singleton PRFunction.substitutionValue)).run
        (NatVector.cons (natPair 0 index)
          (NatVector.cons history
            (NatVector.cons value NatVector.nil))) =
      (RawTerm.numeral value).code
  change PRFunction.numeralCode.run
      (NatVector.cons value NatVector.nil) =
    (RawTerm.numeral value).code
  exact PRFunction.run_numeralCode value

/-- The arithmetic-zero code remains arithmetic zero. -/
theorem PRFunction.run_substitutionTermAt_zero
    (payload history value : Nat) :
    PRFunction.substitutionTermAt.run
        (NatVector.cons (natPair 1 payload)
          (NatVector.cons history
            (NatVector.cons value NatVector.nil))) =
      RawTerm.zero.code := by
  rw [PRFunction.substitutionTermAt,
    PRFunction.run_selectTag,
    PRFunction.run_substitutionTag,
    natUnpairLeft_pair,
    PRFunction.run_selectTag,
    PRFunction.run_substitutionTag,
    natUnpairLeft_pair]
  rfl

/-- A term-child lookup in the canonical trace returns its stored component. -/
theorem PRFunction.run_substitutionTermLookup_of_child
    (childProgram : PRFunction 3)
    (counter value childCode : Nat)
    (childPositive : 0 < childCode)
    (childEarlier : childCode < Nat.succ counter)
    (childRun :
      childProgram.run
          (NatVector.cons counter
            (NatVector.cons (substitutionTraceValue counter value)
              (NatVector.cons value NatVector.nil))) =
        childCode) :
    (PRFunction.substitutionTermLookup childProgram).run
        (NatVector.cons counter
          (NatVector.cons (substitutionTraceValue counter value)
            (NatVector.cons value NatVector.nil))) =
      natUnpairLeft (substitutionEntryAt childCode value) := by
  rw [PRFunction.run_substitutionTermLookup, childRun]
  exact congrArg natUnpairLeft
    (substitutionTraceValue_lookupCode
      (Nat.succ counter) childCode value childPositive childEarlier)

/-- A formula-child lookup in the canonical trace returns its stored component. -/
theorem PRFunction.run_substitutionFormulaLookup_of_child
    (childProgram : PRFunction 3)
    (counter value childCode : Nat)
    (childPositive : 0 < childCode)
    (childEarlier : childCode < Nat.succ counter)
    (childRun :
      childProgram.run
          (NatVector.cons counter
            (NatVector.cons (substitutionTraceValue counter value)
              (NatVector.cons value NatVector.nil))) =
        childCode) :
    (PRFunction.substitutionFormulaLookup childProgram).run
        (NatVector.cons counter
          (NatVector.cons (substitutionTraceValue counter value)
            (NatVector.cons value NatVector.nil))) =
      natUnpairRight (substitutionEntryAt childCode value) := by
  rw [PRFunction.run_substitutionFormulaLookup, childRun]
  exact congrArg natUnpairRight
    (substitutionTraceValue_lookupCode
      (Nat.succ counter) childCode value childPositive childEarlier)

theorem PRFunction.run_substitutionTermAt_succ
    (child history value : Nat) :
    PRFunction.substitutionTermAt.run
        (NatVector.cons (natPair 2 child)
          (NatVector.cons history
            (NatVector.cons value NatVector.nil))) =
      Nat.succ
        (natPair 2
          (natUnpairLeft
            (natTraceLookupCode
              (Nat.succ (natPair 2 child)) child history))) := by
  rw [PRFunction.substitutionTermAt,
    PRFunction.run_selectTag,
    PRFunction.run_substitutionTag,
    natUnpairLeft_pair,
    PRFunction.run_selectTag,
    PRFunction.run_substitutionTag,
    natUnpairLeft_pair,
    PRFunction.run_selectTag,
    PRFunction.run_substitutionTag,
    natUnpairLeft_pair]
  change PRFunction.termSuccessorCode.run
      (NatVector.cons
        ((PRFunction.substitutionTermLookup
          PRFunction.substitutionPayload).run
            (NatVector.cons (natPair 2 child)
              (NatVector.cons history
                (NatVector.cons value NatVector.nil))))
        NatVector.nil) = _
  rw [PRFunction.run_substitutionTermLookup,
    PRFunction.run_substitutionPayload,
    natUnpairRight_pair,
    PRFunction.run_termSuccessorCode]

theorem PRFunction.run_substitutionTermAt_add
    (left right history value : Nat) :
    PRFunction.substitutionTermAt.run
        (NatVector.cons (natPair 3 (natPair left right))
          (NatVector.cons history
            (NatVector.cons value NatVector.nil))) =
      Nat.succ
        (natPair 3
          (natPair
            (natUnpairLeft
              (natTraceLookupCode
                (Nat.succ (natPair 3 (natPair left right))) left history))
            (natUnpairLeft
              (natTraceLookupCode
                (Nat.succ (natPair 3 (natPair left right))) right history)))) := by
  rw [PRFunction.substitutionTermAt,
    PRFunction.run_selectTag,
    PRFunction.run_substitutionTag,
    natUnpairLeft_pair,
    PRFunction.run_selectTag,
    PRFunction.run_substitutionTag,
    natUnpairLeft_pair,
    PRFunction.run_selectTag,
    PRFunction.run_substitutionTag,
    natUnpairLeft_pair,
    PRFunction.run_selectTag,
    PRFunction.run_substitutionTag,
    natUnpairLeft_pair]
  change PRFunction.termAddCode.run
      (NatVector.cons
        ((PRFunction.substitutionTermLookup
          PRFunction.substitutionPayloadLeft).run
            (NatVector.cons (natPair 3 (natPair left right))
              (NatVector.cons history
                (NatVector.cons value NatVector.nil))))
        (NatVector.cons
          ((PRFunction.substitutionTermLookup
            PRFunction.substitutionPayloadRight).run
              (NatVector.cons (natPair 3 (natPair left right))
                (NatVector.cons history
                  (NatVector.cons value NatVector.nil))))
          NatVector.nil)) = _
  rw [PRFunction.run_substitutionTermLookup,
    PRFunction.run_substitutionPayloadLeft,
    natUnpairRight_pair,
    natUnpairLeft_pair,
    PRFunction.run_substitutionTermLookup,
    PRFunction.run_substitutionPayloadRight,
    natUnpairRight_pair,
    natUnpairRight_pair,
    PRFunction.run_termAddCode]

theorem PRFunction.run_substitutionTermAt_mul
    (left right history value : Nat) :
    PRFunction.substitutionTermAt.run
        (NatVector.cons (natPair 4 (natPair left right))
          (NatVector.cons history
            (NatVector.cons value NatVector.nil))) =
      Nat.succ
        (natPair 4
          (natPair
            (natUnpairLeft
              (natTraceLookupCode
                (Nat.succ (natPair 4 (natPair left right))) left history))
            (natUnpairLeft
              (natTraceLookupCode
                (Nat.succ (natPair 4 (natPair left right))) right history)))) := by
  rw [PRFunction.substitutionTermAt,
    PRFunction.run_selectTag,
    PRFunction.run_substitutionTag,
    natUnpairLeft_pair,
    PRFunction.run_selectTag,
    PRFunction.run_substitutionTag,
    natUnpairLeft_pair,
    PRFunction.run_selectTag,
    PRFunction.run_substitutionTag,
    natUnpairLeft_pair,
    PRFunction.run_selectTag,
    PRFunction.run_substitutionTag,
    natUnpairLeft_pair,
    PRFunction.run_selectTag,
    PRFunction.run_substitutionTag,
    natUnpairLeft_pair]
  change PRFunction.termMultiplyCode.run
      (NatVector.cons
        ((PRFunction.substitutionTermLookup
          PRFunction.substitutionPayloadLeft).run
            (NatVector.cons (natPair 4 (natPair left right))
              (NatVector.cons history
                (NatVector.cons value NatVector.nil))))
        (NatVector.cons
          ((PRFunction.substitutionTermLookup
            PRFunction.substitutionPayloadRight).run
              (NatVector.cons (natPair 4 (natPair left right))
                (NatVector.cons history
                  (NatVector.cons value NatVector.nil))))
          NatVector.nil)) = _
  rw [PRFunction.run_substitutionTermLookup,
    PRFunction.run_substitutionPayloadLeft,
    natUnpairRight_pair,
    natUnpairLeft_pair,
    PRFunction.run_substitutionTermLookup,
    PRFunction.run_substitutionPayloadRight,
    natUnpairRight_pair,
    natUnpairRight_pair,
    PRFunction.run_termMultiplyCode]

theorem PRFunction.run_substitutionFormulaAt_falsum
    (payload history value : Nat) :
    PRFunction.substitutionFormulaAt.run
        (NatVector.cons (natPair 0 payload)
          (NatVector.cons history
            (NatVector.cons value NatVector.nil))) =
      RawFormula.falsum.code := by
  rw [PRFunction.substitutionFormulaAt,
    PRFunction.run_selectTag,
    PRFunction.run_substitutionTag,
    natUnpairLeft_pair]
  change (PRFunction.falsumCode 3).run
      (NatVector.cons (natPair 0 payload)
        (NatVector.cons history
          (NatVector.cons value NatVector.nil))) =
    RawFormula.falsum.code
  exact PRFunction.run_falsumCode 3 _

theorem PRFunction.run_substitutionFormulaAt_equal
    (left right history value : Nat) :
    PRFunction.substitutionFormulaAt.run
        (NatVector.cons (natPair 1 (natPair left right))
          (NatVector.cons history
            (NatVector.cons value NatVector.nil))) =
      Nat.succ
        (natPair 1
          (natPair
            (natUnpairLeft
              (natTraceLookupCode
                (Nat.succ (natPair 1 (natPair left right))) left history))
            (natUnpairLeft
              (natTraceLookupCode
                (Nat.succ (natPair 1 (natPair left right))) right history)))) := by
  rw [PRFunction.substitutionFormulaAt,
    PRFunction.run_selectTag,
    PRFunction.run_substitutionTag,
    natUnpairLeft_pair,
    PRFunction.run_selectTag,
    PRFunction.run_substitutionTag,
    natUnpairLeft_pair]
  change PRFunction.formulaEqualCode.run
      (NatVector.cons
        ((PRFunction.substitutionTermLookup
          PRFunction.substitutionPayloadLeft).run
            (NatVector.cons (natPair 1 (natPair left right))
              (NatVector.cons history
                (NatVector.cons value NatVector.nil))))
        (NatVector.cons
          ((PRFunction.substitutionTermLookup
            PRFunction.substitutionPayloadRight).run
              (NatVector.cons (natPair 1 (natPair left right))
                (NatVector.cons history
                  (NatVector.cons value NatVector.nil))))
          NatVector.nil)) = _
  rw [PRFunction.run_substitutionTermLookup,
    PRFunction.run_substitutionPayloadLeft,
    natUnpairRight_pair,
    natUnpairLeft_pair,
    PRFunction.run_substitutionTermLookup,
    PRFunction.run_substitutionPayloadRight,
    natUnpairRight_pair,
    natUnpairRight_pair,
    PRFunction.run_formulaEqualCode]

theorem PRFunction.run_substitutionFormulaAt_conj
    (left right history value : Nat) :
    PRFunction.substitutionFormulaAt.run
        (NatVector.cons (natPair 2 (natPair left right))
          (NatVector.cons history
            (NatVector.cons value NatVector.nil))) =
      Nat.succ
        (natPair 2
          (natPair
            (natUnpairRight
              (natTraceLookupCode
                (Nat.succ (natPair 2 (natPair left right))) left history))
            (natUnpairRight
              (natTraceLookupCode
                (Nat.succ (natPair 2 (natPair left right))) right history)))) := by
  rw [PRFunction.substitutionFormulaAt,
    PRFunction.run_selectTag,
    PRFunction.run_substitutionTag,
    natUnpairLeft_pair,
    PRFunction.run_selectTag,
    PRFunction.run_substitutionTag,
    natUnpairLeft_pair,
    PRFunction.run_selectTag,
    PRFunction.run_substitutionTag,
    natUnpairLeft_pair]
  change PRFunction.formulaConjunctionCode.run
      (NatVector.cons
        ((PRFunction.substitutionFormulaLookup
          PRFunction.substitutionPayloadLeft).run
            (NatVector.cons (natPair 2 (natPair left right))
              (NatVector.cons history
                (NatVector.cons value NatVector.nil))))
        (NatVector.cons
          ((PRFunction.substitutionFormulaLookup
            PRFunction.substitutionPayloadRight).run
              (NatVector.cons (natPair 2 (natPair left right))
                (NatVector.cons history
                  (NatVector.cons value NatVector.nil))))
          NatVector.nil)) = _
  rw [PRFunction.run_substitutionFormulaLookup,
    PRFunction.run_substitutionPayloadLeft,
    natUnpairRight_pair,
    natUnpairLeft_pair,
    PRFunction.run_substitutionFormulaLookup,
    PRFunction.run_substitutionPayloadRight,
    natUnpairRight_pair,
    natUnpairRight_pair,
    PRFunction.run_formulaConjunctionCode]

theorem PRFunction.run_substitutionFormulaAt_disj
    (left right history value : Nat) :
    PRFunction.substitutionFormulaAt.run
        (NatVector.cons (natPair 3 (natPair left right))
          (NatVector.cons history
            (NatVector.cons value NatVector.nil))) =
      Nat.succ
        (natPair 3
          (natPair
            (natUnpairRight
              (natTraceLookupCode
                (Nat.succ (natPair 3 (natPair left right))) left history))
            (natUnpairRight
              (natTraceLookupCode
                (Nat.succ (natPair 3 (natPair left right))) right history)))) := by
  rw [PRFunction.substitutionFormulaAt,
    PRFunction.run_selectTag,
    PRFunction.run_substitutionTag,
    natUnpairLeft_pair,
    PRFunction.run_selectTag,
    PRFunction.run_substitutionTag,
    natUnpairLeft_pair,
    PRFunction.run_selectTag,
    PRFunction.run_substitutionTag,
    natUnpairLeft_pair,
    PRFunction.run_selectTag,
    PRFunction.run_substitutionTag,
    natUnpairLeft_pair]
  change PRFunction.formulaDisjunctionCode.run
      (NatVector.cons
        ((PRFunction.substitutionFormulaLookup
          PRFunction.substitutionPayloadLeft).run
            (NatVector.cons (natPair 3 (natPair left right))
              (NatVector.cons history
                (NatVector.cons value NatVector.nil))))
        (NatVector.cons
          ((PRFunction.substitutionFormulaLookup
            PRFunction.substitutionPayloadRight).run
              (NatVector.cons (natPair 3 (natPair left right))
                (NatVector.cons history
                  (NatVector.cons value NatVector.nil))))
          NatVector.nil)) = _
  rw [PRFunction.run_substitutionFormulaLookup,
    PRFunction.run_substitutionPayloadLeft,
    natUnpairRight_pair,
    natUnpairLeft_pair,
    PRFunction.run_substitutionFormulaLookup,
    PRFunction.run_substitutionPayloadRight,
    natUnpairRight_pair,
    natUnpairRight_pair,
    PRFunction.run_formulaDisjunctionCode]

theorem PRFunction.run_substitutionFormulaAt_impl
    (left right history value : Nat) :
    PRFunction.substitutionFormulaAt.run
        (NatVector.cons (natPair 4 (natPair left right))
          (NatVector.cons history
            (NatVector.cons value NatVector.nil))) =
      Nat.succ
        (natPair 4
          (natPair
            (natUnpairRight
              (natTraceLookupCode
                (Nat.succ (natPair 4 (natPair left right))) left history))
            (natUnpairRight
              (natTraceLookupCode
                (Nat.succ (natPair 4 (natPair left right))) right history)))) := by
  rw [PRFunction.substitutionFormulaAt,
    PRFunction.run_selectTag,
    PRFunction.run_substitutionTag,
    natUnpairLeft_pair,
    PRFunction.run_selectTag,
    PRFunction.run_substitutionTag,
    natUnpairLeft_pair,
    PRFunction.run_selectTag,
    PRFunction.run_substitutionTag,
    natUnpairLeft_pair,
    PRFunction.run_selectTag,
    PRFunction.run_substitutionTag,
    natUnpairLeft_pair,
    PRFunction.run_selectTag,
    PRFunction.run_substitutionTag,
    natUnpairLeft_pair]
  change PRFunction.formulaImplicationCode.run
      (NatVector.cons
        ((PRFunction.substitutionFormulaLookup
          PRFunction.substitutionPayloadLeft).run
            (NatVector.cons (natPair 4 (natPair left right))
              (NatVector.cons history
                (NatVector.cons value NatVector.nil))))
        (NatVector.cons
          ((PRFunction.substitutionFormulaLookup
            PRFunction.substitutionPayloadRight).run
              (NatVector.cons (natPair 4 (natPair left right))
                (NatVector.cons history
                  (NatVector.cons value NatVector.nil))))
          NatVector.nil)) = _
  rw [PRFunction.run_substitutionFormulaLookup,
    PRFunction.run_substitutionPayloadLeft,
    natUnpairRight_pair,
    natUnpairLeft_pair,
    PRFunction.run_substitutionFormulaLookup,
    PRFunction.run_substitutionPayloadRight,
    natUnpairRight_pair,
    natUnpairRight_pair,
    PRFunction.run_formulaImplicationCode]

theorem PRFunction.run_substitutionFormulaAt_all
    (body history value : Nat) :
    PRFunction.substitutionFormulaAt.run
        (NatVector.cons (natPair 5 body)
          (NatVector.cons history
            (NatVector.cons value NatVector.nil))) =
      Nat.succ
        (natPair 5
          (natUnpairRight
            (natTraceLookupCode
              (Nat.succ (natPair 5 body)) body history))) := by
  rw [PRFunction.substitutionFormulaAt,
    PRFunction.run_selectTag,
    PRFunction.run_substitutionTag,
    natUnpairLeft_pair,
    PRFunction.run_selectTag,
    PRFunction.run_substitutionTag,
    natUnpairLeft_pair,
    PRFunction.run_selectTag,
    PRFunction.run_substitutionTag,
    natUnpairLeft_pair,
    PRFunction.run_selectTag,
    PRFunction.run_substitutionTag,
    natUnpairLeft_pair,
    PRFunction.run_selectTag,
    PRFunction.run_substitutionTag,
    natUnpairLeft_pair,
    PRFunction.run_selectTag,
    PRFunction.run_substitutionTag,
    natUnpairLeft_pair]
  change PRFunction.formulaUniversalCode.run
      (NatVector.cons
        ((PRFunction.substitutionFormulaLookup
          PRFunction.substitutionPayload).run
            (NatVector.cons (natPair 5 body)
              (NatVector.cons history
                (NatVector.cons value NatVector.nil))))
        NatVector.nil) = _
  rw [PRFunction.run_substitutionFormulaLookup,
    PRFunction.run_substitutionPayload,
    natUnpairRight_pair,
    PRFunction.run_formulaUniversalCode]

theorem PRFunction.run_substitutionFormulaAt_ex
    (body history value : Nat) :
    PRFunction.substitutionFormulaAt.run
        (NatVector.cons (natPair 6 body)
          (NatVector.cons history
            (NatVector.cons value NatVector.nil))) =
      Nat.succ
        (natPair 6
          (natUnpairRight
            (natTraceLookupCode
              (Nat.succ (natPair 6 body)) body history))) := by
  rw [PRFunction.substitutionFormulaAt,
    PRFunction.run_selectTag,
    PRFunction.run_substitutionTag,
    natUnpairLeft_pair,
    PRFunction.run_selectTag,
    PRFunction.run_substitutionTag,
    natUnpairLeft_pair,
    PRFunction.run_selectTag,
    PRFunction.run_substitutionTag,
    natUnpairLeft_pair,
    PRFunction.run_selectTag,
    PRFunction.run_substitutionTag,
    natUnpairLeft_pair,
    PRFunction.run_selectTag,
    PRFunction.run_substitutionTag,
    natUnpairLeft_pair,
    PRFunction.run_selectTag,
    PRFunction.run_substitutionTag,
    natUnpairLeft_pair,
    PRFunction.run_selectTag,
    PRFunction.run_substitutionTag,
    natUnpairLeft_pair]
  change PRFunction.formulaExistentialCode.run
      (NatVector.cons
        ((PRFunction.substitutionFormulaLookup
          PRFunction.substitutionPayload).run
            (NatVector.cons (natPair 6 body)
              (NatVector.cons history
                (NatVector.cons value NatVector.nil))))
        NatVector.nil) = _
  rw [PRFunction.run_substitutionFormulaLookup,
    PRFunction.run_substitutionPayload,
    natUnpairRight_pair,
    PRFunction.run_formulaExistentialCode]

end HeytingArithmetic
end RelationalPerimeter

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.HeytingArithmetic.PRFunction.run_eq_of_evaluates
#print axioms RelationalPerimeter.HeytingArithmetic.PRFunction.substitutionEntry
#print axioms RelationalPerimeter.HeytingArithmetic.PRFunction.substitutionTrace
#print axioms RelationalPerimeter.HeytingArithmetic.PRFunction.substitutionResult
#print axioms RelationalPerimeter.HeytingArithmetic.PRFunction.quantifierBlindDiagonalSubstitutionPrototype
#print axioms RelationalPerimeter.HeytingArithmetic.natAddSubCancelLeftForSubstitution
#print axioms RelationalPerimeter.HeytingArithmetic.PRFunction.run_substitutionLookup
#print axioms RelationalPerimeter.HeytingArithmetic.PRFunction.run_substitutionTermLookup
#print axioms RelationalPerimeter.HeytingArithmetic.PRFunction.run_substitutionFormulaLookup
#print axioms RelationalPerimeter.HeytingArithmetic.substitutionTraceValue_lookupCode
#print axioms RelationalPerimeter.HeytingArithmetic.PRFunction.run_substitutionTrace
#print axioms RelationalPerimeter.HeytingArithmetic.PRFunction.run_substitutionEntry
#print axioms RelationalPerimeter.HeytingArithmetic.substitutionEntryAt_termComponent
#print axioms RelationalPerimeter.HeytingArithmetic.substitutionEntryAt_formulaComponent
#print axioms RelationalPerimeter.HeytingArithmetic.PRFunction.run_substitutionTermAt_bvar
#print axioms RelationalPerimeter.HeytingArithmetic.PRFunction.run_substitutionTermAt_zero
#print axioms RelationalPerimeter.HeytingArithmetic.PRFunction.run_substitutionTermLookup_of_child
#print axioms RelationalPerimeter.HeytingArithmetic.PRFunction.run_substitutionFormulaLookup_of_child
#print axioms RelationalPerimeter.HeytingArithmetic.PRFunction.run_substitutionTermAt_succ
#print axioms RelationalPerimeter.HeytingArithmetic.PRFunction.run_substitutionTermAt_add
#print axioms RelationalPerimeter.HeytingArithmetic.PRFunction.run_substitutionTermAt_mul
#print axioms RelationalPerimeter.HeytingArithmetic.PRFunction.run_substitutionFormulaAt_falsum
#print axioms RelationalPerimeter.HeytingArithmetic.PRFunction.run_substitutionFormulaAt_equal
#print axioms RelationalPerimeter.HeytingArithmetic.PRFunction.run_substitutionFormulaAt_conj
#print axioms RelationalPerimeter.HeytingArithmetic.PRFunction.run_substitutionFormulaAt_disj
#print axioms RelationalPerimeter.HeytingArithmetic.PRFunction.run_substitutionFormulaAt_impl
#print axioms RelationalPerimeter.HeytingArithmetic.PRFunction.run_substitutionFormulaAt_all
#print axioms RelationalPerimeter.HeytingArithmetic.PRFunction.run_substitutionFormulaAt_ex
/- AXIOM_AUDIT_END -/
