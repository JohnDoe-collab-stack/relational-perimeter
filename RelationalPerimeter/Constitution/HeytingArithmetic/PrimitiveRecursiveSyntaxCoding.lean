import RelationalPerimeter.Constitution.HeytingArithmetic.PrimitiveRecursiveTrace

/-!
# Primitive-recursive constructors for syntax codes

The code constructors below rebuild well-formed term and formula nodes from
already transformed child codes.  They are the local branches used by the
course-of-values substitution trace.
-/

namespace RelationalPerimeter
namespace HeytingArithmetic

/-- Code constructor `payload |-> S(pair tag payload)`. -/
def PRFunction.taggedUnaryCode (tag : Nat) : PRFunction 1 :=
  PRFunction.composition
    PRFunction.successor
    (PRFunctionVector.singleton
      (PRFunction.composition
        PRFunction.pair
        (PRFunctionVector.cons
          (PRFunction.constant 1 tag)
          (PRFunctionVector.singleton PRFunction.identity))))

/-- The unary constructor program computes its tagged code. -/
theorem PRFunction.taggedUnaryCode_evaluates (tag payload : Nat) :
    PRFunction.Evaluates
      (PRFunction.taggedUnaryCode tag)
      (NatVector.cons payload NatVector.nil)
      (Nat.succ (natPair tag payload)) := by
  apply PRFunction.Evaluates.composition
  · apply PRFunctionVector.Evaluates.cons
    · apply PRFunction.Evaluates.composition
      · apply PRFunctionVector.Evaluates.cons
        · exact PRFunction.constant_evaluates 1 tag
            (NatVector.cons payload NatVector.nil)
        · apply PRFunctionVector.Evaluates.cons
          · exact PRFunction.Evaluates.projection
              0
              (Nat.zero_lt_succ 0)
              (NatVector.cons payload NatVector.nil)
          · exact PRFunctionVector.Evaluates.nil
              (NatVector.cons payload NatVector.nil)
      · exact PRFunction.pair_evaluates tag payload
    · exact PRFunctionVector.Evaluates.nil
        (NatVector.cons payload NatVector.nil)
  · exact PRFunction.Evaluates.successor
      (NatVector.cons (natPair tag payload) NatVector.nil)

/-- Pair the two inputs as a payload. -/
def PRFunction.pairInputs : PRFunction 2 :=
  PRFunction.pair

/-- Code constructor `(left,right) |-> S(pair tag (pair left right))`. -/
def PRFunction.taggedBinaryCode (tag : Nat) : PRFunction 2 :=
  PRFunction.composition
    PRFunction.successor
    (PRFunctionVector.singleton
      (PRFunction.composition
        PRFunction.pair
        (PRFunctionVector.cons
          (PRFunction.constant 2 tag)
          (PRFunctionVector.singleton PRFunction.pairInputs))))

/-- The binary constructor program computes its tagged code. -/
theorem PRFunction.taggedBinaryCode_evaluates
    (tag left right : Nat) :
    PRFunction.Evaluates
      (PRFunction.taggedBinaryCode tag)
      (NatVector.cons left
        (NatVector.cons right NatVector.nil))
      (Nat.succ (natPair tag (natPair left right))) := by
  apply PRFunction.Evaluates.composition
  · apply PRFunctionVector.Evaluates.cons
    · apply PRFunction.Evaluates.composition
      · apply PRFunctionVector.Evaluates.cons
        · exact PRFunction.constant_evaluates 2 tag
            (NatVector.cons left
              (NatVector.cons right NatVector.nil))
        · apply PRFunctionVector.Evaluates.cons
          · exact PRFunction.pair_evaluates left right
          · exact PRFunctionVector.Evaluates.nil
              (NatVector.cons left
                (NatVector.cons right NatVector.nil))
      · exact PRFunction.pair_evaluates tag (natPair left right)
    · exact PRFunctionVector.Evaluates.nil
        (NatVector.cons left
          (NatVector.cons right NatVector.nil))
  · exact PRFunction.Evaluates.successor
      (NatVector.cons (natPair tag (natPair left right)) NatVector.nil)

/-- Code of a bound-variable term. -/
def PRFunction.boundVariableCode : PRFunction 1 :=
  PRFunction.taggedUnaryCode 0

/-- Code of the arithmetic zero term, at any input arity. -/
def PRFunction.termZeroCode (arity : Nat) : PRFunction arity :=
  PRFunction.constant arity RawTerm.zero.code

/-- Code constructor for term successor. -/
def PRFunction.termSuccessorCode : PRFunction 1 :=
  PRFunction.taggedUnaryCode 2

/-- Code constructor for term addition. -/
def PRFunction.termAddCode : PRFunction 2 :=
  PRFunction.taggedBinaryCode 3

/-- Code constructor for term multiplication. -/
def PRFunction.termMultiplyCode : PRFunction 2 :=
  PRFunction.taggedBinaryCode 4

/-- Code of falsity, at any input arity. -/
def PRFunction.falsumCode (arity : Nat) : PRFunction arity :=
  PRFunction.constant arity RawFormula.falsum.code

/-- Code constructor for equality. -/
def PRFunction.formulaEqualCode : PRFunction 2 :=
  PRFunction.taggedBinaryCode 1

/-- Code constructor for conjunction. -/
def PRFunction.formulaConjunctionCode : PRFunction 2 :=
  PRFunction.taggedBinaryCode 2

/-- Code constructor for disjunction. -/
def PRFunction.formulaDisjunctionCode : PRFunction 2 :=
  PRFunction.taggedBinaryCode 3

/-- Code constructor for implication. -/
def PRFunction.formulaImplicationCode : PRFunction 2 :=
  PRFunction.taggedBinaryCode 4

/-- Code constructor for universal quantification. -/
def PRFunction.formulaUniversalCode : PRFunction 1 :=
  PRFunction.taggedUnaryCode 5

/-- Code constructor for existential quantification. -/
def PRFunction.formulaExistentialCode : PRFunction 1 :=
  PRFunction.taggedUnaryCode 6

/-- Build the next numeral code from the preceding numeral code. -/
def PRFunction.numeralCodeStep : PRFunction 2 :=
  PRFunction.composition
    PRFunction.termSuccessorCode
    (PRFunctionVector.singleton
      (PRFunction.projection 2 1
        (Nat.succ_lt_succ (Nat.zero_lt_succ 0))))

/-- Primitive-recursive code of the standard arithmetic numeral. -/
def PRFunction.numeralCode : PRFunction 1 :=
  PRFunction.primitiveRecursion
    (PRFunction.termZeroCode 0)
    PRFunction.numeralCodeStep

/-- The explicit numeral-code program computes the syntactic numeral code. -/
theorem PRFunction.numeralCode_evaluates (value : Nat) :
    PRFunction.Evaluates
      PRFunction.numeralCode
      (NatVector.cons value NatVector.nil)
      (RawTerm.numeral value).code := by
  induction value with
  | zero =>
      exact PRFunction.Evaluates.primitiveZero
        (PRFunction.constant_evaluates 0 RawTerm.zero.code NatVector.nil)
  | succ value inductionHypothesis =>
      apply PRFunction.Evaluates.primitiveSucc inductionHypothesis
      apply PRFunction.Evaluates.composition
      · apply PRFunctionVector.Evaluates.cons
        · exact PRFunction.Evaluates.projection
            1
            (Nat.succ_lt_succ (Nat.zero_lt_succ 0))
            (NatVector.cons value
              (NatVector.cons (RawTerm.numeral value).code NatVector.nil))
        · exact PRFunctionVector.Evaluates.nil
            (NatVector.cons value
              (NatVector.cons (RawTerm.numeral value).code NatVector.nil))
      · exact PRFunction.taggedUnaryCode_evaluates
          2
          (RawTerm.numeral value).code

end HeytingArithmetic
end RelationalPerimeter

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.HeytingArithmetic.PRFunction.taggedUnaryCode
#print axioms RelationalPerimeter.HeytingArithmetic.PRFunction.taggedUnaryCode_evaluates
#print axioms RelationalPerimeter.HeytingArithmetic.PRFunction.taggedBinaryCode
#print axioms RelationalPerimeter.HeytingArithmetic.PRFunction.taggedBinaryCode_evaluates
#print axioms RelationalPerimeter.HeytingArithmetic.PRFunction.boundVariableCode
#print axioms RelationalPerimeter.HeytingArithmetic.PRFunction.termZeroCode
#print axioms RelationalPerimeter.HeytingArithmetic.PRFunction.termSuccessorCode
#print axioms RelationalPerimeter.HeytingArithmetic.PRFunction.termAddCode
#print axioms RelationalPerimeter.HeytingArithmetic.PRFunction.termMultiplyCode
#print axioms RelationalPerimeter.HeytingArithmetic.PRFunction.falsumCode
#print axioms RelationalPerimeter.HeytingArithmetic.PRFunction.formulaEqualCode
#print axioms RelationalPerimeter.HeytingArithmetic.PRFunction.formulaConjunctionCode
#print axioms RelationalPerimeter.HeytingArithmetic.PRFunction.formulaDisjunctionCode
#print axioms RelationalPerimeter.HeytingArithmetic.PRFunction.formulaImplicationCode
#print axioms RelationalPerimeter.HeytingArithmetic.PRFunction.formulaUniversalCode
#print axioms RelationalPerimeter.HeytingArithmetic.PRFunction.formulaExistentialCode
#print axioms RelationalPerimeter.HeytingArithmetic.PRFunction.numeralCode
#print axioms RelationalPerimeter.HeytingArithmetic.PRFunction.numeralCode_evaluates
/- AXIOM_AUDIT_END -/
