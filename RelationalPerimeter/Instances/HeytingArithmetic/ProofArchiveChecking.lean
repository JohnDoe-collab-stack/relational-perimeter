import RelationalPerimeter.Instances.HeytingArithmetic.ProofRuleChecking
import RelationalPerimeter.Instances.HeytingArithmetic.PrimitiveRecursiveBetaLookup

/-!
# Constructive decoding and certification of complete PA proof archives

The beta header fixes a finite chronological traversal.  Every line is
decoded before the proof-producing rule checker sees it.  The final checker
returns an actual closed PA derivation of the requested sentence, never a
semantic oracle or an unchecked Boolean assertion.
-/

namespace RelationalPerimeter
namespace HeytingArithmetic

/-- Decode exactly `remaining` beta components, beginning at `index`. -/
def decodeProofLinesFrom
    (header : ProofArchiveHeader) : Nat -> Nat -> Option (List ProofLine)
  | 0, _index => some []
  | Nat.succ remaining, index =>
      Option.bind (decodeProofLine (header.lineCode index)) (fun line =>
        Option.map (fun later => line :: later)
          (decodeProofLinesFrom header remaining (Nat.succ index)))

/-- Decode the finite line sequence designated by an arbitrary archive code.
    The zero-line archive is rejected because it has no conclusion. -/
def decodeNonemptyProofArchiveLines (proofCode : Nat) :
    Option (List ProofLine) :=
  let header := decodeProofArchiveHeader proofCode
  match header.lineCount with
  | 0 => none
  | Nat.succ remaining =>
      decodeProofLinesFrom header (Nat.succ remaining) 0

/-- Check a nonempty chronological list while retaining its last accepted
    proof.  Only already accepted lines are supplied as possible premises. -/
def checkPAProofLinesLastFrom
    (previous : List PackedPADerivation) :
    List ProofLine -> Option PackedPADerivation
  | [] => none
  | [line] => checkPAProofRule previous line
  | line :: next :: remaining =>
      Option.bind (checkPAProofRule previous line) (fun packed =>
        checkPAProofLinesLastFrom (previous ++ [packed])
          (next :: remaining))

def checkPAProofLinesLast (lines : List ProofLine) :
    Option PackedPADerivation :=
  checkPAProofLinesLastFrom [] lines

/-- A successful result is definitionally a closed PA derivation of the
    requested sentence. -/
def checkPAArchiveForSentence
    (proofCode : Nat)
    (sentence : Sentence) :
    Option
      (Derivation LogicMode.classical standardArithmeticTheory
        FormulaContext.nil sentence.scopedFormula) :=
  Option.bind (decodeNonemptyProofArchiveLines proofCode) (fun lines =>
    Option.bind (checkPAProofLinesLast lines) (fun packed =>
      packed.recover FormulaContext.nil sentence.scopedFormula))

end HeytingArithmetic
end RelationalPerimeter

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.HeytingArithmetic.decodeProofLinesFrom
#print axioms RelationalPerimeter.HeytingArithmetic.decodeNonemptyProofArchiveLines
#print axioms RelationalPerimeter.HeytingArithmetic.checkPAProofLinesLast
#print axioms RelationalPerimeter.HeytingArithmetic.checkPAArchiveForSentence
/- AXIOM_AUDIT_END -/
