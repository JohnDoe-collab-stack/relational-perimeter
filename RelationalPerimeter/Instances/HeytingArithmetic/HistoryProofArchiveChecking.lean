import RelationalPerimeter.Instances.HeytingArithmetic.HistoryProofRuleChecking
import RelationalPerimeter.Instances.HeytingArithmetic.ProofArchiveChecking

/-!
# Complete proof-producing archive checker for theory histories
-/

namespace RelationalPerimeter
namespace HeytingArithmetic

def checkHistoryProofLinesLastFrom
    (history : TheoryHistory)
    (previous : List (PackedHistoryDerivation history)) :
    List ProofLine -> Option (PackedHistoryDerivation history)
  | [] => none
  | [line] => checkHistoryProofRule history previous line
  | line :: next :: remaining =>
      Option.bind (checkHistoryProofRule history previous line) (fun packed =>
        checkHistoryProofLinesLastFrom history (previous ++ [packed])
          (next :: remaining))

def checkHistoryProofLinesLast
    (history : TheoryHistory)
    (lines : List ProofLine) : Option (PackedHistoryDerivation history) :=
  checkHistoryProofLinesLastFrom history [] lines

def checkHistoryArchiveForSentence
    (history : TheoryHistory)
    (proofCode : Nat)
    (sentence : Sentence) :
    Option
      (Derivation LogicMode.intuitionistic history.theory
        FormulaContext.nil sentence.scopedFormula) :=
  Option.bind (decodeNonemptyProofArchiveLines proofCode) (fun lines =>
    Option.bind (checkHistoryProofLinesLast history lines) (fun packed =>
      packed.recover FormulaContext.nil sentence.scopedFormula))

end HeytingArithmetic
end RelationalPerimeter

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.HeytingArithmetic.checkHistoryProofLinesLast
#print axioms RelationalPerimeter.HeytingArithmetic.checkHistoryArchiveForSentence
/- AXIOM_AUDIT_END -/
