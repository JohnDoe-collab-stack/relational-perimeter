import RelationalPerimeter.Constitution.HeytingArithmetic.ArithmeticAxiomChecking

/-!
# Constructive checking of proof leaves

This is the first proof-producing layer of the archive checker.  An accepted
leaf returns an actual object derivation.  The claimed bound, context,
conclusion, absence of premises, and canonical rule payload are all compared
numerically before the package is returned.
-/

namespace RelationalPerimeter
namespace HeytingArithmetic

structure PackedPADerivation where
  bound : Nat
  context : FormulaContext bound
  conclusion : ScopedFormula bound
  proof :
    Derivation LogicMode.classical standardArithmeticTheory
      context conclusion

def PackedPADerivation.contextCode
    (packed : PackedPADerivation) : Nat :=
  packed.context.quote

def PackedPADerivation.conclusionCode
    (packed : PackedPADerivation) : Nat :=
  packed.conclusion.raw.code

def proofLineMatchesPacked
    (line : ProofLine)
    (packed : PackedPADerivation)
    (expectedPremiseCode expectedParameterCode : Nat) : Bool :=
  (line.bound == packed.bound) &&
  (line.contextCode == packed.contextCode) &&
  (line.conclusionCode == packed.conclusionCode) &&
  (quoteNatList line.premises == expectedPremiseCode) &&
  (quoteNatList line.parameters == expectedParameterCode)

def acceptPackedProofLine
    (line : ProofLine)
    (packed : PackedPADerivation)
    (expectedPremiseCode expectedParameterCode : Nat) :
    Option PackedPADerivation :=
  if proofLineMatchesPacked line packed
      expectedPremiseCode expectedParameterCode then
    some packed
  else
    none

def checkPATheoryAxiomLeaf (line : ProofLine) :
    Option PackedPADerivation :=
  Option.bind
    (decodeFormulaContext line.bound line.contextCode)
    (fun context =>
      Option.bind
        (standardArithmeticAxiomCandidateFromCode
          line.bound (quoteNatList line.parameters))
        (fun candidate =>
          let packed : PackedPADerivation :=
            { bound := line.bound
              context := context
              conclusion := candidate.formula
              proof := Derivation.theoryAxiom candidate.witness }
          acceptPackedProofLine line packed 0
            (quoteNatList
              (standardArithmeticAxiomParameters candidate.witness))))

def checkPAHypothesisLeaf (line : ProofLine) :
    Option PackedPADerivation :=
  Option.bind
    (decodeFormulaContext line.bound line.contextCode)
    (fun context =>
      Option.bind
        (decodeScopedFormula line.bound line.conclusionCode)
        (fun conclusion =>
          Option.map
            (fun member =>
              { bound := line.bound
                context := context
                conclusion := conclusion
                proof := Derivation.hypothesis member })
            (contextMemberWitness conclusion context)))

def checkPAEqualityReflexivityLeaf (line : ProofLine) :
    Option PackedPADerivation :=
  let parameterCode := quoteNatList line.parameters
  let termCode := codedListEntry parameterCode 0
  Option.bind
    (decodeFormulaContext line.bound line.contextCode)
    (fun context =>
      Option.bind
        (decodeScopedTerm line.bound termCode)
        (fun term =>
          let packed : PackedPADerivation :=
            { bound := line.bound
              context := context
              conclusion := ScopedFormula.equal term term
              proof := Derivation.equalityReflexivity term }
          acceptPackedProofLine line packed 0
            (quoteNatList [term.raw.code])))

/-- Leaf dispatcher.  Non-leaf rule tags are rejected here and handled by
    the chronological rule checker built above this layer. -/
def checkPAProofLeaf (line : ProofLine) : Option PackedPADerivation :=
  if _theory : line.rule = ProofRuleTag.theoryAxiom then
    checkPATheoryAxiomLeaf line
  else if _hypothesis : line.rule = ProofRuleTag.hypothesis then
      Option.bind (checkPAHypothesisLeaf line) (fun packed =>
        acceptPackedProofLine line packed 0 0)
  else if _reflexivity :
      line.rule = ProofRuleTag.equalityReflexivity then
    checkPAEqualityReflexivityLeaf line
  else
    none

end HeytingArithmetic
end RelationalPerimeter

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.HeytingArithmetic.PackedPADerivation
#print axioms RelationalPerimeter.HeytingArithmetic.proofLineMatchesPacked
#print axioms RelationalPerimeter.HeytingArithmetic.checkPATheoryAxiomLeaf
#print axioms RelationalPerimeter.HeytingArithmetic.checkPAHypothesisLeaf
#print axioms RelationalPerimeter.HeytingArithmetic.checkPAEqualityReflexivityLeaf
#print axioms RelationalPerimeter.HeytingArithmetic.checkPAProofLeaf
/- AXIOM_AUDIT_END -/
