import RelationalPerimeter.Constitution.HeytingArithmetic.ProofRuleChecking
import RelationalPerimeter.Constitution.HeytingArithmetic.TheoryHistoryCoding

/-!
# Proof-producing checker for finite theory histories

This is the typed side of the uniform numeric verifier.  Its proof objects live
in `Derivation intuitionistic history.theory`; standard arithmetic postulates
and added history sentences are reconstructed as positive `HistoryAxiom`
witnesses.
-/

namespace RelationalPerimeter
namespace HeytingArithmetic

/-! ## Axiom payloads and uniform encoder -/

def historyAxiomParameters
    {history : TheoryHistory}
    {bound : Nat}
    {formula : ScopedFormula bound} :
    HistoryAxiom history formula -> List Nat
  | HistoryAxiom.arithmetic witness =>
      standardArithmeticAxiomParameters witness
  | @HistoryAxiom.added _ _ sentence _evidence => [7, sentence.quote]

def encodeHistoryDerivation
    {history : TheoryHistory}
    {bound : Nat}
    {context : FormulaContext bound}
    {conclusion : ScopedFormula bound}
    (proof :
      Derivation LogicMode.intuitionistic history.theory context conclusion) :
    ProofArchive :=
  encodeDerivationWithAxiomParameters historyAxiomParameters proof

structure PackedHistoryAxiom
    (history : TheoryHistory)
    (bound : Nat) where
  formula : ScopedFormula bound
  witness : HistoryAxiom history formula

def standardPackedHistoryAxiom
    (history : TheoryHistory)
    {bound : Nat}
    (candidate : PackedStandardArithmeticAxiom bound) :
    PackedHistoryAxiom history bound :=
  { formula := candidate.formula
    witness := HistoryAxiom.arithmetic candidate.witness }

def addedHistoryAxiomCandidate
    (history : TheoryHistory)
    (bound sentenceCode : Nat) : Option (PackedHistoryAxiom history bound) :=
  match history with
  | TheoryHistory.root => none
  | TheoryHistory.extend previous newest =>
      if _same : newest.quote = sentenceCode then
        some
          { formula := newest.atBound bound
            witness := HistoryAxiom.added TheoryHistory.Contains.newest }
      else
        Option.map
          (fun earlier =>
            { formula := earlier.formula
              witness := earlier.witness.preserve })
          (addedHistoryAxiomCandidate previous bound sentenceCode)

def historyAxiomCandidateFromCode
    (history : TheoryHistory)
    (bound parameterCode : Nat) : Option (PackedHistoryAxiom history bound) :=
  let tag := codedListEntry parameterCode 0
  if tag = 7 then
    addedHistoryAxiomCandidate history bound
      (codedListEntry parameterCode 1)
  else
    Option.map (standardPackedHistoryAxiom history)
      (standardArithmeticAxiomCandidateFromCode bound parameterCode)

/-! ## Packed history derivations -/

structure PackedHistoryDerivation (history : TheoryHistory) where
  bound : Nat
  context : FormulaContext bound
  conclusion : ScopedFormula bound
  proof : Derivation LogicMode.intuitionistic history.theory context conclusion

def PackedHistoryDerivation.contextCode
    {history : TheoryHistory}
    (packed : PackedHistoryDerivation history) : Nat := packed.context.quote

def PackedHistoryDerivation.conclusionCode
    {history : TheoryHistory}
    (packed : PackedHistoryDerivation history) : Nat :=
  packed.conclusion.raw.code

def PackedHistoryDerivation.recover
    {history : TheoryHistory}
    {bound : Nat}
    (context : FormulaContext bound)
    (conclusion : ScopedFormula bound)
    (packed : PackedHistoryDerivation history) :
    Option (Derivation LogicMode.intuitionistic history.theory context conclusion) := by
  by_cases sameBound : packed.bound = bound
  · subst bound
    by_cases sameContextCode : packed.context.quote = context.quote
    · have sameContext : packed.context = context :=
        FormulaContext.eq_of_quote_eq sameContextCode
      subst context
      by_cases sameConclusionCode :
          packed.conclusion.raw.code = conclusion.raw.code
      · have sameConclusion : packed.conclusion = conclusion :=
          ScopedFormula.eq_of_code_eq sameConclusionCode
        subst conclusion
        exact some packed.proof
      · exact none
    · exact none
  · exact none

def PackedHistoryDerivation.accept
    {history : TheoryHistory}
    (line : ProofLine)
    (packed : PackedHistoryDerivation history)
    (premises parameters : List Nat) : Option (PackedHistoryDerivation history) :=
  if (line.bound == packed.bound) &&
      (line.contextCode == packed.contextCode) &&
      (line.conclusionCode == packed.conclusionCode) &&
      (quoteNatList line.premises == quoteNatList premises) &&
      (quoteNatList line.parameters == quoteNatList parameters) then
    some packed
  else none

def PackedHistoryDerivation.weakenCandidate
    {history : TheoryHistory}
    (premise : PackedHistoryDerivation history)
    (extra : ScopedFormula premise.bound) :
    Option (PackedHistoryDerivation history) :=
  match premise.recover premise.context premise.conclusion with
  | none => none
  | some proof =>
      some
        { bound := premise.bound
          context := FormulaContext.cons extra premise.context
          conclusion := premise.conclusion
          proof := Derivation.weaken extra proof }

/-! ## Leaves -/

def checkHistoryTheoryAxiomLeaf
    (history : TheoryHistory)
    (line : ProofLine) : Option (PackedHistoryDerivation history) :=
  Option.bind (decodeFormulaContext line.bound line.contextCode) (fun context =>
    Option.bind
      (historyAxiomCandidateFromCode history line.bound
        (quoteNatList line.parameters)) (fun candidate =>
        let packed : PackedHistoryDerivation history :=
          { bound := line.bound
            context := context
            conclusion := candidate.formula
            proof := Derivation.theoryAxiom candidate.witness }
        packed.accept line [] (historyAxiomParameters candidate.witness)))

def checkHistoryHypothesisLeaf
    (history : TheoryHistory)
    (line : ProofLine) : Option (PackedHistoryDerivation history) :=
  Option.bind (decodeFormulaContext line.bound line.contextCode) (fun context =>
    Option.bind (decodeScopedFormula line.bound line.conclusionCode)
      (fun conclusion =>
        Option.bind (contextMemberWitness conclusion context) (fun member =>
          let packed : PackedHistoryDerivation history :=
            { bound := line.bound
              context := context
              conclusion := conclusion
              proof := Derivation.hypothesis member }
          packed.accept line [] [])))

def checkHistoryEqualityReflexivityLeaf
    (history : TheoryHistory)
    (line : ProofLine) : Option (PackedHistoryDerivation history) :=
  let termCode := codedListEntry (quoteNatList line.parameters) 0
  Option.bind (decodeFormulaContext line.bound line.contextCode) (fun context =>
    Option.bind (decodeScopedTerm line.bound termCode) (fun term =>
      let packed : PackedHistoryDerivation history :=
        { bound := line.bound
          context := context
          conclusion := ScopedFormula.equal term term
          proof := Derivation.equalityReflexivity term }
      packed.accept line [] [term.raw.code]))

def checkHistoryProofLeaf
    (history : TheoryHistory)
    (line : ProofLine) : Option (PackedHistoryDerivation history) :=
  if line.rule = ProofRuleTag.theoryAxiom then
    checkHistoryTheoryAxiomLeaf history line
  else if line.rule = ProofRuleTag.hypothesis then
    checkHistoryHypothesisLeaf history line
  else if line.rule = ProofRuleTag.equalityReflexivity then
    checkHistoryEqualityReflexivityLeaf history line
  else none

end HeytingArithmetic
end RelationalPerimeter

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.HeytingArithmetic.historyAxiomParameters
#print axioms RelationalPerimeter.HeytingArithmetic.encodeHistoryDerivation
#print axioms RelationalPerimeter.HeytingArithmetic.addedHistoryAxiomCandidate
#print axioms RelationalPerimeter.HeytingArithmetic.PackedHistoryDerivation
#print axioms RelationalPerimeter.HeytingArithmetic.checkHistoryProofLeaf
/- AXIOM_AUDIT_END -/
