import RelationalPerimeter.Constitution.HeytingArithmetic.HistoryProofChecking

/-!
# Chronological proof-producing rules over a theory history

Every rule consumes only previously reconstructed history derivations.  The
implementation mirrors the shared arithmetic checker, but its logic mode is
intuitionistic and its theory index is the finite intrinsic `TheoryHistory`.
-/

namespace RelationalPerimeter
namespace HeytingArithmetic

def packedHistoryDerivationAt
    {history : TheoryHistory} :
    List (PackedHistoryDerivation history) -> Nat ->
      Option (PackedHistoryDerivation history)
  | [], _index => none
  | head :: _tail, 0 => some head
  | _head :: tail, Nat.succ index => packedHistoryDerivationAt tail index

/-! ## Unary rules -/

def checkHistoryWeakenRule
    {history : TheoryHistory}
    (line : ProofLine) (reference : Nat)
    (premise : PackedHistoryDerivation history) :
    Option (PackedHistoryDerivation history) :=
  Option.bind (decodeScopedFormula premise.bound
      (codedListEntry (quoteNatList line.parameters) 0)) (fun extra =>
    Option.bind (premise.weakenCandidate extra) (fun packed =>
      packed.accept line [reference] [extra.raw.code]))

def checkHistoryImplicationIntroductionRule
    {history : TheoryHistory}
    (line : ProofLine) (reference : Nat)
    (premise : PackedHistoryDerivation history) :
    Option (PackedHistoryDerivation history) :=
  match premise.context with
  | FormulaContext.nil => none
  | FormulaContext.cons left context =>
      Option.bind
        (premise.recover (FormulaContext.cons left context)
          premise.conclusion) (fun proof =>
        let packed : PackedHistoryDerivation history :=
          { bound := premise.bound
            context := context
            conclusion := ScopedFormula.impl left premise.conclusion
            proof := Derivation.implicationIntroduction proof }
        packed.accept line [reference] [])

def checkHistoryConjunctionEliminationLeftRule
    {history : TheoryHistory}
    (line : ProofLine) (reference : Nat)
    (premise : PackedHistoryDerivation history) :
    Option (PackedHistoryDerivation history) :=
  Option.bind (conjunctionView premise.conclusion.raw.code) (fun parts =>
    Option.bind (scopedFormulaCandidate premise.bound parts.left) (fun left =>
      Option.bind (scopedFormulaCandidate premise.bound parts.right) (fun right =>
        Option.bind
          (premise.recover premise.context (ScopedFormula.conj left right))
          (fun proof =>
            let packed : PackedHistoryDerivation history :=
              { bound := premise.bound
                context := premise.context
                conclusion := left
                proof := Derivation.conjunctionEliminationLeft proof }
            packed.accept line [reference] []))))

def checkHistoryConjunctionEliminationRightRule
    {history : TheoryHistory}
    (line : ProofLine) (reference : Nat)
    (premise : PackedHistoryDerivation history) :
    Option (PackedHistoryDerivation history) :=
  Option.bind (conjunctionView premise.conclusion.raw.code) (fun parts =>
    Option.bind (scopedFormulaCandidate premise.bound parts.left) (fun left =>
      Option.bind (scopedFormulaCandidate premise.bound parts.right) (fun right =>
        Option.bind
          (premise.recover premise.context (ScopedFormula.conj left right))
          (fun proof =>
            let packed : PackedHistoryDerivation history :=
              { bound := premise.bound
                context := premise.context
                conclusion := right
                proof := Derivation.conjunctionEliminationRight proof }
            packed.accept line [reference] []))))

def checkHistoryDisjunctionIntroductionLeftRule
    {history : TheoryHistory}
    (line : ProofLine) (reference : Nat)
    (premise : PackedHistoryDerivation history) :
    Option (PackedHistoryDerivation history) :=
  Option.bind (decodeScopedFormula premise.bound line.conclusionCode)
    (fun conclusion =>
      Option.bind (disjunctionView conclusion.raw.code) (fun parts =>
        Option.bind (scopedFormulaCandidate premise.bound parts.left) (fun left =>
          Option.bind (scopedFormulaCandidate premise.bound parts.right) (fun right =>
            Option.bind (premise.recover premise.context left) (fun proof =>
              let packed : PackedHistoryDerivation history :=
                { bound := premise.bound
                  context := premise.context
                  conclusion := ScopedFormula.disj left right
                  proof := Derivation.disjunctionIntroductionLeft proof }
              packed.accept line [reference] [])))))

def checkHistoryDisjunctionIntroductionRightRule
    {history : TheoryHistory}
    (line : ProofLine) (reference : Nat)
    (premise : PackedHistoryDerivation history) :
    Option (PackedHistoryDerivation history) :=
  Option.bind (decodeScopedFormula premise.bound line.conclusionCode)
    (fun conclusion =>
      Option.bind (disjunctionView conclusion.raw.code) (fun parts =>
        Option.bind (scopedFormulaCandidate premise.bound parts.left) (fun left =>
          Option.bind (scopedFormulaCandidate premise.bound parts.right) (fun right =>
            Option.bind (premise.recover premise.context right) (fun proof =>
              let packed : PackedHistoryDerivation history :=
                { bound := premise.bound
                  context := premise.context
                  conclusion := ScopedFormula.disj left right
                  proof := Derivation.disjunctionIntroductionRight proof }
              packed.accept line [reference] [])))))

def checkHistoryFalsumEliminationRule
    {history : TheoryHistory}
    (line : ProofLine) (reference : Nat)
    (premise : PackedHistoryDerivation history) :
    Option (PackedHistoryDerivation history) :=
  Option.bind (decodeScopedFormula premise.bound line.conclusionCode)
    (fun conclusion =>
      Option.bind
        (premise.recover premise.context
          (ScopedFormula.falsum premise.bound)) (fun proof =>
        let packed : PackedHistoryDerivation history :=
          { bound := premise.bound
            context := premise.context
            conclusion := conclusion
            proof := Derivation.falsumElimination proof }
        packed.accept line [reference] []))

def checkHistoryUniversalIntroductionRule
    {history : TheoryHistory}
    (line : ProofLine) (reference : Nat)
    (premise : PackedHistoryDerivation history) :
    Option (PackedHistoryDerivation history) :=
  Option.bind (decodeFormulaContext line.bound line.contextCode) (fun context =>
    Option.bind (decodeScopedFormula line.bound line.conclusionCode)
      (fun conclusion =>
        Option.bind (universalView conclusion.raw.code) (fun bodyRaw =>
          Option.bind (scopedFormulaCandidate (Nat.succ line.bound) bodyRaw)
            (fun body =>
              Option.bind (premise.recover context.lift body) (fun proof =>
                let packed : PackedHistoryDerivation history :=
                  { bound := line.bound
                    context := context
                    conclusion := ScopedFormula.all body
                    proof := Derivation.universalIntroduction proof }
                packed.accept line [reference] [])))))

def checkHistoryUniversalEliminationRule
    {history : TheoryHistory}
    (line : ProofLine) (reference : Nat)
    (premise : PackedHistoryDerivation history) :
    Option (PackedHistoryDerivation history) :=
  Option.bind (universalView premise.conclusion.raw.code) (fun bodyRaw =>
    Option.bind (scopedFormulaCandidate (Nat.succ premise.bound) bodyRaw)
      (fun body =>
        Option.bind (decodeScopedTerm premise.bound
            (codedListEntry (quoteNatList line.parameters) 0)) (fun term =>
          Option.bind
            (premise.recover premise.context (ScopedFormula.all body))
            (fun proof =>
              let packed : PackedHistoryDerivation history :=
                { bound := premise.bound
                  context := premise.context
                  conclusion := body.instantiate term
                  proof := Derivation.universalElimination term proof }
              packed.accept line [reference] [term.raw.code]))))

def checkHistoryExistentialIntroductionRule
    {history : TheoryHistory}
    (line : ProofLine) (reference : Nat)
    (premise : PackedHistoryDerivation history) :
    Option (PackedHistoryDerivation history) :=
  Option.bind (decodeScopedFormula premise.bound line.conclusionCode)
    (fun conclusion =>
      Option.bind (existentialView conclusion.raw.code) (fun bodyRaw =>
        Option.bind (scopedFormulaCandidate (Nat.succ premise.bound) bodyRaw)
          (fun body =>
            Option.bind (decodeScopedTerm premise.bound
                (codedListEntry (quoteNatList line.parameters) 0)) (fun term =>
              Option.bind
                (premise.recover premise.context (body.instantiate term))
                (fun proof =>
                  let packed : PackedHistoryDerivation history :=
                    { bound := premise.bound
                      context := premise.context
                      conclusion := ScopedFormula.ex body
                      proof := Derivation.existentialIntroduction term proof }
                  packed.accept line [reference] [term.raw.code])))))

def checkHistoryEqualitySymmetryRule
    {history : TheoryHistory}
    (line : ProofLine) (reference : Nat)
    (premise : PackedHistoryDerivation history) :
    Option (PackedHistoryDerivation history) :=
  Option.bind (equalityView premise.conclusion.raw.code) (fun equality =>
    Option.bind (scopedTermCandidate premise.bound equality.left) (fun left =>
      Option.bind (scopedTermCandidate premise.bound equality.right) (fun right =>
        Option.bind
          (premise.recover premise.context (ScopedFormula.equal left right))
          (fun proof =>
            let packed : PackedHistoryDerivation history :=
              { bound := premise.bound
                context := premise.context
                conclusion := ScopedFormula.equal right left
                proof := Derivation.equalitySymmetry proof }
            packed.accept line [reference] []))))

def checkHistoryLiftVariablesRule
    {history : TheoryHistory}
    (line : ProofLine) (reference : Nat)
    (premise : PackedHistoryDerivation history) :
    Option (PackedHistoryDerivation history) :=
  let packed : PackedHistoryDerivation history :=
    { bound := Nat.succ premise.bound
      context := premise.context.lift
      conclusion := premise.conclusion.lift
      proof := Derivation.liftVariables premise.proof }
  packed.accept line [reference] []

def checkHistoryFreeInstantiationRule
    {history : TheoryHistory}
    (line : ProofLine) (reference : Nat)
    (premise : PackedHistoryDerivation history) :
    Option (PackedHistoryDerivation history) :=
  Option.bind (decodeFormulaContext (Nat.succ line.bound)
      premise.contextCode) (fun context =>
    Option.bind (decodeScopedFormula (Nat.succ line.bound)
        premise.conclusionCode) (fun conclusion =>
      Option.bind (decodeScopedTerm line.bound
          (codedListEntry (quoteNatList line.parameters) 0)) (fun term =>
        Option.bind (premise.recover context conclusion) (fun proof =>
          let packed : PackedHistoryDerivation history :=
            { bound := line.bound
              context := context.instantiate term
              conclusion := conclusion.instantiate term
              proof := Derivation.freeInstantiation term proof }
          packed.accept line [reference] [term.raw.code]))))

/-! ## Binary and ternary rules -/

def checkHistoryImplicationEliminationRule
    {history : TheoryHistory}
    (line : ProofLine)
    (firstReference : Nat) (first : PackedHistoryDerivation history)
    (secondReference : Nat) (second : PackedHistoryDerivation history) :
    Option (PackedHistoryDerivation history) :=
  Option.bind (implicationView first.conclusion.raw.code) (fun implication =>
    Option.bind (scopedFormulaCandidate first.bound implication.left) (fun left =>
      Option.bind (scopedFormulaCandidate first.bound implication.right) (fun right =>
        Option.bind
          (first.recover first.context (ScopedFormula.impl left right))
          (fun implicationProof =>
            Option.bind (second.recover first.context left) (fun argument =>
              let packed : PackedHistoryDerivation history :=
                { bound := first.bound
                  context := first.context
                  conclusion := right
                  proof := Derivation.implicationElimination
                    implicationProof argument }
              packed.accept line [firstReference, secondReference] [])))))

def checkHistoryConjunctionIntroductionRule
    {history : TheoryHistory}
    (line : ProofLine)
    (firstReference : Nat) (first : PackedHistoryDerivation history)
    (secondReference : Nat) (second : PackedHistoryDerivation history) :
    Option (PackedHistoryDerivation history) :=
  Option.bind (decodeScopedFormula first.bound second.conclusionCode)
    (fun secondConclusion =>
      Option.bind (second.recover first.context secondConclusion) (fun proof =>
        let packed : PackedHistoryDerivation history :=
          { bound := first.bound
            context := first.context
            conclusion := ScopedFormula.conj first.conclusion secondConclusion
            proof := Derivation.conjunctionIntroduction first.proof proof }
        packed.accept line [firstReference, secondReference] []))

def checkHistoryExistentialEliminationRule
    {history : TheoryHistory}
    (line : ProofLine)
    (firstReference : Nat) (first : PackedHistoryDerivation history)
    (secondReference : Nat) (second : PackedHistoryDerivation history) :
    Option (PackedHistoryDerivation history) :=
  Option.bind (existentialView first.conclusion.raw.code) (fun bodyRaw =>
    Option.bind (scopedFormulaCandidate (Nat.succ first.bound) bodyRaw)
      (fun body =>
        Option.bind (decodeScopedFormula first.bound line.conclusionCode)
          (fun conclusion =>
            Option.bind
              (first.recover first.context (ScopedFormula.ex body))
              (fun existentialProof =>
                Option.bind
                  (second.recover
                    (FormulaContext.cons body first.context.lift)
                    conclusion.lift) (fun branch =>
                  let packed : PackedHistoryDerivation history :=
                    { bound := first.bound
                      context := first.context
                      conclusion := conclusion
                      proof := Derivation.existentialElimination
                        existentialProof branch }
                  packed.accept line [firstReference, secondReference] [])))))

def checkHistoryEqualityTransitivityRule
    {history : TheoryHistory}
    (line : ProofLine)
    (firstReference : Nat) (first : PackedHistoryDerivation history)
    (secondReference : Nat) (second : PackedHistoryDerivation history) :
    Option (PackedHistoryDerivation history) :=
  Option.bind (equalityView first.conclusion.raw.code) (fun firstEquality =>
    Option.bind (scopedTermCandidate first.bound firstEquality.left) (fun left =>
      Option.bind (scopedTermCandidate first.bound firstEquality.right) (fun middle =>
        Option.bind (decodeScopedFormula first.bound second.conclusionCode)
          (fun secondConclusion =>
            Option.bind (equalityView secondConclusion.raw.code) (fun secondEquality =>
              Option.bind (scopedTermCandidate first.bound secondEquality.right)
                (fun right =>
                  Option.bind
                    (first.recover first.context
                      (ScopedFormula.equal left middle)) (fun firstProof =>
                    Option.bind
                      (second.recover first.context
                        (ScopedFormula.equal middle right)) (fun secondProof =>
                      let packed : PackedHistoryDerivation history :=
                        { bound := first.bound
                          context := first.context
                          conclusion := ScopedFormula.equal left right
                          proof := Derivation.equalityTransitivity
                            firstProof secondProof }
                      packed.accept line
                        [firstReference, secondReference] []))))))))

def checkHistoryEqualitySubstitutionRule
    {history : TheoryHistory}
    (line : ProofLine)
    (firstReference : Nat) (first : PackedHistoryDerivation history)
    (secondReference : Nat) (second : PackedHistoryDerivation history) :
    Option (PackedHistoryDerivation history) :=
  Option.bind (equalityView first.conclusion.raw.code) (fun equality =>
    Option.bind (scopedTermCandidate first.bound equality.left) (fun left =>
      Option.bind (scopedTermCandidate first.bound equality.right) (fun right =>
        Option.bind (decodeScopedFormula (Nat.succ first.bound)
            (codedListEntry (quoteNatList line.parameters) 0)) (fun body =>
          Option.bind
            (first.recover first.context (ScopedFormula.equal left right))
            (fun equalityProof =>
              Option.bind
                (second.recover first.context (body.instantiate left))
                (fun premise =>
                  let packed : PackedHistoryDerivation history :=
                    { bound := first.bound
                      context := first.context
                      conclusion := body.instantiate right
                      proof := Derivation.equalitySubstitution body
                        equalityProof premise }
                  packed.accept line [firstReference, secondReference]
                    [body.raw.code]))))))

def checkHistoryDisjunctionEliminationRule
    {history : TheoryHistory}
    (line : ProofLine)
    (firstReference : Nat) (first : PackedHistoryDerivation history)
    (secondReference : Nat) (second : PackedHistoryDerivation history)
    (thirdReference : Nat) (third : PackedHistoryDerivation history) :
    Option (PackedHistoryDerivation history) :=
  Option.bind (disjunctionView first.conclusion.raw.code) (fun disjunction =>
    Option.bind (scopedFormulaCandidate first.bound disjunction.left) (fun left =>
      Option.bind (scopedFormulaCandidate first.bound disjunction.right) (fun right =>
        Option.bind (decodeScopedFormula first.bound line.conclusionCode)
          (fun conclusion =>
            Option.bind
              (first.recover first.context (ScopedFormula.disj left right))
              (fun disjunctionProof =>
                Option.bind
                  (second.recover
                    (FormulaContext.cons left first.context) conclusion)
                  (fun leftBranch =>
                    Option.bind
                      (third.recover
                        (FormulaContext.cons right first.context) conclusion)
                      (fun rightBranch =>
                        let packed : PackedHistoryDerivation history :=
                          { bound := first.bound
                            context := first.context
                            conclusion := conclusion
                            proof := Derivation.disjunctionElimination
                              disjunctionProof leftBranch rightBranch }
                        packed.accept line
                          [firstReference, secondReference, thirdReference]
                          [])))))))

/-! ## Dispatch and archive fold -/

def checkHistoryUnaryRule
    {history : TheoryHistory}
    (line : ProofLine) (reference : Nat)
    (premise : PackedHistoryDerivation history) :
    Option (PackedHistoryDerivation history) :=
  if line.rule = ProofRuleTag.weaken then
    checkHistoryWeakenRule line reference premise
  else if line.rule = ProofRuleTag.implicationIntroduction then
    checkHistoryImplicationIntroductionRule line reference premise
  else if line.rule = ProofRuleTag.conjunctionEliminationLeft then
    checkHistoryConjunctionEliminationLeftRule line reference premise
  else if line.rule = ProofRuleTag.conjunctionEliminationRight then
    checkHistoryConjunctionEliminationRightRule line reference premise
  else if line.rule = ProofRuleTag.disjunctionIntroductionLeft then
    checkHistoryDisjunctionIntroductionLeftRule line reference premise
  else if line.rule = ProofRuleTag.disjunctionIntroductionRight then
    checkHistoryDisjunctionIntroductionRightRule line reference premise
  else if line.rule = ProofRuleTag.falsumElimination then
    checkHistoryFalsumEliminationRule line reference premise
  else if line.rule = ProofRuleTag.universalIntroduction then
    checkHistoryUniversalIntroductionRule line reference premise
  else if line.rule = ProofRuleTag.universalElimination then
    checkHistoryUniversalEliminationRule line reference premise
  else if line.rule = ProofRuleTag.existentialIntroduction then
    checkHistoryExistentialIntroductionRule line reference premise
  else if line.rule = ProofRuleTag.equalitySymmetry then
    checkHistoryEqualitySymmetryRule line reference premise
  else if line.rule = ProofRuleTag.liftVariables then
    checkHistoryLiftVariablesRule line reference premise
  else if line.rule = ProofRuleTag.freeInstantiation then
    checkHistoryFreeInstantiationRule line reference premise
  else none

def checkHistoryBinaryRule
    {history : TheoryHistory}
    (line : ProofLine)
    (firstReference : Nat) (first : PackedHistoryDerivation history)
    (secondReference : Nat) (second : PackedHistoryDerivation history) :
    Option (PackedHistoryDerivation history) :=
  if line.rule = ProofRuleTag.implicationElimination then
    checkHistoryImplicationEliminationRule line firstReference first
      secondReference second
  else if line.rule = ProofRuleTag.conjunctionIntroduction then
    checkHistoryConjunctionIntroductionRule line firstReference first
      secondReference second
  else if line.rule = ProofRuleTag.existentialElimination then
    checkHistoryExistentialEliminationRule line firstReference first
      secondReference second
  else if line.rule = ProofRuleTag.equalityTransitivity then
    checkHistoryEqualityTransitivityRule line firstReference first
      secondReference second
  else if line.rule = ProofRuleTag.equalitySubstitution then
    checkHistoryEqualitySubstitutionRule line firstReference first
      secondReference second
  else none

def checkHistoryProofRule
    (history : TheoryHistory)
    (previous : List (PackedHistoryDerivation history))
    (line : ProofLine) : Option (PackedHistoryDerivation history) :=
  if line.rule = ProofRuleTag.theoryAxiom then
    checkHistoryProofLeaf history line
  else if line.rule = ProofRuleTag.hypothesis then
    checkHistoryProofLeaf history line
  else if line.rule = ProofRuleTag.equalityReflexivity then
    checkHistoryProofLeaf history line
  else if line.premises.length == 1 then
    let reference := codedListEntry (quoteNatList line.premises) 0
    Option.bind (packedHistoryDerivationAt previous reference) (fun premise =>
      checkHistoryUnaryRule line reference premise)
  else if line.premises.length == 2 then
    let firstReference := codedListEntry (quoteNatList line.premises) 0
    let secondReference := codedListEntry (quoteNatList line.premises) 1
    Option.bind (packedHistoryDerivationAt previous firstReference) (fun first =>
      Option.bind (packedHistoryDerivationAt previous secondReference) (fun second =>
        checkHistoryBinaryRule line firstReference first secondReference second))
  else if line.premises.length == 3 then
    let firstReference := codedListEntry (quoteNatList line.premises) 0
    let secondReference := codedListEntry (quoteNatList line.premises) 1
    let thirdReference := codedListEntry (quoteNatList line.premises) 2
    Option.bind (packedHistoryDerivationAt previous firstReference) (fun first =>
      Option.bind (packedHistoryDerivationAt previous secondReference) (fun second =>
        Option.bind (packedHistoryDerivationAt previous thirdReference) (fun third =>
          if line.rule = ProofRuleTag.disjunctionElimination then
            checkHistoryDisjunctionEliminationRule line
              firstReference first secondReference second thirdReference third
          else none)))
  else none

def checkHistoryProofLinesFrom
    (history : TheoryHistory) :
    List (PackedHistoryDerivation history) -> List ProofLine ->
      Option (List (PackedHistoryDerivation history))
  | previous, [] => some previous
  | previous, line :: remaining =>
      Option.bind (checkHistoryProofRule history previous line) (fun packed =>
        checkHistoryProofLinesFrom history (previous ++ [packed]) remaining)

def checkHistoryProofLines
    (history : TheoryHistory)
    (lines : List ProofLine) : Option (List (PackedHistoryDerivation history)) :=
  checkHistoryProofLinesFrom history [] lines

end HeytingArithmetic
end RelationalPerimeter

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.HeytingArithmetic.checkHistoryProofRule
#print axioms RelationalPerimeter.HeytingArithmetic.checkHistoryProofLines
/- AXIOM_AUDIT_END -/
