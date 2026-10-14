import RelationalPerimeter.Constitution.HeytingArithmetic.ProofLeafChecking

/-!
# Constructive checking of chronological PA proof rules

Every accepted non-leaf line is rebuilt from already accepted packed
derivations.  A premise reference can therefore only reach the chronological
prefix: no future line is available to the checker.  Numeric codes are used
only to align intrinsically scoped syntax; acceptance returns an actual PA
derivation in `Type`.
-/

namespace RelationalPerimeter
namespace HeytingArithmetic

theorem FormulaContext.eq_of_quote_eq
    {bound : Nat}
    {left right : FormulaContext bound}
    (sameQuote : left.quote = right.quote) : left = right := by
  have leftDecoded := decodeFormulaContext_quote left
  have rightDecoded := decodeFormulaContext_quote right
  rw [sameQuote] at leftDecoded
  exact Option.some.inj (leftDecoded.symm.trans rightDecoded)

theorem ScopedFormula.eq_of_code_eq
    {bound : Nat}
    {left right : ScopedFormula bound}
    (sameCode : left.raw.code = right.raw.code) : left = right :=
  ScopedFormula.eq_of_raw_eq (RawFormula.code_injective sameCode)

/-- Recover a proof at specified intrinsic indices by comparing their fully
    reconstructible numeric codes. -/
def PackedPADerivation.recover
    {bound : Nat}
    (context : FormulaContext bound)
    (conclusion : ScopedFormula bound)
    (packed : PackedPADerivation) :
    Option
      (Derivation LogicMode.classical standardArithmeticTheory
        context conclusion) := by
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

def PackedPADerivation.accept
    (line : ProofLine)
    (packed : PackedPADerivation)
    (premises parameters : List Nat) : Option PackedPADerivation :=
  acceptPackedProofLine line packed
    (quoteNatList premises) (quoteNatList parameters)

def PackedPADerivation.weakenCandidate
    (premise : PackedPADerivation)
    (extra : ScopedFormula premise.bound) :
    Option PackedPADerivation :=
  match premise.recover premise.context premise.conclusion with
  | none => none
  | some proof =>
      some
        { bound := premise.bound
          context := FormulaContext.cons extra premise.context
          conclusion := premise.conclusion
          proof := Derivation.weaken extra proof }

/-! ## Positive views of compound syntax -/

structure BinaryFormulaView where
  left : RawFormula
  right : RawFormula

def formulaCodePayloadForTag (expectedTag formulaCode : Nat) : Option Nat :=
  match formulaCode with
  | 0 => none
  | Nat.succ encoded =>
      let components := natUnpair encoded
      if components.1 == expectedTag then some components.2 else none

def binaryFormulaViewFromCode
    (expectedTag formulaCode : Nat) : Option BinaryFormulaView :=
  Option.bind (formulaCodePayloadForTag expectedTag formulaCode) (fun payload =>
    let children := natUnpair payload
    Option.bind (decodeFormula children.1) (fun left =>
      Option.map (fun right => { left := left, right := right })
        (decodeFormula children.2)))

def implicationView (formulaCode : Nat) : Option BinaryFormulaView :=
  binaryFormulaViewFromCode 4 formulaCode

def conjunctionView (formulaCode : Nat) : Option BinaryFormulaView :=
  binaryFormulaViewFromCode 2 formulaCode

def disjunctionView (formulaCode : Nat) : Option BinaryFormulaView :=
  binaryFormulaViewFromCode 3 formulaCode

structure EqualityFormulaView where
  left : RawTerm
  right : RawTerm

def equalityView (formulaCode : Nat) : Option EqualityFormulaView :=
  Option.bind (formulaCodePayloadForTag 1 formulaCode) (fun payload =>
    let children := natUnpair payload
    Option.bind (decodeTerm children.1) (fun left =>
      Option.map (fun right => { left := left, right := right })
        (decodeTerm children.2)))

def universalView (formulaCode : Nat) : Option RawFormula :=
  Option.bind (formulaCodePayloadForTag 5 formulaCode) decodeFormula

def existentialView (formulaCode : Nat) : Option RawFormula :=
  Option.bind (formulaCodePayloadForTag 6 formulaCode) decodeFormula

def RawFormula.isFalsum (formula : RawFormula) : Bool :=
  decide (formula = RawFormula.falsum)

def isFalsum (formula : ScopedFormula bound) : Bool :=
  formula.raw.isFalsum

/-! ## Chronological premise access -/

def packedDerivationAt : List PackedPADerivation -> Nat ->
    Option PackedPADerivation
  | [], _index => none
  | head :: _tail, 0 => some head
  | _head :: tail, Nat.succ index => packedDerivationAt tail index

/-! ## Unary rules -/

def checkPAWeakenRule
    (line : ProofLine) (reference : Nat)
    (premise : PackedPADerivation) : Option PackedPADerivation :=
  Option.bind (decodeScopedFormula premise.bound
      (codedListEntry (quoteNatList line.parameters) 0)) (fun extra =>
    Option.bind (premise.weakenCandidate extra) (fun packed =>
      packed.accept line [reference] [extra.raw.code]))

def checkPAImplicationIntroductionRule
    (line : ProofLine) (reference : Nat)
    (premise : PackedPADerivation) : Option PackedPADerivation :=
  match premise.context with
  | FormulaContext.nil => none
  | FormulaContext.cons left context =>
      Option.bind
        (premise.recover (FormulaContext.cons left context)
          premise.conclusion) (fun proof =>
        let packed : PackedPADerivation :=
          { bound := premise.bound
            context := context
            conclusion := ScopedFormula.impl left premise.conclusion
            proof := Derivation.implicationIntroduction proof }
        packed.accept line [reference] [])

def checkPAConjunctionEliminationLeftRule
    (line : ProofLine) (reference : Nat)
    (premise : PackedPADerivation) : Option PackedPADerivation :=
  Option.bind (conjunctionView premise.conclusion.raw.code) (fun parts =>
    Option.bind (scopedFormulaCandidate premise.bound parts.left) (fun left =>
      Option.bind (scopedFormulaCandidate premise.bound parts.right) (fun right =>
        Option.bind
          (premise.recover premise.context (ScopedFormula.conj left right))
          (fun proof =>
            let packed : PackedPADerivation :=
              { bound := premise.bound
                context := premise.context
                conclusion := left
                proof := Derivation.conjunctionEliminationLeft proof }
            packed.accept line [reference] []))))

def checkPAConjunctionEliminationRightRule
    (line : ProofLine) (reference : Nat)
    (premise : PackedPADerivation) : Option PackedPADerivation :=
  Option.bind (conjunctionView premise.conclusion.raw.code) (fun parts =>
    Option.bind (scopedFormulaCandidate premise.bound parts.left) (fun left =>
      Option.bind (scopedFormulaCandidate premise.bound parts.right) (fun right =>
        Option.bind
          (premise.recover premise.context (ScopedFormula.conj left right))
          (fun proof =>
            let packed : PackedPADerivation :=
              { bound := premise.bound
                context := premise.context
                conclusion := right
                proof := Derivation.conjunctionEliminationRight proof }
            packed.accept line [reference] []))))

def checkPADisjunctionIntroductionLeftRule
    (line : ProofLine) (reference : Nat)
    (premise : PackedPADerivation) : Option PackedPADerivation :=
  Option.bind (decodeScopedFormula premise.bound line.conclusionCode)
    (fun conclusion =>
      Option.bind (disjunctionView conclusion.raw.code) (fun parts =>
        Option.bind (scopedFormulaCandidate premise.bound parts.left) (fun left =>
          Option.bind (scopedFormulaCandidate premise.bound parts.right) (fun right =>
            Option.bind (premise.recover premise.context left) (fun proof =>
              let packed : PackedPADerivation :=
                { bound := premise.bound
                  context := premise.context
                  conclusion := ScopedFormula.disj left right
                  proof := Derivation.disjunctionIntroductionLeft proof }
              packed.accept line [reference] [])))))

def checkPADisjunctionIntroductionRightRule
    (line : ProofLine) (reference : Nat)
    (premise : PackedPADerivation) : Option PackedPADerivation :=
  Option.bind (decodeScopedFormula premise.bound line.conclusionCode)
    (fun conclusion =>
      Option.bind (disjunctionView conclusion.raw.code) (fun parts =>
        Option.bind (scopedFormulaCandidate premise.bound parts.left) (fun left =>
          Option.bind (scopedFormulaCandidate premise.bound parts.right) (fun right =>
            Option.bind (premise.recover premise.context right) (fun proof =>
              let packed : PackedPADerivation :=
                { bound := premise.bound
                  context := premise.context
                  conclusion := ScopedFormula.disj left right
                  proof := Derivation.disjunctionIntroductionRight proof }
              packed.accept line [reference] [])))))

def checkPAFalsumEliminationRule
    (line : ProofLine) (reference : Nat)
    (premise : PackedPADerivation) : Option PackedPADerivation :=
  Option.bind (decodeScopedFormula premise.bound line.conclusionCode)
    (fun conclusion =>
      Option.bind
        (premise.recover premise.context
          (ScopedFormula.falsum premise.bound)) (fun proof =>
        let packed : PackedPADerivation :=
          { bound := premise.bound
            context := premise.context
            conclusion := conclusion
            proof := Derivation.falsumElimination proof }
        packed.accept line [reference] []))

def checkPAUniversalIntroductionRule
    (line : ProofLine) (reference : Nat)
    (premise : PackedPADerivation) : Option PackedPADerivation :=
  Option.bind (decodeFormulaContext line.bound line.contextCode) (fun context =>
    Option.bind (decodeScopedFormula line.bound line.conclusionCode)
      (fun conclusion =>
        Option.bind (universalView conclusion.raw.code) (fun bodyRaw =>
          Option.bind (scopedFormulaCandidate (Nat.succ line.bound) bodyRaw)
            (fun body =>
              Option.bind (premise.recover context.lift body) (fun proof =>
                let packed : PackedPADerivation :=
                  { bound := line.bound
                    context := context
                    conclusion := ScopedFormula.all body
                    proof := Derivation.universalIntroduction proof }
                packed.accept line [reference] [])))))

def checkPAUniversalEliminationRule
    (line : ProofLine) (reference : Nat)
    (premise : PackedPADerivation) : Option PackedPADerivation :=
  Option.bind (universalView premise.conclusion.raw.code) (fun bodyRaw =>
    Option.bind (scopedFormulaCandidate (Nat.succ premise.bound) bodyRaw)
      (fun body =>
        Option.bind (decodeScopedTerm premise.bound
            (codedListEntry (quoteNatList line.parameters) 0)) (fun term =>
          Option.bind
            (premise.recover premise.context (ScopedFormula.all body))
            (fun proof =>
              let packed : PackedPADerivation :=
                { bound := premise.bound
                  context := premise.context
                  conclusion := body.instantiate term
                  proof := Derivation.universalElimination term proof }
              packed.accept line [reference] [term.raw.code]))))

def checkPAExistentialIntroductionRule
    (line : ProofLine) (reference : Nat)
    (premise : PackedPADerivation) : Option PackedPADerivation :=
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
                  let packed : PackedPADerivation :=
                    { bound := premise.bound
                      context := premise.context
                      conclusion := ScopedFormula.ex body
                      proof := Derivation.existentialIntroduction term proof }
                  packed.accept line [reference] [term.raw.code])))))

def checkPAEqualitySymmetryRule
    (line : ProofLine) (reference : Nat)
    (premise : PackedPADerivation) : Option PackedPADerivation :=
  Option.bind (equalityView premise.conclusion.raw.code) (fun equality =>
    Option.bind (scopedTermCandidate premise.bound equality.left) (fun left =>
      Option.bind (scopedTermCandidate premise.bound equality.right) (fun right =>
        Option.bind
          (premise.recover premise.context (ScopedFormula.equal left right))
          (fun proof =>
            let packed : PackedPADerivation :=
              { bound := premise.bound
                context := premise.context
                conclusion := ScopedFormula.equal right left
                proof := Derivation.equalitySymmetry proof }
            packed.accept line [reference] []))))

def checkPALiftVariablesRule
    (line : ProofLine) (reference : Nat)
    (premise : PackedPADerivation) : Option PackedPADerivation :=
  let packed : PackedPADerivation :=
    { bound := Nat.succ premise.bound
      context := premise.context.lift
      conclusion := premise.conclusion.lift
      proof := Derivation.liftVariables premise.proof }
  packed.accept line [reference] []

def checkPAFreeInstantiationRule
    (line : ProofLine) (reference : Nat)
    (premise : PackedPADerivation) : Option PackedPADerivation :=
  Option.bind (decodeFormulaContext (Nat.succ line.bound)
      premise.contextCode) (fun context =>
    Option.bind (decodeScopedFormula (Nat.succ line.bound)
        premise.conclusionCode) (fun conclusion =>
      Option.bind (decodeScopedTerm line.bound
          (codedListEntry (quoteNatList line.parameters) 0)) (fun term =>
        Option.bind (premise.recover context conclusion) (fun proof =>
          let packed : PackedPADerivation :=
            { bound := line.bound
              context := context.instantiate term
              conclusion := conclusion.instantiate term
              proof := Derivation.freeInstantiation term proof }
          packed.accept line [reference] [term.raw.code]))))

def checkPADoubleNegationEliminationRule
    (line : ProofLine) (reference : Nat)
    (premise : PackedPADerivation) : Option PackedPADerivation :=
  Option.bind (implicationView premise.conclusion.raw.code) (fun outer =>
    Option.bind (implicationView outer.left.code) (fun inner =>
      Option.bind (scopedFormulaCandidate premise.bound inner.left)
        (fun conclusion =>
          Option.bind
            (premise.recover premise.context
              (ScopedFormula.neg (ScopedFormula.neg conclusion))) (fun proof =>
            let packed : PackedPADerivation :=
              { bound := premise.bound
                context := premise.context
                conclusion := conclusion
                proof := Derivation.doubleNegationElimination
                  ClassicalPermission.available proof }
            packed.accept line [reference] []))))

/-! ## Binary and ternary rules -/

def checkPAImplicationEliminationRule
    (line : ProofLine)
    (firstReference : Nat) (first : PackedPADerivation)
    (secondReference : Nat) (second : PackedPADerivation) :
    Option PackedPADerivation :=
  Option.bind (implicationView first.conclusion.raw.code) (fun implication =>
    Option.bind (scopedFormulaCandidate first.bound implication.left) (fun left =>
      Option.bind (scopedFormulaCandidate first.bound implication.right) (fun right =>
        Option.bind
          (first.recover first.context (ScopedFormula.impl left right))
          (fun implicationProof =>
            Option.bind (second.recover first.context left)
              (fun argument =>
                let packed : PackedPADerivation :=
                  { bound := first.bound
                    context := first.context
                    conclusion := right
                    proof := Derivation.implicationElimination
                      implicationProof argument }
                packed.accept line [firstReference, secondReference] [])))))

def checkPAConjunctionIntroductionRule
    (line : ProofLine)
    (firstReference : Nat) (first : PackedPADerivation)
    (secondReference : Nat) (second : PackedPADerivation) :
    Option PackedPADerivation :=
  Option.bind
    (decodeScopedFormula first.bound second.conclusionCode)
    (fun secondConclusion =>
      Option.bind (second.recover first.context secondConclusion) (fun proof =>
        let packed : PackedPADerivation :=
          { bound := first.bound
            context := first.context
            conclusion := ScopedFormula.conj first.conclusion
              secondConclusion
            proof := Derivation.conjunctionIntroduction first.proof proof }
        packed.accept line [firstReference, secondReference] []))

def checkPAExistentialEliminationRule
    (line : ProofLine)
    (firstReference : Nat) (first : PackedPADerivation)
    (secondReference : Nat) (second : PackedPADerivation) :
    Option PackedPADerivation :=
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
                  let packed : PackedPADerivation :=
                    { bound := first.bound
                      context := first.context
                      conclusion := conclusion
                      proof := Derivation.existentialElimination
                        existentialProof branch }
                  packed.accept line [firstReference, secondReference] [])))))

def checkPAEqualityTransitivityRule
    (line : ProofLine)
    (firstReference : Nat) (first : PackedPADerivation)
    (secondReference : Nat) (second : PackedPADerivation) :
    Option PackedPADerivation :=
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
                      let packed : PackedPADerivation :=
                        { bound := first.bound
                          context := first.context
                          conclusion := ScopedFormula.equal left right
                          proof := Derivation.equalityTransitivity
                            firstProof secondProof }
                      packed.accept line
                        [firstReference, secondReference] []))))))))

def checkPAEqualitySubstitutionRule
    (line : ProofLine)
    (firstReference : Nat) (first : PackedPADerivation)
    (secondReference : Nat) (second : PackedPADerivation) :
    Option PackedPADerivation :=
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
                  let packed : PackedPADerivation :=
                    { bound := first.bound
                      context := first.context
                      conclusion := body.instantiate right
                      proof := Derivation.equalitySubstitution body
                        equalityProof premise }
                  packed.accept line [firstReference, secondReference]
                    [body.raw.code]))))))

def checkPADisjunctionEliminationRule
    (line : ProofLine)
    (firstReference : Nat) (first : PackedPADerivation)
    (secondReference : Nat) (second : PackedPADerivation)
    (thirdReference : Nat) (third : PackedPADerivation) :
    Option PackedPADerivation :=
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
                        let packed : PackedPADerivation :=
                          { bound := first.bound
                            context := first.context
                            conclusion := conclusion
                            proof := Derivation.disjunctionElimination
                              disjunctionProof leftBranch rightBranch }
                        packed.accept line
                          [firstReference, secondReference, thirdReference]
                          [])))))))

/-! ## Dispatcher and chronological fold -/

def checkPAUnaryRule
    (line : ProofLine) (reference : Nat)
    (premise : PackedPADerivation) : Option PackedPADerivation :=
  if line.rule = ProofRuleTag.weaken then
    checkPAWeakenRule line reference premise
  else if line.rule = ProofRuleTag.implicationIntroduction then
    checkPAImplicationIntroductionRule line reference premise
  else if line.rule = ProofRuleTag.conjunctionEliminationLeft then
    checkPAConjunctionEliminationLeftRule line reference premise
  else if line.rule = ProofRuleTag.conjunctionEliminationRight then
    checkPAConjunctionEliminationRightRule line reference premise
  else if line.rule = ProofRuleTag.disjunctionIntroductionLeft then
    checkPADisjunctionIntroductionLeftRule line reference premise
  else if line.rule = ProofRuleTag.disjunctionIntroductionRight then
    checkPADisjunctionIntroductionRightRule line reference premise
  else if line.rule = ProofRuleTag.falsumElimination then
    checkPAFalsumEliminationRule line reference premise
  else if line.rule = ProofRuleTag.universalIntroduction then
    checkPAUniversalIntroductionRule line reference premise
  else if line.rule = ProofRuleTag.universalElimination then
    checkPAUniversalEliminationRule line reference premise
  else if line.rule = ProofRuleTag.existentialIntroduction then
    checkPAExistentialIntroductionRule line reference premise
  else if line.rule = ProofRuleTag.equalitySymmetry then
    checkPAEqualitySymmetryRule line reference premise
  else if line.rule = ProofRuleTag.liftVariables then
    checkPALiftVariablesRule line reference premise
  else if line.rule = ProofRuleTag.freeInstantiation then
    checkPAFreeInstantiationRule line reference premise
  else if line.rule = ProofRuleTag.doubleNegationElimination then
    checkPADoubleNegationEliminationRule line reference premise
  else
    none

def checkPABinaryRule
    (line : ProofLine)
    (firstReference : Nat) (first : PackedPADerivation)
    (secondReference : Nat) (second : PackedPADerivation) :
    Option PackedPADerivation :=
  if line.rule = ProofRuleTag.implicationElimination then
    checkPAImplicationEliminationRule line firstReference first
      secondReference second
  else if line.rule = ProofRuleTag.conjunctionIntroduction then
    checkPAConjunctionIntroductionRule line firstReference first
      secondReference second
  else if line.rule = ProofRuleTag.existentialElimination then
    checkPAExistentialEliminationRule line firstReference first
      secondReference second
  else if line.rule = ProofRuleTag.equalityTransitivity then
    checkPAEqualityTransitivityRule line firstReference first
      secondReference second
  else if line.rule = ProofRuleTag.equalitySubstitution then
    checkPAEqualitySubstitutionRule line firstReference first
      secondReference second
  else
    none

def checkPAProofRule
    (previous : List PackedPADerivation)
    (line : ProofLine) : Option PackedPADerivation :=
  if _theory : line.rule = ProofRuleTag.theoryAxiom then
    checkPAProofLeaf line
  else if _hypothesis : line.rule = ProofRuleTag.hypothesis then
    checkPAProofLeaf line
  else if _reflexivity : line.rule = ProofRuleTag.equalityReflexivity then
    checkPAProofLeaf line
  else if line.premises.length == 1 then
      let reference := codedListEntry (quoteNatList line.premises) 0
      Option.bind (packedDerivationAt previous reference) (fun premise =>
        checkPAUnaryRule line reference premise)
  else if line.premises.length == 2 then
      let firstReference := codedListEntry (quoteNatList line.premises) 0
      let secondReference := codedListEntry (quoteNatList line.premises) 1
      Option.bind (packedDerivationAt previous firstReference) (fun first =>
        Option.bind (packedDerivationAt previous secondReference) (fun second =>
          checkPABinaryRule line firstReference first
            secondReference second))
  else if line.premises.length == 3 then
      let firstReference := codedListEntry (quoteNatList line.premises) 0
      let secondReference := codedListEntry (quoteNatList line.premises) 1
      let thirdReference := codedListEntry (quoteNatList line.premises) 2
      Option.bind (packedDerivationAt previous firstReference) (fun first =>
        Option.bind (packedDerivationAt previous secondReference) (fun second =>
          Option.bind (packedDerivationAt previous thirdReference) (fun third =>
            if line.rule = ProofRuleTag.disjunctionElimination then
              checkPADisjunctionEliminationRule line
                firstReference first secondReference second
                thirdReference third
            else
              none)))
  else
    none

def checkPAProofLinesFrom :
    List PackedPADerivation -> List ProofLine ->
      Option (List PackedPADerivation)
  | previous, [] => some previous
  | previous, line :: remaining =>
      Option.bind (checkPAProofRule previous line) (fun packed =>
        checkPAProofLinesFrom (previous ++ [packed]) remaining)

def checkPAProofLines (lines : List ProofLine) :
    Option (List PackedPADerivation) :=
  checkPAProofLinesFrom [] lines

end HeytingArithmetic
end RelationalPerimeter

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.HeytingArithmetic.FormulaContext.eq_of_quote_eq
#print axioms RelationalPerimeter.HeytingArithmetic.RawFormula.isFalsum
#print axioms RelationalPerimeter.HeytingArithmetic.isFalsum
#print axioms RelationalPerimeter.HeytingArithmetic.PackedPADerivation.recover
#print axioms RelationalPerimeter.HeytingArithmetic.checkPAProofRule
#print axioms RelationalPerimeter.HeytingArithmetic.checkPAProofLines
/- AXIOM_AUDIT_END -/
