import RelationalPerimeter.Instances.HeytingArithmetic.PrimitiveRecursiveArithmeticAxioms
import RelationalPerimeter.Instances.HeytingArithmetic.HistoryProofChecking

/-!
# Inverse correctness of numeric arithmetic-postulate recognition

Positive acceptance reconstructs the exact scoped postulate and its canonical
parameter payload.  The result is data in `Type`, not an existential oracle.
-/

namespace RelationalPerimeter
namespace HeytingArithmetic

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- A scoped term reconstructed as data, with its code equality retained. -/
structure DecodedScopedTermCode (bound code : Nat) : Type where
  term : ScopedTerm bound
  codeExact : term.raw.code = code

/-- Positive scoped-term recognition yields a computationally decoded term. -/
def PRFunction.decodeScopedTermCodePositive
    (bound code : Nat)
    (accepted : 0 < PRFunction.isScopedTermCode.run
      (NatVector.cons bound (NatVector.cons code NatVector.nil))) :
    DecodedScopedTermCode bound code := by
  cases decoded : decodeScopedTerm bound code with
  | none =>
      have impossible : False := by
        cases PRFunction.isScopedTermCode_positive_sound bound code accepted with
        | intro witness witnessCode =>
            have witnessDecoded := decodeScopedTerm_code witness
            rw [witnessCode, decoded] at witnessDecoded
            cases witnessDecoded
      exact False.elim impossible
  | some term =>
      refine { term := term, codeExact := ?_ }
      cases PRFunction.isScopedTermCode_positive_sound bound code accepted with
      | intro witness witnessCode =>
          have witnessDecoded := decodeScopedTerm_code witness
          rw [witnessCode, decoded] at witnessDecoded
          have same : term = witness := Option.some.inj witnessDecoded
          rw [same]
          exact witnessCode

/-- A scoped formula reconstructed as data, with its code equality retained. -/
structure DecodedScopedFormulaCode (bound code : Nat) : Type where
  formula : ScopedFormula bound
  codeExact : formula.raw.code = code

/-- Positive scoped-formula recognition yields a computationally decoded formula. -/
def PRFunction.decodeScopedFormulaCodePositive
    (bound code : Nat)
    (accepted : 0 < PRFunction.isScopedFormulaCode.run
      (NatVector.cons bound (NatVector.cons code NatVector.nil))) :
    DecodedScopedFormulaCode bound code := by
  cases decoded : decodeScopedFormula bound code with
  | none =>
      have impossible : False := by
        cases PRFunction.isScopedFormulaCode_positive_sound bound code accepted with
        | intro witness witnessCode =>
            have witnessDecoded := decodeScopedFormula_code witness
            rw [witnessCode, decoded] at witnessDecoded
            cases witnessDecoded
      exact False.elim impossible
  | some formula =>
      refine { formula := formula, codeExact := ?_ }
      cases PRFunction.isScopedFormulaCode_positive_sound bound code accepted with
      | intro witness witnessCode =>
          have witnessDecoded := decodeScopedFormula_code witness
          rw [witnessCode, decoded] at witnessDecoded
          have same : formula = witness := Option.some.inj witnessDecoded
          rw [same]
          exact witnessCode

structure DecodedPAAxiomCode
    (bound conclusionCode parameterCode : Nat) : Type where
  formula : ScopedFormula bound
  witness : StandardArithmeticAxiom formula
  conclusionExact : formula.raw.code = conclusionCode
  parametersExact :
    quoteNatList (standardArithmeticAxiomParameters witness) = parameterCode

private theorem natEqualBit_zero_zero_inverse : natEqualBit 0 0 = 1 := rfl

private theorem natEqualBit_zero_succ_inverse (value : Nat) :
    natEqualBit 0 (Nat.succ value) = 0 := rfl

def PRFunction.isPAAxiomCode_positive_sound
    (bound conclusionCode parameterCode : Nat)
    (accepted : 0 < PRFunction.isPAAxiomCode.run
      (NatVector.cons bound
        (NatVector.cons conclusionCode
          (NatVector.cons parameterCode NatVector.nil)))) :
    DecodedPAAxiomCode bound conclusionCode parameterCode := by
  unfold PRFunction.isPAAxiomCode
    paSuccessorNotZeroCode paSuccessorInjectiveCode
    paAddZeroCode paAddSuccessorCode paMultiplyZeroCode
    paMultiplySuccessorCode paInductionCode
    paAxiomScopedTerm paAxiomSameConclusion paAxiomSameParameters
    paAxiomParametersTwo paAxiomParametersThree
    paAxiomBound paAxiomEntry
    PRFunction.conjoinThree PRFunction.conjoinFour
    PRFunction.formulaNegationCode at accepted
  repeat first
    | rw [PRFunction.run_selectTag] at accepted
    | rw [PRFunction.run_conjoin] at accepted
    | rw [PRFunction.run_binaryIn] at accepted
    | rw [PRFunction.run_unaryIn] at accepted
    | rw [PRFunction.run_composition] at accepted
    | rw [PRFunctionVector.run_cons] at accepted
    | rw [PRFunctionVector.run_singleton] at accepted
    | rw [PRFunction.run_projection] at accepted
    | rw [NatVector.get_cons_zero] at accepted
    | rw [NatVector.get_cons_succ] at accepted
    | rw [PRFunction.run_constant] at accepted
    | rw [PRFunction.run_codedListEntry] at accepted
    | rw [PRFunction.run_codedListPair] at accepted
    | rw [PRFunction.run_codedListTriple] at accepted
    | rw [PRFunction.run_termSuccessorCode] at accepted
    | rw [PRFunction.run_termAddCode] at accepted
    | rw [PRFunction.run_termMultiplyCode] at accepted
    | rw [PRFunction.run_formulaEqualCode] at accepted
    | rw [PRFunction.run_formulaImplicationCode] at accepted
    | rw [PRFunction.run_formulaConjunctionCode] at accepted
    | rw [PRFunction.run_formulaUniversalCode] at accepted
    | rw [PRFunction.run_falsumCode] at accepted
    | rw [PRFunction.run_machineInstantiateTerm] at accepted
    | rw [PRFunction.run_successorInstanceCode] at accepted
    | rw [PRFunction.run_equalBit] at accepted
    | rw [PRFunction.run_andBit] at accepted
    | rw [PRFunction.run_orBit] at accepted
  cases tagValue : RelationalPerimeter.HeytingArithmetic.codedListEntry parameterCode 0 with
  | zero =>
      simp only [tagValue, natEqualBit_zero_zero_inverse,
        natEqualBit_zero_succ_inverse, natIfZero] at accepted
      have fields := (natAndBit_pos_iff _ _).mp accepted
      have remaining := (natAndBit_pos_iff _ _).mp fields.2
      let decoded := PRFunction.decodeScopedTermCodePositive bound
        (RelationalPerimeter.HeytingArithmetic.codedListEntry parameterCode 1) fields.1
      let term := decoded.term
      have termCode := decoded.codeExact
      exact by
          have conclusionEquality :=
            (natEqualBit_pos_iff _ _).mp remaining.1
          have parameterEquality :=
            (natEqualBit_pos_iff _ _).mp remaining.2
          let witness := StandardArithmeticAxiom.successorNotZero term
          exact
            { formula := ScopedFormula.neg
                (ScopedFormula.equal term.succ (ScopedTerm.zero bound))
              witness := witness
              conclusionExact := by
                change Nat.succ (natPair 4
                    (natPair
                      (Nat.succ (natPair 1
                        (natPair
                          (Nat.succ (natPair 2 term.raw.code))
                          RawTerm.zero.code)))
                      RawFormula.falsum.code)) = conclusionCode
                rw [termCode]
                exact conclusionEquality.symm
              parametersExact := by
                change quoteNatList [0, term.raw.code] = parameterCode
                rw [termCode]
                exact parameterEquality.symm }
  | succ tag =>
      cases tag with
      | zero =>
          simp only [tagValue, natEqualBit_zero_zero_inverse,
            natEqualBit_zero_succ_inverse, natEqualBit_succ_zero,
            natEqualBit_succ_succ, natIfZero] at accepted
          have firstFields := (natAndBit_pos_iff _ _).mp accepted
          have secondFields := (natAndBit_pos_iff _ _).mp firstFields.2
          have thirdFields := (natAndBit_pos_iff _ _).mp secondFields.2
          let decodedLeft := PRFunction.decodeScopedTermCodePositive bound
            (RelationalPerimeter.HeytingArithmetic.codedListEntry parameterCode 1) firstFields.1
          let left := decodedLeft.term
          have leftCode := decodedLeft.codeExact
          exact by
              let decodedRight := PRFunction.decodeScopedTermCodePositive bound
                (RelationalPerimeter.HeytingArithmetic.codedListEntry parameterCode 2) secondFields.1
              let right := decodedRight.term
              have rightCode := decodedRight.codeExact
              exact by
                  have conclusionEquality :=
                    (natEqualBit_pos_iff _ _).mp thirdFields.1
                  have parameterEquality :=
                    (natEqualBit_pos_iff _ _).mp thirdFields.2
                  let witness :=
                    StandardArithmeticAxiom.successorInjective left right
                  exact
                    { formula := ScopedFormula.impl
                        (ScopedFormula.equal left.succ right.succ)
                        (ScopedFormula.equal left right)
                      witness := witness
                      conclusionExact := by
                        simp only [ScopedFormula.impl, ScopedFormula.equal,
                          ScopedTerm.succ, RawFormula.code, RawTerm.code]
                        rw [leftCode, rightCode]
                        exact conclusionEquality.symm
                      parametersExact := by
                        change quoteNatList [1, left.raw.code, right.raw.code] =
                          parameterCode
                        rw [leftCode, rightCode]
                        exact parameterEquality.symm }
      | succ tag =>
          cases tag with
          | zero =>
              simp only [tagValue, natEqualBit_zero_zero_inverse,
                natEqualBit_zero_succ_inverse, natEqualBit_succ_zero,
                natEqualBit_succ_succ, natIfZero] at accepted
              have fields := (natAndBit_pos_iff _ _).mp accepted
              have remaining := (natAndBit_pos_iff _ _).mp fields.2
              let decoded := PRFunction.decodeScopedTermCodePositive bound
                (RelationalPerimeter.HeytingArithmetic.codedListEntry parameterCode 1) fields.1
              let term := decoded.term
              have termCode := decoded.codeExact
              exact by
                  have conclusionEquality :=
                    (natEqualBit_pos_iff _ _).mp remaining.1
                  have parameterEquality :=
                    (natEqualBit_pos_iff _ _).mp remaining.2
                  let witness := StandardArithmeticAxiom.addZero term
                  exact
                    { formula := ScopedFormula.equal
                        (ScopedTerm.add term (ScopedTerm.zero bound)) term
                      witness := witness
                      conclusionExact := by
                        simp only [ScopedFormula.equal, ScopedTerm.add,
                          ScopedTerm.zero, RawFormula.code, RawTerm.code]
                        rw [termCode]
                        exact conclusionEquality.symm
                      parametersExact := by
                        change quoteNatList [2, term.raw.code] = parameterCode
                        rw [termCode]
                        exact parameterEquality.symm }
          | succ tag =>
              cases tag with
              | zero =>
                  simp only [tagValue, natEqualBit_zero_zero_inverse,
                    natEqualBit_zero_succ_inverse, natEqualBit_succ_zero,
                    natEqualBit_succ_succ, natIfZero] at accepted
                  have firstFields := (natAndBit_pos_iff _ _).mp accepted
                  have secondFields :=
                    (natAndBit_pos_iff _ _).mp firstFields.2
                  have thirdFields :=
                    (natAndBit_pos_iff _ _).mp secondFields.2
                  let decodedLeft := PRFunction.decodeScopedTermCodePositive bound
                    (RelationalPerimeter.HeytingArithmetic.codedListEntry parameterCode 1) firstFields.1
                  let left := decodedLeft.term
                  have leftCode := decodedLeft.codeExact
                  exact by
                      let decodedRight := PRFunction.decodeScopedTermCodePositive bound
                        (RelationalPerimeter.HeytingArithmetic.codedListEntry parameterCode 2) secondFields.1
                      let right := decodedRight.term
                      have rightCode := decodedRight.codeExact
                      exact by
                          have conclusionEquality :=
                            (natEqualBit_pos_iff _ _).mp thirdFields.1
                          have parameterEquality :=
                            (natEqualBit_pos_iff _ _).mp thirdFields.2
                          let witness :=
                            StandardArithmeticAxiom.addSuccessor left right
                          exact
                            { formula := ScopedFormula.equal
                                (ScopedTerm.add left right.succ)
                                (ScopedTerm.succ
                                  (ScopedTerm.add left right))
                              witness := witness
                              conclusionExact := by
                                simp only [ScopedFormula.equal, ScopedTerm.add,
                                  ScopedTerm.succ, RawFormula.code,
                                  RawTerm.code]
                                rw [leftCode, rightCode]
                                exact conclusionEquality.symm
                              parametersExact := by
                                change quoteNatList
                                  [3, left.raw.code, right.raw.code] =
                                    parameterCode
                                rw [leftCode, rightCode]
                                exact parameterEquality.symm }
              | succ tag =>
                  cases tag with
                  | zero =>
                      simp only [tagValue, natEqualBit_zero_zero_inverse,
                        natEqualBit_zero_succ_inverse, natEqualBit_succ_zero,
                        natEqualBit_succ_succ, natIfZero]
                        at accepted
                      have fields := (natAndBit_pos_iff _ _).mp accepted
                      have remaining :=
                        (natAndBit_pos_iff _ _).mp fields.2
                      let decoded := PRFunction.decodeScopedTermCodePositive bound
                        (RelationalPerimeter.HeytingArithmetic.codedListEntry parameterCode 1) fields.1
                      let term := decoded.term
                      have termCode := decoded.codeExact
                      exact by
                          have conclusionEquality :=
                            (natEqualBit_pos_iff _ _).mp remaining.1
                          have parameterEquality :=
                            (natEqualBit_pos_iff _ _).mp remaining.2
                          let witness :=
                            StandardArithmeticAxiom.multiplyZero term
                          exact
                            { formula := ScopedFormula.equal
                                (ScopedTerm.mul term (ScopedTerm.zero bound))
                                (ScopedTerm.zero bound)
                              witness := witness
                              conclusionExact := by
                                simp only [ScopedFormula.equal, ScopedTerm.mul,
                                  ScopedTerm.zero, RawFormula.code,
                                  RawTerm.code]
                                rw [termCode]
                                exact conclusionEquality.symm
                              parametersExact := by
                                change quoteNatList [4, term.raw.code] =
                                  parameterCode
                                rw [termCode]
                                exact parameterEquality.symm }
                  | succ tag =>
                      cases tag with
                      | zero =>
                          simp only [tagValue, natEqualBit_zero_zero_inverse,
                            natEqualBit_zero_succ_inverse,
                            natEqualBit_succ_zero,
                            natEqualBit_succ_succ, natIfZero]
                            at accepted
                          have firstFields :=
                            (natAndBit_pos_iff _ _).mp accepted
                          have secondFields :=
                            (natAndBit_pos_iff _ _).mp firstFields.2
                          have thirdFields :=
                            (natAndBit_pos_iff _ _).mp secondFields.2
                          let decodedLeft :=
                            PRFunction.decodeScopedTermCodePositive bound
                              (RelationalPerimeter.HeytingArithmetic.codedListEntry parameterCode 1)
                              firstFields.1
                          let left := decodedLeft.term
                          have leftCode := decodedLeft.codeExact
                          exact by
                              let decodedRight :=
                                PRFunction.decodeScopedTermCodePositive bound
                                  (RelationalPerimeter.HeytingArithmetic.codedListEntry parameterCode 2)
                                  secondFields.1
                              let right := decodedRight.term
                              have rightCode := decodedRight.codeExact
                              exact by
                                  have conclusionEquality :=
                                    (natEqualBit_pos_iff _ _).mp thirdFields.1
                                  have parameterEquality :=
                                    (natEqualBit_pos_iff _ _).mp thirdFields.2
                                  let witness :=
                                    StandardArithmeticAxiom.multiplySuccessor
                                      left right
                                  exact
                                    { formula := ScopedFormula.equal
                                        (ScopedTerm.mul left right.succ)
                                        (ScopedTerm.add
                                          (ScopedTerm.mul left right) left)
                                      witness := witness
                                      conclusionExact := by
                                        simp only [ScopedFormula.equal,
                                          ScopedTerm.mul, ScopedTerm.succ,
                                          ScopedTerm.add, RawFormula.code,
                                          RawTerm.code]
                                        rw [leftCode, rightCode]
                                        exact conclusionEquality.symm
                                      parametersExact := by
                                        change quoteNatList
                                          [5, left.raw.code, right.raw.code] =
                                            parameterCode
                                        rw [leftCode, rightCode]
                                        exact parameterEquality.symm }
                      | succ tag =>
                          cases tag with
                          | zero =>
                              simp only [tagValue,
                                natEqualBit_zero_zero_inverse,
                                natEqualBit_succ_zero,
                                natEqualBit_succ_succ, natIfZero]
                                at accepted
                              have fields :=
                                (natAndBit_pos_iff _ _).mp accepted
                              have remaining :=
                                (natAndBit_pos_iff _ _).mp fields.2
                              let decoded :=
                                PRFunction.decodeScopedFormulaCodePositive
                                  (Nat.succ bound)
                                  (RelationalPerimeter.HeytingArithmetic.codedListEntry parameterCode 1)
                                  fields.1
                              let body := decoded.formula
                              have bodyCode := decoded.codeExact
                              exact by
                                  have conclusionEquality :=
                                    (natEqualBit_pos_iff _ _).mp remaining.1
                                  have parameterEquality :=
                                    (natEqualBit_pos_iff _ _).mp remaining.2
                                  let witness :=
                                    StandardArithmeticAxiom.induction body
                                  exact
                                    { formula := ScopedFormula.induction body
                                      witness := witness
                                      conclusionExact := by
                                        rw [conclusionEquality]
                                        have baseCode :
                                            (body.instantiate
                                                (ScopedTerm.zero bound)).raw.code =
                                              machineInstantiateTermCode
                                                body.raw.code RawTerm.zero.code := by
                                          change
                                            (body.raw.instantiateTerm
                                                RawTerm.zero).code = _
                                          exact
                                            (machineInstantiateTermCode_code
                                              body.raw RawTerm.zero).symm
                                        have successorCode :
                                            body.successorInstance.raw.code =
                                              machineSuccessorInstanceCode
                                                body.raw.code := by
                                          change
                                            (body.raw.substitute
                                                ScopedFormula.replaceNewestKeepingScopeSubstitution).code = _
                                          exact
                                            (machineSuccessorInstanceCode_code
                                              body.raw).symm
                                        simp only [ScopedFormula.induction,
                                          ScopedFormula.impl,
                                          ScopedFormula.conj,
                                          ScopedFormula.all,
                                          RawFormula.code]
                                        rw [baseCode, successorCode, bodyCode]
                                      parametersExact := by
                                        change quoteNatList
                                          [6, body.raw.code] = parameterCode
                                        rw [bodyCode]
                                        exact parameterEquality.symm }
                          | succ tag =>
                              simp only [tagValue,
                                natEqualBit_succ_zero,
                                natEqualBit_succ_succ, natIfZero] at accepted
                              exact (Nat.not_lt_zero 0 accepted).elim

structure DecodedHistoryAxiomCode
    (history : TheoryHistory)
    (bound conclusionCode parameterCode : Nat) : Type where
  formula : ScopedFormula bound
  witness : HistoryAxiom history formula
  conclusionExact : formula.raw.code = conclusionCode
  parametersExact :
    quoteNatList (historyAxiomParameters witness) = parameterCode

def PRFunction.isHistoryAxiomCode_positive_sound
    (history : TheoryHistory)
    (bound conclusionCode parameterCode : Nat)
    (accepted : 0 < PRFunction.isHistoryAxiomCode.run
      (NatVector.cons history.quote
        (NatVector.cons bound
          (NatVector.cons conclusionCode
            (NatVector.cons parameterCode NatVector.nil))))) :
    DecodedHistoryAxiomCode history bound conclusionCode parameterCode := by
  unfold PRFunction.isHistoryAxiomCode at accepted
  repeat first
    | rw [PRFunction.run_binaryIn] at accepted
    | rw [PRFunction.run_composition] at accepted
    | rw [PRFunctionVector.run_cons] at accepted
    | rw [PRFunctionVector.run_singleton] at accepted
    | rw [PRFunction.run_projection] at accepted
    | rw [NatVector.get_cons_zero] at accepted
    | rw [NatVector.get_cons_succ] at accepted
    | rw [PRFunction.run_codedListEntry] at accepted
    | rw [PRFunction.run_codedListPair] at accepted
    | rw [PRFunction.run_equalBit] at accepted
    | rw [PRFunction.run_isPAAxiomCode] at accepted
    | rw [PRFunction.run_andBit] at accepted
    | rw [PRFunction.run_orBit] at accepted
  unfold historyAddedAxiomCode PRFunction.conjoinFour at accepted
  repeat first
    | rw [PRFunction.run_conjoin] at accepted
    | rw [PRFunction.run_binaryIn] at accepted
    | rw [PRFunction.run_composition] at accepted
    | rw [PRFunctionVector.run_cons] at accepted
    | rw [PRFunctionVector.run_singleton] at accepted
    | rw [PRFunction.run_projection] at accepted
    | rw [NatVector.get_cons_zero] at accepted
    | rw [NatVector.get_cons_succ] at accepted
    | rw [PRFunction.run_constant] at accepted
    | rw [PRFunction.run_codedListEntry] at accepted
    | rw [PRFunction.run_codedListPair] at accepted
    | rw [PRFunction.run_equalBit] at accepted
    | rw [PRFunction.run_andBit] at accepted
  let arithmeticValue := PRFunction.isPAAxiomCode.run
    (NatVector.cons bound
      (NatVector.cons conclusionCode
        (NatVector.cons parameterCode NatVector.nil)))
  cases arithmeticExact : arithmeticValue with
  | zero =>
      have alternatives := (natOrBit_pos_iff _ _).mp accepted
      have arithmeticNotPositive : ¬ 0 < arithmeticValue := by
        rw [arithmeticExact]
        exact Nat.not_lt_zero 0
      have addedPositive := Or.resolve_left alternatives arithmeticNotPositive
      have firstFields := (natAndBit_pos_iff _ _).mp addedPositive
      have secondFields := (natAndBit_pos_iff _ _).mp firstFields.2
      have thirdFields := (natAndBit_pos_iff _ _).mp secondFields.2
      have tagExact := (natEqualBit_pos_iff _ _).mp firstFields.1
      have parametersExact :=
        (natEqualBit_pos_iff _ _).mp secondFields.1
      have conclusionExact :=
        (natEqualBit_pos_iff _ _).mp thirdFields.1
      cases history.numeric_positive_implies_contains
          (RelationalPerimeter.HeytingArithmetic.codedListEntry parameterCode 1)
          thirdFields.2 with
      | mk sentence membership =>
          have sentenceCode := membership.2
          let formula := sentence.atBound bound
          let witness : HistoryAxiom history formula :=
            HistoryAxiom.added membership.1
          exact
            { formula := formula
              witness := witness
              conclusionExact := by
                change (sentence.atBound bound).raw.code = conclusionCode
                rw [Sentence.atBound_raw_eq]
                change sentence.quote = conclusionCode
                exact sentenceCode.trans conclusionExact.symm
              parametersExact := by
                change quoteNatList [7, sentence.quote] = parameterCode
                rw [sentenceCode]
                exact parametersExact.symm }
  | succ arithmeticPredecessor =>
      have arithmeticPositive : 0 < arithmeticValue := by
        rw [arithmeticExact]
        exact Nat.zero_lt_succ arithmeticPredecessor
      cases PRFunction.isPAAxiomCode_positive_sound bound conclusionCode
          parameterCode arithmeticPositive with
      | mk formula witness conclusionExact parametersExact =>
          exact
            { formula := formula
              witness := HistoryAxiom.arithmetic witness
              conclusionExact := conclusionExact
              parametersExact := parametersExact }

end HeytingArithmetic
end RelationalPerimeter

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.HeytingArithmetic.DecodedPAAxiomCode
#print axioms RelationalPerimeter.HeytingArithmetic.PRFunction.isPAAxiomCode_positive_sound
#print axioms RelationalPerimeter.HeytingArithmetic.DecodedHistoryAxiomCode
#print axioms RelationalPerimeter.HeytingArithmetic.PRFunction.isHistoryAxiomCode_positive_sound
/- AXIOM_AUDIT_END -/
