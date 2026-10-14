import RelationalPerimeter.Constitution.HeytingArithmetic.PrimitiveRecursiveKeepingScopeSubstitution
import RelationalPerimeter.Constitution.HeytingArithmetic.PrimitiveRecursiveProofCoding

/-!
# Primitive-recursive recognition of arithmetic and history axioms

All seven standard arithmetic schemes are reconstructed from their canonical
finite payloads.  In particular, induction is checked by the certified
instantiation and keeping-scope substitution programs; it is not trusted as a
tag.  A history postulate uses tag seven and must be positively present in the
encoded history.
-/

namespace RelationalPerimeter
namespace HeytingArithmetic

private theorem axiomIndexZero_lt_three : 0 < 3 := Nat.zero_lt_succ 2
private theorem axiomIndexOne_lt_three : 1 < 3 :=
  Nat.succ_lt_succ (Nat.zero_lt_succ 1)
private theorem axiomIndexTwo_lt_three : 2 < 3 :=
  Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.zero_lt_succ 0))
private theorem axiomIndexZero_lt_four : 0 < 4 := Nat.zero_lt_succ 3
private theorem axiomIndexOne_lt_four : 1 < 4 :=
  Nat.succ_lt_succ (Nat.zero_lt_succ 2)
private theorem axiomIndexTwo_lt_four : 2 < 4 :=
  Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.zero_lt_succ 1))
private theorem axiomIndexThree_lt_four : 3 < 4 :=
  Nat.succ_lt_succ
    (Nat.succ_lt_succ
      (Nat.succ_lt_succ (Nat.zero_lt_succ 0)))

def PRFunction.conjoinThree
    {arity : Nat} (first second third : PRFunction arity) : PRFunction arity :=
  PRFunction.conjoin first (PRFunction.conjoin second third)

def PRFunction.conjoinFour
    {arity : Nat} (first second third fourth : PRFunction arity) :
    PRFunction arity :=
  PRFunction.conjoin first
    (PRFunction.conjoin second (PRFunction.conjoin third fourth))

def PRFunction.formulaNegationCode
    {arity : Nat} (formula : PRFunction arity) : PRFunction arity :=
  PRFunction.binaryIn PRFunction.formulaImplicationCode formula
    (PRFunction.falsumCode arity)

/-! ## Standard arithmetic schemes -/

def paAxiomBound : PRFunction 3 :=
  PRFunction.projection 3 0 axiomIndexZero_lt_three

def paAxiomEntry (index : Nat) : PRFunction 3 :=
  PRFunction.composition PRFunction.codedListEntry
    (PRFunctionVector.cons
      (PRFunction.projection 3 2 axiomIndexTwo_lt_three)
      (PRFunctionVector.singleton (PRFunction.constant 3 index)))

def paAxiomScopedTerm (term : PRFunction 3) : PRFunction 3 :=
  PRFunction.composition PRFunction.isScopedTermCode
    (PRFunctionVector.cons
      (PRFunction.projection 3 0 axiomIndexZero_lt_three)
      (PRFunctionVector.singleton term))

def paAxiomSameConclusion (candidate : PRFunction 3) : PRFunction 3 :=
  PRFunction.binaryIn PRFunction.equalBit
    (PRFunction.projection 3 1 axiomIndexOne_lt_three) candidate

def paAxiomParametersTwo
    (tag : Nat) (term : PRFunction 3) : PRFunction 3 :=
  PRFunction.composition PRFunction.codedListPair
    (PRFunctionVector.cons (PRFunction.constant 3 tag)
      (PRFunctionVector.singleton term))

def paAxiomParametersThree
    (tag : Nat) (left right : PRFunction 3) : PRFunction 3 :=
  PRFunction.composition PRFunction.codedListTriple
    (PRFunctionVector.cons (PRFunction.constant 3 tag)
      (PRFunctionVector.cons left (PRFunctionVector.singleton right)))

def paAxiomSameParameters (expected : PRFunction 3) : PRFunction 3 :=
  PRFunction.binaryIn PRFunction.equalBit
    (PRFunction.projection 3 2 axiomIndexTwo_lt_three) expected

def paSuccessorNotZeroCode : PRFunction 3 :=
  let first := paAxiomEntry 1
  let zeroTerm := PRFunction.constant 3 RawTerm.zero.code
  let candidate := PRFunction.formulaNegationCode
    (PRFunction.binaryIn PRFunction.formulaEqualCode
      (PRFunction.unaryIn PRFunction.termSuccessorCode first) zeroTerm)
  PRFunction.conjoinThree (paAxiomScopedTerm first)
    (paAxiomSameConclusion candidate)
    (paAxiomSameParameters (paAxiomParametersTwo 0 first))

def paSuccessorInjectiveCode : PRFunction 3 :=
  let first := paAxiomEntry 1
  let second := paAxiomEntry 2
  let equal := fun left right =>
    PRFunction.binaryIn PRFunction.formulaEqualCode left right
  let candidate := PRFunction.binaryIn PRFunction.formulaImplicationCode
    (equal (PRFunction.unaryIn PRFunction.termSuccessorCode first)
      (PRFunction.unaryIn PRFunction.termSuccessorCode second))
    (equal first second)
  PRFunction.conjoinFour (paAxiomScopedTerm first) (paAxiomScopedTerm second)
    (paAxiomSameConclusion candidate)
    (paAxiomSameParameters (paAxiomParametersThree 1 first second))

def paAddZeroCode : PRFunction 3 :=
  let first := paAxiomEntry 1
  let candidate := PRFunction.binaryIn PRFunction.formulaEqualCode
    (PRFunction.binaryIn PRFunction.termAddCode first
      (PRFunction.constant 3 RawTerm.zero.code)) first
  PRFunction.conjoinThree (paAxiomScopedTerm first)
    (paAxiomSameConclusion candidate)
    (paAxiomSameParameters (paAxiomParametersTwo 2 first))

def paAddSuccessorCode : PRFunction 3 :=
  let first := paAxiomEntry 1
  let second := paAxiomEntry 2
  let add := PRFunction.binaryIn PRFunction.termAddCode
  let succ := PRFunction.unaryIn PRFunction.termSuccessorCode
  let candidate := PRFunction.binaryIn PRFunction.formulaEqualCode
    (add first (succ second)) (succ (add first second))
  PRFunction.conjoinFour (paAxiomScopedTerm first) (paAxiomScopedTerm second)
    (paAxiomSameConclusion candidate)
    (paAxiomSameParameters (paAxiomParametersThree 3 first second))

def paMultiplyZeroCode : PRFunction 3 :=
  let first := paAxiomEntry 1
  let zeroTerm := PRFunction.constant 3 RawTerm.zero.code
  let candidate := PRFunction.binaryIn PRFunction.formulaEqualCode
    (PRFunction.binaryIn PRFunction.termMultiplyCode first zeroTerm) zeroTerm
  PRFunction.conjoinThree (paAxiomScopedTerm first)
    (paAxiomSameConclusion candidate)
    (paAxiomSameParameters (paAxiomParametersTwo 4 first))

def paMultiplySuccessorCode : PRFunction 3 :=
  let first := paAxiomEntry 1
  let second := paAxiomEntry 2
  let multiply := PRFunction.binaryIn PRFunction.termMultiplyCode
  let add := PRFunction.binaryIn PRFunction.termAddCode
  let successor := PRFunction.unaryIn PRFunction.termSuccessorCode
  let candidate := PRFunction.binaryIn PRFunction.formulaEqualCode
    (multiply first (successor second)) (add (multiply first second) first)
  PRFunction.conjoinFour (paAxiomScopedTerm first) (paAxiomScopedTerm second)
    (paAxiomSameConclusion candidate)
    (paAxiomSameParameters (paAxiomParametersThree 5 first second))

def paInductionCode : PRFunction 3 :=
  let first := paAxiomEntry 1
  let zeroTerm := PRFunction.constant 3 RawTerm.zero.code
  let scopedBody := PRFunction.composition PRFunction.isScopedFormulaCode
    (PRFunctionVector.cons
      (PRFunction.unaryIn PRFunction.successor paAxiomBound)
      (PRFunctionVector.singleton first))
  let base := PRFunction.composition PRFunction.machineInstantiateTerm
    (PRFunctionVector.cons first (PRFunctionVector.singleton zeroTerm))
  let successorBody := PRFunction.unaryIn PRFunction.successorInstanceCode first
  let imply := PRFunction.binaryIn PRFunction.formulaImplicationCode
  let universal := PRFunction.unaryIn PRFunction.formulaUniversalCode
  let conjunction := PRFunction.binaryIn PRFunction.formulaConjunctionCode
  let candidate := imply
    (conjunction base (universal (imply first successorBody)))
    (universal first)
  PRFunction.conjoinThree scopedBody
    (paAxiomSameConclusion candidate)
    (paAxiomSameParameters (paAxiomParametersTwo 6 first))

/-- Inputs are `(bound,conclusionCode,parameterListCode)`. -/
def PRFunction.isPAAxiomCode : PRFunction 3 :=
  let tag := paAxiomEntry 0
  PRFunction.selectTag tag 0 paSuccessorNotZeroCode
    (PRFunction.selectTag tag 1 paSuccessorInjectiveCode
      (PRFunction.selectTag tag 2 paAddZeroCode
        (PRFunction.selectTag tag 3 paAddSuccessorCode
          (PRFunction.selectTag tag 4 paMultiplyZeroCode
            (PRFunction.selectTag tag 5 paMultiplySuccessorCode
              (PRFunction.selectTag tag 6 paInductionCode
                (PRFunction.constant 3 0)))))))

/-! ## Uniform history axioms -/

def historyAddedAxiomCode : PRFunction 4 :=
  let history := PRFunction.projection 4 0 axiomIndexZero_lt_four
  let conclusion := PRFunction.projection 4 2 axiomIndexTwo_lt_four
  let parameters := PRFunction.projection 4 3 axiomIndexThree_lt_four
  let tag := PRFunction.composition PRFunction.codedListEntry
    (PRFunctionVector.cons parameters
      (PRFunctionVector.singleton (PRFunction.constant 4 0)))
  let sentence := PRFunction.composition PRFunction.codedListEntry
    (PRFunctionVector.cons parameters
      (PRFunctionVector.singleton (PRFunction.constant 4 1)))
  let expectedParameters := PRFunction.composition PRFunction.codedListPair
    (PRFunctionVector.cons (PRFunction.constant 4 7)
      (PRFunctionVector.singleton sentence))
  PRFunction.conjoinFour
    (PRFunction.binaryIn PRFunction.equalBit tag (PRFunction.constant 4 7))
    (PRFunction.binaryIn PRFunction.equalBit parameters expectedParameters)
    (PRFunction.binaryIn PRFunction.equalBit conclusion sentence)
    (PRFunction.composition PRFunction.theoryHistoryContains
      (PRFunctionVector.cons history (PRFunctionVector.singleton sentence)))

/-- Inputs are `(historyCode,bound,conclusionCode,parameterListCode)`. -/
def PRFunction.isHistoryAxiomCode : PRFunction 4 :=
  let bound := PRFunction.projection 4 1 axiomIndexOne_lt_four
  let conclusion := PRFunction.projection 4 2 axiomIndexTwo_lt_four
  let parameters := PRFunction.projection 4 3 axiomIndexThree_lt_four
  let pa := PRFunction.composition PRFunction.isPAAxiomCode
    (PRFunctionVector.cons bound
      (PRFunctionVector.cons conclusion
        (PRFunctionVector.singleton parameters)))
  PRFunction.binaryIn PRFunction.orBit pa historyAddedAxiomCode

/-! ## Canonical acceptance theorems -/

private theorem natAndBit_one_one : natAndBit 1 1 = 1 := rfl
private theorem natOrBit_one_left (right : Nat) : natOrBit 1 right = 1 := rfl
private theorem natOrBit_one_right (left : Nat) : natOrBit left 1 = 1 := by
  cases left <;> rfl
private theorem natEqualBit_self (value : Nat) :
    natEqualBit value value = 1 :=
  (natEqualBit_eq_one_iff value value).mpr rfl

private theorem natEqualBit_of_ne
    (left right : Nat)
    (different : left ≠ right) :
    natEqualBit left right = 0 := by
  induction left generalizing right with
  | zero =>
      cases right with
      | zero => exact (different rfl).elim
      | succ right => rfl
  | succ left inductionHypothesis =>
      cases right with
      | zero => exact natEqualBit_succ_zero left
      | succ right =>
          rw [natEqualBit_succ_succ]
          exact inductionHypothesis right
            (fun equality => different (congrArg Nat.succ equality))

private theorem natEqualBit_zero_succ (right : Nat) :
    natEqualBit 0 (Nat.succ right) = 0 := rfl

private theorem codedListEntry_quote_cons_zero
    (head : Nat) (tail : List Nat) :
    codedListEntry (quoteNatList (head :: tail)) 0 = head := by
  rw [quoteNatList, codedListEntry, codedListHead, natUnpair_pair]

private theorem codedListEntry_quote_cons_succ
    (head : Nat) (tail : List Nat) (index : Nat) :
    codedListEntry (quoteNatList (head :: tail)) (Nat.succ index) =
      codedListEntry (quoteNatList tail) index := by
  rw [codedListEntry, quoteNatList, codedListTail, natUnpair_pair]

macro "normalize_axiom_program" : tactic =>
  `(tactic|
    repeat first
      | unfold PRFunction.conjoinThree
      | unfold PRFunction.conjoinFour
      | unfold PRFunction.formulaNegationCode
      | rw [PRFunction.run_selectTag]
      | rw [PRFunction.run_conjoin]
      | rw [PRFunction.run_binaryIn]
      | rw [PRFunction.run_unaryIn]
      | rw [PRFunction.run_composition]
      | rw [PRFunctionVector.run_cons]
      | rw [PRFunctionVector.run_singleton]
      | rw [PRFunction.run_projection]
      | rw [NatVector.get_cons_zero]
      | rw [NatVector.get_cons_succ]
      | rw [PRFunction.run_constant]
      | rw [PRFunction.run_codedListEntry]
      | rw [PRFunction.run_codedListPair]
      | rw [PRFunction.run_codedListTriple]
      | rw [PRFunction.run_termSuccessorCode]
      | rw [PRFunction.run_termAddCode]
      | rw [PRFunction.run_termMultiplyCode]
      | rw [PRFunction.run_formulaEqualCode]
      | rw [PRFunction.run_formulaImplicationCode]
      | rw [PRFunction.run_formulaConjunctionCode]
      | rw [PRFunction.run_formulaUniversalCode]
      | rw [PRFunction.run_falsumCode]
      | rw [PRFunction.run_equalBit]
      | rw [PRFunction.run_andBit]
      | rw [PRFunction.run_orBit])

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

private theorem PRFunction.run_conjoinThree_of_one
    {arity : Nat}
    (first second third : PRFunction arity)
    (input : NatVector arity)
    (firstOne : first.run input = 1)
    (secondOne : second.run input = 1)
    (thirdOne : third.run input = 1) :
    (PRFunction.conjoinThree first second third).run input = 1 := by
  unfold PRFunction.conjoinThree
  rw [PRFunction.run_conjoin, firstOne,
    PRFunction.run_conjoin, secondOne, thirdOne]
  rfl

private theorem PRFunction.run_conjoinFour_of_one
    {arity : Nat}
    (first second third fourth : PRFunction arity)
    (input : NatVector arity)
    (firstOne : first.run input = 1)
    (secondOne : second.run input = 1)
    (thirdOne : third.run input = 1)
    (fourthOne : fourth.run input = 1) :
    (PRFunction.conjoinFour first second third fourth).run input = 1 := by
  unfold PRFunction.conjoinFour
  rw [PRFunction.run_conjoin, firstOne,
    PRFunction.run_conjoin, secondOne,
    PRFunction.run_conjoin, thirdOne, fourthOne]
  rfl

private theorem paSuccessorNotZeroCode_accepts
    {bound : Nat} (term : ScopedTerm bound) :
    paSuccessorNotZeroCode.run
        (NatVector.cons bound
          (NatVector.cons
            (ScopedFormula.neg
              (ScopedFormula.equal term.succ (ScopedTerm.zero bound))).raw.code
            (NatVector.cons (quoteNatList [0, term.raw.code]) NatVector.nil))) = 1 := by
  unfold paSuccessorNotZeroCode
  apply PRFunction.run_conjoinThree_of_one
  case firstOne =>
    unfold paAxiomScopedTerm paAxiomEntry
    normalize_axiom_program
    rw [codedListEntry_quote_cons_succ, codedListEntry_quote_cons_zero]
    exact PRFunction.isScopedTermCode_accepts term
  case secondOne =>
    unfold paAxiomSameConclusion paAxiomEntry
    normalize_axiom_program
    rw [codedListEntry_quote_cons_succ, codedListEntry_quote_cons_zero]
    exact natEqualBit_self _
  case thirdOne =>
    unfold paAxiomSameParameters paAxiomParametersTwo paAxiomEntry
    normalize_axiom_program
    rw [codedListEntry_quote_cons_succ, codedListEntry_quote_cons_zero]
    exact natEqualBit_self _

private theorem historyAddedAxiomCode_accepts
    {history : TheoryHistory}
    {sentence : Sentence}
    (evidence : history.Contains sentence)
    (bound : Nat) :
    historyAddedAxiomCode.run
        (NatVector.cons history.quote
          (NatVector.cons bound
            (NatVector.cons sentence.raw.code
              (NatVector.cons (quoteNatList [7, sentence.quote])
                NatVector.nil)))) = 1 := by
  unfold historyAddedAxiomCode
  apply PRFunction.run_conjoinFour_of_one
  case firstOne =>
    normalize_axiom_program
    rw [codedListEntry_quote_cons_zero]
    exact natEqualBit_self _
  case secondOne =>
    normalize_axiom_program
    simp only [codedListEntry_quote_cons_zero,
      codedListEntry_quote_cons_succ]
    exact natEqualBit_self _
  case thirdOne =>
    normalize_axiom_program
    simp only [codedListEntry_quote_cons_zero,
      codedListEntry_quote_cons_succ]
    exact natEqualBit_self _
  case fourthOne =>
    normalize_axiom_program
    simp only [codedListEntry_quote_cons_zero,
      codedListEntry_quote_cons_succ]
    exact TheoryHistory.contains_implies_numeric evidence

private theorem paSuccessorInjectiveCode_accepts
    {bound : Nat} (left right : ScopedTerm bound) :
    paSuccessorInjectiveCode.run
        (NatVector.cons bound
          (NatVector.cons
            (ScopedFormula.impl
              (ScopedFormula.equal left.succ right.succ)
              (ScopedFormula.equal left right)).raw.code
            (NatVector.cons
              (quoteNatList [1, left.raw.code, right.raw.code]) NatVector.nil))) = 1 := by
  unfold paSuccessorInjectiveCode
  apply PRFunction.run_conjoinFour_of_one
  case firstOne =>
    unfold paAxiomScopedTerm paAxiomEntry
    normalize_axiom_program
    simp only [codedListEntry_quote_cons_zero,
      codedListEntry_quote_cons_succ]
    exact PRFunction.isScopedTermCode_accepts left
  case secondOne =>
    unfold paAxiomScopedTerm paAxiomEntry
    normalize_axiom_program
    simp only [codedListEntry_quote_cons_zero,
      codedListEntry_quote_cons_succ]
    exact PRFunction.isScopedTermCode_accepts right
  case thirdOne =>
    unfold paAxiomSameConclusion paAxiomEntry
    normalize_axiom_program
    simp only [codedListEntry_quote_cons_zero,
      codedListEntry_quote_cons_succ]
    exact natEqualBit_self _
  case fourthOne =>
    unfold paAxiomSameParameters paAxiomParametersThree paAxiomEntry
    normalize_axiom_program
    simp only [codedListEntry_quote_cons_zero,
      codedListEntry_quote_cons_succ]
    exact natEqualBit_self _

private theorem paAddZeroCode_accepts
    {bound : Nat} (term : ScopedTerm bound) :
    paAddZeroCode.run
        (NatVector.cons bound
          (NatVector.cons
            (ScopedFormula.equal
              (ScopedTerm.add term (ScopedTerm.zero bound)) term).raw.code
            (NatVector.cons (quoteNatList [2, term.raw.code]) NatVector.nil))) = 1 := by
  unfold paAddZeroCode
  apply PRFunction.run_conjoinThree_of_one
  case firstOne =>
    unfold paAxiomScopedTerm paAxiomEntry
    normalize_axiom_program
    simp only [codedListEntry_quote_cons_zero,
      codedListEntry_quote_cons_succ]
    exact PRFunction.isScopedTermCode_accepts term
  case secondOne =>
    unfold paAxiomSameConclusion paAxiomEntry
    normalize_axiom_program
    simp only [codedListEntry_quote_cons_zero,
      codedListEntry_quote_cons_succ]
    exact natEqualBit_self _
  case thirdOne =>
    unfold paAxiomSameParameters paAxiomParametersTwo paAxiomEntry
    normalize_axiom_program
    simp only [codedListEntry_quote_cons_zero,
      codedListEntry_quote_cons_succ]
    exact natEqualBit_self _

private theorem paAddSuccessorCode_accepts
    {bound : Nat} (left right : ScopedTerm bound) :
    paAddSuccessorCode.run
        (NatVector.cons bound
          (NatVector.cons
            (ScopedFormula.equal
              (ScopedTerm.add left right.succ)
              (ScopedTerm.succ (ScopedTerm.add left right))).raw.code
            (NatVector.cons
              (quoteNatList [3, left.raw.code, right.raw.code]) NatVector.nil))) = 1 := by
  unfold paAddSuccessorCode
  apply PRFunction.run_conjoinFour_of_one
  case firstOne =>
    unfold paAxiomScopedTerm paAxiomEntry
    normalize_axiom_program
    simp only [codedListEntry_quote_cons_zero,
      codedListEntry_quote_cons_succ]
    exact PRFunction.isScopedTermCode_accepts left
  case secondOne =>
    unfold paAxiomScopedTerm paAxiomEntry
    normalize_axiom_program
    simp only [codedListEntry_quote_cons_zero,
      codedListEntry_quote_cons_succ]
    exact PRFunction.isScopedTermCode_accepts right
  case thirdOne =>
    unfold paAxiomSameConclusion paAxiomEntry
    normalize_axiom_program
    simp only [codedListEntry_quote_cons_zero,
      codedListEntry_quote_cons_succ]
    exact natEqualBit_self _
  case fourthOne =>
    unfold paAxiomSameParameters paAxiomParametersThree paAxiomEntry
    normalize_axiom_program
    simp only [codedListEntry_quote_cons_zero,
      codedListEntry_quote_cons_succ]
    exact natEqualBit_self _

private theorem paMultiplyZeroCode_accepts
    {bound : Nat} (term : ScopedTerm bound) :
    paMultiplyZeroCode.run
        (NatVector.cons bound
          (NatVector.cons
            (ScopedFormula.equal
              (ScopedTerm.mul term (ScopedTerm.zero bound))
              (ScopedTerm.zero bound)).raw.code
            (NatVector.cons (quoteNatList [4, term.raw.code]) NatVector.nil))) = 1 := by
  unfold paMultiplyZeroCode
  apply PRFunction.run_conjoinThree_of_one
  case firstOne =>
    unfold paAxiomScopedTerm paAxiomEntry
    normalize_axiom_program
    simp only [codedListEntry_quote_cons_zero,
      codedListEntry_quote_cons_succ]
    exact PRFunction.isScopedTermCode_accepts term
  case secondOne =>
    unfold paAxiomSameConclusion paAxiomEntry
    normalize_axiom_program
    simp only [codedListEntry_quote_cons_zero,
      codedListEntry_quote_cons_succ]
    exact natEqualBit_self _
  case thirdOne =>
    unfold paAxiomSameParameters paAxiomParametersTwo paAxiomEntry
    normalize_axiom_program
    simp only [codedListEntry_quote_cons_zero,
      codedListEntry_quote_cons_succ]
    exact natEqualBit_self _

private theorem paMultiplySuccessorCode_accepts
    {bound : Nat} (left right : ScopedTerm bound) :
    paMultiplySuccessorCode.run
        (NatVector.cons bound
          (NatVector.cons
            (ScopedFormula.equal
              (ScopedTerm.mul left right.succ)
              (ScopedTerm.add (ScopedTerm.mul left right) left)).raw.code
            (NatVector.cons
              (quoteNatList [5, left.raw.code, right.raw.code]) NatVector.nil))) = 1 := by
  unfold paMultiplySuccessorCode
  apply PRFunction.run_conjoinFour_of_one
  case firstOne =>
    unfold paAxiomScopedTerm paAxiomEntry
    normalize_axiom_program
    simp only [codedListEntry_quote_cons_zero,
      codedListEntry_quote_cons_succ]
    exact PRFunction.isScopedTermCode_accepts left
  case secondOne =>
    unfold paAxiomScopedTerm paAxiomEntry
    normalize_axiom_program
    simp only [codedListEntry_quote_cons_zero,
      codedListEntry_quote_cons_succ]
    exact PRFunction.isScopedTermCode_accepts right
  case thirdOne =>
    unfold paAxiomSameConclusion paAxiomEntry
    normalize_axiom_program
    simp only [codedListEntry_quote_cons_zero,
      codedListEntry_quote_cons_succ]
    exact natEqualBit_self _
  case fourthOne =>
    unfold paAxiomSameParameters paAxiomParametersThree paAxiomEntry
    normalize_axiom_program
    simp only [codedListEntry_quote_cons_zero,
      codedListEntry_quote_cons_succ]
    exact natEqualBit_self _

private theorem paInductionCode_accepts
    {bound : Nat} (body : ScopedFormula (Nat.succ bound)) :
    paInductionCode.run
        (NatVector.cons bound
          (NatVector.cons (ScopedFormula.induction body).raw.code
            (NatVector.cons (quoteNatList [6, body.raw.code]) NatVector.nil))) = 1 := by
  unfold paInductionCode
  apply PRFunction.run_conjoinThree_of_one
  case firstOne =>
    unfold paAxiomBound paAxiomEntry
    normalize_axiom_program
    simp only [codedListEntry_quote_cons_zero,
      codedListEntry_quote_cons_succ]
    exact PRFunction.isScopedFormulaCode_accepts body
  case secondOne =>
    unfold paAxiomSameConclusion paAxiomEntry
    normalize_axiom_program
    simp only [codedListEntry_quote_cons_zero,
      codedListEntry_quote_cons_succ]
    rw [PRFunction.run_machineInstantiateTerm,
      PRFunction.run_successorInstanceCode]
    have baseCode :
        machineInstantiateTermCode body.raw.code RawTerm.zero.code =
          (body.raw.instantiateTerm RawTerm.zero).code := by
      exact machineInstantiateTermCode_code body.raw RawTerm.zero
    rw [baseCode, machineSuccessorInstanceCode_code body.raw]
    exact natEqualBit_self _
  case thirdOne =>
    unfold paAxiomSameParameters paAxiomParametersTwo paAxiomEntry
    normalize_axiom_program
    simp only [codedListEntry_quote_cons_zero,
      codedListEntry_quote_cons_succ]
    exact natEqualBit_self _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem PRFunction.isPAAxiomCode_accepts
    {bound : Nat}
    {formula : ScopedFormula bound}
    (witness : StandardArithmeticAxiom formula) :
    PRFunction.isPAAxiomCode.run
        (NatVector.cons bound
          (NatVector.cons formula.raw.code
            (NatVector.cons
              (quoteNatList (standardArithmeticAxiomParameters witness))
              NatVector.nil))) = 1 := by
  cases witness with
  | successorNotZero term =>
    unfold PRFunction.isPAAxiomCode paAxiomEntry
    normalize_axiom_program
    simp only [standardArithmeticAxiomParameters,
      codedListEntry_quote_cons_zero, natEqualBit_self, natIfZero]
    exact paSuccessorNotZeroCode_accepts term
  | successorInjective left right =>
    unfold PRFunction.isPAAxiomCode paAxiomEntry
    normalize_axiom_program
    simp only [standardArithmeticAxiomParameters,
      codedListEntry_quote_cons_zero,
      natEqualBit_self,
      natEqualBit_succ_zero, natEqualBit_succ_succ, natIfZero]
    exact paSuccessorInjectiveCode_accepts left right
  | addZero term =>
    unfold PRFunction.isPAAxiomCode paAxiomEntry
    normalize_axiom_program
    simp only [standardArithmeticAxiomParameters,
      codedListEntry_quote_cons_zero,
      natEqualBit_self, natEqualBit_zero_succ,
      natEqualBit_succ_zero, natEqualBit_succ_succ, natIfZero]
    exact paAddZeroCode_accepts term
  | addSuccessor left right =>
    unfold PRFunction.isPAAxiomCode paAxiomEntry
    normalize_axiom_program
    simp only [standardArithmeticAxiomParameters,
      codedListEntry_quote_cons_zero,
      natEqualBit_self, natEqualBit_zero_succ,
      natEqualBit_succ_zero, natEqualBit_succ_succ, natIfZero]
    exact paAddSuccessorCode_accepts left right
  | multiplyZero term =>
    unfold PRFunction.isPAAxiomCode paAxiomEntry
    normalize_axiom_program
    simp only [standardArithmeticAxiomParameters,
      codedListEntry_quote_cons_zero,
      natEqualBit_self, natEqualBit_zero_succ,
      natEqualBit_succ_zero, natEqualBit_succ_succ, natIfZero]
    exact paMultiplyZeroCode_accepts term
  | multiplySuccessor left right =>
    unfold PRFunction.isPAAxiomCode paAxiomEntry
    normalize_axiom_program
    simp only [standardArithmeticAxiomParameters,
      codedListEntry_quote_cons_zero,
      natEqualBit_self, natEqualBit_zero_succ,
      natEqualBit_succ_zero, natEqualBit_succ_succ, natIfZero]
    exact paMultiplySuccessorCode_accepts left right
  | induction body =>
    unfold PRFunction.isPAAxiomCode paAxiomEntry
    normalize_axiom_program
    simp only [standardArithmeticAxiomParameters,
      codedListEntry_quote_cons_zero,
      natEqualBit_self,
      natEqualBit_succ_zero, natEqualBit_succ_succ, natIfZero]
    exact paInductionCode_accepts body

theorem PRFunction.isHistoryAxiomCode_accepts_arithmetic
    (history : TheoryHistory)
    {bound : Nat}
    {formula : ScopedFormula bound}
    (witness : StandardArithmeticAxiom formula) :
    PRFunction.isHistoryAxiomCode.run
        (NatVector.cons history.quote
          (NatVector.cons bound
            (NatVector.cons formula.raw.code
              (NatVector.cons
                (quoteNatList (standardArithmeticAxiomParameters witness))
                NatVector.nil)))) = 1 := by
  unfold PRFunction.isHistoryAxiomCode
  repeat first
    | rw [PRFunction.run_binaryIn]
    | rw [PRFunction.run_composition]
    | rw [PRFunctionVector.run_cons]
    | rw [PRFunctionVector.run_singleton]
    | rw [PRFunction.run_projection]
    | rw [NatVector.get_cons_zero]
    | rw [NatVector.get_cons_succ]
    | rw [PRFunction.run_isPAAxiomCode]
    | rw [PRFunction.run_orBit]
  rw [PRFunction.isPAAxiomCode_accepts witness]
  rfl

theorem Sentence.atBound_raw_eq
    (sentence : Sentence)
    (bound : Nat) :
    (sentence.atBound bound).raw = sentence.raw := by
  induction bound with
  | zero => rfl
  | succ bound inductionHypothesis =>
      change (sentence.atBound bound).raw.rename Nat.succ = sentence.raw
      rw [inductionHypothesis]
      exact sentence.raw.rename_eq_self_of_wellScoped
        0 sentence.isScoped Nat.succ (fun index bounded =>
          (Nat.not_lt_zero index bounded).elim)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem PRFunction.isHistoryAxiomCode_accepts_added
    {history : TheoryHistory}
    {sentence : Sentence}
    (evidence : history.Contains sentence)
    (bound : Nat) :
    PRFunction.isHistoryAxiomCode.run
        (NatVector.cons history.quote
          (NatVector.cons bound
            (NatVector.cons (sentence.atBound bound).raw.code
              (NatVector.cons (quoteNatList [7, sentence.quote])
                NatVector.nil)))) = 1 := by
  rw [Sentence.atBound_raw_eq]
  unfold PRFunction.isHistoryAxiomCode
  rw [PRFunction.run_binaryIn, PRFunction.run_orBit]
  rw [historyAddedAxiomCode_accepts evidence bound]
  exact natOrBit_one_right _

end HeytingArithmetic
end RelationalPerimeter

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.HeytingArithmetic.PRFunction.isPAAxiomCode
#print axioms RelationalPerimeter.HeytingArithmetic.PRFunction.isPAAxiomCode_accepts
#print axioms RelationalPerimeter.HeytingArithmetic.PRFunction.isHistoryAxiomCode
#print axioms RelationalPerimeter.HeytingArithmetic.PRFunction.isHistoryAxiomCode_accepts_arithmetic
#print axioms RelationalPerimeter.HeytingArithmetic.PRFunction.isHistoryAxiomCode_accepts_added
/- AXIOM_AUDIT_END -/
