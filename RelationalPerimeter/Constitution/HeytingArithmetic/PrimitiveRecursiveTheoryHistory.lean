import RelationalPerimeter.Constitution.HeytingArithmetic.PrimitiveRecursiveSyntaxRecognition
import RelationalPerimeter.Constitution.HeytingArithmetic.TheoryHistoryCoding

/-!
# Primitive-recursive access to finite theory histories

Histories are positive prefix lists of closed sentence codes.  Membership is
computed by a bounded scan whose remaining suffix is part of the recursive
state.  This is the numeric operation consumed by the uniform postulate checker.
-/

namespace RelationalPerimeter
namespace HeytingArithmetic

private theorem historyIndexZero_lt_two : 0 < 2 := Nat.zero_lt_succ 1
private theorem historyIndexOne_lt_two : 1 < 2 :=
  Nat.succ_lt_succ (Nat.zero_lt_succ 0)
private theorem historyIndexOne_lt_four : 1 < 4 :=
  Nat.succ_lt_succ (Nat.zero_lt_succ 2)
private theorem historyIndexThree_lt_four : 3 < 4 :=
  Nat.succ_lt_succ
    (Nat.succ_lt_succ
      (Nat.succ_lt_succ (Nat.zero_lt_succ 0)))

/-! ## Bounded membership scan -/

def theoryHistoryContainsStep (state target : Nat) : Nat :=
  let remaining := natUnpairLeft state
  let found := natUnpairRight state
  match remaining with
  | 0 => state
  | Nat.succ encoded =>
      let head := natUnpairLeft encoded
      let tail := natUnpairRight encoded
      natPair tail (natOrBit found (natEqualBit head target))

def theoryHistoryContainsRun : Nat -> Nat -> Nat -> Nat
  | 0, state, _target => state
  | Nat.succ steps, state, target =>
      theoryHistoryContainsRun steps
        (theoryHistoryContainsStep state target) target

theorem theoryHistoryContainsRun_add
    (first second state target : Nat) :
    theoryHistoryContainsRun (first + second) state target =
      theoryHistoryContainsRun second
        (theoryHistoryContainsRun first state target) target := by
  induction first generalizing state with
  | zero =>
      rw [Nat.zero_add]
      rfl
  | succ first inductionHypothesis =>
      rw [Nat.succ_add]
      change theoryHistoryContainsRun (first + second)
        (theoryHistoryContainsStep state target) target = _
      exact inductionHypothesis (theoryHistoryContainsStep state target)

theorem theoryHistoryContainsRun_succ_right
    (steps state target : Nat) :
    theoryHistoryContainsRun (Nat.succ steps) state target =
      theoryHistoryContainsStep
        (theoryHistoryContainsRun steps state target) target := by
  induction steps generalizing state with
  | zero => rfl
  | succ steps inductionHypothesis =>
      change theoryHistoryContainsRun steps
          (theoryHistoryContainsStep
            (theoryHistoryContainsStep state target) target) target =
        theoryHistoryContainsStep
          (theoryHistoryContainsRun steps
            (theoryHistoryContainsStep state target) target) target
      exact inductionHypothesis (theoryHistoryContainsStep state target)

def theoryHistoryContainsBit (historyCode sentenceCode : Nat) : Nat :=
  natUnpairRight
    (theoryHistoryContainsRun historyCode (natPair historyCode 0)
      sentenceCode)

def PRFunction.theoryHistoryContainsIterationStep : PRFunction 4 :=
  let previous := PRFunction.projection 4 1 historyIndexOne_lt_four
  let target := PRFunction.projection 4 3 historyIndexThree_lt_four
  let remaining := PRFunction.unaryIn PRFunction.unpairLeft previous
  let found := PRFunction.unaryIn PRFunction.unpairRight previous
  let encoded := PRFunction.unaryIn PRFunction.predecessor remaining
  let head := PRFunction.unaryIn PRFunction.unpairLeft encoded
  let tail := PRFunction.unaryIn PRFunction.unpairRight encoded
  let same := PRFunction.binaryIn PRFunction.equalBit head target
  let nextFound := PRFunction.binaryIn PRFunction.orBit found same
  let next := PRFunction.binaryIn PRFunction.pair tail nextFound
  PRFunction.select remaining previous next

def PRFunction.theoryHistoryContainsRun : PRFunction 3 :=
  PRFunction.primitiveRecursion
    (PRFunction.projection 2 0 historyIndexZero_lt_two)
    PRFunction.theoryHistoryContainsIterationStep

def PRFunction.theoryHistoryContains : PRFunction 2 :=
  let historyCode := PRFunction.projection 2 0 historyIndexZero_lt_two
  let sentenceCode := PRFunction.projection 2 1 historyIndexOne_lt_two
  let initial := PRFunction.binaryIn PRFunction.pair historyCode
    (PRFunction.constant 2 0)
  let finalState := PRFunction.composition
    PRFunction.theoryHistoryContainsRun
    (PRFunctionVector.cons historyCode
      (PRFunctionVector.cons initial
        (PRFunctionVector.singleton sentenceCode)))
  PRFunction.unaryIn PRFunction.unpairRight finalState

@[simp] theorem PRFunction.run_theoryHistoryContainsIterationStep
    (counter previous state target : Nat) :
    PRFunction.theoryHistoryContainsIterationStep.run
        (NatVector.cons counter
          (NatVector.cons previous
            (NatVector.cons state
              (NatVector.cons target NatVector.nil)))) =
      theoryHistoryContainsStep previous target := by
  unfold PRFunction.theoryHistoryContainsIterationStep
    theoryHistoryContainsStep
  repeat first
    | rw [PRFunction.run_select]
    | rw [PRFunction.run_projection]
    | rw [NatVector.get_cons_zero]
    | rw [NatVector.get_cons_succ]
    | rw [PRFunction.run_unaryIn]
    | rw [PRFunction.run_binaryIn]
    | rw [PRFunction.run_unpairLeft]
    | rw [PRFunction.run_unpairRight]
    | rw [PRFunction.run_predecessor]
    | rw [PRFunction.run_equalBit]
    | rw [PRFunction.run_orBit]
    | rw [PRFunction.run_pair]
  cases remaining : natUnpairLeft previous <;> rfl

theorem PRFunction.run_theoryHistoryContainsRun
    (steps state target : Nat) :
    PRFunction.theoryHistoryContainsRun.run
        (NatVector.cons steps
          (NatVector.cons state (NatVector.cons target NatVector.nil))) =
      HeytingArithmetic.theoryHistoryContainsRun steps state target := by
  induction steps with
  | zero => rfl
  | succ steps inductionHypothesis =>
      change PRFunction.theoryHistoryContainsIterationStep.run
        (NatVector.cons steps
          (NatVector.cons
            (PRFunction.theoryHistoryContainsRun.run
              (NatVector.cons steps
                (NatVector.cons state
                  (NatVector.cons target NatVector.nil))))
            (NatVector.cons state
              (NatVector.cons target NatVector.nil)))) = _
      rw [PRFunction.run_theoryHistoryContainsIterationStep,
        inductionHypothesis]
      exact (theoryHistoryContainsRun_succ_right steps state target).symm

@[simp] theorem PRFunction.run_theoryHistoryContains
    (historyCode sentenceCode : Nat) :
    PRFunction.theoryHistoryContains.run
        (NatVector.cons historyCode
          (NatVector.cons sentenceCode NatVector.nil)) =
      theoryHistoryContainsBit historyCode sentenceCode := by
  unfold PRFunction.theoryHistoryContains theoryHistoryContainsBit
  repeat first
    | rw [PRFunction.run_unaryIn]
    | rw [PRFunction.run_binaryIn]
    | rw [PRFunction.run_composition]
    | rw [PRFunctionVector.run_cons]
    | rw [PRFunctionVector.run_singleton]
    | rw [PRFunction.run_projection]
    | rw [NatVector.get_cons_zero]
    | rw [NatVector.get_cons_succ]
    | rw [PRFunction.run_constant]
    | rw [PRFunction.run_pair]
    | rw [PRFunction.run_theoryHistoryContainsRun]
    | rw [PRFunction.run_unpairRight]

/-! ## Correctness on intrinsic histories -/

def TheoryHistory.sentenceCodes : TheoryHistory -> List Nat
  | TheoryHistory.root => []
  | TheoryHistory.extend previous sentence =>
      sentence.quote :: previous.sentenceCodes

theorem TheoryHistory.quote_eq_quoteNatList_sentenceCodes
    (history : TheoryHistory) :
    history.quote = quoteNatList history.sentenceCodes := by
  induction history with
  | root => rfl
  | extend previous sentence inductionHypothesis =>
      change Nat.succ (natPair sentence.quote previous.quote) =
        Nat.succ (natPair sentence.quote
          (quoteNatList previous.sentenceCodes))
      rw [inductionHypothesis]

def listContainsFrom : List Nat -> Nat -> Nat -> Nat
  | [], _target, found => found
  | head :: tail, target, found =>
      listContainsFrom tail target
        (natOrBit found (natEqualBit head target))

def listContainsBit (values : List Nat) (target : Nat) : Nat :=
  listContainsFrom values target 0

theorem theoryHistoryContainsRun_quote_exact
    (values : List Nat)
    (target found : Nat) :
    theoryHistoryContainsRun values.length
        (natPair (quoteNatList values) found) target =
      natPair 0 (listContainsFrom values target found) := by
  induction values generalizing found with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      simpa [theoryHistoryContainsRun, theoryHistoryContainsStep,
        quoteNatList, listContainsFrom,
        natUnpairLeft_pair, natUnpairRight_pair] using
        inductionHypothesis
          (natOrBit found (natEqualBit head target))

theorem theoryHistoryContainsRun_completed
    (steps found target : Nat) :
    theoryHistoryContainsRun steps (natPair 0 found) target =
      natPair 0 found := by
  induction steps with
  | zero => rfl
  | succ steps inductionHypothesis =>
      change theoryHistoryContainsRun steps
        (theoryHistoryContainsStep (natPair 0 found) target) target = _
      unfold theoryHistoryContainsStep
      rw [natUnpairLeft_pair, natUnpairRight_pair]
      exact inductionHypothesis

theorem theoryHistoryContainsBit_quote
    (history : TheoryHistory)
    (sentenceCode : Nat) :
    theoryHistoryContainsBit history.quote sentenceCode =
      listContainsBit history.sentenceCodes sentenceCode := by
  rw [TheoryHistory.quote_eq_quoteNatList_sentenceCodes]
  unfold theoryHistoryContainsBit
  cases natExistsEqAddOfLe
      (quoteNatList_length_le history.sentenceCodes) with
  | intro extra equality =>
      calc
        natUnpairRight
            (theoryHistoryContainsRun
              (quoteNatList history.sentenceCodes)
              (natPair (quoteNatList history.sentenceCodes) 0)
              sentenceCode) =
            natUnpairRight
              (theoryHistoryContainsRun
                (history.sentenceCodes.length + extra)
                (natPair (quoteNatList history.sentenceCodes) 0)
                sentenceCode) := by rw [equality]
        _ = listContainsBit history.sentenceCodes sentenceCode := by
          rw [theoryHistoryContainsRun_add,
            theoryHistoryContainsRun_quote_exact,
            theoryHistoryContainsRun_completed, natUnpairRight_pair]
          rfl

theorem theoryHistoryContainsBit_quoteNatList
    (values : List Nat)
    (target : Nat) :
    theoryHistoryContainsBit (quoteNatList values) target =
      listContainsBit values target := by
  unfold theoryHistoryContainsBit
  cases natExistsEqAddOfLe (quoteNatList_length_le values) with
  | intro extra equality =>
      calc
        natUnpairRight
            (theoryHistoryContainsRun (quoteNatList values)
              (natPair (quoteNatList values) 0) target) =
            natUnpairRight
              (theoryHistoryContainsRun (values.length + extra)
                (natPair (quoteNatList values) 0) target) := by rw [equality]
        _ = listContainsBit values target := by
          rw [theoryHistoryContainsRun_add,
            theoryHistoryContainsRun_quote_exact,
            theoryHistoryContainsRun_completed, natUnpairRight_pair]
          rfl

inductive ListCodeContains (target : Nat) : List Nat -> Type
  | here {head : Nat} {tail : List Nat} :
      head = target -> ListCodeContains target (head :: tail)
  | there {head : Nat} {tail : List Nat} :
      ListCodeContains target tail ->
      ListCodeContains target (head :: tail)

theorem listContainsFrom_one
    (values : List Nat)
    (target : Nat) :
    listContainsFrom values target 1 = 1 := by
  induction values with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      change listContainsFrom tail target
        (natOrBit 1 (natEqualBit head target)) = 1
      change listContainsFrom tail target 1 = 1
      exact inductionHypothesis

theorem listContainsFrom_of_contains
    {values : List Nat}
    {target found : Nat}
    (evidence : ListCodeContains target values) :
    listContainsFrom values target found = 1 := by
  induction evidence generalizing found with
  | here same =>
      cases same
      change listContainsFrom _ target
        (natOrBit found (natEqualBit target target)) = 1
      rw [(natEqualBit_eq_one_iff target target).mpr rfl]
      unfold natOrBit
      cases found <;> exact listContainsFrom_one _ target
  | there evidence inductionHypothesis =>
      change listContainsFrom _ target
        (natOrBit found (natEqualBit _ target)) = 1
      exact inductionHypothesis

def listContainsFrom_zero_positive_sound
    (values : List Nat) :
    (target : Nat) ->
    0 < listContainsFrom values target 0 ->
    ListCodeContains target values
  | target, accepted =>
      match values with
      | [] => (Nat.not_lt_zero 0 accepted).elim
      | head :: tail =>
          if same : head = target then
            ListCodeContains.here same
          else
            have unequalBit : natEqualBit head target = 0 := by
              cases bitValue : natEqualBit head target with
              | zero => rfl
              | succ rest =>
                  have positive : 0 < natEqualBit head target := by
                    rw [bitValue]
                    exact Nat.zero_lt_succ rest
                  exact (same ((natEqualBit_pos_iff _ _).mp positive)).elim
            have tailAccepted : 0 < listContainsFrom tail target 0 := by
              simpa [listContainsFrom, unequalBit, natOrBit] using accepted
            ListCodeContains.there
              (listContainsFrom_zero_positive_sound tail target tailAccepted)

def TheoryHistory.Contains.toCodeContains
    {history : TheoryHistory}
    {sentence : Sentence}
    (evidence : history.Contains sentence) :
    ListCodeContains sentence.quote history.sentenceCodes :=
  match evidence with
  | .newest => ListCodeContains.here rfl
  | .earlier earlierEvidence =>
      ListCodeContains.there earlierEvidence.toCodeContains

def TheoryHistory.containsOfCodeContains
    {history : TheoryHistory} :
    {sentenceCode : Nat} ->
    ListCodeContains sentenceCode history.sentenceCodes ->
    Sigma fun sentence : Sentence =>
      PSigma fun _membership : history.Contains sentence =>
        sentence.quote = sentenceCode
  | sentenceCode, evidence =>
      match history with
      | .root => nomatch evidence
      | .extend previous newest => by
          change ListCodeContains sentenceCode
            (newest.quote :: previous.sentenceCodes) at evidence
          cases evidence with
          | here sameCode =>
              exact Sigma.mk newest
                (PSigma.mk TheoryHistory.Contains.newest sameCode)
          | there earlier =>
              match previous.containsOfCodeContains earlier with
              | .mk sentence result =>
                  exact Sigma.mk sentence
                    (PSigma.mk result.1.preserve result.2)

theorem TheoryHistory.contains_implies_numeric
    {history : TheoryHistory}
    {sentence : Sentence}
    (evidence : history.Contains sentence) :
    PRFunction.theoryHistoryContains.run
        (NatVector.cons history.quote
          (NatVector.cons sentence.quote NatVector.nil)) = 1 := by
  rw [PRFunction.run_theoryHistoryContains,
    theoryHistoryContainsBit_quote]
  exact listContainsFrom_of_contains evidence.toCodeContains

def TheoryHistory.numeric_positive_implies_contains
    (history : TheoryHistory)
    (sentenceCode : Nat)
    (accepted : 0 < PRFunction.theoryHistoryContains.run
      (NatVector.cons history.quote
        (NatVector.cons sentenceCode NatVector.nil))) :
    Sigma fun sentence : Sentence =>
      PSigma fun _membership : history.Contains sentence =>
        sentence.quote = sentenceCode := by
  rw [PRFunction.run_theoryHistoryContains,
    theoryHistoryContainsBit_quote] at accepted
  exact history.containsOfCodeContains
    (listContainsFrom_zero_positive_sound
      history.sentenceCodes sentenceCode accepted)

def FormulaContext.memberOfCodeContains
    {bound : Nat}
    {context : FormulaContext bound} :
    {formula : ScopedFormula bound} ->
    ListCodeContains formula.raw.code context.rawCodes ->
    ContextMember formula context
  | formula, evidence =>
      match context with
      | .nil => nomatch evidence
      | .cons head tail => by
          change ListCodeContains formula.raw.code
            (head.raw.code :: tail.rawCodes) at evidence
          cases evidence with
          | here sameCode =>
              have same : formula = head :=
                ScopedFormula.eq_of_raw_eq
                  (RawFormula.code_injective sameCode.symm)
              exact Eq.mp
                (congrArg
                  (fun selected =>
                    ContextMember selected (FormulaContext.cons head tail))
                  same.symm)
                ContextMember.here
          | there earlier =>
              exact ContextMember.there
                (tail.memberOfCodeContains earlier)

def FormulaContext.numeric_positive_implies_member
    {bound : Nat}
    (context : FormulaContext bound)
    (formula : ScopedFormula bound)
    (accepted : 0 < PRFunction.theoryHistoryContains.run
      (NatVector.cons context.quote
        (NatVector.cons formula.raw.code NatVector.nil))) :
    ContextMember formula context := by
  rw [PRFunction.run_theoryHistoryContains,
    FormulaContext.quote_eq_quoteNatList_rawCodes,
    theoryHistoryContainsBit_quoteNatList] at accepted
  exact context.memberOfCodeContains
    (listContainsFrom_zero_positive_sound
      context.rawCodes formula.raw.code accepted)

/-! ## Generic bounded universal scan and context recognition -/

def prefixAllStep
    (predicate : Nat -> Nat -> Nat)
    (state parameter : Nat) : Nat :=
  let remaining := natUnpairLeft state
  let accepted := natUnpairRight state
  match remaining with
  | 0 => state
  | Nat.succ encoded =>
      let head := natUnpairLeft encoded
      let tail := natUnpairRight encoded
      natPair tail (natAndBit accepted (predicate parameter head))

def prefixAllRun
    (predicate : Nat -> Nat -> Nat) : Nat -> Nat -> Nat -> Nat
  | 0, state, _parameter => state
  | Nat.succ steps, state, parameter =>
      prefixAllRun predicate steps
        (prefixAllStep predicate state parameter) parameter

def prefixAllBit
    (predicate : Nat -> Nat -> Nat)
    (parameter code : Nat) : Nat :=
  natUnpairRight
    (prefixAllRun predicate code (natPair code 1) parameter)

def listAllFrom
    (predicate : Nat -> Nat -> Nat) : List Nat -> Nat -> Nat -> Nat
  | [], _parameter, accepted => accepted
  | head :: tail, parameter, accepted =>
      listAllFrom predicate tail parameter
        (natAndBit accepted (predicate parameter head))

inductive ListAll (property : Nat -> Prop) : List Nat -> Prop
  | nil : ListAll property []
  | cons {head : Nat} {tail : List Nat} :
      property head -> ListAll property tail ->
      ListAll property (head :: tail)

theorem listAllFrom_pos_iff
    (predicate : Nat -> Nat -> Nat)
    (values : List Nat)
    (parameter accepted : Nat) :
    0 < listAllFrom predicate values parameter accepted ↔
      0 < accepted ∧
      ListAll (fun code => 0 < predicate parameter code) values := by
  induction values generalizing accepted with
  | nil =>
      constructor
      · intro positive
        exact And.intro positive ListAll.nil
      · intro result
        exact result.1
  | cons head tail inductionHypothesis =>
      constructor
      · intro positive
        have result :=
          (inductionHypothesis
            (natAndBit accepted (predicate parameter head))).mp positive
        have headAndAccepted :=
          (natAndBit_pos_iff accepted (predicate parameter head)).mp result.1
        exact And.intro headAndAccepted.1
          (ListAll.cons headAndAccepted.2 result.2)
      · intro result
        cases result.2 with
        | cons headPositive tailPositive =>
            apply (inductionHypothesis
              (natAndBit accepted (predicate parameter head))).mpr
            exact And.intro
              ((natAndBit_pos_iff accepted
                (predicate parameter head)).mpr
                (And.intro result.1 headPositive))
              tailPositive

theorem prefixAllRun_quote_exact
    (predicate : Nat -> Nat -> Nat)
    (values : List Nat)
    (parameter accepted : Nat) :
    prefixAllRun predicate values.length
        (natPair (quoteNatList values) accepted) parameter =
      natPair 0 (listAllFrom predicate values parameter accepted) := by
  induction values generalizing accepted with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      simpa [prefixAllRun, prefixAllStep, quoteNatList,
        listAllFrom, natUnpairLeft_pair, natUnpairRight_pair] using
        inductionHypothesis
          (natAndBit accepted (predicate parameter head))

theorem prefixAllRun_completed
    (predicate : Nat -> Nat -> Nat)
    (steps accepted parameter : Nat) :
    prefixAllRun predicate steps (natPair 0 accepted) parameter =
      natPair 0 accepted := by
  induction steps with
  | zero => rfl
  | succ steps inductionHypothesis =>
      change prefixAllRun predicate steps
        (prefixAllStep predicate (natPair 0 accepted) parameter) parameter = _
      unfold prefixAllStep
      rw [natUnpairLeft_pair, natUnpairRight_pair]
      exact inductionHypothesis

theorem prefixAllRun_succ_right
    (predicate : Nat -> Nat -> Nat)
    (steps state parameter : Nat) :
    prefixAllRun predicate (Nat.succ steps) state parameter =
      prefixAllStep predicate
        (prefixAllRun predicate steps state parameter) parameter := by
  induction steps generalizing state with
  | zero => rfl
  | succ steps inductionHypothesis =>
      change prefixAllRun predicate steps
          (prefixAllStep predicate
            (prefixAllStep predicate state parameter) parameter) parameter =
        prefixAllStep predicate
          (prefixAllRun predicate steps
            (prefixAllStep predicate state parameter) parameter) parameter
      exact inductionHypothesis (prefixAllStep predicate state parameter)

theorem prefixAllBit_quote
    (predicate : Nat -> Nat -> Nat)
    (values : List Nat)
    (parameter : Nat) :
    prefixAllBit predicate parameter (quoteNatList values) =
      listAllFrom predicate values parameter 1 := by
  unfold prefixAllBit
  cases natExistsEqAddOfLe (quoteNatList_length_le values) with
  | intro extra equality =>
      have runAdd : forall first second state,
          prefixAllRun predicate (first + second) state parameter =
            prefixAllRun predicate second
              (prefixAllRun predicate first state parameter) parameter := by
        intro first second state
        induction first generalizing state with
        | zero =>
            rw [Nat.zero_add]
            rfl
        | succ first inductionHypothesis =>
            rw [Nat.succ_add]
            change prefixAllRun predicate (first + second)
              (prefixAllStep predicate state parameter) parameter = _
            exact inductionHypothesis (prefixAllStep predicate state parameter)
      calc
        natUnpairRight
            (prefixAllRun predicate (quoteNatList values)
              (natPair (quoteNatList values) 1) parameter) =
            natUnpairRight
              (prefixAllRun predicate (values.length + extra)
                (natPair (quoteNatList values) 1) parameter) := by rw [equality]
        _ = listAllFrom predicate values parameter 1 := by
          rw [runAdd, prefixAllRun_quote_exact,
            prefixAllRun_completed, natUnpairRight_pair]

def PRFunction.prefixAllIterationStep
    (predicate : PRFunction 2) : PRFunction 4 :=
  let previous := PRFunction.projection 4 1 historyIndexOne_lt_four
  let parameter := PRFunction.projection 4 3 historyIndexThree_lt_four
  let remaining := PRFunction.unaryIn PRFunction.unpairLeft previous
  let accepted := PRFunction.unaryIn PRFunction.unpairRight previous
  let encoded := PRFunction.unaryIn PRFunction.predecessor remaining
  let head := PRFunction.unaryIn PRFunction.unpairLeft encoded
  let tail := PRFunction.unaryIn PRFunction.unpairRight encoded
  let current := PRFunction.composition predicate
    (PRFunctionVector.cons parameter (PRFunctionVector.singleton head))
  let nextAccepted := PRFunction.binaryIn PRFunction.andBit accepted current
  let next := PRFunction.binaryIn PRFunction.pair tail nextAccepted
  PRFunction.select remaining previous next

def PRFunction.prefixAllRun
    (predicate : PRFunction 2) : PRFunction 3 :=
  PRFunction.primitiveRecursion
    (PRFunction.projection 2 0 historyIndexZero_lt_two)
    (PRFunction.prefixAllIterationStep predicate)

def PRFunction.prefixAll
    (predicate : PRFunction 2) : PRFunction 2 :=
  let parameter := PRFunction.projection 2 0 historyIndexZero_lt_two
  let code := PRFunction.projection 2 1 historyIndexOne_lt_two
  let initial := PRFunction.binaryIn PRFunction.pair code
    (PRFunction.constant 2 1)
  let finalState := PRFunction.composition (PRFunction.prefixAllRun predicate)
    (PRFunctionVector.cons code
      (PRFunctionVector.cons initial
        (PRFunctionVector.singleton parameter)))
  PRFunction.unaryIn PRFunction.unpairRight finalState

def PRFunction.isContextCode : PRFunction 2 :=
  PRFunction.prefixAll PRFunction.isScopedFormulaCode

@[simp] theorem PRFunction.run_prefixAllIterationStep
    (predicate : PRFunction 2)
    (counter previous state parameter : Nat) :
    (PRFunction.prefixAllIterationStep predicate).run
        (NatVector.cons counter
          (NatVector.cons previous
            (NatVector.cons state
              (NatVector.cons parameter NatVector.nil)))) =
      prefixAllStep
        (fun argument code => predicate.run
          (NatVector.cons argument (NatVector.cons code NatVector.nil)))
        previous parameter := by
  unfold PRFunction.prefixAllIterationStep prefixAllStep
  repeat first
    | rw [PRFunction.run_select]
    | rw [PRFunction.run_projection]
    | rw [NatVector.get_cons_zero]
    | rw [NatVector.get_cons_succ]
    | rw [PRFunction.run_unaryIn]
    | rw [PRFunction.run_binaryIn]
    | rw [PRFunction.run_composition]
    | rw [PRFunctionVector.run_cons]
    | rw [PRFunctionVector.run_singleton]
    | rw [PRFunction.run_unpairLeft]
    | rw [PRFunction.run_unpairRight]
    | rw [PRFunction.run_predecessor]
    | rw [PRFunction.run_andBit]
    | rw [PRFunction.run_pair]
  cases remaining : natUnpairLeft previous <;> rfl

theorem PRFunction.run_prefixAllRun
    (predicate : PRFunction 2)
    (steps state parameter : Nat) :
    (PRFunction.prefixAllRun predicate).run
        (NatVector.cons steps
          (NatVector.cons state (NatVector.cons parameter NatVector.nil))) =
      HeytingArithmetic.prefixAllRun
        (fun argument code => predicate.run
          (NatVector.cons argument (NatVector.cons code NatVector.nil)))
        steps state parameter := by
  induction steps with
  | zero => rfl
  | succ steps inductionHypothesis =>
      change (PRFunction.prefixAllIterationStep predicate).run
        (NatVector.cons steps
          (NatVector.cons
            ((PRFunction.prefixAllRun predicate).run
              (NatVector.cons steps
                (NatVector.cons state
                  (NatVector.cons parameter NatVector.nil))))
            (NatVector.cons state
              (NatVector.cons parameter NatVector.nil)))) = _
      rw [PRFunction.run_prefixAllIterationStep, inductionHypothesis]
      exact (prefixAllRun_succ_right
        (fun argument code => predicate.run
          (NatVector.cons argument (NatVector.cons code NatVector.nil)))
        steps state parameter).symm

@[simp] theorem PRFunction.run_prefixAll
    (predicate : PRFunction 2)
    (parameter code : Nat) :
    (PRFunction.prefixAll predicate).run
        (NatVector.cons parameter (NatVector.cons code NatVector.nil)) =
      prefixAllBit
        (fun argument syntaxCode => predicate.run
          (NatVector.cons argument
            (NatVector.cons syntaxCode NatVector.nil)))
        parameter code := by
  unfold PRFunction.prefixAll prefixAllBit
  repeat first
    | rw [PRFunction.run_unaryIn]
    | rw [PRFunction.run_binaryIn]
    | rw [PRFunction.run_composition]
    | rw [PRFunctionVector.run_cons]
    | rw [PRFunctionVector.run_singleton]
    | rw [PRFunction.run_projection]
    | rw [NatVector.get_cons_zero]
    | rw [NatVector.get_cons_succ]
    | rw [PRFunction.run_constant]
    | rw [PRFunction.run_pair]
    | rw [PRFunction.run_prefixAllRun]
    | rw [PRFunction.run_unpairRight]

theorem prefixAllRun_context_exact
    {bound : Nat}
    (context : FormulaContext bound) :
    prefixAllRun
        (fun argument formulaCode =>
          PRFunction.isScopedFormulaCode.run
            (NatVector.cons argument
              (NatVector.cons formulaCode NatVector.nil)))
        context.rawCodes.length (natPair context.quote 1) bound =
      natPair 0 1 := by
  have listExact :
      listAllFrom
          (fun argument formulaCode =>
            PRFunction.isScopedFormulaCode.run
              (NatVector.cons argument
                (NatVector.cons formulaCode NatVector.nil)))
          context.rawCodes bound 1 = 1 := by
    induction context with
    | nil => rfl
    | cons head tail inductionHypothesis =>
        change listAllFrom _ tail.rawCodes bound
          (natAndBit 1
            (PRFunction.isScopedFormulaCode.run
              (NatVector.cons bound
                (NatVector.cons head.raw.code NatVector.nil)))) = 1
        rw [PRFunction.isScopedFormulaCode_accepts]
        change listAllFrom _ tail.rawCodes bound 1 = 1
        exact inductionHypothesis
  calc
    prefixAllRun
        (fun argument formulaCode =>
          PRFunction.isScopedFormulaCode.run
            (NatVector.cons argument
              (NatVector.cons formulaCode NatVector.nil)))
        context.rawCodes.length (natPair context.quote 1) bound =
      natPair 0
        (listAllFrom
          (fun argument formulaCode =>
            PRFunction.isScopedFormulaCode.run
              (NatVector.cons argument
                (NatVector.cons formulaCode NatVector.nil)))
          context.rawCodes bound 1) := by
            rw [FormulaContext.quote_eq_quoteNatList_rawCodes,
              prefixAllRun_quote_exact]
    _ = natPair 0 1 := congrArg (natPair 0) listExact

theorem listAllFrom_context_exact
    {bound : Nat}
    (context : FormulaContext bound) :
    listAllFrom
        (fun argument formulaCode =>
          PRFunction.isScopedFormulaCode.run
            (NatVector.cons argument
              (NatVector.cons formulaCode NatVector.nil)))
        context.rawCodes bound 1 = 1 := by
  induction context with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      change listAllFrom _ tail.rawCodes bound
        (natAndBit 1
          (PRFunction.isScopedFormulaCode.run
            (NatVector.cons bound
              (NatVector.cons head.raw.code NatVector.nil)))) = 1
      rw [PRFunction.isScopedFormulaCode_accepts]
      change listAllFrom _ tail.rawCodes bound 1 = 1
      exact inductionHypothesis

theorem PRFunction.isContextCode_accepts
    {bound : Nat}
    (context : FormulaContext bound) :
    PRFunction.isContextCode.run
        (NatVector.cons bound
          (NatVector.cons context.quote NatVector.nil)) = 1 := by
  unfold PRFunction.isContextCode
  rw [PRFunction.run_prefixAll]
  rw [FormulaContext.quote_eq_quoteNatList_rawCodes,
    prefixAllBit_quote]
  exact listAllFrom_context_exact context

theorem PRFunction.isContextCode_positive_sound
    (bound code : Nat)
    (accepted : 0 < PRFunction.isContextCode.run
      (NatVector.cons bound (NatVector.cons code NatVector.nil))) :
    Exists fun context : FormulaContext bound => context.quote = code := by
  unfold PRFunction.isContextCode at accepted
  rw [PRFunction.run_prefixAll] at accepted
  cases decodeNatList_total code with
  | intro values decoded =>
      rw [← decoded.2, prefixAllBit_quote] at accepted
      have allScoped := (listAllFrom_pos_iff _ values bound 1).mp accepted |>.2
      have build : forall remaining : List Nat,
          ListAll
              (fun formulaCode =>
                0 < PRFunction.isScopedFormulaCode.run
                  (NatVector.cons bound
                    (NatVector.cons formulaCode NatVector.nil)))
              remaining ->
          Exists fun context : FormulaContext bound =>
            context.quote = quoteNatList remaining := by
        intro remaining evidence
        induction evidence with
        | nil => exact Exists.intro FormulaContext.nil rfl
        | @cons head tail headAccepted tailAccepted inductionHypothesis =>
            cases PRFunction.isScopedFormulaCode_positive_sound
                bound head headAccepted with
            | intro formula formulaCode =>
                cases inductionHypothesis with
                | intro context contextCode =>
                    exact Exists.intro
                      (FormulaContext.cons formula context) (by
                        rw [FormulaContext.quote, formulaCode, contextCode,
                          quoteNatList])
      cases build values allScoped with
      | intro context contextCode =>
          exact Exists.intro context (contextCode.trans decoded.2)

end HeytingArithmetic
end RelationalPerimeter

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.HeytingArithmetic.theoryHistoryContainsRun_add
#print axioms RelationalPerimeter.HeytingArithmetic.theoryHistoryContainsRun_quote_exact
#print axioms RelationalPerimeter.HeytingArithmetic.theoryHistoryContainsBit_quote
#print axioms RelationalPerimeter.HeytingArithmetic.listContainsFrom_of_contains
#print axioms RelationalPerimeter.HeytingArithmetic.TheoryHistory.Contains.toCodeContains
#print axioms RelationalPerimeter.HeytingArithmetic.prefixAllBit_quote
#print axioms RelationalPerimeter.HeytingArithmetic.listAllFrom_pos_iff
#print axioms RelationalPerimeter.HeytingArithmetic.prefixAllRun_context_exact
#print axioms RelationalPerimeter.HeytingArithmetic.listAllFrom_context_exact
#print axioms RelationalPerimeter.HeytingArithmetic.PRFunction.theoryHistoryContains
#print axioms RelationalPerimeter.HeytingArithmetic.TheoryHistory.contains_implies_numeric
#print axioms RelationalPerimeter.HeytingArithmetic.TheoryHistory.numeric_positive_implies_contains
#print axioms RelationalPerimeter.HeytingArithmetic.FormulaContext.numeric_positive_implies_member
#print axioms RelationalPerimeter.HeytingArithmetic.PRFunction.isContextCode
#print axioms RelationalPerimeter.HeytingArithmetic.PRFunction.isContextCode_accepts
#print axioms RelationalPerimeter.HeytingArithmetic.PRFunction.isContextCode_positive_sound
/- AXIOM_AUDIT_END -/
