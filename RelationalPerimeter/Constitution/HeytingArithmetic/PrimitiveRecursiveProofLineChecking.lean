import RelationalPerimeter.Constitution.HeytingArithmetic.PrimitiveRecursiveArithmeticAxioms

/-!
# Primitive-recursive checker for all proof-line rules

The checker reads a line and its cited predecessors directly from the beta
archive.  Every rule among the twenty-three constructors of `Derivation` is
validated by exact equalities of scoped syntax codes.  References are required
to be strictly earlier than the current line.
-/

namespace RelationalPerimeter
namespace HeytingArithmetic

set_option maxRecDepth 8192
set_option maxHeartbeats 5000000

private theorem lineIndexZero_lt_three : 0 < 3 := Nat.zero_lt_succ 2
private theorem lineIndexOne_lt_three : 1 < 3 :=
  Nat.succ_lt_succ (Nat.zero_lt_succ 1)
private theorem lineIndexTwo_lt_three : 2 < 3 :=
  Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.zero_lt_succ 0))

/-! ## Context-polymorphic code expressions -/

def PRFunction.allBits
    {arity : Nat} : List (PRFunction arity) -> PRFunction arity
  | [] => PRFunction.constant arity 1
  | head :: tail => PRFunction.conjoin head (PRFunction.allBits tail)

def PRFunction.anyBits
    {arity : Nat} : List (PRFunction arity) -> PRFunction arity
  | [] => PRFunction.constant arity 0
  | head :: tail =>
      PRFunction.binaryIn PRFunction.orBit head (PRFunction.anyBits tail)

def PRFunction.sameIn
    {arity : Nat} (left right : PRFunction arity) : PRFunction arity :=
  PRFunction.binaryIn PRFunction.equalBit left right

def PRFunction.lessIn
    {arity : Nat} (left right : PRFunction arity) : PRFunction arity :=
  PRFunction.binaryIn PRFunction.lessBit left right

def PRFunction.lineAtIn
    {arity : Nat} (archive index : PRFunction arity) : PRFunction arity :=
  PRFunction.composition PRFunction.archiveLineCode
    (PRFunctionVector.cons archive (PRFunctionVector.singleton index))

def PRFunction.listEntryIn
    {arity : Nat} (listCode : PRFunction arity) (index : Nat) :
    PRFunction arity :=
  PRFunction.composition PRFunction.codedListEntry
    (PRFunctionVector.cons listCode
      (PRFunctionVector.singleton (PRFunction.constant arity index)))

def PRFunction.lineRuleIn {arity : Nat} (line : PRFunction arity) :
    PRFunction arity := PRFunction.unaryIn PRFunction.proofLineRule line
def PRFunction.lineBoundIn {arity : Nat} (line : PRFunction arity) :
    PRFunction arity := PRFunction.unaryIn PRFunction.proofLineBound line
def PRFunction.lineContextIn {arity : Nat} (line : PRFunction arity) :
    PRFunction arity := PRFunction.unaryIn PRFunction.proofLineContext line
def PRFunction.lineConclusionIn {arity : Nat} (line : PRFunction arity) :
    PRFunction arity := PRFunction.unaryIn PRFunction.proofLineConclusion line
def PRFunction.linePremisesIn {arity : Nat} (line : PRFunction arity) :
    PRFunction arity := PRFunction.unaryIn PRFunction.proofLinePremises line
def PRFunction.lineParametersIn {arity : Nat} (line : PRFunction arity) :
    PRFunction arity := PRFunction.unaryIn PRFunction.proofLineParameters line

def PRFunction.syntaxEncodedIn
    {arity : Nat} (code : PRFunction arity) : PRFunction arity :=
  PRFunction.unaryIn PRFunction.predecessor code
def PRFunction.syntaxTagIn
    {arity : Nat} (code : PRFunction arity) : PRFunction arity :=
  PRFunction.unaryIn PRFunction.unpairLeft
    (PRFunction.syntaxEncodedIn code)
def PRFunction.syntaxPayloadIn
    {arity : Nat} (code : PRFunction arity) : PRFunction arity :=
  PRFunction.unaryIn PRFunction.unpairRight
    (PRFunction.syntaxEncodedIn code)
def PRFunction.syntaxLeftIn
    {arity : Nat} (code : PRFunction arity) : PRFunction arity :=
  PRFunction.unaryIn PRFunction.unpairLeft
    (PRFunction.syntaxPayloadIn code)
def PRFunction.syntaxRightIn
    {arity : Nat} (code : PRFunction arity) : PRFunction arity :=
  PRFunction.unaryIn PRFunction.unpairRight
    (PRFunction.syntaxPayloadIn code)

def PRFunction.contextConsIn
    {arity : Nat} (head tail : PRFunction arity) : PRFunction arity :=
  PRFunction.binaryIn PRFunction.codedListCons head tail

def PRFunction.formulaEqualIn
    {arity : Nat} (left right : PRFunction arity) : PRFunction arity :=
  PRFunction.binaryIn PRFunction.formulaEqualCode left right
def PRFunction.formulaConjIn
    {arity : Nat} (left right : PRFunction arity) : PRFunction arity :=
  PRFunction.binaryIn PRFunction.formulaConjunctionCode left right
def PRFunction.formulaDisjIn
    {arity : Nat} (left right : PRFunction arity) : PRFunction arity :=
  PRFunction.binaryIn PRFunction.formulaDisjunctionCode left right
def PRFunction.formulaImplIn
    {arity : Nat} (left right : PRFunction arity) : PRFunction arity :=
  PRFunction.binaryIn PRFunction.formulaImplicationCode left right
def PRFunction.formulaAllIn
    {arity : Nat} (body : PRFunction arity) : PRFunction arity :=
  PRFunction.unaryIn PRFunction.formulaUniversalCode body
def PRFunction.formulaExIn
    {arity : Nat} (body : PRFunction arity) : PRFunction arity :=
  PRFunction.unaryIn PRFunction.formulaExistentialCode body

def PRFunction.instantiateFormulaIn
    {arity : Nat} (body term : PRFunction arity) : PRFunction arity :=
  PRFunction.composition PRFunction.machineInstantiateTerm
    (PRFunctionVector.cons body (PRFunctionVector.singleton term))
def PRFunction.raiseFormulaOneIn
    {arity : Nat} (formula : PRFunction arity) : PRFunction arity :=
  PRFunction.composition PRFunction.raiseFormulaCode
    (PRFunctionVector.cons formula
      (PRFunctionVector.singleton (PRFunction.constant arity 1)))
def PRFunction.raiseContextOneIn
    {arity : Nat} (context : PRFunction arity) : PRFunction arity :=
  PRFunction.composition PRFunction.raiseContextCode
    (PRFunctionVector.cons context
      (PRFunctionVector.singleton (PRFunction.constant arity 1)))
def PRFunction.instantiateContextIn
    {arity : Nat} (context term : PRFunction arity) : PRFunction arity :=
  PRFunction.composition PRFunction.instantiateContextTermCode
    (PRFunctionVector.cons context (PRFunctionVector.singleton term))

/-! ## Complete local checker -/

/-- The line-local well-formedness gate, separated from rule recognition so
downstream correctness proofs never have to unfold all twenty-three rules merely
to recover the current typed frame.  Inputs are
`(historyCode,archiveCode,lineIndex)`; the history component is intentionally
unused by this gate. -/
def PRFunction.checkProofLineFrame : PRFunction 3 :=
  let archive := PRFunction.projection 3 1 lineIndexOne_lt_three
  let index := PRFunction.projection 3 2 lineIndexTwo_lt_three
  let line := PRFunction.lineAtIn archive index
  let bound := PRFunction.lineBoundIn line
  let context := PRFunction.lineContextIn line
  let conclusion := PRFunction.lineConclusionIn line
  PRFunction.allBits [
    PRFunction.lessIn index
      (PRFunction.unaryIn PRFunction.archiveLineCount archive),
    PRFunction.composition PRFunction.isContextCode
      (PRFunctionVector.cons bound (PRFunctionVector.singleton context)),
    PRFunction.composition PRFunction.isScopedFormulaCode
      (PRFunctionVector.cons bound (PRFunctionVector.singleton conclusion))]

/-- The twenty-three rule bodies are stored as independent projections.  A
projection can reduce to one body without zeta-expanding all the others. -/
structure PRFunction.ProofLineRuleBodies : Type where
  theoryAxiom : PRFunction 3
  hypothesis : PRFunction 3
  weaken : PRFunction 3
  implicationIntroduction : PRFunction 3
  implicationElimination : PRFunction 3
  conjunctionIntroduction : PRFunction 3
  conjunctionEliminationLeft : PRFunction 3
  conjunctionEliminationRight : PRFunction 3
  disjunctionIntroductionLeft : PRFunction 3
  disjunctionIntroductionRight : PRFunction 3
  disjunctionElimination : PRFunction 3
  falsumElimination : PRFunction 3
  universalIntroduction : PRFunction 3
  universalElimination : PRFunction 3
  existentialIntroduction : PRFunction 3
  existentialElimination : PRFunction 3
  equalityReflexivity : PRFunction 3
  equalitySymmetry : PRFunction 3
  equalityTransitivity : PRFunction 3
  equalitySubstitution : PRFunction 3
  liftVariables : PRFunction 3
  freeInstantiation : PRFunction 3
  doubleNegationElimination : PRFunction 3

/-- Named components of a proof-line input.  Keeping these definitions separate
ensures that reducing one rule body unfolds only the components it actually
uses. -/
def PRFunction.proofCheckHistory : PRFunction 3 :=
  PRFunction.projection 3 0 lineIndexZero_lt_three

def PRFunction.proofCheckArchive : PRFunction 3 :=
  PRFunction.projection 3 1 lineIndexOne_lt_three

def PRFunction.proofCheckIndex : PRFunction 3 :=
  PRFunction.projection 3 2 lineIndexTwo_lt_three

def PRFunction.proofCheckLine : PRFunction 3 :=
  PRFunction.lineAtIn PRFunction.proofCheckArchive
    PRFunction.proofCheckIndex

def PRFunction.proofCheckBound : PRFunction 3 :=
  PRFunction.lineBoundIn PRFunction.proofCheckLine

def PRFunction.proofCheckContext : PRFunction 3 :=
  PRFunction.lineContextIn PRFunction.proofCheckLine

def PRFunction.proofCheckConclusion : PRFunction 3 :=
  PRFunction.lineConclusionIn PRFunction.proofCheckLine

def PRFunction.proofCheckPremises : PRFunction 3 :=
  PRFunction.linePremisesIn PRFunction.proofCheckLine

def PRFunction.proofCheckParameters : PRFunction 3 :=
  PRFunction.lineParametersIn PRFunction.proofCheckLine

def PRFunction.proofCheckReference (position : Nat) : PRFunction 3 :=
  PRFunction.listEntryIn PRFunction.proofCheckPremises position

def PRFunction.proofCheckParameter (position : Nat) : PRFunction 3 :=
  PRFunction.listEntryIn PRFunction.proofCheckParameters position

def PRFunction.proofCheckFirstRef : PRFunction 3 :=
  PRFunction.proofCheckReference 0

def PRFunction.proofCheckSecondRef : PRFunction 3 :=
  PRFunction.proofCheckReference 1

def PRFunction.proofCheckThirdRef : PRFunction 3 :=
  PRFunction.proofCheckReference 2

def PRFunction.proofCheckFirstLine : PRFunction 3 :=
  PRFunction.lineAtIn PRFunction.proofCheckArchive
    PRFunction.proofCheckFirstRef

def PRFunction.proofCheckSecondLine : PRFunction 3 :=
  PRFunction.lineAtIn PRFunction.proofCheckArchive
    PRFunction.proofCheckSecondRef

def PRFunction.proofCheckThirdLine : PRFunction 3 :=
  PRFunction.lineAtIn PRFunction.proofCheckArchive
    PRFunction.proofCheckThirdRef

def PRFunction.proofCheckFirstBound : PRFunction 3 :=
  PRFunction.lineBoundIn PRFunction.proofCheckFirstLine

def PRFunction.proofCheckSecondBound : PRFunction 3 :=
  PRFunction.lineBoundIn PRFunction.proofCheckSecondLine

def PRFunction.proofCheckThirdBound : PRFunction 3 :=
  PRFunction.lineBoundIn PRFunction.proofCheckThirdLine

def PRFunction.proofCheckFirstContext : PRFunction 3 :=
  PRFunction.lineContextIn PRFunction.proofCheckFirstLine

def PRFunction.proofCheckSecondContext : PRFunction 3 :=
  PRFunction.lineContextIn PRFunction.proofCheckSecondLine

def PRFunction.proofCheckThirdContext : PRFunction 3 :=
  PRFunction.lineContextIn PRFunction.proofCheckThirdLine

def PRFunction.proofCheckFirstConclusion : PRFunction 3 :=
  PRFunction.lineConclusionIn PRFunction.proofCheckFirstLine

def PRFunction.proofCheckSecondConclusion : PRFunction 3 :=
  PRFunction.lineConclusionIn PRFunction.proofCheckSecondLine

def PRFunction.proofCheckThirdConclusion : PRFunction 3 :=
  PRFunction.lineConclusionIn PRFunction.proofCheckThirdLine

def PRFunction.proofCheckEmpty : PRFunction 3 :=
  PRFunction.constant 3 0

def PRFunction.proofCheckSuccessorBound : PRFunction 3 :=
  PRFunction.unaryIn PRFunction.successor PRFunction.proofCheckBound

def PRFunction.proofCheckFalsum : PRFunction 3 :=
  PRFunction.falsumCode 3

def PRFunction.proofCheckSyntaxTagIs
    (formula : PRFunction 3) (expected : Nat) : PRFunction 3 :=
  PRFunction.sameIn (PRFunction.syntaxTagIn formula)
    (PRFunction.constant 3 expected)

def PRFunction.proofCheckUnaryPremises : PRFunction 3 :=
  PRFunction.sameIn PRFunction.proofCheckPremises
    (PRFunction.unaryIn PRFunction.codedListSingleton
      PRFunction.proofCheckFirstRef)

def PRFunction.proofCheckBinaryPremises : PRFunction 3 :=
  PRFunction.sameIn PRFunction.proofCheckPremises
    (PRFunction.binaryIn PRFunction.codedListPair
      PRFunction.proofCheckFirstRef PRFunction.proofCheckSecondRef)

def PRFunction.proofCheckTernaryPremises : PRFunction 3 :=
  PRFunction.sameIn PRFunction.proofCheckPremises
    (PRFunction.composition PRFunction.codedListTriple
      (PRFunctionVector.cons PRFunction.proofCheckFirstRef
        (PRFunctionVector.cons PRFunction.proofCheckSecondRef
          (PRFunctionVector.singleton PRFunction.proofCheckThirdRef))))

def PRFunction.proofCheckEmptyParameters : PRFunction 3 :=
  PRFunction.sameIn PRFunction.proofCheckParameters
    PRFunction.proofCheckEmpty

def PRFunction.proofCheckSingletonParameter
    (value : PRFunction 3) : PRFunction 3 :=
  PRFunction.sameIn PRFunction.proofCheckParameters
    (PRFunction.unaryIn PRFunction.codedListSingleton value)

def PRFunction.proofCheckUnaryChronological : PRFunction 3 :=
  PRFunction.allBits [PRFunction.proofCheckUnaryPremises,
    PRFunction.lessIn PRFunction.proofCheckFirstRef
      PRFunction.proofCheckIndex]

def PRFunction.proofCheckBinaryChronological : PRFunction 3 :=
  PRFunction.allBits [PRFunction.proofCheckBinaryPremises,
    PRFunction.lessIn PRFunction.proofCheckFirstRef
      PRFunction.proofCheckIndex,
    PRFunction.lessIn PRFunction.proofCheckSecondRef
      PRFunction.proofCheckIndex]

def PRFunction.proofCheckTernaryChronological : PRFunction 3 :=
  PRFunction.allBits [PRFunction.proofCheckTernaryPremises,
    PRFunction.lessIn PRFunction.proofCheckFirstRef
      PRFunction.proofCheckIndex,
    PRFunction.lessIn PRFunction.proofCheckSecondRef
      PRFunction.proofCheckIndex,
    PRFunction.lessIn PRFunction.proofCheckThirdRef
      PRFunction.proofCheckIndex]

def PRFunction.proofCheckSameFirstFrame : PRFunction 3 :=
  PRFunction.allBits [
    PRFunction.sameIn PRFunction.proofCheckFirstBound
      PRFunction.proofCheckBound,
    PRFunction.sameIn PRFunction.proofCheckFirstContext
      PRFunction.proofCheckContext]

def PRFunction.proofCheckSameSecondFrame : PRFunction 3 :=
  PRFunction.allBits [
    PRFunction.sameIn PRFunction.proofCheckSecondBound
      PRFunction.proofCheckBound,
    PRFunction.sameIn PRFunction.proofCheckSecondContext
      PRFunction.proofCheckContext]

/-! ## Independent rule bodies -/

def PRFunction.proofCheckTheoryAxiomBody : PRFunction 3 :=
  PRFunction.allBits [
    PRFunction.sameIn PRFunction.proofCheckPremises
      PRFunction.proofCheckEmpty,
    PRFunction.composition PRFunction.isHistoryAxiomCode
      (PRFunctionVector.cons PRFunction.proofCheckHistory
        (PRFunctionVector.cons PRFunction.proofCheckBound
          (PRFunctionVector.cons PRFunction.proofCheckConclusion
            (PRFunctionVector.singleton
              PRFunction.proofCheckParameters))))]

def PRFunction.proofCheckHypothesisBody : PRFunction 3 :=
  PRFunction.allBits [
    PRFunction.sameIn PRFunction.proofCheckPremises
      PRFunction.proofCheckEmpty,
    PRFunction.proofCheckEmptyParameters,
    PRFunction.composition PRFunction.theoryHistoryContains
      (PRFunctionVector.cons PRFunction.proofCheckContext
        (PRFunctionVector.singleton PRFunction.proofCheckConclusion))]

def PRFunction.proofCheckWeakenBody : PRFunction 3 :=
  let extra := PRFunction.proofCheckParameter 0
  PRFunction.allBits [PRFunction.proofCheckUnaryChronological,
    PRFunction.proofCheckSingletonParameter extra,
    PRFunction.sameIn PRFunction.proofCheckFirstBound
      PRFunction.proofCheckBound,
    PRFunction.sameIn PRFunction.proofCheckContext
      (PRFunction.contextConsIn extra PRFunction.proofCheckFirstContext),
    PRFunction.sameIn PRFunction.proofCheckConclusion
      PRFunction.proofCheckFirstConclusion,
    PRFunction.composition PRFunction.isScopedFormulaCode
      (PRFunctionVector.cons PRFunction.proofCheckBound
        (PRFunctionVector.singleton extra))]

def PRFunction.proofCheckImplicationIntroductionBody : PRFunction 3 :=
  let implicationLeft :=
    PRFunction.syntaxLeftIn PRFunction.proofCheckConclusion
  let implicationRight :=
    PRFunction.syntaxRightIn PRFunction.proofCheckConclusion
  PRFunction.allBits [PRFunction.proofCheckUnaryChronological,
    PRFunction.proofCheckEmptyParameters,
    PRFunction.proofCheckSyntaxTagIs PRFunction.proofCheckConclusion 4,
    PRFunction.sameIn PRFunction.proofCheckFirstBound
      PRFunction.proofCheckBound,
    PRFunction.sameIn PRFunction.proofCheckFirstContext
      (PRFunction.contextConsIn implicationLeft
        PRFunction.proofCheckContext),
    PRFunction.sameIn PRFunction.proofCheckFirstConclusion implicationRight]

def PRFunction.proofCheckImplicationEliminationBody : PRFunction 3 :=
  PRFunction.allBits [PRFunction.proofCheckBinaryChronological,
    PRFunction.proofCheckEmptyParameters,
    PRFunction.proofCheckSameFirstFrame,
    PRFunction.proofCheckSameSecondFrame,
    PRFunction.proofCheckSyntaxTagIs
      PRFunction.proofCheckFirstConclusion 4,
    PRFunction.sameIn
      (PRFunction.syntaxLeftIn PRFunction.proofCheckFirstConclusion)
      PRFunction.proofCheckSecondConclusion,
    PRFunction.sameIn
      (PRFunction.syntaxRightIn PRFunction.proofCheckFirstConclusion)
      PRFunction.proofCheckConclusion]

def PRFunction.proofCheckConjunctionIntroductionBody : PRFunction 3 :=
  PRFunction.allBits [PRFunction.proofCheckBinaryChronological,
    PRFunction.proofCheckEmptyParameters,
    PRFunction.proofCheckSameFirstFrame,
    PRFunction.proofCheckSameSecondFrame,
    PRFunction.sameIn PRFunction.proofCheckConclusion
      (PRFunction.formulaConjIn PRFunction.proofCheckFirstConclusion
        PRFunction.proofCheckSecondConclusion)]

def PRFunction.proofCheckConjunctionEliminationLeftBody : PRFunction 3 :=
  PRFunction.allBits [PRFunction.proofCheckUnaryChronological,
    PRFunction.proofCheckEmptyParameters,
    PRFunction.proofCheckSameFirstFrame,
    PRFunction.proofCheckSyntaxTagIs
      PRFunction.proofCheckFirstConclusion 2,
    PRFunction.sameIn PRFunction.proofCheckConclusion
      (PRFunction.syntaxLeftIn PRFunction.proofCheckFirstConclusion)]

def PRFunction.proofCheckConjunctionEliminationRightBody : PRFunction 3 :=
  PRFunction.allBits [PRFunction.proofCheckUnaryChronological,
    PRFunction.proofCheckEmptyParameters,
    PRFunction.proofCheckSameFirstFrame,
    PRFunction.proofCheckSyntaxTagIs
      PRFunction.proofCheckFirstConclusion 2,
    PRFunction.sameIn PRFunction.proofCheckConclusion
      (PRFunction.syntaxRightIn PRFunction.proofCheckFirstConclusion)]

def PRFunction.proofCheckDisjunctionIntroductionLeftBody : PRFunction 3 :=
  PRFunction.allBits [PRFunction.proofCheckUnaryChronological,
    PRFunction.proofCheckEmptyParameters,
    PRFunction.proofCheckSameFirstFrame,
    PRFunction.proofCheckSyntaxTagIs PRFunction.proofCheckConclusion 3,
    PRFunction.sameIn PRFunction.proofCheckFirstConclusion
      (PRFunction.syntaxLeftIn PRFunction.proofCheckConclusion)]

def PRFunction.proofCheckDisjunctionIntroductionRightBody : PRFunction 3 :=
  PRFunction.allBits [PRFunction.proofCheckUnaryChronological,
    PRFunction.proofCheckEmptyParameters,
    PRFunction.proofCheckSameFirstFrame,
    PRFunction.proofCheckSyntaxTagIs PRFunction.proofCheckConclusion 3,
    PRFunction.sameIn PRFunction.proofCheckFirstConclusion
      (PRFunction.syntaxRightIn PRFunction.proofCheckConclusion)]

def PRFunction.proofCheckDisjunctionEliminationBody : PRFunction 3 :=
  let disjunctionLeft :=
    PRFunction.syntaxLeftIn PRFunction.proofCheckFirstConclusion
  let disjunctionRight :=
    PRFunction.syntaxRightIn PRFunction.proofCheckFirstConclusion
  PRFunction.allBits [PRFunction.proofCheckTernaryChronological,
    PRFunction.proofCheckEmptyParameters,
    PRFunction.proofCheckSameFirstFrame,
    PRFunction.proofCheckSyntaxTagIs
      PRFunction.proofCheckFirstConclusion 3,
    PRFunction.sameIn PRFunction.proofCheckSecondBound
      PRFunction.proofCheckBound,
    PRFunction.sameIn PRFunction.proofCheckThirdBound
      PRFunction.proofCheckBound,
    PRFunction.sameIn PRFunction.proofCheckSecondContext
      (PRFunction.contextConsIn disjunctionLeft
        PRFunction.proofCheckContext),
    PRFunction.sameIn PRFunction.proofCheckThirdContext
      (PRFunction.contextConsIn disjunctionRight
        PRFunction.proofCheckContext),
    PRFunction.sameIn PRFunction.proofCheckSecondConclusion
      PRFunction.proofCheckConclusion,
    PRFunction.sameIn PRFunction.proofCheckThirdConclusion
      PRFunction.proofCheckConclusion]

def PRFunction.proofCheckFalsumEliminationBody : PRFunction 3 :=
  PRFunction.allBits [PRFunction.proofCheckUnaryChronological,
    PRFunction.proofCheckEmptyParameters,
    PRFunction.proofCheckSameFirstFrame,
    PRFunction.sameIn PRFunction.proofCheckFirstConclusion
      PRFunction.proofCheckFalsum]

def PRFunction.proofCheckUniversalIntroductionBody : PRFunction 3 :=
  let universalBody :=
    PRFunction.syntaxPayloadIn PRFunction.proofCheckConclusion
  PRFunction.allBits [PRFunction.proofCheckUnaryChronological,
    PRFunction.proofCheckEmptyParameters,
    PRFunction.proofCheckSyntaxTagIs PRFunction.proofCheckConclusion 5,
    PRFunction.sameIn PRFunction.proofCheckFirstBound
      PRFunction.proofCheckSuccessorBound,
    PRFunction.sameIn PRFunction.proofCheckFirstContext
      (PRFunction.raiseContextOneIn PRFunction.proofCheckContext),
    PRFunction.sameIn PRFunction.proofCheckFirstConclusion universalBody]

def PRFunction.proofCheckUniversalEliminationBody : PRFunction 3 :=
  let eliminationBody :=
    PRFunction.syntaxPayloadIn PRFunction.proofCheckFirstConclusion
  let quantifiedTerm := PRFunction.proofCheckParameter 0
  PRFunction.allBits [PRFunction.proofCheckUnaryChronological,
    PRFunction.proofCheckSingletonParameter quantifiedTerm,
    PRFunction.proofCheckSameFirstFrame,
    PRFunction.proofCheckSyntaxTagIs
      PRFunction.proofCheckFirstConclusion 5,
    PRFunction.composition PRFunction.isScopedTermCode
      (PRFunctionVector.cons PRFunction.proofCheckBound
        (PRFunctionVector.singleton quantifiedTerm)),
    PRFunction.sameIn PRFunction.proofCheckConclusion
      (PRFunction.instantiateFormulaIn eliminationBody quantifiedTerm)]

def PRFunction.proofCheckExistentialIntroductionBody : PRFunction 3 :=
  let existentialBody :=
    PRFunction.syntaxPayloadIn PRFunction.proofCheckConclusion
  let quantifiedTerm := PRFunction.proofCheckParameter 0
  PRFunction.allBits [PRFunction.proofCheckUnaryChronological,
    PRFunction.proofCheckSingletonParameter quantifiedTerm,
    PRFunction.proofCheckSameFirstFrame,
    PRFunction.proofCheckSyntaxTagIs PRFunction.proofCheckConclusion 6,
    PRFunction.composition PRFunction.isScopedTermCode
      (PRFunctionVector.cons PRFunction.proofCheckBound
        (PRFunctionVector.singleton quantifiedTerm)),
    PRFunction.sameIn PRFunction.proofCheckFirstConclusion
      (PRFunction.instantiateFormulaIn existentialBody quantifiedTerm)]

def PRFunction.proofCheckExistentialEliminationBody : PRFunction 3 :=
  let eliminatedBody :=
    PRFunction.syntaxPayloadIn PRFunction.proofCheckFirstConclusion
  PRFunction.allBits [PRFunction.proofCheckBinaryChronological,
    PRFunction.proofCheckEmptyParameters,
    PRFunction.proofCheckSameFirstFrame,
    PRFunction.proofCheckSyntaxTagIs
      PRFunction.proofCheckFirstConclusion 6,
    PRFunction.sameIn PRFunction.proofCheckSecondBound
      PRFunction.proofCheckSuccessorBound,
    PRFunction.sameIn PRFunction.proofCheckSecondContext
      (PRFunction.contextConsIn eliminatedBody
        (PRFunction.raiseContextOneIn PRFunction.proofCheckContext)),
    PRFunction.sameIn PRFunction.proofCheckSecondConclusion
      (PRFunction.raiseFormulaOneIn PRFunction.proofCheckConclusion)]

def PRFunction.proofCheckEqualityReflexivityBody : PRFunction 3 :=
  let reflexiveTerm := PRFunction.proofCheckParameter 0
  PRFunction.allBits [
    PRFunction.sameIn PRFunction.proofCheckPremises
      PRFunction.proofCheckEmpty,
    PRFunction.proofCheckSingletonParameter reflexiveTerm,
    PRFunction.composition PRFunction.isScopedTermCode
      (PRFunctionVector.cons PRFunction.proofCheckBound
        (PRFunctionVector.singleton reflexiveTerm)),
    PRFunction.sameIn PRFunction.proofCheckConclusion
      (PRFunction.formulaEqualIn reflexiveTerm reflexiveTerm)]

def PRFunction.proofCheckEqualitySymmetryBody : PRFunction 3 :=
  PRFunction.allBits [PRFunction.proofCheckUnaryChronological,
    PRFunction.proofCheckEmptyParameters,
    PRFunction.proofCheckSameFirstFrame,
    PRFunction.proofCheckSyntaxTagIs
      PRFunction.proofCheckFirstConclusion 1,
    PRFunction.proofCheckSyntaxTagIs PRFunction.proofCheckConclusion 1,
    PRFunction.sameIn
      (PRFunction.syntaxLeftIn PRFunction.proofCheckConclusion)
      (PRFunction.syntaxRightIn PRFunction.proofCheckFirstConclusion),
    PRFunction.sameIn
      (PRFunction.syntaxRightIn PRFunction.proofCheckConclusion)
      (PRFunction.syntaxLeftIn PRFunction.proofCheckFirstConclusion)]

def PRFunction.proofCheckEqualityTransitivityBody : PRFunction 3 :=
  let firstEqualityLeft :=
    PRFunction.syntaxLeftIn PRFunction.proofCheckFirstConclusion
  let firstEqualityMiddle :=
    PRFunction.syntaxRightIn PRFunction.proofCheckFirstConclusion
  let secondEqualityMiddle :=
    PRFunction.syntaxLeftIn PRFunction.proofCheckSecondConclusion
  let secondEqualityRight :=
    PRFunction.syntaxRightIn PRFunction.proofCheckSecondConclusion
  PRFunction.allBits [PRFunction.proofCheckBinaryChronological,
    PRFunction.proofCheckEmptyParameters,
    PRFunction.proofCheckSameFirstFrame,
    PRFunction.proofCheckSameSecondFrame,
    PRFunction.proofCheckSyntaxTagIs
      PRFunction.proofCheckFirstConclusion 1,
    PRFunction.proofCheckSyntaxTagIs
      PRFunction.proofCheckSecondConclusion 1,
    PRFunction.proofCheckSyntaxTagIs PRFunction.proofCheckConclusion 1,
    PRFunction.sameIn firstEqualityMiddle secondEqualityMiddle,
    PRFunction.sameIn
      (PRFunction.syntaxLeftIn PRFunction.proofCheckConclusion)
      firstEqualityLeft,
    PRFunction.sameIn
      (PRFunction.syntaxRightIn PRFunction.proofCheckConclusion)
      secondEqualityRight]

def PRFunction.proofCheckEqualitySubstitutionBody : PRFunction 3 :=
  let firstEqualityLeft :=
    PRFunction.syntaxLeftIn PRFunction.proofCheckFirstConclusion
  let firstEqualityMiddle :=
    PRFunction.syntaxRightIn PRFunction.proofCheckFirstConclusion
  let substitutionBody := PRFunction.proofCheckParameter 0
  PRFunction.allBits [PRFunction.proofCheckBinaryChronological,
    PRFunction.proofCheckSingletonParameter substitutionBody,
    PRFunction.proofCheckSameFirstFrame,
    PRFunction.proofCheckSameSecondFrame,
    PRFunction.proofCheckSyntaxTagIs
      PRFunction.proofCheckFirstConclusion 1,
    PRFunction.composition PRFunction.isScopedFormulaCode
      (PRFunctionVector.cons PRFunction.proofCheckSuccessorBound
        (PRFunctionVector.singleton substitutionBody)),
    PRFunction.sameIn PRFunction.proofCheckSecondConclusion
      (PRFunction.instantiateFormulaIn substitutionBody
        firstEqualityLeft),
    PRFunction.sameIn PRFunction.proofCheckConclusion
      (PRFunction.instantiateFormulaIn substitutionBody
        firstEqualityMiddle)]

def PRFunction.proofCheckLiftVariablesBody : PRFunction 3 :=
  PRFunction.allBits [PRFunction.proofCheckUnaryChronological,
    PRFunction.proofCheckEmptyParameters,
    PRFunction.sameIn PRFunction.proofCheckBound
      (PRFunction.unaryIn PRFunction.successor
        PRFunction.proofCheckFirstBound),
    PRFunction.sameIn PRFunction.proofCheckContext
      (PRFunction.raiseContextOneIn PRFunction.proofCheckFirstContext),
    PRFunction.sameIn PRFunction.proofCheckConclusion
      (PRFunction.raiseFormulaOneIn PRFunction.proofCheckFirstConclusion)]

def PRFunction.proofCheckFreeInstantiationBody : PRFunction 3 :=
  let freeTerm := PRFunction.proofCheckParameter 0
  PRFunction.allBits [PRFunction.proofCheckUnaryChronological,
    PRFunction.proofCheckSingletonParameter freeTerm,
    PRFunction.sameIn PRFunction.proofCheckFirstBound
      PRFunction.proofCheckSuccessorBound,
    PRFunction.composition PRFunction.isScopedTermCode
      (PRFunctionVector.cons PRFunction.proofCheckBound
        (PRFunctionVector.singleton freeTerm)),
    PRFunction.sameIn PRFunction.proofCheckContext
      (PRFunction.instantiateContextIn
        PRFunction.proofCheckFirstContext freeTerm),
    PRFunction.sameIn PRFunction.proofCheckConclusion
      (PRFunction.instantiateFormulaIn
        PRFunction.proofCheckFirstConclusion freeTerm)]

def PRFunction.proofCheckDoubleNegationEliminationBody : PRFunction 3 :=
  let negConclusion :=
    PRFunction.formulaImplIn PRFunction.proofCheckConclusion
      PRFunction.proofCheckFalsum
  let doubleNegConclusion :=
    PRFunction.formulaImplIn negConclusion PRFunction.proofCheckFalsum
  PRFunction.allBits [PRFunction.proofCheckUnaryChronological,
    PRFunction.proofCheckEmptyParameters,
    PRFunction.proofCheckSameFirstFrame,
    PRFunction.sameIn PRFunction.proofCheckFirstConclusion
      doubleNegConclusion]

/-- The independent rule bodies packaged for numeric selection. -/
def PRFunction.checkProofLineRuleBodies : PRFunction.ProofLineRuleBodies :=
  { theoryAxiom := PRFunction.proofCheckTheoryAxiomBody
    hypothesis := PRFunction.proofCheckHypothesisBody
    weaken := PRFunction.proofCheckWeakenBody
    implicationIntroduction :=
      PRFunction.proofCheckImplicationIntroductionBody
    implicationElimination :=
      PRFunction.proofCheckImplicationEliminationBody
    conjunctionIntroduction :=
      PRFunction.proofCheckConjunctionIntroductionBody
    conjunctionEliminationLeft :=
      PRFunction.proofCheckConjunctionEliminationLeftBody
    conjunctionEliminationRight :=
      PRFunction.proofCheckConjunctionEliminationRightBody
    disjunctionIntroductionLeft :=
      PRFunction.proofCheckDisjunctionIntroductionLeftBody
    disjunctionIntroductionRight :=
      PRFunction.proofCheckDisjunctionIntroductionRightBody
    disjunctionElimination :=
      PRFunction.proofCheckDisjunctionEliminationBody
    falsumElimination := PRFunction.proofCheckFalsumEliminationBody
    universalIntroduction :=
      PRFunction.proofCheckUniversalIntroductionBody
    universalElimination :=
      PRFunction.proofCheckUniversalEliminationBody
    existentialIntroduction :=
      PRFunction.proofCheckExistentialIntroductionBody
    existentialElimination :=
      PRFunction.proofCheckExistentialEliminationBody
    equalityReflexivity := PRFunction.proofCheckEqualityReflexivityBody
    equalitySymmetry := PRFunction.proofCheckEqualitySymmetryBody
    equalityTransitivity := PRFunction.proofCheckEqualityTransitivityBody
    equalitySubstitution := PRFunction.proofCheckEqualitySubstitutionBody
    liftVariables := PRFunction.proofCheckLiftVariablesBody
    freeInstantiation := PRFunction.proofCheckFreeInstantiationBody
    doubleNegationElimination :=
      PRFunction.proofCheckDoubleNegationEliminationBody }

/-- The body of one rule check, with its numeric tag guard factored out. -/
def PRFunction.checkProofLineRuleBody (expected : Nat) : PRFunction 3 :=
  match expected with
  | 0 => PRFunction.checkProofLineRuleBodies.theoryAxiom
  | 1 => PRFunction.checkProofLineRuleBodies.hypothesis
  | 2 => PRFunction.checkProofLineRuleBodies.weaken
  | 3 => PRFunction.checkProofLineRuleBodies.implicationIntroduction
  | 4 => PRFunction.checkProofLineRuleBodies.implicationElimination
  | 5 => PRFunction.checkProofLineRuleBodies.conjunctionIntroduction
  | 6 => PRFunction.checkProofLineRuleBodies.conjunctionEliminationLeft
  | 7 => PRFunction.checkProofLineRuleBodies.conjunctionEliminationRight
  | 8 => PRFunction.checkProofLineRuleBodies.disjunctionIntroductionLeft
  | 9 => PRFunction.checkProofLineRuleBodies.disjunctionIntroductionRight
  | 10 => PRFunction.checkProofLineRuleBodies.disjunctionElimination
  | 11 => PRFunction.checkProofLineRuleBodies.falsumElimination
  | 12 => PRFunction.checkProofLineRuleBodies.universalIntroduction
  | 13 => PRFunction.checkProofLineRuleBodies.universalElimination
  | 14 => PRFunction.checkProofLineRuleBodies.existentialIntroduction
  | 15 => PRFunction.checkProofLineRuleBodies.existentialElimination
  | 16 => PRFunction.checkProofLineRuleBodies.equalityReflexivity
  | 17 => PRFunction.checkProofLineRuleBodies.equalitySymmetry
  | 18 => PRFunction.checkProofLineRuleBodies.equalityTransitivity
  | 19 => PRFunction.checkProofLineRuleBodies.equalitySubstitution
  | 20 => PRFunction.checkProofLineRuleBodies.liftVariables
  | 21 => PRFunction.checkProofLineRuleBodies.freeInstantiation
  | 22 => PRFunction.checkProofLineRuleBodies.doubleNegationElimination
  | _ => PRFunction.constant 3 0

/-- The tag read from the current encoded line equals the expected rule. -/
def PRFunction.checkProofLineRuleTag (expected : Nat) : PRFunction 3 :=
  let archive := PRFunction.projection 3 1 lineIndexOne_lt_three
  let index := PRFunction.projection 3 2 lineIndexTwo_lt_three
  let line := PRFunction.lineAtIn archive index
  PRFunction.sameIn (PRFunction.lineRuleIn line)
    (PRFunction.constant 3 expected)

/-- One guarded rule checker. -/
def PRFunction.checkProofLineRuleCheck (expected : Nat) : PRFunction 3 :=
  PRFunction.conjoin (PRFunction.checkProofLineRuleTag expected)
    (PRFunction.checkProofLineRuleBody expected)

/-- A guarded rule check evaluates its common tag projection once and leaves
the selected rule body opaque. -/
@[simp] theorem PRFunction.run_checkProofLineRuleCheck
    (expected historyCode archiveCode lineIndex : Nat) :
    (PRFunction.checkProofLineRuleCheck expected).run
        (NatVector.cons historyCode
          (NatVector.cons archiveCode
            (NatVector.cons lineIndex NatVector.nil))) =
      natAndBit
        (natEqualBit
          (PRFunction.proofLineRule.run
            (NatVector.cons
              (PRFunction.archiveLineCode.run
                (NatVector.cons archiveCode
                  (NatVector.cons lineIndex NatVector.nil)))
              NatVector.nil))
          expected)
        ((PRFunction.checkProofLineRuleBody expected).run
          (NatVector.cons historyCode
            (NatVector.cons archiveCode
              (NatVector.cons lineIndex NatVector.nil)))) := by
  unfold PRFunction.checkProofLineRuleCheck
    PRFunction.checkProofLineRuleTag PRFunction.sameIn
    PRFunction.lineRuleIn PRFunction.lineAtIn
  repeat first
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
    | rw [PRFunction.run_equalBit]

/-- Recursive dispatcher over a finite list of numeric rule tags. -/
def PRFunction.checkProofLineRuleChecks :
    List Nat -> PRFunction 3
  | [] => PRFunction.constant 3 0
  | expected :: tail =>
      PRFunction.binaryIn PRFunction.orBit
        (PRFunction.checkProofLineRuleCheck expected)
        (PRFunction.checkProofLineRuleChecks tail)

/-- Descending list of every tag strictly below a bound. -/
def intuitionisticRuleTags : Nat -> List Nat
  | 0 => []
  | Nat.succ bound => bound :: intuitionisticRuleTags bound

/-- Exactly the twenty-two rules admitted by the intuitionistic calculus. -/
def intuitionisticProofRuleTags : List Nat :=
  intuitionisticRuleTags 22

/-- Inputs are `(historyCode,archiveCode,lineIndex)`. -/
def PRFunction.checkProofLineRules : PRFunction 3 :=
  PRFunction.checkProofLineRuleChecks
    intuitionisticProofRuleTags

/-- Canonical input vector for the local proof checker. -/
def proofCheckInputs
    (historyCode archiveCode lineIndex : Nat) : NatVector 3 :=
  NatVector.cons historyCode
    (NatVector.cons archiveCode
      (NatVector.cons lineIndex NatVector.nil))

/-- Numeric rule tag read from the selected archive line. -/
def proofCheckRuleValue (archiveCode lineIndex : Nat) : Nat :=
  PRFunction.proofLineRule.run
    (NatVector.cons
      (PRFunction.archiveLineCode.run
        (NatVector.cons archiveCode
          (NatVector.cons lineIndex NatVector.nil)))
      NatVector.nil)

@[simp] theorem PRFunction.run_checkProofLineRuleCheck_inputs
    (expected historyCode archiveCode lineIndex : Nat) :
    (PRFunction.checkProofLineRuleCheck expected).run
        (proofCheckInputs historyCode archiveCode lineIndex) =
      natAndBit
        (natEqualBit (proofCheckRuleValue archiveCode lineIndex) expected)
        ((PRFunction.checkProofLineRuleBody expected).run
          (proofCheckInputs historyCode archiveCode lineIndex)) := by
  unfold proofCheckInputs proofCheckRuleValue
  exact PRFunction.run_checkProofLineRuleCheck
    expected historyCode archiveCode lineIndex

/-- Positive alternatives corresponding exactly to a finite dispatcher. -/
def proofCheckRuleAlternatives
    (historyCode archiveCode lineIndex : Nat) :
    List Nat -> Prop
  | [] => False
  | expected :: tail =>
      (proofCheckRuleValue archiveCode lineIndex = expected ∧
        0 < (PRFunction.checkProofLineRuleBody expected).run
          (proofCheckInputs historyCode archiveCode lineIndex)) ∨
      proofCheckRuleAlternatives historyCode archiveCode lineIndex tail

/-- Any accepted alternative whose observed tag is `expected` yields the body
for `expected`; no bound or decidability hypothesis is required. -/
theorem proofCheckRuleAlternatives_body_of_tag
    (expected historyCode archiveCode lineIndex : Nat)
    (expectedRules : List Nat)
    (tagExact :
      proofCheckRuleValue archiveCode lineIndex = expected)
    (accepted :
      proofCheckRuleAlternatives historyCode archiveCode lineIndex
        expectedRules) :
    0 < (PRFunction.checkProofLineRuleBody expected).run
      (proofCheckInputs historyCode archiveCode lineIndex) := by
  induction expectedRules with
  | nil =>
      unfold proofCheckRuleAlternatives at accepted
      exact accepted.elim
  | cons head tail inductionHypothesis =>
      unfold proofCheckRuleAlternatives at accepted
      cases accepted with
      | inl current =>
          have sameTag : head = expected :=
            current.1.symm.trans tagExact
          cases sameTag
          exact current.2
      | inr later =>
          exact inductionHypothesis later

/-- Constructive positive semantics of every finite rule dispatcher. -/
theorem PRFunction.checkProofLineRuleChecks_positive_iff
    (expectedRules : List Nat)
    (historyCode archiveCode lineIndex : Nat) :
    0 < (PRFunction.checkProofLineRuleChecks expectedRules).run
        (proofCheckInputs historyCode archiveCode lineIndex) ↔
      proofCheckRuleAlternatives historyCode archiveCode lineIndex
        expectedRules := by
  induction expectedRules with
  | nil =>
      unfold PRFunction.checkProofLineRuleChecks
        proofCheckRuleAlternatives proofCheckInputs
      rw [PRFunction.run_constant]
      constructor
      · intro impossible
        exact (Nat.not_lt_zero 0 impossible).elim
      · intro impossible
        exact impossible.elim
  | cons expected tail inductionHypothesis =>
      unfold PRFunction.checkProofLineRuleChecks
        proofCheckRuleAlternatives
      rw [PRFunction.run_binaryIn, PRFunction.run_orBit]
      constructor
      · intro positive
        cases (natOrBit_pos_iff _ _).mp positive with
        | inl headPositive =>
            left
            rw [PRFunction.run_checkProofLineRuleCheck_inputs] at headPositive
            have guarded := (natAndBit_pos_iff _ _).mp headPositive
            exact And.intro
              ((natEqualBit_pos_iff _ _).mp guarded.1)
              guarded.2
        | inr tailPositive =>
            exact Or.inr (inductionHypothesis.mp tailPositive)
      · intro alternative
        apply (natOrBit_pos_iff _ _).mpr
        cases alternative with
        | inl head =>
            left
            rw [PRFunction.run_checkProofLineRuleCheck_inputs]
            apply (natAndBit_pos_iff _ _).mpr
            exact And.intro
              ((natEqualBit_pos_iff _ _).mpr head.1)
              head.2
        | inr tailAlternative =>
            exact Or.inr (inductionHypothesis.mpr tailAlternative)

/-- Exact positive semantics of the intuitionistic rule dispatcher. -/
theorem PRFunction.checkProofLineRules_positive_iff
    (historyCode archiveCode lineIndex : Nat) :
    0 < PRFunction.checkProofLineRules.run
        (proofCheckInputs historyCode archiveCode lineIndex) ↔
      proofCheckRuleAlternatives historyCode archiveCode lineIndex
        intuitionisticProofRuleTags := by
  unfold PRFunction.checkProofLineRules
  exact PRFunction.checkProofLineRuleChecks_positive_iff
    _ historyCode archiveCode lineIndex

/-- Every accepted dispatcher branch identifies the line tag with an element
of the explicitly supported intuitionistic rule list. -/
theorem proofCheckRuleAlternatives_tag_mem
    (historyCode archiveCode lineIndex : Nat)
    (expectedRules : List Nat)
    (accepted : proofCheckRuleAlternatives historyCode archiveCode lineIndex
      expectedRules) :
    proofCheckRuleValue archiveCode lineIndex ∈
      expectedRules := by
  induction expectedRules with
  | nil => exact accepted.elim
  | cons expected tail inductionHypothesis =>
      cases accepted with
      | inl current =>
          rw [current.1]
          exact List.Mem.head tail
      | inr later =>
          exact List.Mem.tail expected (inductionHypothesis later)

/-- Membership in the generated tag list carries the strict numeric bound. -/
theorem intuitionisticRuleTags_lt
    {value bound : Nat}
    (member : value ∈ intuitionisticRuleTags bound) : value < bound := by
  induction bound with
  | zero => cases member
  | succ bound inductionHypothesis =>
      cases member with
      | head => exact Nat.lt_succ_self _
      | tail _ later =>
          exact Nat.lt_succ_of_lt (inductionHypothesis later)

/-- Strict self-comparison is constructively impossible. -/
theorem natLtIrreflexiveConstructive
    (value : Nat) : value < value → False := by
  induction value with
  | zero =>
      intro impossible
      exact (Nat.not_lt_zero 0 impossible).elim
  | succ value inductionHypothesis =>
      intro impossible
      exact inductionHypothesis (Nat.lt_of_succ_lt_succ impossible)

/-- The classical double-negation-elimination tag is absent from the HA
dispatcher and is therefore rejected before any rule body can be accepted. -/
theorem PRFunction.checkProofLineRules_rejects_doubleNegationTag
    (historyCode archiveCode lineIndex : Nat)
    (tagExact :
      proofCheckRuleValue archiveCode lineIndex = 22) :
    PRFunction.checkProofLineRules.run
        (proofCheckInputs historyCode archiveCode lineIndex) = 0 := by
  cases resultExact : PRFunction.checkProofLineRules.run
      (proofCheckInputs historyCode archiveCode lineIndex) with
  | zero => rfl
  | succ result =>
      have positive : 0 < PRFunction.checkProofLineRules.run
          (proofCheckInputs historyCode archiveCode lineIndex) :=
        Eq.mp (congrArg (fun value => 0 < value) resultExact.symm)
          (Nat.zero_lt_succ result)
      have alternatives :=
        (PRFunction.checkProofLineRules_positive_iff
          historyCode archiveCode lineIndex).mp positive
      have member := proofCheckRuleAlternatives_tag_mem
        historyCode archiveCode lineIndex
        intuitionisticProofRuleTags
        alternatives
      have observedLt :
          proofCheckRuleValue archiveCode lineIndex < 22 := by
        exact intuitionisticRuleTags_lt member
      have selfLt : 22 < 22 := tagExact ▸ observedLt
      exact (natLtIrreflexiveConstructive 22 selfLt).elim

/-- The complete local checker is the positive conjunction of the typed-frame
gate and the rule-recognition gate. -/
def PRFunction.checkProofLine : PRFunction 3 :=
  PRFunction.conjoin PRFunction.checkProofLineFrame
    PRFunction.checkProofLineRules

end HeytingArithmetic
end RelationalPerimeter

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.HeytingArithmetic.PRFunction.allBits
#print axioms RelationalPerimeter.HeytingArithmetic.PRFunction.checkProofLineFrame
#print axioms RelationalPerimeter.HeytingArithmetic.PRFunction.checkProofLineRuleBodies
#print axioms RelationalPerimeter.HeytingArithmetic.PRFunction.checkProofLineRuleBody
#print axioms RelationalPerimeter.HeytingArithmetic.PRFunction.checkProofLineRuleCheck
#print axioms RelationalPerimeter.HeytingArithmetic.PRFunction.run_checkProofLineRuleCheck
#print axioms RelationalPerimeter.HeytingArithmetic.intuitionisticProofRuleTags
#print axioms RelationalPerimeter.HeytingArithmetic.PRFunction.checkProofLineRules
#print axioms RelationalPerimeter.HeytingArithmetic.proofCheckRuleAlternatives_body_of_tag
#print axioms RelationalPerimeter.HeytingArithmetic.PRFunction.checkProofLineRules_positive_iff
#print axioms RelationalPerimeter.HeytingArithmetic.proofCheckRuleAlternatives_tag_mem
#print axioms RelationalPerimeter.HeytingArithmetic.intuitionisticRuleTags_lt
#print axioms RelationalPerimeter.HeytingArithmetic.natLtIrreflexiveConstructive
#print axioms RelationalPerimeter.HeytingArithmetic.PRFunction.checkProofLineRules_rejects_doubleNegationTag
#print axioms RelationalPerimeter.HeytingArithmetic.PRFunction.checkProofLine
/- AXIOM_AUDIT_END -/
