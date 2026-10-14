import RelationalPerimeter.Constitution.HeytingArithmetic.ProofCalculus
import RelationalPerimeter.Constitution.HeytingArithmetic.ConstructiveBetaEncoding
import RelationalPerimeter.Constitution.HeytingArithmetic.PrimitiveRecursiveUnpair

/-!
# Positive coding and chronological linearization of object derivations

This file erases no rule information into a semantic predicate.  A proof is
linearized into finitely many explicitly tagged lines.  Every premise
reference is an earlier line number; concatenating premise archives therefore
requires a constructive rebasing operation.  The resulting line codes are
stored by the already certified finite beta encoder.
-/

namespace RelationalPerimeter
namespace HeytingArithmetic

/-! ## Numeric codes for finite lists -/

/-- Prefix coding of a finite list.  Zero is the empty list. -/
def quoteNatList : List Nat -> Nat
  | [] => 0
  | head :: tail => Nat.succ (natPair head (quoteNatList tail))

/-- Total decoder for prefix-coded finite lists. -/
def decodeNatListFuel : Nat -> Nat -> Option (List Nat)
  | 0, 0 => some []
  | 0, Nat.succ _encoded => none
  | Nat.succ _fuel, 0 => some []
  | Nat.succ fuel, Nat.succ encoded =>
      let components := natUnpair encoded
      return components.1 :: (← decodeNatListFuel fuel components.2)

def decodeNatList (code : Nat) : Option (List Nat) :=
  decodeNatListFuel code code

theorem decodeNatListFuel_quote
    (values : List Nat)
    (fuel : Nat)
    (bounded : quoteNatList values <= fuel) :
    decodeNatListFuel fuel (quoteNatList values) = some values := by
  induction values generalizing fuel with
  | nil =>
      cases fuel <;> rfl
  | cons head tail inductionHypothesis =>
      cases fuel with
      | zero => exact (Nat.not_succ_le_zero _ bounded).elim
      | succ fuel =>
          have tailBound : quoteNatList tail <= fuel := by
            have pairedBound : natPair head (quoteNatList tail) <= fuel :=
              Nat.le_of_succ_le_succ bounded
            exact Nat.le_trans
              (natPair_right_le head (quoteNatList tail)) pairedBound
          rw [quoteNatList, decodeNatListFuel, natUnpair_pair]
          rw [inductionHypothesis fuel tailBound]
          rfl

theorem decodeNatList_quote (values : List Nat) :
    decodeNatList (quoteNatList values) = some values :=
  decodeNatListFuel_quote values (quoteNatList values)
    (Nat.le_refl (quoteNatList values))

/-- Every natural is a canonical prefix-list code. -/
theorem decodeNatList_total (code : Nat) :
    Exists fun values : List Nat =>
      decodeNatList code = some values ∧ quoteNatList values = code := by
  induction code using Nat.strongRecOn with
  | ind code inductionHypothesis =>
      cases code with
      | zero => exact Exists.intro [] (And.intro rfl rfl)
      | succ encoded =>
          cases natPair_surjective encoded with
          | intro components decomposition =>
              cases components with
              | mk head tail =>
                  have tailEarlier : tail < Nat.succ encoded :=
                    Nat.lt_succ_of_le (by
                      rw [decomposition]
                      exact natPair_right_le head tail)
                  cases inductionHypothesis tail tailEarlier with
                  | intro values decoded =>
                      have tailBound :
                          quoteNatList values <= natPair head tail := by
                        rw [decoded.2]
                        exact natPair_right_le head tail
                      have decodedAtLarge :
                          decodeNatListFuel (natPair head tail)
                            (quoteNatList values) = some values :=
                        decodeNatListFuel_quote values
                          (natPair head tail) tailBound
                      rw [decoded.2] at decodedAtLarge
                      exact Exists.intro (head :: values) (And.intro (by
                        unfold decodeNatList
                        rw [decodeNatListFuel, decomposition,
                          natUnpair_pair]
                        rw [decodedAtLarge]
                        rfl)
                        (by
                          rw [quoteNatList, decoded.2, decomposition]))

/-! ## Context codes -/

def FormulaContext.quote {bound : Nat} : FormulaContext bound -> Nat
  | FormulaContext.nil => 0
  | FormulaContext.cons head tail =>
      Nat.succ (natPair head.raw.code tail.quote)

/-! ## Rule and line codes -/

inductive ProofRuleTag where
  | theoryAxiom
  | hypothesis
  | weaken
  | implicationIntroduction
  | implicationElimination
  | conjunctionIntroduction
  | conjunctionEliminationLeft
  | conjunctionEliminationRight
  | disjunctionIntroductionLeft
  | disjunctionIntroductionRight
  | disjunctionElimination
  | falsumElimination
  | universalIntroduction
  | universalElimination
  | existentialIntroduction
  | existentialElimination
  | equalityReflexivity
  | equalitySymmetry
  | equalityTransitivity
  | equalitySubstitution
  | liftVariables
  | freeInstantiation
  | doubleNegationElimination
deriving DecidableEq

def ProofRuleTag.code : ProofRuleTag -> Nat
  | ProofRuleTag.theoryAxiom => 0
  | ProofRuleTag.hypothesis => 1
  | ProofRuleTag.weaken => 2
  | ProofRuleTag.implicationIntroduction => 3
  | ProofRuleTag.implicationElimination => 4
  | ProofRuleTag.conjunctionIntroduction => 5
  | ProofRuleTag.conjunctionEliminationLeft => 6
  | ProofRuleTag.conjunctionEliminationRight => 7
  | ProofRuleTag.disjunctionIntroductionLeft => 8
  | ProofRuleTag.disjunctionIntroductionRight => 9
  | ProofRuleTag.disjunctionElimination => 10
  | ProofRuleTag.falsumElimination => 11
  | ProofRuleTag.universalIntroduction => 12
  | ProofRuleTag.universalElimination => 13
  | ProofRuleTag.existentialIntroduction => 14
  | ProofRuleTag.existentialElimination => 15
  | ProofRuleTag.equalityReflexivity => 16
  | ProofRuleTag.equalitySymmetry => 17
  | ProofRuleTag.equalityTransitivity => 18
  | ProofRuleTag.equalitySubstitution => 19
  | ProofRuleTag.liftVariables => 20
  | ProofRuleTag.freeInstantiation => 21
  | ProofRuleTag.doubleNegationElimination => 22

def decodeProofRuleTag : Nat -> Option ProofRuleTag
  | 0 => some ProofRuleTag.theoryAxiom
  | 1 => some ProofRuleTag.hypothesis
  | 2 => some ProofRuleTag.weaken
  | 3 => some ProofRuleTag.implicationIntroduction
  | 4 => some ProofRuleTag.implicationElimination
  | 5 => some ProofRuleTag.conjunctionIntroduction
  | 6 => some ProofRuleTag.conjunctionEliminationLeft
  | 7 => some ProofRuleTag.conjunctionEliminationRight
  | 8 => some ProofRuleTag.disjunctionIntroductionLeft
  | 9 => some ProofRuleTag.disjunctionIntroductionRight
  | 10 => some ProofRuleTag.disjunctionElimination
  | 11 => some ProofRuleTag.falsumElimination
  | 12 => some ProofRuleTag.universalIntroduction
  | 13 => some ProofRuleTag.universalElimination
  | 14 => some ProofRuleTag.existentialIntroduction
  | 15 => some ProofRuleTag.existentialElimination
  | 16 => some ProofRuleTag.equalityReflexivity
  | 17 => some ProofRuleTag.equalitySymmetry
  | 18 => some ProofRuleTag.equalityTransitivity
  | 19 => some ProofRuleTag.equalitySubstitution
  | 20 => some ProofRuleTag.liftVariables
  | 21 => some ProofRuleTag.freeInstantiation
  | 22 => some ProofRuleTag.doubleNegationElimination
  | _ => none

theorem decodeProofRuleTag_code (tag : ProofRuleTag) :
    decodeProofRuleTag tag.code = some tag := by
  cases tag <;> rfl

/-- A checker line contains only numeric syntax and backward references. -/
structure ProofLine where
  rule : ProofRuleTag
  bound : Nat
  contextCode : Nat
  conclusionCode : Nat
  premises : List Nat
  parameters : List Nat

def ProofLine.quote (line : ProofLine) : Nat :=
  natPair line.rule.code
    (natPair line.bound
      (natPair line.contextCode
        (natPair line.conclusionCode
          (natPair (quoteNatList line.premises)
            (quoteNatList line.parameters)))))

/-- Rebase only references; syntax codes and rule parameters are invariant. -/
def ProofLine.rebase (offset : Nat) (line : ProofLine) : ProofLine :=
  { line with premises := line.premises.map (fun index => offset + index) }

/-- Length preservation for maps, proved without the library theorem whose
    current dependency closure contains propositional extensionality. -/
theorem listLengthMapConstructive
    {alpha beta : Type}
    (transform : alpha -> beta)
    (values : List alpha) :
    (values.map transform).length = values.length := by
  induction values with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      change Nat.succ ((tail.map transform).length) =
        Nat.succ tail.length
      exact congrArg Nat.succ inductionHypothesis

private theorem proofNatZeroAddConstructive (right : Nat) :
    0 + right = right := by
  induction right with
  | zero => rfl
  | succ right inductionHypothesis =>
      change Nat.succ (0 + right) = Nat.succ right
      exact congrArg Nat.succ inductionHypothesis

private theorem proofNatSuccAddConstructive (left right : Nat) :
    Nat.succ left + right = Nat.succ (left + right) := by
  induction right with
  | zero => rfl
  | succ right inductionHypothesis =>
      change Nat.succ (Nat.succ left + right) =
        Nat.succ (Nat.succ (left + right))
      exact congrArg Nat.succ inductionHypothesis

/-- Length of append, rebuilt structurally for the same constructive audit. -/
theorem listLengthAppendConstructive
    {alpha : Type}
    (left right : List alpha) :
    (left ++ right).length = left.length + right.length := by
  induction left with
  | nil => exact (proofNatZeroAddConstructive right.length).symm
  | cons head tail inductionHypothesis =>
      exact (congrArg Nat.succ inductionHypothesis).trans
        (proofNatSuccAddConstructive tail.length right.length).symm

/-! ## Chronological archives -/

/-- A transparent finite archive, before its canonical numeric quotation. -/
structure ProofArchive where
  lines : List ProofLine

namespace ProofArchive

def empty : ProofArchive := { lines := [] }

def singleton (line : ProofLine) : ProofArchive := { lines := [line] }

def lineCount (archive : ProofArchive) : Nat := archive.lines.length

def rebase (offset : Nat) (archive : ProofArchive) : ProofArchive :=
  { lines := archive.lines.map (ProofLine.rebase offset) }

/-- Append a block after rebasing all of its internal references. -/
def appendRebased (earlier later : ProofArchive) : ProofArchive :=
  { lines := earlier.lines ++
      (later.rebase earlier.lineCount).lines }

/-- Close accumulated premise blocks by one new conclusion line. -/
def finish (premises : ProofArchive) (line : ProofLine) : ProofArchive :=
  { lines := premises.lines ++ [line] }

def lastIndex (archive : ProofArchive) : Nat := archive.lineCount.pred

/-- Convert line quotations to the indexed vector expected by beta encoding. -/
def lineCodeVector : (lines : List ProofLine) -> NatVector lines.length
  | [] => NatVector.nil
  | head :: tail => NatVector.cons head.quote (lineCodeVector tail)

def betaCoefficient (archive : ProofArchive) : Nat :=
  (lineCodeVector archive.lines).betaCoefficient

def betaDividend (archive : ProofArchive) : Nat :=
  (lineCodeVector archive.lines).betaDividend

/-- Numeric archive code: line count plus the canonical beta witness. -/
def quote (archive : ProofArchive) : Nat :=
  natPair archive.lineCount
    (natPair archive.betaDividend archive.betaCoefficient)

def lineCode
    (archive : ProofArchive)
    (index : Nat)
    (bounded : index < archive.lineCount) : Nat :=
  (lineCodeVector archive.lines).get index bounded

theorem betaLookup_lineCode
    (archive : ProofArchive)
    (index : Nat)
    (bounded : index < archive.lineCount) :
    betaComponent archive.betaDividend archive.betaCoefficient index =
      archive.lineCode index bounded := by
  unfold betaComponent betaDividend betaCoefficient lineCode
  exact constructiveRemainder_betaDividend
    (lineCodeVector archive.lines) bounded

theorem lineCount_rebase (archive : ProofArchive) (offset : Nat) :
    (archive.rebase offset).lineCount = archive.lineCount := by
  unfold rebase lineCount
  exact listLengthMapConstructive (ProofLine.rebase offset) archive.lines

theorem lineCount_appendRebased (earlier later : ProofArchive) :
    (earlier.appendRebased later).lineCount =
      earlier.lineCount + later.lineCount := by
  unfold appendRebased lineCount rebase
  rw [listLengthAppendConstructive]
  exact congrArg (earlier.lines.length + ·)
    (listLengthMapConstructive (ProofLine.rebase earlier.lines.length)
      later.lines)

theorem lineCount_finish (archive : ProofArchive) (line : ProofLine) :
    (archive.finish line).lineCount = Nat.succ archive.lineCount := by
  unfold finish lineCount
  exact (listLengthAppendConstructive archive.lines [line]).trans rfl

end ProofArchive

/-! ## Erasure of a typed derivation into chronological lines -/

def proofLine
    (rule : ProofRuleTag)
    (bound contextCode conclusionCode : Nat)
    (premises parameters : List Nat) : ProofLine :=
  { rule := rule
    bound := bound
    contextCode := contextCode
    conclusionCode := conclusionCode
    premises := premises
    parameters := parameters }

def unaryArchive
    (premise : ProofArchive)
    (line : Nat -> ProofLine) : ProofArchive :=
  premise.finish (line premise.lastIndex)

def binaryArchive
    (first second : ProofArchive)
    (line : Nat -> Nat -> ProofLine) : ProofArchive :=
  let combined := first.appendRebased second
  combined.finish (line first.lastIndex combined.lastIndex)

def ternaryArchive
    (first second third : ProofArchive)
    (line : Nat -> Nat -> Nat -> ProofLine) : ProofArchive :=
  let firstSecond := first.appendRebased second
  let combined := firstSecond.appendRebased third
  combined.finish
    (line first.lastIndex firstSecond.lastIndex combined.lastIndex)

def encodeDerivationWithAxiomParameters
    {mode : LogicMode}
    {theory : ArithmeticTheory}
    (axiomParameters :
      {bound : Nat} -> {formula : ScopedFormula bound} ->
        theory.Axiom bound formula -> List Nat)
    {bound : Nat}
    {context : FormulaContext bound}
    {conclusion : ScopedFormula bound}
    (proof : Derivation mode theory context conclusion) : ProofArchive :=
  let currentLine := fun rule premises parameters =>
    proofLine rule bound context.quote conclusion.raw.code premises parameters
  match proof with
  | .theoryAxiom witness =>
      ProofArchive.singleton
        (currentLine ProofRuleTag.theoryAxiom []
          (axiomParameters witness))
  | .hypothesis _member =>
      ProofArchive.singleton
        (currentLine ProofRuleTag.hypothesis [] [])
  | .weaken extra premise =>
      unaryArchive (encodeDerivationWithAxiomParameters axiomParameters premise) (fun reference =>
        currentLine ProofRuleTag.weaken [reference]
          [extra.raw.code])
  | .implicationIntroduction premise =>
      unaryArchive (encodeDerivationWithAxiomParameters axiomParameters premise) (fun reference =>
        currentLine ProofRuleTag.implicationIntroduction
          [reference] [])
  | .implicationElimination implication argument =>
      binaryArchive
        (encodeDerivationWithAxiomParameters axiomParameters implication)
        (encodeDerivationWithAxiomParameters axiomParameters argument)
        (fun first second =>
          currentLine ProofRuleTag.implicationElimination
            [first, second] [])
  | .conjunctionIntroduction left right =>
      binaryArchive
        (encodeDerivationWithAxiomParameters axiomParameters left)
        (encodeDerivationWithAxiomParameters axiomParameters right)
        (fun first second =>
          currentLine ProofRuleTag.conjunctionIntroduction
            [first, second] [])
  | .conjunctionEliminationLeft premise =>
      unaryArchive (encodeDerivationWithAxiomParameters axiomParameters premise) (fun reference =>
        currentLine ProofRuleTag.conjunctionEliminationLeft
          [reference] [])
  | .conjunctionEliminationRight premise =>
      unaryArchive (encodeDerivationWithAxiomParameters axiomParameters premise) (fun reference =>
        currentLine ProofRuleTag.conjunctionEliminationRight
          [reference] [])
  | .disjunctionIntroductionLeft premise =>
      unaryArchive (encodeDerivationWithAxiomParameters axiomParameters premise) (fun reference =>
        currentLine ProofRuleTag.disjunctionIntroductionLeft
          [reference] [])
  | .disjunctionIntroductionRight premise =>
      unaryArchive (encodeDerivationWithAxiomParameters axiomParameters premise) (fun reference =>
        currentLine ProofRuleTag.disjunctionIntroductionRight
          [reference] [])
  | .disjunctionElimination disjunction leftBranch rightBranch =>
      ternaryArchive
        (encodeDerivationWithAxiomParameters axiomParameters disjunction)
        (encodeDerivationWithAxiomParameters axiomParameters leftBranch)
        (encodeDerivationWithAxiomParameters axiomParameters rightBranch)
        (fun first second third =>
          currentLine ProofRuleTag.disjunctionElimination
            [first, second, third] [])
  | .falsumElimination premise =>
      unaryArchive (encodeDerivationWithAxiomParameters axiomParameters premise) (fun reference =>
        currentLine ProofRuleTag.falsumElimination
          [reference] [])
  | .universalIntroduction premise =>
      unaryArchive (encodeDerivationWithAxiomParameters axiomParameters premise) (fun reference =>
        currentLine ProofRuleTag.universalIntroduction
          [reference] [])
  | .universalElimination term premise =>
      unaryArchive (encodeDerivationWithAxiomParameters axiomParameters premise) (fun reference =>
        currentLine ProofRuleTag.universalElimination
          [reference] [term.raw.code])
  | .existentialIntroduction term premise =>
      unaryArchive (encodeDerivationWithAxiomParameters axiomParameters premise) (fun reference =>
        currentLine ProofRuleTag.existentialIntroduction
          [reference] [term.raw.code])
  | .existentialElimination existential branch =>
      binaryArchive
        (encodeDerivationWithAxiomParameters axiomParameters existential)
        (encodeDerivationWithAxiomParameters axiomParameters branch)
        (fun first second =>
          currentLine ProofRuleTag.existentialElimination
            [first, second] [])
  | .equalityReflexivity term =>
      ProofArchive.singleton
        (currentLine ProofRuleTag.equalityReflexivity []
          [term.raw.code])
  | .equalitySymmetry premise =>
      unaryArchive (encodeDerivationWithAxiomParameters axiomParameters premise) (fun reference =>
        currentLine ProofRuleTag.equalitySymmetry
          [reference] [])
  | .equalityTransitivity first second =>
      binaryArchive
        (encodeDerivationWithAxiomParameters axiomParameters first)
        (encodeDerivationWithAxiomParameters axiomParameters second)
        (fun firstReference secondReference =>
          currentLine ProofRuleTag.equalityTransitivity
            [firstReference, secondReference] [])
  | .equalitySubstitution body equality premise =>
      binaryArchive
        (encodeDerivationWithAxiomParameters axiomParameters equality)
        (encodeDerivationWithAxiomParameters axiomParameters premise)
        (fun first second =>
          currentLine ProofRuleTag.equalitySubstitution
            [first, second] [body.raw.code])
  | .liftVariables premise =>
      unaryArchive (encodeDerivationWithAxiomParameters axiomParameters premise) (fun reference =>
        currentLine ProofRuleTag.liftVariables
          [reference] [])
  | .freeInstantiation replacement premise =>
      unaryArchive (encodeDerivationWithAxiomParameters axiomParameters premise) (fun reference =>
        currentLine ProofRuleTag.freeInstantiation
          [reference] [replacement.raw.code])
  | .doubleNegationElimination _permission premise =>
      unaryArchive (encodeDerivationWithAxiomParameters axiomParameters premise) (fun reference =>
        currentLine ProofRuleTag.doubleNegationElimination
          [reference] [])

/-- Generic theories retain an explicit but empty postulate payload. -/
def encodeDerivation
    {mode : LogicMode}
    {theory : ArithmeticTheory}
    {bound : Nat}
    {context : FormulaContext bound}
    {conclusion : ScopedFormula bound}
    (proof : Derivation mode theory context conclusion) : ProofArchive :=
  encodeDerivationWithAxiomParameters (fun _witness => []) proof

/-- Canonical finite parameters for every standard arithmetic postulate. -/
def standardArithmeticAxiomParameters
    {bound : Nat}
    {formula : ScopedFormula bound} :
    StandardArithmeticAxiom formula -> List Nat
  | .successorNotZero term => [0, term.raw.code]
  | .successorInjective left right =>
      [1, left.raw.code, right.raw.code]
  | .addZero term => [2, term.raw.code]
  | .addSuccessor left right =>
      [3, left.raw.code, right.raw.code]
  | .multiplyZero term => [4, term.raw.code]
  | .multiplySuccessor left right =>
      [5, left.raw.code, right.raw.code]
  | .induction body => [6, body.raw.code]

/-- PA/HA archive encoding with reconstructible arithmetic postulate payloads. -/
def encodeStandardDerivation
    {mode : LogicMode}
    {bound : Nat}
    {context : FormulaContext bound}
    {conclusion : ScopedFormula bound}
    (proof :
      Derivation mode standardArithmeticTheory context conclusion) :
    ProofArchive :=
  encodeDerivationWithAxiomParameters
    standardArithmeticAxiomParameters proof

theorem encodeDerivation_lineCount_positive
    {mode : LogicMode}
    {theory : ArithmeticTheory}
    {bound : Nat}
    {context : FormulaContext bound}
    {conclusion : ScopedFormula bound}
    (proof : Derivation mode theory context conclusion) :
    0 < (encodeDerivation proof).lineCount := by
  cases proof <;>
    unfold encodeDerivation encodeDerivationWithAxiomParameters
      unaryArchive binaryArchive ternaryArchive <;>
    first
    | exact Nat.zero_lt_succ 0
    | rw [ProofArchive.lineCount_finish]
      exact Nat.zero_lt_succ _

end HeytingArithmetic
end RelationalPerimeter

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.HeytingArithmetic.decodeNatList_quote
#print axioms RelationalPerimeter.HeytingArithmetic.decodeNatList_total
#print axioms RelationalPerimeter.HeytingArithmetic.ProofArchive.quote
#print axioms RelationalPerimeter.HeytingArithmetic.ProofArchive.betaLookup_lineCode
#print axioms RelationalPerimeter.HeytingArithmetic.encodeDerivation
#print axioms RelationalPerimeter.HeytingArithmetic.standardArithmeticAxiomParameters
#print axioms RelationalPerimeter.HeytingArithmetic.encodeStandardDerivation
#print axioms RelationalPerimeter.HeytingArithmetic.encodeDerivation_lineCount_positive
/- AXIOM_AUDIT_END -/
