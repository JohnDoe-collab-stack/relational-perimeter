import RelationalPerimeter.Constitution.HeytingArithmetic.PrimitiveRecursiveProofSoundness
import RelationalPerimeter.Constitution.HeytingArithmetic.ProofChronology

/-!
# Structural core of primitive-recursive proof completeness

The canonical encoding of every typed history derivation is a nonempty
archive ending in one line whose rule-independent frame is exactly the bound,
context and conclusion carried by the derivation.
-/

namespace RelationalPerimeter
namespace HeytingArithmetic

set_option maxRecDepth 16384
set_option maxHeartbeats 10000000

theorem embeddedArchive_finishedLineFrame
    (prefixLines suffixLines : List ProofLine)
    (archive : ProofArchive)
    (line : ProofLine) :
    let archiveCode :=
      (embeddedArchive prefixLines (archive.finish line) suffixLines).quote
    let terminalIndex :=
      prefixLines.length + (archive.finish line).lastIndex
    numericLineBound
        (numericArchiveLine archiveCode terminalIndex) = line.bound ∧
    numericLineContext
        (numericArchiveLine archiveCode terminalIndex) = line.contextCode ∧
    numericLineConclusion
        (numericArchiveLine archiveCode terminalIndex) =
      line.conclusionCode := by
  dsimp only
  rw [ProofArchive.lastIndex_finish,
    numericArchiveLine_embeddedFinish,
    numericLineBound_quote, numericLineContext_quote,
    numericLineConclusion_quote]
  exact ⟨rfl, rfl, rfl⟩

def derivationRuleTag
    {history : TheoryHistory}
    {bound : Nat}
    {context : FormulaContext bound}
    {conclusion : ScopedFormula bound} :
    Derivation LogicMode.intuitionistic history.theory context conclusion ->
      ProofRuleTag
  | .theoryAxiom _ => .theoryAxiom
  | .hypothesis _ => .hypothesis
  | .weaken _ _ => .weaken
  | .implicationIntroduction _ => .implicationIntroduction
  | .implicationElimination _ _ => .implicationElimination
  | .conjunctionIntroduction _ _ => .conjunctionIntroduction
  | .conjunctionEliminationLeft _ => .conjunctionEliminationLeft
  | .conjunctionEliminationRight _ => .conjunctionEliminationRight
  | .disjunctionIntroductionLeft _ => .disjunctionIntroductionLeft
  | .disjunctionIntroductionRight _ => .disjunctionIntroductionRight
  | .disjunctionElimination _ _ _ => .disjunctionElimination
  | .falsumElimination _ => .falsumElimination
  | .universalIntroduction _ => .universalIntroduction
  | .universalElimination _ _ => .universalElimination
  | .existentialIntroduction _ _ => .existentialIntroduction
  | .existentialElimination _ _ => .existentialElimination
  | .equalityReflexivity _ => .equalityReflexivity
  | .equalitySymmetry _ => .equalitySymmetry
  | .equalityTransitivity _ _ => .equalityTransitivity
  | .equalitySubstitution _ _ _ => .equalitySubstitution
  | .liftVariables _ => .liftVariables
  | .freeInstantiation _ _ => .freeInstantiation
  | .doubleNegationElimination _ _ => .doubleNegationElimination

structure EncodedHistoryTerminal
    {history : TheoryHistory}
    {bound : Nat}
    {context : FormulaContext bound}
    {conclusion : ScopedFormula bound}
    (proof :
      Derivation LogicMode.intuitionistic history.theory context conclusion) where
  archive : ProofArchive
  line : ProofLine
  encoding : encodeHistoryDerivation proof = archive.finish line
  ruleEquation : line.rule = derivationRuleTag proof
  boundEquation : line.bound = bound
  contextEquation : line.contextCode = context.quote
  conclusionEquation : line.conclusionCode = conclusion.raw.code

def encodeHistoryDerivation_terminalDecomposition
    {history : TheoryHistory}
    {bound : Nat}
    {context : FormulaContext bound}
    {conclusion : ScopedFormula bound}
    (proof :
      Derivation LogicMode.intuitionistic history.theory context conclusion) :
    EncodedHistoryTerminal proof := by
  cases proof <;>
    first
    | exact
        { archive := ProofArchive.empty
          line := _
          encoding := rfl
          ruleEquation := rfl
          boundEquation := rfl
          contextEquation := rfl
          conclusionEquation := rfl }
    | exact
        { archive := _
          line := _
          encoding := rfl
          ruleEquation := rfl
          boundEquation := rfl
          contextEquation := rfl
          conclusionEquation := rfl }

theorem encodeHistoryDerivation_embeddedTerminalFrame_of_finishedLine
    {history : TheoryHistory}
    {bound : Nat}
    {context : FormulaContext bound}
    {conclusion : ScopedFormula bound}
    (proof :
      Derivation LogicMode.intuitionistic history.theory context conclusion)
    (prefixLines suffixLines : List ProofLine)
    (archive : ProofArchive)
    (line : ProofLine)
    (encoding : encodeHistoryDerivation proof = archive.finish line)
    (boundEquation : line.bound = bound)
    (contextEquation : line.contextCode = context.quote)
    (conclusionEquation : line.conclusionCode = conclusion.raw.code) :
    let archiveCode :=
      (embeddedArchive prefixLines
        (encodeHistoryDerivation proof) suffixLines).quote
    let terminalIndex :=
      prefixLines.length + (encodeHistoryDerivation proof).lastIndex
    numericLineBound
        (numericArchiveLine archiveCode terminalIndex) = bound ∧
    numericLineContext
        (numericArchiveLine archiveCode terminalIndex) = context.quote ∧
    numericLineConclusion
        (numericArchiveLine archiveCode terminalIndex) =
      conclusion.raw.code := by
  rw [encoding]
  have frame :=
    embeddedArchive_finishedLineFrame
      prefixLines suffixLines archive line
  rw [boundEquation, contextEquation, conclusionEquation] at frame
  exact frame

theorem encodeHistoryDerivation_embeddedTerminalFrame
    {history : TheoryHistory}
    {bound : Nat}
    {context : FormulaContext bound}
    {conclusion : ScopedFormula bound}
    (proof :
      Derivation LogicMode.intuitionistic history.theory context conclusion)
    (prefixLines suffixLines : List ProofLine) :
    let archiveCode :=
      (embeddedArchive prefixLines
        (encodeHistoryDerivation proof) suffixLines).quote
    let terminalIndex :=
      prefixLines.length + (encodeHistoryDerivation proof).lastIndex
    numericLineBound
        (numericArchiveLine archiveCode terminalIndex) = bound ∧
    numericLineContext
        (numericArchiveLine archiveCode terminalIndex) = context.quote ∧
    numericLineConclusion
        (numericArchiveLine archiveCode terminalIndex) =
      conclusion.raw.code := by
  let terminal := encodeHistoryDerivation_terminalDecomposition proof
  exact encodeHistoryDerivation_embeddedTerminalFrame_of_finishedLine
    proof prefixLines suffixLines terminal.archive terminal.line
    terminal.encoding terminal.boundEquation terminal.contextEquation
    terminal.conclusionEquation

end HeytingArithmetic
end RelationalPerimeter

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.HeytingArithmetic.embeddedArchive_finishedLineFrame
#print axioms RelationalPerimeter.HeytingArithmetic.encodeHistoryDerivation_terminalDecomposition
#print axioms RelationalPerimeter.HeytingArithmetic.encodeHistoryDerivation_embeddedTerminalFrame_of_finishedLine
#print axioms RelationalPerimeter.HeytingArithmetic.encodeHistoryDerivation_embeddedTerminalFrame
/- AXIOM_AUDIT_END -/
