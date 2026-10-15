import RelationalPerimeter.Constitution.Godel.PerimetralCorrespondence
import RelationalPerimeter.Instances.HeytingArithmetic.HASoundness
import RelationalPerimeter.Instances.HeytingArithmetic.InternalFixedPoint
import RelationalPerimeter.Instances.HeytingArithmetic.ProvabilityPredicate

set_option autoImplicit false
set_option linter.defProp false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Effective Gödel system for Heyting arithmetic

This module closes the named-theory obligation left open by the generic
correspondence.  Its syntax is ordinary first-order arithmetic, its proof
checker is the executable root-history HA checker, its proof predicate is the
arithmetical graph of that same checker, and its parametric fixed point is an
HA derivation built from the represented capture-avoiding substitution
program.
-/

namespace RelationalPerimeter
namespace HeytingArithmetic

open StrongPerimetralTurning

set_option maxRecDepth 1000000
set_option maxHeartbeats 500000

/-! ## Executable syntax decoders -/

/-- Decode a unary formula and recompute its scoping evidence. -/
def decodePredicate (code : Nat) : Option Predicate := do
  let formula <- decodeScopedFormula 1 code
  pure { raw := formula.raw, isScoped := formula.isScoped }

theorem decodePredicate_code (predicate : Predicate) :
    decodePredicate predicate.raw.code = some predicate := by
  unfold decodePredicate
  have decoded : decodeScopedFormula 1 predicate.raw.code =
      some { raw := predicate.raw, isScoped := predicate.isScoped } :=
    decodeScopedFormula_code
      { raw := predicate.raw, isScoped := predicate.isScoped }
  rw [decoded]
  rfl

/-! ## Boolean HA checker and constructive decoder -/

/-- Boolean facade over the primitive-recursive root-history HA checker. -/
def haProofCheck (proofCode sentenceCode : Nat) : Bool :=
  if proofCheckBit TheoryHistory.root.quote proofCode sentenceCode = 1 then
    true
  else
    false

theorem haProofCheck_eq_true_iff
    (proofCode sentenceCode : Nat) :
    haProofCheck proofCode sentenceCode = true ↔
      proofCheckBit TheoryHistory.root.quote proofCode sentenceCode = 1 := by
  unfold haProofCheck
  by_cases accepted :
      proofCheckBit TheoryHistory.root.quote proofCode sentenceCode = 1
  · rw [if_pos accepted]
    constructor
    · intro _equality
      exact accepted
    · intro _equality
      rfl
  · rw [if_neg accepted]
    constructor
    · intro impossible
      cases impossible
    · intro equality
      exact (accepted equality).elim

/-- Decode an accepted numeric certificate to the exact typed derivation it
contains.  No choice principle is used: the verified archive is reconstructed
line by line by the primitive-recursive soundness development. -/
def decodeAcceptedHistoryProof
    (history : TheoryHistory)
    (proofCode : Nat)
    (sentence : Sentence)
    (accepted : proofCheckBit history.quote proofCode sentence.quote = 1) :
    Derivation LogicMode.intuitionistic history.theory
      FormulaContext.nil sentence.scopedFormula := by
  unfold proofCheckBit at accepted
  dsimp only at accepted
  have first := (natAndBit_eq_one_iff _ _).mp accepted
  have lineCountPositive : 0 < natUnpairLeft proofCode :=
    (natPositiveBit_pos_iff _).mp first.1
  have second := (natAndBit_pos_iff _ _).mp first.2
  have foldPositive : 0 <
      proofCheckFold (natUnpairLeft proofCode) 1 history.quote proofCode :=
    second.1
  have third := (natAndBit_pos_iff _ _).mp second.2
  have fourth := (natAndBit_pos_iff _ _).mp third.2
  have fifth := (natAndBit_pos_iff _ _).mp fourth.2
  have terminalBound :
      numericLineBound
          (numericArchiveLine proofCode (natUnpairLeft proofCode).pred) = 0 := by
    rw [numericLineBound_eq_unpair, numericArchiveLine_eq_beta]
    exact (natEqualBit_pos_iff _ _).mp third.1
  have terminalContext :
      numericLineContext
          (numericArchiveLine proofCode (natUnpairLeft proofCode).pred) = 0 := by
    rw [numericLineContext_eq_unpair, numericArchiveLine_eq_beta]
    exact (natEqualBit_pos_iff _ _).mp fourth.1
  have terminalConclusion :
      numericLineConclusion
          (numericArchiveLine proofCode (natUnpairLeft proofCode).pred) =
        sentence.quote := by
    rw [numericLineConclusion_eq_unpair, numericArchiveLine_eq_beta]
    exact (natEqualBit_pos_iff _ _).mp fifth.1
  let acceptedPrefix := acceptedNumericPrefix_of_fold_positive history proofCode
    (natUnpairLeft proofCode) 1 foldPositive
  have lastBounded : (natUnpairLeft proofCode).pred <
      natUnpairLeft proofCode :=
    Nat.pred_lt (Nat.ne_of_gt lineCountPositive)
  let last := acceptedPrefix.at (natUnpairLeft proofCode).pred lastBounded
  have lastBound : last.bound = 0 := by
    unfold last
    rw [AcceptedNumericPrefix.at_bound, terminalBound]
  have lastContext :
      last.context.quote = (FormulaContext.nil : FormulaContext 0).quote := by
    unfold last
    rw [AcceptedNumericPrefix.at_contextCode, terminalContext]
    rfl
  have lastConclusion :
      last.conclusion.raw.code = sentence.scopedFormula.raw.code := by
    unfold last
    rw [AcceptedNumericPrefix.at_conclusionCode, terminalConclusion]
    rfl
  exact last.recoverFromCodes FormulaContext.nil sentence.scopedFormula
    lastBound lastContext lastConclusion

/-- Decode a checked root-history certificate as an HA derivation. -/
def haDerivationOfCheckedProof
    {sentence : Sentence}
    (proof : CheckedSentenceProof Sentence.quote haProofCheck sentence) :
    Derivation LogicMode.intuitionistic haTheory FormulaContext.nil
      sentence.scopedFormula := by
  rcases proof with ⟨proofCode, ⟨verification⟩⟩
  apply rootDerivationToHA
  exact decodeAcceptedHistoryProof TheoryHistory.root proofCode sentence
    ((haProofCheck_eq_true_iff proofCode sentence.quote).mp verification)

/-- Encode a typed HA derivation and certify acceptance by the same checker. -/
def haCheckedProofOfDerivation
    {sentence : Sentence}
    (proof : Derivation LogicMode.intuitionistic haTheory
      FormulaContext.nil sentence.scopedFormula) :
    CheckedSentenceProof Sentence.quote haProofCheck sentence := by
  let rootProof := haDerivationToRoot proof
  let archive := encodeHistoryDerivation rootProof
  refine ⟨archive.quote, ⟨?_⟩⟩
  apply (haProofCheck_eq_true_iff archive.quote sentence.quote).mpr
  exact proofCheckBit_encodeHistoryDerivation
    TheoryHistory.root sentence rootProof

/-! ## Object biconditionals and proof transport -/

def haBiconditional (left right : Sentence) : Sentence :=
  let formula := ScopedFormula.conj
    (ScopedFormula.impl left.scopedFormula right.scopedFormula)
    (ScopedFormula.impl right.scopedFormula left.scopedFormula)
  { raw := formula.raw, isScoped := formula.isScoped }

/-- Structural code of an object-language implication. -/
def haImplicationCode (leftCode rightCode : Nat) : Nat :=
  Nat.succ (natPair 4 (natPair leftCode rightCode))

/-- Structural code of the conjunction of both directed implications. -/
def haBiconditionalCode (leftCode rightCode : Nat) : Nat :=
  Nat.succ (natPair 2
    (natPair (haImplicationCode leftCode rightCode)
      (haImplicationCode rightCode leftCode)))

theorem haBiconditional_quote (left right : Sentence) :
    (haBiconditional left right).quote =
      haBiconditionalCode left.quote right.quote := by
  rfl

def haEquivalenceCheck
    (certificateCode leftCode rightCode : Nat) : Bool :=
  haProofCheck certificateCode
    (haBiconditionalCode leftCode rightCode)

/-- An accepted equivalence certificate is exactly a checked HA proof of the
object-language biconditional. -/
def haBiconditionalProofOfCheckedEquivalence
    {left right : Sentence}
    (equivalence : CheckedSentenceEquivalence Sentence.quote
      haEquivalenceCheck left right) :
    CheckedSentenceProof Sentence.quote haProofCheck
      (haBiconditional left right) := by
  rcases equivalence with ⟨certificateCode, ⟨verification⟩⟩
  exact ⟨certificateCode, ⟨by
    rw [haBiconditional_quote]
    exact verification⟩⟩

def haProofForward
    {left right : Sentence}
    (equivalence : CheckedSentenceEquivalence Sentence.quote
      haEquivalenceCheck left right)
    (leftProof : CheckedSentenceProof Sentence.quote haProofCheck left) :
    CheckedSentenceProof Sentence.quote haProofCheck right :=
  let biconditionalProof := haDerivationOfCheckedProof
    (haBiconditionalProofOfCheckedEquivalence equivalence)
  let implicationProof :=
    Derivation.conjunctionEliminationLeft biconditionalProof
  let argumentProof := haDerivationOfCheckedProof leftProof
  haCheckedProofOfDerivation
    (Derivation.implicationElimination implicationProof argumentProof)

def haProofBackward
    {left right : Sentence}
    (equivalence : CheckedSentenceEquivalence Sentence.quote
      haEquivalenceCheck left right)
    (rightProof : CheckedSentenceProof Sentence.quote haProofCheck right) :
    CheckedSentenceProof Sentence.quote haProofCheck left :=
  let biconditionalProof := haDerivationOfCheckedProof
    (haBiconditionalProofOfCheckedEquivalence equivalence)
  let implicationProof :=
    Derivation.conjunctionEliminationRight biconditionalProof
  let argumentProof := haDerivationOfCheckedProof rightProof
  haCheckedProofOfDerivation
    (Derivation.implicationElimination implicationProof argumentProof)

/-! ## Parametric fixed-point certificate -/

def haDiagonalize (target : Predicate) : Predicate :=
  internalFixedPointBody target

def haDiagonalLeft (target source : Predicate) : Sentence :=
  (haDiagonalize target).applyNumeral source.raw.code

def haDiagonalRight (target source : Predicate) : Sentence :=
  target.applyNumeral (source.applyNumeral source.raw.code).quote

def haDiagonalDerivation
    (target source : Predicate) :
    Derivation LogicMode.intuitionistic haTheory FormulaContext.nil
      (haBiconditional (haDiagonalLeft target source)
        (haDiagonalRight target source)).scopedFormula :=
  internalFixedPoint_derivable target source

def haDiagonalProofArchive
    (target source : Predicate) : ProofArchive :=
  encodeHistoryDerivation
    (haDerivationToRoot (haDiagonalDerivation target source))

theorem haDiagonalProofArchive_accepted
    (target source : Predicate) :
    haProofCheck (haDiagonalProofArchive target source).quote
        (haBiconditional (haDiagonalLeft target source)
          (haDiagonalRight target source)).quote = true := by
  apply (haProofCheck_eq_true_iff _ _).mpr
  exact proofCheckBit_encodeHistoryDerivation TheoryHistory.root
    (haBiconditional (haDiagonalLeft target source)
      (haDiagonalRight target source))
    (haDerivationToRoot (haDiagonalDerivation target source))

theorem haDiagonalEquivalence_accepted
    (target source : Predicate) :
    haEquivalenceCheck (haDiagonalProofArchive target source).quote
        (haDiagonalLeft target source).quote
        (haDiagonalRight target source).quote = true := by
  unfold haEquivalenceCheck
  rw [← haBiconditional_quote]
  exact haDiagonalProofArchive_accepted target source

def haDiagonalizeExact
    (target source : Predicate) :
    CheckedSentenceEquivalence Sentence.quote haEquivalenceCheck
      ((haDiagonalize target).applyNumeral source.raw.code)
      (target.applyNumeral
        (source.applyNumeral source.raw.code).quote) :=
  ⟨(haDiagonalProofArchive target source).quote,
    ⟨haDiagonalEquivalence_accepted target source⟩⟩

/-! ## Standard semantics and the represented HA proof predicate -/

def haTruth (sentence : Sentence) : Type := PLift sentence.models

def haProofSound
    {sentence : Sentence}
    (proof : CheckedSentenceProof Sentence.quote haProofCheck sentence) :
    haTruth sentence :=
  ⟨haDerivation_sound (haDerivationOfCheckedProof proof)
    emptyEnvironment trivial⟩

def haEquivalenceTruthForward
    {left right : Sentence}
    (equivalence : CheckedSentenceEquivalence Sentence.quote
      haEquivalenceCheck left right) :
    haTruth left → haTruth right := by
  intro leftTruth
  let biconditionalTruth := haProofSound
    (haBiconditionalProofOfCheckedEquivalence equivalence)
  rcases biconditionalTruth with ⟨biconditionalHolds⟩
  rcases leftTruth with ⟨leftHolds⟩
  exact ⟨biconditionalHolds.1 leftHolds⟩

def haEquivalenceTruthBackward
    {left right : Sentence}
    (equivalence : CheckedSentenceEquivalence Sentence.quote
      haEquivalenceCheck left right) :
    haTruth right → haTruth left := by
  intro rightTruth
  let biconditionalTruth := haProofSound
    (haBiconditionalProofOfCheckedEquivalence equivalence)
  rcases biconditionalTruth with ⟨biconditionalHolds⟩
  rcases rightTruth with ⟨rightHolds⟩
  exact ⟨biconditionalHolds.2 rightHolds⟩

/-- Object-language negation of the represented HA provability predicate. -/
def haUnprovabilityPredicate : Predicate :=
  { raw := RawFormula.neg provHA.raw
    isScoped := And.intro provHA.isScoped trivial }

theorem haUnprovabilityPredicate_spec
    (sentence : Sentence) :
    (haUnprovabilityPredicate.applyNumeral sentence.quote).models ↔
      ((provHA.applyNumeral sentence.quote).models → False) := by
  rfl

def haRepresentsUnprovabilityForward
    (sentence : Sentence) :
    haTruth (haUnprovabilityPredicate.applyNumeral sentence.quote) →
      CheckedSentenceProof Sentence.quote haProofCheck sentence → Empty := by
  intro unprovabilityTruth checkedProof
  rcases unprovabilityTruth with ⟨unprovabilityHolds⟩
  have noProvability :
      (provHA.applyNumeral sentence.quote).models → False :=
    (haUnprovabilityPredicate_spec sentence).mp unprovabilityHolds
  apply False.elim
  apply noProvability
  apply (provHA_spec sentence).mpr
  exact Nonempty.intro (haDerivationOfCheckedProof checkedProof)

def haRepresentsUnprovabilityBackward
    (sentence : Sentence) :
    (CheckedSentenceProof Sentence.quote haProofCheck sentence → Empty) →
      haTruth (haUnprovabilityPredicate.applyNumeral sentence.quote) := by
  intro noCheckedProof
  refine ⟨(haUnprovabilityPredicate_spec sentence).mpr ?_⟩
  intro provabilityTruth
  have provable : HAProvable sentence :=
    (provHA_spec sentence).mp provabilityTruth
  exact Nonempty.elim provable (fun derivation =>
    Empty.elim (noCheckedProof (haCheckedProofOfDerivation derivation)))

/-! ## Named-theory realization and correspondence -/

def heytingArithmeticEffectiveGodelSystem :
    EffectivelyPresentedSoundGodelSystem :=
  { UnaryFormula := Predicate
    Sentence := Sentence
    encodeUnary := fun predicate => predicate.raw.code
    decodeUnary := decodePredicate
    decodeUnary_encode := decodePredicate_code
    encodeSentence := Sentence.quote
    decodeSentence := decodeSentence
    decodeSentence_encode := decodeSentence_quote
    substitute := Predicate.applyNumeral
    diagonalize := haDiagonalize
    proofCheck := haProofCheck
    equivalenceCheck := haEquivalenceCheck
    diagonalizeExact := haDiagonalizeExact
    proofForward := haProofForward
    proofBackward := haProofBackward
    Truth := haTruth
    proofSound := haProofSound
    equivalenceTruthForward := haEquivalenceTruthForward
    equivalenceTruthBackward := haEquivalenceTruthBackward
    unprovabilityFormula := haUnprovabilityPredicate
    representsUnprovabilityForward := haRepresentsUnprovabilityForward
    representsUnprovabilityBackward := haRepresentsUnprovabilityBackward }

def heytingArithmeticGodelExecution :
    ExecutedGodelProduction
      heytingArithmeticEffectiveGodelSystem.toGodelSyntax
      heytingArithmeticEffectiveGodelSystem.unprovabilityFormula
      heytingArithmeticEffectiveGodelSystem.toGodelInterpretation :=
  effectiveGodelExecution heytingArithmeticEffectiveGodelSystem

def heytingArithmeticGodelPerimetralCorrespondence :
    ExecutedGodelPerimetralCorrespondence
      heytingArithmeticGodelExecution :=
  executedGodelPerimetralCorrespondence
    heytingArithmeticGodelExecution

def heytingArithmeticAffirmativeConstitution :
    GodelAffirmativeConstitution heytingArithmeticGodelExecution :=
  heytingArithmeticGodelPerimetralCorrespondence.affirmative

def heytingArithmeticStrictContinuation :
    StrictConstitutivePrefix
      (perimeterDeployment
        (godelPerimetralPresentation heytingArithmeticGodelExecution))
      (godelPerimetralContinuation heytingArithmeticGodelExecution) :=
  heytingArithmeticGodelPerimetralCorrespondence.strictContinuation

def heytingArithmeticSameRegimeAdmissionToEmpty :
    GodelPositiveSameRegimeAdmission heytingArithmeticGodelExecution -> Empty :=
  heytingArithmeticGodelPerimetralCorrespondence.explicitAdmissionToEmpty

def heytingArithmeticSameRegimeAdmissionRejected :
    GodelPositiveSameRegimeAdmission heytingArithmeticGodelExecution -> False :=
  heytingArithmeticGodelPerimetralCorrespondence.explicitAdmissionRejected

end HeytingArithmetic
end RelationalPerimeter

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.HeytingArithmetic.decodePredicate
#print axioms RelationalPerimeter.HeytingArithmetic.decodePredicate_code
#print axioms RelationalPerimeter.HeytingArithmetic.haProofCheck
#print axioms RelationalPerimeter.HeytingArithmetic.haProofCheck_eq_true_iff
#print axioms RelationalPerimeter.HeytingArithmetic.decodeAcceptedHistoryProof
#print axioms RelationalPerimeter.HeytingArithmetic.haDerivationOfCheckedProof
#print axioms RelationalPerimeter.HeytingArithmetic.haCheckedProofOfDerivation
#print axioms RelationalPerimeter.HeytingArithmetic.haBiconditional
#print axioms RelationalPerimeter.HeytingArithmetic.haImplicationCode
#print axioms RelationalPerimeter.HeytingArithmetic.haBiconditionalCode
#print axioms RelationalPerimeter.HeytingArithmetic.haBiconditional_quote
#print axioms RelationalPerimeter.HeytingArithmetic.haEquivalenceCheck
#print axioms RelationalPerimeter.HeytingArithmetic.haBiconditionalProofOfCheckedEquivalence
#print axioms RelationalPerimeter.HeytingArithmetic.haProofForward
#print axioms RelationalPerimeter.HeytingArithmetic.haProofBackward
#print axioms RelationalPerimeter.HeytingArithmetic.haDiagonalize
#print axioms RelationalPerimeter.HeytingArithmetic.haDiagonalLeft
#print axioms RelationalPerimeter.HeytingArithmetic.haDiagonalRight
#print axioms RelationalPerimeter.HeytingArithmetic.haDiagonalDerivation
#print axioms RelationalPerimeter.HeytingArithmetic.haDiagonalProofArchive
#print axioms RelationalPerimeter.HeytingArithmetic.haDiagonalProofArchive_accepted
#print axioms RelationalPerimeter.HeytingArithmetic.haDiagonalEquivalence_accepted
#print axioms RelationalPerimeter.HeytingArithmetic.haDiagonalizeExact
#print axioms RelationalPerimeter.HeytingArithmetic.haTruth
#print axioms RelationalPerimeter.HeytingArithmetic.haProofSound
#print axioms RelationalPerimeter.HeytingArithmetic.haEquivalenceTruthForward
#print axioms RelationalPerimeter.HeytingArithmetic.haEquivalenceTruthBackward
#print axioms RelationalPerimeter.HeytingArithmetic.haUnprovabilityPredicate
#print axioms RelationalPerimeter.HeytingArithmetic.haUnprovabilityPredicate_spec
#print axioms RelationalPerimeter.HeytingArithmetic.haRepresentsUnprovabilityForward
#print axioms RelationalPerimeter.HeytingArithmetic.haRepresentsUnprovabilityBackward
#print axioms RelationalPerimeter.HeytingArithmetic.heytingArithmeticEffectiveGodelSystem
#print axioms RelationalPerimeter.HeytingArithmetic.heytingArithmeticGodelExecution
#print axioms RelationalPerimeter.HeytingArithmetic.heytingArithmeticGodelPerimetralCorrespondence
#print axioms RelationalPerimeter.HeytingArithmetic.heytingArithmeticAffirmativeConstitution
#print axioms RelationalPerimeter.HeytingArithmetic.heytingArithmeticStrictContinuation
#print axioms RelationalPerimeter.HeytingArithmetic.heytingArithmeticSameRegimeAdmissionToEmpty
#print axioms RelationalPerimeter.HeytingArithmetic.heytingArithmeticSameRegimeAdmissionRejected
/- AXIOM_AUDIT_END -/
