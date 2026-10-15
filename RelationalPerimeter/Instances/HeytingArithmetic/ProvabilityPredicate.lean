import RelationalPerimeter.Instances.HeytingArithmetic.PrimitiveRecursiveProofCorrectness
import RelationalPerimeter.Instances.HeytingArithmetic.ProofTheoryTransport

/-!
# Arithmetic proof and provability formulas

The numeric verifier is compiled by the existing structural graph compiler.
Fixing the output to one gives a ternary proof relation.  Fixing an intrinsic
history and existentially binding the proof code gives the unary arithmetic
predicate `provabilityPredicate history`.
-/

namespace RelationalPerimeter
namespace HeytingArithmetic

def proofCheckGraph : ArithmeticGraph 3 :=
  PRFunction.proofCheck.graphFormula

def proofFormulaInputs : RawTermVector 3 :=
  RawTermVector.cons (RawTerm.bvar 0)
    (RawTermVector.cons (RawTerm.bvar 1)
      (RawTermVector.cons (RawTerm.bvar 2) RawTermVector.nil))

theorem proofFormulaInputs_wellScoped :
    proofFormulaInputs.WellScoped 3 :=
  And.intro (Nat.zero_lt_succ 2)
    (And.intro (Nat.succ_lt_succ (Nat.zero_lt_succ 1))
      (And.intro
        (Nat.succ_lt_succ
          (Nat.succ_lt_succ (Nat.zero_lt_succ 0))) trivial))

/-- Ternary relation `Proof(history,proof,sentence)`. -/
def proofFormula : ScopedFormula 3 :=
  { raw := proofCheckGraph.apply (RawTerm.numeral 1) proofFormulaInputs
    isScoped := proofCheckGraph.apply_wellScoped
      (RawTerm.numeral 1) proofFormulaInputs
      (RawTerm.numeral_wellScoped 1 3)
      proofFormulaInputs_wellScoped }

theorem proofFormulaInputs_evaluate
    (environment : Environment) :
    proofFormulaInputs.evaluate environment =
      NatVector.cons (environment 0)
        (NatVector.cons (environment 1)
          (NatVector.cons (environment 2) NatVector.nil)) := rfl

theorem proofFormula_spec
    (environment : Environment) :
    proofFormula.raw.Holds environment ↔
      proofCheckBit (environment 0) (environment 1) (environment 2) = 1 := by
  unfold proofFormula
  apply Iff.trans
    (proofCheckGraph.apply_holds
      (RawTerm.numeral 1) proofFormulaInputs environment)
  change proofCheckGraph.Holds
      (NatVector.cons (environment 0)
        (NatVector.cons (environment 1)
          (NatVector.cons (environment 2) NatVector.nil))) 1 ↔ _
  unfold proofCheckGraph
  apply Iff.trans
    (PRFunction.graphFormula_spec PRFunction.proofCheck
      (NatVector.cons (environment 0)
        (NatVector.cons (environment 1)
          (NatVector.cons (environment 2) NatVector.nil))) 1)
  constructor
  · intro accepted
    have evaluation :=
      PRFunction.proofCheck_evaluates
        (environment 0) (environment 1) (environment 2)
    unfold PRFunction.Evaluates at accepted evaluation
    exact evaluation.trans accepted.symm
  · intro checked
    have evaluation :=
      PRFunction.proofCheck_evaluates
        (environment 0) (environment 1) (environment 2)
    unfold PRFunction.Evaluates at evaluation ⊢
    exact checked.symm.trans evaluation

/-- Binary proof relation for a fixed finite theory history. -/
def historyProofFormula (history : TheoryHistory) : ScopedFormula 2 :=
  proofFormula.instantiate (ScopedTerm.numeral 2 history.quote)

/-- Unary arithmetical provability predicate for one finite history. -/
def provabilityPredicate (history : TheoryHistory) : Predicate :=
  let quantified := ScopedFormula.ex (historyProofFormula history)
  { raw := quantified.raw, isScoped := quantified.isScoped }

/-- Root-history HA provability predicate. -/
def provHA : Predicate := provabilityPredicate TheoryHistory.root

/-- Conventional mathematical spelling for the represented HA predicate. -/
def Prov_HA : Predicate := provHA

theorem historyProofFormula_spec
    (history : TheoryHistory)
    (environment : Environment) :
    (historyProofFormula history).raw.Holds environment ↔
      proofCheckBit history.quote (environment 0) (environment 1) = 1 := by
  unfold historyProofFormula ScopedFormula.instantiate
  apply Iff.trans
    (RawFormula.holds_instantiateTerm proofFormula.raw
      (ScopedTerm.numeral 2 history.quote).raw environment)
  apply Iff.trans
    (proofFormula_spec
      (pushEnvironment environment
        ((ScopedTerm.numeral 2 history.quote).raw.evaluate environment)))
  have numeralEvaluation :
      (ScopedTerm.numeral 2 history.quote).raw.evaluate environment =
        history.quote := by
    unfold ScopedTerm.numeral
    exact RawTerm.evaluate_numeral history.quote environment
  have checkEquation :
      proofCheckBit
          (pushEnvironment environment
            ((ScopedTerm.numeral 2 history.quote).raw.evaluate environment) 0)
          (pushEnvironment environment
            ((ScopedTerm.numeral 2 history.quote).raw.evaluate environment) 1)
          (pushEnvironment environment
            ((ScopedTerm.numeral 2 history.quote).raw.evaluate environment) 2) =
        proofCheckBit history.quote (environment 0) (environment 1) := by
    rw [numeralEvaluation]
    rfl
  constructor
  · intro checked
    exact checkEquation.symm.trans checked
  · intro checked
    exact checkEquation.trans checked

theorem provabilityPredicate_spec_numeric
    (history : TheoryHistory)
    (sentenceCode : Nat) :
    (provabilityPredicate history).raw.Holds
        (pushEnvironment emptyEnvironment sentenceCode) ↔
      Exists fun proofCode =>
        proofCheckBit history.quote proofCode sentenceCode = 1 := by
  unfold provabilityPredicate
  change (RawFormula.ex (historyProofFormula history).raw).Holds _ ↔ _
  constructor
  · intro witness
    cases witness with
    | intro proofCode proofHolds =>
        exact Exists.intro proofCode
          ((historyProofFormula_spec history
            (pushEnvironment
              (pushEnvironment emptyEnvironment sentenceCode) proofCode)).mp
            proofHolds)
  · intro witness
    cases witness with
    | intro proofCode checked =>
        exact Exists.intro proofCode
          ((historyProofFormula_spec history
            (pushEnvironment
              (pushEnvironment emptyEnvironment sentenceCode) proofCode)).mpr
            checked)

theorem provabilityPredicate_models_applyNumeral
    (history : TheoryHistory)
    (sentenceCode : Nat) :
    ((provabilityPredicate history).applyNumeral sentenceCode |>.models) ↔
      Exists fun proofCode =>
        proofCheckBit history.quote proofCode sentenceCode = 1 := by
  apply Iff.trans
    (Predicate.models_applyNumeral
      (provabilityPredicate history) sentenceCode)
  exact provabilityPredicate_spec_numeric history sentenceCode

theorem provabilityPredicate_spec
    (history : TheoryHistory)
    (sentence : Sentence) :
    ((provabilityPredicate history).applyNumeral sentence.quote |>.models) ↔
      HistoryProvable history sentence := by
  apply Iff.trans
    (provabilityPredicate_models_applyNumeral history sentence.quote)
  exact (historyProvable_iff_numericProof history sentence).symm

theorem provHA_spec
    (sentence : Sentence) :
    (provHA.applyNumeral sentence.quote |>.models) ↔
      HAProvable sentence := by
  apply Iff.trans
    (provabilityPredicate_spec TheoryHistory.root sentence)
  exact rootHistoryProvable_iff_haProvable sentence

theorem Prov_HA_spec
    (sentence : Sentence) :
    (Prov_HA.applyNumeral sentence.quote |>.models) ↔
      HAProvable sentence := by
  exact provHA_spec sentence

end HeytingArithmetic
end RelationalPerimeter

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.HeytingArithmetic.proofFormula
#print axioms RelationalPerimeter.HeytingArithmetic.proofFormula_spec
#print axioms RelationalPerimeter.HeytingArithmetic.provabilityPredicate
#print axioms RelationalPerimeter.HeytingArithmetic.provabilityPredicate_models_applyNumeral
#print axioms RelationalPerimeter.HeytingArithmetic.provabilityPredicate_spec
#print axioms RelationalPerimeter.HeytingArithmetic.provHA
#print axioms RelationalPerimeter.HeytingArithmetic.provHA_spec
#print axioms RelationalPerimeter.HeytingArithmetic.Prov_HA_spec
/- AXIOM_AUDIT_END -/
