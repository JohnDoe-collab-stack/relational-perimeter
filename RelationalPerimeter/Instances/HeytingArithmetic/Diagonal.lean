import RelationalPerimeter.Instances.HeytingArithmetic.Representability
import RelationalPerimeter.Instances.HeytingArithmetic.PrimitiveRecursiveSubstitutionMachine

/-!
# Genuine diagonal lemma in bare first-order arithmetic

The fixed point is constructed from the arithmetic graph of the verified
capture-avoiding substitution program.  The grammar contains no quotation or
fixed-point constructor, and formula semantics has no reflective clause.
-/

namespace RelationalPerimeter
namespace HeytingArithmetic

/-! ## Arithmetic graph of self-substitution -/

/-- Bare arithmetic formula representing capture-avoiding self-substitution. -/
def diagonalSubstitutionGraph : ArithmeticGraph 1 :=
  PRFunction.captureAvoidingDiagonalSubstitution.graphFormula

/-- The represented graph is the positive execution relation of the program. -/
theorem diagonalSubstitutionGraph_iff_evaluates
    (input output : Nat) :
    diagonalSubstitutionGraph.Holds
        (NatVector.cons input NatVector.nil)
        output ↔
      PRFunction.Evaluates
        PRFunction.captureAvoidingDiagonalSubstitution
        (NatVector.cons input NatVector.nil)
        output :=
  PRFunction.graphFormula_spec
    PRFunction.captureAvoidingDiagonalSubstitution
    (NatVector.cons input NatVector.nil)
    output

/-- On every formula code, the graph has exactly the substituted formula code. -/
theorem diagonalSubstitutionGraph_code
    (formula : RawFormula)
    (output : Nat) :
    diagonalSubstitutionGraph.Holds
        (NatVector.cons formula.code NatVector.nil)
        output ↔
      output = (formula.instantiateNumeral formula.code).code := by
  apply Iff.trans
    (diagonalSubstitutionGraph_iff_evaluates formula.code output)
  constructor
  · intro evaluation
    exact PRFunction.evaluates_unique
      evaluation
      (PRFunction.captureAvoidingDiagonalSubstitution_evaluates_code formula)
  · intro equality
    cases equality
    exact PRFunction.captureAvoidingDiagonalSubstitution_evaluates_code formula

/-! ## Applying a unary predicate to an arbitrary arithmetic term -/

/-- Substitute the same arithmetic term for the sole free predicate variable. -/
def Predicate.applyTermRaw
    (predicate : Predicate)
    (term : RawTerm) : RawFormula :=
  predicate.raw.substitute (fun _index => term)

/-- Term application preserves a supplied target scope. -/
theorem Predicate.applyTermRaw_wellScoped
    (predicate : Predicate)
    (term : RawTerm)
    (bound : Nat)
    (termScoped : term.WellScoped bound) :
    (predicate.applyTermRaw term).WellScoped bound :=
  predicate.raw.wellScoped_substitute
    predicate.isScoped
    (fun _index => term)
    (fun _index _bounded => termScoped)

/-- Term application has exactly the unary-predicate semantics. -/
theorem Predicate.applyTermRaw_holds
    (predicate : Predicate)
    (term : RawTerm)
    (environment : Environment) :
    (predicate.applyTermRaw term).Holds environment ↔
      predicate.raw.Holds
        (pushEnvironment emptyEnvironment (term.evaluate environment)) := by
  apply Iff.trans
    (predicate.raw.holds_substitute
      (fun _index => term)
      environment)
  apply predicate.raw.holds_iff_of_scoped_agreement predicate.isScoped
  intro index bounded
  cases index with
  | zero => rfl
  | succ index =>
      exact (Nat.not_lt_zero index
        (Nat.lt_of_succ_lt_succ bounded)).elim

/-- Term application agrees with closed numeral application at its value. -/
theorem Predicate.applyTermRaw_holds_iff_models_applyNumeral
    (predicate : Predicate)
    (term : RawTerm)
    (environment : Environment) :
    (predicate.applyTermRaw term).Holds environment ↔
      (predicate.applyNumeral (term.evaluate environment)).models :=
  (predicate.applyTermRaw_holds term environment).trans
    (predicate.models_applyNumeral (term.evaluate environment)).symm

/-! ## Constructed fixed point -/

/--
Unary self-application body

`body_tau(x) := exists y, Subst(x,x,y) and not tau(y)`.
-/
def diagonalBody (predicate : Predicate) : Predicate :=
  let graphAt := diagonalSubstitutionGraph.apply
    (RawTerm.bvar 0)
    (RawTermVector.cons (RawTerm.bvar 1) RawTermVector.nil)
  let predicateAt := predicate.applyTermRaw (RawTerm.bvar 0)
  { raw := RawFormula.ex
      (RawFormula.conj graphAt (RawFormula.neg predicateAt))
    isScoped := And.intro
      (diagonalSubstitutionGraph.apply_wellScoped
        (RawTerm.bvar 0)
        (RawTermVector.cons (RawTerm.bvar 1) RawTermVector.nil)
        (Nat.zero_lt_succ 1)
        (And.intro
          (Nat.succ_lt_succ (Nat.zero_lt_succ 0))
          trivial))
      (And.intro
        (predicate.applyTermRaw_wellScoped
          (RawTerm.bvar 0)
          2
          (Nat.zero_lt_succ 1))
        trivial) }

/-- The actual diagonal sentence is the body applied to its own code. -/
def diagonal (predicate : Predicate) : Sentence :=
  let body := diagonalBody predicate
  body.applyNumeral body.raw.code

/-- The diagonal sentence code is the verified self-substitution output. -/
theorem diagonal_quote
    (predicate : Predicate) :
    (diagonal predicate).quote =
      ((diagonalBody predicate).raw.instantiateNumeral
        (diagonalBody predicate).raw.code).code :=
  rfl

/-- The body graph recognizes exactly the code of the constructed diagonal. -/
theorem diagonal_graph_at_own_code
    (predicate : Predicate) :
    diagonalSubstitutionGraph.Holds
        (NatVector.cons
          (diagonalBody predicate).raw.code NatVector.nil)
        (diagonal predicate).quote := by
  apply (diagonalSubstitutionGraph_code
    (diagonalBody predicate).raw
    (diagonal predicate).quote).mpr
  rfl

/-- Semantic fixed-point specification obtained from the represented graph. -/
theorem diagonal_spec (predicate : Predicate) :
    (diagonal predicate).models ↔
      ((predicate.applyNumeral (diagonal predicate).quote).models -> False) := by
  let body := diagonalBody predicate
  let bodyCode := body.raw.code
  let diagonalSentence := diagonal predicate
  apply Iff.trans (body.models_applyNumeral bodyCode)
  change
    (Exists fun output : Nat =>
      (diagonalSubstitutionGraph.apply
          (RawTerm.bvar 0)
          (RawTermVector.cons (RawTerm.bvar 1) RawTermVector.nil)).Holds
            (pushEnvironment
              (pushEnvironment emptyEnvironment bodyCode)
              output) ∧
        ((predicate.applyTermRaw (RawTerm.bvar 0)).Holds
          (pushEnvironment
            (pushEnvironment emptyEnvironment bodyCode)
            output) -> False)) ↔
      ((predicate.applyNumeral diagonalSentence.quote).models -> False)
  constructor
  · intro witness candidateHolds
    cases witness with
    | intro output conjunction =>
        have graphHolds :
            diagonalSubstitutionGraph.Holds
              (NatVector.cons bodyCode NatVector.nil)
              output := by
          apply (diagonalSubstitutionGraph.apply_holds_of_values
            (RawTerm.bvar 0)
            (RawTermVector.cons (RawTerm.bvar 1) RawTermVector.nil)
            (pushEnvironment
              (pushEnvironment emptyEnvironment bodyCode)
              output)
            (NatVector.cons bodyCode NatVector.nil)
            output
            rfl
            ?_).mp
          · exact conjunction.1
          · intro index bounded
            cases index with
            | zero => rfl
            | succ index =>
                exact (Nat.not_lt_zero index
                  (Nat.lt_of_succ_lt_succ bounded)).elim
        have outputCode : output = diagonalSentence.quote :=
          (diagonalSubstitutionGraph_code body.raw output).mp graphHolds
        have predicateAtOutput :
            (predicate.applyTermRaw (RawTerm.bvar 0)).Holds
              (pushEnvironment
                (pushEnvironment emptyEnvironment bodyCode)
                output) := by
          apply (predicate.applyTermRaw_holds_iff_models_applyNumeral
            (RawTerm.bvar 0)
            (pushEnvironment
              (pushEnvironment emptyEnvironment bodyCode)
              output)).mpr
          rw [outputCode]
          exact candidateHolds
        exact conjunction.2 predicateAtOutput
  · intro notCandidate
    refine Exists.intro diagonalSentence.quote ?_
    constructor
    · apply (diagonalSubstitutionGraph.apply_holds_of_values
        (RawTerm.bvar 0)
        (RawTermVector.cons (RawTerm.bvar 1) RawTermVector.nil)
        (pushEnvironment
          (pushEnvironment emptyEnvironment bodyCode)
          diagonalSentence.quote)
        (NatVector.cons bodyCode NatVector.nil)
        diagonalSentence.quote
        rfl
        ?_).mpr
      · exact diagonal_graph_at_own_code predicate
      · intro index bounded
        cases index with
        | zero => rfl
        | succ index =>
            exact (Nat.not_lt_zero index
              (Nat.lt_of_succ_lt_succ bounded)).elim
    · intro predicateAt
      apply notCandidate
      apply (predicate.applyTermRaw_holds_iff_models_applyNumeral
        (RawTerm.bvar 0)
        (pushEnvironment
          (pushEnvironment emptyEnvironment bodyCode)
          diagonalSentence.quote)).mp
      exact predicateAt

end HeytingArithmetic
end RelationalPerimeter

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.HeytingArithmetic.diagonalSubstitutionGraph_code
#print axioms RelationalPerimeter.HeytingArithmetic.diagonal
#print axioms RelationalPerimeter.HeytingArithmetic.diagonal_quote
#print axioms RelationalPerimeter.HeytingArithmetic.diagonal_spec
/- AXIOM_AUDIT_END -/
