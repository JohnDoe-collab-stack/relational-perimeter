import RelationalPerimeter.Instances.HeytingArithmetic.Diagonal
import RelationalPerimeter.Instances.HeytingArithmetic.InternalPRDeterminacy

/-!
# The negative diagonal lemma as an internal HA derivation

The semantic theorem `diagonal_spec` remains separate.  This file constructs
the two object-language implications by consuming the internally represented
capture-avoiding substitution program.
-/

namespace RelationalPerimeter
namespace HeytingArithmetic

set_option maxRecDepth 8192
set_option maxHeartbeats 500000

/-- A unary graph applied to one closed numeral remains scoped without
unfolding the concrete graph compiler. -/
theorem ArithmeticGraph.applyUnaryNumeral_wellScoped
    (graph : ArithmeticGraph 1)
    (input : Nat) :
    (graph.apply (RawTerm.bvar 0)
      (RawTermVector.cons (RawTerm.numeral input) RawTermVector.nil)).WellScoped
        1 :=
  graph.apply_wellScoped _ _ (Nat.zero_lt_succ 0)
    (And.intro (RawTerm.numeral_wellScoped input 1) trivial)

/-- A unary graph applied to two closed numerals is a closed formula. -/
theorem ArithmeticGraph.applyUnaryNumerals_wellScoped
    (graph : ArithmeticGraph 1)
    (input output : Nat) :
    (graph.apply (RawTerm.numeral output)
      (RawTermVector.cons (RawTerm.numeral input) RawTermVector.nil)).WellScoped
        0 :=
  graph.apply_wellScoped _ _ (RawTerm.numeral_wellScoped output 0)
    (And.intro (RawTerm.numeral_wellScoped input 0) trivial)

/-- Substitution commutes with applying a unary predicate to a term. -/
theorem Predicate.applyTermRaw_substitute
    (predicate : Predicate)
    (term : RawTerm)
    (substitution : Substitution) :
    (predicate.applyTermRaw term).substitute substitution =
      predicate.applyTermRaw (term.substitute substitution) := by
  unfold Predicate.applyTermRaw
  rw [RawFormula.substitute_compose]

/-- Instantiating the output variable of a unary graph does not unfold the
compiled graph itself. -/
theorem ArithmeticGraph.applyUnaryNumeral_instantiate_raw
    (graph : ArithmeticGraph 1)
    (input output : Nat) :
    (graph.apply (RawTerm.bvar 0)
      (RawTermVector.cons (RawTerm.numeral input) RawTermVector.nil)).substitute
        (singleTermSubstitution (RawTerm.numeral output)) =
      graph.apply (RawTerm.numeral output)
        (RawTermVector.cons (RawTerm.numeral input) RawTermVector.nil) := by
  apply ArithmeticGraph.apply_substitute_exact_bounded
  · rfl
  · intro index bounded
    cases index with
    | zero => exact RawTerm.numeral_substitute _ _
    | succ index =>
        exact (Nat.not_succ_le_zero index
          (Nat.lt_of_succ_lt_succ bounded)).elim

/-- The instantiated diagonal witness is exactly the conjunction of the
closed graph instance and the closed predicate instance. -/
theorem diagonalWitnessBody_instantiate_raw
    (predicate : Predicate)
    (input output : Nat) :
    (RawFormula.conj
      (diagonalSubstitutionGraph.apply (RawTerm.bvar 0)
        (RawTermVector.cons (RawTerm.numeral input) RawTermVector.nil))
      (RawFormula.neg
        (predicate.applyTermRaw (RawTerm.bvar 0)))).substitute
          (singleTermSubstitution (RawTerm.numeral output)) =
      RawFormula.conj
        (diagonalSubstitutionGraph.apply (RawTerm.numeral output)
          (RawTermVector.cons (RawTerm.numeral input) RawTermVector.nil))
        (RawFormula.neg
          (predicate.applyTermRaw (RawTerm.numeral output))) := by
  apply congrArgTwo RawFormula.conj
  · exact diagonalSubstitutionGraph.applyUnaryNumeral_instantiate_raw
      input output
  · apply congrArg RawFormula.neg
    exact (Predicate.applyTermRaw_substitute predicate (RawTerm.bvar 0)
      (singleTermSubstitution (RawTerm.numeral output))).trans rfl

/-- Instantiating the diagonal body exposes exactly its witness block while
keeping the concrete substitution graph opaque. -/
theorem diagonalBody_instantiateNumeral_raw_at
    (predicate : Predicate)
    (code : Nat) :
    (diagonalBody predicate).raw.instantiateNumeral
        code =
      RawFormula.ex
        (RawFormula.conj
          (diagonalSubstitutionGraph.apply
            (RawTerm.bvar 0)
            (RawTermVector.cons
              (RawTerm.numeral code)
              RawTermVector.nil))
          (RawFormula.neg
            (predicate.applyTermRaw (RawTerm.bvar 0)))) := by
  unfold diagonalBody RawFormula.instantiateNumeral
  apply congrArg RawFormula.ex
  apply congrArgTwo RawFormula.conj
  · apply Eq.trans (ArithmeticGraph.apply_substitute
      diagonalSubstitutionGraph (RawTerm.bvar 0)
      (RawTermVector.cons (RawTerm.bvar 1) RawTermVector.nil)
      (liftSubstitution (fun _index =>
        RawTerm.numeral code)))
    apply congrArgTwo diagonalSubstitutionGraph.apply
    · rfl
    · apply congrArg (fun head =>
        RawTermVector.cons head RawTermVector.nil)
      exact RawTerm.numeral_rename _ _
  · apply congrArg RawFormula.neg
    exact (Predicate.applyTermRaw_substitute predicate (RawTerm.bvar 0)
      (liftSubstitution (fun _index =>
        RawTerm.numeral code))).trans rfl

def Predicate.applyTerm
    {bound : Nat}
    (predicate : Predicate)
    (term : ScopedTerm bound) : ScopedFormula bound :=
  { raw := predicate.applyTermRaw term.raw
    isScoped := predicate.applyTermRaw_wellScoped term.raw bound term.isScoped }

/-- Applying a predicate to a numeral at scope one is the lift of its closed
numeral application. -/
theorem Predicate.applyTerm_numeral_eq_lift_applyNumeral
    (predicate : Predicate)
    (value : Nat) :
    predicate.applyTerm (ScopedTerm.numeral 1 value) =
      (predicate.applyNumeral value).scopedFormula.lift := by
  apply ScopedFormula.eq_of_raw_eq
  change
    predicate.raw.instantiateNumeral value =
      (predicate.raw.instantiateNumeral value).rename Nat.succ
  apply Eq.symm
  apply Eq.trans
    (RawFormula.substitute_bvars_eq_rename
      (predicate.raw.instantiateNumeral value) Nat.succ).symm
  apply RawFormula.substitute_eq_self_of_scoped_agreement
    (predicate.raw.instantiateNumeral value)
    (predicate.applyNumeral value).isScoped
  intro index bounded
  exact (Nat.not_lt_zero index bounded).elim

/-- Instantiating the newest variable in the negative predicate instance is
the lift of the corresponding closed negative instance. -/
theorem Predicate.negativeNewest_instantiate_numeral_eq_lift_applyNumeral
    (predicate : Predicate)
    (value : Nat) :
    (ScopedFormula.neg
      (predicate.applyTerm
        (ScopedTerm.bvar 0 (Nat.zero_lt_succ 1)))).instantiate
          (ScopedTerm.numeral 1 value) =
      (ScopedFormula.neg
        (predicate.applyNumeral value).scopedFormula).lift := by
  apply ScopedFormula.eq_of_raw_eq
  apply congrArgTwo RawFormula.impl
  · apply Eq.trans (Predicate.applyTermRaw_substitute predicate
      (RawTerm.bvar 0)
      (singleTermSubstitution (RawTerm.numeral value)))
    exact congrArg ScopedFormula.raw
      (predicate.applyTerm_numeral_eq_lift_applyNumeral value)
  · rfl

def internalLiarDiagonal (predicate : Predicate) : Sentence :=
  diagonal predicate

theorem internalLiarDiagonal_quote
    (predicate : Predicate) :
    (internalLiarDiagonal predicate).quote =
      ((diagonalBody predicate).raw.instantiateNumeral
        (diagonalBody predicate).raw.code).code :=
  diagonal_quote predicate

def internalLiarDiagonalTarget (predicate : Predicate) : ScopedFormula 0 :=
  ScopedFormula.neg
    ((predicate.applyNumeral (internalLiarDiagonal predicate).quote)
      |>.scopedFormula)

def internalLiarDiagonal_derivable_forward
    (predicate : Predicate) :
    Derivation LogicMode.intuitionistic haTheory FormulaContext.nil
      (ScopedFormula.impl
        (internalLiarDiagonal predicate).scopedFormula
        (internalLiarDiagonalTarget predicate)) := by
  apply Derivation.implicationIntroduction
  let diagonalFormula := (internalLiarDiagonal predicate).scopedFormula
  let diagonalContext := FormulaContext.cons diagonalFormula FormulaContext.nil
  let diagonalProof : Derivation LogicMode.intuitionistic haTheory diagonalContext
      diagonalFormula := Derivation.hypothesis ContextMember.here
  let body := diagonalBody predicate
  let bodyCode := body.raw.code
  let graphAt := diagonalSubstitutionGraph.apply
    (RawTerm.bvar 0)
    (RawTermVector.cons (RawTerm.numeral bodyCode) RawTermVector.nil)
  let predicateAt := predicate.applyTerm
    (ScopedTerm.bvar 0 (Nat.zero_lt_succ 0))
  let witnessBody : ScopedFormula 1 :=
    ScopedFormula.conj
      { raw := graphAt
        isScoped :=
          diagonalSubstitutionGraph.applyUnaryNumeral_wellScoped bodyCode }
      (ScopedFormula.neg predicateAt)
  let normalizedDiagonal : Derivation LogicMode.intuitionistic haTheory
      diagonalContext (ScopedFormula.ex witnessBody) := by
    refine Derivation.castConclusion ?_ diagonalProof
    apply ScopedFormula.eq_of_raw_eq
    change
      (diagonalBody predicate).raw.instantiateNumeral
          (diagonalBody predicate).raw.code =
        witnessBody.raw.ex
    exact diagonalBody_instantiateNumeral_raw_at predicate
      (diagonalBody predicate).raw.code
  let witnessContext := FormulaContext.cons witnessBody diagonalContext.lift
  let witnessProof : Derivation LogicMode.intuitionistic haTheory witnessContext
      witnessBody := Derivation.hypothesis ContextMember.here
  let graphProof := Derivation.conjunctionEliminationLeft witnessProof
  let negativeAtWitness := Derivation.conjunctionEliminationRight witnessProof
  let witness := ScopedTerm.bvar 0 (Nat.zero_lt_succ 0)
  let inputs := NatVector.cons bodyCode NatVector.nil
  let normalizedGraph : Derivation LogicMode.intuitionistic haTheory witnessContext
      (PRFunction.captureAvoidingDiagonalSubstitution.graphFormula
        |>.numeralApplicationAt inputs witness) := by
    refine Derivation.castConclusion ?_ graphProof
    apply ScopedFormula.eq_of_raw_eq
    rfl
  let forcedRun :=
    PRFunction.captureAvoidingDiagonalSubstitution.internalGraphFunctional
      inputs witness normalizedGraph
  have diagonalRun :
      (internalLiarDiagonal predicate).quote =
        PRFunction.captureAvoidingDiagonalSubstitution.run inputs := by
    exact PRFunction.captureAvoidingDiagonalSubstitution_evaluates_code
      body.raw
  let normalizeRun := (numeralEqualityProof 1
    (PRFunction.captureAvoidingDiagonalSubstitution.run inputs)
    (internalLiarDiagonal predicate).quote diagonalRun.symm)
    |>.weakenClosedTo witnessContext
  let normalizedRunEquality : Derivation LogicMode.intuitionistic haTheory
      witnessContext
      (ScopedFormula.equal
        (ScopedTerm.numeral 1
          (PRFunction.captureAvoidingDiagonalSubstitution.run inputs))
        (ScopedTerm.numeral 1
          (internalLiarDiagonal predicate).quote)) := by
    refine Derivation.castConclusion ?_ normalizeRun
    apply ScopedFormula.eq_of_raw_eq
    rfl
  let witnessEqualsDiagonal := Derivation.equalityTransitivity forcedRun
    normalizedRunEquality
  let negativeBody : ScopedFormula 2 :=
    ScopedFormula.neg
      (predicate.applyTerm
        (ScopedTerm.bvar 0 (Nat.zero_lt_succ 1)))
  let negativeAtWitnessExact : Derivation LogicMode.intuitionistic haTheory
      witnessContext (negativeBody.instantiate witness) := by
    refine Derivation.castConclusion ?_ negativeAtWitness
    apply ScopedFormula.eq_of_raw_eq
    apply congrArg RawFormula.neg
    exact (Predicate.applyTermRaw_substitute predicate (RawTerm.bvar 0)
      (singleTermSubstitution witness.raw)).symm
  let transportedNegative := Derivation.equalitySubstitution negativeBody
    witnessEqualsDiagonal negativeAtWitnessExact
  have transportedConclusionExact :
      negativeBody.instantiate
          (ScopedTerm.numeral 1 (internalLiarDiagonal predicate).quote) =
        (internalLiarDiagonalTarget predicate).lift := by
    exact predicate.negativeNewest_instantiate_numeral_eq_lift_applyNumeral
      (internalLiarDiagonal predicate).quote
  let transportedTarget : Derivation LogicMode.intuitionistic haTheory
      witnessContext (internalLiarDiagonalTarget predicate).lift :=
    Derivation.castConclusion transportedConclusionExact transportedNegative
  let eliminated := Derivation.existentialElimination normalizedDiagonal
    transportedTarget
  exact eliminated

def internalLiarDiagonal_derivable_backward
    (predicate : Predicate) :
    Derivation LogicMode.intuitionistic haTheory FormulaContext.nil
      (ScopedFormula.impl
        (internalLiarDiagonalTarget predicate)
        (internalLiarDiagonal predicate).scopedFormula) := by
  apply Derivation.implicationIntroduction
  let target := internalLiarDiagonalTarget predicate
  let targetContext := FormulaContext.cons target FormulaContext.nil
  let negativeProof : Derivation LogicMode.intuitionistic haTheory targetContext
      target := Derivation.hypothesis ContextMember.here
  let body := diagonalBody predicate
  let bodyCode := body.raw.code
  let diagonalCode := (internalLiarDiagonal predicate).quote
  let inputs := NatVector.cons bodyCode NatVector.nil
  have evaluation : PRFunction.Evaluates
      PRFunction.captureAvoidingDiagonalSubstitution inputs diagonalCode := by
    exact PRFunction.captureAvoidingDiagonalSubstitution_evaluates_code body.raw
  let graphProofPA := PRFunction.internalGraphNumeralProof
    PRFunction.captureAvoidingDiagonalSubstitution inputs diagonalCode evaluation
  let graphProof := graphProofPA.weakenClosedTo targetContext
  let witnessBody : ScopedFormula 1 :=
    ScopedFormula.conj
      { raw := diagonalSubstitutionGraph.apply
          (RawTerm.bvar 0)
          (RawTermVector.cons (RawTerm.numeral bodyCode) RawTermVector.nil)
        isScoped :=
          diagonalSubstitutionGraph.applyUnaryNumeral_wellScoped bodyCode }
      (ScopedFormula.neg
        (predicate.applyTerm
          (ScopedTerm.bvar 0 (Nat.zero_lt_succ 0))))
  let closedGraph : ScopedFormula 0 :=
    { raw := diagonalSubstitutionGraph.apply
        (RawTerm.numeral diagonalCode)
        (RawTermVector.cons (RawTerm.numeral bodyCode) RawTermVector.nil)
      isScoped := diagonalSubstitutionGraph.applyUnaryNumerals_wellScoped
        bodyCode diagonalCode }
  let graphProofExact : Derivation LogicMode.intuitionistic haTheory targetContext
      closedGraph := by
    refine Derivation.castConclusion ?_ graphProof
    apply ScopedFormula.eq_of_raw_eq
    rfl
  let closedNegative := ScopedFormula.neg
    (predicate.applyTerm (ScopedTerm.numeral 0 diagonalCode))
  let negativeProofExact : Derivation LogicMode.intuitionistic haTheory targetContext
      closedNegative := by
    refine Derivation.castConclusion ?_ negativeProof
    apply ScopedFormula.eq_of_raw_eq
    rfl
  let closedConjunction := Derivation.conjunctionIntroduction
    graphProofExact negativeProofExact
  let graphAtDiagonal : Derivation LogicMode.intuitionistic haTheory targetContext
      (witnessBody.instantiate (ScopedTerm.numeral 0 diagonalCode)) := by
    refine Derivation.castConclusion ?_ closedConjunction
    apply ScopedFormula.eq_of_raw_eq
    exact (diagonalWitnessBody_instantiate_raw predicate bodyCode
      diagonalCode).symm
  let introduced := Derivation.existentialIntroduction
    (body := witnessBody) (ScopedTerm.numeral 0 diagonalCode)
    graphAtDiagonal
  refine Derivation.castConclusion ?_ introduced
  apply ScopedFormula.eq_of_raw_eq
  exact (diagonalBody_instantiateNumeral_raw_at predicate bodyCode).symm

def internalLiarDiagonal_derivable
    (predicate : Predicate) :
    Derivation LogicMode.intuitionistic haTheory FormulaContext.nil
      (ScopedFormula.conj
        (ScopedFormula.impl
          (internalLiarDiagonal predicate).scopedFormula
          (internalLiarDiagonalTarget predicate))
        (ScopedFormula.impl
          (internalLiarDiagonalTarget predicate)
          (internalLiarDiagonal predicate).scopedFormula)) :=
  Derivation.conjunctionIntroduction
    (internalLiarDiagonal_derivable_forward predicate)
    (internalLiarDiagonal_derivable_backward predicate)

end HeytingArithmetic
end RelationalPerimeter

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.HeytingArithmetic.ArithmeticGraph.applyUnaryNumeral_wellScoped
#print axioms RelationalPerimeter.HeytingArithmetic.internalLiarDiagonal_quote
#print axioms RelationalPerimeter.HeytingArithmetic.internalLiarDiagonal_derivable_forward
#print axioms RelationalPerimeter.HeytingArithmetic.internalLiarDiagonal_derivable_backward
#print axioms RelationalPerimeter.HeytingArithmetic.internalLiarDiagonal_derivable
/- AXIOM_AUDIT_END -/
