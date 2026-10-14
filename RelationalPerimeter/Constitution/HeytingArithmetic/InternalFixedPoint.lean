import RelationalPerimeter.Constitution.HeytingArithmetic.InternalDiagonal

/-!
# Parametric fixed points inside Heyting arithmetic

The diagonal syntax used by the generic correspondence must work for every
target predicate and every source predicate.  This module constructs the
required body from the represented capture-avoiding substitution program and
derives both directions of its object-language biconditional in HA.
-/

namespace RelationalPerimeter
namespace HeytingArithmetic

set_option maxRecDepth 8192
set_option maxHeartbeats 500000

/-- The parametric diagonal body
`D_tau(x) := exists y, Subst(x,x,y) and tau(y)`. -/
def internalFixedPointBody (target : Predicate) : Predicate :=
  let graphAt := diagonalSubstitutionGraph.apply
    (RawTerm.bvar 0)
    (RawTermVector.cons (RawTerm.bvar 1) RawTermVector.nil)
  let targetAt := target.applyTermRaw (RawTerm.bvar 0)
  { raw := RawFormula.ex (RawFormula.conj graphAt targetAt)
    isScoped := And.intro
      (diagonalSubstitutionGraph.apply_wellScoped
        (RawTerm.bvar 0)
        (RawTermVector.cons (RawTerm.bvar 1) RawTermVector.nil)
        (Nat.zero_lt_succ 1)
        (And.intro
          (Nat.succ_lt_succ (Nat.zero_lt_succ 0))
          trivial))
      (target.applyTermRaw_wellScoped
        (RawTerm.bvar 0) 2 (Nat.zero_lt_succ 1)) }

/-- Instantiating the witness variable exposes the closed graph and target
instances without unfolding the graph compiler. -/
theorem internalFixedPointWitnessBody_instantiate_raw
    (target : Predicate)
    (input output : Nat) :
    (RawFormula.conj
      (diagonalSubstitutionGraph.apply (RawTerm.bvar 0)
        (RawTermVector.cons (RawTerm.numeral input) RawTermVector.nil))
      (target.applyTermRaw (RawTerm.bvar 0))).substitute
        (singleTermSubstitution (RawTerm.numeral output)) =
      RawFormula.conj
        (diagonalSubstitutionGraph.apply (RawTerm.numeral output)
          (RawTermVector.cons (RawTerm.numeral input) RawTermVector.nil))
        (target.applyTermRaw (RawTerm.numeral output)) := by
  apply congrArgTwo RawFormula.conj
  · exact diagonalSubstitutionGraph.applyUnaryNumeral_instantiate_raw
      input output
  · exact (Predicate.applyTermRaw_substitute target (RawTerm.bvar 0)
      (singleTermSubstitution (RawTerm.numeral output))).trans rfl

/-- Applying the parametric body to an input code exposes its existential
witness block. -/
theorem internalFixedPointBody_instantiateNumeral_raw_at
    (target : Predicate)
    (code : Nat) :
    (internalFixedPointBody target).raw.instantiateNumeral code =
      RawFormula.ex
        (RawFormula.conj
          (diagonalSubstitutionGraph.apply
            (RawTerm.bvar 0)
            (RawTermVector.cons
              (RawTerm.numeral code)
              RawTermVector.nil))
          (target.applyTermRaw (RawTerm.bvar 0))) := by
  unfold internalFixedPointBody RawFormula.instantiateNumeral
  apply congrArg RawFormula.ex
  apply congrArgTwo RawFormula.conj
  · apply Eq.trans (ArithmeticGraph.apply_substitute
      diagonalSubstitutionGraph (RawTerm.bvar 0)
      (RawTermVector.cons (RawTerm.bvar 1) RawTermVector.nil)
      (liftSubstitution (fun _index => RawTerm.numeral code)))
    apply congrArgTwo diagonalSubstitutionGraph.apply
    · rfl
    · apply congrArg (fun head => RawTermVector.cons head RawTermVector.nil)
      exact RawTerm.numeral_rename _ _
  · exact (Predicate.applyTermRaw_substitute target (RawTerm.bvar 0)
      (liftSubstitution (fun _index => RawTerm.numeral code))).trans rfl

/-- Instantiating the newest variable in a predicate instance yields the lift
of the corresponding closed numeral instance. -/
theorem Predicate.newest_instantiate_numeral_eq_lift_applyNumeral
    (target : Predicate)
    (value : Nat) :
    (target.applyTerm
      (ScopedTerm.bvar 0 (Nat.zero_lt_succ 1))).instantiate
        (ScopedTerm.numeral 1 value) =
      (target.applyNumeral value).scopedFormula.lift := by
  apply ScopedFormula.eq_of_raw_eq
  apply Eq.trans (Predicate.applyTermRaw_substitute target
    (RawTerm.bvar 0)
    (singleTermSubstitution (RawTerm.numeral value)))
  exact congrArg ScopedFormula.raw
    (target.applyTerm_numeral_eq_lift_applyNumeral value)

/-- Left side of the parametric diagonal law for a chosen source predicate. -/
def internalFixedPointLeft
    (target source : Predicate) : Sentence :=
  (internalFixedPointBody target).applyNumeral source.raw.code

/-- Right side of the parametric diagonal law for a chosen source predicate. -/
def internalFixedPointRight
    (target source : Predicate) : Sentence :=
  target.applyNumeral (source.applyNumeral source.raw.code).quote

/-- HA derives the forward direction of the parametric diagonal law. -/
def internalFixedPoint_derivable_forward
    (target source : Predicate) :
    Derivation LogicMode.intuitionistic haTheory FormulaContext.nil
      (ScopedFormula.impl
        (internalFixedPointLeft target source).scopedFormula
        (internalFixedPointRight target source).scopedFormula) := by
  apply Derivation.implicationIntroduction
  let leftFormula := (internalFixedPointLeft target source).scopedFormula
  let leftContext := FormulaContext.cons leftFormula FormulaContext.nil
  let leftProof : Derivation LogicMode.intuitionistic haTheory leftContext
      leftFormula := Derivation.hypothesis ContextMember.here
  let sourceCode := source.raw.code
  let resultSentence := source.applyNumeral sourceCode
  let graphAt := diagonalSubstitutionGraph.apply
    (RawTerm.bvar 0)
    (RawTermVector.cons (RawTerm.numeral sourceCode) RawTermVector.nil)
  let targetAt := target.applyTerm
    (ScopedTerm.bvar 0 (Nat.zero_lt_succ 0))
  let witnessBody : ScopedFormula 1 :=
    ScopedFormula.conj
      { raw := graphAt
        isScoped :=
          diagonalSubstitutionGraph.applyUnaryNumeral_wellScoped sourceCode }
      targetAt
  let normalizedLeft : Derivation LogicMode.intuitionistic haTheory
      leftContext (ScopedFormula.ex witnessBody) := by
    refine Derivation.castConclusion ?_ leftProof
    apply ScopedFormula.eq_of_raw_eq
    change
      (internalFixedPointBody target).raw.instantiateNumeral sourceCode =
        witnessBody.raw.ex
    exact internalFixedPointBody_instantiateNumeral_raw_at target sourceCode
  let witnessContext := FormulaContext.cons witnessBody leftContext.lift
  let witnessProof : Derivation LogicMode.intuitionistic haTheory witnessContext
      witnessBody := Derivation.hypothesis ContextMember.here
  let graphProof := Derivation.conjunctionEliminationLeft witnessProof
  let targetAtWitness := Derivation.conjunctionEliminationRight witnessProof
  let witness := ScopedTerm.bvar 0 (Nat.zero_lt_succ 0)
  let inputs := NatVector.cons sourceCode NatVector.nil
  let normalizedGraph : Derivation LogicMode.intuitionistic haTheory
      witnessContext
      (PRFunction.captureAvoidingDiagonalSubstitution.graphFormula
        |>.numeralApplicationAt inputs witness) := by
    refine Derivation.castConclusion ?_ graphProof
    apply ScopedFormula.eq_of_raw_eq
    rfl
  let forcedRun :=
    PRFunction.captureAvoidingDiagonalSubstitution.internalGraphFunctional
      inputs witness normalizedGraph
  have resultRun :
      resultSentence.quote =
        PRFunction.captureAvoidingDiagonalSubstitution.run inputs := by
    exact PRFunction.captureAvoidingDiagonalSubstitution_evaluates_code
      source.raw
  let normalizeRun := (numeralEqualityProof 1
    (PRFunction.captureAvoidingDiagonalSubstitution.run inputs)
    resultSentence.quote resultRun.symm).weakenClosedTo witnessContext
  let normalizedRunEquality : Derivation LogicMode.intuitionistic haTheory
      witnessContext
      (ScopedFormula.equal
        (ScopedTerm.numeral 1
          (PRFunction.captureAvoidingDiagonalSubstitution.run inputs))
        (ScopedTerm.numeral 1 resultSentence.quote)) := by
    refine Derivation.castConclusion ?_ normalizeRun
    apply ScopedFormula.eq_of_raw_eq
    rfl
  let witnessEqualsResult := Derivation.equalityTransitivity forcedRun
    normalizedRunEquality
  let targetBody : ScopedFormula 2 :=
    target.applyTerm (ScopedTerm.bvar 0 (Nat.zero_lt_succ 1))
  let targetAtWitnessExact : Derivation LogicMode.intuitionistic haTheory
      witnessContext (targetBody.instantiate witness) := by
    refine Derivation.castConclusion ?_ targetAtWitness
    apply ScopedFormula.eq_of_raw_eq
    exact (Predicate.applyTermRaw_substitute target (RawTerm.bvar 0)
      (singleTermSubstitution witness.raw)).symm
  let transportedTarget := Derivation.equalitySubstitution targetBody
    witnessEqualsResult targetAtWitnessExact
  have transportedConclusionExact :
      targetBody.instantiate
          (ScopedTerm.numeral 1 resultSentence.quote) =
        (internalFixedPointRight target source).scopedFormula.lift := by
    exact target.newest_instantiate_numeral_eq_lift_applyNumeral
      resultSentence.quote
  let exactTarget : Derivation LogicMode.intuitionistic haTheory
      witnessContext
      (internalFixedPointRight target source).scopedFormula.lift :=
    Derivation.castConclusion transportedConclusionExact transportedTarget
  exact Derivation.existentialElimination normalizedLeft exactTarget

/-- HA derives the backward direction of the parametric diagonal law. -/
def internalFixedPoint_derivable_backward
    (target source : Predicate) :
    Derivation LogicMode.intuitionistic haTheory FormulaContext.nil
      (ScopedFormula.impl
        (internalFixedPointRight target source).scopedFormula
        (internalFixedPointLeft target source).scopedFormula) := by
  apply Derivation.implicationIntroduction
  let rightFormula := (internalFixedPointRight target source).scopedFormula
  let rightContext := FormulaContext.cons rightFormula FormulaContext.nil
  let rightProof : Derivation LogicMode.intuitionistic haTheory rightContext
      rightFormula := Derivation.hypothesis ContextMember.here
  let sourceCode := source.raw.code
  let resultSentence := source.applyNumeral sourceCode
  let inputs := NatVector.cons sourceCode NatVector.nil
  have evaluation : PRFunction.Evaluates
      PRFunction.captureAvoidingDiagonalSubstitution inputs
        resultSentence.quote := by
    exact PRFunction.captureAvoidingDiagonalSubstitution_evaluates_code source.raw
  let graphProofHA := PRFunction.internalGraphNumeralProof
    PRFunction.captureAvoidingDiagonalSubstitution inputs
      resultSentence.quote evaluation
  let graphProof := graphProofHA.weakenClosedTo rightContext
  let witnessBody : ScopedFormula 1 :=
    ScopedFormula.conj
      { raw := diagonalSubstitutionGraph.apply
          (RawTerm.bvar 0)
          (RawTermVector.cons (RawTerm.numeral sourceCode) RawTermVector.nil)
        isScoped :=
          diagonalSubstitutionGraph.applyUnaryNumeral_wellScoped sourceCode }
      (target.applyTerm
        (ScopedTerm.bvar 0 (Nat.zero_lt_succ 0)))
  let closedGraph : ScopedFormula 0 :=
    { raw := diagonalSubstitutionGraph.apply
        (RawTerm.numeral resultSentence.quote)
        (RawTermVector.cons (RawTerm.numeral sourceCode) RawTermVector.nil)
      isScoped := diagonalSubstitutionGraph.applyUnaryNumerals_wellScoped
        sourceCode resultSentence.quote }
  let graphProofExact : Derivation LogicMode.intuitionistic haTheory
      rightContext closedGraph := by
    refine Derivation.castConclusion ?_ graphProof
    apply ScopedFormula.eq_of_raw_eq
    rfl
  let closedTarget :=
    target.applyTerm (ScopedTerm.numeral 0 resultSentence.quote)
  let rightProofExact : Derivation LogicMode.intuitionistic haTheory
      rightContext closedTarget := by
    refine Derivation.castConclusion ?_ rightProof
    apply ScopedFormula.eq_of_raw_eq
    rfl
  let closedConjunction := Derivation.conjunctionIntroduction
    graphProofExact rightProofExact
  let graphAtResult : Derivation LogicMode.intuitionistic haTheory rightContext
      (witnessBody.instantiate
        (ScopedTerm.numeral 0 resultSentence.quote)) := by
    refine Derivation.castConclusion ?_ closedConjunction
    apply ScopedFormula.eq_of_raw_eq
    exact (internalFixedPointWitnessBody_instantiate_raw target sourceCode
      resultSentence.quote).symm
  let introduced := Derivation.existentialIntroduction
    (body := witnessBody) (ScopedTerm.numeral 0 resultSentence.quote)
    graphAtResult
  refine Derivation.castConclusion ?_ introduced
  apply ScopedFormula.eq_of_raw_eq
  exact (internalFixedPointBody_instantiateNumeral_raw_at
    target sourceCode).symm

/-- HA derivation of the full parametric fixed-point biconditional. -/
def internalFixedPoint_derivable
    (target source : Predicate) :
    Derivation LogicMode.intuitionistic haTheory FormulaContext.nil
      (ScopedFormula.conj
        (ScopedFormula.impl
          (internalFixedPointLeft target source).scopedFormula
          (internalFixedPointRight target source).scopedFormula)
        (ScopedFormula.impl
          (internalFixedPointRight target source).scopedFormula
          (internalFixedPointLeft target source).scopedFormula)) :=
  Derivation.conjunctionIntroduction
    (internalFixedPoint_derivable_forward target source)
    (internalFixedPoint_derivable_backward target source)

end HeytingArithmetic
end RelationalPerimeter

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.HeytingArithmetic.internalFixedPointBody
#print axioms RelationalPerimeter.HeytingArithmetic.internalFixedPointBody_instantiateNumeral_raw_at
#print axioms RelationalPerimeter.HeytingArithmetic.internalFixedPoint_derivable_forward
#print axioms RelationalPerimeter.HeytingArithmetic.internalFixedPoint_derivable_backward
#print axioms RelationalPerimeter.HeytingArithmetic.internalFixedPoint_derivable
/- AXIOM_AUDIT_END -/
