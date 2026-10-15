import RelationalPerimeter.Instances.HeytingArithmetic.InternalAddition
import RelationalPerimeter.Instances.HeytingArithmetic.InternalScopedSubstitution

/-!
# Internally derived strict-order laws of HA

Strict order is the existing existential arithmetic formula
`x < y :⇔ ∃g, x + S g = y`.  Every result below is an object-language
derivation; no semantic reflection rule is used.
-/

namespace RelationalPerimeter
namespace HeytingArithmetic

set_option maxHeartbeats 16000000

/-- A term already shifted away from the newest variable is insensitive to
whether the second shift is expressed under a binder or directly. -/
theorem RawTerm.renameSucc_renameLiftSucc
    (term : RawTerm) :
    (term.rename Nat.succ).rename (liftRenaming Nat.succ) =
      (term.rename Nat.succ).rename Nat.succ := by
  induction term with
  | bvar _index => rfl
  | zero => rfl
  | succ body inductionHypothesis =>
      exact congrArg RawTerm.succ inductionHypothesis
  | add left right leftHypothesis rightHypothesis =>
      exact congrArgTwo RawTerm.add leftHypothesis rightHypothesis
  | mul left right leftHypothesis rightHypothesis =>
      exact congrArgTwo RawTerm.mul leftHypothesis rightHypothesis

theorem RawTerm.renameSuccTwice_substituteLiftSingle
    (term replacement : RawTerm) :
    ((term.rename Nat.succ).rename Nat.succ).substitute
        (liftSubstitution (singleTermSubstitution replacement)) =
      term.rename Nat.succ := by
  induction term with
  | bvar _index => rfl
  | zero => rfl
  | succ body inductionHypothesis =>
      exact congrArg RawTerm.succ inductionHypothesis
  | add left right leftHypothesis rightHypothesis =>
      exact congrArgTwo RawTerm.add leftHypothesis rightHypothesis
  | mul left right leftHypothesis rightHypothesis =>
      exact congrArgTwo RawTerm.mul leftHypothesis rightHypothesis

theorem RawTerm.renameSuccTwice_substituteLiftKeeping
    (term : RawTerm) :
    ((term.rename Nat.succ).rename Nat.succ).substitute
        (liftSubstitution
          ScopedFormula.replaceNewestKeepingScopeSubstitution) =
      (term.rename Nat.succ).rename Nat.succ := by
  induction term with
  | bvar _index => rfl
  | zero => rfl
  | succ body inductionHypothesis =>
      exact congrArg RawTerm.succ inductionHypothesis
  | add left right leftHypothesis rightHypothesis =>
      exact congrArgTwo RawTerm.add leftHypothesis rightHypothesis
  | mul left right leftHypothesis rightHypothesis =>
      exact congrArgTwo RawTerm.mul leftHypothesis rightHypothesis

def scopedLessThanFormulaAt
    {bound : Nat}
    (left right : ScopedTerm bound) : ScopedFormula bound :=
  { raw := lessThanFormula left.raw right.raw
    isScoped := lessThanFormula_wellScoped left.raw right.raw
      left.isScoped right.isScoped }

theorem scopedLessThanFormulaAt_lift
    {bound : Nat}
    (left right : ScopedTerm bound) :
    scopedLessThanFormulaAt left.lift right.lift =
      (scopedLessThanFormulaAt left right).lift := by
  apply ScopedFormula.eq_of_raw_eq
  change
    (lessThanFormula (left.raw.rename Nat.succ)
        (right.raw.rename Nat.succ)) =
      (lessThanFormula left.raw right.raw).rename Nat.succ
  apply congrArg RawFormula.ex
  apply congrArgTwo RawFormula.equal
  · exact congrArgTwo RawTerm.add
      (RawTerm.renameSucc_renameLiftSucc left.raw).symm rfl
  · exact (RawTerm.renameSucc_renameLiftSucc right.raw).symm

/-- Introduce the strict-order witness carried by
`left + S(gap) = right`, entirely inside the object calculus. -/
def lessThanIntroductionAt
    {bound : Nat}
    {context : FormulaContext bound}
    (left right gap : ScopedTerm bound)
    (equation : Derivation LogicMode.intuitionistic haTheory context
      (ScopedFormula.equal (ScopedTerm.add left gap.succ) right)) :
    Derivation LogicMode.intuitionistic haTheory context
      (scopedLessThanFormulaAt left right) := by
  let body : ScopedFormula (Nat.succ bound) :=
    ScopedFormula.equal
      (ScopedTerm.add left.lift
        (ScopedTerm.succ
          (ScopedTerm.bvar 0 (Nat.zero_lt_succ bound))))
      right.lift
  have instantiated : Derivation LogicMode.intuitionistic haTheory context
      (body.instantiate gap) := by
    simpa [body, ScopedFormula.instantiate, ScopedTerm.instantiate,
      RawFormula.instantiateTerm, RawTerm.instantiateTerm,
      RawFormula.substitute, RawTerm.substitute,
      singleTermSubstitution, ScopedFormula.equal,
      ScopedTerm.bvar, ScopedTerm.add, ScopedTerm.succ, ScopedTerm.lift,
      RawTerm.rename, RawTerm.renameSucc_substituteSingle] using equation
  let introduced := Derivation.existentialIntroduction
    (body := body) gap instantiated
  simpa [scopedLessThanFormulaAt, lessThanFormula, body,
    ScopedFormula.ex, ScopedFormula.equal, ScopedTerm.bvar,
    ScopedTerm.add, ScopedTerm.succ, ScopedTerm.lift,
    RawTerm.shift, RawTerm.rename]
    using introduced

def noAddSuccessorSelfUniversal
    {bound : Nat}
    (gap : ScopedTerm bound) :
    Derivation LogicMode.intuitionistic haTheory FormulaContext.nil
      (ScopedFormula.all
        (let value := ScopedTerm.bvar 0 (Nat.zero_lt_succ bound)
         ScopedFormula.neg
          (ScopedFormula.equal
            (ScopedTerm.add value gap.lift.succ) value))) := by
  let value := ScopedTerm.bvar 0 (Nat.zero_lt_succ bound)
  let body : ScopedFormula (Nat.succ bound) :=
    ScopedFormula.neg
      (ScopedFormula.equal (ScopedTerm.add value gap.lift.succ) value)
  let baseEquality := zeroAddProof gap.succ
  let successorNonzero : Derivation LogicMode.intuitionistic haTheory
      FormulaContext.nil
      (ScopedFormula.neg
        (ScopedFormula.equal gap.succ (ScopedTerm.zero bound))) :=
    Derivation.theoryAxiom
      (StandardArithmeticAxiom.successorNotZero gap)
  let base : Derivation LogicMode.intuitionistic haTheory FormulaContext.nil
      (body.instantiate (ScopedTerm.zero bound)) := by
    let normalizedBase : Derivation LogicMode.intuitionistic haTheory
        FormulaContext.nil
        (ScopedFormula.neg
          (ScopedFormula.equal
            (ScopedTerm.add (ScopedTerm.zero bound) gap.succ)
            (ScopedTerm.zero bound))) := by
      apply Derivation.implicationIntroduction
      let equalityContext := FormulaContext.cons
        (ScopedFormula.equal
          (ScopedTerm.add (ScopedTerm.zero bound) gap.succ)
          (ScopedTerm.zero bound)) FormulaContext.nil
      let hypothesis : Derivation LogicMode.intuitionistic haTheory equalityContext
          (ScopedFormula.equal
            (ScopedTerm.add (ScopedTerm.zero bound) gap.succ)
            (ScopedTerm.zero bound)) :=
        Derivation.hypothesis ContextMember.here
      let normalized := Derivation.equalityTransitivity
        (Derivation.equalitySymmetry
          (baseEquality.weakenClosedTo equalityContext)) hypothesis
      exact Derivation.implicationElimination
        (successorNonzero.weakenClosedTo equalityContext) normalized
    simpa [body, value, ScopedFormula.instantiate, ScopedTerm.instantiate,
      RawFormula.instantiateTerm, RawTerm.instantiateTerm,
      RawFormula.substitute, RawTerm.substitute,
      singleTermSubstitution, ScopedFormula.neg, ScopedFormula.impl,
      ScopedFormula.equal, ScopedFormula.falsum, ScopedTerm.bvar,
      ScopedTerm.add, ScopedTerm.succ,
      ScopedTerm.zero, ScopedTerm.lift, RawTerm.rename,
      RawTerm.renameSucc_substituteSingle] using normalizedBase
  let step : Derivation LogicMode.intuitionistic haTheory FormulaContext.nil
      (ScopedFormula.all
        (ScopedFormula.impl body body.successorInstance)) := by
    apply Derivation.universalIntroduction
    apply Derivation.implicationIntroduction
    let targetEquality := ScopedFormula.equal
      (ScopedTerm.add value.succ gap.lift.succ) value.succ
    let stepContext := FormulaContext.cons body FormulaContext.nil
    let normalizedStep : Derivation LogicMode.intuitionistic haTheory stepContext
        (ScopedFormula.neg targetEquality) := by
      apply Derivation.implicationIntroduction
      let targetContext := FormulaContext.cons targetEquality stepContext
      let inductionHypothesis : Derivation LogicMode.intuitionistic haTheory
          targetContext body :=
        Derivation.weaken targetEquality
          (Derivation.hypothesis ContextMember.here)
      let equalityHypothesis : Derivation LogicMode.intuitionistic haTheory
          targetContext targetEquality :=
        Derivation.hypothesis ContextMember.here
      let unfoldLeft := (successorAddProof value gap.lift.succ)
        |>.weakenClosedTo targetContext
      let successorEquality := Derivation.equalityTransitivity
        (Derivation.equalitySymmetry unfoldLeft) equalityHypothesis
      let predecessorEquality := Derivation.implicationElimination
        (Derivation.theoryAxiom
          (StandardArithmeticAxiom.successorInjective
            (ScopedTerm.add value gap.lift.succ) value))
        successorEquality
      exact Derivation.implicationElimination
        inductionHypothesis predecessorEquality
    simpa [targetEquality, body, value, stepContext, FormulaContext.lift,
      ScopedFormula.successorInstance,
      ScopedFormula.replaceNewestKeepingScopeSubstitution,
      RawFormula.substitute, RawTerm.substitute,
      ScopedFormula.equal, ScopedFormula.neg, ScopedFormula.impl,
      ScopedFormula.falsum, ScopedTerm.bvar, ScopedTerm.add,
      ScopedTerm.succ, ScopedTerm.lift,
      RawTerm.rename, RawTerm.renameSucc_substituteKeepingScope]
      using normalizedStep
  exact Derivation.byArithmeticInduction body (by
    simpa [body, ScopedFormula.instantiate, ScopedTerm.instantiate,
      RawFormula.instantiateTerm, RawTerm.instantiateTerm,
      RawFormula.substitute, RawTerm.substitute,
      singleTermSubstitution, ScopedTerm.add, ScopedTerm.succ,
      ScopedTerm.zero, ScopedTerm.lift, RawTerm.rename,
      RawTerm.renameSucc_substituteSingle] using base) step

def noAddSuccessorSelfProof
    {bound : Nat}
    (value gap : ScopedTerm bound) :
    Derivation LogicMode.intuitionistic haTheory FormulaContext.nil
      (ScopedFormula.neg
        (ScopedFormula.equal
          (ScopedTerm.add value gap.succ) value)) := by
  let instantiated := Derivation.universalElimination value
    (noAddSuccessorSelfUniversal gap)
  apply Derivation.castConclusion ?_ instantiated
  apply ScopedFormula.eq_of_raw_eq
  dsimp [ScopedFormula.instantiate, ScopedTerm.instantiate,
    RawFormula.instantiateTerm, RawTerm.instantiateTerm,
    RawFormula.substitute, RawTerm.substitute,
    singleTermSubstitution, ScopedFormula.neg, ScopedFormula.impl,
    ScopedFormula.equal, ScopedFormula.falsum,
    ScopedTerm.add, ScopedTerm.succ,
    ScopedTerm.bvar, ScopedTerm.lift, RawTerm.rename, RawTerm.raise]
  rw [RawTerm.renameSucc_substituteSingle gap.raw value.raw]

def lessThanIrreflexiveProof
    {bound : Nat}
    (value : ScopedTerm bound) :
    Derivation LogicMode.intuitionistic haTheory FormulaContext.nil
      (ScopedFormula.neg (scopedLessThanFormulaAt value value)) := by
  apply Derivation.implicationIntroduction
  let lessFormula := scopedLessThanFormulaAt value value
  let lessContext := FormulaContext.cons lessFormula FormulaContext.nil
  let lessHypothesis : Derivation LogicMode.intuitionistic haTheory lessContext
      lessFormula := Derivation.hypothesis ContextMember.here
  let witnessBody : ScopedFormula (Nat.succ bound) :=
    ScopedFormula.equal
      (ScopedTerm.add value.lift
        (ScopedTerm.succ
          (ScopedTerm.bvar 0 (Nat.zero_lt_succ bound))))
      value.lift
  let witnessContext := FormulaContext.cons witnessBody lessContext.lift
  let equationHypothesis : Derivation LogicMode.intuitionistic haTheory
      witnessContext witnessBody := Derivation.hypothesis ContextMember.here
  let impossible := (noAddSuccessorSelfProof value.lift
    (ScopedTerm.bvar 0 (Nat.zero_lt_succ bound)))
    |>.weakenClosedTo witnessContext
  let contradiction := Derivation.implicationElimination impossible
    equationHypothesis
  have lessExact : lessFormula = ScopedFormula.ex witnessBody := by
    apply ScopedFormula.eq_of_raw_eq
    rfl
  let normalizedLess := Derivation.castConclusion lessExact lessHypothesis
  have liftedContradiction : Derivation LogicMode.intuitionistic haTheory
      witnessContext (ScopedFormula.falsum bound).lift := by
    simpa [ScopedFormula.falsum, ScopedFormula.lift,
      RawFormula.rename] using contradiction
  let eliminated := Derivation.existentialElimination
    (body := witnessBody)
    (conclusion := ScopedFormula.falsum bound)
    normalizedLess liftedContradiction
  simpa [lessFormula, lessContext, scopedLessThanFormulaAt, lessThanFormula,
    witnessBody, ScopedFormula.neg, ScopedFormula.impl,
    ScopedFormula.lift, ScopedTerm.lift,
    RawFormula.rename, RawTerm.rename, RawTerm.shift] using eliminated

def lessThanAndEqualityContradiction
    {bound : Nat}
    {context : FormulaContext bound}
    (left right : ScopedTerm bound)
    (strict : Derivation LogicMode.intuitionistic haTheory context
      (scopedLessThanFormulaAt left right))
    (equal : Derivation LogicMode.intuitionistic haTheory context
      (ScopedFormula.equal left right)) :
    Derivation LogicMode.intuitionistic haTheory context
      (ScopedFormula.falsum bound) := by
  let witnessBody : ScopedFormula (Nat.succ bound) :=
    ScopedFormula.equal
      (ScopedTerm.add left.lift
        (ScopedTerm.succ
          (ScopedTerm.bvar 0 (Nat.zero_lt_succ bound))))
      right.lift
  have strictExact : scopedLessThanFormulaAt left right =
      ScopedFormula.ex witnessBody := by
    apply ScopedFormula.eq_of_raw_eq
    rfl
  let normalizedStrict := Derivation.castConclusion strictExact strict
  let witnessContext := FormulaContext.cons witnessBody context.lift
  let equation : Derivation LogicMode.intuitionistic haTheory witnessContext
      witnessBody := Derivation.hypothesis ContextMember.here
  let liftedEquality := Derivation.weaken witnessBody
    (Derivation.liftVariables equal)
  have explicitEquality : Derivation LogicMode.intuitionistic haTheory
      witnessContext
      (ScopedFormula.equal left.lift right.lift) := by
    simpa [witnessContext, ScopedFormula.equal, ScopedFormula.lift,
      ScopedTerm.lift,
      RawFormula.rename, RawTerm.rename] using liftedEquality
  let selfEquation := Derivation.equalityTransitivity equation
    (Derivation.equalitySymmetry explicitEquality)
  let impossible := (noAddSuccessorSelfProof left.lift
    (ScopedTerm.bvar 0 (Nat.zero_lt_succ bound)))
    |>.weakenClosedTo witnessContext
  let contradiction := Derivation.implicationElimination impossible
    selfEquation
  have liftedContradiction : Derivation LogicMode.intuitionistic haTheory
      witnessContext (ScopedFormula.falsum bound).lift := by
    simpa [ScopedFormula.falsum, ScopedFormula.lift,
      RawFormula.rename] using contradiction
  exact Derivation.existentialElimination
    (body := witnessBody)
    (conclusion := ScopedFormula.falsum bound)
    normalizedStrict liftedContradiction

def zeroLessSuccessorProof
    {bound : Nat}
    (value : ScopedTerm bound) :
    Derivation LogicMode.intuitionistic haTheory FormulaContext.nil
      (scopedLessThanFormulaAt (ScopedTerm.zero bound) value.succ) := by
  let body : ScopedFormula (Nat.succ bound) :=
    ScopedFormula.equal
      (ScopedTerm.add (ScopedTerm.zero _)
        (ScopedTerm.succ
          (ScopedTerm.bvar 0 (Nat.zero_lt_succ bound))))
      value.succ.lift
  let equality := zeroAddProof value.succ
  exact lessThanIntroductionAt (ScopedTerm.zero bound) value.succ value equality

def lessThanSuccessorSelfProof
    {bound : Nat}
    (value : ScopedTerm bound) :
    Derivation LogicMode.intuitionistic haTheory FormulaContext.nil
      (scopedLessThanFormulaAt value value.succ) := by
  let unfold : Derivation LogicMode.intuitionistic haTheory FormulaContext.nil
      (ScopedFormula.equal
        (ScopedTerm.add value (ScopedTerm.zero bound).succ)
        (ScopedTerm.succ
          (ScopedTerm.add value (ScopedTerm.zero bound)))) :=
    Derivation.theoryAxiom
    (context := FormulaContext.nil)
    (StandardArithmeticAxiom.addSuccessor value (ScopedTerm.zero bound))
  let normalize : Derivation LogicMode.intuitionistic haTheory FormulaContext.nil
      (ScopedFormula.equal
        (ScopedTerm.succ
          (ScopedTerm.add value (ScopedTerm.zero bound))) value.succ) :=
    successorCongruenceAt
    (Derivation.theoryAxiom
      (mode := LogicMode.intuitionistic)
      (theory := haTheory)
      (context := FormulaContext.nil)
      (StandardArithmeticAxiom.addZero value))
  let equality := Derivation.equalityTransitivity unfold normalize
  exact lessThanIntroductionAt value value.succ
    (ScopedTerm.zero bound) equality

def successorLessSuccessorOfLessAt
    {bound : Nat}
    {context : FormulaContext bound}
    (left right : ScopedTerm bound)
    (strict : Derivation LogicMode.intuitionistic haTheory context
      (scopedLessThanFormulaAt left right)) :
    Derivation LogicMode.intuitionistic haTheory context
      (scopedLessThanFormulaAt left.succ right.succ) := by
  let witnessBody : ScopedFormula (Nat.succ bound) :=
    ScopedFormula.equal
      (ScopedTerm.add left.lift
        (ScopedTerm.succ
          (ScopedTerm.bvar 0 (Nat.zero_lt_succ bound))))
      right.lift
  let witnessContext := FormulaContext.cons witnessBody context.lift
  let equation : Derivation LogicMode.intuitionistic haTheory witnessContext
      witnessBody := Derivation.hypothesis ContextMember.here
  let gap := ScopedTerm.bvar 0 (Nat.zero_lt_succ bound)
  let unfold := (successorAddProof left.lift gap.succ)
    |>.weakenClosedTo witnessContext
  let liftEquation := successorCongruenceAt equation
  let resultEquation := Derivation.equalityTransitivity unfold liftEquation
  let branchStrict := lessThanIntroductionAt left.lift.succ
    right.lift.succ gap resultEquation
  have strictExact : scopedLessThanFormulaAt left right =
      ScopedFormula.ex witnessBody := by
    apply ScopedFormula.eq_of_raw_eq
    rfl
  let normalizedStrict := Derivation.castConclusion strictExact strict
  have branch : Derivation LogicMode.intuitionistic haTheory witnessContext
      (scopedLessThanFormulaAt left.succ right.succ).lift := by
    apply Derivation.castConclusion
      (scopedLessThanFormulaAt_lift left.succ right.succ)
    simpa [ScopedTerm.lift, ScopedTerm.succ, RawTerm.rename]
      using branchStrict
  exact Derivation.existentialElimination
    (body := witnessBody)
    (conclusion := scopedLessThanFormulaAt left.succ right.succ)
    normalizedStrict branch

def lessThanSuccessorRightOfLessAt
    {bound : Nat}
    {context : FormulaContext bound}
    (left right : ScopedTerm bound)
    (strict : Derivation LogicMode.intuitionistic haTheory context
      (scopedLessThanFormulaAt left right)) :
    Derivation LogicMode.intuitionistic haTheory context
      (scopedLessThanFormulaAt left right.succ) := by
  let witnessBody : ScopedFormula (Nat.succ bound) :=
    ScopedFormula.equal
      (ScopedTerm.add left.lift
        (ScopedTerm.succ
          (ScopedTerm.bvar 0 (Nat.zero_lt_succ bound))))
      right.lift
  let witnessContext := FormulaContext.cons witnessBody context.lift
  let equation : Derivation LogicMode.intuitionistic haTheory witnessContext
      witnessBody := Derivation.hypothesis ContextMember.here
  let gap := ScopedTerm.bvar 0 (Nat.zero_lt_succ bound)
  let unfold : Derivation LogicMode.intuitionistic haTheory witnessContext
      (ScopedFormula.equal
        (ScopedTerm.add left.lift gap.succ.succ)
        (ScopedTerm.succ (ScopedTerm.add left.lift gap.succ))) :=
    Derivation.theoryAxiom
      (StandardArithmeticAxiom.addSuccessor left.lift gap.succ)
  let liftEquation := successorCongruenceAt equation
  let resultEquation := Derivation.equalityTransitivity unfold liftEquation
  let branchStrict := lessThanIntroductionAt left.lift right.lift.succ
    gap.succ resultEquation
  have strictExact : scopedLessThanFormulaAt left right =
      ScopedFormula.ex witnessBody := by
    apply ScopedFormula.eq_of_raw_eq
    rfl
  let normalizedStrict := Derivation.castConclusion strictExact strict
  have branch : Derivation LogicMode.intuitionistic haTheory witnessContext
      (scopedLessThanFormulaAt left right.succ).lift := by
    apply Derivation.castConclusion
      (scopedLessThanFormulaAt_lift left right.succ)
    simpa [ScopedTerm.lift, ScopedTerm.succ, RawTerm.rename]
      using branchStrict
  exact Derivation.existentialElimination
    (body := witnessBody)
    (conclusion := scopedLessThanFormulaAt left right.succ)
    normalizedStrict branch

def orderTrichotomyFormula
    {bound : Nat}
    (left right : ScopedTerm bound) : ScopedFormula bound :=
  ScopedFormula.disj
    (scopedLessThanFormulaAt left right)
    (ScopedFormula.disj
      (ScopedFormula.equal left right)
      (scopedLessThanFormulaAt right left))

theorem orderTrichotomyFormula_lift
    {bound : Nat}
    (left right : ScopedTerm bound) :
    orderTrichotomyFormula left.lift right.lift =
      (orderTrichotomyFormula left right).lift := by
  apply ScopedFormula.eq_of_raw_eq
  apply congrArgTwo RawFormula.disj
  · exact congrArg ScopedFormula.raw
      (scopedLessThanFormulaAt_lift left right)
  · apply congrArgTwo RawFormula.disj
    · rfl
    · exact congrArg ScopedFormula.raw
        (scopedLessThanFormulaAt_lift right left)

def successorTrichotomyAt
    {bound : Nat}
    {context : FormulaContext bound}
    (left right : ScopedTerm bound)
    (casesProof : Derivation LogicMode.intuitionistic haTheory context
      (orderTrichotomyFormula left right)) :
    Derivation LogicMode.intuitionistic haTheory context
      (orderTrichotomyFormula left.succ right.succ) := by
  let leftStrict := scopedLessThanFormulaAt left right
  let equality := ScopedFormula.equal left right
  let rightStrict := scopedLessThanFormulaAt right left
  let leftContext := FormulaContext.cons leftStrict context
  let leftHypothesis : Derivation LogicMode.intuitionistic haTheory leftContext
      leftStrict := Derivation.hypothesis ContextMember.here
  let leftMapped := successorLessSuccessorOfLessAt left right leftHypothesis
  let leftBranch := Derivation.disjunctionIntroductionLeft
    (right := ScopedFormula.disj
      (ScopedFormula.equal left.succ right.succ)
      (scopedLessThanFormulaAt right.succ left.succ)) leftMapped
  let middleContext := FormulaContext.cons
    (ScopedFormula.disj equality rightStrict) context
  let middleHypothesis : Derivation LogicMode.intuitionistic haTheory middleContext
      (ScopedFormula.disj equality rightStrict) :=
    Derivation.hypothesis ContextMember.here
  let equalityContext := FormulaContext.cons equality middleContext
  let equalityHypothesis : Derivation LogicMode.intuitionistic haTheory
      equalityContext equality := Derivation.hypothesis ContextMember.here
  let equalityMapped := successorCongruenceAt equalityHypothesis
  let equalityInner := Derivation.disjunctionIntroductionLeft
    (right := scopedLessThanFormulaAt right.succ left.succ)
    equalityMapped
  let equalityBranch : Derivation LogicMode.intuitionistic haTheory
      equalityContext (orderTrichotomyFormula left.succ right.succ) :=
    Derivation.disjunctionIntroductionRight
    (left := scopedLessThanFormulaAt left.succ right.succ)
    equalityInner
  let rightContext := FormulaContext.cons rightStrict middleContext
  let rightHypothesis : Derivation LogicMode.intuitionistic haTheory rightContext
      rightStrict := Derivation.hypothesis ContextMember.here
  let rightMapped := successorLessSuccessorOfLessAt right left rightHypothesis
  let rightInner := Derivation.disjunctionIntroductionRight
    (left := ScopedFormula.equal left.succ right.succ) rightMapped
  let rightBranch : Derivation LogicMode.intuitionistic haTheory rightContext
      (orderTrichotomyFormula left.succ right.succ) :=
    Derivation.disjunctionIntroductionRight
    (left := scopedLessThanFormulaAt left.succ right.succ)
    rightInner
  let middleBranch := Derivation.disjunctionElimination middleHypothesis
    equalityBranch rightBranch
  exact Derivation.disjunctionElimination casesProof leftBranch middleBranch

def zeroTrichotomyUniversal
    {bound : Nat} :
    Derivation LogicMode.intuitionistic haTheory FormulaContext.nil
      (ScopedFormula.all
        (let right := ScopedTerm.bvar 0 (Nat.zero_lt_succ bound)
         orderTrichotomyFormula (ScopedTerm.zero (Nat.succ bound)) right)) := by
  let right := ScopedTerm.bvar 0 (Nat.zero_lt_succ bound)
  let body : ScopedFormula (Nat.succ bound) :=
    orderTrichotomyFormula (ScopedTerm.zero (Nat.succ bound)) right
  let baseEquality : Derivation LogicMode.intuitionistic haTheory
      FormulaContext.nil
      (ScopedFormula.equal (ScopedTerm.zero bound) (ScopedTerm.zero bound)) :=
    Derivation.equalityReflexivity (ScopedTerm.zero bound)
  let base : Derivation LogicMode.intuitionistic haTheory FormulaContext.nil
      (orderTrichotomyFormula
        (ScopedTerm.zero bound) (ScopedTerm.zero bound)) :=
    Derivation.disjunctionIntroductionRight
    (left := scopedLessThanFormulaAt
      (ScopedTerm.zero bound) (ScopedTerm.zero bound))
    (Derivation.disjunctionIntroductionLeft
      (right := scopedLessThanFormulaAt
        (ScopedTerm.zero bound) (ScopedTerm.zero bound)) baseEquality)
  let step : Derivation LogicMode.intuitionistic haTheory FormulaContext.nil
      (ScopedFormula.all
        (ScopedFormula.impl body body.successorInstance)) := by
    apply Derivation.universalIntroduction
    apply Derivation.implicationIntroduction
    let stepContext := FormulaContext.cons body FormulaContext.nil.lift
    let strict := (zeroLessSuccessorProof right).weakenClosedTo stepContext
    let result : Derivation LogicMode.intuitionistic haTheory stepContext
        (orderTrichotomyFormula
          (ScopedTerm.zero (Nat.succ bound)) right.succ) :=
      Derivation.disjunctionIntroductionLeft
        (right := ScopedFormula.disj
          (ScopedFormula.equal
            (ScopedTerm.zero (Nat.succ bound)) right.succ)
          (scopedLessThanFormulaAt right.succ
            (ScopedTerm.zero (Nat.succ bound)))) strict
    simpa [body, right, stepContext, orderTrichotomyFormula,
      ScopedFormula.successorInstance,
      ScopedFormula.replaceNewestKeepingScopeSubstitution,
      scopedLessThanFormulaAt, lessThanFormula,
      RawFormula.substitute, RawTerm.substitute, liftSubstitution,
      ScopedFormula.disj, ScopedFormula.ex, ScopedFormula.equal,
      ScopedTerm.bvar, ScopedTerm.succ, ScopedTerm.zero,
      ScopedTerm.lift, RawFormula.rename, RawTerm.rename,
      RawTerm.shift] using result
  exact Derivation.byArithmeticInduction body (by
    simpa [body, right, orderTrichotomyFormula,
      ScopedFormula.instantiate, ScopedTerm.instantiate,
      RawFormula.instantiateTerm, RawTerm.instantiateTerm,
      RawFormula.substitute, RawTerm.substitute,
      singleTermSubstitution, liftSubstitution, ScopedFormula.disj,
      ScopedFormula.ex,
      ScopedFormula.equal, ScopedTerm.bvar, ScopedTerm.zero,
      scopedLessThanFormulaAt, lessThanFormula,
      RawTerm.shift, RawTerm.rename,
      RawTerm.renameSucc_substituteSingle] using base) step

def orderTrichotomyUniversal
    {bound : Nat} :
    Derivation LogicMode.intuitionistic haTheory FormulaContext.nil
      (ScopedFormula.all
        (let left := ScopedTerm.bvar 0 (Nat.zero_lt_succ bound)
         ScopedFormula.all
          (let right := ScopedTerm.bvar 0
            (Nat.zero_lt_succ (Nat.succ bound))
           orderTrichotomyFormula left.lift right))) := by
  let left := ScopedTerm.bvar 0 (Nat.zero_lt_succ bound)
  let right := ScopedTerm.bvar 0
    (Nat.zero_lt_succ (Nat.succ bound))
  let outerBody : ScopedFormula (Nat.succ bound) :=
    ScopedFormula.all (orderTrichotomyFormula left.lift right)
  let base : Derivation LogicMode.intuitionistic haTheory FormulaContext.nil
      (outerBody.instantiate (ScopedTerm.zero bound)) := by
    simpa [outerBody, left, right, orderTrichotomyFormula,
      ScopedFormula.instantiate, ScopedTerm.instantiate,
      RawFormula.instantiateTerm, RawTerm.instantiateTerm,
      RawFormula.substitute, RawTerm.substitute,
      singleTermSubstitution, liftSubstitution, ScopedFormula.all,
      ScopedFormula.disj, ScopedFormula.ex, ScopedFormula.equal,
      ScopedTerm.bvar, ScopedTerm.zero, ScopedTerm.lift,
      RawTerm.rename, scopedLessThanFormulaAt, lessThanFormula,
      RawTerm.shift] using (zeroTrichotomyUniversal (bound := bound))
  let step : Derivation LogicMode.intuitionistic haTheory FormulaContext.nil
      (ScopedFormula.all
        (ScopedFormula.impl outerBody outerBody.successorInstance)) := by
    apply Derivation.universalIntroduction
    apply Derivation.implicationIntroduction
    let outerContext := FormulaContext.cons outerBody FormulaContext.nil
    let outerHypothesis : Derivation LogicMode.intuitionistic haTheory outerContext
        outerBody := Derivation.hypothesis ContextMember.here
    let innerBody : ScopedFormula (Nat.succ (Nat.succ bound)) :=
      orderTrichotomyFormula left.lift.succ right
    let innerBaseStrict := zeroLessSuccessorProof left
    let innerBase : Derivation LogicMode.intuitionistic haTheory
        outerContext
        (orderTrichotomyFormula left.succ
          (ScopedTerm.zero (Nat.succ bound))) :=
      Derivation.disjunctionIntroductionRight
      (left := scopedLessThanFormulaAt left.succ
        (ScopedTerm.zero (Nat.succ bound)))
      (Derivation.disjunctionIntroductionRight
        (left := ScopedFormula.equal left.succ
          (ScopedTerm.zero (Nat.succ bound)))
        innerBaseStrict)
      |>.weakenClosedTo outerContext
    let innerStep : Derivation LogicMode.intuitionistic haTheory outerContext
        (ScopedFormula.all
          (ScopedFormula.impl innerBody innerBody.successorInstance)) := by
      apply Derivation.universalIntroduction
      apply Derivation.implicationIntroduction
      let innerContext := FormulaContext.cons innerBody outerContext.lift
      let liftedOuter : Derivation LogicMode.intuitionistic haTheory
          outerContext.lift outerBody.lift :=
        Derivation.liftVariables outerHypothesis
      let outerRight := ScopedTerm.bvar 0
        (Nat.zero_lt_succ (Nat.succ (Nat.succ bound)))
      have liftedOuterUniversal : Derivation LogicMode.intuitionistic haTheory
          outerContext.lift
          (ScopedFormula.all
            (orderTrichotomyFormula left.lift.lift outerRight)) := by
        apply Derivation.castConclusion ?_ liftedOuter
        apply ScopedFormula.eq_of_raw_eq
        rfl
      let outerAtRight := Derivation.universalElimination right
        liftedOuterUniversal
      let outerAtRightInContext := Derivation.weaken innerBody outerAtRight
      let mapped := successorTrichotomyAt left.lift right
        outerAtRightInContext
      simpa [innerBody, outerBody, right, orderTrichotomyFormula,
        ScopedFormula.successorInstance,
        ScopedFormula.replaceNewestKeepingScopeSubstitution,
        ScopedFormula.instantiate, ScopedTerm.instantiate,
        RawFormula.instantiateTerm, RawTerm.instantiateTerm,
        RawFormula.substitute, RawTerm.substitute, liftSubstitution,
        singleTermSubstitution, ScopedFormula.disj, ScopedFormula.ex,
        ScopedFormula.equal, ScopedFormula.lift, ScopedTerm.lift,
        RawFormula.rename, RawTerm.rename, ScopedTerm.bvar, ScopedTerm.succ,
        scopedLessThanFormulaAt, lessThanFormula, RawTerm.shift,
        RawTerm.renameSuccTwice_substituteLiftKeeping,
        RawTerm.renameSucc_substituteKeepingScope]
        using mapped
    let innerUniversal := Derivation.byArithmeticInductionAt innerBody
      (by
        simpa [innerBody, left, right, orderTrichotomyFormula,
          ScopedFormula.instantiate, ScopedTerm.instantiate,
          RawFormula.instantiateTerm, RawTerm.instantiateTerm,
          RawFormula.substitute, RawTerm.substitute,
          singleTermSubstitution, liftSubstitution, ScopedFormula.disj,
          ScopedFormula.ex, ScopedFormula.equal, ScopedTerm.bvar,
          ScopedTerm.zero, ScopedTerm.succ, ScopedTerm.lift,
          RawTerm.rename, scopedLessThanFormulaAt, lessThanFormula,
          RawTerm.shift] using innerBase)
      innerStep
    simpa [outerBody, innerBody, left, right, outerContext,
      FormulaContext.lift,
      ScopedFormula.successorInstance,
      ScopedFormula.replaceNewestKeepingScopeSubstitution,
      orderTrichotomyFormula, RawFormula.substitute,
      RawTerm.substitute, liftSubstitution, ScopedFormula.all,
      ScopedFormula.disj, ScopedFormula.ex, ScopedFormula.equal,
      ScopedFormula.lift, ScopedTerm.lift,
      RawFormula.rename, RawTerm.rename, ScopedTerm.bvar, ScopedTerm.succ,
      scopedLessThanFormulaAt, lessThanFormula, RawTerm.shift]
      using innerUniversal
  exact Derivation.byArithmeticInduction outerBody base step

def orderTrichotomyProof
    {bound : Nat}
    (left right : ScopedTerm bound) :
    Derivation LogicMode.intuitionistic haTheory FormulaContext.nil
      (orderTrichotomyFormula left right) := by
  let atLeft := Derivation.universalElimination left
    (orderTrichotomyUniversal (bound := bound))
  let rightVariable := ScopedTerm.bvar 0 (Nat.zero_lt_succ bound)
  have atLeftUniversal : Derivation LogicMode.intuitionistic haTheory
      FormulaContext.nil
      (ScopedFormula.all
        (orderTrichotomyFormula left.lift rightVariable)) := by
    apply Derivation.castConclusion ?_ atLeft
    apply ScopedFormula.eq_of_raw_eq
    rfl
  let atRight := Derivation.universalElimination right atLeftUniversal
  apply Derivation.castConclusion ?_ atRight
  apply ScopedFormula.eq_of_raw_eq
  dsimp [orderTrichotomyFormula, scopedLessThanFormulaAt,
    lessThanFormula, ScopedFormula.instantiate,
    ScopedTerm.instantiate, RawFormula.instantiateTerm,
    RawTerm.instantiateTerm, RawFormula.substitute,
    RawTerm.substitute, singleTermSubstitution,
    ScopedFormula.disj, ScopedFormula.equal, ScopedFormula.ex,
    ScopedFormula.lift, ScopedTerm.lift, ScopedTerm.bvar,
    RawFormula.rename, RawTerm.rename, RawTerm.raise, RawTerm.shift,
    liftSubstitution]
  repeat' rw [RawTerm.renameSuccTwice_substituteLiftSingle]
  repeat' rw [RawTerm.renameSucc_substituteSingle]
  have newestExact : rightVariable.raw.substitute
      (singleTermSubstitution right.raw) = right.raw := by
    rfl
  have liftedNewestExact :
      (rightVariable.raw.rename Nat.succ).substitute
          (liftSubstitution (singleTermSubstitution right.raw)) =
        right.raw.rename Nat.succ := by
    rfl
  rw [newestExact, liftedNewestExact]

def lessThanTransportLeftAt
    {bound : Nat}
    {context : FormulaContext bound}
    (left replacement right : ScopedTerm bound)
    (equality : Derivation LogicMode.intuitionistic haTheory context
      (ScopedFormula.equal left replacement))
    (strict : Derivation LogicMode.intuitionistic haTheory context
      (scopedLessThanFormulaAt left right)) :
    Derivation LogicMode.intuitionistic haTheory context
      (scopedLessThanFormulaAt replacement right) := by
  let witnessBody : ScopedFormula (Nat.succ bound) :=
    ScopedFormula.equal
      (ScopedTerm.add left.lift
        (ScopedTerm.succ
          (ScopedTerm.bvar 0 (Nat.zero_lt_succ bound))))
      right.lift
  have strictExact : scopedLessThanFormulaAt left right =
      ScopedFormula.ex witnessBody := by
    apply ScopedFormula.eq_of_raw_eq
    rfl
  let normalizedStrict := Derivation.castConclusion strictExact strict
  let witnessContext := FormulaContext.cons witnessBody context.lift
  let equation : Derivation LogicMode.intuitionistic haTheory witnessContext
      witnessBody := Derivation.hypothesis ContextMember.here
  let liftedEquality := Derivation.weaken witnessBody
    (Derivation.liftVariables equality)
  have explicitEquality : Derivation LogicMode.intuitionistic haTheory
      witnessContext
      (ScopedFormula.equal left.lift replacement.lift) := by
    simpa [witnessContext, ScopedFormula.equal, ScopedFormula.lift,
      ScopedTerm.lift,
      RawFormula.rename, RawTerm.rename] using liftedEquality
  let addedEquality := addCongruenceLeftAt
    (fixed := ScopedTerm.bvar 0 (Nat.zero_lt_succ bound) |>.succ)
    explicitEquality
  let replacementEquation := Derivation.equalityTransitivity
    (Derivation.equalitySymmetry addedEquality) equation
  let branchStrict := lessThanIntroductionAt replacement.lift right.lift
    (ScopedTerm.bvar 0 (Nat.zero_lt_succ bound)) replacementEquation
  have branch : Derivation LogicMode.intuitionistic haTheory witnessContext
      (scopedLessThanFormulaAt replacement right).lift := by
    apply Derivation.castConclusion
      (scopedLessThanFormulaAt_lift replacement right)
    exact branchStrict
  exact Derivation.existentialElimination
    (body := witnessBody)
    (conclusion := scopedLessThanFormulaAt replacement right)
    normalizedStrict branch

def lessThanTransportRightAt
    {bound : Nat}
    {context : FormulaContext bound}
    (left right replacement : ScopedTerm bound)
    (equality : Derivation LogicMode.intuitionistic haTheory context
      (ScopedFormula.equal right replacement))
    (strict : Derivation LogicMode.intuitionistic haTheory context
      (scopedLessThanFormulaAt left right)) :
    Derivation LogicMode.intuitionistic haTheory context
      (scopedLessThanFormulaAt left replacement) := by
  let witnessBody : ScopedFormula (Nat.succ bound) :=
    ScopedFormula.equal
      (ScopedTerm.add left.lift
        (ScopedTerm.succ
          (ScopedTerm.bvar 0 (Nat.zero_lt_succ bound))))
      right.lift
  have strictExact : scopedLessThanFormulaAt left right =
      ScopedFormula.ex witnessBody := by
    apply ScopedFormula.eq_of_raw_eq
    rfl
  let normalizedStrict := Derivation.castConclusion strictExact strict
  let witnessContext := FormulaContext.cons witnessBody context.lift
  let equation : Derivation LogicMode.intuitionistic haTheory witnessContext
      witnessBody := Derivation.hypothesis ContextMember.here
  let liftedEquality := Derivation.weaken witnessBody
    (Derivation.liftVariables equality)
  have explicitEquality : Derivation LogicMode.intuitionistic haTheory
      witnessContext
      (ScopedFormula.equal right.lift replacement.lift) := by
    simpa [witnessContext, ScopedFormula.equal, ScopedFormula.lift,
      ScopedTerm.lift,
      RawFormula.rename, RawTerm.rename] using liftedEquality
  let replacementEquation := Derivation.equalityTransitivity equation
    explicitEquality
  let branchStrict := lessThanIntroductionAt left.lift replacement.lift
    (ScopedTerm.bvar 0 (Nat.zero_lt_succ bound)) replacementEquation
  have branch : Derivation LogicMode.intuitionistic haTheory witnessContext
      (scopedLessThanFormulaAt left replacement).lift := by
    apply Derivation.castConclusion
      (scopedLessThanFormulaAt_lift left replacement)
    exact branchStrict
  exact Derivation.existentialElimination
    (body := witnessBody)
    (conclusion := scopedLessThanFormulaAt left replacement)
    normalizedStrict branch

def lessThanAddLeftAt
    {bound : Nat}
    {context : FormulaContext bound}
    (fixed left right : ScopedTerm bound)
    (strict : Derivation LogicMode.intuitionistic haTheory context
      (scopedLessThanFormulaAt left right)) :
    Derivation LogicMode.intuitionistic haTheory context
      (scopedLessThanFormulaAt
        (ScopedTerm.add fixed left) (ScopedTerm.add fixed right)) := by
  let witnessBody : ScopedFormula (Nat.succ bound) :=
    ScopedFormula.equal
      (ScopedTerm.add left.lift
        (ScopedTerm.succ
          (ScopedTerm.bvar 0 (Nat.zero_lt_succ bound))))
      right.lift
  let witnessContext := FormulaContext.cons witnessBody context.lift
  let equation : Derivation LogicMode.intuitionistic haTheory witnessContext
      witnessBody := Derivation.hypothesis ContextMember.here
  let gap := ScopedTerm.bvar 0 (Nat.zero_lt_succ bound)
  let reassociate := (addAssociativeProof fixed.lift left.lift gap.succ)
    |>.weakenClosedTo witnessContext
  let replace := addCongruenceRightAt (fixed := fixed.lift) equation
  let resultEquation := Derivation.equalityTransitivity reassociate replace
  let branchStrict := lessThanIntroductionAt
    (ScopedTerm.add fixed.lift left.lift)
    (ScopedTerm.add fixed.lift right.lift) gap resultEquation
  have strictExact : scopedLessThanFormulaAt left right =
      ScopedFormula.ex witnessBody := by
    apply ScopedFormula.eq_of_raw_eq
    rfl
  let normalizedStrict := Derivation.castConclusion strictExact strict
  have branch : Derivation LogicMode.intuitionistic haTheory witnessContext
      (scopedLessThanFormulaAt
        (ScopedTerm.add fixed left) (ScopedTerm.add fixed right)).lift := by
    apply Derivation.castConclusion
      (scopedLessThanFormulaAt_lift
        (ScopedTerm.add fixed left) (ScopedTerm.add fixed right))
    simpa [ScopedTerm.lift, ScopedTerm.add, RawTerm.rename]
      using branchStrict
  exact Derivation.existentialElimination
    (body := witnessBody)
    (conclusion := scopedLessThanFormulaAt
      (ScopedTerm.add fixed left) (ScopedTerm.add fixed right))
    normalizedStrict branch

def lessThanAddRightAt
    {bound : Nat}
    {context : FormulaContext bound}
    (left right fixed : ScopedTerm bound)
    (strict : Derivation LogicMode.intuitionistic haTheory context
      (scopedLessThanFormulaAt left right)) :
    Derivation LogicMode.intuitionistic haTheory context
      (scopedLessThanFormulaAt
        (ScopedTerm.add left fixed) (ScopedTerm.add right fixed)) := by
  let commuted := lessThanAddLeftAt fixed left right strict
  let leftEquality := (addCommutativeProof fixed left).weakenClosedTo context
  let rightEquality := (addCommutativeProof fixed right).weakenClosedTo context
  exact lessThanTransportRightAt _ _ _ rightEquality
    (lessThanTransportLeftAt _ _ _ leftEquality commuted)

def lessThanTransitiveAt
    {bound : Nat}
    {context : FormulaContext bound}
    (first second third : ScopedTerm bound)
    (firstStrict : Derivation LogicMode.intuitionistic haTheory context
      (scopedLessThanFormulaAt first second))
    (secondStrict : Derivation LogicMode.intuitionistic haTheory context
      (scopedLessThanFormulaAt second third)) :
    Derivation LogicMode.intuitionistic haTheory context
      (scopedLessThanFormulaAt first third) := by
  let firstBody : ScopedFormula (Nat.succ bound) :=
    ScopedFormula.equal
      (ScopedTerm.add first.lift
        (ScopedTerm.succ
          (ScopedTerm.bvar 0 (Nat.zero_lt_succ bound))))
      second.lift
  let firstContext := FormulaContext.cons firstBody context.lift
  let firstEquation : Derivation LogicMode.intuitionistic haTheory firstContext
      firstBody := Derivation.hypothesis ContextMember.here
  let liftedSecond := Derivation.weaken firstBody
    (Derivation.liftVariables secondStrict)
  let secondBody : ScopedFormula (Nat.succ (Nat.succ bound)) :=
    ScopedFormula.equal
      (ScopedTerm.add second.lift.lift
        (ScopedTerm.succ
          (ScopedTerm.bvar 0 (Nat.zero_lt_succ (Nat.succ bound)))))
      third.lift.lift
  let secondContext := FormulaContext.cons secondBody firstContext.lift
  let secondEquation : Derivation LogicMode.intuitionistic haTheory secondContext
      secondBody := Derivation.hypothesis ContextMember.here
  let gapOne := ScopedTerm.bvar 1
    (Nat.succ_lt_succ (Nat.zero_lt_succ bound))
  let gapTwo := ScopedTerm.bvar 0 (Nat.zero_lt_succ (Nat.succ bound))
  let liftedFirstEquation : Derivation LogicMode.intuitionistic haTheory
      secondContext firstBody.lift :=
    Derivation.weaken secondBody (Derivation.liftVariables firstEquation)
  have explicitFirstEquation : Derivation LogicMode.intuitionistic haTheory
      secondContext
      (ScopedFormula.equal
        (ScopedTerm.add first.lift.lift gapOne.succ)
        second.lift.lift) := by
    simpa [firstBody, gapOne, ScopedFormula.equal, ScopedFormula.lift,
      ScopedTerm.bvar, ScopedTerm.add, ScopedTerm.succ, ScopedTerm.lift,
      RawFormula.rename, RawTerm.rename] using liftedFirstEquation
  let addSecondGap := addCongruenceLeftAt (fixed := gapTwo.succ)
    explicitFirstEquation
  let toThird := Derivation.equalityTransitivity addSecondGap secondEquation
  let reassociate := (addAssociativeProof first.lift.lift gapOne.succ
    gapTwo.succ).weakenClosedTo secondContext
  let combineGaps := successorAddProof gapOne gapTwo.succ
    |>.weakenClosedTo secondContext
  let combineAtFirst := addCongruenceRightAt
    (fixed := first.lift.lift) combineGaps
  let resultEquation := Derivation.equalityTransitivity
    (Derivation.equalityTransitivity
      (Derivation.equalitySymmetry combineAtFirst)
      (Derivation.equalitySymmetry reassociate)) toThird
  let targetGap := ScopedTerm.add gapOne gapTwo.succ
  let branchStrict := lessThanIntroductionAt first.lift.lift
    third.lift.lift targetGap resultEquation
  have normalizedSecond : Derivation LogicMode.intuitionistic haTheory
      firstContext (ScopedFormula.ex secondBody) := by
    have liftedAsStrict : Derivation LogicMode.intuitionistic haTheory
        firstContext
        (scopedLessThanFormulaAt second.lift third.lift) :=
      Derivation.castConclusion
        (scopedLessThanFormulaAt_lift second third).symm liftedSecond
    simpa [secondBody, scopedLessThanFormulaAt, lessThanFormula,
      ScopedFormula.ex, ScopedFormula.equal, ScopedTerm.bvar,
      ScopedTerm.add, ScopedTerm.succ, ScopedTerm.lift,
      RawTerm.shift, RawTerm.rename]
      using liftedAsStrict
  have secondBranch : Derivation LogicMode.intuitionistic haTheory secondContext
      (scopedLessThanFormulaAt first.lift third.lift).lift := by
    apply Derivation.castConclusion
      (scopedLessThanFormulaAt_lift first.lift third.lift)
    exact branchStrict
  let eliminateSecond := Derivation.existentialElimination
    (body := secondBody)
    (conclusion := scopedLessThanFormulaAt first.lift third.lift)
    normalizedSecond secondBranch
  have normalizedFirst : Derivation LogicMode.intuitionistic haTheory context
      (ScopedFormula.ex firstBody) := by
    simpa [firstBody, scopedLessThanFormulaAt, lessThanFormula,
      ScopedFormula.ex, ScopedFormula.equal, ScopedTerm.bvar,
      ScopedTerm.add, ScopedTerm.succ, ScopedTerm.lift,
      RawTerm.shift, RawTerm.rename]
      using firstStrict
  have firstBranch : Derivation LogicMode.intuitionistic haTheory firstContext
      (scopedLessThanFormulaAt first third).lift := by
    apply Derivation.castConclusion
      (scopedLessThanFormulaAt_lift first third)
    exact eliminateSecond
  exact Derivation.existentialElimination
    (body := firstBody)
    (conclusion := scopedLessThanFormulaAt first third)
    normalizedFirst firstBranch

def lessOrEqualFormula
    {bound : Nat}
    (left right : ScopedTerm bound) : ScopedFormula bound :=
  ScopedFormula.disj
    (scopedLessThanFormulaAt left right)
    (ScopedFormula.equal left right)

theorem lessOrEqualFormula_lift
    {bound : Nat}
    (left right : ScopedTerm bound) :
    lessOrEqualFormula left.lift right.lift =
      (lessOrEqualFormula left right).lift := by
  apply ScopedFormula.eq_of_raw_eq
  apply congrArgTwo RawFormula.disj
  · exact congrArg ScopedFormula.raw
      (scopedLessThanFormulaAt_lift left right)
  · rfl

theorem lessOrEqualAddBody_instantiate
    {bound : Nat}
    (base replacement : ScopedTerm bound) :
    (let added := ScopedTerm.bvar 0 (Nat.zero_lt_succ bound)
     lessOrEqualFormula base.lift
      (ScopedTerm.add base.lift added)).instantiate replacement =
      lessOrEqualFormula base (ScopedTerm.add base replacement) := by
  apply ScopedFormula.eq_of_raw_eq
  dsimp [lessOrEqualFormula, scopedLessThanFormulaAt, lessThanFormula,
    ScopedFormula.instantiate, ScopedTerm.instantiate,
    RawFormula.instantiateTerm, RawTerm.instantiateTerm,
    RawFormula.substitute, RawTerm.substitute,
    singleTermSubstitution, ScopedFormula.lift,
    ScopedFormula.disj, ScopedFormula.equal, ScopedFormula.ex,
    ScopedTerm.lift, ScopedTerm.add, ScopedTerm.bvar,
    RawFormula.rename, RawTerm.rename, RawTerm.raise, RawTerm.shift]
  repeat' rw [RawTerm.renameSuccTwice_substituteLiftSingle]
  repeat' rw [RawTerm.renameSucc_substituteSingle]
  dsimp [liftSubstitution, singleTermSubstitution]

theorem lessOrEqualAddBody_successorInstance
    {bound : Nat}
    (base : ScopedTerm bound) :
    let added := ScopedTerm.bvar 0 (Nat.zero_lt_succ bound)
    (lessOrEqualFormula base.lift
      (ScopedTerm.add base.lift added)).successorInstance =
      lessOrEqualFormula base.lift
        (ScopedTerm.add base.lift added.succ) := by
  apply ScopedFormula.eq_of_raw_eq
  dsimp [lessOrEqualFormula, scopedLessThanFormulaAt, lessThanFormula,
    ScopedFormula.successorInstance,
    ScopedFormula.replaceNewestKeepingScopeSubstitution,
    RawFormula.substitute, RawTerm.substitute,
    ScopedFormula.disj, ScopedFormula.equal, ScopedFormula.ex,
    ScopedFormula.lift, ScopedTerm.lift, ScopedTerm.add,
    ScopedTerm.succ, ScopedTerm.bvar,
    RawFormula.rename, RawTerm.rename, RawTerm.raise, RawTerm.shift,
    liftSubstitution]
  repeat' rw [RawTerm.renameSuccTwice_substituteLiftKeeping]
  repeat' rw [RawTerm.renameSucc_substituteKeepingScope]

def lessThanAddSuccessorProof
    {bound : Nat}
    (base added : ScopedTerm bound) :
    Derivation LogicMode.intuitionistic haTheory FormulaContext.nil
      (scopedLessThanFormulaAt base
        (ScopedTerm.add base added.succ)) := by
  let reflexive : Derivation LogicMode.intuitionistic haTheory FormulaContext.nil
      (ScopedFormula.equal
        (ScopedTerm.add base added.succ)
        (ScopedTerm.add base added.succ)) :=
    Derivation.equalityReflexivity (ScopedTerm.add base added.succ)
  exact lessThanIntroductionAt base
    (ScopedTerm.add base added.succ) added reflexive

def lessOrEqualAddRightUniversal
    {bound : Nat}
    (base : ScopedTerm bound) :
    Derivation LogicMode.intuitionistic haTheory FormulaContext.nil
      (ScopedFormula.all
        (let added := ScopedTerm.bvar 0 (Nat.zero_lt_succ bound)
         lessOrEqualFormula base.lift
          (ScopedTerm.add base.lift added))) := by
  let added := ScopedTerm.bvar 0 (Nat.zero_lt_succ bound)
  let body : ScopedFormula (Nat.succ bound) :=
    lessOrEqualFormula base.lift (ScopedTerm.add base.lift added)
  let addZero : Derivation LogicMode.intuitionistic haTheory FormulaContext.nil
      (ScopedFormula.equal
        (ScopedTerm.add base (ScopedTerm.zero bound)) base) :=
    Derivation.theoryAxiom
    (context := FormulaContext.nil)
    (StandardArithmeticAxiom.addZero base)
  let baseProof : Derivation LogicMode.intuitionistic haTheory FormulaContext.nil
      (lessOrEqualFormula base
        (ScopedTerm.add base (ScopedTerm.zero bound))) :=
    Derivation.disjunctionIntroductionRight
    (left := scopedLessThanFormulaAt base
      (ScopedTerm.add base (ScopedTerm.zero bound)))
      (Derivation.equalitySymmetry addZero)
  let step : Derivation LogicMode.intuitionistic haTheory FormulaContext.nil
      (ScopedFormula.all
        (ScopedFormula.impl body body.successorInstance)) := by
    apply Derivation.universalIntroduction
    apply Derivation.implicationIntroduction
    let stepContext := FormulaContext.cons body FormulaContext.nil
    let strict := (lessThanAddSuccessorProof base.lift added)
      |>.weakenClosedTo stepContext
    let result : Derivation LogicMode.intuitionistic haTheory stepContext
        (lessOrEqualFormula base.lift
          (ScopedTerm.add base.lift added.succ)) :=
      Derivation.disjunctionIntroductionLeft
        (right := ScopedFormula.equal base.lift
          (ScopedTerm.add base.lift added.succ)) strict
    apply Derivation.castConclusion
      (lessOrEqualAddBody_successorInstance base).symm
    exact result
  have normalizedBase : Derivation LogicMode.intuitionistic haTheory
      FormulaContext.nil (body.instantiate (ScopedTerm.zero bound)) := by
    apply Derivation.castConclusion
      (lessOrEqualAddBody_instantiate base
        (ScopedTerm.zero bound)).symm
    exact baseProof
  exact Derivation.byArithmeticInduction body normalizedBase step

def lessOrEqualAddRightProof
    {bound : Nat}
    (base added : ScopedTerm bound) :
    Derivation LogicMode.intuitionistic haTheory FormulaContext.nil
      (lessOrEqualFormula base (ScopedTerm.add base added)) := by
  let instantiated := Derivation.universalElimination added
    (lessOrEqualAddRightUniversal base)
  apply Derivation.castConclusion
    (lessOrEqualAddBody_instantiate base added)
  exact instantiated

def lessThanThenLessOrEqualAt
    {bound : Nat}
    {context : FormulaContext bound}
    (first second third : ScopedTerm bound)
    (strict : Derivation LogicMode.intuitionistic haTheory context
      (scopedLessThanFormulaAt first second))
    (bounded : Derivation LogicMode.intuitionistic haTheory context
      (lessOrEqualFormula second third)) :
    Derivation LogicMode.intuitionistic haTheory context
      (scopedLessThanFormulaAt first third) := by
  let strictCase := scopedLessThanFormulaAt second third
  let equalityCase := ScopedFormula.equal second third
  let strictContext := FormulaContext.cons strictCase context
  let strictHypothesis : Derivation LogicMode.intuitionistic haTheory strictContext
      strictCase := Derivation.hypothesis ContextMember.here
  let strictBranch := lessThanTransitiveAt first second third
    (Derivation.weaken strictCase strict) strictHypothesis
  let equalityContext := FormulaContext.cons equalityCase context
  let equalityHypothesis : Derivation LogicMode.intuitionistic haTheory
      equalityContext equalityCase := Derivation.hypothesis ContextMember.here
  let equalityBranch := lessThanTransportRightAt first second third
    equalityHypothesis (Derivation.weaken equalityCase strict)
  exact Derivation.disjunctionElimination bounded strictBranch equalityBranch

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.HeytingArithmetic.noAddSuccessorSelfProof
#print axioms RelationalPerimeter.HeytingArithmetic.lessThanIrreflexiveProof
#print axioms RelationalPerimeter.HeytingArithmetic.lessThanAndEqualityContradiction
#print axioms RelationalPerimeter.HeytingArithmetic.zeroLessSuccessorProof
#print axioms RelationalPerimeter.HeytingArithmetic.lessThanSuccessorSelfProof
#print axioms RelationalPerimeter.HeytingArithmetic.successorLessSuccessorOfLessAt
#print axioms RelationalPerimeter.HeytingArithmetic.lessThanSuccessorRightOfLessAt
#print axioms RelationalPerimeter.HeytingArithmetic.orderTrichotomyProof
#print axioms RelationalPerimeter.HeytingArithmetic.lessThanTransportLeftAt
#print axioms RelationalPerimeter.HeytingArithmetic.lessThanAddLeftAt
#print axioms RelationalPerimeter.HeytingArithmetic.lessThanTransitiveAt
#print axioms RelationalPerimeter.HeytingArithmetic.lessOrEqualAddRightProof
#print axioms RelationalPerimeter.HeytingArithmetic.lessThanThenLessOrEqualAt
/- AXIOM_AUDIT_END -/
