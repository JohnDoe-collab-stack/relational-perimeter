import RelationalPerimeter.Instances.HeytingArithmetic.PrimitiveRecursiveContextOperations
import RelationalPerimeter.Instances.HeytingArithmetic.StrictSyntaxCorrectness

/-!
# Primitive-recursive recognition of scoped syntax

The formula-raising machine is also a syntax normalizer.  Raising by zero
rebuilds a code without changing genuine syntax.  Closing a formula by `b`
universal binders and then raising by one leaves it unchanged exactly on the
well-scoped fragment.  This file defines the positive programs and proves the
forward, proof-checker-critical equations on all typed syntax.
-/

namespace RelationalPerimeter
namespace HeytingArithmetic

private theorem recognitionIndexZero_lt_one : 0 < 1 := Nat.zero_lt_succ 0
private theorem recognitionIndexZero_lt_two : 0 < 2 := Nat.zero_lt_succ 1
private theorem recognitionIndexOne_lt_two : 1 < 2 :=
  Nat.succ_lt_succ (Nat.zero_lt_succ 0)
private theorem recognitionIndexOne_lt_three : 1 < 3 :=
  Nat.succ_lt_succ (Nat.zero_lt_succ 1)

/-! ## Closing codes by explicit binders -/

def wrapUniversalCode : Nat -> Nat -> Nat
  | 0, formulaCode => formulaCode
  | Nat.succ count, formulaCode =>
      Nat.succ (natPair 5 (wrapUniversalCode count formulaCode))

def PRFunction.wrapUniversalIterationStep : PRFunction 3 :=
  let previous := PRFunction.projection 3 1 recognitionIndexOne_lt_three
  PRFunction.unaryIn PRFunction.formulaUniversalCode previous

def PRFunction.wrapUniversalCore : PRFunction 2 :=
  PRFunction.primitiveRecursion PRFunction.identity
    PRFunction.wrapUniversalIterationStep

/-- Input order is `(formulaCode,binderCount)`. -/
def PRFunction.wrapUniversalCode : PRFunction 2 :=
  PRFunction.composition PRFunction.wrapUniversalCore
    (PRFunctionVector.cons
      (PRFunction.projection 2 1 recognitionIndexOne_lt_two)
      (PRFunctionVector.singleton
        (PRFunction.projection 2 0 recognitionIndexZero_lt_two)))

@[simp] theorem PRFunction.run_wrapUniversalIterationStep
    (counter previous formulaCode : Nat) :
    PRFunction.wrapUniversalIterationStep.run
        (NatVector.cons counter
          (NatVector.cons previous
            (NatVector.cons formulaCode NatVector.nil))) =
      Nat.succ (natPair 5 previous) := by
  unfold PRFunction.wrapUniversalIterationStep
  rw [PRFunction.run_unaryIn, PRFunction.run_projection,
    NatVector.get_cons_succ, NatVector.get_cons_zero,
    PRFunction.run_formulaUniversalCode]

theorem PRFunction.run_wrapUniversalCore
    (binderCount formulaCode : Nat) :
    PRFunction.wrapUniversalCore.run
        (NatVector.cons binderCount
          (NatVector.cons formulaCode NatVector.nil)) =
      RelationalPerimeter.HeytingArithmetic.wrapUniversalCode binderCount formulaCode := by
  induction binderCount with
  | zero => rfl
  | succ binderCount inductionHypothesis =>
      change PRFunction.wrapUniversalIterationStep.run
        (NatVector.cons binderCount
          (NatVector.cons
            (PRFunction.wrapUniversalCore.run
              (NatVector.cons binderCount
                (NatVector.cons formulaCode NatVector.nil)))
            (NatVector.cons formulaCode NatVector.nil))) = _
      rw [PRFunction.run_wrapUniversalIterationStep, inductionHypothesis]
      rfl

@[simp] theorem PRFunction.run_wrapUniversalCode
    (formulaCode binderCount : Nat) :
    PRFunction.wrapUniversalCode.run
        (NatVector.cons formulaCode
          (NatVector.cons binderCount NatVector.nil)) =
      RelationalPerimeter.HeytingArithmetic.wrapUniversalCode binderCount formulaCode := by
  unfold PRFunction.wrapUniversalCode
  rw [PRFunction.run_composition, PRFunctionVector.run_cons,
    PRFunctionVector.run_singleton, PRFunction.run_projection,
    NatVector.get_cons_succ, NatVector.get_cons_zero,
    PRFunction.run_wrapUniversalCore]
  rw [PRFunction.run_projection, NatVector.get_cons_zero]

/-! ## Numeric recognition bits -/

/-- Strict canonical formula-code recognition by course-of-values trace. -/
def PRFunction.isFormulaCode : PRFunction 1 :=
  PRFunction.binaryIn PRFunction.equalBit
    PRFunction.strictFormulaCode (PRFunction.constant 1 1)

/-- Embed a term code into the formula code `t = t`. -/
def PRFunction.termEqualityEnvelope : PRFunction 1 :=
  PRFunction.binaryIn PRFunction.formulaEqualCode
    PRFunction.identity PRFunction.identity

def PRFunction.isTermCode : PRFunction 1 :=
  PRFunction.binaryIn PRFunction.equalBit
    PRFunction.strictTermCode (PRFunction.constant 1 1)

/-- Input order is `(bound,formulaCode)`. -/
def PRFunction.isScopedFormulaCode : PRFunction 2 :=
  let bound := PRFunction.projection 2 0 recognitionIndexZero_lt_two
  let formulaCode := PRFunction.projection 2 1 recognitionIndexOne_lt_two
  let closed := PRFunction.composition PRFunction.wrapUniversalCode
    (PRFunctionVector.cons formulaCode (PRFunctionVector.singleton bound))
  let raised := PRFunction.composition PRFunction.raiseFormulaCode
    (PRFunctionVector.cons closed
      (PRFunctionVector.singleton (PRFunction.constant 2 1)))
  PRFunction.conjoin
    (PRFunction.unaryIn PRFunction.isFormulaCode formulaCode)
    (PRFunction.binaryIn PRFunction.equalBit raised closed)

/-- Input order is `(bound,termCode)`. -/
def PRFunction.isScopedTermCode : PRFunction 2 :=
  let bound := PRFunction.projection 2 0 recognitionIndexZero_lt_two
  let termCode := PRFunction.projection 2 1 recognitionIndexOne_lt_two
  let envelope := PRFunction.unaryIn PRFunction.termEqualityEnvelope termCode
  PRFunction.conjoin
    (PRFunction.unaryIn PRFunction.isTermCode termCode)
    (PRFunction.composition PRFunction.isScopedFormulaCode
      (PRFunctionVector.cons bound (PRFunctionVector.singleton envelope)))

@[simp] theorem PRFunction.run_isFormulaCode (code : Nat) :
    PRFunction.isFormulaCode.run (NatVector.cons code NatVector.nil) =
      natEqualBit (natUnpairRight (syntaxEntryAt code)) 1 := by
  unfold PRFunction.isFormulaCode
  rw [PRFunction.run_binaryIn, PRFunction.run_strictFormulaCode,
    PRFunction.run_constant, PRFunction.run_equalBit]

@[simp] theorem PRFunction.run_termEqualityEnvelope (code : Nat) :
    PRFunction.termEqualityEnvelope.run (NatVector.cons code NatVector.nil) =
      Nat.succ (natPair 1 (natPair code code)) := by
  unfold PRFunction.termEqualityEnvelope
  rw [PRFunction.run_binaryIn, PRFunction.run_identity,
    PRFunction.run_formulaEqualCode]

@[simp] theorem PRFunction.run_isTermCode (code : Nat) :
    PRFunction.isTermCode.run (NatVector.cons code NatVector.nil) =
      natEqualBit (natUnpairLeft (syntaxEntryAt code)) 1 := by
  unfold PRFunction.isTermCode
  rw [PRFunction.run_binaryIn, PRFunction.run_strictTermCode,
    PRFunction.run_constant, PRFunction.run_equalBit]

@[simp] theorem PRFunction.run_isScopedFormulaCode
    (bound code : Nat) :
    PRFunction.isScopedFormulaCode.run
        (NatVector.cons bound (NatVector.cons code NatVector.nil)) =
      natAndBit
        (PRFunction.isFormulaCode.run (NatVector.cons code NatVector.nil))
        (natEqualBit
          (machineRaiseFormulaCode
            (RelationalPerimeter.HeytingArithmetic.wrapUniversalCode bound code) 1)
          (RelationalPerimeter.HeytingArithmetic.wrapUniversalCode bound code)) := by
  unfold PRFunction.isScopedFormulaCode
  repeat first
    | rw [PRFunction.run_binaryIn]
    | rw [PRFunction.run_composition]
    | rw [PRFunctionVector.run_cons]
    | rw [PRFunctionVector.run_singleton]
    | rw [PRFunction.run_projection]
    | rw [NatVector.get_cons_zero]
    | rw [NatVector.get_cons_succ]
    | rw [PRFunction.run_constant]
    | rw [PRFunction.run_unaryIn]
    | rw [PRFunction.run_wrapUniversalCode]
    | rw [PRFunction.run_raiseFormulaCode]
    | rw [PRFunction.run_equalBit]
    | rw [PRFunction.run_conjoin]

@[simp] theorem PRFunction.run_isScopedTermCode
    (bound code : Nat) :
    PRFunction.isScopedTermCode.run
        (NatVector.cons bound (NatVector.cons code NatVector.nil)) =
      natAndBit
        (PRFunction.isTermCode.run (NatVector.cons code NatVector.nil))
        (PRFunction.isScopedFormulaCode.run
          (NatVector.cons bound
            (NatVector.cons (Nat.succ (natPair 1 (natPair code code)))
              NatVector.nil))) := by
  unfold PRFunction.isScopedTermCode
  repeat first
    | rw [PRFunction.run_conjoin]
    | rw [PRFunction.run_composition]
    | rw [PRFunctionVector.run_cons]
    | rw [PRFunctionVector.run_singleton]
    | rw [PRFunction.run_projection]
    | rw [NatVector.get_cons_zero]
    | rw [NatVector.get_cons_succ]
    | rw [PRFunction.run_unaryIn]
    | rw [PRFunction.run_termEqualityEnvelope]

/-! ## Syntactic correctness on typed inputs -/

theorem RawTerm.rename_eq_self_of_wellScoped
    (term : RawTerm)
    (bound : Nat)
    (isScoped : term.WellScoped bound)
    (renameMap : Renaming)
    (fixed : forall index, index < bound -> renameMap index = index) :
    term.rename renameMap = term := by
  induction term with
  | bvar index =>
      change RawTerm.bvar (renameMap index) = RawTerm.bvar index
      rw [fixed index isScoped]
  | zero => rfl
  | succ body inductionHypothesis =>
      change RawTerm.succ (body.rename renameMap) = RawTerm.succ body
      rw [inductionHypothesis isScoped]
  | add left right leftHypothesis rightHypothesis =>
      change RawTerm.add (left.rename renameMap) (right.rename renameMap) =
        RawTerm.add left right
      rw [leftHypothesis isScoped.1, rightHypothesis isScoped.2]
  | mul left right leftHypothesis rightHypothesis =>
      change RawTerm.mul (left.rename renameMap) (right.rename renameMap) =
        RawTerm.mul left right
      rw [leftHypothesis isScoped.1, rightHypothesis isScoped.2]

theorem RawFormula.rename_eq_self_of_wellScoped
    (formula : RawFormula)
    (bound : Nat)
    (isScoped : formula.WellScoped bound)
    (renameMap : Renaming)
    (fixed : forall index, index < bound -> renameMap index = index) :
    formula.rename renameMap = formula := by
  induction formula generalizing bound renameMap with
  | falsum => rfl
  | equal left right =>
      change RawFormula.equal (left.rename renameMap) (right.rename renameMap) =
        RawFormula.equal left right
      rw [left.rename_eq_self_of_wellScoped bound isScoped.1 renameMap fixed,
        right.rename_eq_self_of_wellScoped bound isScoped.2 renameMap fixed]
  | conj left right leftHypothesis rightHypothesis =>
      change RawFormula.conj (left.rename renameMap) (right.rename renameMap) =
        RawFormula.conj left right
      rw [leftHypothesis bound isScoped.1 renameMap fixed,
        rightHypothesis bound isScoped.2 renameMap fixed]
  | disj left right leftHypothesis rightHypothesis =>
      change RawFormula.disj (left.rename renameMap) (right.rename renameMap) =
        RawFormula.disj left right
      rw [leftHypothesis bound isScoped.1 renameMap fixed,
        rightHypothesis bound isScoped.2 renameMap fixed]
  | impl left right leftHypothesis rightHypothesis =>
      change RawFormula.impl (left.rename renameMap) (right.rename renameMap) =
        RawFormula.impl left right
      rw [leftHypothesis bound isScoped.1 renameMap fixed,
        rightHypothesis bound isScoped.2 renameMap fixed]
  | all body inductionHypothesis =>
      change RawFormula.all (body.rename (liftRenaming renameMap)) =
        RawFormula.all body
      rw [inductionHypothesis (Nat.succ bound) isScoped
        (liftRenaming renameMap)]
      intro index bounded
      cases index with
      | zero => rfl
      | succ index =>
          change Nat.succ (renameMap index) = Nat.succ index
          rw [fixed index (Nat.lt_of_succ_lt_succ bounded)]
  | ex body inductionHypothesis =>
      change RawFormula.ex (body.rename (liftRenaming renameMap)) =
        RawFormula.ex body
      rw [inductionHypothesis (Nat.succ bound) isScoped
        (liftRenaming renameMap)]
      intro index bounded
      cases index with
      | zero => rfl
      | succ index =>
          change Nat.succ (renameMap index) = Nat.succ index
          rw [fixed index (Nat.lt_of_succ_lt_succ bounded)]

def wrapUniversalFormula : Nat -> RawFormula -> RawFormula
  | 0, formula => formula
  | Nat.succ count, formula =>
      RawFormula.all (wrapUniversalFormula count formula)

theorem wrapUniversalFormula_code
    (count : Nat)
    (formula : RawFormula) :
    (wrapUniversalFormula count formula).code =
      RelationalPerimeter.HeytingArithmetic.wrapUniversalCode count formula.code := by
  induction count with
  | zero => rfl
  | succ count inductionHypothesis =>
      change Nat.succ (natPair 5
          (wrapUniversalFormula count formula).code) = _
      rw [RelationalPerimeter.HeytingArithmetic.wrapUniversalCode,
        inductionHypothesis]

private theorem wrapUniversalFormula_wellScoped
    (formula : RawFormula)
    (count base : Nat)
    (isScoped : formula.WellScoped (base + count)) :
    (wrapUniversalFormula count formula).WellScoped base := by
  induction count generalizing base with
  | zero => simpa [wrapUniversalFormula] using isScoped
  | succ count inductionHypothesis =>
      change (wrapUniversalFormula count formula).WellScoped (Nat.succ base)
      apply inductionHypothesis (base := Nat.succ base)
      have sameBound : Nat.succ base + count = base + Nat.succ count :=
        (Nat.succ_add base count).trans (Nat.add_succ base count).symm
      exact Eq.mpr
        (congrArg (fun available => formula.WellScoped available) sameBound)
        isScoped

theorem wrapUniversalFormula_wellScoped_zero
    (formula : RawFormula)
    (bound : Nat)
    (isScoped : formula.WellScoped bound) :
    (wrapUniversalFormula bound formula).WellScoped 0 := by
  exact wrapUniversalFormula_wellScoped formula bound 0 (by
    simpa using isScoped)

theorem machineRaiseFormulaCode_closed_fixed
    (formula : RawFormula)
    (isClosed : formula.WellScoped 0)
    (amount : Nat) :
    machineRaiseFormulaCode formula.code amount = formula.code := by
  rw [machineRaiseFormulaCode_code]
  unfold RawFormula.raiseFreeVariables
  rw [formula.rename_eq_self_of_wellScoped 0 isClosed
    (raisingRenamingAtDepth amount 0)]
  intro index bounded
  exact (Nat.not_lt_zero index bounded).elim

theorem raisingRenamingAtDepth_zero
    (depth index : Nat) :
    raisingRenamingAtDepth 0 depth index = index := by
  induction depth generalizing index with
  | zero => exact Nat.add_zero index
  | succ depth inductionHypothesis =>
      cases index with
      | zero => rfl
      | succ index =>
          change Nat.succ (raisingRenamingAtDepth 0 depth index) =
            Nat.succ index
          rw [inductionHypothesis]

theorem RawTerm.wellScoped_of_raising_fixed
    (term : RawTerm)
    (bound : Nat)
    (fixed : term.rename (raisingRenamingAtDepth 1 bound) = term) :
    term.WellScoped bound := by
  induction term with
  | bvar index =>
      have indexFixed : raisingRenamingAtDepth 1 bound index = index :=
        RawTerm.bvar.inj fixed
      by_cases bounded : index < bound
      · exact bounded
      · rw [raisingRenamingAtDepth_of_not_lt 1 bound index bounded,
          Nat.add_one] at indexFixed
        exact ((Nat.ne_of_lt (Nat.lt_succ_self index)) indexFixed.symm).elim
  | zero => exact trivial
  | succ body inductionHypothesis =>
      exact inductionHypothesis (RawTerm.succ.inj fixed)
  | add left right leftHypothesis rightHypothesis =>
      have parts := RawTerm.add.inj fixed
      exact And.intro (leftHypothesis parts.1) (rightHypothesis parts.2)
  | mul left right leftHypothesis rightHypothesis =>
      have parts := RawTerm.mul.inj fixed
      exact And.intro (leftHypothesis parts.1) (rightHypothesis parts.2)

theorem RawFormula.wellScoped_of_raising_fixed
    (formula : RawFormula)
    (bound : Nat)
    (fixed : formula.rename (raisingRenamingAtDepth 1 bound) = formula) :
    formula.WellScoped bound := by
  induction formula generalizing bound with
  | falsum => exact trivial
  | equal left right =>
      have parts := RawFormula.equal.inj fixed
      exact And.intro
        (left.wellScoped_of_raising_fixed bound parts.1)
        (right.wellScoped_of_raising_fixed bound parts.2)
  | conj left right leftHypothesis rightHypothesis =>
      have parts := RawFormula.conj.inj fixed
      exact And.intro (leftHypothesis bound parts.1)
        (rightHypothesis bound parts.2)
  | disj left right leftHypothesis rightHypothesis =>
      have parts := RawFormula.disj.inj fixed
      exact And.intro (leftHypothesis bound parts.1)
        (rightHypothesis bound parts.2)
  | impl left right leftHypothesis rightHypothesis =>
      have parts := RawFormula.impl.inj fixed
      exact And.intro (leftHypothesis bound parts.1)
        (rightHypothesis bound parts.2)
  | all body inductionHypothesis =>
      have bodyFixed := RawFormula.all.inj fixed
      exact inductionHypothesis (Nat.succ bound) bodyFixed
  | ex body inductionHypothesis =>
      have bodyFixed := RawFormula.ex.inj fixed
      exact inductionHypothesis (Nat.succ bound) bodyFixed

theorem wellScoped_of_wrapUniversalFormula
    (count base : Nat)
    (formula : RawFormula)
    (isScoped : (wrapUniversalFormula count formula).WellScoped base) :
    formula.WellScoped (base + count) := by
  induction count generalizing base with
  | zero => simpa [wrapUniversalFormula] using isScoped
  | succ count inductionHypothesis =>
      change (wrapUniversalFormula count formula).WellScoped
        (Nat.succ base) at isScoped
      have result := inductionHypothesis (Nat.succ base) isScoped
      have sameBound : Nat.succ base + count = base + Nat.succ count :=
        (Nat.succ_add base count).trans (Nat.add_succ base count).symm
      exact Eq.mp
        (congrArg (fun available => formula.WellScoped available) sameBound)
        result

theorem PRFunction.isFormulaCode_accepts
    (formula : RawFormula) :
      PRFunction.isFormulaCode.run
        (NatVector.cons formula.code NatVector.nil) = 1 := by
  rw [PRFunction.run_isFormulaCode]
  rw [formula.strictCode_accepts]
  rfl

theorem PRFunction.isTermCode_accepts
    (term : RawTerm) :
    PRFunction.isTermCode.run
        (NatVector.cons term.code NatVector.nil) = 1 := by
  rw [PRFunction.run_isTermCode]
  rw [term.strictCode_accepts]
  rfl

theorem PRFunction.isFormulaCode_sound
    (code : Nat)
    (accepted : PRFunction.isFormulaCode.run
      (NatVector.cons code NatVector.nil) = 1) :
    Exists fun formula : RawFormula => formula.code = code := by
  rw [PRFunction.run_isFormulaCode] at accepted
  exact strictFormulaCode_sound code
    ((natEqualBit_eq_one_iff _ _).mp accepted)

theorem PRFunction.isFormulaCode_positive_sound
    (code : Nat)
    (accepted : 0 < PRFunction.isFormulaCode.run
      (NatVector.cons code NatVector.nil)) :
    Exists fun formula : RawFormula => formula.code = code := by
  rw [PRFunction.run_isFormulaCode] at accepted
  exact strictFormulaCode_sound code
    ((natEqualBit_pos_iff _ _).mp accepted)

theorem PRFunction.isTermCode_sound
    (code : Nat)
    (accepted : PRFunction.isTermCode.run
      (NatVector.cons code NatVector.nil) = 1) :
    Exists fun term : RawTerm => term.code = code := by
  rw [PRFunction.run_isTermCode] at accepted
  exact strictTermCode_sound code
    ((natEqualBit_eq_one_iff _ _).mp accepted)

theorem PRFunction.isTermCode_positive_sound
    (code : Nat)
    (accepted : 0 < PRFunction.isTermCode.run
      (NatVector.cons code NatVector.nil)) :
    Exists fun term : RawTerm => term.code = code := by
  rw [PRFunction.run_isTermCode] at accepted
  exact strictTermCode_sound code
    ((natEqualBit_pos_iff _ _).mp accepted)

theorem PRFunction.isScopedFormulaCode_accepts
    {bound : Nat}
    (formula : ScopedFormula bound) :
    PRFunction.isScopedFormulaCode.run
        (NatVector.cons bound
          (NatVector.cons formula.raw.code NatVector.nil)) = 1 := by
  rw [PRFunction.run_isScopedFormulaCode]
  rw [PRFunction.isFormulaCode_accepts]
  rw [← wrapUniversalFormula_code]
  rw [machineRaiseFormulaCode_closed_fixed
    (wrapUniversalFormula bound formula.raw)
    (wrapUniversalFormula_wellScoped_zero
      formula.raw bound formula.isScoped) 1]
  exact (natAndBit_eq_one_iff _ _).mpr
    (And.intro (Nat.zero_lt_succ 0)
      ((natEqualBit_pos_iff _ _).mpr rfl))

theorem PRFunction.isScopedTermCode_accepts
    {bound : Nat}
    (term : ScopedTerm bound) :
    PRFunction.isScopedTermCode.run
        (NatVector.cons bound
          (NatVector.cons term.raw.code NatVector.nil)) = 1 := by
  rw [PRFunction.run_isScopedTermCode]
  rw [PRFunction.isTermCode_accepts]
  have envelopeAccepted := PRFunction.isScopedFormulaCode_accepts
    (ScopedFormula.equal term term)
  have envelopeCode : (ScopedFormula.equal term term).raw.code =
      Nat.succ (natPair 1 (natPair term.raw.code term.raw.code)) := rfl
  rw [envelopeCode] at envelopeAccepted
  exact (natAndBit_eq_one_iff _ _).mpr
    (And.intro (Nat.zero_lt_succ 0) (by
      rw [envelopeAccepted]
      exact Nat.zero_lt_succ 0))

theorem PRFunction.isScopedFormulaCode_sound
    (bound code : Nat)
    (accepted : PRFunction.isScopedFormulaCode.run
      (NatVector.cons bound (NatVector.cons code NatVector.nil)) = 1) :
    Exists fun formula : ScopedFormula bound => formula.raw.code = code := by
  rw [PRFunction.run_isScopedFormulaCode] at accepted
  have parts := (natAndBit_eq_one_iff _ _).mp accepted
  rw [PRFunction.run_isFormulaCode] at parts
  have syntaxExact : natUnpairRight (syntaxEntryAt code) = 1 :=
    (natEqualBit_pos_iff _ _).mp parts.1
  cases strictFormulaCode_sound code syntaxExact with
  | intro raw rawCode =>
      have fixedCode :
          machineRaiseFormulaCode
              (RelationalPerimeter.HeytingArithmetic.wrapUniversalCode bound code) 1 =
            RelationalPerimeter.HeytingArithmetic.wrapUniversalCode bound code :=
        (natEqualBit_pos_iff _ _).mp parts.2
      rw [← rawCode, ← wrapUniversalFormula_code,
        machineRaiseFormulaCode_code] at fixedCode
      have fixedFormula :
          (wrapUniversalFormula bound raw).raiseFreeVariables 1 =
            wrapUniversalFormula bound raw :=
        RawFormula.code_injective fixedCode
      have wrappedScoped :
          (wrapUniversalFormula bound raw).WellScoped 0 := by
        unfold RawFormula.raiseFreeVariables at fixedFormula
        exact RawFormula.wellScoped_of_raising_fixed _ 0 fixedFormula
      have rawScoped : raw.WellScoped bound := by
        simpa using
          (wellScoped_of_wrapUniversalFormula bound 0 raw wrappedScoped)
      exact Exists.intro
        ({ raw := raw, isScoped := rawScoped } : ScopedFormula bound)
        rawCode

theorem PRFunction.isScopedFormulaCode_positive_sound
    (bound code : Nat)
    (accepted : 0 < PRFunction.isScopedFormulaCode.run
      (NatVector.cons bound (NatVector.cons code NatVector.nil))) :
    Exists fun formula : ScopedFormula bound => formula.raw.code = code := by
  rw [PRFunction.run_isScopedFormulaCode] at accepted
  have parts := (natAndBit_pos_iff _ _).mp accepted
  rw [PRFunction.run_isFormulaCode] at parts
  have syntaxExact : natUnpairRight (syntaxEntryAt code) = 1 :=
    (natEqualBit_pos_iff _ _).mp parts.1
  cases strictFormulaCode_sound code syntaxExact with
  | intro raw rawCode =>
      have fixedCode :
          machineRaiseFormulaCode
              (RelationalPerimeter.HeytingArithmetic.wrapUniversalCode bound code) 1 =
            RelationalPerimeter.HeytingArithmetic.wrapUniversalCode bound code :=
        (natEqualBit_pos_iff _ _).mp parts.2
      rw [← rawCode, ← wrapUniversalFormula_code,
        machineRaiseFormulaCode_code] at fixedCode
      have fixedFormula :
          (wrapUniversalFormula bound raw).raiseFreeVariables 1 =
            wrapUniversalFormula bound raw :=
        RawFormula.code_injective fixedCode
      have wrappedScoped :
          (wrapUniversalFormula bound raw).WellScoped 0 := by
        unfold RawFormula.raiseFreeVariables at fixedFormula
        exact RawFormula.wellScoped_of_raising_fixed _ 0 fixedFormula
      have rawScoped : raw.WellScoped bound := by
        simpa using
          (wellScoped_of_wrapUniversalFormula bound 0 raw wrappedScoped)
      exact Exists.intro
        ({ raw := raw, isScoped := rawScoped } : ScopedFormula bound)
        rawCode

theorem PRFunction.isScopedTermCode_sound
    (bound code : Nat)
    (accepted : PRFunction.isScopedTermCode.run
      (NatVector.cons bound (NatVector.cons code NatVector.nil)) = 1) :
    Exists fun term : ScopedTerm bound => term.raw.code = code := by
  rw [PRFunction.run_isScopedTermCode] at accepted
  have parts := (natAndBit_eq_one_iff _ _).mp accepted
  rw [PRFunction.run_isTermCode] at parts
  have syntaxExact : natUnpairLeft (syntaxEntryAt code) = 1 :=
    (natEqualBit_pos_iff _ _).mp parts.1
  cases strictTermCode_sound code syntaxExact with
  | intro raw rawCode =>
      cases PRFunction.isScopedFormulaCode_positive_sound bound
          (Nat.succ (natPair 1 (natPair code code))) parts.2 with
      | intro formula formulaCode =>
          have formulaRaw : formula.raw = RawFormula.equal raw raw := by
            apply RawFormula.code_injective
            rw [formulaCode, RawFormula.code, rawCode]
          have termScoped : raw.WellScoped bound := by
            have formulaScoped := formula.isScoped
            rw [formulaRaw] at formulaScoped
            exact formulaScoped.1
          exact Exists.intro
            ({ raw := raw, isScoped := termScoped } : ScopedTerm bound)
            rawCode

theorem PRFunction.isScopedTermCode_positive_sound
    (bound code : Nat)
    (accepted : 0 < PRFunction.isScopedTermCode.run
      (NatVector.cons bound (NatVector.cons code NatVector.nil))) :
    Exists fun term : ScopedTerm bound => term.raw.code = code := by
  rw [PRFunction.run_isScopedTermCode] at accepted
  have parts := (natAndBit_pos_iff _ _).mp accepted
  rw [PRFunction.run_isTermCode] at parts
  have syntaxExact : natUnpairLeft (syntaxEntryAt code) = 1 :=
    (natEqualBit_pos_iff _ _).mp parts.1
  cases strictTermCode_sound code syntaxExact with
  | intro raw rawCode =>
      cases PRFunction.isScopedFormulaCode_positive_sound bound
          (Nat.succ (natPair 1 (natPair code code))) parts.2 with
      | intro formula formulaCode =>
          have formulaRaw : formula.raw = RawFormula.equal raw raw := by
            apply RawFormula.code_injective
            rw [formulaCode, RawFormula.code, rawCode]
          have termScoped : raw.WellScoped bound := by
            have formulaScoped := formula.isScoped
            rw [formulaRaw] at formulaScoped
            exact formulaScoped.1
          exact Exists.intro
            ({ raw := raw, isScoped := termScoped } : ScopedTerm bound)
            rawCode

end HeytingArithmetic
end RelationalPerimeter

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.HeytingArithmetic.PRFunction.isFormulaCode
#print axioms RelationalPerimeter.HeytingArithmetic.PRFunction.isTermCode
#print axioms RelationalPerimeter.HeytingArithmetic.PRFunction.isScopedFormulaCode
#print axioms RelationalPerimeter.HeytingArithmetic.PRFunction.isScopedTermCode
#print axioms RelationalPerimeter.HeytingArithmetic.PRFunction.isFormulaCode_sound
#print axioms RelationalPerimeter.HeytingArithmetic.PRFunction.isTermCode_sound
#print axioms RelationalPerimeter.HeytingArithmetic.PRFunction.isFormulaCode_positive_sound
#print axioms RelationalPerimeter.HeytingArithmetic.PRFunction.isTermCode_positive_sound
#print axioms RelationalPerimeter.HeytingArithmetic.PRFunction.isScopedFormulaCode_accepts
#print axioms RelationalPerimeter.HeytingArithmetic.PRFunction.isScopedTermCode_accepts
#print axioms RelationalPerimeter.HeytingArithmetic.PRFunction.isScopedFormulaCode_sound
#print axioms RelationalPerimeter.HeytingArithmetic.PRFunction.isScopedTermCode_sound
#print axioms RelationalPerimeter.HeytingArithmetic.PRFunction.isScopedFormulaCode_positive_sound
#print axioms RelationalPerimeter.HeytingArithmetic.PRFunction.isScopedTermCode_positive_sound
/- AXIOM_AUDIT_END -/
