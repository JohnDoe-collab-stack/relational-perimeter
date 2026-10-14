import RelationalPerimeter.Constitution.HeytingArithmetic.PrimitiveRecursiveTheoryHistory
import RelationalPerimeter.Constitution.HeytingArithmetic.PrimitiveRecursiveBetaLookup
import RelationalPerimeter.Constitution.HeytingArithmetic.ArithmeticAxiomChecking
import RelationalPerimeter.Constitution.HeytingArithmetic.ProofDecoding

/-!
# Primitive-recursive projections for proof codes

Every projection below is a positive `PRFunction` tree.  Together they erase
the typed archive header, proof-line record, and prefix-list accessors into the
numeric interface used by the line checker.
-/

namespace RelationalPerimeter
namespace HeytingArithmetic

private theorem proofCodeIndexZero_lt_one : 0 < 1 := Nat.zero_lt_succ 0
private theorem proofCodeIndexZero_lt_two : 0 < 2 := Nat.zero_lt_succ 1
private theorem proofCodeIndexOne_lt_two : 1 < 2 :=
  Nat.succ_lt_succ (Nat.zero_lt_succ 0)
private theorem proofCodeIndexZero_lt_three : 0 < 3 := Nat.zero_lt_succ 2
private theorem proofCodeIndexOne_lt_three : 1 < 3 :=
  Nat.succ_lt_succ (Nat.zero_lt_succ 1)
private theorem proofCodeIndexTwo_lt_three : 2 < 3 :=
  Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.zero_lt_succ 0))

/-! ## Prefix-list programs -/

def PRFunction.codedListHead : PRFunction 1 :=
  PRFunction.select PRFunction.identity PRFunction.zero
    (PRFunction.unaryIn PRFunction.unpairLeft PRFunction.predecessor)

def PRFunction.codedListTail : PRFunction 1 :=
  PRFunction.select PRFunction.identity PRFunction.zero
    (PRFunction.unaryIn PRFunction.unpairRight PRFunction.predecessor)

def PRFunction.codedListTailIteration : PRFunction 3 :=
  PRFunction.unaryIn PRFunction.codedListTail
    (PRFunction.projection 3 1 proofCodeIndexOne_lt_three)

def PRFunction.codedListDropCore : PRFunction 2 :=
  PRFunction.primitiveRecursion PRFunction.identity
    PRFunction.codedListTailIteration

/-- Input order is `(listCode,index)`. -/
def PRFunction.codedListDrop : PRFunction 2 :=
  PRFunction.composition PRFunction.codedListDropCore
    (PRFunctionVector.cons
      (PRFunction.projection 2 1 proofCodeIndexOne_lt_two)
      (PRFunctionVector.singleton
        (PRFunction.projection 2 0 proofCodeIndexZero_lt_two)))

def PRFunction.codedListEntry : PRFunction 2 :=
  PRFunction.unaryIn PRFunction.codedListHead PRFunction.codedListDrop

def PRFunction.codedListCons : PRFunction 2 :=
  PRFunction.machineStackPush

def PRFunction.codedListSingleton : PRFunction 1 :=
  PRFunction.binaryIn PRFunction.codedListCons PRFunction.identity
    (PRFunction.constant 1 0)

def PRFunction.codedListPair : PRFunction 2 :=
  let first := PRFunction.projection 2 0 proofCodeIndexZero_lt_two
  let second := PRFunction.projection 2 1 proofCodeIndexOne_lt_two
  PRFunction.binaryIn PRFunction.codedListCons first
    (PRFunction.unaryIn PRFunction.codedListSingleton second)

def PRFunction.codedListTriple : PRFunction 3 :=
  let first := PRFunction.projection 3 0 proofCodeIndexZero_lt_three
  let second := PRFunction.projection 3 1 proofCodeIndexOne_lt_three
  let third := PRFunction.projection 3 2 proofCodeIndexTwo_lt_three
  let tail := PRFunction.composition PRFunction.codedListPair
    (PRFunctionVector.cons second (PRFunctionVector.singleton third))
  PRFunction.binaryIn PRFunction.codedListCons first tail

@[simp] theorem PRFunction.run_codedListHead (code : Nat) :
    PRFunction.codedListHead.run (NatVector.cons code NatVector.nil) =
      _root_.RelationalPerimeter.HeytingArithmetic.codedListHead code := by
  cases code with
  | zero =>
      unfold PRFunction.codedListHead
        _root_.RelationalPerimeter.HeytingArithmetic.codedListHead
      rw [PRFunction.run_select, PRFunction.run_identity,
        PRFunction.run_zero]
      rfl
  | succ encoded =>
      unfold PRFunction.codedListHead
        _root_.RelationalPerimeter.HeytingArithmetic.codedListHead
      rw [PRFunction.run_select, PRFunction.run_identity,
        PRFunction.run_zero]
      rw [PRFunction.run_unaryIn, PRFunction.run_unpairLeft,
        PRFunction.run_predecessor]
      simp only [Nat.add_one, natIfZero, Nat.pred_succ]
      exact (congrArg Prod.fst
        (natUnpair_eq_unpairComponents encoded)).symm

@[simp] theorem PRFunction.run_codedListTail (code : Nat) :
    PRFunction.codedListTail.run (NatVector.cons code NatVector.nil) =
      _root_.RelationalPerimeter.HeytingArithmetic.codedListTail code := by
  cases code with
  | zero =>
      unfold PRFunction.codedListTail
        _root_.RelationalPerimeter.HeytingArithmetic.codedListTail
      rw [PRFunction.run_select, PRFunction.run_identity,
        PRFunction.run_zero]
      rfl
  | succ encoded =>
      unfold PRFunction.codedListTail
        _root_.RelationalPerimeter.HeytingArithmetic.codedListTail
      rw [PRFunction.run_select, PRFunction.run_identity,
        PRFunction.run_zero]
      rw [PRFunction.run_unaryIn, PRFunction.run_unpairRight,
        PRFunction.run_predecessor]
      simp only [Nat.add_one, natIfZero, Nat.pred_succ]
      exact (congrArg Prod.snd
        (natUnpair_eq_unpairComponents encoded)).symm

@[simp] theorem PRFunction.run_codedListTailIteration
    (counter previous parameter : Nat) :
    PRFunction.codedListTailIteration.run
        (NatVector.cons counter
          (NatVector.cons previous
            (NatVector.cons parameter NatVector.nil))) =
      _root_.RelationalPerimeter.HeytingArithmetic.codedListTail previous := by
  unfold PRFunction.codedListTailIteration
  rw [PRFunction.run_unaryIn, PRFunction.run_projection,
    NatVector.get_cons_succ, NatVector.get_cons_zero,
    PRFunction.run_codedListTail]

theorem PRFunction.run_codedListDropCore
    (index code : Nat) :
    PRFunction.codedListDropCore.run
        (NatVector.cons index (NatVector.cons code NatVector.nil)) =
      Nat.rec code
        (fun _counter previous =>
          _root_.RelationalPerimeter.HeytingArithmetic.codedListTail previous) index := by
  induction index with
  | zero => rfl
  | succ index inductionHypothesis =>
      change PRFunction.codedListTailIteration.run
        (NatVector.cons index
          (NatVector.cons
            (PRFunction.codedListDropCore.run
              (NatVector.cons index (NatVector.cons code NatVector.nil)))
            (NatVector.cons code NatVector.nil))) = _
      rw [PRFunction.run_codedListTailIteration, inductionHypothesis]

def codedListDrop : Nat -> Nat -> Nat
  | code, 0 => code
  | code, Nat.succ index =>
      codedListDrop
        (_root_.RelationalPerimeter.HeytingArithmetic.codedListTail code) index

theorem codedListDrop_succ_right (code index : Nat) :
    codedListDrop code (Nat.succ index) =
      _root_.RelationalPerimeter.HeytingArithmetic.codedListTail
        (codedListDrop code index) := by
  induction index generalizing code with
  | zero => rfl
  | succ index inductionHypothesis =>
      change codedListDrop
          (_root_.RelationalPerimeter.HeytingArithmetic.codedListTail code)
          (Nat.succ index) =
        _root_.RelationalPerimeter.HeytingArithmetic.codedListTail
          (codedListDrop
            (_root_.RelationalPerimeter.HeytingArithmetic.codedListTail code) index)
      exact inductionHypothesis
        (_root_.RelationalPerimeter.HeytingArithmetic.codedListTail code)

theorem codedListDrop_eq_rec (code index : Nat) :
    codedListDrop code index =
      Nat.rec code
        (fun _counter previous =>
          _root_.RelationalPerimeter.HeytingArithmetic.codedListTail previous) index := by
  induction index generalizing code with
  | zero => rfl
  | succ index inductionHypothesis =>
      rw [codedListDrop_succ_right, inductionHypothesis]

@[simp] theorem PRFunction.run_codedListDrop (code index : Nat) :
    PRFunction.codedListDrop.run
        (NatVector.cons code (NatVector.cons index NatVector.nil)) =
      _root_.RelationalPerimeter.HeytingArithmetic.codedListDrop code index := by
  unfold PRFunction.codedListDrop
  rw [PRFunction.run_composition, PRFunctionVector.run_cons,
    PRFunctionVector.run_singleton, PRFunction.run_projection,
    NatVector.get_cons_succ, NatVector.get_cons_zero,
    PRFunction.run_projection, NatVector.get_cons_zero,
    PRFunction.run_codedListDropCore, codedListDrop_eq_rec]

@[simp] theorem PRFunction.run_codedListEntry (code index : Nat) :
    PRFunction.codedListEntry.run
        (NatVector.cons code (NatVector.cons index NatVector.nil)) =
      _root_.RelationalPerimeter.HeytingArithmetic.codedListEntry code index := by
  unfold PRFunction.codedListEntry
  rw [PRFunction.run_unaryIn, PRFunction.run_codedListDrop,
    PRFunction.run_codedListHead]
  induction index generalizing code with
  | zero => rfl
  | succ index inductionHypothesis =>
      change _root_.RelationalPerimeter.HeytingArithmetic.codedListHead
        (_root_.RelationalPerimeter.HeytingArithmetic.codedListDrop
          (_root_.RelationalPerimeter.HeytingArithmetic.codedListTail code) index) = _
      exact inductionHypothesis
        (_root_.RelationalPerimeter.HeytingArithmetic.codedListTail code)

@[simp] theorem PRFunction.run_codedListCons (head tail : Nat) :
    PRFunction.codedListCons.run
        (NatVector.cons head (NatVector.cons tail NatVector.nil)) =
      Nat.succ (natPair head tail) := by
  exact PRFunction.run_machineStackPush head tail

@[simp] theorem PRFunction.run_codedListSingleton (value : Nat) :
    PRFunction.codedListSingleton.run (NatVector.cons value NatVector.nil) =
      quoteNatList [value] := by
  unfold PRFunction.codedListSingleton
  rw [PRFunction.run_binaryIn, PRFunction.run_identity,
    PRFunction.run_constant, PRFunction.run_codedListCons]
  rfl

@[simp] theorem PRFunction.run_codedListPair (first second : Nat) :
    PRFunction.codedListPair.run
        (NatVector.cons first (NatVector.cons second NatVector.nil)) =
      quoteNatList [first, second] := by
  unfold PRFunction.codedListPair
  rw [PRFunction.run_binaryIn, PRFunction.run_projection,
    NatVector.get_cons_zero, PRFunction.run_unaryIn,
    PRFunction.run_projection, NatVector.get_cons_succ,
    NatVector.get_cons_zero, PRFunction.run_codedListSingleton,
    PRFunction.run_codedListCons]
  rfl

@[simp] theorem PRFunction.run_codedListTriple
    (first second third : Nat) :
    PRFunction.codedListTriple.run
        (NatVector.cons first
          (NatVector.cons second
            (NatVector.cons third NatVector.nil))) =
      quoteNatList [first, second, third] := by
  unfold PRFunction.codedListTriple
  rw [PRFunction.run_binaryIn, PRFunction.run_projection,
    NatVector.get_cons_zero, PRFunction.run_composition,
    PRFunctionVector.run_cons, PRFunctionVector.run_singleton,
    PRFunction.run_projection, NatVector.get_cons_succ,
    NatVector.get_cons_zero, PRFunction.run_projection,
    NatVector.get_cons_succ, NatVector.get_cons_succ,
    NatVector.get_cons_zero, PRFunction.run_codedListPair,
    PRFunction.run_codedListCons]
  rfl

/-! ## Nested-pair projections -/

def PRFunction.pairLeftIn
    {arity : Nat} (source : PRFunction arity) : PRFunction arity :=
  PRFunction.unaryIn PRFunction.unpairLeft source

def PRFunction.pairRightIn
    {arity : Nat} (source : PRFunction arity) : PRFunction arity :=
  PRFunction.unaryIn PRFunction.unpairRight source

def PRFunction.proofLineRule : PRFunction 1 :=
  PRFunction.pairLeftIn PRFunction.identity

def PRFunction.proofLineAfterRule : PRFunction 1 :=
  PRFunction.pairRightIn PRFunction.identity

def PRFunction.proofLineBound : PRFunction 1 :=
  PRFunction.pairLeftIn PRFunction.proofLineAfterRule

def PRFunction.proofLineAfterBound : PRFunction 1 :=
  PRFunction.pairRightIn PRFunction.proofLineAfterRule

def PRFunction.proofLineContext : PRFunction 1 :=
  PRFunction.pairLeftIn PRFunction.proofLineAfterBound

def PRFunction.proofLineAfterContext : PRFunction 1 :=
  PRFunction.pairRightIn PRFunction.proofLineAfterBound

def PRFunction.proofLineConclusion : PRFunction 1 :=
  PRFunction.pairLeftIn PRFunction.proofLineAfterContext

def PRFunction.proofLineLists : PRFunction 1 :=
  PRFunction.pairRightIn PRFunction.proofLineAfterContext

def PRFunction.proofLinePremises : PRFunction 1 :=
  PRFunction.pairLeftIn PRFunction.proofLineLists

def PRFunction.proofLineParameters : PRFunction 1 :=
  PRFunction.pairRightIn PRFunction.proofLineLists

def PRFunction.archiveLineCount : PRFunction 1 :=
  PRFunction.pairLeftIn PRFunction.identity

def PRFunction.archiveBetaPair : PRFunction 1 :=
  PRFunction.pairRightIn PRFunction.identity

def PRFunction.archiveDividend : PRFunction 1 :=
  PRFunction.pairLeftIn PRFunction.archiveBetaPair

def PRFunction.archiveCoefficient : PRFunction 1 :=
  PRFunction.pairRightIn PRFunction.archiveBetaPair

def PRFunction.archiveLineCode : PRFunction 2 :=
  let archive := PRFunction.projection 2 0 proofCodeIndexZero_lt_two
  let index := PRFunction.projection 2 1 proofCodeIndexOne_lt_two
  let dividend := PRFunction.unaryIn PRFunction.archiveDividend archive
  let coefficient := PRFunction.unaryIn PRFunction.archiveCoefficient archive
  PRFunction.composition PRFunction.betaLookup
    (PRFunctionVector.cons dividend
      (PRFunctionVector.cons coefficient
        (PRFunctionVector.singleton index)))

macro "prove_unary_projection" : tactic =>
  `(tactic|
    repeat first
      | rw [PRFunction.run_unaryIn]
      | rw [PRFunction.run_unpairLeft]
      | rw [PRFunction.run_unpairRight]
      | rw [PRFunction.run_identity]
      | rfl)

@[simp] theorem PRFunction.run_proofLineRule (code : Nat) :
    PRFunction.proofLineRule.run (NatVector.cons code NatVector.nil) =
      natUnpairLeft code := by
  unfold PRFunction.proofLineRule PRFunction.pairLeftIn
  prove_unary_projection

@[simp] theorem PRFunction.run_proofLineAfterRule (code : Nat) :
    PRFunction.proofLineAfterRule.run (NatVector.cons code NatVector.nil) =
      natUnpairRight code := by
  unfold PRFunction.proofLineAfterRule PRFunction.pairRightIn
  prove_unary_projection

@[simp] theorem PRFunction.run_proofLineBound (code : Nat) :
    PRFunction.proofLineBound.run (NatVector.cons code NatVector.nil) =
      natUnpairLeft (natUnpairRight code) := by
  unfold PRFunction.proofLineBound PRFunction.pairLeftIn
  rw [PRFunction.run_unaryIn, PRFunction.run_proofLineAfterRule,
    PRFunction.run_unpairLeft]

@[simp] theorem PRFunction.run_proofLineAfterBound (code : Nat) :
    PRFunction.proofLineAfterBound.run (NatVector.cons code NatVector.nil) =
      natUnpairRight (natUnpairRight code) := by
  unfold PRFunction.proofLineAfterBound PRFunction.pairRightIn
  rw [PRFunction.run_unaryIn, PRFunction.run_proofLineAfterRule,
    PRFunction.run_unpairRight]

@[simp] theorem PRFunction.run_proofLineContext (code : Nat) :
    PRFunction.proofLineContext.run (NatVector.cons code NatVector.nil) =
      natUnpairLeft (natUnpairRight (natUnpairRight code)) := by
  unfold PRFunction.proofLineContext PRFunction.pairLeftIn
  rw [PRFunction.run_unaryIn, PRFunction.run_proofLineAfterBound,
    PRFunction.run_unpairLeft]

@[simp] theorem PRFunction.run_proofLineAfterContext (code : Nat) :
    PRFunction.proofLineAfterContext.run (NatVector.cons code NatVector.nil) =
      natUnpairRight (natUnpairRight (natUnpairRight code)) := by
  unfold PRFunction.proofLineAfterContext PRFunction.pairRightIn
  rw [PRFunction.run_unaryIn, PRFunction.run_proofLineAfterBound,
    PRFunction.run_unpairRight]

@[simp] theorem PRFunction.run_proofLineConclusion (code : Nat) :
    PRFunction.proofLineConclusion.run (NatVector.cons code NatVector.nil) =
      natUnpairLeft
        (natUnpairRight (natUnpairRight (natUnpairRight code))) := by
  unfold PRFunction.proofLineConclusion PRFunction.pairLeftIn
  rw [PRFunction.run_unaryIn, PRFunction.run_proofLineAfterContext,
    PRFunction.run_unpairLeft]

@[simp] theorem PRFunction.run_proofLineLists (code : Nat) :
    PRFunction.proofLineLists.run (NatVector.cons code NatVector.nil) =
      natUnpairRight
        (natUnpairRight (natUnpairRight (natUnpairRight code))) := by
  unfold PRFunction.proofLineLists PRFunction.pairRightIn
  rw [PRFunction.run_unaryIn, PRFunction.run_proofLineAfterContext,
    PRFunction.run_unpairRight]

@[simp] theorem PRFunction.run_proofLinePremises (code : Nat) :
    PRFunction.proofLinePremises.run (NatVector.cons code NatVector.nil) =
      natUnpairLeft
        (natUnpairRight
          (natUnpairRight (natUnpairRight (natUnpairRight code)))) := by
  unfold PRFunction.proofLinePremises PRFunction.pairLeftIn
  rw [PRFunction.run_unaryIn, PRFunction.run_proofLineLists,
    PRFunction.run_unpairLeft]

@[simp] theorem PRFunction.run_proofLineParameters (code : Nat) :
    PRFunction.proofLineParameters.run (NatVector.cons code NatVector.nil) =
      natUnpairRight
        (natUnpairRight
          (natUnpairRight (natUnpairRight (natUnpairRight code)))) := by
  unfold PRFunction.proofLineParameters PRFunction.pairRightIn
  rw [PRFunction.run_unaryIn, PRFunction.run_proofLineLists,
    PRFunction.run_unpairRight]

@[simp] theorem PRFunction.run_archiveLineCount (code : Nat) :
    PRFunction.archiveLineCount.run (NatVector.cons code NatVector.nil) =
      natUnpairLeft code := by
  unfold PRFunction.archiveLineCount PRFunction.pairLeftIn
  prove_unary_projection

@[simp] theorem PRFunction.run_archiveBetaPair (code : Nat) :
    PRFunction.archiveBetaPair.run (NatVector.cons code NatVector.nil) =
      natUnpairRight code := by
  unfold PRFunction.archiveBetaPair PRFunction.pairRightIn
  prove_unary_projection

@[simp] theorem PRFunction.run_archiveDividend (code : Nat) :
    PRFunction.archiveDividend.run (NatVector.cons code NatVector.nil) =
      natUnpairLeft (natUnpairRight code) := by
  unfold PRFunction.archiveDividend PRFunction.pairLeftIn
  rw [PRFunction.run_unaryIn, PRFunction.run_archiveBetaPair,
    PRFunction.run_unpairLeft]

@[simp] theorem PRFunction.run_archiveCoefficient (code : Nat) :
    PRFunction.archiveCoefficient.run (NatVector.cons code NatVector.nil) =
      natUnpairRight (natUnpairRight code) := by
  unfold PRFunction.archiveCoefficient PRFunction.pairRightIn
  rw [PRFunction.run_unaryIn, PRFunction.run_archiveBetaPair,
    PRFunction.run_unpairRight]

@[simp] theorem PRFunction.run_archiveLineCode (archive index : Nat) :
    PRFunction.archiveLineCode.run
        (NatVector.cons archive (NatVector.cons index NatVector.nil)) =
      betaComponent
        (natUnpairLeft (natUnpairRight archive))
        (natUnpairRight (natUnpairRight archive)) index := by
  unfold PRFunction.archiveLineCode
  rw [PRFunction.run_composition, PRFunctionVector.run_cons,
    PRFunctionVector.run_cons, PRFunctionVector.run_singleton,
    PRFunction.run_unaryIn, PRFunction.run_projection,
    NatVector.get_cons_zero, PRFunction.run_archiveDividend,
    PRFunction.run_unaryIn, PRFunction.run_projection,
    NatVector.get_cons_zero, PRFunction.run_archiveCoefficient,
    PRFunction.run_projection, NatVector.get_cons_succ,
    NatVector.get_cons_zero, PRFunction.betaLookup_run]

end HeytingArithmetic
end RelationalPerimeter

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.HeytingArithmetic.PRFunction.codedListEntry
#print axioms RelationalPerimeter.HeytingArithmetic.PRFunction.proofLineRule
#print axioms RelationalPerimeter.HeytingArithmetic.PRFunction.proofLineConclusion
#print axioms RelationalPerimeter.HeytingArithmetic.PRFunction.archiveLineCount
#print axioms RelationalPerimeter.HeytingArithmetic.PRFunction.archiveLineCode
/- AXIOM_AUDIT_END -/
