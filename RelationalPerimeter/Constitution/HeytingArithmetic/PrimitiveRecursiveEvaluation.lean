import RelationalPerimeter.Constitution.HeytingArithmetic.PrimitiveRecursiveSyntaxCoding

/-!
# Total evaluator for positive primitive-recursive programs

The evaluator is defined only by recursion on the positive program tree and,
in the primitive-recursion case, on the explicit natural counter.  It carries
no arbitrary Lean function.  Its correctness is witnessed by the original
positive `Evaluates` relation.
-/

namespace RelationalPerimeter
namespace HeytingArithmetic

/-- Construct a vector pointwise by primitive recursion on its length. -/
def NatVector.tabulate :
    (length : Nat) ->
    ((index : Nat) -> index < length -> Nat) ->
    NatVector length
  | 0, _values => NatVector.nil
  | Nat.succ length, values =>
      NatVector.cons
        (values 0 (Nat.zero_lt_succ length))
        (NatVector.tabulate length
          (fun index bounded =>
            values (Nat.succ index) (Nat.succ_lt_succ bounded)))

/-- Remove the first entry without dependent elimination on the vector. -/
def NatVector.dropFirst
    {length : Nat}
    (values : NatVector (Nat.succ length)) : NatVector length :=
  NatVector.tabulate length fun index bounded =>
    values.get (Nat.succ index) (Nat.succ_lt_succ bounded)

@[simp] theorem NatVector.get_cons_zero
    {length : Nat}
    (head : Nat)
    (tail : NatVector length)
    (bounded : 0 < Nat.succ length) :
    (NatVector.cons head tail).get 0 bounded = head := rfl

@[simp] theorem NatVector.get_cons_succ
    {length index : Nat}
    (head : Nat)
    (tail : NatVector length)
    (bounded : Nat.succ index < Nat.succ length) :
    (NatVector.cons head tail).get (Nat.succ index) bounded =
      tail.get index (Nat.lt_of_succ_lt_succ bounded) := rfl

/-- Pointwise removal recovers the constructor tail. -/
@[simp] theorem NatVector.dropFirst_cons
    {length : Nat}
    (head : Nat)
    (tail : NatVector length) :
    (NatVector.cons head tail).dropFirst = tail := by
  induction tail generalizing head with
  | nil => rfl
  | cons next rest inductionHypothesis =>
      change NatVector.cons next
        ((NatVector.cons next rest).dropFirst) =
          NatVector.cons next rest
      rw [inductionHypothesis next]

/-- Total evaluator of a positive primitive-recursive program. -/
abbrev PRFunction.run
    {arity : Nat}
    (program : PRFunction arity)
    (inputs : NatVector arity) : Nat :=
  PRFunction.runCore program inputs

/-- Pointwise total evaluator for a vector of positive programs. -/
abbrev PRFunctionVector.run
    {inputArity outputArity : Nat}
    (programs : PRFunctionVector inputArity outputArity)
    (inputs : NatVector inputArity) : NatVector outputArity :=
  PRFunctionVector.runCore programs inputs

@[simp] theorem PRFunction.run_zero
    {arity : Nat}
    (inputs : NatVector arity) :
    (PRFunction.zero : PRFunction arity).run inputs = 0 := rfl

@[simp] theorem PRFunction.run_successor
    (value : Nat) :
    PRFunction.successor.run
      (NatVector.cons value NatVector.nil) = Nat.succ value := rfl

@[simp] theorem PRFunction.run_projection
    (arity index : Nat)
    (bounded : index < arity)
    (inputs : NatVector arity) :
    (PRFunction.projection arity index bounded).run inputs =
      inputs.get index bounded := rfl

@[simp] theorem PRFunction.run_composition
    {inputArity outputArity : Nat}
    (outer : PRFunction outputArity)
    (inner : PRFunctionVector inputArity outputArity)
    (inputs : NatVector inputArity) :
    (PRFunction.composition outer inner).run inputs =
      outer.run (inner.run inputs) := rfl

@[simp] theorem PRFunction.run_primitive_zero
    {parameterArity : Nat}
    (base : PRFunction parameterArity)
    (step : PRFunction (Nat.succ (Nat.succ parameterArity)))
    (parameters : NatVector parameterArity) :
    (PRFunction.primitiveRecursion base step).run
      (NatVector.cons 0 parameters) = base.run parameters :=
  PRFunction.Evaluates.runCore_primitive_zero base step parameters

@[simp] theorem PRFunction.run_primitive_succ
    {parameterArity : Nat}
    (base : PRFunction parameterArity)
    (step : PRFunction (Nat.succ (Nat.succ parameterArity)))
    (counter : Nat)
    (parameters : NatVector parameterArity) :
    (PRFunction.primitiveRecursion base step).run
        (NatVector.cons (Nat.succ counter) parameters) =
      step.run
        (NatVector.cons counter
          (NatVector.cons
            ((PRFunction.primitiveRecursion base step).run
              (NatVector.cons counter parameters))
            parameters)) :=
  PRFunction.Evaluates.runCore_primitive_succ
    base step counter parameters

@[simp] theorem PRFunctionVector.run_nil
    {inputArity : Nat}
    (inputs : NatVector inputArity) :
    (PRFunctionVector.nil : PRFunctionVector inputArity 0).run inputs =
      NatVector.nil := rfl

@[simp] theorem PRFunctionVector.run_cons
    {inputArity length : Nat}
    (head : PRFunction inputArity)
    (tail : PRFunctionVector inputArity length)
    (inputs : NatVector inputArity) :
    (PRFunctionVector.cons head tail).run inputs =
      NatVector.cons (head.run inputs) (tail.run inputs) := rfl

@[simp] theorem PRFunctionVector.run_singleton
    {inputArity : Nat}
    (program : PRFunction inputArity)
    (inputs : NatVector inputArity) :
    (PRFunctionVector.singleton program).run inputs =
      NatVector.cons (program.run inputs) NatVector.nil := by
  unfold PRFunctionVector.singleton
  rfl


/-- Packaged correctness of a compiled program evaluator. -/
structure PRFunctionRunCorrect
    {arity : Nat}
    (program : PRFunction arity) : Type where
  apply : (inputs : NatVector arity) ->
    PRFunction.Evaluates program inputs (program.run inputs)

/-- Packaged pointwise correctness of a compiled vector evaluator. -/
structure PRFunctionVectorRunCorrect
    {inputArity outputArity : Nat}
    (programs : PRFunctionVector inputArity outputArity) : Type where
  apply : (inputs : NatVector inputArity) ->
    PRFunctionVector.Evaluates programs inputs (programs.run inputs)

/-- Structural correctness package for one positive program. -/
def PRFunction.runCorrect
    {arity : Nat}
    (program : PRFunction arity) :
    PRFunctionRunCorrect program :=
  { apply := fun _inputs => rfl }

/-- Structural correctness package for a program vector. -/
def PRFunctionVector.runCorrect
    {inputArity outputArity : Nat}
    (programs : PRFunctionVector inputArity outputArity) :
    PRFunctionVectorRunCorrect programs :=
  { apply := fun _inputs => rfl }

/-- The structural evaluator always produces positive execution evidence. -/
theorem PRFunction.run_evaluates
    {arity : Nat}
    (program : PRFunction arity)
    (inputs : NatVector arity) :
    PRFunction.Evaluates program inputs (program.run inputs) :=
  rfl

/-- The vector evaluator always produces pointwise execution evidence. -/
theorem PRFunctionVector.run_evaluates
    {inputArity outputArity : Nat}
    (programs : PRFunctionVector inputArity outputArity)
    (inputs : NatVector inputArity) :
    PRFunctionVector.Evaluates programs inputs (programs.run inputs) :=
  rfl

/-- Every positive execution computes the structural evaluator's result. -/
theorem PRFunction.Evaluates.output_eq_run
    {arity : Nat}
    {program : PRFunction arity}
    {inputs : NatVector arity}
    {output : Nat}
    (evaluation : PRFunction.Evaluates program inputs output) :
    output = program.run inputs :=
  evaluation

/-- Every vector execution computes the structural vector evaluator's result. -/
theorem PRFunctionVector.Evaluates.output_eq_run
    {inputArity outputArity : Nat}
    {programs : PRFunctionVector inputArity outputArity}
    {inputs : NatVector inputArity}
    {output : NatVector outputArity}
    (evaluation : PRFunctionVector.Evaluates programs inputs output) :
    output = programs.run inputs :=
  evaluation

/-- Positive program execution is functional. -/
theorem PRFunction.evaluates_unique
    {arity : Nat}
    {program : PRFunction arity}
    {inputs : NatVector arity}
    {left right : Nat}
    (leftEvaluation : PRFunction.Evaluates program inputs left)
    (rightEvaluation : PRFunction.Evaluates program inputs right) :
    left = right :=
  leftEvaluation.output_eq_run.trans rightEvaluation.output_eq_run.symm

/-- Pointwise vector execution is functional. -/
theorem PRFunctionVector.evaluates_unique
    {inputArity outputArity : Nat}
    {programs : PRFunctionVector inputArity outputArity}
    {inputs : NatVector inputArity}
    {left right : NatVector outputArity}
    (leftEvaluation : PRFunctionVector.Evaluates programs inputs left)
    (rightEvaluation : PRFunctionVector.Evaluates programs inputs right) :
    left = right :=
  leftEvaluation.output_eq_run.trans rightEvaluation.output_eq_run.symm

end HeytingArithmetic
end RelationalPerimeter

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.HeytingArithmetic.PRFunction.run
#print axioms RelationalPerimeter.HeytingArithmetic.PRFunctionVector.run
#print axioms RelationalPerimeter.HeytingArithmetic.PRFunctionVector.run_singleton
#print axioms RelationalPerimeter.HeytingArithmetic.PRFunction.run_evaluates
#print axioms RelationalPerimeter.HeytingArithmetic.PRFunctionVector.run_evaluates
#print axioms RelationalPerimeter.HeytingArithmetic.PRFunction.evaluates_unique
#print axioms RelationalPerimeter.HeytingArithmetic.PRFunctionVector.evaluates_unique
#print axioms RelationalPerimeter.HeytingArithmetic.PRFunction.runCorrect
#print axioms RelationalPerimeter.HeytingArithmetic.PRFunction.run_primitive_zero
#print axioms RelationalPerimeter.HeytingArithmetic.PRFunction.run_primitive_succ
/- AXIOM_AUDIT_END -/
