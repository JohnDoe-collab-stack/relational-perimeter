import RelationalPerimeter.Instances.HeytingArithmetic.CodeSubstitution

/-!
# Positive language of primitive-recursive programs

This module starts gate G5 with an intrinsically generated program language.
There is no constructor carrying an arbitrary Lean function.  Consequently a
future certificate for code substitution must be an actual program tree.
-/

namespace RelationalPerimeter
namespace HeytingArithmetic

/-- Length-indexed vectors used as program inputs and intermediate outputs. -/
inductive NatVector : Nat -> Type
  | nil : NatVector 0
  | cons {length : Nat} : Nat -> NatVector length -> NatVector (Nat.succ length)

/-- Total vector access, returning zero outside the indexed extent. -/
def NatVector.getD {length : Nat} (values : NatVector length) : Nat -> Nat
  | 0 =>
      match values with
      | NatVector.nil => 0
      | NatVector.cons head _tail => head
  | Nat.succ index =>
      match values with
      | NatVector.nil => 0
      | NatVector.cons _head tail => tail.getD index

/-- Build an indexed vector from a total component function. -/
def NatVector.tabulateD :
    (length : Nat) -> (Nat -> Nat) -> NatVector length
  | 0, _values => NatVector.nil
  | Nat.succ length, values =>
      NatVector.cons (values 0)
        (NatVector.tabulateD length (fun index => values (Nat.succ index)))

/-- Remove the first component without dependent pattern elimination. -/
def NatVector.tailD
    {length : Nat}
    (values : NatVector (Nat.succ length)) : NatVector length :=
  NatVector.tabulateD length (fun index => values.getD (Nat.succ index))

/-- Tabulating the total components of a vector reconstructs it. -/
theorem NatVector.tabulateD_getD_self
    {length : Nat}
    (values : NatVector length) :
    NatVector.tabulateD length values.getD = values := by
  induction values with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      exact congrArg (fun rest => NatVector.cons head rest)
        inductionHypothesis

/-- The total tail of an explicit constructor is its constructor tail. -/
theorem NatVector.tailD_cons
    {length : Nat}
    (head : Nat)
    (tail : NatVector length) :
    (NatVector.cons head tail).tailD = tail :=
  NatVector.tabulateD_getD_self tail

/-- Every nonempty vector is its total head followed by its total tail. -/
theorem NatVector.rebuildD
    {length : Nat}
    (values : NatVector (Nat.succ length)) :
    NatVector.cons (values.getD 0) values.tailD = values :=
  NatVector.tabulateD_getD_self values

/-- Constructive lookup in a length-indexed vector. -/
def NatVector.get
    {length : Nat}
    (values : NatVector length)
    (index : Nat)
    (bounded : index < length) :
    Nat :=
  match values with
  | NatVector.nil => (Nat.not_lt_zero index bounded).elim
  | NatVector.cons head tail =>
      match index with
      | 0 => head
      | Nat.succ inner =>
          tail.get inner (Nat.lt_of_succ_lt_succ bounded)

mutual
  /-- Standard primitive-recursive program trees, indexed by input arity. -/
  inductive PRFunction : Nat -> Type
    | zero {arity : Nat} : PRFunction arity
    | successor : PRFunction 1
    | projection
        (arity index : Nat)
        (bounded : index < arity) :
        PRFunction arity
    | composition
        {inputArity outputArity : Nat} :
        PRFunction outputArity ->
        PRFunctionVector inputArity outputArity ->
        PRFunction inputArity
    | primitiveRecursion
        {parameterArity : Nat} :
        PRFunction parameterArity ->
        PRFunction (Nat.succ (Nat.succ parameterArity)) ->
        PRFunction (Nat.succ parameterArity)

  /-- A vector of programs sharing the same input arity. -/
  inductive PRFunctionVector : Nat -> Nat -> Type
    | nil {inputArity : Nat} : PRFunctionVector inputArity 0
    | cons
        {inputArity length : Nat} :
        PRFunction inputArity ->
        PRFunctionVector inputArity length ->
        PRFunctionVector inputArity (Nat.succ length)
end

mutual
  /-- Total structural evaluator for one positive program. -/
  def PRFunction.runCore :
      {arity : Nat} -> PRFunction arity -> NatVector arity -> Nat
    | _, PRFunction.zero, _inputs => 0
    | _, PRFunction.successor, inputs => Nat.succ (inputs.getD 0)
    | _, PRFunction.projection _arity index bounded, inputs =>
        inputs.get index bounded
    | _, PRFunction.composition outer inner, inputs =>
        PRFunction.runCore outer (PRFunctionVector.runCore inner inputs)
    | _, PRFunction.primitiveRecursion base step, inputs =>
        Nat.rec
          (PRFunction.runCore base inputs.tailD)
          (fun counter previous =>
            PRFunction.runCore step
              (NatVector.cons counter
                (NatVector.cons previous inputs.tailD)))
          (inputs.getD 0)

  /-- Total structural evaluator for a vector of positive programs. -/
  def PRFunctionVector.runCore :
      {inputArity outputArity : Nat} ->
      PRFunctionVector inputArity outputArity ->
      NatVector inputArity ->
      NatVector outputArity
    | _, _, PRFunctionVector.nil, _inputs => NatVector.nil
    | _, _, PRFunctionVector.cons head tail, inputs =>
        NatVector.cons
          (PRFunction.runCore head inputs)
          (PRFunctionVector.runCore tail inputs)
end

/-- Positive execution is equality with the structural evaluator. -/
def PRFunction.Evaluates
    {arity : Nat}
    (program : PRFunction arity)
    (inputs : NatVector arity)
    (output : Nat) : Prop :=
  output = PRFunction.runCore program inputs

/-- Pointwise vector execution is equality with its structural evaluator. -/
def PRFunctionVector.Evaluates
    {inputArity outputArity : Nat}
    (programs : PRFunctionVector inputArity outputArity)
    (inputs : NatVector inputArity)
    (outputs : NatVector outputArity) : Prop :=
  outputs = PRFunctionVector.runCore programs inputs

namespace PRFunction.Evaluates

theorem zero {arity : Nat} (inputs : NatVector arity) :
    PRFunction.Evaluates (PRFunction.zero : PRFunction arity) inputs 0 := rfl

theorem successor (inputs : NatVector 1) :
    PRFunction.Evaluates PRFunction.successor inputs
      (Nat.succ (inputs.getD 0)) := rfl

theorem projection
    {arity : Nat}
    (index : Nat)
    (bounded : index < arity)
    (inputs : NatVector arity) :
    PRFunction.Evaluates
      (PRFunction.projection arity index bounded)
      inputs
      (inputs.get index bounded) := rfl

theorem composition
    {inputArity outputArity : Nat}
    {outer : PRFunction outputArity}
    {inner : PRFunctionVector inputArity outputArity}
    {inputs : NatVector inputArity}
    {intermediate : NatVector outputArity}
    {output : Nat}
    (innerEvaluation :
      PRFunctionVector.Evaluates inner inputs intermediate)
    (outerEvaluation :
      PRFunction.Evaluates outer intermediate output) :
    PRFunction.Evaluates
      (PRFunction.composition outer inner) inputs output := by
  unfold PRFunction.Evaluates at *
  exact outerEvaluation.trans
    (congrArg (PRFunction.runCore outer) innerEvaluation)

theorem runCore_primitive_cons
    {parameterArity : Nat}
    (base : PRFunction parameterArity)
    (step : PRFunction (Nat.succ (Nat.succ parameterArity)))
    (counter : Nat)
    (parameters : NatVector parameterArity) :
    PRFunction.runCore (PRFunction.primitiveRecursion base step)
        (NatVector.cons counter parameters) =
      Nat.rec
        (PRFunction.runCore base parameters)
        (fun index previous =>
          PRFunction.runCore step
            (NatVector.cons index (NatVector.cons previous parameters)))
        counter := by
  change Nat.rec (motive := fun _counter => Nat)
      (PRFunction.runCore base (NatVector.cons counter parameters).tailD)
      (fun index previous =>
        PRFunction.runCore step
          (NatVector.cons index
            (NatVector.cons previous
              (NatVector.cons counter parameters).tailD)))
      counter = _
  rw [NatVector.tailD_cons]

theorem runCore_primitive_zero
    {parameterArity : Nat}
    (base : PRFunction parameterArity)
    (step : PRFunction (Nat.succ (Nat.succ parameterArity)))
    (parameters : NatVector parameterArity) :
    PRFunction.runCore (PRFunction.primitiveRecursion base step)
        (NatVector.cons 0 parameters) =
      PRFunction.runCore base parameters :=
  runCore_primitive_cons base step 0 parameters

theorem runCore_primitive_succ
    {parameterArity : Nat}
    (base : PRFunction parameterArity)
    (step : PRFunction (Nat.succ (Nat.succ parameterArity)))
    (counter : Nat)
    (parameters : NatVector parameterArity) :
    PRFunction.runCore (PRFunction.primitiveRecursion base step)
        (NatVector.cons (Nat.succ counter) parameters) =
      PRFunction.runCore step
        (NatVector.cons counter
          (NatVector.cons
            (PRFunction.runCore (PRFunction.primitiveRecursion base step)
              (NatVector.cons counter parameters))
            parameters)) := by
  exact (runCore_primitive_cons base step (Nat.succ counter) parameters).trans
    (congrArg
      (fun previous =>
        PRFunction.runCore step
          (NatVector.cons counter (NatVector.cons previous parameters)))
      (runCore_primitive_cons base step counter parameters).symm)

theorem primitiveZero
    {parameterArity : Nat}
    {base : PRFunction parameterArity}
    {step : PRFunction (Nat.succ (Nat.succ parameterArity))}
    {parameters : NatVector parameterArity}
    {output : Nat}
    (baseEvaluation : PRFunction.Evaluates base parameters output) :
    PRFunction.Evaluates
      (PRFunction.primitiveRecursion base step)
      (NatVector.cons 0 parameters) output :=
  baseEvaluation.trans (runCore_primitive_zero base step parameters).symm

theorem primitiveSucc
    {parameterArity : Nat}
    {base : PRFunction parameterArity}
    {step : PRFunction (Nat.succ (Nat.succ parameterArity))}
    {counter previous output : Nat}
    {parameters : NatVector parameterArity}
    (previousEvaluation :
      PRFunction.Evaluates
        (PRFunction.primitiveRecursion base step)
        (NatVector.cons counter parameters) previous)
    (stepEvaluation :
      PRFunction.Evaluates step
        (NatVector.cons counter (NatVector.cons previous parameters)) output) :
    PRFunction.Evaluates
      (PRFunction.primitiveRecursion base step)
      (NatVector.cons (Nat.succ counter) parameters) output := by
  unfold PRFunction.Evaluates at *
  exact stepEvaluation.trans
    ((congrArg
      (fun value =>
        PRFunction.runCore step
          (NatVector.cons counter (NatVector.cons value parameters)))
      previousEvaluation).trans
      (runCore_primitive_succ base step counter parameters).symm)

end PRFunction.Evaluates

namespace PRFunctionVector.Evaluates

theorem nil {inputArity : Nat} (inputs : NatVector inputArity) :
    PRFunctionVector.Evaluates
      (PRFunctionVector.nil : PRFunctionVector inputArity 0)
      inputs NatVector.nil := rfl

theorem cons
    {inputArity length : Nat}
    {head : PRFunction inputArity}
    {tail : PRFunctionVector inputArity length}
    {inputs : NatVector inputArity}
    {headOutput : Nat}
    {tailOutput : NatVector length}
    (headEvaluation : PRFunction.Evaluates head inputs headOutput)
    (tailEvaluation :
      PRFunctionVector.Evaluates tail inputs tailOutput) :
    PRFunctionVector.Evaluates
      (PRFunctionVector.cons head tail)
      inputs
      (NatVector.cons headOutput tailOutput) :=
  (congrArg
    (fun headValue => NatVector.cons headValue tailOutput)
    headEvaluation).trans
    (congrArg
      (fun tailValues =>
        NatVector.cons (PRFunction.runCore head inputs) tailValues)
      tailEvaluation)

end PRFunctionVector.Evaluates

/-- The unary identity program. -/
def PRFunction.identity : PRFunction 1 :=
  PRFunction.projection 1 0 (Nat.zero_lt_succ 0)

/-- A closed positive execution witness for successor. -/
theorem PRFunction.successor_evaluates (value : Nat) :
    PRFunction.Evaluates
      PRFunction.successor
      (NatVector.cons value NatVector.nil)
      (Nat.succ value) :=
  PRFunction.Evaluates.successor (NatVector.cons value NatVector.nil)

/-- A closed positive execution witness for projections. -/
theorem PRFunction.projection_evaluates
    (arity index : Nat)
    (bounded : index < arity)
    (inputs : NatVector arity) :
    PRFunction.Evaluates
      (PRFunction.projection arity index bounded)
      inputs
      (inputs.get index bounded) :=
  PRFunction.Evaluates.projection index bounded inputs

end HeytingArithmetic
end RelationalPerimeter

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.HeytingArithmetic.NatVector
#print axioms RelationalPerimeter.HeytingArithmetic.PRFunction
#print axioms RelationalPerimeter.HeytingArithmetic.PRFunctionVector
#print axioms RelationalPerimeter.HeytingArithmetic.PRFunction.Evaluates
#print axioms RelationalPerimeter.HeytingArithmetic.PRFunctionVector.Evaluates
#print axioms RelationalPerimeter.HeytingArithmetic.NatVector.tailD_cons
#print axioms RelationalPerimeter.HeytingArithmetic.PRFunction.Evaluates.composition
#print axioms RelationalPerimeter.HeytingArithmetic.PRFunction.Evaluates.primitiveSucc
#print axioms RelationalPerimeter.HeytingArithmetic.PRFunction.successor_evaluates
#print axioms RelationalPerimeter.HeytingArithmetic.PRFunction.projection_evaluates
/- AXIOM_AUDIT_END -/
