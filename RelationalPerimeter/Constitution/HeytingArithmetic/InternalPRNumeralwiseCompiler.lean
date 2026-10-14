import RelationalPerimeter.Constitution.HeytingArithmetic.InternalPrimitiveRecursionRepresentation

/-!
# Complete positive numeralwise compiler for primitive-recursive programs
-/

namespace RelationalPerimeter
namespace HeytingArithmetic

mutual
  def PRFunction.internalNumeralwiseCompiler :
      {arity : Nat} ->
      (program : PRFunction arity) ->
      InternallyNumeralwiseRepresentedPRFunction program
    | _, PRFunction.zero => internallyNumeralwiseRepresentedZero
    | _, PRFunction.successor => internallyNumeralwiseRepresentedSuccessor
    | _, PRFunction.projection arity index bounded =>
        internallyNumeralwiseRepresentedProjection arity index bounded
    | _, PRFunction.composition outer inner =>
        internallyNumeralwiseRepresentedComposition
          outer.internalNumeralwiseCompiler
          inner.internalNumeralwiseCompiler
    | _, PRFunction.primitiveRecursion base step =>
        internallyNumeralwiseRepresentedPrimitiveRecursion
          base.internalNumeralwiseCompiler step.internalNumeralwiseCompiler

  def PRFunctionVector.internalNumeralwiseCompiler :
      {inputArity outputArity : Nat} ->
      (programs : PRFunctionVector inputArity outputArity) ->
      InternallyNumeralwiseRepresentedPRFunctionVector programs
    | _, _, PRFunctionVector.nil =>
        InternallyNumeralwiseRepresentedPRFunctionVector.nil
    | _, _, PRFunctionVector.cons head tail =>
        InternallyNumeralwiseRepresentedPRFunctionVector.cons
          head.internalNumeralwiseCompiler tail.internalNumeralwiseCompiler
end

def PRFunction.internalGraphNumeralProof
    {arity : Nat}
    (program : PRFunction arity)
    (inputs : NatVector arity)
    (output : Nat)
    (evaluation : PRFunction.Evaluates program inputs output) :
    Derivation LogicMode.intuitionistic haTheory FormulaContext.nil
      (program.numeralGraphInstance inputs output) := by
  have outputExact : output = program.run inputs := evaluation
  subst output
  exact program.internalNumeralwiseCompiler.numeralProof inputs

end HeytingArithmetic
end RelationalPerimeter

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.HeytingArithmetic.PRFunction.internalNumeralwiseCompiler
#print axioms RelationalPerimeter.HeytingArithmetic.PRFunction.internalGraphNumeralProof
/- AXIOM_AUDIT_END -/
