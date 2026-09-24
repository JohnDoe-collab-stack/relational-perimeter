import RelationalPerimeter.Computation.ConstitutiveSearch.SAT.StructuralBranchContext

/-!
# Generated structural SAT branch contexts

This module restricts the hardened structural SAT contexts to those actually
generated from one root formula by successive fresh Boolean decisions.

Generation records only constitutive provenance.  Satisfaction remains the
separate acceptance predicate supplied by structuralBranchContextSystem.
-/

namespace ConstitutiveSearch
namespace SAT

/-- The selected variable is absent from a structural decision history. -/
def StructuralDecisionsAvoid
    (var : Var) : List StructuralBranchDecision → Prop
  | [] => True
  | decision :: rest =>
      decision.var ≠ var ∧
        StructuralDecisionsAvoid var rest

/-- Executable freshness check against structural decision provenance. -/
def structuralDecisionsAvoidCheck
    (var : Var) : List StructuralBranchDecision → Bool
  | [] => true
  | decision :: rest =>
      if decision.var = var then
        false
      else
        structuralDecisionsAvoidCheck var rest

/-- Successful executable freshness checking reconstructs the proof witness. -/
theorem structuralDecisionsAvoid_of_check_true
    (var : Var)
    (decisions : List StructuralBranchDecision)
    (check : structuralDecisionsAvoidCheck var decisions = true) :
    StructuralDecisionsAvoid var decisions := by
  induction decisions with
  | nil =>
      exact True.intro
  | cons decision rest inductionHypothesis =>
      by_cases same : decision.var = var
      · rw [structuralDecisionsAvoidCheck, if_pos same] at check
        cases check
      · constructor
        · exact same
        · apply inductionHypothesis
          rw [structuralDecisionsAvoidCheck, if_neg same] at check
          exact check

/--
Proof-relevant provenance from one root formula through fresh structural branch
decisions.
-/
inductive StructuralGeneratedFrom
    (rootFormula : Cnf) :
    StructuralBranchContext → Type where
  | root :
      StructuralGeneratedFrom
        rootFormula
        (structuralRootContext rootFormula)
  | child
      {parent : StructuralBranchContext}
      (parentGenerated :
        StructuralGeneratedFrom rootFormula parent)
      (var : Var)
      (value : Bool)
      (fresh :
        StructuralDecisionsAvoid var parent.decisions) :
      StructuralGeneratedFrom
        rootFormula
        (structuralChildContext parent var value)

namespace StructuralGeneratedFrom

/-- Number of constituted decisions in one generation witness. -/
def depth
    {rootFormula : Cnf}
    {context : StructuralBranchContext} :
    StructuralGeneratedFrom rootFormula context → Nat
  | .root => 0
  | .child parentGenerated _var _value _fresh =>
      depth parentGenerated + 1

end StructuralGeneratedFrom

/-- Uniform state type for structural contexts generated from one SAT root. -/
structure GeneratedStructuralBranchContext
    (rootFormula : Cnf) where
  context : StructuralBranchContext
  generated :
    StructuralGeneratedFrom rootFormula context

namespace GeneratedStructuralBranchContext

/-- Canonical generated root. -/
def root
    (formula : Cnf) :
    GeneratedStructuralBranchContext formula :=
  { context := structuralRootContext formula
    generated := .root }

/-- Generate one fresh structural child. -/
def child
    {rootFormula : Cnf}
    (parent : GeneratedStructuralBranchContext rootFormula)
    (var : Var)
    (value : Bool)
    (fresh :
      StructuralDecisionsAvoid
        var
        parent.context.decisions) :
    GeneratedStructuralBranchContext rootFormula :=
  { context :=
      structuralChildContext
        parent.context
        var
        value
    generated :=
      .child
        parent.generated
        var
        value
        fresh }

/-- Structural generation depth. -/
def depth
    {rootFormula : Cnf}
    (state : GeneratedStructuralBranchContext rootFormula) :
    Nat :=
  state.generated.depth

theorem root_depth
    (formula : Cnf) :
    (root formula).depth = 0 :=
  rfl

theorem child_depth
    {rootFormula : Cnf}
    (parent : GeneratedStructuralBranchContext rootFormula)
    (var : Var)
    (value : Bool)
    (fresh :
      StructuralDecisionsAvoid
        var
        parent.context.decisions) :
    (child parent var value fresh).depth =
      parent.depth + 1 :=
  rfl

theorem child_decisions
    {rootFormula : Cnf}
    (parent : GeneratedStructuralBranchContext rootFormula)
    (var : Var)
    (value : Bool)
    (fresh :
      StructuralDecisionsAvoid
        var
        parent.context.decisions) :
    (child parent var value fresh).context.decisions =
      { var := var, value := value } ::
        parent.context.decisions :=
  rfl

end GeneratedStructuralBranchContext

/-- Structural continuation family indexed by generated states. -/
abbrev GeneratedStructuralBranchContinuation
    {rootFormula : Cnf}
    (state : GeneratedStructuralBranchContext rootFormula) :
    Type :=
  StructuralBranchContinuation state.context

/-- Acceptance remains satisfaction of the generated state's residual formula. -/
def GeneratedStructuralBranchAccept
    {rootFormula : Cnf}
    (state : GeneratedStructuralBranchContext rootFormula)
    (continuation :
      GeneratedStructuralBranchContinuation state) :
    Prop :=
  StructuralBranchAccept state.context continuation

/-- Hardened search system on all generated states of one fixed root. -/
abbrev generatedStructuralBranchSystem
    (rootFormula : Cnf) :
    SearchSystem :=
  { State :=
      GeneratedStructuralBranchContext rootFormula
    Continuation :=
      GeneratedStructuralBranchContinuation
    Accept :=
      GeneratedStructuralBranchAccept }

/--
A fresh decision gives an exact acceptance-preserving split in the uniform
generated-state type.
-/
def generatedStructuralSplit
    {rootFormula : Cnf}
    (parent : GeneratedStructuralBranchContext rootFormula)
    (var : Var)
    (fresh :
      StructuralDecisionsAvoid
        var
        parent.context.decisions) :
    AcceptingExactBinarySplit
      (generatedStructuralBranchSystem rootFormula)
      parent
      (GeneratedStructuralBranchContext.child
        parent var false fresh)
      (GeneratedStructuralBranchContext.child
        parent var true fresh) :=
  let splitter :=
    structuralContextSplit parent.context var
  { split := splitter.split
    merge := splitter.merge
    splitMerge := splitter.splitMerge
    mergeSplit := splitter.mergeSplit
    splitPreservesAccept := by
      intro continuation accepted
      by_cases valueFalse : continuation.1 var = false
      · have residualAccepted :
            Satisfies continuation.1
              (branchResidual parent.context.formula var false) :=
          (branchWeakening
              parent.context.formula
              var
              false).preservesSatisfaction
            accepted
        simpa only [
          generatedStructuralBranchSystem,
          GeneratedStructuralBranchContinuation,
          GeneratedStructuralBranchAccept,
          GeneratedStructuralBranchContext.child,
          splitter,
          structuralContextSplit,
          splitStructuralContextContinuation,
          dif_pos valueFalse,
          BinaryAccept,
          StructuralBranchAccept,
          structuralChildContext
        ] using residualAccepted
      · have residualAccepted :
            Satisfies continuation.1
              (branchResidual parent.context.formula var true) :=
          (branchWeakening
              parent.context.formula
              var
              true).preservesSatisfaction
            accepted
        simpa only [
          generatedStructuralBranchSystem,
          GeneratedStructuralBranchContinuation,
          GeneratedStructuralBranchAccept,
          GeneratedStructuralBranchContext.child,
          splitter,
          structuralContextSplit,
          splitStructuralContextContinuation,
          dif_neg valueFalse,
          BinaryAccept,
          StructuralBranchAccept,
          structuralChildContext
        ] using residualAccepted
    mergePreservesAccept := by
      intro branch accepted
      cases branch with
      | inl leftContinuation =>
          change
            Satisfies leftContinuation.1
              (branchResidual
                parent.context.formula
                var
                false) at accepted
          change
            Satisfies leftContinuation.1
              parent.context.formula
          exact
            restoreSatisfaction
              parent.context.formula
              leftContinuation.1
              var
              false
              leftContinuation.2.1
              accepted
      | inr rightContinuation =>
          change
            Satisfies rightContinuation.1
              (branchResidual
                parent.context.formula
                var
                true) at accepted
          change
            Satisfies rightContinuation.1
              parent.context.formula
          exact
            restoreSatisfaction
              parent.context.formula
              rightContinuation.1
              var
              true
              rightContinuation.2.1
              accepted }

/-- Fresh generated expansion preserves frontier viability exactly. -/
def generatedStructuralExpansion
    {rootFormula : Cnf}
    (parent : GeneratedStructuralBranchContext rootFormula)
    (var : Var)
    (fresh :
      StructuralDecisionsAvoid
        var
        parent.context.decisions) :
    AcceptedFrontierPreservation
      (generatedStructuralBranchSystem rootFormula)
      [parent]
      [GeneratedStructuralBranchContext.child
          parent var false fresh,
        GeneratedStructuralBranchContext.child
          parent var true fresh] :=
  AcceptedFrontierPreservation.expandHead
    (generatedStructuralSplit parent var fresh)

end SAT
end ConstitutiveSearch

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.SAT.StructuralDecisionsAvoid
#print axioms ConstitutiveSearch.SAT.structuralDecisionsAvoidCheck
#print axioms ConstitutiveSearch.SAT.structuralDecisionsAvoid_of_check_true
#print axioms ConstitutiveSearch.SAT.StructuralGeneratedFrom
#print axioms ConstitutiveSearch.SAT.StructuralGeneratedFrom.depth
#print axioms ConstitutiveSearch.SAT.GeneratedStructuralBranchContext
#print axioms ConstitutiveSearch.SAT.GeneratedStructuralBranchContext.root
#print axioms ConstitutiveSearch.SAT.GeneratedStructuralBranchContext.child
#print axioms ConstitutiveSearch.SAT.GeneratedStructuralBranchContext.depth
#print axioms ConstitutiveSearch.SAT.GeneratedStructuralBranchContinuation
#print axioms ConstitutiveSearch.SAT.GeneratedStructuralBranchAccept
#print axioms ConstitutiveSearch.SAT.generatedStructuralBranchSystem
#print axioms ConstitutiveSearch.SAT.generatedStructuralSplit
#print axioms ConstitutiveSearch.SAT.generatedStructuralExpansion
/- AXIOM_AUDIT_END -/
