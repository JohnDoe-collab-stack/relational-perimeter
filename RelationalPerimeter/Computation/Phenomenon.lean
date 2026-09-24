import RelationalPerimeter.Computation.ExecutedReconstruction
import RelationalPerimeter.Computation.OperationalReduction

/-!
# Endogenous operational decomposition

This package gathers the exact evidence needed to conclude that a structural
opening does not by itself determine the operational decomposition.  A failed
candidate is recorded by the executed run, a later relation is produced by
that same run, the relation acts on arbitrary continuations, and preservation
of the criterion is supplied as a separate proof.
-/

namespace RelationalPerimeter.Computation

universe uCandidate uRelation

/-- Proof-relevant witness of an operational decomposition produced by search. -/
structure EndogenousOperationalDecomposition
    (system : SearchSystem)
    (Candidate : Type uCandidate)
    (Relation : system.State → system.State → Type uRelation)
    (parent left right : system.State) where
  opening : ExactStructuralOpening system parent left right
  criterionOpening : CriterionExactOpening system opening
  reconstruction : ReconstructionSystem system Candidate Relation left right
  run : ReconstructionRun reconstruction
  success : SuccessfulRun run
  failedCandidate : Candidate
  failedCandidateExact : reconstruction.attempt failedCandidate = none
  failedCandidateWasTested :
    ∃ remaining : List Candidate,
      run.testedCandidates = failedCandidate :: remaining
  action : RelationalContinuationAction system Relation
  actionPreserves : CriterionPreservingAction system Relation action
  alternativesDistinct : left ≠ right
  absorbedContinuation : system.Continuation left
  absorbedContinuationAccepted :
    system.Criterion left absorbedContinuation

namespace EndogenousOperationalDecomposition

/--
The only relation exposed by the package is projected from the witnessed
`found` constructor of its executed run.
-/
def producedRelation
    {system : SearchSystem}
    {Candidate : Type uCandidate}
    {Relation : system.State → system.State → Type uRelation}
    {parent left right : system.State}
    (witness : EndogenousOperationalDecomposition
      system Candidate Relation parent left right) :
    Relation left right :=
  witness.success.relation

/-- The relation exposed by the package is explicitly the output of its run. -/
theorem relation_comes_from_executed_run
    {system : SearchSystem}
    {Candidate : Type uCandidate}
    {Relation : system.State → system.State → Type uRelation}
    {parent left right : system.State}
    (witness : EndogenousOperationalDecomposition
      system Candidate Relation parent left right) :
    witness.run.relation? = some witness.producedRelation :=
  witness.success.relation_exact

/-- The absorbed alternative remains positively viable for the criterion. -/
theorem absorbedAlternative_viable
    {system : SearchSystem}
    {Candidate : Type uCandidate}
    {Relation : system.State → system.State → Type uRelation}
    {parent left right : system.State}
    (witness : EndogenousOperationalDecomposition
      system Candidate Relation parent left right) :
    system.Viable left :=
  ⟨witness.absorbedContinuation, witness.absorbedContinuationAccepted⟩

/-- Reduction computed from the relation produced by the executed run. -/
def reduction
    {system : SearchSystem}
    {Candidate : Type uCandidate}
    {Relation : system.State → system.State → Type uRelation}
    {parent left right : system.State}
    (witness : EndogenousOperationalDecomposition
      system Candidate Relation parent left right) :
    system.Continuation parent → system.Continuation right :=
  OperationalReduction.absorbLeft
    witness.action witness.opening witness.producedRelation

/-- Preservation remains a theorem distinct from the reduction function. -/
theorem reduction_preserves
    {system : SearchSystem}
    {Candidate : Type uCandidate}
    {Relation : system.State → system.State → Type uRelation}
    {parent left right : system.State}
    (witness : EndogenousOperationalDecomposition
      system Candidate Relation parent left right)
    (continuation : system.Continuation parent)
    (accepted : system.Criterion parent continuation) :
    system.Criterion right (witness.reduction continuation) :=
  OperationalReduction.absorbLeft_preserves
    witness.actionPreserves witness.criterionOpening
    witness.producedRelation continuation accepted

/--
For the specified criterion, carrying the parent multiplicity and carrying only
the retained right alternative have the same viability status.  This licenses
the operational absorption without identifying the alternatives or declaring
the absorbed carrier empty.
-/
theorem viable_iff_after_reduction
    {system : SearchSystem}
    {Candidate : Type uCandidate}
    {Relation : system.State → system.State → Type uRelation}
    {parent left right : system.State}
    (witness : EndogenousOperationalDecomposition
      system Candidate Relation parent left right) :
    system.Viable parent ↔ system.Viable right :=
  OperationalReduction.viable_iff_after_absorbLeft
    witness.actionPreserves witness.criterionOpening witness.producedRelation

end EndogenousOperationalDecomposition
end RelationalPerimeter.Computation

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Computation.EndogenousOperationalDecomposition
#print axioms RelationalPerimeter.Computation.EndogenousOperationalDecomposition.producedRelation
#print axioms RelationalPerimeter.Computation.EndogenousOperationalDecomposition.relation_comes_from_executed_run
#print axioms RelationalPerimeter.Computation.EndogenousOperationalDecomposition.absorbedAlternative_viable
#print axioms RelationalPerimeter.Computation.EndogenousOperationalDecomposition.reduction
#print axioms RelationalPerimeter.Computation.EndogenousOperationalDecomposition.reduction_preserves
#print axioms RelationalPerimeter.Computation.EndogenousOperationalDecomposition.viable_iff_after_reduction
/- AXIOM_AUDIT_END -/
