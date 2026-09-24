import RelationalPerimeter.Computation.ExecutedReconstruction

/-!
# Regression for executed reconstruction

The first two candidates fail, the third produces the relation, and the fourth
remains untested.  All readouts reduce from the same executable recursion.
-/

namespace RelationalPerimeter.Tests.ExecutedReconstructionRegression

open RelationalPerimeter.Computation

def regressionSystem : SearchSystem where
  State := Unit
  Continuation := fun _state => Nat
  Criterion := fun _state continuation => continuation = continuation

def RegressionRelation
    (_source _target : regressionSystem.State) : Type :=
  Unit

def regressionAttempt
    (candidate : Nat) : Option (RegressionRelation () ()) :=
  match candidate with
  | 2 => some ()
  | _ => none

def regressionReconstruction :
    ReconstructionSystem regressionSystem Nat RegressionRelation () () where
  extract := [0, 1, 2, 3]
  attempt := regressionAttempt

def regressionRun := regressionReconstruction.run

theorem regressionRun_tested_exact :
    regressionRun.testedCandidates = [0, 1, 2] :=
  rfl

theorem regressionRun_attempts_exact :
    regressionRun.attempts = 3 :=
  rfl

theorem regressionRun_selected_exact :
    regressionRun.selectedCandidate? = some 2 :=
  rfl

theorem regressionRun_relation_exact :
    regressionRun.relation? = some () :=
  rfl

end RelationalPerimeter.Tests.ExecutedReconstructionRegression

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Tests.ExecutedReconstructionRegression.regressionSystem
#print axioms RelationalPerimeter.Tests.ExecutedReconstructionRegression.regressionReconstruction
#print axioms RelationalPerimeter.Tests.ExecutedReconstructionRegression.regressionRun
#print axioms RelationalPerimeter.Tests.ExecutedReconstructionRegression.regressionRun_tested_exact
#print axioms RelationalPerimeter.Tests.ExecutedReconstructionRegression.regressionRun_attempts_exact
#print axioms RelationalPerimeter.Tests.ExecutedReconstructionRegression.regressionRun_selected_exact
#print axioms RelationalPerimeter.Tests.ExecutedReconstructionRegression.regressionRun_relation_exact
/- AXIOM_AUDIT_END -/
