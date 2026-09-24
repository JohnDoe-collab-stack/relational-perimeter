import RelationalPerimeter.Instances.EndogenousOperationalDecomposition
import RelationalPerimeter.Instances.FourNodeExample

/-!
# Regression checks for the perimetral computation adapter

The four-node example makes the separation visible: the constituted perimeter
has derived length three, its continuation is one unary generated step, and
the binary opening belongs only to the operational realization.
-/

namespace RelationalPerimeter.Tests.PerimetralComputationRegression

open StrongPerimetralTurning
open RelationalPerimeter.Instances.GrowingReconstruction
open RelationalPerimeter.Instances.PerimetralComputation

/-- Canonical computational state of the existing four-node presentation. -/
def exampleState :=
  perimeterComputationalState Example.examplePresentation

/-- The numerical stage is read from the already constituted perimeter. -/
theorem example_output_is_derived_length :
    exampleState.operational.output = 3 :=
  rfl

/-- Constitutive advancement is exactly the existing one-step continuation. -/
theorem example_advance_is_existing_continuation :
    advanceConstitution exampleState =
      oneStepAfterPerimeter Example.examplePresentation :=
  perimeter_advance_is_oneStepAfterPerimeter Example.examplePresentation

/-- The one-step continuation positively carries a strict constitutive suffix. -/
def example_advance_is_strict :
    StrictConstitutivePrefix
      exampleState.constituted
      (advanceConstitution exampleState) :=
  advanceConstitutionStrict exampleState

/-- Binary multiplicity appears only when the realization is opened. -/
theorem example_opening_left_exact :
    (operationalOpening exampleState).split (.inl 7) = .inl 7 :=
  rfl

/-- The executed reconstruction produces the stage-three relation. -/
theorem example_relation_is_run_output :
    (perimetralReconstruction exampleState).run.relation? =
      some (.absorb 3) :=
  realizedHistory_relation_is_reconstructed
    (perimeterDeployment Example.examplePresentation)

/-- The relation output is converted into an executable reduction. -/
theorem example_reduction_exact :
    reconstructedReduction exampleState = some (stageReduction 3) :=
  realizedHistory_reconstructedReduction_exact
    (perimeterDeployment Example.examplePresentation)

/-- The aligned advance preserves the derived-length equation. -/
theorem example_advanced_output_is_derived_length :
    (advance exampleState).operational.output =
      (advance exampleState).constituted.history.length :=
  (advance exampleState).outputIsDerivedLength

/-- The relation-produced seed stays aligned with the generated history. -/
theorem example_advanced_seed_is_derived_length :
    (advance exampleState).operational.nextSeed =
      (advance exampleState).constituted.history.length :=
  advance_seed_is_derived_length exampleState

/-- The next endpoint-indexed run reconstructs the relation at stage four. -/
theorem example_advanced_relation_is_run_output :
    (perimetralReconstruction (advance exampleState)).run.relation? =
      some (.absorb 4) :=
  perimetralReconstruction_relation_exact (advance exampleState)

/-- The next reconstruction consumes the relation-produced filtering decision. -/
theorem example_next_reconstruction_attempts :
    (perimetralReconstruction (advance exampleState)).run.attempts = 5 :=
  rfl

/-- The operational realization is indexed by the exact perimetral endpoint. -/
theorem example_endpoint_is_realized_exactly :
    exampleState.realization.realizedEndpoint =
      exampleState.constituted.endpoint :=
  exampleState.endpoint_realized_exactly

/-- The same realization carries the endpoint's inherited obstruction. -/
theorem example_obstruction_is_realized_exactly :
    exampleState.realization.inheritedClosureObstruction =
      exampleState.constituted.terminalClosureObstruction :=
  exampleState.obstruction_realized_exactly

/-- The executed reconstruction itself retains that exact endpoint obstruction. -/
theorem example_reconstruction_obstruction_is_endpoint_exact :
    (perimetralReconstruction exampleState).inheritedClosureObstruction =
      exampleState.constituted.endpoint.2.1.1.inheritedClosureObstruction :=
  perimetralReconstruction_obstruction_exact exampleState

end RelationalPerimeter.Tests.PerimetralComputationRegression

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Tests.PerimetralComputationRegression.exampleState
#print axioms RelationalPerimeter.Tests.PerimetralComputationRegression.example_output_is_derived_length
#print axioms RelationalPerimeter.Tests.PerimetralComputationRegression.example_advance_is_existing_continuation
#print axioms RelationalPerimeter.Tests.PerimetralComputationRegression.example_advance_is_strict
#print axioms RelationalPerimeter.Tests.PerimetralComputationRegression.example_opening_left_exact
#print axioms RelationalPerimeter.Tests.PerimetralComputationRegression.example_relation_is_run_output
#print axioms RelationalPerimeter.Tests.PerimetralComputationRegression.example_reduction_exact
#print axioms RelationalPerimeter.Tests.PerimetralComputationRegression.example_advanced_output_is_derived_length
#print axioms RelationalPerimeter.Tests.PerimetralComputationRegression.example_advanced_seed_is_derived_length
#print axioms RelationalPerimeter.Tests.PerimetralComputationRegression.example_advanced_relation_is_run_output
#print axioms RelationalPerimeter.Tests.PerimetralComputationRegression.example_next_reconstruction_attempts
#print axioms RelationalPerimeter.Tests.PerimetralComputationRegression.example_endpoint_is_realized_exactly
#print axioms RelationalPerimeter.Tests.PerimetralComputationRegression.example_obstruction_is_realized_exactly
#print axioms RelationalPerimeter.Tests.PerimetralComputationRegression.example_reconstruction_obstruction_is_endpoint_exact
/- AXIOM_AUDIT_END -/
