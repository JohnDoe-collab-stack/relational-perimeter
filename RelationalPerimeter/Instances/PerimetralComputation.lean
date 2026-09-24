import StrongPerimetralTurning
import RelationalPerimeter.Instances.GrowingFeedback

/-!
# Operational decomposition over a perimetral history

The adapter keeps unary constitutive generation distinct from binary
operational opening. An operational realization is indexed by the exact
endpoint of its rooted history and carries the closure obstruction inherited at
that endpoint. Its executed reconstruction produces the decision and seed used
to build the next operational state.
-/

namespace RelationalPerimeter.Instances.PerimetralComputation

open RelationalPerimeter.Computation
open RelationalPerimeter.Instances.GrowingReconstruction
open RelationalPerimeter.Instances.GrowingFeedback
open StrongPerimetralTurning

/--
Operational data realized at one exact constituted history. Endpoint identity
and inherited closure provenance remain proof-relevant fields.
-/
structure EndpointOperationalRealization
    (P : CircularPresentation)
    (history : RootedGeneratedHistory P) where
  realizedEndpoint : PositiveConstitution P
  endpointExact : realizedEndpoint = history.endpoint
  inheritedClosureObstruction : PositiveClosureObstruction P
  obstructionExact :
    inheritedClosureObstruction = history.terminalClosureObstruction
  opening : ExactStructuralOpening growingSearchSystem .parent .left .right
  openingExact : opening = growingOpening
  operational : GrowingFeedbackState
  outputIsDerivedLength : operational.output = history.history.length
  seedIsDerivedLength : operational.nextSeed = history.history.length

/-- A constituted history together with its endpoint-indexed realization. -/
structure PerimetralComputationalState (P : CircularPresentation) where
  constituted : RootedGeneratedHistory P
  realization : EndpointOperationalRealization P constituted

namespace PerimetralComputationalState

/-- Operational state carried by the endpoint-indexed realization. -/
def operational
    {P : CircularPresentation}
    (state : PerimetralComputationalState P) : GrowingFeedbackState :=
  state.realization.operational

/-- The numerical output remains a derived reading of the constituted history. -/
theorem outputIsDerivedLength
    {P : CircularPresentation}
    (state : PerimetralComputationalState P) :
    state.operational.output = state.constituted.history.length :=
  state.realization.outputIsDerivedLength

/-- The reconstruction seed is aligned with the same constituted history. -/
theorem seedIsDerivedLength
    {P : CircularPresentation}
    (state : PerimetralComputationalState P) :
    state.operational.nextSeed = state.constituted.history.length :=
  state.realization.seedIsDerivedLength

/-- The operational opening is the concrete exact growing opening. -/
theorem openingExact
    {P : CircularPresentation}
    (state : PerimetralComputationalState P) :
    state.realization.opening = growingOpening :=
  state.realization.openingExact

/-- The realization is indexed by exactly the endpoint of its history. -/
theorem endpoint_realized_exactly
    {P : CircularPresentation}
    (state : PerimetralComputationalState P) :
    state.realization.realizedEndpoint = state.constituted.endpoint :=
  state.realization.endpointExact

/-- The realization carries the obstruction inherited at that same endpoint. -/
theorem obstruction_realized_exactly
    {P : CircularPresentation}
    (state : PerimetralComputationalState P) :
    state.realization.inheritedClosureObstruction =
      state.constituted.terminalClosureObstruction :=
  state.realization.obstructionExact

end PerimetralComputationalState

/-- Initial operational realization of any already constituted history. -/
def realizeHistory
    {P : CircularPresentation}
    (history : RootedGeneratedHistory P) :
    PerimetralComputationalState P :=
  { constituted := history
    realization :=
      { realizedEndpoint := history.endpoint
        endpointExact := rfl
        inheritedClosureObstruction := history.terminalClosureObstruction
        obstructionExact := rfl
        opening := growingOpening
        openingExact := rfl
        operational := feedbackInitialState history.history.length
        outputIsDerivedLength := rfl
        seedIsDerivedLength := rfl } }

/-- The canonical perimeter is the distinguished initial realization. -/
def perimeterComputationalState (P : CircularPresentation) :
    PerimetralComputationalState P :=
  realizeHistory (perimeterDeployment P)

/-- Unary constitutive continuation from the realized endpoint. -/
def advanceConstitution
    {P : CircularPresentation}
    (state : PerimetralComputationalState P) :
    RootedGeneratedHistory P :=
  appendGenerated state.constituted (generate state.constituted.endpoint)

/-- The constitutive advance contains exactly one positive generated suffix. -/
def advanceConstitutionStrict
    {P : CircularPresentation}
    (state : PerimetralComputationalState P) :
    StrictConstitutivePrefix state.constituted (advanceConstitution state) :=
  { continuation :=
      { predecessor := state.constituted.endpoint
        priorHistory := .root
        lastStep := (generate state.constituted.endpoint).2 }
    historyExact := rfl }

/-- The constitutive continuation cannot collapse back to its source history. -/
theorem advanceConstitution_ne
    {P : CircularPresentation}
    (state : PerimetralComputationalState P) :
    advanceConstitution state ≠ state.constituted :=
  fun equality => strictPrefix_ne (advanceConstitutionStrict state) equality

/-- Binary opening read from the endpoint-indexed realization. -/
def operationalOpening
    {P : CircularPresentation}
    (state : PerimetralComputationalState P) :
    ExactStructuralOpening growingSearchSystem .parent .left .right :=
  state.realization.opening

/--
An executed reconstruction indexed by the perimetral endpoint at which its
operational state is realized.
-/
structure EndpointIndexedReconstruction
    (P : CircularPresentation)
    (endpoint : PositiveConstitution P)
    (operational : GrowingFeedbackState) where
  inheritedClosureObstruction : PositiveClosureObstruction P
  obstructionExact :
    inheritedClosureObstruction = endpoint.2.1.1.inheritedClosureObstruction
  run : ReconstructionRun
    (growingReconstructionFrom (reconstructionIndex operational)
      (extractedCandidatesFromState operational))

/-- Reconstruction executed at the exact endpoint of the constituted history. -/
def perimetralReconstruction
    {P : CircularPresentation}
    (state : PerimetralComputationalState P) :
    EndpointIndexedReconstruction P state.constituted.endpoint state.operational :=
  { inheritedClosureObstruction :=
      state.realization.inheritedClosureObstruction
    obstructionExact := state.realization.obstructionExact
    run := reconstructionFromState state.operational }

/-- The reconstruction carries the obstruction of its exact endpoint. -/
theorem perimetralReconstruction_obstruction_exact
    {P : CircularPresentation}
    (state : PerimetralComputationalState P) :
    (perimetralReconstruction state).inheritedClosureObstruction =
      state.constituted.endpoint.2.1.1.inheritedClosureObstruction :=
  (perimetralReconstruction state).obstructionExact

/-- Every endpoint-indexed run reconstructs the relation at its constituted stage. -/
theorem perimetralReconstruction_relation_exact
    {P : CircularPresentation}
    (state : PerimetralComputationalState P) :
    (perimetralReconstruction state).run.relation? =
      some (GrowingRelation.absorb state.constituted.history.length) := by
  change
    (reconstructionFromState state.operational).relation? =
      some (GrowingRelation.absorb state.constituted.history.length)
  rw [reconstructionFromState_relation_exact]
  change
    some (GrowingRelation.absorb state.operational.nextSeed) =
      some (GrowingRelation.absorb state.constituted.history.length)
  rw [state.seedIsDerivedLength]

/-- A freshly realized history reconstructs its stage-indexed relation. -/
theorem realizedHistory_relation_is_reconstructed
    {P : CircularPresentation}
    (history : RootedGeneratedHistory P) :
    (perimetralReconstruction (realizeHistory history)).run.relation? =
      some (.absorb history.history.length) :=
  by
    change
      (reconstructionFromState
        (feedbackInitialState history.history.length)).relation? =
          some (.absorb history.history.length)
    exact feedbackInitial_relation_exact history.history.length

/-- Reduction is computed only from the relation returned at this endpoint. -/
def reconstructedReduction
    {P : CircularPresentation}
    (state : PerimetralComputationalState P) :
    Option (Nat ⊕ Nat → Nat) :=
  (perimetralReconstruction state).run.relation?.map
    (fun relation =>
      OperationalReduction.absorbLeft
        growingAction (operationalOpening state) relation)

/-- A fresh realization exposes the reduction produced by its exact run. -/
theorem realizedHistory_reconstructedReduction_exact
    {P : CircularPresentation}
    (history : RootedGeneratedHistory P) :
    reconstructedReduction (realizeHistory history) =
      some (stageReduction history.history.length) := by
  change
    (reconstructionFromState
      (feedbackInitialState history.history.length)).relation?.map
        (fun relation =>
          OperationalReduction.absorbLeft growingAction growingOpening relation) =
      some (stageReduction history.history.length)
  have relationExact := realizedHistory_relation_is_reconstructed history
  change
    (reconstructionFromState
      (feedbackInitialState history.history.length)).relation? =
        some (.absorb history.history.length) at relationExact
  exact congrArg
    (Option.map (fun relation =>
      OperationalReduction.absorbLeft growingAction growingOpening relation))
    relationExact

/-- The reduction of any aligned state is obtained from its exact indexed run. -/
theorem perimetralReconstructedReduction_exact
    {P : CircularPresentation}
    (state : PerimetralComputationalState P) :
    reconstructedReduction state =
      some (stageReduction state.constituted.history.length) := by
  unfold reconstructedReduction stageReduction
  rw [perimetralReconstruction_relation_exact]
  change
    some
      (OperationalReduction.absorbLeft growingAction
        state.realization.opening
        (GrowingRelation.absorb state.constituted.history.length)) =
      some
        (OperationalReduction.absorbLeft growingAction growingOpening
          (GrowingRelation.absorb state.constituted.history.length))
  rw [state.openingExact]

/--
The next operational state is produced from the endpoint-indexed run. Its
relation output determines the new decision and seed.
-/
def advanceOperational
    {P : CircularPresentation}
    (state : PerimetralComputationalState P) : GrowingFeedbackState :=
  produceNextState state.operational (perimetralReconstruction state).run

/-- The endpoint-indexed run is exactly the run consumed by state production. -/
theorem advanceOperational_has_exact_origin
    {P : CircularPresentation}
    (state : PerimetralComputationalState P) :
    ProducedFrom
      (growingStateProducer state.operational)
      (perimetralReconstruction state).run
      (advanceOperational state) :=
  OperationalStateProducer.produce_exact
    (growingStateProducer state.operational)
    (perimetralReconstruction state).run

/--
One aligned step: unary constitution and relation-produced operational feedback
remain distinct, then meet in a new endpoint-indexed realization.
-/
def advance
    {P : CircularPresentation}
    (state : PerimetralComputationalState P) :
    PerimetralComputationalState P :=
  let nextHistory := advanceConstitution state
  { constituted := nextHistory
    realization :=
      { realizedEndpoint := nextHistory.endpoint
        endpointExact := rfl
        inheritedClosureObstruction := nextHistory.terminalClosureObstruction
        obstructionExact := rfl
        opening := growingOpening
        openingExact := rfl
        operational := advanceOperational state
        outputIsDerivedLength := by
          change
            state.operational.output + 1 =
              state.constituted.history.length + 1
          exact congrArg (fun value => value + 1)
            state.outputIsDerivedLength
        seedIsDerivedLength := by
          change
            (advanceOperational state).nextSeed =
              state.constituted.history.length + 1
          change
            (growingFeedbackStep.next state.operational).nextSeed =
              state.constituted.history.length + 1
          rw [nextState_seed_succ]
          exact congrArg (fun value => value + 1)
            state.seedIsDerivedLength } }

/-- The next constituted history is exactly the unary generated continuation. -/
theorem advance_constitution_exact
    {P : CircularPresentation}
    (state : PerimetralComputationalState P) :
    (advance state).constituted = advanceConstitution state :=
  rfl

/-- The next realization is indexed by the newly generated endpoint. -/
theorem advance_endpoint_realized_exactly
    {P : CircularPresentation}
    (state : PerimetralComputationalState P) :
    (advance state).realization.realizedEndpoint =
      (advanceConstitution state).endpoint :=
  rfl

/-- Advancement keeps the next reconstruction seed aligned with the new history. -/
theorem advance_seed_is_derived_length
    {P : CircularPresentation}
    (state : PerimetralComputationalState P) :
    (advance state).operational.nextSeed =
      (advance state).constituted.history.length :=
  (advance state).seedIsDerivedLength

/-- The next operational state comes from the preceding endpoint-indexed run. -/
theorem advance_operational_exact
    {P : CircularPresentation}
    (state : PerimetralComputationalState P) :
    (advance state).operational = advanceOperational state :=
  rfl

/-- The next reconstruction consumes the exact operational state just produced. -/
theorem reconstruction_after_advance_consumes_producedState
    {P : CircularPresentation}
    (state : PerimetralComputationalState P) :
    (perimetralReconstruction (advance state)).run =
      reconstructionFromState (advanceOperational state) :=
  rfl

/-- At the canonical boundary, unary advancement is the existing free step. -/
theorem perimeter_advance_is_oneStepAfterPerimeter
    (P : CircularPresentation) :
    advanceConstitution (perimeterComputationalState P) =
      oneStepAfterPerimeter P :=
  by
    unfold advanceConstitution perimeterComputationalState realizeHistory
    rfl

end RelationalPerimeter.Instances.PerimetralComputation

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Instances.PerimetralComputation.EndpointOperationalRealization
#print axioms RelationalPerimeter.Instances.PerimetralComputation.PerimetralComputationalState
#print axioms RelationalPerimeter.Instances.PerimetralComputation.PerimetralComputationalState.operational
#print axioms RelationalPerimeter.Instances.PerimetralComputation.PerimetralComputationalState.outputIsDerivedLength
#print axioms RelationalPerimeter.Instances.PerimetralComputation.PerimetralComputationalState.seedIsDerivedLength
#print axioms RelationalPerimeter.Instances.PerimetralComputation.PerimetralComputationalState.openingExact
#print axioms RelationalPerimeter.Instances.PerimetralComputation.PerimetralComputationalState.endpoint_realized_exactly
#print axioms RelationalPerimeter.Instances.PerimetralComputation.PerimetralComputationalState.obstruction_realized_exactly
#print axioms RelationalPerimeter.Instances.PerimetralComputation.realizeHistory
#print axioms RelationalPerimeter.Instances.PerimetralComputation.perimeterComputationalState
#print axioms RelationalPerimeter.Instances.PerimetralComputation.advanceConstitution
#print axioms RelationalPerimeter.Instances.PerimetralComputation.advanceConstitutionStrict
#print axioms RelationalPerimeter.Instances.PerimetralComputation.advanceConstitution_ne
#print axioms RelationalPerimeter.Instances.PerimetralComputation.operationalOpening
#print axioms RelationalPerimeter.Instances.PerimetralComputation.EndpointIndexedReconstruction
#print axioms RelationalPerimeter.Instances.PerimetralComputation.perimetralReconstruction
#print axioms RelationalPerimeter.Instances.PerimetralComputation.perimetralReconstruction_obstruction_exact
#print axioms RelationalPerimeter.Instances.PerimetralComputation.perimetralReconstruction_relation_exact
#print axioms RelationalPerimeter.Instances.PerimetralComputation.realizedHistory_relation_is_reconstructed
#print axioms RelationalPerimeter.Instances.PerimetralComputation.reconstructedReduction
#print axioms RelationalPerimeter.Instances.PerimetralComputation.realizedHistory_reconstructedReduction_exact
#print axioms RelationalPerimeter.Instances.PerimetralComputation.perimetralReconstructedReduction_exact
#print axioms RelationalPerimeter.Instances.PerimetralComputation.advanceOperational
#print axioms RelationalPerimeter.Instances.PerimetralComputation.advanceOperational_has_exact_origin
#print axioms RelationalPerimeter.Instances.PerimetralComputation.advance
#print axioms RelationalPerimeter.Instances.PerimetralComputation.advance_constitution_exact
#print axioms RelationalPerimeter.Instances.PerimetralComputation.advance_endpoint_realized_exactly
#print axioms RelationalPerimeter.Instances.PerimetralComputation.advance_seed_is_derived_length
#print axioms RelationalPerimeter.Instances.PerimetralComputation.advance_operational_exact
#print axioms RelationalPerimeter.Instances.PerimetralComputation.reconstruction_after_advance_consumes_producedState
#print axioms RelationalPerimeter.Instances.PerimetralComputation.perimeter_advance_is_oneStepAfterPerimeter
/- AXIOM_AUDIT_END -/
