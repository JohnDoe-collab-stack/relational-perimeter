import RelationalPerimeter.Constitution.PositiveGenerationBridge

/-!
# Separating positive formation, closure and successor choice

The directed history deploys positively but has no closing witness. The other
models close a generated chain, allow two successors, and repeat a raw node
without identifying the occurrences of their finite histories.
-/

namespace RelationalPerimeter.Constitution.PositiveGenerationExamples

open StrongPerimetralTurning

def directedCompatible (source target : Bool) : Type :=
  Bool.rec (motive := fun _ => Type) Unit
    (Bool.rec (motive := fun _ => Type) Empty Unit target) source

def directedNode (state : Bool) : LocalNode Bool Bool directedCompatible Unit (fun _ => Unit) :=
  { explicit := state
    implicit := state
    difference := ()
    provenance := ()
    internallyCompatible := by cases state <;> exact () }

inductive DirectedStep : Bool → Bool → Type
  | forward : DirectedStep false true

def directedFormation : PositiveFormation :=
  { Explicit := Bool
    Implicit := Bool
    Compatible := directedCompatible
    Difference := Unit
    Provenance := fun _ => Unit
    State := Bool
    node := directedNode
    Step := DirectedStep
    compatibility := fun step => by cases step; exact () }

def directedHistory : PositiveHistory directedFormation false true :=
  .cons .forward .nil

def directedPositive : PositiveHistory.Occurrence directedHistory := .here

theorem directed_closing_empty : ClosingWitness directedHistory.boundaryShape → False :=
  fun junction => nomatch junction

theorem directed_no_pointing :
    Nonempty (PointedClosingBoundary directedHistory.boundaryShape) → False :=
  directedHistory.boundaryShape.noPointingOfEmpty directed_closing_empty

theorem directed_no_global_continuation
    (choice : ChosenPositiveContinuation directedFormation) : False := by
  have step := choice.step true
  cases step

def unitNode : LocalNode Unit Unit (fun _ _ => Bool) Unit (fun _ => Unit) :=
  { explicit := ()
    implicit := ()
    difference := ()
    provenance := ()
    internallyCompatible := true }

def unitFormation : PositiveFormation :=
  { Explicit := Unit
    Implicit := Unit
    Compatible := fun _ _ => Bool
    Difference := Unit
    Provenance := fun _ => Unit
    State := Unit
    node := fun _ => unitNode
    Step := fun _ _ => Bool
    compatibility := fun step => step }

def unitHistory : PositiveHistory unitFormation () () := .cons true .nil

def unitPositive : PositiveHistory.Occurrence unitHistory := .here

def unitCircular : PositiveCircularPresentation := unitHistory.toCircular unitPositive false

theorem unit_step_witness : (unitHistory.linkAt unitPositive).compatibility = true := rfl

theorem unit_closing_witness : unitCircular.finalJunction = false := rfl

def unitEndpoints : EndpointBoundary unitCircular :=
  { Endpoint := Bool
    leftEndpoint := false
    rightEndpoint := true
    leftPole := fun _ => false
    rightPole := fun _ => true
    initialLeftPole := rfl
    initialRightPole := rfl }

def unitObstruction : CircularClosureObstruction unitCircular unitEndpoints :=
  { TotalLoop := PLift (false = true)
    closeFromIdentification := fun equality => ⟨equality⟩
    loopContractsInitialDifference := fun loop => loop.down
    rejectInitialContraction := fun _ equality => Bool.noConfusion equality }

def unitHistorical : CircularPresentation :=
  unitHistory.toHistorical unitPositive false unitEndpoints unitObstruction

theorem unit_historical_deployment : unitHistorical.perimeter = unitHistory.deploy := rfl

theorem unit_historical_positive : unitHistorical.toPositiveCircularPresentation = unitCircular := rfl

def branchingNode (state : Bool) : LocalNode Bool Bool (fun _ _ => Unit) Unit (fun _ => Unit) :=
  { explicit := state
    implicit := state
    difference := ()
    provenance := ()
    internallyCompatible := () }

def branchingFormation : PositiveFormation :=
  { Explicit := Bool
    Implicit := Bool
    Compatible := fun _ _ => Unit
    Difference := Unit
    Provenance := fun _ => Unit
    State := Bool
    node := branchingNode
    Step := fun _ _ => Unit
    compatibility := fun _ => () }

def leftHistory : PositiveHistory branchingFormation false false := .cons () .nil

def rightHistory : PositiveHistory branchingFormation false true := .cons () .nil

theorem branching_targets_distinct :
    leftHistory.deploy.finalNode.explicit ≠ rightHistory.deploy.finalNode.explicit :=
  fun equality => Bool.noConfusion equality

def leftContinuation : ChosenPositiveContinuation branchingFormation :=
  { successor := fun _ => false
    step := fun _ => () }

def rightContinuation : ChosenPositiveContinuation branchingFormation :=
  { successor := fun _ => true
    step := fun _ => () }

theorem chosen_successors_distinct :
    leftContinuation.successor false ≠ rightContinuation.successor false :=
  fun equality => Bool.noConfusion equality

def chosenTwoSteps :
    Σ target : branchingFormation.State, PositiveHistory branchingFormation false target :=
  rightContinuation.walk false 2

def chosenTwoStepsPositive : PositiveHistory.Occurrence chosenTwoSteps.2 :=
  rightContinuation.walk_successor_positive false 1

def repeatedHistory : PositiveHistory unitFormation () () :=
  .cons (middle := ()) true (.cons false .nil)

def firstOccurrence : PositiveHistory.Occurrence repeatedHistory := .here

def secondOccurrence : PositiveHistory.Occurrence repeatedHistory := .later .here

theorem raw_nodes_repeat :
    (repeatedHistory.linkAt firstOccurrence).source =
      (repeatedHistory.linkAt secondOccurrence).source := rfl

theorem repeated_occurrences_distinct : firstOccurrence ≠ secondOccurrence :=
  PositiveHistory.here_ne_later .here

theorem repeated_positions_distinct :
    repeatedHistory.toPosition firstOccurrence ≠ repeatedHistory.toPosition secondOccurrence := by
  intro equality
  have recovered := congrArg repeatedHistory.fromPosition equality
  exact repeated_occurrences_distinct recovered

theorem repeated_step_witnesses_distinct :
    (repeatedHistory.linkAt firstOccurrence).compatibility ≠
      (repeatedHistory.linkAt secondOccurrence).compatibility :=
  fun equality => Bool.noConfusion equality

end RelationalPerimeter.Constitution.PositiveGenerationExamples

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Constitution.PositiveGenerationExamples.directedCompatible
#print axioms RelationalPerimeter.Constitution.PositiveGenerationExamples.directedNode
#print axioms RelationalPerimeter.Constitution.PositiveGenerationExamples.DirectedStep
#print axioms RelationalPerimeter.Constitution.PositiveGenerationExamples.directedFormation
#print axioms RelationalPerimeter.Constitution.PositiveGenerationExamples.directedHistory
#print axioms RelationalPerimeter.Constitution.PositiveGenerationExamples.directedPositive
#print axioms RelationalPerimeter.Constitution.PositiveGenerationExamples.directed_closing_empty
#print axioms RelationalPerimeter.Constitution.PositiveGenerationExamples.directed_no_pointing
#print axioms RelationalPerimeter.Constitution.PositiveGenerationExamples.directed_no_global_continuation
#print axioms RelationalPerimeter.Constitution.PositiveGenerationExamples.unitNode
#print axioms RelationalPerimeter.Constitution.PositiveGenerationExamples.unitFormation
#print axioms RelationalPerimeter.Constitution.PositiveGenerationExamples.unitHistory
#print axioms RelationalPerimeter.Constitution.PositiveGenerationExamples.unitPositive
#print axioms RelationalPerimeter.Constitution.PositiveGenerationExamples.unitCircular
#print axioms RelationalPerimeter.Constitution.PositiveGenerationExamples.unit_step_witness
#print axioms RelationalPerimeter.Constitution.PositiveGenerationExamples.unit_closing_witness
#print axioms RelationalPerimeter.Constitution.PositiveGenerationExamples.unitEndpoints
#print axioms RelationalPerimeter.Constitution.PositiveGenerationExamples.unitObstruction
#print axioms RelationalPerimeter.Constitution.PositiveGenerationExamples.unitHistorical
#print axioms RelationalPerimeter.Constitution.PositiveGenerationExamples.unit_historical_deployment
#print axioms RelationalPerimeter.Constitution.PositiveGenerationExamples.unit_historical_positive
#print axioms RelationalPerimeter.Constitution.PositiveGenerationExamples.branchingNode
#print axioms RelationalPerimeter.Constitution.PositiveGenerationExamples.branchingFormation
#print axioms RelationalPerimeter.Constitution.PositiveGenerationExamples.leftHistory
#print axioms RelationalPerimeter.Constitution.PositiveGenerationExamples.rightHistory
#print axioms RelationalPerimeter.Constitution.PositiveGenerationExamples.branching_targets_distinct
#print axioms RelationalPerimeter.Constitution.PositiveGenerationExamples.leftContinuation
#print axioms RelationalPerimeter.Constitution.PositiveGenerationExamples.rightContinuation
#print axioms RelationalPerimeter.Constitution.PositiveGenerationExamples.chosen_successors_distinct
#print axioms RelationalPerimeter.Constitution.PositiveGenerationExamples.chosenTwoSteps
#print axioms RelationalPerimeter.Constitution.PositiveGenerationExamples.chosenTwoStepsPositive
#print axioms RelationalPerimeter.Constitution.PositiveGenerationExamples.repeatedHistory
#print axioms RelationalPerimeter.Constitution.PositiveGenerationExamples.firstOccurrence
#print axioms RelationalPerimeter.Constitution.PositiveGenerationExamples.secondOccurrence
#print axioms RelationalPerimeter.Constitution.PositiveGenerationExamples.raw_nodes_repeat
#print axioms RelationalPerimeter.Constitution.PositiveGenerationExamples.repeated_occurrences_distinct
#print axioms RelationalPerimeter.Constitution.PositiveGenerationExamples.repeated_positions_distinct
#print axioms RelationalPerimeter.Constitution.PositiveGenerationExamples.repeated_step_witnesses_distinct
/- AXIOM_AUDIT_END -/
