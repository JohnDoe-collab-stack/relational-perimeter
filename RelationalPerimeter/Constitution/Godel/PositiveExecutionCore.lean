import RelationalPerimeter.Constitution.Godel.Diagonal

set_option genInjectivity false
set_option autoImplicit false
set_option linter.defProp false

/-! The positive resource shared by the operational and perimetral consumers.
A structural prefix fold extracts the received execution without impossible
branches and without constructing another diagonal production. -/
namespace StrongPerimetralTurning

universe uA uB uC uP uV uT
variable {coding : GodelDiagonalSyntax.{uC,uA,uB,uP,uV}}
  {unprovabilityFormula : coding.UnaryFormula}
  {interpretation : GodelProvabilityInterpretation.{uT,uC,uA,uB,uP,uV} coding unprovabilityFormula}

structure GodelPositiveLastOccurrence
    {state : ExecutedGodelProductionState coding unprovabilityFormula interpretation}
    (history : History (@ExecutedGodelProductionStep coding unprovabilityFormula interpretation)
      .received state) where
  occurrence : History.Occurrence history
  beforeExtension :
    {nextState : ExecutedGodelProductionState coding unprovabilityFormula interpretation} →
    (step : ExecutedGodelProductionStep state nextState) →
    History.OccurrenceNext (.earlier occurrence)
      (.last : History.Occurrence (.extend history step))

structure GodelPositiveDiagonalPrefix
    (diagonal : ExecutedGodelDiagonalProduction coding unprovabilityFormula)
    (history : History (@ExecutedGodelProductionStep coding unprovabilityFormula interpretation)
      .received (.diagonalized diagonal)) where
  diagonalIsCanonical : diagonal = executeGodelDiagonalProduction coding unprovabilityFormula
  last : GodelPositiveLastOccurrence history

structure GodelPositiveSentencePrefix
    (production : ExecutedGodelSentenceProduction coding unprovabilityFormula)
    (history : History (@ExecutedGodelProductionStep coding unprovabilityFormula interpretation)
      .received (.sentenceProduced production)) where
  diagonal : ExecutedGodelDiagonalProduction coding unprovabilityFormula
  diagonalIsCanonical : diagonal = executeGodelDiagonalProduction coding unprovabilityFormula
  productionIsSelfApplication : production = executeGodelSentenceProduction diagonal
  diagonalizeOccurrence : History.Occurrence history
  last : GodelPositiveLastOccurrence history
  diagonalizeNextSelfApply : History.OccurrenceNext diagonalizeOccurrence last.occurrence

def GodelPositiveProductionPrefix
    {state : ExecutedGodelProductionState coding unprovabilityFormula interpretation}
    (history : History (@ExecutedGodelProductionStep coding unprovabilityFormula interpretation)
      .received state) : Type (max uA uC uP uV uT) :=
  match state with
  | .received => PUnit
  | .diagonalized diagonal => GodelPositiveDiagonalPrefix diagonal history
  | .sentenceProduced production => GodelPositiveSentencePrefix production history
  | .witnessProduced witness => ExecutedGodelProductionOccurrences
      ({ witness := witness, history := history } :
        ExecutedGodelProduction coding unprovabilityFormula interpretation)

def godelPositiveProductionPrefixExtend
    {state nextState : ExecutedGodelProductionState coding unprovabilityFormula interpretation}
    (history : History (@ExecutedGodelProductionStep coding unprovabilityFormula interpretation)
      .received state)
    (step : ExecutedGodelProductionStep state nextState)
    (received : GodelPositiveProductionPrefix history) :
    GodelPositiveProductionPrefix (.extend history step) := by
      cases step with
      | diagonalize =>
          exact
          { diagonalIsCanonical := rfl
            last := { occurrence := .last, beforeExtension := fun _ => .previous_last } }
      | selfApply diagonal =>
          exact
          { diagonal := diagonal
            diagonalIsCanonical := received.diagonalIsCanonical
            productionIsSelfApplication := rfl
            diagonalizeOccurrence := .earlier received.last.occurrence
            last := { occurrence := .last, beforeExtension := fun _ => .previous_last }
            diagonalizeNextSelfApply := received.last.beforeExtension (.selfApply diagonal) }
      | certify production =>
          exact
          { diagonal := received.diagonal
            production := production
            diagonalIsCanonical := received.diagonalIsCanonical
            productionIsSelfApplication := received.productionIsSelfApplication
            witnessIsCertification := rfl
            diagonalizeOccurrence := .earlier received.diagonalizeOccurrence
            selfApplyOccurrence := .earlier received.last.occurrence
            certifyOccurrence := .last
            diagonalizeNextSelfApply := .earlier_earlier received.diagonalizeNextSelfApply
            selfApplyNextCertify := received.last.beforeExtension (.certify production) }

def godelPositiveProductionPrefix
    {state : ExecutedGodelProductionState coding unprovabilityFormula interpretation}
    (history : History (@ExecutedGodelProductionStep coding unprovabilityFormula interpretation)
      .received state) : GodelPositiveProductionPrefix history :=
  match history with
  | .root => .unit
  | .extend previous step =>
      godelPositiveProductionPrefixExtend previous step (godelPositiveProductionPrefix previous)
termination_by structural history

def godelPositiveExecutionOccurrences
    (execution : ExecutedGodelProduction coding unprovabilityFormula interpretation) :
    ExecutedGodelProductionOccurrences execution :=
  godelPositiveProductionPrefix execution.history

structure GodelPositiveExecutionCore
    (execution : ExecutedGodelProduction coding unprovabilityFormula interpretation) where
  occurrences : ExecutedGodelProductionOccurrences execution
  productionIsWitnessProduction :
    occurrences.production = execution.witness.production

def godelPositiveExecutionCore
    (execution : ExecutedGodelProduction coding unprovabilityFormula interpretation) :
    GodelPositiveExecutionCore execution :=
  let occurrences := godelPositiveExecutionOccurrences execution
  { occurrences := occurrences
    productionIsWitnessProduction :=
      (congrArg ExecutedGodelWitness.production occurrences.witnessIsCertification).symm }

end StrongPerimetralTurning

/- AXIOM_AUDIT_BEGIN -/
#print axioms StrongPerimetralTurning.GodelPositiveLastOccurrence
#print axioms StrongPerimetralTurning.GodelPositiveDiagonalPrefix
#print axioms StrongPerimetralTurning.GodelPositiveSentencePrefix
#print axioms StrongPerimetralTurning.GodelPositiveProductionPrefix
#print axioms StrongPerimetralTurning.godelPositiveProductionPrefixExtend
#print axioms StrongPerimetralTurning.godelPositiveProductionPrefix
#print axioms StrongPerimetralTurning.godelPositiveExecutionOccurrences
#print axioms StrongPerimetralTurning.GodelPositiveExecutionCore
#print axioms StrongPerimetralTurning.godelPositiveExecutionCore
/- AXIOM_AUDIT_END -/
