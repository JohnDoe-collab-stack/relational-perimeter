import RelationalPerimeter.Constitution.Godel.OperationalH1
import RelationalPerimeter.Constitution.Godel.PerimetralCorrespondence
import RelationalPerimeter.Constitution.Godel.OperationalClosure

set_option genInjectivity false
set_option autoImplicit false
set_option linter.defProp false
set_option maxHeartbeats 2000000

/-! Downstream compatibility of the operational H1 and the historical
perimetral H1. Both consumers receive the same positive execution core. -/
namespace StrongPerimetralTurning

universe uA uB uC uP uV
variable {coding : GodelDiagonalSyntax.{uC,uA,uB,uP,uV}}
  {unprovabilityFormula : coding.UnaryFormula}
  {interpretation : GodelProvabilityInterpretation coding unprovabilityFormula}
  {execution : ExecutedGodelProduction coding unprovabilityFormula interpretation}

def godelOperationalPerimetralOccurrenceTransport
    (core : GodelPositiveExecutionCore execution) (h1 : GodelOperationalH1 core) :
    ExactTypeTransport (History.Occurrence h1.history)
      (History.Occurrence (godelPerimetralContinuation execution).history) := by
  cases h1 with
  | mk history exactHistory executedOrder =>
      cases exactHistory
      exact
        { forward := fun
            | .last => .last
            | .earlier .last => .earlier .last
            | .earlier (.earlier .last) => .earlier (.earlier .last)
            | .earlier (.earlier (.earlier impossible)) => nomatch impossible
          backward := fun
            | .last => .last
            | .earlier .last => .earlier .last
            | .earlier (.earlier .last) => .earlier (.earlier .last)
            | .earlier (.earlier (.earlier impossible)) => nomatch impossible
          forwardBackward := by
            intro occurrence
            cases occurrence with
            | last => rfl
            | earlier occurrence =>
                cases occurrence with
                | last => rfl
                | earlier occurrence =>
                    cases occurrence with
                    | last => rfl
                    | earlier impossible => exact nomatch impossible
          backwardForward := by
            intro occurrence
            cases occurrence with
            | last => rfl
            | earlier occurrence =>
                cases occurrence with
                | last => rfl
                | earlier occurrence =>
                    cases occurrence with
                    | last => rfl
                    | earlier impossible => exact nomatch impossible }

theorem godelOperationalPerimetralTransport_production
    (core : GodelPositiveExecutionCore execution) (h1 : GodelOperationalH1 core) :
    (godelOperationalPerimetralOccurrenceTransport core h1).forward h1.productionOccurrence =
      (godelAffirmativeConstitutionFromCore core).productionOccurrence := by
  cases h1 with
  | mk history exactHistory executedOrder => cases exactHistory; rfl

theorem godelOperationalPerimetralTransport_injective
    (core : GodelPositiveExecutionCore execution) (h1 : GodelOperationalH1 core) :
    Function.Injective (godelOperationalPerimetralOccurrenceTransport core h1).forward := by
  intro first second equality
  let transport := godelOperationalPerimetralOccurrenceTransport core h1
  exact (transport.forwardBackward first).symm.trans
    ((congrArg transport.backward equality).trans (transport.forwardBackward second))

theorem godelOperationalPerimetralTransport_preservesNext
    (core : GodelPositiveExecutionCore execution) (h1 : GodelOperationalH1 core)
    {first second : History.Occurrence h1.history}
    (next : History.OccurrenceNext first second) :
    History.OccurrenceNext
      ((godelOperationalPerimetralOccurrenceTransport core h1).forward first)
      ((godelOperationalPerimetralOccurrenceTransport core h1).forward second) := by
  cases h1 with
  | mk history exactHistory executedOrder =>
      cases exactHistory
      cases next with
      | previous_last => exact .previous_last
      | earlier_earlier previous =>
          cases previous with
          | previous_last => exact .earlier_earlier .previous_last
          | earlier_earlier impossible =>
              cases impossible
              rename_i firstRoot secondRoot remainingOrder
              exact nomatch firstRoot

theorem godelOperationalPerimetralTransport_certification
    (core : GodelPositiveExecutionCore execution) (h1 : GodelOperationalH1 core) :
    (godelOperationalPerimetralOccurrenceTransport core h1).forward h1.certificationOccurrence =
      (godelAffirmativeConstitutionFromCore core).certificationOccurrence := by
  cases h1 with
  | mk history exactHistory executedOrder => cases exactHistory; rfl

theorem godelOperationalPerimetralTransport_continuation
    (core : GodelPositiveExecutionCore execution) (h1 : GodelOperationalH1 core) :
    (godelOperationalPerimetralOccurrenceTransport core h1).forward h1.continuationOccurrence =
      (godelAffirmativeConstitutionFromCore core).continuationOccurrence := by
  cases h1 with
  | mk history exactHistory executedOrder => cases exactHistory; rfl

theorem godelOperationalPerimetralTransport_productionNextCertification
    (core : GodelPositiveExecutionCore execution) (h1 : GodelOperationalH1 core) :
    History.OccurrenceNext
      ((godelOperationalPerimetralOccurrenceTransport core h1).forward h1.productionOccurrence)
      ((godelOperationalPerimetralOccurrenceTransport core h1).forward h1.certificationOccurrence) := by
  cases h1 with
  | mk history exactHistory executedOrder =>
      cases exactHistory
      exact .earlier_earlier .previous_last

theorem godelOperationalPerimetralTransport_certificationNextContinuation
    (core : GodelPositiveExecutionCore execution) (h1 : GodelOperationalH1 core) :
    History.OccurrenceNext
      ((godelOperationalPerimetralOccurrenceTransport core h1).forward h1.certificationOccurrence)
      ((godelOperationalPerimetralOccurrenceTransport core h1).forward h1.continuationOccurrence) := by
  cases h1 with
  | mk history exactHistory executedOrder =>
      cases exactHistory
      exact .previous_last

structure GodelOperationalPerimetralBridge
    (core : GodelPositiveExecutionCore execution) (h1 : GodelOperationalH1 core) where
  transport : ExactTypeTransport (History.Occurrence h1.history)
    (History.Occurrence (godelPerimetralContinuation execution).history)
  affirmative : GodelAffirmativeConstitution execution
  executedOccurrencesAreShared : affirmative.occurrenceCorrespondence.executed = core.occurrences
  productionExact : transport.forward h1.productionOccurrence = affirmative.productionOccurrence
  certificationExact : transport.forward h1.certificationOccurrence = affirmative.certificationOccurrence
  continuationExact : transport.forward h1.continuationOccurrence = affirmative.continuationOccurrence
  productionNextCertification : History.OccurrenceNext
    (transport.forward h1.productionOccurrence) (transport.forward h1.certificationOccurrence)
  certificationNextContinuation : History.OccurrenceNext
    (transport.forward h1.certificationOccurrence) (transport.forward h1.continuationOccurrence)
  sourceProvenanceRetainsWitness :
    PLift ((godelPerimetralPresentation execution).perimeter.finalNode.difference = execution.witness)

def godelOperationalPerimetralBridge
    (core : GodelPositiveExecutionCore execution) (h1 : GodelOperationalH1 core) :
    GodelOperationalPerimetralBridge core h1 :=
  { transport := godelOperationalPerimetralOccurrenceTransport core h1
    affirmative := godelAffirmativeConstitutionFromCore core
    executedOccurrencesAreShared := rfl
    productionExact := godelOperationalPerimetralTransport_production core h1
    certificationExact := godelOperationalPerimetralTransport_certification core h1
    continuationExact := godelOperationalPerimetralTransport_continuation core h1
    productionNextCertification :=
      godelOperationalPerimetralTransport_productionNextCertification core h1
    certificationNextContinuation :=
      godelOperationalPerimetralTransport_certificationNextContinuation core h1
    sourceProvenanceRetainsWitness := godelContinuation_sourceProvenance_retains_witness execution }

def endpointAt (presentation : CircularPresentation) : ClosurePole → presentation.Endpoint
  | .left => presentation.leftEndpoint
  | .right => presentation.rightEndpoint

theorem godelEndpointAt_matches_perimeter
    (execution : ExecutedGodelProduction coding unprovabilityFormula interpretation)
    (pole : ClosurePole) :
    godelEndpointAt execution pole = endpointAt (godelPerimetralPresentation execution) pole := by
  cases pole <;> rfl

/-- Interpret each already received continuation step by one historical
perimetral generation. The fold consumes the history itself. -/
def godelPerimetralHistoryAlongPostH1
    {source target : GodelPostH1State}
    (post : History GodelPostH1Step source target)
    (initial : RootedGeneratedHistory (godelPerimetralPresentation execution)) :
    RootedGeneratedHistory (godelPerimetralPresentation execution) :=
  match post with
  | .root => initial
  | .extend previous _ =>
      let received := godelPerimetralHistoryAlongPostH1 previous initial
      appendGenerated received (generate received.endpoint)
termination_by structural post

def godelPerimetralHistoryFromOperational
    (core : GodelPositiveExecutionCore execution) (h1 : GodelOperationalH1 core)
    (history : GodelOperationalHistory h1) :
    RootedGeneratedHistory (godelPerimetralPresentation execution) :=
  godelPerimetralHistoryAlongPostH1 history.continuation (godelPerimetralContinuation execution)

namespace GodelClosureSource

def perimetralHistory (source : GodelClosureSource execution) :
    RootedGeneratedHistory (godelPerimetralPresentation execution) :=
  godelPerimetralHistoryFromOperational source.core source.h1 source.operationalHistory

def perimetralEndpoint (source : GodelClosureSource execution) := source.perimetralHistory.endpoint

def perimetralDifference (source : GodelClosureSource execution) :=
  boundaryDifferenceReadout source.perimetralEndpoint.2.2

def perimetralProvenance (source : GodelClosureSource execution) :=
  source.perimetralHistory.terminalClosureObstruction.provenance

theorem perimetralProvenance_is_initial (source : GodelClosureSource execution) :
    source.perimetralProvenance =
      (godelPerimetralPresentation execution).initialNode.provenance :=
  congrArg PositiveClosureObstruction.provenance
    source.perimetralHistory.terminalClosureObstruction_is_initial

theorem perimetralHistory_continue (source : GodelClosureSource execution)
    (active : source.phase = .active) :
    (godelRuntimeNext execution source .continue).perimetralHistory =
      appendGenerated source.perimetralHistory (generate source.perimetralHistory.endpoint) := by
  cases source with
  | mk core h1 pole history phase =>
      cases active
      rfl

end GodelClosureSource

theorem initializeAt_perimetralHistory
    (execution : ExecutedGodelProduction coding unprovabilityFormula interpretation)
    (core : GodelPositiveExecutionCore execution) (h1 : GodelOperationalH1 core)
    (pole : ClosurePole) :
    (initializeAt execution core h1 pole).perimetralHistory = godelPerimetralContinuation execution := rfl

end StrongPerimetralTurning

/- AXIOM_AUDIT_BEGIN -/
#print axioms StrongPerimetralTurning.godelOperationalPerimetralOccurrenceTransport
#print axioms StrongPerimetralTurning.godelOperationalPerimetralTransport_production
#print axioms StrongPerimetralTurning.godelOperationalPerimetralTransport_injective
#print axioms StrongPerimetralTurning.godelOperationalPerimetralTransport_preservesNext
#print axioms StrongPerimetralTurning.godelOperationalPerimetralTransport_certification
#print axioms StrongPerimetralTurning.godelOperationalPerimetralTransport_continuation
#print axioms StrongPerimetralTurning.godelOperationalPerimetralTransport_productionNextCertification
#print axioms StrongPerimetralTurning.godelOperationalPerimetralTransport_certificationNextContinuation
#print axioms StrongPerimetralTurning.GodelOperationalPerimetralBridge
#print axioms StrongPerimetralTurning.godelOperationalPerimetralBridge
#print axioms StrongPerimetralTurning.endpointAt
#print axioms StrongPerimetralTurning.godelEndpointAt_matches_perimeter
#print axioms StrongPerimetralTurning.godelPerimetralHistoryAlongPostH1
#print axioms StrongPerimetralTurning.godelPerimetralHistoryFromOperational
#print axioms StrongPerimetralTurning.GodelClosureSource.perimetralHistory
#print axioms StrongPerimetralTurning.GodelClosureSource.perimetralEndpoint
#print axioms StrongPerimetralTurning.GodelClosureSource.perimetralDifference
#print axioms StrongPerimetralTurning.GodelClosureSource.perimetralProvenance
#print axioms StrongPerimetralTurning.GodelClosureSource.perimetralProvenance_is_initial
#print axioms StrongPerimetralTurning.GodelClosureSource.perimetralHistory_continue
#print axioms StrongPerimetralTurning.initializeAt_perimetralHistory
/- AXIOM_AUDIT_END -/
