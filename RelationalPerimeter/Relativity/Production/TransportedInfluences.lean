import RelationalPerimeter.Relativity.Production.InfluencePlans
import RelationalPerimeter.Relativity.Production.TransportedContinuations

/-!
# Permitted influence through exact occurrence transports

The plan's ports, origin, intervening productions and continuation are all
transported. This preserves the possibility of realizing the local influence,
not just the reading of an endpoint. Read and used-edge raccords remain
necessary to compare the actual executions; a bare reference permutation
does not assert that their received physical resources agree.
-/
set_option genInjectivity false
namespace RelationalPerimeter.Relativity.Production
open ConstitutiveSearch.Resources

def InfluencePlan.rename {source target : List Kind} {origin finalKind}
    (transport : ReferenceTransport source target) (plan : InfluencePlan source origin finalKind) :
    InfluencePlan target (transport.occurrences.forward origin) finalKind :=
  match plan with
  | .finish instruction ref port => .finish (instruction.rename transport.forward)
      (transport.forward ref) (port.rename transport.forward)
  | .follow instruction ref port tail => .follow (instruction.rename transport.forward)
      (transport.forward ref) (port.rename transport.forward) (tail.rename (transport.extend _))
  | .delay instruction tail => .delay (instruction.rename transport.forward) (tail.rename (transport.extend _))
termination_by structural plan

def InfluencePlan.returned {source target : List Kind} {origin finalKind}
    (transport : ReferenceTransport source target)
    (plan : InfluencePlan target (transport.occurrences.forward origin) finalKind) :
    InfluencePlan source origin finalKind :=
  transport.occurrences.forwardBackward origin ▸ plan.rename transport.reverse

theorem transported_influence_iff {source target : List Kind} (transport : ReferenceTransport source target)
    (origin : Occurrence source) (finalKind : Kind) :
    Nonempty (InfluencePlan target (transport.occurrences.forward origin) finalKind) ↔
      Nonempty (InfluencePlan source origin finalKind) :=
  ⟨fun ⟨plan⟩ => ⟨plan.returned transport⟩, fun ⟨plan⟩ => ⟨plan.rename transport⟩⟩

theorem InfluencePlan.renamed_schedule {source target : List Kind} {origin finalKind}
    (transport : ReferenceTransport source target) (plan : InfluencePlan source origin finalKind) :
    (plan.rename transport).schedule = plan.schedule.rename transport := by
  induction plan generalizing target with
  | finish instruction ref port => rfl
  | follow instruction ref port tail ih =>
    exact congrArg (Program.step (instruction.rename transport.forward)) (ih (transport.extend _))
  | delay instruction tail ih =>
    exact congrArg (Program.step (instruction.rename transport.forward)) (ih (transport.extend _))

theorem InfluencePlan.schedule_returns {source target : List Kind} {origin finalKind}
    (transport : ReferenceTransport source target) (plan : InfluencePlan source origin finalKind) :
    ((plan.rename transport).schedule).rename transport.reverse = plan.schedule :=
  (congrArg (fun schedule => schedule.rename transport.reverse) (plan.renamed_schedule transport)).trans
    (Program.rename_returns transport plan.schedule)

/-- Exact execution erasure on both sides, for a constituted read/edge raccord.
These are proof equations, not a runner that executes either side twice. -/
theorem corresponding_influence_executions {source target : Cursor} {origin finalKind}
    (raccord : ConstitutedRaccord source target) (plan : InfluencePlan source.kinds origin finalKind) :
    (continueCorresponding raccord plan.schedule).first = (realizeInfluence source plan).execution ∧
    (continueCorresponding raccord plan.schedule).second =
      (realizeInfluence target (plan.rename raccord.reading.references)).execution := by
  constructor
  · exact (continueCorresponding_source_exact raccord plan.schedule).trans
      (realizeInfluence_execution_exact source plan).symm
  · exact (continueCorresponding_target_exact raccord plan.schedule).trans
      ((congrArg (run target) (plan.renamed_schedule raccord.reading.references).symm).trans
        (realizeInfluence_execution_exact target _).symm)

end RelationalPerimeter.Relativity.Production
/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Relativity.Production.InfluencePlan.rename
#print axioms RelationalPerimeter.Relativity.Production.InfluencePlan.returned
#print axioms RelationalPerimeter.Relativity.Production.transported_influence_iff
#print axioms RelationalPerimeter.Relativity.Production.InfluencePlan.renamed_schedule
#print axioms RelationalPerimeter.Relativity.Production.InfluencePlan.schedule_returns
#print axioms RelationalPerimeter.Relativity.Production.corresponding_influence_executions
/- AXIOM_AUDIT_END -/
