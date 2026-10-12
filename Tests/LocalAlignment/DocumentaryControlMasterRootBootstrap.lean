import Tests.LocalAlignment.DocumentaryControlMasterGeneration
import Tests.LocalAlignment.DocumentaryControlResources
import RelationalPerimeter.Computation.ConstitutiveSearch.EndogenousDecomposition.MasterResourceExecution

/-! Generic convenience bootstrap reads the actual retained source through its
received reference before creating the measured root. Its receipt only
retargets the original root specification in erased proof data. -/
set_option genInjectivity false
set_option maxHeartbeats 3000000
namespace ConstitutiveSearch.Agent.Local.Documentary.ControlMasterRootBootstrap
open Resources EndogenousDecomposition Control ControlBindings ControlMasterData

@[inline] def receivedRoot (cursor : MasterResources.Cursor)
    (state : ControlResources.Read cursor.support.values cursor.source)
    (root : Actual (constructMeasuredOperationalRoot state.1.down.searchSeed)) :
    Actual (constructMeasuredOperationalRoot cursor.state.searchSeed) := by
  obtain ⟨_, same⟩ := state
  cases same
  exact root

def code (cursor : MasterResources.Cursor) : Code Label (Actual (constructMeasuredOperationalRoot cursor.state.searchSeed)) :=
  (ControlResources.readCode cursor.support.values cursor.source).bind (fun state =>
    (ControlMasterGeneration.rootCode state.1.down.searchSeed).bind (fun root =>
      .done (receivedRoot cursor state root)))

theorem finite (cursor : MasterResources.Cursor) : Finite (code cursor) := by
  apply finite_bind
  · obtain ⟨value, labels, trace, _⟩ := ControlResources.read_bounded cursor.support.values cursor.source
    exact ⟨value, labels, trace⟩
  · intro state
    apply finite_bind (ControlMasterGeneration.root_finite _); intro root
    exact finite_done _

end ConstitutiveSearch.Agent.Local.Documentary.ControlMasterRootBootstrap

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMasterRootBootstrap.receivedRoot
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMasterRootBootstrap.code
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMasterRootBootstrap.finite
/- AXIOM_AUDIT_END -/
