import Tests.LocalAlignment.DocumentaryPortableCheckpoint
import RelationalPerimeter.Computation.ConstitutiveSearch.EndogenousDecomposition.VariableMasterInstance

/-! Start-side fixture only. The resume client does not import this module.
Its prefix consumes a received initial frame and is executed once at runtime. -/
set_option genInjectivity false
set_option maxHeartbeats 2000000
namespace ConstitutiveSearch.Agent.Local.Documentary.PortableStart
open Resources Program PortableCheckpoint

def baselineTask : Dossier.Obligation context :=
  ⟨⟨7, 42, some 1⟩, ⟨⟨0, 2, 0⟩, .here⟩, ⟨⟨1, 1, 0⟩, .prior .here⟩⟩
def revisionTask : Dossier.Obligation context :=
  ⟨⟨7, 43, some 2⟩, ⟨⟨1, 1, 0⟩, .prior .here⟩, ⟨⟨1, 2, 0⟩, .prior (.prior .here)⟩⟩

def script : Script context policy [] slots :=
  .cons (.quotation baselineTask) (.cons (.quotation revisionTask)
    (.cons (.conclusion difference (.prior .here) .here ⟨1, some 0, some [1, 2]⟩)
      (.cons (.quotation baselineTask) .done)))

def initial (cursor : EndogenousDecomposition.MasterResources.Cursor) : Frame sources contract policy [] :=
  ⟨⟨cursor, Documentary.empty sources contract⟩, ⟨[], Deduction.empty sources contract policy⟩, fun ref => nomatch ref⟩

def executePrefix (frame : Frame sources contract policy []) := Program.execute frame script

def remaining : Script context policy slots (.conclusion demand :: slots) :=
  .cons (.conclusion sum (.prior .here) (.prior .here) demand) .done

end ConstitutiveSearch.Agent.Local.Documentary.PortableStart
/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableStart.baselineTask
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableStart.revisionTask
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableStart.script
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableStart.initial
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableStart.executePrefix
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableStart.remaining
/- AXIOM_AUDIT_END -/
