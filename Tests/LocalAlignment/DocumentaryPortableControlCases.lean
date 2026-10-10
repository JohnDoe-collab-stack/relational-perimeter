import Tests.LocalAlignment.DocumentaryPortableControl
import Tests.LocalAlignment.DocumentaryMemoryCases

/-! Closed control restoration cases. Actual frames include diversions, failures,
absent task bindings and equal-valued distinct occurrences. The supplied master
and store remain explicit; none of these cases claims full-present byte restart. -/
set_option genInjectivity false
set_option maxHeartbeats 3000000
namespace ConstitutiveSearch.Agent.Local.Documentary.PortableControlCases
open Resources Program Adaptive Snapshot ControlCodec

theorem every_typed_present {context sources contract rules Context final}
    (codec : Codec Context) (before : @PresentData context sources contract rules Context final) :
    PortableControl.loadPresent codec before.session.frame.dossier before.session.frame.store final
      (PortableControl.save codec (PortableControl.capture before)) = some before := PortableControl.present_byte_roundtrip codec before

theorem actual_prefix : PortableControl.loadPresent natural MemoryCases.retainedPrefix.session.frame.dossier
    MemoryCases.retainedPrefix.session.frame.store _ (PortableControl.save natural (PortableControl.capture MemoryCases.retainedPrefix)) =
    some MemoryCases.retainedPrefix := PortableControl.present_byte_roundtrip natural MemoryCases.retainedPrefix

theorem every_prefix_future
    (after : PresentData Cases.sources Cases.contract DeductionCases.policy Nat
      [ProgramCases.sumSpec, ProgramCases.baselineSpec, ProgramCases.deltaSpec,
       ProgramCases.revisedSpec, ProgramCases.baselineSpec])
    (loaded : PortableControl.loadPresent natural MemoryCases.retainedPrefix.session.frame.dossier
      MemoryCases.retainedPrefix.session.frame.store _
      (PortableControl.save natural (PortableControl.capture MemoryCases.retainedPrefix)) = some after)
    (requests : List (Memory.Request Nat)) :
    HEq (Memory.run after requests) (Memory.run MemoryCases.retainedPrefix requests) :=
  PortableControl.loaded_all_futures natural MemoryCases.retainedPrefix after loaded requests

def afterReset := MemoryCases.retainedPrefix.reset (AdaptiveCases.policy 4)

theorem reset_control : PortableControl.loadPresent natural afterReset.session.frame.dossier afterReset.session.frame.store _
    (PortableControl.save natural (PortableControl.capture afterReset)) = some afterReset := PortableControl.present_byte_roundtrip natural afterReset

theorem actual_boot : PortableControl.loadPresent natural MemoryCases.boot.session.frame.dossier MemoryCases.boot.session.frame.store _
    (PortableControl.save natural (PortableControl.capture MemoryCases.boot)) = some MemoryCases.boot :=
  PortableControl.present_byte_roundtrip natural MemoryCases.boot

def wrongRun := Adaptive.run (AdaptiveCases.policy 0) (AdaptiveCases.feed false)
  AdaptiveCases.start ProgramCases.wrongScript
def wrong : PresentData Cases.sources Cases.contract DeductionCases.policy Nat
    [.conclusion ProgramCases.downstreamDemand, ProgramCases.wrongSpec,
     ProgramCases.revisedSpec, ProgramCases.baselineSpec] :=
  Snapshot.present ⟨_, wrongRun.1, .done⟩

theorem wrong_control : PortableControl.loadPresent natural wrong.session.frame.dossier wrong.session.frame.store _
    (PortableControl.save natural (PortableControl.capture wrong)) = some wrong := PortableControl.present_byte_roundtrip natural wrong

theorem wrong_stays_wrong : succeeded wrong.session.frame.restore = false := rfl

theorem blocked_control : PortableControl.loadPresent natural MemoryCases.blockedRetained.session.frame.dossier
    MemoryCases.blockedRetained.session.frame.store _ (PortableControl.save natural (PortableControl.capture MemoryCases.blockedRetained)) =
    some MemoryCases.blockedRetained := PortableControl.present_byte_roundtrip natural MemoryCases.blockedRetained

def prefixRaw := PortableControl.record (PortableControl.capture MemoryCases.retainedPrefix)

theorem prefix_context : prefixRaw.context = 1 := rfl
theorem prefix_clock : prefixRaw.round = 3 := rfl
theorem prefix_queue : prefixRaw.remaining =
    [.quotation ProgramCases.baselineTask.demand 0 1,
     .conclusion 1 1 1 DeductionCases.sumDemand] := rfl

theorem missing_source :
    PortableControl.loadInstruction Cases.context DeductionCases.policy []
      (.quotation ProgramCases.baselineTask.demand 99 1) = none := rfl

theorem missing_rule :
    PortableControl.loadInstruction Cases.context DeductionCases.policy
      [ProgramCases.revisedSpec, ProgramCases.baselineSpec]
      (.conclusion 99 1 0 DeductionCases.deltaDemand) = none := rfl

theorem missing_dependency :
    PortableControl.loadInstruction Cases.context DeductionCases.policy
      [ProgramCases.revisedSpec, ProgramCases.baselineSpec]
      (.conclusion 0 99 0 DeductionCases.deltaDemand) = none := rfl

/-- Queued requests are data, not admissions. A forbidden operation is restored
as that very pending instruction, so its future refusal is preserved. -/
def forbiddenPending : Instruction Cases.context DeductionCases.policy
    [ProgramCases.revisedSpec, ProgramCases.baselineSpec] (.conclusion DeductionCases.forbiddenDemand) :=
  .conclusion DeductionCases.duplicateRequest (.prior .here) .here DeductionCases.forbiddenDemand

theorem forbidden_pending_preserved :
    PortableControl.loadInstruction Cases.context DeductionCases.policy
      [ProgramCases.revisedSpec, ProgramCases.baselineSpec]
      (PortableControl.instruction forbiddenPending) =
      some ⟨Specification.conclusion DeductionCases.forbiddenDemand, forbiddenPending⟩ :=
  PortableControl.instruction_exact forbiddenPending

theorem missing_binding_occurrence :
    PortableControl.loadBinding (⟨[], Deduction.empty Cases.sources Cases.contract DeductionCases.policy⟩) (some 99) = none := rfl

theorem missing_binding_entry :
    PortableControl.loadBindings (⟨[], Deduction.empty Cases.sources Cases.contract DeductionCases.policy⟩)
      [ProgramCases.baselineSpec] [] = none := rfl

theorem extra_binding_entry :
    PortableControl.loadBindings MemoryCases.boot.session.frame.store [] [none] = none := rfl

def emptyRaw : Raw Nat := ⟨[], [], [], 0, 0, none⟩

theorem altered_final :
    (PortableControl.restore (⟨[], Deduction.empty Cases.sources Cases.contract DeductionCases.policy⟩)
      [ProgramCases.baselineSpec] emptyRaw).isSome = false := rfl

def wrongVersion : List UInt8 :=
  bytes ([2, 4] ++ (raw natural).words emptyRaw)
def wrongSchema : List UInt8 :=
  bytes ([1, 3] ++ (raw natural).words emptyRaw)
def extraWord : List UInt8 :=
  bytes ((envelope natural).words emptyRaw ++ [0])

theorem bad_version : ControlCodec.load natural wrongVersion = none := rfl
theorem bad_schema : ControlCodec.load natural wrongSchema = none := rfl
theorem trailing_word : ControlCodec.load natural extraWord = none := rfl
theorem bad_alphabet : ControlCodec.load natural [7] = none := rfl

def listContext : Raw (List Nat) :=
  ⟨prefixRaw.slots, prefixRaw.bindings, prefixRaw.remaining, [0, 1, 1], prefixRaw.round, prefixRaw.last⟩

theorem list_context_realized : ControlCodec.load natural.list (ControlCodec.save natural.list listContext) =
    some listContext := ControlCodec.byte_roundtrip natural.list listContext

end ConstitutiveSearch.Agent.Local.Documentary.PortableControlCases

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableControlCases.every_typed_present
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableControlCases.actual_prefix
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableControlCases.every_prefix_future
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableControlCases.afterReset
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableControlCases.reset_control
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableControlCases.actual_boot
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableControlCases.wrongRun
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableControlCases.wrong
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableControlCases.wrong_control
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableControlCases.wrong_stays_wrong
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableControlCases.blocked_control
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableControlCases.prefixRaw
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableControlCases.prefix_context
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableControlCases.prefix_clock
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableControlCases.prefix_queue
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableControlCases.missing_source
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableControlCases.missing_rule
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableControlCases.missing_dependency
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableControlCases.forbiddenPending
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableControlCases.forbidden_pending_preserved
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableControlCases.missing_binding_occurrence
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableControlCases.missing_binding_entry
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableControlCases.extra_binding_entry
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableControlCases.emptyRaw
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableControlCases.altered_final
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableControlCases.wrongVersion
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableControlCases.wrongSchema
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableControlCases.extraWord
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableControlCases.bad_version
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableControlCases.bad_schema
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableControlCases.trailing_word
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableControlCases.bad_alphabet
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableControlCases.listContext
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableControlCases.list_context_realized
/- AXIOM_AUDIT_END -/
