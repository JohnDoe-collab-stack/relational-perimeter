import Tests.LocalAlignment.DocumentaryRecoveryData
import Tests.LocalAlignment.DocumentaryAssembledCases

/-! Recovery uses the received documentary root and an actually executed
prefix. The raw forbidden task remains executable and fails its criterion.
The assembled checkpoint still receives its typed master payload. -/
set_option genInjectivity false
set_option maxHeartbeats 3000000
namespace ConstitutiveSearch.Agent.Local.Documentary.RecoveryDataCases
open Resources Program Snapshot

def initialPacket := RecoveryData.prepare MemoryCases.boot

def initialValid : RecoveryData.Valid initialPacket.transition.next :=
  RecoveryData.preserves initialPacket MemoryCases.bootValid

theorem initial_progress : RecoveryData.rank initialPacket.transition.next < RecoveryData.rank MemoryCases.boot :=
  RecoveryData.decreases initialPacket (by decide)

def initialRecovery := RecoveryData.recover MemoryCases.boot

def initialComplete : Complete initialRecovery.1.frame :=
  RecoveryData.recover_complete MemoryCases.boot initialRecovery MemoryCases.bootValid

theorem initial_attempts : initialRecovery.2.attempts = 5 :=
  RecoveryData.recover_attempts MemoryCases.boot

def prefixRecovery := RecoveryData.recover MemoryCases.retainedPrefix

def prefixComplete : Complete prefixRecovery.1.frame :=
  RecoveryData.recover_complete MemoryCases.retainedPrefix prefixRecovery MemoryCases.prefixValid

theorem prefix_attempts : prefixRecovery.2.attempts = 2 :=
  RecoveryData.recover_attempts MemoryCases.retainedPrefix

theorem prefix_round : prefixRecovery.1.round = 5 :=
  RecoveryData.recover_rounds MemoryCases.retainedPrefix

def terminal : Realized prefixRecovery.1.frame (.here : Ref _ ProgramCases.sumSpec) := prefixComplete .here

theorem terminal_value : prefixRecovery.1.frame.store.2.resources.read terminal.occurrence.2 = 2 := terminal.meets.1

theorem terminal_origins : terminal.occurrence.1.origins = [1, 2, 1, 2] := terminal.meets.2.2

theorem reset_then_packet :
    (RecoveryData.prepare (MemoryCases.retainedPrefix.reset (AdaptiveCases.policy 4))).transition.next =
      (RecoveryData.prepare MemoryCases.retainedPrefix).transition.next.reset (AdaptiveCases.policy 4) :=
  RecoveryData.reset_commutes MemoryCases.retainedPrefix (AdaptiveCases.policy 4)

theorem forgotten_same_recovery :
    HEq (RecoveryData.recover (Memory.project MemoryCases.leftProduced.1))
      (RecoveryData.recover (Memory.project MemoryCases.rightProduced.1)) := by
  cases MemoryCases.same_retained_present
  rfl

theorem control_loaded_recovery
    (after : PresentData Cases.sources Cases.contract DeductionCases.policy Nat
      [ProgramCases.sumSpec, ProgramCases.baselineSpec, ProgramCases.deltaSpec,
       ProgramCases.revisedSpec, ProgramCases.baselineSpec])
    (loaded : PortableControl.loadPresent ControlCodec.natural
      MemoryCases.retainedPrefix.session.frame.dossier MemoryCases.retainedPrefix.session.frame.store _
      (PortableControl.save ControlCodec.natural (PortableControl.capture MemoryCases.retainedPrefix)) = some after) :
    HEq (RecoveryData.recover after) prefixRecovery :=
  RecoveryData.loaded_recover ControlCodec.natural MemoryCases.retainedPrefix after loaded

theorem assembled_loaded_recovery
    (after : PresentData Cases.sources Cases.contract DeductionCases.policy Nat
      [ProgramCases.sumSpec, ProgramCases.baselineSpec, ProgramCases.deltaSpec,
       ProgramCases.revisedSpec, ProgramCases.baselineSpec])
    (loaded : AssembledCheckpoint.restore Cases.sources Cases.contract DeductionCases.policy
      ControlCodec.natural _ AssembledCases.boot = some after) :
    HEq (RecoveryData.recover after) initialRecovery := by
  have same := Option.some.inj (AssembledCases.boot_restored.symm.trans loaded)
  cases same
  rfl

def blockedBoot : PresentData Cases.sources Cases.contract DeductionCases.policy Nat
    [ProgramCases.baselineSpec, ProgramCases.sumSpec, .conclusion DeductionCases.forbiddenDemand,
      ProgramCases.revisedSpec, ProgramCases.baselineSpec] :=
  Snapshot.present ⟨[], AdaptiveCases.start, ProgramCases.blockedScript⟩

def blockedRecovery := RecoveryData.recover blockedBoot

theorem blocked_stays_incompatible : Complete blockedRecovery.1.frame → False :=
  Program.forbidden_rule_incompatible blockedRecovery.1.frame (.prior (.prior .here)) 2 rfl rfl

theorem blocked_no_success : Program.succeeded blockedRecovery.1.frame = false := rfl

theorem blocked_attempts : blockedRecovery.2.attempts = 5 := RecoveryData.recover_attempts blockedBoot

def report : Nat × Nat × Nat × Int × List Nat × Bool × Nat :=
  (initialRecovery.2.attempts, prefixRecovery.2.attempts, prefixRecovery.1.round,
    prefixRecovery.1.frame.store.2.resources.read terminal.occurrence.2,
    terminal.occurrence.1.origins, Program.succeeded blockedRecovery.1.frame, blockedRecovery.2.attempts)

end ConstitutiveSearch.Agent.Local.Documentary.RecoveryDataCases

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Agent.Local.Documentary.RecoveryDataCases.initialPacket
#print axioms ConstitutiveSearch.Agent.Local.Documentary.RecoveryDataCases.initialValid
#print axioms ConstitutiveSearch.Agent.Local.Documentary.RecoveryDataCases.initial_progress
#print axioms ConstitutiveSearch.Agent.Local.Documentary.RecoveryDataCases.initialRecovery
#print axioms ConstitutiveSearch.Agent.Local.Documentary.RecoveryDataCases.initialComplete
#print axioms ConstitutiveSearch.Agent.Local.Documentary.RecoveryDataCases.initial_attempts
#print axioms ConstitutiveSearch.Agent.Local.Documentary.RecoveryDataCases.prefixRecovery
#print axioms ConstitutiveSearch.Agent.Local.Documentary.RecoveryDataCases.prefixComplete
#print axioms ConstitutiveSearch.Agent.Local.Documentary.RecoveryDataCases.prefix_attempts
#print axioms ConstitutiveSearch.Agent.Local.Documentary.RecoveryDataCases.prefix_round
#print axioms ConstitutiveSearch.Agent.Local.Documentary.RecoveryDataCases.terminal
#print axioms ConstitutiveSearch.Agent.Local.Documentary.RecoveryDataCases.terminal_value
#print axioms ConstitutiveSearch.Agent.Local.Documentary.RecoveryDataCases.terminal_origins
#print axioms ConstitutiveSearch.Agent.Local.Documentary.RecoveryDataCases.reset_then_packet
#print axioms ConstitutiveSearch.Agent.Local.Documentary.RecoveryDataCases.forgotten_same_recovery
#print axioms ConstitutiveSearch.Agent.Local.Documentary.RecoveryDataCases.control_loaded_recovery
#print axioms ConstitutiveSearch.Agent.Local.Documentary.RecoveryDataCases.assembled_loaded_recovery
#print axioms ConstitutiveSearch.Agent.Local.Documentary.RecoveryDataCases.blockedBoot
#print axioms ConstitutiveSearch.Agent.Local.Documentary.RecoveryDataCases.blockedRecovery
#print axioms ConstitutiveSearch.Agent.Local.Documentary.RecoveryDataCases.blocked_stays_incompatible
#print axioms ConstitutiveSearch.Agent.Local.Documentary.RecoveryDataCases.blocked_no_success
#print axioms ConstitutiveSearch.Agent.Local.Documentary.RecoveryDataCases.blocked_attempts
#print axioms ConstitutiveSearch.Agent.Local.Documentary.RecoveryDataCases.report
/- AXIOM_AUDIT_END -/
