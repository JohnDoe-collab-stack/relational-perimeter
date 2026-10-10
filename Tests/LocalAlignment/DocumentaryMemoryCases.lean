import Tests.LocalAlignment.DocumentaryMemory
import Tests.LocalAlignment.DocumentaryAdaptiveCases

/-! Closed documentary memory cases. Distinct archived proposals were actually
received and executed from the same boot. No arbitrary erased flag is introduced.
Checkpoints below are typed values, not filesystem or process-restart effects. -/
set_option genInjectivity false
set_option maxHeartbeats 2000000
namespace ConstitutiveSearch.Agent.Local.Documentary.MemoryCases
open Resources Program Adaptive Snapshot Memory

def boot : PresentData Cases.sources Cases.contract DeductionCases.policy Nat
    [ProgramCases.sumSpec, ProgramCases.baselineSpec, ProgramCases.deltaSpec,
     ProgramCases.revisedSpec, ProgramCases.baselineSpec] :=
  Snapshot.present ⟨[], AdaptiveCases.start, ProgramCases.script⟩

def bootValid : Accomplishable boot := ⟨complete_forward ProgramCases.start ProgramCases.initiallyComplete, ProgramCases.admissible⟩

def richBoot : Source Cases.sources Cases.contract DeductionCases.policy Nat
    [ProgramCases.sumSpec, ProgramCases.baselineSpec, ProgramCases.deltaSpec,
     ProgramCases.revisedSpec, ProgramCases.baselineSpec] := ⟨boot, []⟩

def invalidPolicy (index : Nat) : Adaptive.Policy Nat :=
  ⟨fun context _ _ => ⟨context + 1, some (.quote index index)⟩, fun _ => 0⟩

def leftProduced := sourceStep richBoot (.progress (invalidPolicy 98) (AdaptiveCases.feed false 0))
def rightProduced := sourceStep richBoot (.progress (invalidPolicy 99) (AdaptiveCases.feed false 0))

def archivedProposal {context sources contract rules Context final}
    (source : @Source context sources contract rules Context final) : Option Proposal :=
  match source.archive with
  | [] => none
  | received :: _ => received.proposal

theorem left_received : archivedProposal leftProduced.1 = some (.quote 98 98) := rfl
theorem right_received : archivedProposal rightProduced.1 = some (.quote 99 99) := rfl
theorem same_retained_present : project leftProduced.1 = project rightProduced.1 := rfl

theorem archived_distinction : archivedProposal leftProduced.1 = archivedProposal rightProduced.1 → False := by
  intro same
  have impossible : true = false := congrArg (fun proposal => match proposal with
    | none => false
    | some .current => false
    | some .reverseSources => false
    | some (.inspect _) => false
    | some (.quote left _) => left == 98
    | some (.deduce _ _ _) => false) same
  exact Bool.noConfusion impossible

theorem cannot_recover (recover : PresentData Cases.sources Cases.contract DeductionCases.policy Nat
    [ProgramCases.sumSpec, ProgramCases.baselineSpec, ProgramCases.deltaSpec,
     ProgramCases.revisedSpec, ProgramCases.baselineSpec] → Option Proposal)
    (left : recover (project leftProduced.1) = archivedProposal leftProduced.1)
    (right : recover (project rightProduced.1) = archivedProposal rightProduced.1) : False :=
  archived_distinction (left.symm.trans ((congrArg recover same_retained_present).trans right))

theorem cannot_recover_after_any_future (requests : List (Memory.Request Nat))
    (recover : PresentData Cases.sources Cases.contract DeductionCases.policy Nat
      [ProgramCases.sumSpec, ProgramCases.baselineSpec, ProgramCases.deltaSpec,
       ProgramCases.revisedSpec, ProgramCases.baselineSpec] → Option Proposal)
    (left : recover (project (sourceRun leftProduced.1 requests).1) = archivedProposal leftProduced.1)
    (right : recover (project (sourceRun rightProduced.1 requests).1) = archivedProposal rightProduced.1) : False :=
  archived_distinction (left.symm.trans ((congrArg recover
    (indistinguishable_futures leftProduced.1 rightProduced.1 same_retained_present requests).1).trans right))

def retainedPrefix : PresentData Cases.sources Cases.contract DeductionCases.policy Nat
    [ProgramCases.sumSpec, ProgramCases.baselineSpec, ProgramCases.deltaSpec,
     ProgramCases.revisedSpec, ProgramCases.baselineSpec] := Snapshot.present AdaptiveCases.present

def prefixValid : Accomplishable retainedPrefix :=
  ⟨complete_forward AdaptiveCases.prefixRun.1.frame AdaptiveCases.prefixComplete, AdaptiveCases.lastReady⟩

def checkpoint := Snapshot.save retainedPrefix
def loaded := checkpoint.payload

theorem loaded_actual_present : Snapshot.load checkpoint = some loaded := rfl
theorem loaded_clock : loaded.session.round = 3 := AdaptiveCases.prefixRun.2.rounds
theorem loaded_remaining : loaded.remaining.length = 2 := rfl
def retainedDelta := prefixValid.initial (.here : Ref _ ProgramCases.deltaSpec)
theorem loaded_delta_value : loaded.session.frame.store.2.resources.read retainedDelta.occurrence.2 = 1 := retainedDelta.meets.1
theorem loaded_delta_origins : retainedDelta.occurrence.1.origins = [1, 2] := retainedDelta.meets.2.2
theorem bad_version_rejected : Snapshot.load { checkpoint with version := 2 } = none := rfl

def resumed := Memory.finish loaded (AdaptiveCases.policy 4) (AdaptiveCases.feed true)
def resumedComplete : Complete resumed.1.frame := Memory.finish_complete (data := loaded) resumed prefixValid
def terminal := resumedComplete (.here : Ref _ ProgramCases.sumSpec)
theorem resumed_value : resumed.1.frame.store.2.resources.read terminal.occurrence.2 = 2 := terminal.meets.1
theorem resumed_origins : terminal.occurrence.1.origins = [1, 2, 1, 2] := terminal.meets.2.2
theorem resumed_clock : resumed.1.round = 5 := Memory.finish_rounds (data := loaded) resumed
theorem resumed_bound : resumed.2.attempts ≤ 4 := Memory.finish_bound (data := loaded) resumed

def futures : List (Memory.Request Nat) :=
  [.inspect 0, .status, .reset (AdaptiveCases.policy 4),
    .progress (AdaptiveCases.policy 4) (AdaptiveCases.feed true 3), .inspect 1,
    .progress (AdaptiveCases.policy 4) (AdaptiveCases.feed true 4), .inspect 0,
    .inspect 99, .status, .progress (AdaptiveCases.policy 4) (AdaptiveCases.feed true 5)]

def continued := Memory.run loaded futures
def continuedValid : Accomplishable continued.1 := continued.2.progress prefixValid
theorem continued_done : continued.1.remaining.length = 0 := rfl
theorem denied_read : (Memory.accepted continued.1 (.inspect 99)).isSome = false := rfl

def versionOne : PresentData AdaptiveCases.twoVersions Cases.contract DeductionCases.policy Nat
    [.quotation AdaptiveCases.choiceTask.demand] :=
  Snapshot.present ⟨_, AdaptiveCases.choiceReversed.1, .done⟩
def versionTwo : PresentData AdaptiveCases.twoVersions Cases.contract DeductionCases.policy Nat
    [.quotation AdaptiveCases.choiceTask.demand] :=
  Snapshot.present ⟨_, AdaptiveCases.choiceNormal.1, .done⟩
theorem version_one_read : Memory.read versionOne 0 = some ⟨0, 42, [1]⟩ := rfl
theorem version_two_read : Memory.read versionTwo 0 = some ⟨0, 42, [2]⟩ := rfl
theorem origins_separate : Memory.read versionOne 0 = Memory.read versionTwo 0 → False := by
  intro same
  have impossible : true = false := congrArg (fun result => match result with
    | some found => found.origins == [1]
    | none => false) same
  exact Bool.noConfusion impossible

def finalData : PresentData Cases.sources Cases.contract DeductionCases.policy Nat
    [ProgramCases.sumSpec, ProgramCases.baselineSpec, ProgramCases.deltaSpec,
     ProgramCases.revisedSpec, ProgramCases.baselineSpec] := Snapshot.present ⟨_, resumed.1, .done⟩
theorem remaining_separates : retainedPrefix.remaining.length = finalData.remaining.length → False := by
  intro same
  have impossible : false = true := congrArg (fun n => n == 0) same
  exact Bool.noConfusion impossible

theorem reset_preserves_delta : Memory.read (loaded.reset (AdaptiveCases.policy 4)) 0 = Memory.read loaded 0 := rfl
theorem reset_preserves_clock : (loaded.reset (AdaptiveCases.policy 4)).session.round = loaded.session.round := rfl
theorem reset_changes_context : (loaded.reset (AdaptiveCases.policy 4)).session.context = 0 ∧ loaded.session.context = 1 := ⟨rfl, rfl⟩

def contextPolicy : Adaptive.Policy Nat :=
  ⟨fun context _ _ => ⟨context + 1, if context == 0 then none else some .current⟩, fun _ => 0⟩

def contextTurn := Memory.step loaded (.progress contextPolicy (AdaptiveCases.feed false 3))
def resetContextTurn := Memory.step (loaded.reset contextPolicy) (.progress contextPolicy (AdaptiveCases.feed false 3))
theorem context_proposal : contextTurn.interaction.map (fun received => received.proposal) = some (some .current) := rfl
theorem reset_context_proposal : resetContextTurn.interaction.map (fun received => received.proposal) = some none := rfl

def clockRead : Memory.Event → Option Nat
  | .produced _ => none
  | .inspected _ => none
  | .observed clock _ _ _ _ _ => some clock
  | .reset => none
  | .finished => none

theorem retained_clock_separates : clockRead (Memory.step loaded .status).event = some 3 ∧
    clockRead (Memory.step finalData .status).event = some 5 :=
  ⟨congrArg some loaded_clock, congrArg some resumed_clock⟩

def blockedRetained : PresentData Cases.sources Cases.contract DeductionCases.policy Nat
    [ProgramCases.baselineSpec, ProgramCases.sumSpec, .conclusion DeductionCases.forbiddenDemand,
      ProgramCases.revisedSpec, ProgramCases.baselineSpec] :=
  Snapshot.present ⟨_, AdaptiveCases.blocked.1, .done⟩

theorem blocked_after_projection : Complete blockedRetained.session.frame.restore → False :=
  fun retained => AdaptiveCases.blocked_stays_incompatible (complete_backward AdaptiveCases.blocked.1.frame retained)

end ConstitutiveSearch.Agent.Local.Documentary.MemoryCases
/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Agent.Local.Documentary.MemoryCases.boot
#print axioms ConstitutiveSearch.Agent.Local.Documentary.MemoryCases.bootValid
#print axioms ConstitutiveSearch.Agent.Local.Documentary.MemoryCases.richBoot
#print axioms ConstitutiveSearch.Agent.Local.Documentary.MemoryCases.invalidPolicy
#print axioms ConstitutiveSearch.Agent.Local.Documentary.MemoryCases.leftProduced
#print axioms ConstitutiveSearch.Agent.Local.Documentary.MemoryCases.rightProduced
#print axioms ConstitutiveSearch.Agent.Local.Documentary.MemoryCases.archivedProposal
#print axioms ConstitutiveSearch.Agent.Local.Documentary.MemoryCases.left_received
#print axioms ConstitutiveSearch.Agent.Local.Documentary.MemoryCases.right_received
#print axioms ConstitutiveSearch.Agent.Local.Documentary.MemoryCases.same_retained_present
#print axioms ConstitutiveSearch.Agent.Local.Documentary.MemoryCases.archived_distinction
#print axioms ConstitutiveSearch.Agent.Local.Documentary.MemoryCases.cannot_recover
#print axioms ConstitutiveSearch.Agent.Local.Documentary.MemoryCases.cannot_recover_after_any_future
#print axioms ConstitutiveSearch.Agent.Local.Documentary.MemoryCases.retainedPrefix
#print axioms ConstitutiveSearch.Agent.Local.Documentary.MemoryCases.prefixValid
#print axioms ConstitutiveSearch.Agent.Local.Documentary.MemoryCases.checkpoint
#print axioms ConstitutiveSearch.Agent.Local.Documentary.MemoryCases.loaded
#print axioms ConstitutiveSearch.Agent.Local.Documentary.MemoryCases.loaded_actual_present
#print axioms ConstitutiveSearch.Agent.Local.Documentary.MemoryCases.loaded_clock
#print axioms ConstitutiveSearch.Agent.Local.Documentary.MemoryCases.loaded_remaining
#print axioms ConstitutiveSearch.Agent.Local.Documentary.MemoryCases.retainedDelta
#print axioms ConstitutiveSearch.Agent.Local.Documentary.MemoryCases.loaded_delta_value
#print axioms ConstitutiveSearch.Agent.Local.Documentary.MemoryCases.loaded_delta_origins
#print axioms ConstitutiveSearch.Agent.Local.Documentary.MemoryCases.bad_version_rejected
#print axioms ConstitutiveSearch.Agent.Local.Documentary.MemoryCases.resumed
#print axioms ConstitutiveSearch.Agent.Local.Documentary.MemoryCases.resumedComplete
#print axioms ConstitutiveSearch.Agent.Local.Documentary.MemoryCases.terminal
#print axioms ConstitutiveSearch.Agent.Local.Documentary.MemoryCases.resumed_value
#print axioms ConstitutiveSearch.Agent.Local.Documentary.MemoryCases.resumed_origins
#print axioms ConstitutiveSearch.Agent.Local.Documentary.MemoryCases.resumed_clock
#print axioms ConstitutiveSearch.Agent.Local.Documentary.MemoryCases.resumed_bound
#print axioms ConstitutiveSearch.Agent.Local.Documentary.MemoryCases.futures
#print axioms ConstitutiveSearch.Agent.Local.Documentary.MemoryCases.continued
#print axioms ConstitutiveSearch.Agent.Local.Documentary.MemoryCases.continuedValid
#print axioms ConstitutiveSearch.Agent.Local.Documentary.MemoryCases.continued_done
#print axioms ConstitutiveSearch.Agent.Local.Documentary.MemoryCases.denied_read
#print axioms ConstitutiveSearch.Agent.Local.Documentary.MemoryCases.versionOne
#print axioms ConstitutiveSearch.Agent.Local.Documentary.MemoryCases.versionTwo
#print axioms ConstitutiveSearch.Agent.Local.Documentary.MemoryCases.version_one_read
#print axioms ConstitutiveSearch.Agent.Local.Documentary.MemoryCases.version_two_read
#print axioms ConstitutiveSearch.Agent.Local.Documentary.MemoryCases.origins_separate
#print axioms ConstitutiveSearch.Agent.Local.Documentary.MemoryCases.finalData
#print axioms ConstitutiveSearch.Agent.Local.Documentary.MemoryCases.remaining_separates
#print axioms ConstitutiveSearch.Agent.Local.Documentary.MemoryCases.reset_preserves_delta
#print axioms ConstitutiveSearch.Agent.Local.Documentary.MemoryCases.reset_preserves_clock
#print axioms ConstitutiveSearch.Agent.Local.Documentary.MemoryCases.reset_changes_context
#print axioms ConstitutiveSearch.Agent.Local.Documentary.MemoryCases.contextPolicy
#print axioms ConstitutiveSearch.Agent.Local.Documentary.MemoryCases.contextTurn
#print axioms ConstitutiveSearch.Agent.Local.Documentary.MemoryCases.resetContextTurn
#print axioms ConstitutiveSearch.Agent.Local.Documentary.MemoryCases.context_proposal
#print axioms ConstitutiveSearch.Agent.Local.Documentary.MemoryCases.reset_context_proposal
#print axioms ConstitutiveSearch.Agent.Local.Documentary.MemoryCases.clockRead
#print axioms ConstitutiveSearch.Agent.Local.Documentary.MemoryCases.retained_clock_separates
#print axioms ConstitutiveSearch.Agent.Local.Documentary.MemoryCases.blockedRetained
#print axioms ConstitutiveSearch.Agent.Local.Documentary.MemoryCases.blocked_after_projection
/- AXIOM_AUDIT_END -/
