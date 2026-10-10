import Tests.LocalAlignment.DocumentaryAdaptive
import Tests.LocalAlignment.DocumentaryProgramCases

/-! Closed adaptive continuations. Policies are constructed development inputs;
the completion witnesses consume the stored execution, including diversions. -/
set_option genInjectivity false
set_option maxHeartbeats 600000
namespace ConstitutiveSearch.Agent.Local.Documentary.AdaptiveCases
open Resources Program Adaptive

def proposalFor (mode : Nat) (view : Observation) : Option Proposal :=
  if mode == 0 then none
  else if mode == 1 then some .current
  else if mode == 2 then some (.inspect 0)
  else if mode == 3 then some (.quote 99 99)
  else if mode == 4 then match view.goal with
    | .quotation _ => some (.quote 0 0)
    | .conclusion _ => if view.round == 2 then some (.deduce 2 1 0) else some (.deduce 0 1 1)
  else if mode == 5 then match view.goal with
    | .quotation _ => some .reverseSources
    | .conclusion _ => some .current
  else if mode == 6 then match view.goal with
    | .quotation _ => some .current
    | .conclusion _ => if view.round == 2 then some (.deduce 0 0 1) else some .current
  else if view.round == 0 then some (.quote 0 1)
  else if view.round == 1 then some (.quote 1 2)
  else if view.round == 2 then some (.deduce 0 1 0)
  else if view.round == 3 then some (.quote 0 1)
  else some (.deduce 1 1 1)

def policy (mode : Nat) : Adaptive.Policy Nat :=
  ⟨fun context _ view => ⟨context + 1, proposalFor mode view⟩, fun _ => 0⟩

def feed (forget : Bool) (_round : Nat) : Signal := ⟨"received task", forget⟩

def start : Session Cases.sources Cases.contract DeductionCases.policy Nat [] :=
  ⟨ProgramCases.start, 0, 0, none⟩

def silent := Adaptive.run (policy 0) (feed false) start ProgramCases.script
def repeatedRead := Adaptive.run (policy 2) (feed true) start ProgramCases.script
def hostile := Adaptive.run (policy 4) (feed true) start ProgramCases.script
def wrongOrder := Adaptive.run (policy 6) (feed false) start ProgramCases.script
def exact := Adaptive.run (policy 7) (feed false) start ProgramCases.script

def silentComplete : Complete silent.1.frame :=
  silent.2.complete ProgramCases.admissible ProgramCases.initiallyComplete
def repeatedComplete : Complete repeatedRead.1.frame :=
  repeatedRead.2.complete ProgramCases.admissible ProgramCases.initiallyComplete
def hostileComplete : Complete hostile.1.frame :=
  hostile.2.complete ProgramCases.admissible ProgramCases.initiallyComplete
def wrongOrderComplete : Complete wrongOrder.1.frame :=
  wrongOrder.2.complete ProgramCases.admissible ProgramCases.initiallyComplete

def terminal : Realized hostile.1.frame (.here : Ref _ ProgramCases.sumSpec) := hostileComplete .here
theorem terminal_value : hostile.1.frame.store.2.resources.read terminal.occurrence.2 = 2 := terminal.meets.1
theorem terminal_origins : terminal.occurrence.1.origins = [1, 2, 1, 2] := terminal.meets.2.2
theorem terminal_sources :
    (hostile.1.frame.store.2.valid terminal.occurrence.2).sources.map (fun output => output.item.position) = [1, 2, 1, 2] :=
  (Deduction.Justified.origins_exact (hostile.1.frame.store.2.valid terminal.occurrence.2)).trans terminal_origins

theorem every_policy_finishes (proposer : Adaptive.Policy Nat) (signals : Nat → Signal) :
    Nonempty (Complete (Adaptive.run proposer signals start ProgramCases.script).1.frame) :=
  all_policies_accomplish proposer signals start ProgramCases.script ProgramCases.admissible ProgramCases.initiallyComplete
theorem hostile_five_turns : hostile.1.round = 5 := hostile.2.rounds
theorem hostile_action_bound : hostile.2.attempts ≤ 10 := hostile.2.bound
theorem repeated_five_turns : repeatedRead.1.round = 5 := repeatedRead.2.rounds






def firstReady : Program.Admissible Cases.sources Cases.contract ProgramCases.firstPart :=
  .cons ProgramCases.baselineReady (.cons ProgramCases.revisedReady (.cons ProgramCases.differenceCompatible .done))
def lastReady : Program.Admissible Cases.sources Cases.contract ProgramCases.lastPart :=
  .cons ProgramCases.baselineReady (.cons ProgramCases.sumCompatible .done)
def prefixRun := Adaptive.run (policy 4) (feed true) start ProgramCases.firstPart
def prefixComplete : Complete prefixRun.1.frame := prefixRun.2.complete firstReady ProgramCases.initiallyComplete
def present : Present Cases.sources Cases.contract DeductionCases.policy Nat
    [ProgramCases.sumSpec, ProgramCases.baselineSpec, ProgramCases.deltaSpec,
     ProgramCases.revisedSpec, ProgramCases.baselineSpec] :=
  ⟨[ProgramCases.deltaSpec, ProgramCases.revisedSpec, ProgramCases.baselineSpec],
    prefixRun.1, ProgramCases.lastPart⟩
def resumed := Adaptive.run (policy 4) (feed true) prefixRun.1 ProgramCases.lastPart
def resetResumed := Adaptive.run (policy 4) (feed true) (resetContext (policy 4) prefixRun.1) ProgramCases.lastPart
def resumedComplete : Complete resumed.1.frame := resumed.2.complete lastReady prefixComplete
def resetResumedComplete : Complete resetResumed.1.frame := resetResumed.2.complete lastReady prefixComplete
theorem resume_same_actual_session : hostile.1 = resumed.1 := run_append (policy 4) (feed true) start ProgramCases.firstPart ProgramCases.lastPart
theorem reset_keeps_queue : (present.reset (policy 4)).remaining.length = present.remaining.length := present.reset_keeps_remaining (policy 4)
theorem reset_keeps_actual_frame : (present.reset (policy 4)).session.frame = prefixRun.1.frame := rfl
theorem reset_keeps_actual_clock : (present.reset (policy 4)).session.round = 3 := prefixRun.2.rounds
theorem resumed_preserves_delta :
    resumed.1.frame.bindings (ProgramCases.lastPart.previous (.here : Ref _ ProgramCases.deltaSpec)) =
      (prefixRun.1.frame.bindings .here).map (transport prefixRun.1.frame.store.2 resumed.1.frame.store.2 resumed.2.extension) :=
  resumed.2.bindings .here

def blocked := Adaptive.run (policy 0) (feed true) start ProgramCases.blockedScript
theorem blocked_stays_incompatible : Complete blocked.1.frame → False :=
  forbidden_rule_incompatible blocked.1.frame (.prior (.prior .here)) 2 rfl rfl

/-- Separate received fixture with two equally valued, permitted versions. -/
def twoVersions : Support SourceValue Cases.context :=
  .given (⟨7, 42, "Private"⟩, ⟨7, 42, "Version one"⟩, ⟨7, 42, "Version two"⟩, PUnit.unit)
def choiceTask : Dossier.Obligation Cases.context := ⟨⟨7, 42, none⟩, Cases.publicOrigin, Cases.updatedOrigin⟩
def choiceScript : Script Cases.context DeductionCases.policy [] [.quotation choiceTask.demand] :=
  .cons (.quotation choiceTask) .done
def choiceStart : Session twoVersions Cases.contract DeductionCases.policy Nat [] :=
  ⟨⟨⟨ProgramCases.start.dossier.cursor, Documentary.empty twoVersions Cases.contract⟩,
    ⟨[], Deduction.empty twoVersions Cases.contract DeductionCases.policy⟩, fun ref => nomatch ref⟩, 0, 0, none⟩
def choiceReady : Program.Admissible twoVersions Cases.contract choiceScript := .cons (.left .here ⟨rfl, rfl, True.intro⟩) .done
def choiceNormal := Adaptive.run (policy 1) (feed false) choiceStart choiceScript
def choiceReversed := Adaptive.run (policy 5) (feed true) choiceStart choiceScript
def choiceNormalComplete : Complete choiceNormal.1.frame := choiceNormal.2.complete choiceReady (fun ref => nomatch ref)
def choiceReversedComplete : Complete choiceReversed.1.frame := choiceReversed.2.complete choiceReady (fun ref => nomatch ref)

def actualDocument : List UInt8 := DossierCases.render hostile.1.frame.dossier.memory.items.reverse ++
  DeductionCases.renderConclusion "variation + variation" hostile.1.frame.store.2 terminal.occurrence.2

end ConstitutiveSearch.Agent.Local.Documentary.AdaptiveCases
/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Agent.Local.Documentary.AdaptiveCases.proposalFor
#print axioms ConstitutiveSearch.Agent.Local.Documentary.AdaptiveCases.policy
#print axioms ConstitutiveSearch.Agent.Local.Documentary.AdaptiveCases.feed
#print axioms ConstitutiveSearch.Agent.Local.Documentary.AdaptiveCases.start
#print axioms ConstitutiveSearch.Agent.Local.Documentary.AdaptiveCases.silent
#print axioms ConstitutiveSearch.Agent.Local.Documentary.AdaptiveCases.repeatedRead
#print axioms ConstitutiveSearch.Agent.Local.Documentary.AdaptiveCases.hostile
#print axioms ConstitutiveSearch.Agent.Local.Documentary.AdaptiveCases.wrongOrder
#print axioms ConstitutiveSearch.Agent.Local.Documentary.AdaptiveCases.exact
#print axioms ConstitutiveSearch.Agent.Local.Documentary.AdaptiveCases.silentComplete
#print axioms ConstitutiveSearch.Agent.Local.Documentary.AdaptiveCases.repeatedComplete
#print axioms ConstitutiveSearch.Agent.Local.Documentary.AdaptiveCases.hostileComplete
#print axioms ConstitutiveSearch.Agent.Local.Documentary.AdaptiveCases.wrongOrderComplete
#print axioms ConstitutiveSearch.Agent.Local.Documentary.AdaptiveCases.terminal
#print axioms ConstitutiveSearch.Agent.Local.Documentary.AdaptiveCases.terminal_value
#print axioms ConstitutiveSearch.Agent.Local.Documentary.AdaptiveCases.terminal_origins
#print axioms ConstitutiveSearch.Agent.Local.Documentary.AdaptiveCases.terminal_sources
#print axioms ConstitutiveSearch.Agent.Local.Documentary.AdaptiveCases.every_policy_finishes
#print axioms ConstitutiveSearch.Agent.Local.Documentary.AdaptiveCases.hostile_five_turns
#print axioms ConstitutiveSearch.Agent.Local.Documentary.AdaptiveCases.hostile_action_bound
#print axioms ConstitutiveSearch.Agent.Local.Documentary.AdaptiveCases.repeated_five_turns
#print axioms ConstitutiveSearch.Agent.Local.Documentary.AdaptiveCases.firstReady
#print axioms ConstitutiveSearch.Agent.Local.Documentary.AdaptiveCases.lastReady
#print axioms ConstitutiveSearch.Agent.Local.Documentary.AdaptiveCases.prefixRun
#print axioms ConstitutiveSearch.Agent.Local.Documentary.AdaptiveCases.prefixComplete
#print axioms ConstitutiveSearch.Agent.Local.Documentary.AdaptiveCases.present
#print axioms ConstitutiveSearch.Agent.Local.Documentary.AdaptiveCases.resumed
#print axioms ConstitutiveSearch.Agent.Local.Documentary.AdaptiveCases.resetResumed
#print axioms ConstitutiveSearch.Agent.Local.Documentary.AdaptiveCases.resumedComplete
#print axioms ConstitutiveSearch.Agent.Local.Documentary.AdaptiveCases.resetResumedComplete
#print axioms ConstitutiveSearch.Agent.Local.Documentary.AdaptiveCases.resume_same_actual_session
#print axioms ConstitutiveSearch.Agent.Local.Documentary.AdaptiveCases.reset_keeps_queue
#print axioms ConstitutiveSearch.Agent.Local.Documentary.AdaptiveCases.reset_keeps_actual_frame
#print axioms ConstitutiveSearch.Agent.Local.Documentary.AdaptiveCases.reset_keeps_actual_clock
#print axioms ConstitutiveSearch.Agent.Local.Documentary.AdaptiveCases.resumed_preserves_delta
#print axioms ConstitutiveSearch.Agent.Local.Documentary.AdaptiveCases.blocked
#print axioms ConstitutiveSearch.Agent.Local.Documentary.AdaptiveCases.blocked_stays_incompatible
#print axioms ConstitutiveSearch.Agent.Local.Documentary.AdaptiveCases.twoVersions
#print axioms ConstitutiveSearch.Agent.Local.Documentary.AdaptiveCases.choiceTask
#print axioms ConstitutiveSearch.Agent.Local.Documentary.AdaptiveCases.choiceScript
#print axioms ConstitutiveSearch.Agent.Local.Documentary.AdaptiveCases.choiceStart
#print axioms ConstitutiveSearch.Agent.Local.Documentary.AdaptiveCases.choiceReady
#print axioms ConstitutiveSearch.Agent.Local.Documentary.AdaptiveCases.choiceNormal
#print axioms ConstitutiveSearch.Agent.Local.Documentary.AdaptiveCases.choiceReversed
#print axioms ConstitutiveSearch.Agent.Local.Documentary.AdaptiveCases.choiceNormalComplete
#print axioms ConstitutiveSearch.Agent.Local.Documentary.AdaptiveCases.choiceReversedComplete
#print axioms ConstitutiveSearch.Agent.Local.Documentary.AdaptiveCases.actualDocument
/- AXIOM_AUDIT_END -/
