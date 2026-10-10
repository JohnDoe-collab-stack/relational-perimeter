import Tests.LocalAlignment.DocumentaryProgram
import Tests.LocalAlignment.DocumentaryDeductionCases

/-! Closed interleaved programs over the received sources and unchanged contracts.
These are constructed development cases, not a new local-model experiment. -/
set_option genInjectivity false
set_option maxHeartbeats 600000
namespace ConstitutiveSearch.Agent.Local.Documentary.ProgramCases
open Resources Program

def baselineTask : Dossier.Obligation Cases.context :=
  ⟨⟨7, 42, some 1⟩, Cases.privateOrigin, Cases.publicOrigin⟩
def revisedTask : Dossier.Obligation Cases.context :=
  ⟨⟨7, 43, some 2⟩, Cases.publicOrigin, Cases.updatedOrigin⟩
def baselineSpec : Specification := .quotation baselineTask.demand
def revisedSpec : Specification := .quotation revisedTask.demand
def deltaSpec : Specification := .conclusion DeductionCases.deltaDemand
def sumSpec : Specification := .conclusion DeductionCases.sumDemand

def start : Frame Cases.sources Cases.contract DeductionCases.policy [] :=
  ⟨DossierCases.start, ⟨[], Deduction.empty Cases.sources Cases.contract DeductionCases.policy⟩,
    fun ref => nomatch ref⟩
def initiallyComplete : Complete start := fun ref => nomatch ref

def firstPart : Script Cases.context DeductionCases.policy [] [deltaSpec, revisedSpec, baselineSpec] :=
  .cons (.quotation baselineTask) (.cons (.quotation revisedTask)
    (.cons (.conclusion DeductionCases.differenceRequest (.prior .here) .here DeductionCases.deltaDemand) .done))
def lastPart : Script Cases.context DeductionCases.policy [deltaSpec, revisedSpec, baselineSpec]
    [sumSpec, baselineSpec, deltaSpec, revisedSpec, baselineSpec] :=
  .cons (.quotation baselineTask)
    (.cons (.conclusion DeductionCases.sumRequest (.prior .here) (.prior .here) DeductionCases.sumDemand) .done)
def script := firstPart.append lastPart
def actual := Program.execute start script

theorem quotation_value {demand kind value} (correct : Holds (.quotation demand) kind value) :
    value = Int.ofNat demand.value := by
  cases kind with
  | quotation item => exact correct.1.trans (congrArg Int.ofNat correct.2.2.1)
  | derived _ _ _ _ _ _ => exact False.elim correct

theorem quotation_origins {demand kind value} (correct : Holds (.quotation demand) kind value)
    (position : Nat) (pinned : demand.origin = some position) : kind.origins = [position] := by
  cases kind with
  | quotation item =>
      have same := correct.2.2.2
      rw [pinned] at same
      exact congrArg (fun p => [p]) same
  | derived _ _ _ _ _ _ => exact False.elim correct

def baselineReady : Dossier.PairAdmissible Cases.sources Cases.contract baselineTask :=
  .right .here ⟨rfl, rfl, rfl⟩
def revisedReady : Dossier.PairAdmissible Cases.sources Cases.contract revisedTask :=
  .right (.prior .here) ⟨rfl, rfl, rfl⟩

def differenceCompatible : Compatible DeductionCases.policy DeductionCases.differenceRequest
    baselineSpec revisedSpec DeductionCases.deltaDemand :=
  ⟨.here, fun left right lp rp lv rv leftMeets rightMeets =>
    ⟨by rw [quotation_value leftMeets, quotation_value rightMeets]; rfl,
      rfl, by
        change left.origins ++ right.origins = [1, 2]
        rw [quotation_origins leftMeets 1 rfl, quotation_origins rightMeets 2 rfl]
        rfl⟩⟩

def sumCompatible : Compatible DeductionCases.policy DeductionCases.sumRequest
    deltaSpec deltaSpec DeductionCases.sumDemand :=
  ⟨.prior .here, fun left right lp rp lv rv leftMeets rightMeets =>
    ⟨by rw [leftMeets.1, rightMeets.1]; rfl,
      rfl, by
        change left.origins ++ right.origins = [1, 2, 1, 2]
        rw [leftMeets.2.2, rightMeets.2.2]
        rfl⟩⟩

def admissible : Program.Admissible Cases.sources Cases.contract script :=
  .cons baselineReady (.cons revisedReady (.cons differenceCompatible
    (.cons baselineReady (.cons sumCompatible .done))))

/-- Consumes the stored actual trace, without executing the program again. -/
def actualComplete : Complete actual.1 := actual.2.complete admissible initiallyComplete
def sumRealized : Realized actual.1 (.here : Ref _ sumSpec) := actualComplete .here

theorem all_five_completed : Nonempty (Complete actual.1) := ⟨actualComplete⟩
theorem three_actual_master_heads : actual.1.dossier.cursor.depth = start.dossier.cursor.depth + 3 :=
  actual.2.depth
theorem five_events : actual.2.events.length = 5 := actual.2.length
theorem five_actual_occurrences : actual.1.store.1.length = 5 := rfl

theorem actual_sum : actual.1.store.2.resources.read sumRealized.occurrence.2 = 2 := sumRealized.meets.1
theorem actual_origins : sumRealized.occurrence.1.origins = [1, 2, 1, 2] := sumRealized.meets.2.2


theorem actual_source_origins :
    (actual.1.store.2.valid sumRealized.occurrence.2).sources.map (fun output => output.item.position) =
      [1, 2, 1, 2] :=
  (Deduction.Justified.origins_exact (actual.1.store.2.valid sumRealized.occurrence.2)).trans actual_origins

def prefixRun := Program.execute start firstPart
def resumed := Program.execute prefixRun.1 lastPart
theorem resume_same_actual_frame : actual.1 = resumed.1 := execute_append start firstPart lastPart

def baselineBinding := actual.1.bindings (.prior (.prior (.prior (.prior .here))))
def repeatedBinding := actual.1.bindings (.prior .here)
def bindingPosition {context sources contract policy} (store : @Deduction.Store context sources contract policy) :
    Option (Occurrence store) → Option Nat
  | none => none
  | some occurrence => some occurrence.2.position
def bindingValue {context sources contract policy} (store : @Deduction.Store context sources contract policy) :
    Option (Occurrence store) → Option Int
  | none => none
  | some occurrence => some (store.2.resources.read occurrence.2)
theorem equal_values : bindingValue actual.1.store baselineBinding = bindingValue actual.1.store repeatedBinding := rfl
theorem distinct_occurrences : bindingPosition actual.1.store baselineBinding = some 4 ∧
    bindingPosition actual.1.store repeatedBinding = some 1 := ⟨rfl, rfl⟩

def wrongDemand : Deduction.Demand := ⟨99, some 0, some [1, 2]⟩
def wrongSpec : Specification := .conclusion wrongDemand
def downstreamDemand : Deduction.Demand := ⟨2, some 1, some [1, 2, 1, 2]⟩
def wrongScript : Script Cases.context DeductionCases.policy []
    [.conclusion downstreamDemand, wrongSpec, revisedSpec, baselineSpec] :=
  .cons (.quotation baselineTask) (.cons (.quotation revisedTask)
    (.cons (.conclusion DeductionCases.differenceRequest (.prior .here) .here wrongDemand)
      (.cons (.conclusion DeductionCases.sumRequest .here .here downstreamDemand) .done)))
def wrongActual := Program.execute start wrongScript
theorem legal_wrong_output_retained : bindingValue wrongActual.1.store (wrongActual.1.bindings (.prior .here)) = some 1 := rfl
theorem dependent_reads_that_output : bindingValue wrongActual.1.store (wrongActual.1.bindings .here) = some 2 := rfl
theorem wrong_task_incomplete : succeeded wrongActual.1 = false := rfl

def blockedScript : Script Cases.context DeductionCases.policy []
    [baselineSpec, sumSpec, .conclusion DeductionCases.forbiddenDemand, revisedSpec, baselineSpec] :=
  .cons (.quotation baselineTask) (.cons (.quotation revisedTask)
    (.cons (.conclusion DeductionCases.duplicateRequest (.prior .here) .here DeductionCases.forbiddenDemand)
      (.cons (.conclusion DeductionCases.sumRequest .here .here DeductionCases.sumDemand)
        (.cons (.quotation baselineTask) .done))))
def blockedActual := Program.execute start blockedScript

theorem refused_has_no_binding : blockedActual.1.bindings (.prior (.prior .here)) = none := rfl
theorem missing_has_no_binding : blockedActual.1.bindings (.prior .here) = none := rfl
theorem independent_continuation : bindingValue blockedActual.1.store (blockedActual.1.bindings .here) = some 42 := rfl
theorem refused_has_no_occurrence : blockedActual.1.store.1.length = 3 := rfl
theorem forbidden_whole_goal_impossible : Complete blockedActual.1 → False :=
  Program.forbidden_rule_incompatible blockedActual.1 (.prior (.prior .here)) 2 rfl rfl

def sourceBlockedScript : Script Cases.context DeductionCases.policy []
    [baselineSpec, sumSpec, .quotation Cases.pinnedDemand] :=
  .cons (.quotation ⟨Cases.pinnedDemand, Cases.privateOrigin, Cases.publicOrigin⟩)
    (.cons (.conclusion DeductionCases.sumRequest .here .here DeductionCases.sumDemand)
      (.cons (.quotation baselineTask) .done))
def sourceBlockedActual := Program.execute start sourceBlockedScript
theorem forbidden_source_then_missing : sourceBlockedActual.2.events = [.refused, .missing, .quoted] := rfl
theorem source_blocked_incomplete : succeeded sourceBlockedActual.1 = false := rfl

def erased := Program.execute (start, "temporary proposal").1 script
theorem context_erasure_same_execution : erased = actual := rfl
def erasedBlocked := Program.execute (start, "").1 blockedScript
theorem context_erasure_same_refusal : erasedBlocked.2.events = blockedActual.2.events := rfl

def actualDocument : List UInt8 :=
  DossierCases.render actual.1.dossier.memory.items.reverse ++
    DeductionCases.renderConclusion "variation + variation" actual.1.store.2 sumRealized.occurrence.2

end ConstitutiveSearch.Agent.Local.Documentary.ProgramCases
/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ProgramCases.baselineTask
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ProgramCases.revisedTask
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ProgramCases.baselineSpec
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ProgramCases.revisedSpec
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ProgramCases.deltaSpec
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ProgramCases.sumSpec
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ProgramCases.start
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ProgramCases.initiallyComplete
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ProgramCases.firstPart
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ProgramCases.lastPart
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ProgramCases.script
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ProgramCases.actual
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ProgramCases.quotation_value
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ProgramCases.quotation_origins
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ProgramCases.baselineReady
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ProgramCases.revisedReady
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ProgramCases.differenceCompatible
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ProgramCases.sumCompatible
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ProgramCases.admissible
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ProgramCases.actualComplete
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ProgramCases.sumRealized
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ProgramCases.all_five_completed
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ProgramCases.three_actual_master_heads
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ProgramCases.five_events
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ProgramCases.five_actual_occurrences
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ProgramCases.actual_sum
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ProgramCases.actual_origins
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ProgramCases.actual_source_origins
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ProgramCases.prefixRun
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ProgramCases.resumed
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ProgramCases.resume_same_actual_frame
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ProgramCases.baselineBinding
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ProgramCases.repeatedBinding
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ProgramCases.bindingPosition
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ProgramCases.bindingValue
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ProgramCases.equal_values
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ProgramCases.distinct_occurrences
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ProgramCases.wrongDemand
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ProgramCases.wrongSpec
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ProgramCases.downstreamDemand
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ProgramCases.wrongScript
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ProgramCases.wrongActual
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ProgramCases.legal_wrong_output_retained
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ProgramCases.dependent_reads_that_output
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ProgramCases.wrong_task_incomplete
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ProgramCases.blockedScript
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ProgramCases.blockedActual
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ProgramCases.refused_has_no_binding
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ProgramCases.missing_has_no_binding
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ProgramCases.independent_continuation
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ProgramCases.refused_has_no_occurrence
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ProgramCases.forbidden_whole_goal_impossible
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ProgramCases.sourceBlockedScript
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ProgramCases.sourceBlockedActual
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ProgramCases.forbidden_source_then_missing
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ProgramCases.source_blocked_incomplete
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ProgramCases.erased
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ProgramCases.context_erasure_same_execution
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ProgramCases.erasedBlocked
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ProgramCases.context_erasure_same_refusal
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ProgramCases.actualDocument
/- AXIOM_AUDIT_END -/
