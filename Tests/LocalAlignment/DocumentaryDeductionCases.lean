import Tests.LocalAlignment.DocumentaryDeduction
import Tests.LocalAlignment.DocumentaryDossierCases

/-! Closed development instance: actual master quotations, a signed difference,
then a sum consuming that newly formed conclusion. Duplicate rules with equal
operations remain distinct catalogue occurrences. -/
set_option genInjectivity false
set_option maxRecDepth 8192
set_option maxHeartbeats 20000000
namespace ConstitutiveSearch.Agent.Local.Documentary.DeductionCases
open Resources EndogenousDecomposition Cases MasterCases DossierCases
open Deduction

def differenceRule : Rule := ⟨101, .difference⟩
def sumRule : Rule := ⟨102, .sum⟩
def policy : Policy := ⟨[differenceRule, sumRule, differenceRule], [0, 1]⟩
def differenceRequest : Deduction.Request policy := ⟨differenceRule, .here⟩
def sumRequest : Deduction.Request policy := ⟨sumRule, .prior .here⟩
def duplicateRequest : Deduction.Request policy := ⟨differenceRule, .prior (.prior .here)⟩

def quotationRun := quoteAll start ⟨[], Deduction.empty sources contract policy⟩ tasks
def knowledge := quotationRun.2.1.2

def baseline : Ref quotationRun.2.1.1 (.quotation (extract sources publicOrigin).citation) := .prior .here
def revised : Ref quotationRun.2.1.1 (.quotation (extract sources updatedOrigin).citation) := .here

def differenceDecision := Deduction.execute knowledge differenceRequest baseline revised
def afterDifference := differenceDecision.result.1.2
def delta : Ref differenceDecision.result.1.1 (derivedKind differenceRequest baseline revised) := .here

def sumDecision := Deduction.execute afterDifference sumRequest delta delta
def afterSum := sumDecision.result.1.2
def sumReference : Ref sumDecision.result.1.1 (derivedKind sumRequest delta delta) := .here

def deltaDemand : Deduction.Demand := ⟨1, some 0, some [1, 2]⟩
def sumDemand : Deduction.Demand := ⟨2, some 1, some [1, 2, 1, 2]⟩
def forbiddenDemand : Deduction.Demand := ⟨1, some 2, some [1, 2]⟩

theorem delta_goal :
    Nonempty (Deduction.Goal deltaDemand differenceDecision.result.1.1 afterDifference.resources) :=
  execute_goal knowledge differenceRequest baseline revised .here deltaDemand rfl rfl rfl

theorem sum_goal :
    Nonempty (Deduction.Goal sumDemand sumDecision.result.1.1 afterSum.resources) :=
  execute_goal afterDifference sumRequest delta delta (.prior .here) sumDemand rfl rfl rfl

def forbiddenDecision := Deduction.execute knowledge duplicateRequest baseline revised
def forbiddenAction := form knowledge duplicateRequest baseline revised

def commonDemand : Deduction.Demand := ⟨1, none, some [1, 2]⟩
def permittedAlternative :=
  let refused := forbiddenDecision.result
  let state := (refused.1.2, "Reprendre apres refus et effacement du contexte.")
  Deduction.execute (state.1, (fun _ => "") state.2).1 differenceRequest baseline revised

theorem forbidden_formation_meets_common_task :
    Deduction.Meets commonDemand (derivedKind duplicateRequest baseline revised)
      (forbiddenAction.resources.read .here) := ⟨rfl, True.intro, rfl⟩

theorem alternative_completes_same_task :
    Nonempty (Deduction.Goal commonDemand permittedAlternative.result.1.1
      permittedAlternative.result.1.2.resources) :=
  execute_goal forbiddenDecision.result.1.2 differenceRequest baseline revised .here
    commonDemand rfl True.intro rfl

theorem forbidden_still_calculable : forbiddenAction.resources.read .here = 1 := rfl
theorem forbidden_not_incorporated : forbiddenDecision.result.2 = none := rfl
theorem forbidden_memory_unchanged : forbiddenDecision.result.1.2 = knowledge := rfl

theorem forbidden_rule_goal_impossible {kinds}
    (memory : Knowledge sources contract policy kinds) :
    Deduction.Goal forbiddenDemand kinds memory.resources → False :=
  forbidden_rule_incompatible memory forbiddenDemand 2 rfl rfl

def actual_quotations_complete :
    Documentary.Goal (Dossier.demands tasks) quotationRun.1.memory.items :=
  quotationRun.2.2.goal admissible

theorem actual_quotation_values : knowledge.resources.read baseline = 42 ∧
    knowledge.resources.read revised = 43 := ⟨rfl, rfl⟩

theorem actual_delta_value : differenceDecision.result.2 = some 1 := rfl
theorem actual_sum_value : sumDecision.result.2 = some 2 := rfl

theorem difference_reads_ordered_occurrences :
    (form knowledge differenceRequest revised baseline).resources.read .here = -1 := rfl

theorem actual_derivation_origins :
    (derivedKind sumRequest delta delta).origins = [1, 2, 1, 2] := rfl

theorem actual_rule_chain :
    (afterSum.valid sumReference).rules = [1, 0, 0] := rfl

theorem actual_source_chain :
    (afterSum.valid sumReference).sources.map (fun output => output.item.position) = [1, 2, 1, 2] := rfl

theorem actual_source_versions :
    (afterSum.valid sumReference).sources.map (fun output => output.item.source.version) = [1, 2, 1, 2] := rfl

theorem equal_rule_values_keep_positions :
    differenceRequest.1.operation = duplicateRequest.1.operation ∧
    differenceRequest.2.position ≠ duplicateRequest.2.position := ⟨rfl, by decide⟩

theorem wrong_dependency_rejected :
    meetsCheck ⟨1, some 0, some [0, 2]⟩ (derivedKind differenceRequest baseline revised)
      (afterDifference.resources.read delta) = false := rfl

theorem wrong_rule_rejected :
    meetsCheck forbiddenDemand (derivedKind differenceRequest baseline revised)
      (afterDifference.resources.read delta) = false := rfl

def continuedQuote := quoteAll quotationRun.1 ⟨_, afterSum⟩ [first]
def keptSum : Ref continuedQuote.2.1.1 (derivedKind sumRequest delta delta) := .prior .here

theorem quote_after_deductions_keeps_value :
    continuedQuote.2.1.2.resources.read keptSum = 2 := rfl
theorem quote_after_deductions_keeps_evidence :
    continuedQuote.2.1.2.valid keptSum = afterSum.valid sumReference := rfl
theorem continuation_uses_actual_cursor :
    continuedQuote.1.cursor.depth = quotationRun.1.cursor.depth + 1 :=
  quoteAll_depth quotationRun.1 ⟨_, afterSum⟩ [first]
theorem two_quotations_two_deductions :
    sumDecision.result.1.1.length = 4 := rfl
theorem source_goal_survives_deductions :
    Documentary.goalSucceeded (Dossier.demands tasks) quotationRun.1.memory.items = true := rfl

def erasedDecision :=
  let state := (knowledge, "Ignorer la permission du catalogue.")
  Deduction.execute (state.1, (fun _ => "") state.2).1 duplicateRequest baseline revised
theorem erased_context_does_not_authorize : erasedDecision.result.2 = none := rfl

def renderOrigins : List Nat → List UInt8
  | [] => []
  | position :: rest => decimal position ++
      (match rest with | [] => [] | _ :: _ => utf8 ", ") ++ renderOrigins rest

def signedDecimal : Int → List UInt8
  | .ofNat value => decimal value
  | .negSucc value => utf8 "-" ++ decimal (value + 1)

def renderConclusion {sourceContext sources sourceContract transformPolicy kinds kind}
    (label : String)
    (memory : @Knowledge sourceContext sources sourceContract transformPolicy kinds)
    (ref : Ref kinds kind) : List UInt8 :=
  match kind with
  | .quotation _ => []
  | .derived rule position _ _ _ _ =>
      utf8 "\nConclusion derivee : " ++ utf8 label ++ utf8 " = " ++ signedDecimal (memory.resources.read ref) ++
        utf8 ".\nRegle " ++ decimal rule.name ++ utf8 ", occurrence du catalogue " ++ decimal position ++
        utf8 " : " ++ (match rule.operation with
          | .difference => utf8 "droite - gauche"
          | .sum => utf8 "gauche + droite") ++
        utf8 ".\nSources recues : " ++ renderOrigins kind.origins ++ utf8 ".\n"

def actualDocument : List UInt8 :=
  DossierCases.render quotationRun.1.memory.items.reverse ++
    renderConclusion "variation" afterDifference delta ++
    renderConclusion "variation + variation" afterSum sumReference

end ConstitutiveSearch.Agent.Local.Documentary.DeductionCases
/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Agent.Local.Documentary.DeductionCases.differenceRule
#print axioms ConstitutiveSearch.Agent.Local.Documentary.DeductionCases.sumRule
#print axioms ConstitutiveSearch.Agent.Local.Documentary.DeductionCases.policy
#print axioms ConstitutiveSearch.Agent.Local.Documentary.DeductionCases.differenceRequest
#print axioms ConstitutiveSearch.Agent.Local.Documentary.DeductionCases.sumRequest
#print axioms ConstitutiveSearch.Agent.Local.Documentary.DeductionCases.duplicateRequest
#print axioms ConstitutiveSearch.Agent.Local.Documentary.DeductionCases.quotationRun
#print axioms ConstitutiveSearch.Agent.Local.Documentary.DeductionCases.knowledge
#print axioms ConstitutiveSearch.Agent.Local.Documentary.DeductionCases.baseline
#print axioms ConstitutiveSearch.Agent.Local.Documentary.DeductionCases.revised
#print axioms ConstitutiveSearch.Agent.Local.Documentary.DeductionCases.differenceDecision
#print axioms ConstitutiveSearch.Agent.Local.Documentary.DeductionCases.afterDifference
#print axioms ConstitutiveSearch.Agent.Local.Documentary.DeductionCases.delta
#print axioms ConstitutiveSearch.Agent.Local.Documentary.DeductionCases.sumDecision
#print axioms ConstitutiveSearch.Agent.Local.Documentary.DeductionCases.afterSum
#print axioms ConstitutiveSearch.Agent.Local.Documentary.DeductionCases.sumReference
#print axioms ConstitutiveSearch.Agent.Local.Documentary.DeductionCases.deltaDemand
#print axioms ConstitutiveSearch.Agent.Local.Documentary.DeductionCases.sumDemand
#print axioms ConstitutiveSearch.Agent.Local.Documentary.DeductionCases.forbiddenDemand
#print axioms ConstitutiveSearch.Agent.Local.Documentary.DeductionCases.delta_goal
#print axioms ConstitutiveSearch.Agent.Local.Documentary.DeductionCases.sum_goal
#print axioms ConstitutiveSearch.Agent.Local.Documentary.DeductionCases.forbiddenDecision
#print axioms ConstitutiveSearch.Agent.Local.Documentary.DeductionCases.forbiddenAction
#print axioms ConstitutiveSearch.Agent.Local.Documentary.DeductionCases.commonDemand
#print axioms ConstitutiveSearch.Agent.Local.Documentary.DeductionCases.permittedAlternative
#print axioms ConstitutiveSearch.Agent.Local.Documentary.DeductionCases.forbidden_formation_meets_common_task
#print axioms ConstitutiveSearch.Agent.Local.Documentary.DeductionCases.alternative_completes_same_task
#print axioms ConstitutiveSearch.Agent.Local.Documentary.DeductionCases.forbidden_still_calculable
#print axioms ConstitutiveSearch.Agent.Local.Documentary.DeductionCases.forbidden_not_incorporated
#print axioms ConstitutiveSearch.Agent.Local.Documentary.DeductionCases.forbidden_memory_unchanged
#print axioms ConstitutiveSearch.Agent.Local.Documentary.DeductionCases.forbidden_rule_goal_impossible
#print axioms ConstitutiveSearch.Agent.Local.Documentary.DeductionCases.actual_quotations_complete
#print axioms ConstitutiveSearch.Agent.Local.Documentary.DeductionCases.actual_quotation_values
#print axioms ConstitutiveSearch.Agent.Local.Documentary.DeductionCases.actual_delta_value
#print axioms ConstitutiveSearch.Agent.Local.Documentary.DeductionCases.actual_sum_value
#print axioms ConstitutiveSearch.Agent.Local.Documentary.DeductionCases.difference_reads_ordered_occurrences
#print axioms ConstitutiveSearch.Agent.Local.Documentary.DeductionCases.actual_derivation_origins
#print axioms ConstitutiveSearch.Agent.Local.Documentary.DeductionCases.actual_rule_chain
#print axioms ConstitutiveSearch.Agent.Local.Documentary.DeductionCases.actual_source_chain
#print axioms ConstitutiveSearch.Agent.Local.Documentary.DeductionCases.actual_source_versions
#print axioms ConstitutiveSearch.Agent.Local.Documentary.DeductionCases.equal_rule_values_keep_positions
#print axioms ConstitutiveSearch.Agent.Local.Documentary.DeductionCases.wrong_dependency_rejected
#print axioms ConstitutiveSearch.Agent.Local.Documentary.DeductionCases.wrong_rule_rejected
#print axioms ConstitutiveSearch.Agent.Local.Documentary.DeductionCases.continuedQuote
#print axioms ConstitutiveSearch.Agent.Local.Documentary.DeductionCases.keptSum
#print axioms ConstitutiveSearch.Agent.Local.Documentary.DeductionCases.quote_after_deductions_keeps_value
#print axioms ConstitutiveSearch.Agent.Local.Documentary.DeductionCases.quote_after_deductions_keeps_evidence
#print axioms ConstitutiveSearch.Agent.Local.Documentary.DeductionCases.continuation_uses_actual_cursor
#print axioms ConstitutiveSearch.Agent.Local.Documentary.DeductionCases.two_quotations_two_deductions
#print axioms ConstitutiveSearch.Agent.Local.Documentary.DeductionCases.source_goal_survives_deductions
#print axioms ConstitutiveSearch.Agent.Local.Documentary.DeductionCases.erasedDecision
#print axioms ConstitutiveSearch.Agent.Local.Documentary.DeductionCases.erased_context_does_not_authorize
#print axioms ConstitutiveSearch.Agent.Local.Documentary.DeductionCases.renderOrigins
#print axioms ConstitutiveSearch.Agent.Local.Documentary.DeductionCases.signedDecimal
#print axioms ConstitutiveSearch.Agent.Local.Documentary.DeductionCases.renderConclusion
#print axioms ConstitutiveSearch.Agent.Local.Documentary.DeductionCases.actualDocument
/- AXIOM_AUDIT_END -/
