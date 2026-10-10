import Tests.LocalAlignment.DocumentaryControlInterpreter

/-! Paid traversal of the retained finite binding table. The loaded occurrence
is the actual cell, not a search by value. Each visited constructor costs one
binding transition. Computing the reference bound is a separate bootstrap task. -/
set_option genInjectivity false
set_option maxHeartbeats 3000000
namespace ConstitutiveSearch.Agent.Local.Documentary.ControlBindings
open Resources Program Snapshot Control

inductive Label where
  | instruction
  | binding
  | quotationProducer
  | deductionProducer
  | missingAssembly
  | naturalComparison
  | permissionCell
  | permissionReturn
  | deductionDecision
  | deductionAssembly
  | referencePosition
  | referenceReturn
  | resourceCell
  | producerKindCell
  | producerPortCell
  | producerOutputKind
  | producerAssembly
  | integerNaturalCell
  | integerNaturalReturn
  | integerSign
  | integerSignReturn
  | integerOperation
  | integerNegate
  | formationValues
  | formationWitness
  | formationResources
  | assemblyKind
  | assemblyKinds
  | assemblyKnowledge
  | assemblyStore
  | assemblyExtension
  | assemblyOutput
  | assemblyFrame
  | assemblyPacket
  | citationOrigin
  | citationCheckResult
  | citationReadout
  | citationHead
  | citationFormula
  | citationOpening
  | citationReduction
  | citationStage
  | citationSeed
  | citationInput
  | citationPreservation
  | citationRouting
  | citationContinuationCell
  | citationAssignment
  | citationCandidate
  | citationProducer
  | citationAuthorize
  | citationIncorporate
  | citationCompletion
  | citationDecision
  | citationPacket

variable {context : List SourceKey} {sources : Support SourceValue context}
  {contract : Contract} {rules : Deduction.Policy} {store : Deduction.Store sources contract rules}
  {slots : List Specification} {spec : Specification}

abbrev Read (table : Bindings store slots) (slot : Ref slots spec) :=
  {found : Option (Occurrence store) // table.read slot = found}

def readCode {slots : List Specification} {spec : Specification}
    (table : Bindings store slots) (slot : Ref slots spec) : Code Label (Read table slot) :=
  .step .binding (fun _ => match table, slot with
    | .cons head _, .here => .done ⟨head, rfl⟩
    | .cons _ tail, .prior prior => readCode tail prior)

def readTrace {slots : List Specification} {spec : Specification}
    (table : Bindings store slots) (slot : Ref slots spec) :
    Eval (readCode table slot) (List.replicate (slot.position + 1) .binding) ⟨table.read slot, rfl⟩ :=
  match table, slot with
  | .cons _ _, .here => .step .done
  | .cons _ tail, .prior prior => .step (readTrace tail prior)

theorem replicate_length (count : Nat) :
    (List.replicate count Label.binding).length = count := by
  induction count with
  | zero => rfl
  | succ count previous => exact congrArg Nat.succ previous

theorem read_within (table : Bindings store slots) (slot : Ref slots spec)
    (fuel : Nat) (enough : slot.position + 1 ≤ fuel) :
    runCtl fuel (readCode table slot) =
      some (⟨table.read slot, rfl⟩, List.replicate (slot.position + 1) .binding) :=
  ctl_complete (readTrace table slot) fuel (by rw [replicate_length]; exact enough)

theorem read_short (table : Bindings store slots) (slot : Ref slots spec)
    (fuel : Nat) (short : fuel < slot.position + 1) :
    runCtl fuel (readCode table slot) = none :=
  fuel_short (readTrace table slot) fuel (by rw [replicate_length]; exact short)

end ConstitutiveSearch.Agent.Local.Documentary.ControlBindings

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlBindings.Label
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlBindings.Read
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlBindings.readCode
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlBindings.readTrace
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlBindings.replicate_length
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlBindings.read_within
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlBindings.read_short
/- AXIOM_AUDIT_END -/
