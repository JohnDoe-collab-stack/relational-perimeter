import RelationalPerimeter.Relativity.Production.UsedDependencies
import RelationalPerimeter.Relativity.Production.PortAdmissions

/-!
# Permitted finite influence and its actual realization

A plan is constructed from the declared instruction ports, not from the
absence or presence of an executed edge. Its target is a future production,
not an arbitrarily prescribed occurrence in the present history. Intervening
productions are allowed. Executing it constructs the values, the founded
history and the used path together, with one shared production at each step.

This is influence under the current emission/relay/reception law. It is not
a complete physical influence relation or a criterion of spacelike separation.
-/
set_option genInjectivity false
namespace RelationalPerimeter.Relativity.Production
open ConstitutiveSearch.Resources

inductive InfluencePlan : (context : List Kind) → Occurrence context → Kind → Type where
  | finish {context outputKind inputKind} (instruction : Instruction context outputKind)
      (ref : Ref context inputKind) (port : InputPort instruction ref) :
      InfluencePlan context ⟨inputKind, ref⟩ outputKind
  | follow {context outputKind inputKind finalKind} (instruction : Instruction context outputKind)
      (ref : Ref context inputKind) (port : InputPort instruction ref)
      (tail : InfluencePlan (outputKind :: context) (freshOccurrence context outputKind) finalKind) :
      InfluencePlan context ⟨inputKind, ref⟩ finalKind
  | delay {context addedKind finalKind} {origin : Occurrence context}
      (instruction : Instruction context addedKind)
      (tail : InfluencePlan (addedKind :: context) (oldOccurrence addedKind origin) finalKind) :
      InfluencePlan context origin finalKind

def InfluencePlan.schedule {context origin finalKind} (plan : InfluencePlan context origin finalKind) :
    Program context :=
  match plan with
  | .finish instruction _ _ => .step instruction .done
  | .follow instruction _ _ tail => .step instruction tail.schedule
  | .delay instruction tail => .step instruction tail.schedule
termination_by structural plan

theorem InfluencePlan.target_not_payload {context origin finalKind}
    (plan : InfluencePlan context origin finalKind) : finalKind ≠ .payload := by
  induction plan with
  | finish instruction ref port => cases instruction <;> intro same <;> cases same
  | follow instruction ref port tail ih => exact ih
  | delay instruction tail ih => exact ih

def Instruction.request {context kind} (instruction : Instruction context kind) : LocalRequest :=
  match instruction with
  | .emit reading payload => .emit reading.position payload.position
  | .relay signal calibration => .relay signal.position calibration.position
  | .receive signal => .receive signal.position

def instructionAdmission (source : Cursor) {kind} (instruction : Instruction source.kinds kind) :
    LocalAdmission source instruction.request :=
  match instruction with
  | .emit reading payload => (⟨reading, rfl⟩, ⟨payload, rfl⟩)
  | .relay signal calibration => (⟨signal, rfl⟩, ⟨calibration, rfl⟩)
  | .receive signal => ⟨signal, rfl⟩

theorem instruction_request_enabled (source : Cursor) {kind}
    (instruction : Instruction source.kinds kind) : admissionEnabled source instruction.request = true := by
  cases enabled : admissionEnabled source instruction.request with
  | true => rfl
  | false => exact False.elim (refusal_refutes_admission source instruction.request enabled
      (instructionAdmission source instruction))

/-- Pointwise composition on constituted references; no function extensionality. -/
theorem historyTransport_append_occurrence {source middle target : Cursor}
    (first : LocalHistory source middle) (second : LocalHistory middle target)
    (origin : Occurrence source.kinds) :
    extensionOccurrence (historyTransport (StrongPerimetralTurning.History.append first second)) origin =
      extensionOccurrence (historyTransport second) (extensionOccurrence (historyTransport first) origin) := by
  induction second with
  | root => rfl
  | extend past step ih => exact congrArg (extensionOccurrence step.transport) ih

def productionHistory {source kind} {instruction : Instruction source.kinds kind}
    (head : Production source instruction) : LocalHistory source head.successor :=
  .extend .root ⟨kind, instruction, head.determination, head.successorExact⟩

structure InfluenceExecution (source : Cursor) (origin : Occurrence source.kinds) (finalKind : Kind) where
  execution : Execution source
  target : Ref execution.cursor.kinds finalKind
  path : UsedPath execution.cursor.formation
    (extensionOccurrence (historyTransport execution.history) origin) ⟨finalKind, target⟩

/-- Prefixing consumes the already produced head, never a fresh execution. -/
def InfluenceExecution.prepend {source kind} {instruction : Instruction source.kinds kind}
    (head : Production source instruction) (suffix : Execution head.successor) : Execution source :=
  ⟨suffix.cursor, StrongPerimetralTurning.History.append (productionHistory head) suffix.history⟩

def realizeInfluenceFrom {context origin finalKind} (plan : InfluencePlan context origin finalKind)
    (values : Values Value context) (formation : Formed (context := context) values)
    (resourceFormation : Formation Value (context := context) values)
    (resourceExact : ResourceInterpretation formation resourceFormation) :
    InfluenceExecution ⟨context, values, formation, resourceFormation, resourceExact⟩ origin finalKind :=
  match plan with
  | .finish instruction ref port => by
    let source : Cursor := ⟨_, values, formation, resourceFormation, resourceExact⟩
    let head := perform source instruction
    exact ⟨⟨head.successor, productionHistory head⟩, .here,
      .single (executedPort head.determination ref port)⟩
  | .follow instruction ref port tail => by
    let source : Cursor := ⟨_, values, formation, resourceFormation, resourceExact⟩
    let head := perform source instruction
    let suffix := realizeInfluenceFrom tail head.successor.values head.successor.formation
      head.successor.resourceFormation head.successor.resourceExact
    have edge := historyTransportUsed suffix.execution.history (executedPort head.determination ref port)
    have path := UsedPath.cons edge suffix.path
    have sourceExact := historyTransport_append_occurrence (productionHistory head)
      suffix.execution.history ⟨_, ref⟩
    exact ⟨InfluenceExecution.prepend head suffix.execution, suffix.target, sourceExact.symm ▸ path⟩
  | .delay instruction tail => by
    let source : Cursor := ⟨_, values, formation, resourceFormation, resourceExact⟩
    let head := perform source instruction
    let suffix := realizeInfluenceFrom tail head.successor.values head.successor.formation
      head.successor.resourceFormation head.successor.resourceExact
    have sourceExact := historyTransport_append_occurrence (productionHistory head)
      suffix.execution.history origin
    exact ⟨InfluenceExecution.prepend head suffix.execution, suffix.target, sourceExact.symm ▸ suffix.path⟩
termination_by structural plan

def realizeInfluence (source : Cursor) {origin finalKind}
    (plan : InfluencePlan source.kinds origin finalKind) : InfluenceExecution source origin finalKind :=
  realizeInfluenceFrom plan source.values source.formation source.resourceFormation source.resourceExact

/-- Erasing the path proof recovers the existing runner, including its history. -/
theorem realizeInfluenceFrom_execution_exact {context origin finalKind}
    (plan : InfluencePlan context origin finalKind)
    (values : Values Value context) (formation : Formed (context := context) values)
    (resourceFormation : Formation Value (context := context) values)
    (resourceExact : ResourceInterpretation formation resourceFormation) :
    (realizeInfluenceFrom plan values formation resourceFormation resourceExact).execution =
      runFrom plan.schedule values formation resourceFormation resourceExact := by
  induction plan with
  | finish instruction ref port => rfl
  | follow instruction ref port tail ih =>
    let source : Cursor := ⟨_, values, formation, resourceFormation, resourceExact⟩
    let head := perform source instruction
    exact congrArg (InfluenceExecution.prepend head)
      (ih head.successor.values head.successor.formation head.successor.resourceFormation head.successor.resourceExact)
  | delay instruction tail ih =>
    let source : Cursor := ⟨_, values, formation, resourceFormation, resourceExact⟩
    let head := perform source instruction
    exact congrArg (InfluenceExecution.prepend head)
      (ih head.successor.values head.successor.formation head.successor.resourceFormation head.successor.resourceExact)

theorem realizeInfluence_execution_exact (source : Cursor) {origin finalKind}
    (plan : InfluencePlan source.kinds origin finalKind) :
    (realizeInfluence source plan).execution = run source plan.schedule :=
  realizeInfluenceFrom_execution_exact plan source.values source.formation source.resourceFormation source.resourceExact

theorem realized_influence_distinct (source : Cursor) {origin finalKind}
    (plan : InfluencePlan source.kinds origin finalKind) :
    extensionOccurrence (historyTransport (realizeInfluence source plan).execution.history) origin ≠
      ⟨finalKind, (realizeInfluence source plan).target⟩ := by
  intro same
  have path := (realizeInfluence source plan).path
  exact UsedPath.no_cycle (same ▸ path)

end RelationalPerimeter.Relativity.Production
/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Relativity.Production.InfluencePlan
#print axioms RelationalPerimeter.Relativity.Production.InfluencePlan.schedule
#print axioms RelationalPerimeter.Relativity.Production.InfluencePlan.target_not_payload
#print axioms RelationalPerimeter.Relativity.Production.Instruction.request
#print axioms RelationalPerimeter.Relativity.Production.instructionAdmission
#print axioms RelationalPerimeter.Relativity.Production.instruction_request_enabled
#print axioms RelationalPerimeter.Relativity.Production.historyTransport_append_occurrence
#print axioms RelationalPerimeter.Relativity.Production.productionHistory
#print axioms RelationalPerimeter.Relativity.Production.InfluenceExecution
#print axioms RelationalPerimeter.Relativity.Production.InfluenceExecution.prepend
#print axioms RelationalPerimeter.Relativity.Production.realizeInfluenceFrom
#print axioms RelationalPerimeter.Relativity.Production.realizeInfluence
#print axioms RelationalPerimeter.Relativity.Production.realizeInfluenceFrom_execution_exact
#print axioms RelationalPerimeter.Relativity.Production.realizeInfluence_execution_exact
#print axioms RelationalPerimeter.Relativity.Production.realized_influence_distinct
/- AXIOM_AUDIT_END -/
