import RelationalPerimeter.Relativity.Production.ConstitutedEvents

/-!
# Dependencies read by constituted local productions

Edges are constructed from the ports of the positive production role.
Resource positions are used afterwards to prove acyclicity, never to create
an edge. Permitted input use is a separate, unexecuted instruction witness;
it does not assert that a signal was emitted or define relativistic influence.
-/
set_option genInjectivity false
namespace RelationalPerimeter.Relativity.Production
open ConstitutiveSearch.Resources

inductive InputPort {context} : {outputKind : Kind} → Instruction context outputKind →
    {inputKind : Kind} → Ref context inputKind → Type where
  | emissionReading (reading : Ref context .reading) (payload : Ref context .payload) :
      InputPort (.emit reading payload) reading
  | emissionPayload (reading : Ref context .reading) (payload : Ref context .payload) :
      InputPort (.emit reading payload) payload
  | relaySignal (signal : Ref context .signal) (calibration : Ref context .calibration) :
      InputPort (.relay signal calibration) signal
  | relayCalibration (signal : Ref context .signal) (calibration : Ref context .calibration) :
      InputPort (.relay signal calibration) calibration
  | receptionSignal (signal : Ref context .signal) : InputPort (.receive signal) signal

structure PermittedUse (source : Cursor) (occurrence : Occurrence source.kinds) where
  outputKind : Kind
  instruction : Instruction source.kinds outputKind
  port : InputPort instruction occurrence.2

def permittedUse {source : Cursor} {outputKind inputKind}
    (instruction : Instruction source.kinds outputKind) (ref : Ref source.kinds inputKind)
    (port : InputPort instruction ref) : PermittedUse source ⟨inputKind, ref⟩ :=
  ⟨outputKind, instruction, port⟩

inductive Used : {context : List Kind} → {values : Values Value context} →
    Formed (context := context) values → Occurrence context → Occurrence context → Type where
  | produced {context} {values : Values Value context} (past : Formed (context := context) values)
      {outputKind inputKind} {instruction : Instruction context outputKind} {output : Value outputKind}
      (role : Produces values instruction output) (ref : Ref context inputKind)
      (port : InputPort instruction ref) :
      Used (.produced past role) (oldOccurrence outputKind ⟨inputKind, ref⟩)
        (freshOccurrence context outputKind)
  | inherited {context} {values : Values Value context} {past : Formed (context := context) values}
      {outputKind} {instruction : Instruction context outputKind} {output : Value outputKind}
      (role : Produces values instruction output) {source target : Occurrence context}
      (edge : Used past source target) :
      Used (.produced past role) (oldOccurrence outputKind source) (oldOccurrence outputKind target)

theorem Used.position_decreases {context} {values : Values Value context}
    {formation : Formed (context := context) values} {source target : Occurrence context}
    (edge : Used formation source target) : target.2.position < source.2.position := by
  induction edge with
  | produced past role ref port => exact Nat.zero_lt_succ _
  | inherited role edge ih => exact Nat.add_lt_add_right ih 1

theorem Used.no_cycle {context} {values : Values Value context}
    {formation : Formed (context := context) values} {occurrence : Occurrence context}
    (edge : Used formation occurrence occurrence) : False :=
  Nat.lt_irrefl _ edge.position_decreases

theorem received_has_no_used_edge (input : Received) {source target : Occurrence receivedKinds}
    (edge : Used (.received input) source target) : False := by cases edge

inductive UsedPath {context} {values : Values Value context}
    (formation : Formed (context := context) values) : Occurrence context → Occurrence context → Type where
  | single {source target} (edge : Used formation source target) : UsedPath formation source target
  | cons {source middle target} (head : Used formation source middle)
      (tail : UsedPath formation middle target) : UsedPath formation source target

def UsedPath.append {context} {values : Values Value context}
    {formation : Formed (context := context) values} {source middle target : Occurrence context}
    (first : UsedPath formation source middle) (second : UsedPath formation middle target) :
    UsedPath formation source target :=
  match first with
  | .single edge => .cons edge second
  | .cons head tail => .cons head (tail.append second)
termination_by structural first

theorem UsedPath.position_decreases {context} {values : Values Value context}
    {formation : Formed (context := context) values} {source target : Occurrence context}
    (path : UsedPath formation source target) : target.2.position < source.2.position := by
  induction path with
  | single edge => exact edge.position_decreases
  | cons head tail ih => exact Nat.lt_trans ih head.position_decreases

theorem UsedPath.no_cycle {context} {values : Values Value context}
    {formation : Formed (context := context) values} {occurrence : Occurrence context}
    (path : UsedPath formation occurrence occurrence) : False :=
  Nat.lt_irrefl _ path.position_decreases

def UsedPath.extend {context} {values : Values Value context}
    {formation : Formed (context := context) values} {source target : Occurrence context}
    {outputKind} {instruction : Instruction context outputKind} {output : Value outputKind}
    (role : Produces values instruction output) (path : UsedPath formation source target) :
    UsedPath (.produced formation role) (oldOccurrence outputKind source) (oldOccurrence outputKind target) :=
  match path with
  | .single edge => .single (.inherited role edge)
  | .cons head tail => .cons (.inherited role head) (tail.extend role)
termination_by structural path

def executedPort {source : Cursor} {outputKind inputKind}
    {instruction : Instruction source.kinds outputKind}
    (determination : Determination source instruction) (ref : Ref source.kinds inputKind)
    (port : InputPort instruction ref) :
    Used (source.extend determination).formation (oldOccurrence outputKind ⟨inputKind, ref⟩)
      (freshOccurrence source.kinds outputKind) :=
  .produced source.formation determination.2 ref port

def extensionOccurrence {source target : Cursor}
    (extension : Support.Extension source.support target.support) (occurrence : Occurrence source.kinds) :
    Occurrence target.kinds := ⟨occurrence.1, extension.references occurrence.2⟩

def Step.transportUsed {source target : Cursor} (step : Step source target)
    {one two : Occurrence source.kinds} (edge : Used source.formation one two) :
    Used target.formation (extensionOccurrence step.transport one) (extensionOccurrence step.transport two) := by
  cases step with
  | mk kind instruction determination exactTarget =>
    cases exactTarget
    exact .inherited determination.2 edge

def historyTransportUsed {source target : Cursor} (history : LocalHistory source target)
    {one two : Occurrence source.kinds} (edge : Used source.formation one two) :
    Used target.formation (extensionOccurrence (historyTransport history) one)
      (extensionOccurrence (historyTransport history) two) :=
  match history with
  | .root => edge
  | .extend past step => step.transportUsed (historyTransportUsed past edge)
termination_by structural history

def historyTransportPath {source target : Cursor} (history : LocalHistory source target)
    {one two : Occurrence source.kinds} (path : UsedPath source.formation one two) :
    UsedPath target.formation (extensionOccurrence (historyTransport history) one)
      (extensionOccurrence (historyTransport history) two) :=
  match path with
  | .single edge => .single (historyTransportUsed history edge)
  | .cons head tail => .cons (historyTransportUsed history head) (historyTransportPath history tail)
termination_by structural path

end RelationalPerimeter.Relativity.Production
/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Relativity.Production.InputPort
#print axioms RelationalPerimeter.Relativity.Production.PermittedUse
#print axioms RelationalPerimeter.Relativity.Production.permittedUse
#print axioms RelationalPerimeter.Relativity.Production.Used
#print axioms RelationalPerimeter.Relativity.Production.Used.position_decreases
#print axioms RelationalPerimeter.Relativity.Production.Used.no_cycle
#print axioms RelationalPerimeter.Relativity.Production.received_has_no_used_edge
#print axioms RelationalPerimeter.Relativity.Production.UsedPath.append
#print axioms RelationalPerimeter.Relativity.Production.UsedPath.position_decreases
#print axioms RelationalPerimeter.Relativity.Production.UsedPath.no_cycle
#print axioms RelationalPerimeter.Relativity.Production.UsedPath.extend
#print axioms RelationalPerimeter.Relativity.Production.executedPort
#print axioms RelationalPerimeter.Relativity.Production.Step.transportUsed
#print axioms RelationalPerimeter.Relativity.Production.historyTransportUsed
#print axioms RelationalPerimeter.Relativity.Production.historyTransportPath
/- AXIOM_AUDIT_END -/
