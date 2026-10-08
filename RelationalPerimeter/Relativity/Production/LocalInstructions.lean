import RelationalPerimeter.Relativity.Production.PhysicalPrimitives
import RelationalPerimeter.Constitution.Resources.ConstructedSupport

/-!
# Closed local instructions and their positive relational determinations

Every variable input is a typed resource reference. There is no arbitrary
operation closure and no future history argument. `Produces` is the positive
relation between those actual inputs, an instruction and its output. Its
constructors determine the output; an independent prescribed target is not
an input to the executor.
-/
set_option genInjectivity false
namespace RelationalPerimeter.Relativity.Production
open ConstitutiveSearch.Resources

inductive Instruction (context : List Kind) : Kind → Type where
  | emit : Ref context .reading → Ref context .payload → Instruction context .signal
  | relay : Ref context .signal → Ref context .calibration → Instruction context .signal
  | receive : Ref context .signal → Instruction context .reading

def Instruction.lower {context} : {kind : Kind} → Instruction context kind → Producer Value context
  | _, .emit reading payload =>
    { inputKinds := [.reading, .payload]
      inputs := .cons reading (.cons payload .nil)
      outputKind := fun _ => .signal
      operation := fun arguments => SignalRecord.emit arguments.1 arguments.2.1 }
  | _, .relay signal calibration =>
    { inputKinds := [.signal, .calibration]
      inputs := .cons signal (.cons calibration .nil)
      outputKind := fun _ => .signal
      operation := fun arguments => arguments.1.relay arguments.2.1 }
  | _, .receive signal =>
    { inputKinds := [.signal]
      inputs := .cons signal .nil
      outputKind := fun _ => .reading
      operation := fun arguments => arguments.1.reading }

def Instruction.interpret {context} (values : Values Value context) :
    {kind : Kind} → Instruction context kind → Value kind
  | _, .emit reading payload => SignalRecord.emit (read values reading) (read values payload)
  | _, .relay signal calibration => (read values signal).relay (read values calibration)
  | _, .receive signal => (read values signal).reading

theorem lower_outputKind {context kind} (values : Values Value context) (instruction : Instruction context kind) :
    instruction.lower.outputKind (instruction.lower.arguments values) = kind := by
  cases instruction <;> rfl

theorem lower_value_exact {context kind} (values : Values Value context) (instruction : Instruction context kind) :
    HEq (instruction.lower.operation (instruction.lower.arguments values)) (instruction.interpret values) := by
  cases instruction <;> rfl

inductive Produces {context} (values : Values Value context) :
    {kind : Kind} → Instruction context kind → Value kind → Type where
  | emitted (reading : Ref context .reading) (payload : Ref context .payload) :
    Produces values (.emit reading payload) (SignalRecord.emit (read values reading) (read values payload))
  | relayed (signal : Ref context .signal) (calibration : Ref context .calibration) :
    Produces values (.relay signal calibration) ((read values signal).relay (read values calibration))
  | received (signal : Ref context .signal) :
    Produces values (.receive signal) (read values signal).reading

def execute {context} (values : Values Value context) :
    {kind : Kind} → (instruction : Instruction context kind) → (output : Value kind) ×'
      Produces values instruction output
  | _, .emit reading payload =>
    ⟨SignalRecord.emit (read values reading) (read values payload), .emitted reading payload⟩
  | _, .relay signal calibration =>
    ⟨(read values signal).relay (read values calibration), .relayed signal calibration⟩
  | _, .receive signal => ⟨(read values signal).reading, .received signal⟩

theorem Produces.output_exact {context kind} {values : Values Value context}
    {instruction : Instruction context kind} {output : Value kind}
    (role : Produces values instruction output) : output = instruction.interpret values := by
  cases role <;> rfl

theorem execute_output_exact {context kind} (values : Values Value context) (instruction : Instruction context kind) :
    (execute values instruction).1 = instruction.interpret values :=
  (execute values instruction).2.output_exact

theorem relay_output_changes {context} (values : Values Value context)
    (signal : Ref context .signal) (calibration : Ref context .calibration) :
    (execute values (.relay signal calibration)).1.reading ≠ (read values signal).reading :=
  relay_changes_reading (read values signal) (read values calibration)

end RelationalPerimeter.Relativity.Production
/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Relativity.Production.Instruction
#print axioms RelationalPerimeter.Relativity.Production.Instruction.lower
#print axioms RelationalPerimeter.Relativity.Production.Instruction.interpret
#print axioms RelationalPerimeter.Relativity.Production.lower_outputKind
#print axioms RelationalPerimeter.Relativity.Production.lower_value_exact
#print axioms RelationalPerimeter.Relativity.Production.Produces
#print axioms RelationalPerimeter.Relativity.Production.execute
#print axioms RelationalPerimeter.Relativity.Production.Produces.output_exact
#print axioms RelationalPerimeter.Relativity.Production.execute_output_exact
#print axioms RelationalPerimeter.Relativity.Production.relay_output_changes
/- AXIOM_AUDIT_END -/
