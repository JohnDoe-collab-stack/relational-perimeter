import RelationalPerimeter.Relativity.Production.ConstitutedEvents

/-!
# Exact renaming of constituted resource references

References are transported with their kinds and two return laws. Numerical
addresses do not define occurrence identity. Renamed instructions read the
transported ports; their action agrees only under the explicit read raccord.
-/
set_option genInjectivity false
namespace RelationalPerimeter.Relativity.Production
open ConstitutiveSearch.Resources

structure ReferenceTransport (source target : List Kind) where
  forward : {kind : Kind} → Ref source kind → Ref target kind
  backward : {kind : Kind} → Ref target kind → Ref source kind
  forwardBackward : ∀ {kind} (ref : Ref source kind), backward (forward ref) = ref
  backwardForward : ∀ {kind} (ref : Ref target kind), forward (backward ref) = ref

def ReferenceTransport.identity (context : List Kind) : ReferenceTransport context context :=
  ⟨id, id, fun _ => rfl, fun _ => rfl⟩

def ReferenceTransport.reverse {source target} (transport : ReferenceTransport source target) :
    ReferenceTransport target source :=
  ⟨transport.backward, transport.forward, transport.backwardForward, transport.forwardBackward⟩

def ReferenceTransport.extend {source target} (transport : ReferenceTransport source target) (added : Kind) :
    ReferenceTransport (added :: source) (added :: target) where
  forward := fun ref => match ref with
    | .here => .here
    | .prior old => .prior (transport.forward old)
  backward := fun ref => match ref with
    | .here => .here
    | .prior old => .prior (transport.backward old)
  forwardBackward := by
    intro kind ref
    cases ref with
    | here => rfl
    | prior old => exact congrArg Ref.prior (transport.forwardBackward old)
  backwardForward := by
    intro kind ref
    cases ref with
    | here => rfl
    | prior old => exact congrArg Ref.prior (transport.backwardForward old)

def swapReferences {context : List Kind} {one two : Kind} :
    {kind : Kind} → Ref (two :: one :: context) kind → Ref (one :: two :: context) kind
  | _, .here => .prior .here
  | _, .prior .here => .here
  | _, .prior (.prior old) => .prior (.prior old)

theorem swapReferences_returns {context : List Kind} {one two kind : Kind}
    (ref : Ref (two :: one :: context) kind) : swapReferences (swapReferences ref) = ref := by
  cases ref with
  | here => rfl
  | prior rest => cases rest <;> rfl

def swapTransport (context : List Kind) (one two : Kind) :
    ReferenceTransport (two :: one :: context) (one :: two :: context) :=
  ⟨swapReferences, swapReferences, swapReferences_returns, swapReferences_returns⟩

def ReferenceTransport.occurrences {source target} (transport : ReferenceTransport source target) :
    ExactTypeTransport (Occurrence source) (Occurrence target) where
  forward := fun occurrence => ⟨occurrence.1, transport.forward occurrence.2⟩
  backward := fun occurrence => ⟨occurrence.1, transport.backward occurrence.2⟩
  forwardBackward := by
    intro occurrence
    cases occurrence with
    | mk kind ref => exact congrArg (fun ref => PSigma.mk kind ref) (transport.forwardBackward ref)
  backwardForward := by
    intro occurrence
    cases occurrence with
    | mk kind ref => exact congrArg (fun ref => PSigma.mk kind ref) (transport.backwardForward ref)

def Instruction.rename {source target : List Kind}
    (references : {kind : Kind} → Ref source kind → Ref target kind) :
    {kind : Kind} → Instruction source kind → Instruction target kind
  | _, .emit reading payload => .emit (references reading) (references payload)
  | _, .relay signal calibration => .relay (references signal) (references calibration)
  | _, .receive signal => .receive (references signal)

theorem Instruction.rename_interpret {source target : List Kind}
    (references : {kind : Kind} → Ref source kind → Ref target kind)
    (sourceValues : Values Value source) (targetValues : Values Value target)
    (reads : ∀ {kind} (ref : Ref source kind), read targetValues (references ref) = read sourceValues ref)
    {kind} (instruction : Instruction source kind) :
    (instruction.rename references).interpret targetValues = instruction.interpret sourceValues := by
  cases instruction with
  | emit reading payload =>
    change SignalRecord.emit _ _ = SignalRecord.emit _ _
    rw [reads reading, reads payload]
  | relay signal calibration =>
    change SignalRecord.relay _ _ = SignalRecord.relay _ _
    rw [reads signal, reads calibration]
  | receive signal =>
    change (read targetValues (references signal)).reading = (read sourceValues signal).reading
    rw [reads signal]

theorem Instruction.rename_returns {source target : List Kind}
    (transport : ReferenceTransport source target) {kind} (instruction : Instruction source kind) :
    (instruction.rename transport.forward).rename transport.backward = instruction := by
  cases instruction with
  | emit reading payload =>
    change Instruction.emit (transport.backward (transport.forward reading))
      (transport.backward (transport.forward payload)) = Instruction.emit reading payload
    rw [transport.forwardBackward reading, transport.forwardBackward payload]
  | relay signal calibration =>
    change Instruction.relay (transport.backward (transport.forward signal))
      (transport.backward (transport.forward calibration)) = Instruction.relay signal calibration
    rw [transport.forwardBackward signal, transport.forwardBackward calibration]
  | receive signal =>
    exact congrArg Instruction.receive (transport.forwardBackward signal)

structure ReadRaccord (source target : Cursor) where
  references : ReferenceTransport source.kinds target.kinds
  reads : ∀ {kind} (ref : Ref source.kinds kind), target.read (references.forward ref) = source.read ref

def ReadRaccord.reverse {source target} (raccord : ReadRaccord source target) : ReadRaccord target source where
  references := raccord.references.reverse
  reads := fun ref => by
    have same := raccord.reads (raccord.references.backward ref)
    rw [raccord.references.backwardForward ref] at same
    exact same.symm

theorem ReadRaccord.action_exact {source target} (raccord : ReadRaccord source target)
    {kind} (instruction : Instruction source.kinds kind) :
    (perform target (instruction.rename raccord.references.forward)).determination.1 =
      (perform source instruction).determination.1 :=
  (perform_output_exact target _).trans
    ((instruction.rename_interpret _ source.values target.values raccord.reads).trans
      (perform_output_exact source instruction).symm)

end RelationalPerimeter.Relativity.Production
/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Relativity.Production.ReferenceTransport
#print axioms RelationalPerimeter.Relativity.Production.ReferenceTransport.identity
#print axioms RelationalPerimeter.Relativity.Production.ReferenceTransport.reverse
#print axioms RelationalPerimeter.Relativity.Production.ReferenceTransport.extend
#print axioms RelationalPerimeter.Relativity.Production.swapReferences
#print axioms RelationalPerimeter.Relativity.Production.swapReferences_returns
#print axioms RelationalPerimeter.Relativity.Production.swapTransport
#print axioms RelationalPerimeter.Relativity.Production.ReferenceTransport.occurrences
#print axioms RelationalPerimeter.Relativity.Production.Instruction.rename
#print axioms RelationalPerimeter.Relativity.Production.Instruction.rename_interpret
#print axioms RelationalPerimeter.Relativity.Production.Instruction.rename_returns
#print axioms RelationalPerimeter.Relativity.Production.ReadRaccord
#print axioms RelationalPerimeter.Relativity.Production.ReadRaccord.reverse
#print axioms RelationalPerimeter.Relativity.Production.ReadRaccord.action_exact
/- AXIOM_AUDIT_END -/
