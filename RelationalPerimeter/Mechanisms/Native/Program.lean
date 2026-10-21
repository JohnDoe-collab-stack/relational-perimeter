import RelationalPerimeter.Mechanisms.Native.Arithmetic

/-!
# Chronologically constituted native network programs

Every added neuron can refer only to received inputs and to neuron outputs that
were already produced. The program stores architecture and parameters only;
no normative criterion or expected proposal occurs here.
-/
set_option genInjectivity false
namespace ConstitutiveSearch.NativeMechanism

inductive NetworkProgram (inputCount : Nat) : Nat -> Type where
  | empty : NetworkProgram inputCount 0
  | extend {produced : Nat} :
      NetworkProgram inputCount produced ->
      NeuronSpec inputCount produced ->
      NetworkProgram inputCount (produced + 1)

def NetworkProgram.inputCount
    {inputCount produced : Nat}
    (_ : NetworkProgram inputCount produced) : Nat := inputCount

def NetworkProgram.producedCount
    {inputCount produced : Nat}
    (_ : NetworkProgram inputCount produced) : Nat := produced

def NetworkProgram.neuronAt {inputCount : Nat} :
    {produced : Nat} ->
    (program : NetworkProgram inputCount produced) ->
    (index : Fin produced) -> NeuronSpec inputCount index.val
  | _, .empty, index => nomatch index
  | _, .extend (produced := priorCount) prior neuron, index =>
      if before : index.val < priorCount then
        prior.neuronAt ⟨index.val, before⟩
      else
        have exactLast : index.val = priorCount :=
          Nat.eq_of_lt_succ_of_not_lt index.isLt before
        exactLast.symm ▸ neuron

/-- Chronological depth is an execution-order readout. Dependency paths remain
represented separately by `SourceIndex` and are reconstructed from edges. -/
def NetworkProgram.depthAt
    {inputCount produced : Nat}
    (_program : NetworkProgram inputCount produced)
    (index : Fin produced) : Nat := index.val + 1

structure OutputPorts (produced : Nat) where
  sources : List (Fin produced)
  nonempty : sources ≠ []

def readOutputs {produced : Nat} (ports : OutputPorts produced)
    (values : SizedActivations produced) : List Activation :=
  ports.sources.map values.read

universe u v

structure NativeSystem (Input : Type u) (Proposal : Type v) where
  inputCount : Nat
  producedCount : Nat
  encode : Input -> SizedActivations inputCount
  program : NetworkProgram inputCount producedCount
  outputs : OutputPorts producedCount
  decode : List Activation -> Proposal

end ConstitutiveSearch.NativeMechanism
/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.NativeMechanism.NetworkProgram
#print axioms ConstitutiveSearch.NativeMechanism.NetworkProgram.neuronAt
#print axioms ConstitutiveSearch.NativeMechanism.NetworkProgram.depthAt
#print axioms ConstitutiveSearch.NativeMechanism.OutputPorts
#print axioms ConstitutiveSearch.NativeMechanism.readOutputs
#print axioms ConstitutiveSearch.NativeMechanism.NativeSystem
/- AXIOM_AUDIT_END -/
