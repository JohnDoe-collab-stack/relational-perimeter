import RelationalPerimeter.Mechanisms.Native.Program

/-!
# Native execution with a co-produced trace

The activation vector and its trace are produced by one structural recursion.
`executeProgram` is only a projection of that recursion, never an independent
evaluator to which a retrospective trace could be attached.
-/
set_option genInjectivity false
namespace ConstitutiveSearch.NativeMechanism

inductive NativeTrace {inputCount : Nat}
    (inputs : SizedActivations inputCount) :
    {produced : Nat} ->
    (program : NetworkProgram inputCount produced) ->
    SizedActivations produced -> Type where
  | empty : NativeTrace inputs .empty SizedActivations.empty
  | extend {produced : Nat}
      {priorProgram : NetworkProgram inputCount produced}
      {neuron : NeuronSpec inputCount produced}
      {activations : SizedActivations produced}
      (prior : NativeTrace inputs priorProgram activations) :
      NativeTrace inputs (.extend priorProgram neuron)
        (SizedActivations.snoc activations
          (fireNeuron neuron inputs activations))

/-- The activation prefix available when a target neuron was executed.

This is eliminated directly from the co-produced trace.  In particular, it
cannot inspect a completed future suffix and cannot be replaced by a prefix
chosen independently after execution. -/
def NativeTrace.activationsBefore
    {inputs : SizedActivations inputCount} :
    {produced : Nat} ->
    {program : NetworkProgram inputCount produced} ->
    {activations : SizedActivations produced} ->
    NativeTrace inputs program activations ->
    (target : Fin produced) -> SizedActivations target.val
  | _, _, _, .empty, target => nomatch target
  | _, _, _, .extend (produced := priorCount)
      (activations := priorActivations) prior, target =>
      if before : target.val < priorCount then
        prior.activationsBefore ⟨target.val, before⟩
      else
        have exactLast : target.val = priorCount :=
          Nat.eq_of_lt_succ_of_not_lt target.isLt before
        exactLast.symm ▸ priorActivations

theorem NativeTrace.activationsBefore_read_exact
    {inputs : SizedActivations inputCount}
    {program : NetworkProgram inputCount produced}
    {activations : SizedActivations produced}
    (trace : NativeTrace inputs program activations)
    (target : Fin produced) (source : Fin target.val) :
    (trace.activationsBefore target).read source =
      activations.read
        ⟨source.val, Nat.lt_trans source.isLt target.isLt⟩ := by
  induction trace with
  | empty => nomatch target
  | @extend priorCount priorProgram neuron priorActivations prior ih =>
      if before : target.val < priorCount then
        let priorTarget : Fin priorCount := ⟨target.val, before⟩
        let priorSource : Fin priorCount :=
          ⟨source.val, Nat.lt_trans source.isLt before⟩
        unfold NativeTrace.activationsBefore
        rw [dif_pos before]
        change (prior.activationsBefore priorTarget).read source =
          (priorActivations.snoc
            (fireNeuron neuron inputs priorActivations)).read
              priorSource.castSucc
        rw [SizedActivations.read_snoc_castSucc]
        exact ih priorTarget source
      else
        have targetValue : target.val = priorCount :=
          Nat.eq_of_lt_succ_of_not_lt target.isLt before
        have targetExact : target = Fin.last priorCount := by
          apply Fin.ext
          exact targetValue
        revert source
        subst target
        intro source
        unfold NativeTrace.activationsBefore
        rw [dif_neg before]
        change priorActivations.read source =
          (priorActivations.snoc
            (fireNeuron neuron inputs priorActivations)).read
              source.castSucc
        rw [SizedActivations.read_snoc_castSucc]

theorem NativeTrace.neuron_output_exact
    {inputs : SizedActivations inputCount}
    {program : NetworkProgram inputCount produced}
    {activations : SizedActivations produced}
    (trace : NativeTrace inputs program activations)
    (target : Fin produced) :
    activations.read target =
      fireNeuron (program.neuronAt target) inputs
        (trace.activationsBefore target) := by
  induction trace with
  | empty => nomatch target
  | @extend priorCount priorProgram neuron priorActivations prior ih =>
      if before : target.val < priorCount then
        let priorIndex : Fin priorCount := ⟨target.val, before⟩
        have targetExact : target = priorIndex.castSucc := by
          apply Fin.ext
          rfl
        rw [targetExact, SizedActivations.read_snoc_castSucc]
        unfold NetworkProgram.neuronAt NativeTrace.activationsBefore
        have castBefore : (priorIndex.castSucc).val < priorCount :=
          priorIndex.isLt
        rw [dif_pos castBefore, dif_pos castBefore]
        exact ih priorIndex
      else
        have valueExact : target.val = priorCount :=
          Nat.eq_of_lt_succ_of_not_lt target.isLt before
        have targetExact : target = Fin.last priorCount := by
          apply Fin.ext
          exact valueExact
        rw [targetExact, SizedActivations.read_snoc_last]
        unfold NetworkProgram.neuronAt NativeTrace.activationsBefore
        have lastNotBefore : ¬(Fin.last priorCount).val < priorCount :=
          Nat.lt_irrefl priorCount
        rw [dif_neg lastNotBefore, dif_neg lastNotBefore]

def executeWithTrace (program : NetworkProgram inputCount produced)
    (inputs : SizedActivations inputCount) :
    Sigma (fun activations : SizedActivations produced =>
      NativeTrace inputs program activations) :=
  match program with
  | .empty => ⟨SizedActivations.empty, .empty⟩
  | .extend prior neuron =>
      let executed := executeWithTrace prior inputs
      ⟨SizedActivations.snoc executed.1
          (fireNeuron neuron inputs executed.1),
        .extend executed.2⟩

def executeProgram (program : NetworkProgram inputCount produced)
    (inputs : SizedActivations inputCount) : SizedActivations produced :=
  (executeWithTrace program inputs).1

structure NativeRun {inputCount produced : Nat}
    (program : NetworkProgram inputCount produced) where
  private mk ::
  inputs : SizedActivations inputCount
  activations : SizedActivations produced
  trace : NativeTrace inputs program activations

def NativeSystem.run (system : NativeSystem Input Proposal) (input : Input) :
    NativeRun system.program :=
  let executed := executeWithTrace system.program (system.encode input)
  NativeRun.mk (system.encode input) executed.1 executed.2

def NativeSystem.outputValues
    (system : NativeSystem Input Proposal) (input : Input) : List Activation :=
  readOutputs system.outputs (system.run input).activations

def NativeSystem.proposal
    (system : NativeSystem Input Proposal) (input : Input) : Proposal :=
  system.decode (system.outputValues input)

theorem run_output_exact (system : NativeSystem Input Proposal) (input : Input) :
    system.outputValues input =
      readOutputs system.outputs
        (executeProgram system.program (system.encode input)) := rfl

theorem run_trace_exact (system : NativeSystem Input Proposal) (input : Input) :
    (system.run input).trace =
      (executeWithTrace system.program (system.encode input)).2 := rfl

end ConstitutiveSearch.NativeMechanism
/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.NativeMechanism.NativeTrace
#print axioms ConstitutiveSearch.NativeMechanism.NativeTrace.activationsBefore
#print axioms ConstitutiveSearch.NativeMechanism.NativeTrace.activationsBefore_read_exact
#print axioms ConstitutiveSearch.NativeMechanism.NativeTrace.neuron_output_exact
#print axioms ConstitutiveSearch.NativeMechanism.executeWithTrace
#print axioms ConstitutiveSearch.NativeMechanism.executeProgram
#print axioms ConstitutiveSearch.NativeMechanism.NativeRun
#print axioms ConstitutiveSearch.NativeMechanism.NativeSystem.run
#print axioms ConstitutiveSearch.NativeMechanism.run_output_exact
#print axioms ConstitutiveSearch.NativeMechanism.run_trace_exact
/- AXIOM_AUDIT_END -/
