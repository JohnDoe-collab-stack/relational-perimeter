import RelationalPerimeter.Mechanisms.Native.Explanation

set_option genInjectivity false
namespace Tests.Mechanisms.NativeExecutionRegression
open ConstitutiveSearch.NativeMechanism

def inputZero : Fin 2 := ⟨0, Nat.zero_lt_succ 1⟩
def inputOne : Fin 2 := ⟨1, Nat.lt_add_one 1⟩
def firstNeuron : Fin 1 := ⟨0, Nat.zero_lt_succ 0⟩
def permissionOutput : Fin 2 := ⟨0, Nat.zero_lt_succ 1⟩
def outputNeuron : Fin 2 := ⟨1, Nat.lt_add_one 1⟩

def encodePair (input : Bool × Bool) : SizedActivations 2 :=
  { values := [asActivation input.1, asActivation input.2]
    lengthExact := rfl }

def permissionNeuron : NeuronSpec 2 0 :=
  { inputs := [{ source := .receivedInput inputZero, weight := 1 }]
    bias := 0
    threshold := ⟨1⟩ }

def permissionProgram : NetworkProgram 2 1 :=
  .extend .empty permissionNeuron

def conjunctionNeuron : NeuronSpec 2 1 :=
  { inputs :=
      [{ source := .priorNeuron firstNeuron, weight := 1 },
       { source := .receivedInput inputOne, weight := 1 }]
    bias := 0
    threshold := ⟨2⟩ }

def conjunctionProgram : NetworkProgram 2 2 :=
  .extend permissionProgram conjunctionNeuron

def outputPorts : OutputPorts 2 :=
  { sources := [outputNeuron]
    nonempty := by intro impossible; cases impossible }

def onlyOutputPort : Fin outputPorts.sources.length := ⟨0, by decide⟩

def decodeOutput : List Activation -> Bool
  | [] => false
  | value :: _ => decide (value ≠ 0)

def exampleSystem : NativeSystem (Bool × Bool) Bool :=
  { inputCount := 2
    producedCount := 2
    encode := encodePair
    program := conjunctionProgram
    outputs := outputPorts
    decode := decodeOutput }

theorem accepted_pair : exampleSystem.proposal (true, true) = true := rfl

theorem rejected_without_permission :
    exampleSystem.proposal (false, true) = false := rfl

theorem rejected_without_context :
    exampleSystem.proposal (true, false) = false := rfl

def permissionIntervention :
    Intervention (exampleSystem.run (true, true)) :=
  { focus := .neuron permissionOutput
    replacement := 0
    changesValue := by decide }

def permissionIntervenedActivations : SizedActivations 2 :=
  executeIntervened permissionIntervention

theorem intervention_changes_proposal :
    exampleSystem.decode
        (intervenedOutputs exampleSystem (true, true)
          permissionIntervention) = false := rfl

theorem permissionTargetChange :
    ChangesTarget (exampleSystem.run (true, true)) permissionIntervention
      exampleSystem.outputs :=
  { different := by decide }

theorem permissionProposalChange :
    ChangesProposal exampleSystem (true, true) permissionIntervention :=
  { different := by decide }

def permissionToOutput :
    ReadsFrom (exampleSystem.run (true, true))
      (.neuronOutput permissionOutput) (.neuronOutput outputNeuron) :=
  .executedEdge outputNeuron
    { source := .priorNeuron firstNeuron, weight := 1 }
    (by
      change
        ({ source := .priorNeuron firstNeuron, weight := 1 } :
          WeightedInput 2 1) ∈
          [{ source := .priorNeuron firstNeuron, weight := 1 },
           { source := .receivedInput inputOne, weight := 1 }]
      exact List.Mem.head _)

theorem outputOccurrenceChanged :
    OccurrenceChanged permissionIntervention (.neuronOutput outputNeuron) :=
  { different := by decide }

def permissionPropagation :
    NontrivialExecutedChangePath permissionIntervention
      (.neuronOutput outputNeuron) :=
  .step .origin permissionToOutput outputOccurrenceChanged

def permissionReachesOutput :
    Reaches (exampleSystem.run (true, true))
      (.neuronOutput permissionOutput) (.neuronOutput outputNeuron) :=
  .step permissionToOutput (.refl _)

def outputCircuit :
    ConstructedCircuit (exampleSystem.run (true, true))
      (.neuronOutput outputNeuron) :=
  reconstructCircuit (exampleSystem.run (true, true))
    (.neuronOutput outputNeuron)

def permissionCircuitMember :
    outputCircuit.Contains (.neuronOutput permissionOutput) :=
  reconstructed_path_to_member (exampleSystem.run (true, true))
    (.neuronOutput outputNeuron) (.neuronOutput permissionOutput)
    permissionReachesOutput

def permissionCircuitPath :
    Reaches (exampleSystem.run (true, true))
      (.neuronOutput permissionOutput) (.neuronOutput outputNeuron) :=
  reconstructed_member_to_path (exampleSystem.run (true, true))
    (.neuronOutput outputNeuron) (.neuronOutput permissionOutput)
    permissionCircuitMember

def permissionCausalRole :
    CausalRole exampleSystem (true, true)
      (.neuronOutput permissionOutput) :=
  { intervention := permissionIntervention
    focusExact := rfl
    output := onlyOutputPort
    propagation := permissionPropagation
    targetChange := permissionTargetChange
    proposalChange := permissionProposalChange }

def permissionExecutedPath :
    Sigma fun output : Fin exampleSystem.outputs.sources.length =>
      Reaches (exampleSystem.run (true, true))
        (.neuronOutput permissionOutput)
        (.neuronOutput (exampleSystem.outputs.sources.get output)) :=
  causal_role_has_executed_path permissionCausalRole

def permissionExplanation :
    CausalExplanation exampleSystem (true, true)
      (.neuronOutput permissionOutput) :=
  explainCausalRole permissionCausalRole

def permissionExplainedPath :
    Reaches (exampleSystem.run (true, true))
      (.neuronOutput permissionOutput) (.neuronOutput outputNeuron) :=
  permissionExplanation.executedPath

def permissionContribution :
    ContributesTo exampleSystem (true, true)
      (.neuronOutput permissionOutput)
      (exampleSystem.proposalOccurrence (true, true)) :=
  { role := permissionCausalRole
    targetExact := rfl }

theorem trace_is_the_executed_trace :
    (exampleSystem.run (true, true)).trace =
      (executeWithTrace exampleSystem.program
        (exampleSystem.encode (true, true))).2 :=
  run_trace_exact exampleSystem (true, true)

def outputFormation :
    FormedBy (exampleSystem.run (true, true)) (.neuronOutput outputNeuron) :=
  formedBy (exampleSystem.run (true, true)) (.neuronOutput outputNeuron)

end Tests.Mechanisms.NativeExecutionRegression
/- AXIOM_AUDIT_BEGIN -/
#print axioms Tests.Mechanisms.NativeExecutionRegression.accepted_pair
#print axioms Tests.Mechanisms.NativeExecutionRegression.rejected_without_permission
#print axioms Tests.Mechanisms.NativeExecutionRegression.rejected_without_context
#print axioms Tests.Mechanisms.NativeExecutionRegression.permissionIntervention
#print axioms Tests.Mechanisms.NativeExecutionRegression.permissionIntervenedActivations
#print axioms Tests.Mechanisms.NativeExecutionRegression.intervention_changes_proposal
#print axioms Tests.Mechanisms.NativeExecutionRegression.permissionTargetChange
#print axioms Tests.Mechanisms.NativeExecutionRegression.permissionProposalChange
#print axioms Tests.Mechanisms.NativeExecutionRegression.permissionToOutput
#print axioms Tests.Mechanisms.NativeExecutionRegression.outputOccurrenceChanged
#print axioms Tests.Mechanisms.NativeExecutionRegression.permissionPropagation
#print axioms Tests.Mechanisms.NativeExecutionRegression.permissionReachesOutput
#print axioms Tests.Mechanisms.NativeExecutionRegression.outputCircuit
#print axioms Tests.Mechanisms.NativeExecutionRegression.permissionCircuitMember
#print axioms Tests.Mechanisms.NativeExecutionRegression.permissionCircuitPath
#print axioms Tests.Mechanisms.NativeExecutionRegression.permissionCausalRole
#print axioms Tests.Mechanisms.NativeExecutionRegression.permissionExecutedPath
#print axioms Tests.Mechanisms.NativeExecutionRegression.permissionExplanation
#print axioms Tests.Mechanisms.NativeExecutionRegression.permissionExplainedPath
#print axioms Tests.Mechanisms.NativeExecutionRegression.permissionContribution
#print axioms Tests.Mechanisms.NativeExecutionRegression.trace_is_the_executed_trace
#print axioms Tests.Mechanisms.NativeExecutionRegression.outputFormation
/- AXIOM_AUDIT_END -/
