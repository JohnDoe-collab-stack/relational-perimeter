import RelationalPerimeter.Agents.ContinuationSignatures.PositiveDirectedComposition

set_option autoImplicit false
namespace PositiveDirectedCompositionRegression
open ConstitutiveSearch ConstitutiveSearch.ContinuationSignatures
open SAT EndogenousDecomposition

variable {state : CausalConstitutiveState}
  {run : CausalConstitutiveStageExecution state}
  (role : RelationalConstitutiveRoleStage run)

theorem source_occurrences_remain_distinct :
    positiveDirectedSourceAccepted role ≠
      positiveDirectedTargetAccepted role :=
  positiveDirectedAcceptedSources_ne role

theorem indexed_source_positions_retain_that_distinction :
    positiveDirectedAcceptedSource role .source ≠
      positiveDirectedAcceptedSource role .target :=
  positiveDirectedIndexedAcceptedSources_ne role

theorem close_is_a_real_phase_change :
    positiveDirectedNext role ⟨.source, .active⟩ .close =
      ⟨.source, .terminal⟩ :=
  positiveDirectedCloseChangesPhase role .source

theorem initial_sources_remain_distinct :
    positiveDirectedSourceInitial role ≠ positiveDirectedTargetInitial role :=
  positiveDirectedInitialSources_ne role

theorem terminal_sources_remain_distinct :
    positiveDirectedSourceTerminal role ≠ positiveDirectedTargetTerminal role :=
  positiveDirectedTerminals_ne role

theorem active_memories_remain_distinct :
    positiveDirectedProject role (positiveDirectedSourceInitial role) ≠
      positiveDirectedProject role (positiveDirectedTargetInitial role) :=
  positiveDirectedActiveMemories_ne role

theorem grouping_is_nonempty :
    (positiveDirectedGrouping role).requests ≠ [] :=
  (positiveDirectedGrouping role).nonempty

theorem terminal_memory_collision_is_computed :
    positiveDirectedProject role (positiveDirectedSourceTerminal role) =
      positiveDirectedProject role (positiveDirectedTargetTerminal role) :=
  positiveDirectedTerminalProjectionsEqual role

theorem event_traces_preserve_the_positions :
    (positiveDirectedGrouping role).leftEvents ≠
      (positiveDirectedGrouping role).rightEvents :=
  positiveDirectedEventTracesDistinct role

theorem selected_readout_equality_is_produced :
    positiveDirectedProducedBit role .source =
      positiveDirectedProducedBit role .target :=
  positiveDirectedProducedBitsEqual role

def directed_transport_is_computed := positiveDirectedTerminalTransport role

def transported_witness_is_constructed := positiveDirectedTransportedWitness role

theorem transported_witness_is_exact :
    (transported_witness_is_constructed role).1 =
      positiveDirectedProducedBit role .target :=
  positiveDirectedTransportedWitness_exact role

end PositiveDirectedCompositionRegression
/- AXIOM_AUDIT_BEGIN -/
#print axioms PositiveDirectedCompositionRegression.source_occurrences_remain_distinct
#print axioms PositiveDirectedCompositionRegression.indexed_source_positions_retain_that_distinction
#print axioms PositiveDirectedCompositionRegression.close_is_a_real_phase_change
#print axioms PositiveDirectedCompositionRegression.initial_sources_remain_distinct
#print axioms PositiveDirectedCompositionRegression.terminal_sources_remain_distinct
#print axioms PositiveDirectedCompositionRegression.active_memories_remain_distinct
#print axioms PositiveDirectedCompositionRegression.grouping_is_nonempty
#print axioms PositiveDirectedCompositionRegression.terminal_memory_collision_is_computed
#print axioms PositiveDirectedCompositionRegression.event_traces_preserve_the_positions
#print axioms PositiveDirectedCompositionRegression.selected_readout_equality_is_produced
#print axioms PositiveDirectedCompositionRegression.directed_transport_is_computed
#print axioms PositiveDirectedCompositionRegression.transported_witness_is_constructed
#print axioms PositiveDirectedCompositionRegression.transported_witness_is_exact
/- AXIOM_AUDIT_END -/
