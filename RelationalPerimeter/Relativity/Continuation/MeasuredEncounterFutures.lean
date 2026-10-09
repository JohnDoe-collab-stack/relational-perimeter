import RelationalPerimeter.Relativity.Reconstruction.MeasuredLocationGrouping
import RelationalPerimeter.Relativity.Continuation.EncounterFutures

/-!
# Measured encounters retain the distinctions exposed by the declared contract

This uses the existing rich-effects future contract without narrowing it.
The same attached-effects request distinguishes the paths after any actual
finite continuation, even though both participants have one local encounter
agreement. No physical memory reduction or ideal-point coverage is inferred.
-/
set_option genInjectivity false
namespace RelationalPerimeter.Relativity.Continuation.Encounter
open RelationalPerimeter.Relativity.Production
open RelationalPerimeter.Relativity.Reconstruction
open ConstitutiveSearch.ContinuationSignatures

theorem measured_effects_forbid_rich_grouping {source} (result : Production.Encounter.Measurement source)
    {target} (history : Production.Encounter.History result.head.next target)
    (different : source.coupling.cursor.read source.reading.firstSignal ≠
      source.coupling.cursor.read source.reading.secondSignal) :
    ¬ FutureEquivalent (readerContract result.head)
      ⟨target, measuredFirst result history⟩ ⟨target, measuredSecond result history⟩ := by
  apply different_effects_forbid_rich_grouping
  intro same
  have exactEffects := measured_encounter_keeps_effects result history
  exact different (exactEffects.1.symm.trans (same.trans exactEffects.2))

theorem measured_requests_preserve_path_distinctions {source} (result : Production.Encounter.Measurement source)
    (requests : List Request)
    (different : source.coupling.cursor.read source.reading.firstSignal ≠
      source.coupling.cursor.read source.reading.secondSignal) :
    ¬ FutureEquivalent (readerContract result.head)
      ⟨(run result.head.next requests).state, measuredFirst result (run result.head.next requests).history⟩
      ⟨(run result.head.next requests).state, measuredSecond result (run result.head.next requests).history⟩ :=
  measured_effects_forbid_rich_grouping result _ different

/-- Refining a description of the old measurement does not narrow the rich
contract, even after subsequent requests and refusals at its actual endpoint. -/
theorem measured_description_futures_keep_distinctions {source result coarse}
    (description : @MeasuredDescriptionRun source result coarse) (requests : List Request)
    (different : source.coupling.cursor.read source.reading.firstSignal ≠
      source.coupling.cursor.read source.reading.secondSignal) :
    let suffix := run description.realization.state.coupling requests
    let history := StrongPerimetralTurning.History.append description.realization.chain.history suffix.history
    ¬ FutureEquivalent (readerContract result.head)
      ⟨suffix.state, measuredFirst result history⟩ ⟨suffix.state, measuredSecond result history⟩ :=
  measured_effects_forbid_rich_grouping result _ different

/-- The common selected-reader description is not an exact realization of
the rich contract. Its actual input participants still have a same-request
separator; no observation permission has been silently removed. -/
theorem grouped_measured_description_is_not_rich_equivalence {source result coarse}
    (description : @MeasuredDescriptionRun source result coarse)
    (different : source.coupling.cursor.read source.reading.firstSignal ≠
      source.coupling.cursor.read source.reading.secondSignal) :
    ¬ FutureEquivalent (readerContract result.head)
      ⟨description.realization.state.coupling, (measuredDescriptionPort description .left).presentation⟩
      ⟨description.realization.state.coupling, (measuredDescriptionPort description .right).presentation⟩ :=
  measured_effects_forbid_rich_grouping result description.realization.chain.history different

end RelationalPerimeter.Relativity.Continuation.Encounter
/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Relativity.Continuation.Encounter.measured_effects_forbid_rich_grouping
#print axioms RelationalPerimeter.Relativity.Continuation.Encounter.measured_requests_preserve_path_distinctions
#print axioms RelationalPerimeter.Relativity.Continuation.Encounter.measured_description_futures_keep_distinctions
#print axioms RelationalPerimeter.Relativity.Continuation.Encounter.grouped_measured_description_is_not_rich_equivalence
/- AXIOM_AUDIT_END -/
