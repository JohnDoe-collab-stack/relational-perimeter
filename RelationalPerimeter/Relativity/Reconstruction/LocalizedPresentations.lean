import RelationalPerimeter.Relativity.Production.ConstitutedEncounters
import RelationalPerimeter.Relativity.Production.InteractionDescriptionAgreement

/-!
# Local presentations formed from an admitted coupling

The origin is a stored joint production, not a pre-existing geometrical point.
Participant selection reads its actual consumed port. Description paths carry
that determination without replay; attached records remain separately readable.
This is a finite local presentation in the declared coupling model. It does
not yet define the continuous domain or coordinates of R4-R7.
-/
set_option genInjectivity false
namespace RelationalPerimeter.Relativity.Reconstruction
open RelationalPerimeter.Relativity.Production
open RelationalPerimeter.Relativity.Production.Encounter
open ConstitutiveSearch.Resources

structure LocalizedPresentation {source admitted}
    (production : EncounterProduction source admitted) (current : RecurringCursor) where
  participant : Port
  path : DescriptionPath production.head.successor current

def LocalizedPresentation.attachment {source admitted production current}
    (presentation : @LocalizedPresentation source admitted production current) :=
  match presentation.participant with
  | .left => InteractionAttachment.first production.head presentation.path
  | .right => InteractionAttachment.second production.head presentation.path

def LocalizedPresentation.location {source admitted production current}
    (presentation : @LocalizedPresentation source admitted production current) : Ref current.kinds .reading :=
  presentation.attachment.anchor

def AttachedEffects {source admitted production current}
    (presentation : @LocalizedPresentation source admitted production current) : SignalRecord :=
  presentation.attachment.effects

def localizeParticipant {source admitted} (production : EncounterProduction source admitted)
    (participant : Port) : LocalizedPresentation production production.head.successor := ⟨participant, .root⟩

def LocalizedPresentation.reexpress {source admitted production current target}
    (presentation : @LocalizedPresentation source admitted production current)
    (raccord : AddressedRecurringRaccord current target) : LocalizedPresentation production target :=
  ⟨presentation.participant, .reexpressed presentation.path raccord⟩

def LocalizedPresentation.prolong {source admitted production} {current target : State}
    (presentation : @LocalizedPresentation source admitted production current.cursor)
    (history : Encounter.History current target) : LocalizedPresentation production target.cursor :=
  ⟨presentation.participant, history.describe presentation.path⟩

theorem localized_location_exact {source admitted production current}
    (presentation : @LocalizedPresentation source admitted production current) :
    presentation.location = presentation.path.reference (comparisonAnchor production.head) := by
  rcases presentation with ⟨participant, path⟩
  cases participant <;> rfl

theorem localized_reexpress_location {source admitted production current target}
    (presentation : @LocalizedPresentation source admitted production current)
    (raccord : AddressedRecurringRaccord current target) :
    (presentation.reexpress raccord).location = raccord.constitution.references.forward presentation.location := by
  rcases presentation with ⟨participant, path⟩
  cases participant <;> rfl

theorem localized_reexpress_effects {source admitted production current target}
    (presentation : @LocalizedPresentation source admitted production current)
    (raccord : AddressedRecurringRaccord current target) :
    AttachedEffects (presentation.reexpress raccord) = AttachedEffects presentation := by
  rcases presentation with ⟨participant, path⟩
  cases participant with
  | left => exact attached_reexpress_effects (InteractionAttachment.first production.head path) raccord
  | right => exact attached_reexpress_effects (InteractionAttachment.second production.head path) raccord

theorem localized_prolong_location {source admitted production} {current target : State}
    (presentation : @LocalizedPresentation source admitted production current.cursor)
    (history : Encounter.History current target) :
    (presentation.prolong history).location = history.transport.references presentation.location := by
  rw [localized_location_exact, localized_location_exact]
  exact history_description_exact presentation.path history _

theorem localized_prolong_effects {source admitted production} {current target : State}
    (presentation : @LocalizedPresentation source admitted production current.cursor)
    (history : Encounter.History current target) :
    AttachedEffects (presentation.prolong history) = AttachedEffects presentation := by
  rcases presentation with ⟨participant, path⟩
  cases participant with
  | left => exact attached_prolong_effects (InteractionAttachment.first production.head path) history.resources
  | right => exact attached_prolong_effects (InteractionAttachment.second production.head path) history.resources

theorem localized_return_location {source admitted production current target}
    (presentation : @LocalizedPresentation source admitted production current)
    (raccord : AddressedRecurringRaccord current target) :
    ((presentation.reexpress raccord).reexpress raccord.reverse).location = presentation.location := by
  rw [localized_reexpress_location, localized_reexpress_location]
  exact raccord.constitution.references.forwardBackward _

theorem localized_return_effects {source admitted production current target}
    (presentation : @LocalizedPresentation source admitted production current)
    (raccord : AddressedRecurringRaccord current target) :
    AttachedEffects ((presentation.reexpress raccord).reexpress raccord.reverse) = AttachedEffects presentation :=
  (localized_reexpress_effects _ _).trans (localized_reexpress_effects _ _)

theorem localized_sources_distinct {source admitted} (production : EncounterProduction source admitted) :
    (localizeParticipant production .left).attachment.readingReference ≠
      (localizeParticipant production .right).attachment.readingReference := encounter_sources_distinct production

theorem differing_effects_distinguish_presentations {source admitted production current}
    (one two : @LocalizedPresentation source admitted production current)
    (different : AttachedEffects one ≠ AttachedEffects two) : one ≠ two :=
  fun same => different (congrArg AttachedEffects same)

theorem localized_prolong_compose {source admitted production} {current middle target : State}
    (presentation : @LocalizedPresentation source admitted production current.cursor)
    (one : Encounter.History current middle) (two : Encounter.History middle target) :
    (presentation.prolong (StrongPerimetralTurning.History.append one two)).location =
      ((presentation.prolong one).prolong two).location := by
  rw [localized_prolong_location, localized_prolong_location, localized_prolong_location]
  exact history_transport_append one two presentation.location

end RelationalPerimeter.Relativity.Reconstruction
/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Relativity.Reconstruction.LocalizedPresentation
#print axioms RelationalPerimeter.Relativity.Reconstruction.AttachedEffects
#print axioms RelationalPerimeter.Relativity.Reconstruction.localizeParticipant
#print axioms RelationalPerimeter.Relativity.Reconstruction.localized_location_exact
#print axioms RelationalPerimeter.Relativity.Reconstruction.localized_reexpress_location
#print axioms RelationalPerimeter.Relativity.Reconstruction.localized_reexpress_effects
#print axioms RelationalPerimeter.Relativity.Reconstruction.localized_prolong_location
#print axioms RelationalPerimeter.Relativity.Reconstruction.localized_prolong_effects
#print axioms RelationalPerimeter.Relativity.Reconstruction.localized_return_location
#print axioms RelationalPerimeter.Relativity.Reconstruction.localized_return_effects
#print axioms RelationalPerimeter.Relativity.Reconstruction.localized_sources_distinct
#print axioms RelationalPerimeter.Relativity.Reconstruction.differing_effects_distinguish_presentations
#print axioms RelationalPerimeter.Relativity.Reconstruction.localized_prolong_compose
/- AXIOM_AUDIT_END -/
