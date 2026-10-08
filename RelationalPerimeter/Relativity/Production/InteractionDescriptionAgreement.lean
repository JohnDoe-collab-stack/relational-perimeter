import RelationalPerimeter.Relativity.Production.InteractionAttachments

/-!
# Positive agreements between descriptions of one constituted interaction

An interaction agreement transports the actual fresh anchor. A rich agreement
also transports the participant's reception and signal. The same head indexes
both descriptions; equal values never supply that constitutive connection.
Readers restrict observations, not the memory or its unchanged future contract.
This remains instrumental agreement, not physical location agreement.
-/
set_option genInjectivity false
namespace RelationalPerimeter.Relativity.Production
open ConstitutiveSearch.Resources
open ConstitutiveSearch.ContinuationSignatures

def AddressedRecurringRaccord.identity (cursor : RecurringCursor) :
    AddressedRecurringRaccord cursor cursor :=
  ⟨.identity cursor, ⟨id, id, fun _ => rfl, fun _ => rfl, fun _ => rfl⟩⟩

def AddressedRecurringRaccord.compose {source middle target}
    (first : AddressedRecurringRaccord source middle)
    (second : AddressedRecurringRaccord middle target) : AddressedRecurringRaccord source target where
  constitution := {
    references := {
      forward := fun ref => second.constitution.references.forward (first.constitution.references.forward ref)
      backward := fun ref => first.constitution.references.backward (second.constitution.references.backward ref)
      forwardBackward := fun ref =>
        (congrArg first.constitution.references.backward
          (second.constitution.references.forwardBackward _)).trans
          (first.constitution.references.forwardBackward ref)
      backwardForward := fun ref =>
        (congrArg second.constitution.references.forward
          (first.constitution.references.backwardForward _)).trans
          (second.constitution.references.backwardForward ref) }
    reads := fun ref => (second.constitution.reads _).trans (first.constitution.reads ref)
    forwardArrival := fun arrival => second.constitution.forwardArrival (first.constitution.forwardArrival arrival)
    backwardArrival := fun arrival => first.constitution.backwardArrival (second.constitution.backwardArrival arrival)
    forwardUsed := fun edge => second.constitution.forwardUsed (first.constitution.forwardUsed edge)
    backwardUsed := fun edge => first.constitution.backwardUsed (second.constitution.backwardUsed edge) }
  addresses := {
    forward := fun address => second.addresses.forward (first.addresses.forward address)
    backward := fun address => first.addresses.backward (second.addresses.backward address)
    forwardBackward := fun address =>
      (congrArg first.addresses.backward (second.addresses.forwardBackward _)).trans
        (first.addresses.forwardBackward address)
    backwardForward := fun address =>
      (congrArg second.addresses.forward (first.addresses.backwardForward _)).trans
        (second.addresses.backwardForward address)
    positions := fun ref => (second.addresses.positions _).trans
      (congrArg second.addresses.forward (first.addresses.positions ref)) }

theorem addressed_composition_reference {source middle target}
    (first : AddressedRecurringRaccord source middle) (second : AddressedRecurringRaccord middle target)
    {kind} (ref : Ref source.kinds kind) :
    (first.compose second).constitution.references.forward ref =
      second.constitution.references.forward (first.constitution.references.forward ref) := rfl

theorem addressed_composition_associates {one two three four}
    (first : AddressedRecurringRaccord one two) (second : AddressedRecurringRaccord two three)
    (third : AddressedRecurringRaccord three four) {kind} (ref : Ref one.kinds kind) :
    ((first.compose second).compose third).constitution.references.forward ref =
      (first.compose (second.compose third)).constitution.references.forward ref := rfl

/-- Agreement of the interaction anchor only; it licenses no erasure of effects. -/
structure InteractionSiteAgreement {source pair head current target}
    (one : @InteractionAttachment source pair head current)
    (two : @InteractionAttachment source pair head target) where
  raccord : AddressedRecurringRaccord current target
  anchorExact : raccord.constitution.references.forward one.anchor = two.anchor

/-- Rich description agreement includes the exact participant occurrences. -/
structure AttachedDescriptionAgreement {source pair head current target}
    (one : @InteractionAttachment source pair head current)
    (two : @InteractionAttachment source pair head target) where
  raccord : AddressedRecurringRaccord current target
  anchorExact : raccord.constitution.references.forward one.anchor = two.anchor
  readingExact : raccord.constitution.references.forward one.readingReference = two.readingReference
  signalExact : raccord.constitution.references.forward one.signalReference = two.signalReference

def InteractionSiteAgreement.identity {source pair head current}
    (attached : @InteractionAttachment source pair head current) : InteractionSiteAgreement attached attached :=
  ⟨.identity current, rfl⟩

def InteractionSiteAgreement.reexpression {source pair head current target}
    (attached : @InteractionAttachment source pair head current)
    (raccord : AddressedRecurringRaccord current target) :
    InteractionSiteAgreement attached (attached.reexpress raccord) := ⟨raccord, rfl⟩

def InteractionSiteAgreement.participants {source : RecurringCursor} {pair : RecurringPair source}
    (head : RecurringProduction source (.compare pair)) {current}
    (path : DescriptionPath head.successor current) :
    InteractionSiteAgreement (InteractionAttachment.first head path) (InteractionAttachment.second head path) :=
  ⟨.identity current, participants_share_anchor head path⟩

def InteractionSiteAgreement.reverse {source pair head current target}
    {one : @InteractionAttachment source pair head current}
    {two : @InteractionAttachment source pair head target} (agreement : InteractionSiteAgreement one two) :
    InteractionSiteAgreement two one :=
  ⟨agreement.raccord.reverse,
    (congrArg agreement.raccord.constitution.references.backward agreement.anchorExact).symm.trans
      (agreement.raccord.constitution.references.forwardBackward _)⟩

def InteractionSiteAgreement.compose {source pair head current middle target}
    {one : @InteractionAttachment source pair head current}
    {two : @InteractionAttachment source pair head middle}
    {three : @InteractionAttachment source pair head target}
    (first : InteractionSiteAgreement one two) (second : InteractionSiteAgreement two three) :
    InteractionSiteAgreement one three :=
  ⟨first.raccord.compose second.raccord,
    (congrArg second.raccord.constitution.references.forward first.anchorExact).trans second.anchorExact⟩

def AttachedDescriptionAgreement.identity {source pair head current}
    (attached : @InteractionAttachment source pair head current) : AttachedDescriptionAgreement attached attached :=
  ⟨.identity current, rfl, rfl, rfl⟩

def AttachedDescriptionAgreement.reexpression {source pair head current target}
    (attached : @InteractionAttachment source pair head current)
    (raccord : AddressedRecurringRaccord current target) :
    AttachedDescriptionAgreement attached (attached.reexpress raccord) := ⟨raccord, rfl, rfl, rfl⟩

def AttachedDescriptionAgreement.site {source pair head current target}
    {one : @InteractionAttachment source pair head current}
    {two : @InteractionAttachment source pair head target} (agreement : AttachedDescriptionAgreement one two) :
    InteractionSiteAgreement one two := ⟨agreement.raccord, agreement.anchorExact⟩

def AttachedDescriptionAgreement.reverse {source pair head current target}
    {one : @InteractionAttachment source pair head current}
    {two : @InteractionAttachment source pair head target} (agreement : AttachedDescriptionAgreement one two) :
    AttachedDescriptionAgreement two one :=
  ⟨agreement.raccord.reverse,
    (congrArg agreement.raccord.constitution.references.backward agreement.anchorExact).symm.trans
      (agreement.raccord.constitution.references.forwardBackward _),
    (congrArg agreement.raccord.constitution.references.backward agreement.readingExact).symm.trans
      (agreement.raccord.constitution.references.forwardBackward _),
    (congrArg agreement.raccord.constitution.references.backward agreement.signalExact).symm.trans
      (agreement.raccord.constitution.references.forwardBackward _)⟩

def AttachedDescriptionAgreement.compose {source pair head current middle target}
    {one : @InteractionAttachment source pair head current}
    {two : @InteractionAttachment source pair head middle}
    {three : @InteractionAttachment source pair head target}
    (first : AttachedDescriptionAgreement one two) (second : AttachedDescriptionAgreement two three) :
    AttachedDescriptionAgreement one three :=
  ⟨first.raccord.compose second.raccord,
    (congrArg second.raccord.constitution.references.forward first.anchorExact).trans second.anchorExact,
    (congrArg second.raccord.constitution.references.forward first.readingExact).trans second.readingExact,
    (congrArg second.raccord.constitution.references.forward first.signalExact).trans second.signalExact⟩

theorem attached_agreement_effects {source pair head current target}
    {one : @InteractionAttachment source pair head current}
    {two : @InteractionAttachment source pair head target} (agreement : AttachedDescriptionAgreement one two) :
    two.effects = one.effects :=
  (congrArg (fun ref : Ref target.kinds .signal => target.read ref) agreement.signalExact).symm.trans
    (agreement.raccord.constitution.reads _)

theorem attached_agreement_reading {source pair head current target}
    {one : @InteractionAttachment source pair head current}
    {two : @InteractionAttachment source pair head target} (agreement : AttachedDescriptionAgreement one two) :
    target.read two.readingReference = current.read one.readingReference :=
  (congrArg (fun ref : Ref target.kinds .reading => target.read ref) agreement.readingExact).symm.trans
    (agreement.raccord.constitution.reads _)

theorem site_agreement_anchor_reading {source pair head current target}
    {one : @InteractionAttachment source pair head current}
    {two : @InteractionAttachment source pair head target} (agreement : InteractionSiteAgreement one two) :
    target.read two.anchor = current.read one.anchor :=
  (congrArg (fun ref : Ref target.kinds .reading => target.read ref) agreement.anchorExact).symm.trans
    (agreement.raccord.constitution.reads _)

theorem differing_effects_refute_rich_agreement {source pair head current target}
    (one : @InteractionAttachment source pair head current)
    (two : @InteractionAttachment source pair head target) (different : one.effects ≠ two.effects)
    (agreement : AttachedDescriptionAgreement one two) : False :=
  different (attached_agreement_effects agreement).symm

def InteractionAttachment.observe {source pair head current}
    (attached : @InteractionAttachment source pair head current) (readers : SignalReaders) : SignalObservation :=
  observeSignal readers attached.effects

theorem attached_observation_restrict {source pair head current}
    (attached : @InteractionAttachment source pair head current) {coarse fine}
    (refinement : ReaderRefinement coarse fine) :
    (attached.observe fine).restrict coarse = attached.observe coarse := restrict_signal_exact refinement _

theorem attached_observation_common_refinement {source pair head current}
    (attached : @InteractionAttachment source pair head current) (one two : SignalReaders) :
    (attached.observe (one.join two)).restrict one = attached.observe one ∧
      (attached.observe (one.join two)).restrict two = attached.observe two :=
  ⟨attached_observation_restrict attached (reader_left_in_join one two),
    attached_observation_restrict attached (reader_right_in_join one two)⟩

theorem attached_observation_prolong {source pair head current target}
    (attached : @InteractionAttachment source pair head current) (history : RecurringHistory current target)
    (readers : SignalReaders) : (attached.prolong history).observe readers = attached.observe readers :=
  congrArg (observeSignal readers) (attached_prolong_effects attached history)

theorem attached_observation_reexpress {source pair head current target}
    (attached : @InteractionAttachment source pair head current) (raccord : AddressedRecurringRaccord current target)
    (readers : SignalReaders) : (attached.reexpress raccord).observe readers = attached.observe readers :=
  congrArg (observeSignal readers) (attached_reexpress_effects attached raccord)

theorem attached_agreement_observations {source pair head current target}
    {one : @InteractionAttachment source pair head current}
    {two : @InteractionAttachment source pair head target} (agreement : AttachedDescriptionAgreement one two)
    (readers : SignalReaders) : two.observe readers = one.observe readers :=
  congrArg (observeSignal readers) (attached_agreement_effects agreement)

/-- Requests follow the evolving exact raccord; they are not compared as
unchanged address codes in two different presentations. -/
theorem attached_agreement_all_futures {source pair head current target}
    {one : @InteractionAttachment source pair head current}
    {two : @InteractionAttachment source pair head target} (agreement : AttachedDescriptionAgreement one two)
    (requests : List RecurringRequest) :
    recurringContract.outcome target (runSharedRecurring agreement.raccord requests).translated =
      recurringContract.outcome current requests := shared_recurring_all_futures agreement.raccord requests

theorem attached_joint_observations_exact {source pair head current target}
    (one : @InteractionAttachment source pair head current) (two : @InteractionAttachment source pair head target) :
    one.observe .full = two.observe .full ↔ one.effects = two.effects := joint_signal_readers_exact _ _

theorem attached_rich_return_reference {source pair head current target}
    {one : @InteractionAttachment source pair head current}
    {two : @InteractionAttachment source pair head target} (agreement : AttachedDescriptionAgreement one two)
    {kind} (ref : Ref current.kinds kind) :
    (agreement.compose agreement.reverse).raccord.constitution.references.forward ref = ref :=
  agreement.raccord.constitution.references.forwardBackward ref

end RelationalPerimeter.Relativity.Production
/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Relativity.Production.AddressedRecurringRaccord.identity
#print axioms RelationalPerimeter.Relativity.Production.AddressedRecurringRaccord.compose
#print axioms RelationalPerimeter.Relativity.Production.addressed_composition_reference
#print axioms RelationalPerimeter.Relativity.Production.addressed_composition_associates
#print axioms RelationalPerimeter.Relativity.Production.InteractionSiteAgreement
#print axioms RelationalPerimeter.Relativity.Production.AttachedDescriptionAgreement
#print axioms RelationalPerimeter.Relativity.Production.InteractionSiteAgreement.identity
#print axioms RelationalPerimeter.Relativity.Production.InteractionSiteAgreement.reexpression
#print axioms RelationalPerimeter.Relativity.Production.InteractionSiteAgreement.participants
#print axioms RelationalPerimeter.Relativity.Production.InteractionSiteAgreement.reverse
#print axioms RelationalPerimeter.Relativity.Production.InteractionSiteAgreement.compose
#print axioms RelationalPerimeter.Relativity.Production.AttachedDescriptionAgreement.identity
#print axioms RelationalPerimeter.Relativity.Production.AttachedDescriptionAgreement.reexpression
#print axioms RelationalPerimeter.Relativity.Production.AttachedDescriptionAgreement.site
#print axioms RelationalPerimeter.Relativity.Production.AttachedDescriptionAgreement.reverse
#print axioms RelationalPerimeter.Relativity.Production.AttachedDescriptionAgreement.compose
#print axioms RelationalPerimeter.Relativity.Production.attached_agreement_effects
#print axioms RelationalPerimeter.Relativity.Production.attached_agreement_reading
#print axioms RelationalPerimeter.Relativity.Production.site_agreement_anchor_reading
#print axioms RelationalPerimeter.Relativity.Production.differing_effects_refute_rich_agreement
#print axioms RelationalPerimeter.Relativity.Production.InteractionAttachment.observe
#print axioms RelationalPerimeter.Relativity.Production.attached_observation_restrict
#print axioms RelationalPerimeter.Relativity.Production.attached_observation_common_refinement
#print axioms RelationalPerimeter.Relativity.Production.attached_observation_prolong
#print axioms RelationalPerimeter.Relativity.Production.attached_observation_reexpress
#print axioms RelationalPerimeter.Relativity.Production.attached_agreement_observations
#print axioms RelationalPerimeter.Relativity.Production.attached_agreement_all_futures
#print axioms RelationalPerimeter.Relativity.Production.attached_joint_observations_exact
#print axioms RelationalPerimeter.Relativity.Production.attached_rich_return_reference
/- AXIOM_AUDIT_END -/
