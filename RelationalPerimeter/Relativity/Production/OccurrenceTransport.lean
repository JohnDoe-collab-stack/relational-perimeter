import RelationalPerimeter.Relativity.Production.PhysicalPrimitives
import ExactTypeTransport
import SegmentedResidualRole

/-! Exact old/fresh occurrence transport, before any numerical readout.
The residual-role hypotheses are closed on the actual typed-reference carrier.
This does not identify old resources whose numerical values happen to agree. -/
set_option genInjectivity false
namespace RelationalPerimeter.Relativity.Production
open ConstitutiveSearch.Resources

abbrev Occurrence (context : List Kind) := (kind : Kind) ×' Ref context kind

def oldOccurrence {context} (added : Kind) (occurrence : Occurrence context) :
    Occurrence (added :: context) := ⟨occurrence.1, .prior occurrence.2⟩

def freshOccurrence (context : List Kind) (added : Kind) : Occurrence (added :: context) :=
  ⟨added, .here⟩

def occurrenceSplit (context : List Kind) (added : Kind) :
    ExactTypeTransport (Occurrence context ⊕ Unit) (Occurrence (added :: context)) where
  forward := fun choice => match choice with
    | .inl old => oldOccurrence added old
    | .inr _ => freshOccurrence context added
  backward := fun occurrence => match occurrence with
    | ⟨_, .here⟩ => .inr ()
    | ⟨kind, .prior old⟩ => .inl ⟨kind, old⟩
  forwardBackward := by
    intro choice
    cases choice with
    | inl old => cases old; rfl
    | inr singleton => cases singleton; rfl
  backwardForward := by
    intro occurrence
    cases occurrence with
    | mk kind ref => cases ref <;> rfl

def internalOccurrenceRealization (context : List Kind) :
    SegmentedResidualRole.ExactInternalRealization (Occurrence context) (Occurrence context) :=
  ⟨id, id, fun _ => rfl, fun _ => rfl⟩

def freshRole : SegmentedResidualRole.ContractibleRole Unit :=
  ⟨(), fun singleton => by cases singleton; rfl⟩

def faithfulOccurrenceExtension (context : List Kind) (added : Kind) :
    SegmentedResidualRole.FaithfulExtension (Occurrence context) Unit
      (Occurrence context) Unit (Occurrence (added :: context))
      (internalOccurrenceRealization context) freshRole where
  embedOld := oldOccurrence added
  embedNew := fun _ => freshOccurrence context added
  oldNewDisjoint := by
    intro old singleton same
    have labelled := congrArg (occurrenceSplit context added).backward same
    cases old with
    | mk kind ref =>
      change (Sum.inl ⟨kind, ref⟩ : Occurrence context ⊕ Unit) = .inr () at labelled
      cases labelled
  embedNewInjective := by
    intro one two _
    cases one
    cases two
    rfl
  label := (occurrenceSplit context added).backward
  preservesInternal := fun _ => rfl
  labelFaithful := fun one two same =>
    ((occurrenceSplit context added).backwardForward one).symm.trans
      ((congrArg (occurrenceSplit context added).forward same).trans
        ((occurrenceSplit context added).backwardForward two))

def constitutedFreshRole (context : List Kind) (added : Kind) :=
  SegmentedResidualRole.positiveCore_hasUniqueResidualOccurrence
    (faithfulOccurrenceExtension context added).toResidualUniquenessKernel.toDeterminationCore ⟨()⟩

end RelationalPerimeter.Relativity.Production
/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Relativity.Production.oldOccurrence
#print axioms RelationalPerimeter.Relativity.Production.freshOccurrence
#print axioms RelationalPerimeter.Relativity.Production.occurrenceSplit
#print axioms RelationalPerimeter.Relativity.Production.internalOccurrenceRealization
#print axioms RelationalPerimeter.Relativity.Production.freshRole
#print axioms RelationalPerimeter.Relativity.Production.faithfulOccurrenceExtension
#print axioms RelationalPerimeter.Relativity.Production.constitutedFreshRole
/- AXIOM_AUDIT_END -/
