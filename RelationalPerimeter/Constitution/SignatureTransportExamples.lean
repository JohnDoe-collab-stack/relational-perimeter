import RelationalPerimeter.Constitution.SignatureTransport

namespace RelationalPerimeter.Constitution.SignatureTransportExamples

def boolFlip : ExactTypeTransport Bool Bool :=
  { forward := Bool.not
    backward := Bool.not
    forwardBackward := fun value => by cases value <;> rfl
    backwardForward := fun value => by cases value <;> rfl }

def boolSignature : ConstitutiveSignature :=
  ⟨Bool, Bool, fun _ _ => Bool, Bool, fun _ => Bool⟩

def flip : ConstitutiveSignatureTransport boolSignature boolSignature :=
  { explicit := boolFlip
    implicit := boolFlip
    difference := boolFlip
    compatibility := fun _ _ => boolFlip
    provenance := fun _ => boolFlip }

def inhabitedSignature : ConstitutiveSignature :=
  ⟨Bool, Bool, fun _ _ => Unit, Bool, fun _ => Unit⟩

def emptySignature : ConstitutiveSignature :=
  ⟨Bool, Bool, fun _ _ => Empty, Bool, fun _ => Unit⟩

theorem same_explicit_sorts : inhabitedSignature.Explicit = emptySignature.Explicit := rfl

theorem same_implicit_sorts : inhabitedSignature.Implicit = emptySignature.Implicit := rfl

theorem same_difference_sorts : inhabitedSignature.Difference = emptySignature.Difference := rfl

theorem no_family_transport :
    ConstitutiveSignatureTransport inhabitedSignature emptySignature → False :=
  fun transport => nomatch (transport.compatibility false false).forward ()

theorem no_family_transport_nonempty :
    Nonempty (ConstitutiveSignatureTransport inhabitedSignature emptySignature) → False :=
  fun ⟨transport⟩ => no_family_transport transport

def selectedBoundary : ConstitutiveBoundary :=
  { Explicit := Bool
    Implicit := Bool
    Compatible := fun _ _ => Bool
    Difference := Bool
    Provenance := fun _ => Bool
    source := false
    target := false
    junction := true
    difference := false
    provenance := true }

def junctionSwap : ConstitutiveSignatureTransport selectedBoundary.signature selectedBoundary.signature :=
  { explicit := .reflexive _
    implicit := .reflexive _
    difference := .reflexive _
    compatibility := fun _ _ => boolFlip
    provenance := fun _ => .reflexive _ }

def provenanceSwap : ConstitutiveSignatureTransport selectedBoundary.signature selectedBoundary.signature :=
  { explicit := .reflexive _
    implicit := .reflexive _
    difference := .reflexive _
    compatibility := fun _ _ => .reflexive _
    provenance := fun _ => boolFlip }

theorem junction_swap_indices : junctionSwap.implicit.forward selectedBoundary.source = selectedBoundary.source ∧
    junctionSwap.explicit.forward selectedBoundary.target = selectedBoundary.target ∧
    junctionSwap.difference.forward selectedBoundary.difference = selectedBoundary.difference := ⟨rfl, rfl, rfl⟩

theorem junction_swap_changes_choice :
    (junctionSwap.compatibilityAt (i := false) (e := false) rfl rfl).forward selectedBoundary.junction ≠ selectedBoundary.junction := by
  intro equality
  cases equality

theorem junction_swap_keeps_provenance :
    (junctionSwap.provenanceAt (d := false) rfl).forward selectedBoundary.provenance = selectedBoundary.provenance := rfl

theorem provenance_swap_keeps_junction :
    (provenanceSwap.compatibilityAt (i := false) (e := false) rfl rfl).forward selectedBoundary.junction = selectedBoundary.junction := rfl

theorem provenance_swap_changes_choice :
    (provenanceSwap.provenanceAt (d := false) rfl).forward selectedBoundary.provenance ≠ selectedBoundary.provenance := by
  intro equality
  cases equality

def movedBoundary : ConstitutiveBoundary :=
  { Explicit := Bool
    Implicit := Bool
    Compatible := fun _ _ => Bool
    Difference := Bool
    Provenance := fun _ => Bool
    source := true
    target := true
    junction := false
    difference := true
    provenance := false }

def selectedRestriction : BoundaryTransport selectedBoundary movedBoundary :=
  flip.restrict (B := selectedBoundary) (C := movedBoundary) rfl rfl rfl rfl rfl

theorem restriction_junction : selectedRestriction.junction.forward selectedBoundary.junction =
    movedBoundary.junction := selectedRestriction.junctionExact

theorem restriction_provenance : selectedRestriction.provenance.forward selectedBoundary.provenance =
    movedBoundary.provenance := selectedRestriction.provenanceExact

theorem restriction_junction_return (w : selectedBoundary.Compatible selectedBoundary.source selectedBoundary.target) :
    selectedRestriction.junction.backward (selectedRestriction.junction.forward w) = w :=
  selectedRestriction.junction.forwardBackward w

theorem restriction_provenance_return (w : movedBoundary.Provenance movedBoundary.difference) :
    selectedRestriction.provenance.forward (selectedRestriction.provenance.backward w) = w :=
  selectedRestriction.provenance.backwardForward w

theorem unselected_compatibility : (flip.compatibility true false).forward false = true := rfl

theorem unselected_provenance : (flip.provenance true).forward false = true := rfl

theorem inverse_unselected_compatibility :
    (flip.reverse.compatibility false true).forward ((flip.compatibility true false).forward false) = false := rfl

theorem inverse_unselected_provenance :
    (flip.reverse.provenance false).forward ((flip.provenance true).forward false) = false := rfl

theorem composed_unselected_compatibility :
    ((flip.compose flip).compatibility true false).forward false = false := rfl

theorem composed_unselected_provenance : ((flip.compose flip).provenance true).forward false = false := rfl

end RelationalPerimeter.Constitution.SignatureTransportExamples

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Constitution.SignatureTransportExamples.boolFlip
#print axioms RelationalPerimeter.Constitution.SignatureTransportExamples.boolSignature
#print axioms RelationalPerimeter.Constitution.SignatureTransportExamples.flip
#print axioms RelationalPerimeter.Constitution.SignatureTransportExamples.inhabitedSignature
#print axioms RelationalPerimeter.Constitution.SignatureTransportExamples.emptySignature
#print axioms RelationalPerimeter.Constitution.SignatureTransportExamples.same_explicit_sorts
#print axioms RelationalPerimeter.Constitution.SignatureTransportExamples.same_implicit_sorts
#print axioms RelationalPerimeter.Constitution.SignatureTransportExamples.same_difference_sorts
#print axioms RelationalPerimeter.Constitution.SignatureTransportExamples.no_family_transport
#print axioms RelationalPerimeter.Constitution.SignatureTransportExamples.no_family_transport_nonempty
#print axioms RelationalPerimeter.Constitution.SignatureTransportExamples.selectedBoundary
#print axioms RelationalPerimeter.Constitution.SignatureTransportExamples.junctionSwap
#print axioms RelationalPerimeter.Constitution.SignatureTransportExamples.provenanceSwap
#print axioms RelationalPerimeter.Constitution.SignatureTransportExamples.junction_swap_indices
#print axioms RelationalPerimeter.Constitution.SignatureTransportExamples.junction_swap_changes_choice
#print axioms RelationalPerimeter.Constitution.SignatureTransportExamples.junction_swap_keeps_provenance
#print axioms RelationalPerimeter.Constitution.SignatureTransportExamples.provenance_swap_keeps_junction
#print axioms RelationalPerimeter.Constitution.SignatureTransportExamples.provenance_swap_changes_choice
#print axioms RelationalPerimeter.Constitution.SignatureTransportExamples.movedBoundary
#print axioms RelationalPerimeter.Constitution.SignatureTransportExamples.selectedRestriction
#print axioms RelationalPerimeter.Constitution.SignatureTransportExamples.restriction_junction
#print axioms RelationalPerimeter.Constitution.SignatureTransportExamples.restriction_provenance
#print axioms RelationalPerimeter.Constitution.SignatureTransportExamples.restriction_junction_return
#print axioms RelationalPerimeter.Constitution.SignatureTransportExamples.restriction_provenance_return
#print axioms RelationalPerimeter.Constitution.SignatureTransportExamples.unselected_compatibility
#print axioms RelationalPerimeter.Constitution.SignatureTransportExamples.unselected_provenance
#print axioms RelationalPerimeter.Constitution.SignatureTransportExamples.inverse_unselected_compatibility
#print axioms RelationalPerimeter.Constitution.SignatureTransportExamples.inverse_unselected_provenance
#print axioms RelationalPerimeter.Constitution.SignatureTransportExamples.composed_unselected_compatibility
#print axioms RelationalPerimeter.Constitution.SignatureTransportExamples.composed_unselected_provenance
/- AXIOM_AUDIT_END -/
