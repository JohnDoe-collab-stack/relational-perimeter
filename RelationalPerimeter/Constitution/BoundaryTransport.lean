import RelationalPerimeter.Constitution.PositivePresentation
import ExactTypeTransport

set_option linter.checkUnivs false

/-!
# Exact transports of selected constitutive boundary data

This signature contains the closing source and target, the distinguished
closing compatibility, and the initial difference with its provenance. The
transports preserve those selected fibres and witnesses. They do not assert
preservation of every compatibility fibre or of a whole generated history.
-/

namespace RelationalPerimeter.Constitution

universe uE uI uK uD uP

structure ConstitutiveBoundary where
  Explicit : Type uE
  Implicit : Type uI
  Compatible : Implicit → Explicit → Type uK
  source : Implicit
  target : Explicit
  junction : Compatible source target
  Difference : Type uD
  Provenance : Difference → Type uP
  difference : Difference
  provenance : Provenance difference

def closingBoundary (P : StrongPerimetralTurning.PositiveCircularPresentation) :
    ConstitutiveBoundary :=
  { Explicit := P.Explicit
    Implicit := P.Implicit
    Compatible := P.Compatible
    source := P.perimeter.finalNode.implicit
    target := P.initialNode.explicit
    junction := P.finalJunction
    Difference := P.Difference
    Provenance := P.Provenance
    difference := P.initialNode.difference
    provenance := P.initialNode.provenance }

/- Exactness of the five carriers is deliberately separate from preservation
   of the three indices and of the two distinguished witnesses. -/
structure BoundaryCarrierTransport (B C : ConstitutiveBoundary) where
  explicit : ExactTypeTransport B.Explicit C.Explicit
  implicit : ExactTypeTransport B.Implicit C.Implicit
  difference : ExactTypeTransport B.Difference C.Difference
  junction : ExactTypeTransport
    (B.Compatible B.source B.target) (C.Compatible C.source C.target)
  provenance : ExactTypeTransport
    (B.Provenance B.difference) (C.Provenance C.difference)

structure BoundaryTransport (B C : ConstitutiveBoundary)
    extends BoundaryCarrierTransport B C where
  sourceExact : implicit.forward B.source = C.source
  targetExact : explicit.forward B.target = C.target
  differenceExact : difference.forward B.difference = C.difference
  junctionExact : junction.forward B.junction = C.junction
  provenanceExact : provenance.forward B.provenance = C.provenance

namespace BoundaryTransport

def identity (B : ConstitutiveBoundary) : BoundaryTransport B B :=
  { explicit := ExactTypeTransport.reflexive _
    implicit := ExactTypeTransport.reflexive _
    difference := ExactTypeTransport.reflexive _
    junction := ExactTypeTransport.reflexive _
    provenance := ExactTypeTransport.reflexive _
    sourceExact := rfl
    targetExact := rfl
    differenceExact := rfl
    junctionExact := rfl
    provenanceExact := rfl }

/- The inverse conservation laws are derived from the forward ones and the
   return laws; they are not independently prescribed payloads. -/
def reverse {B C : ConstitutiveBoundary} (transport : BoundaryTransport B C) :
    BoundaryTransport C B :=
  { explicit := transport.explicit.reverse
    implicit := transport.implicit.reverse
    difference := transport.difference.reverse
    junction := transport.junction.reverse
    provenance := transport.provenance.reverse
    sourceExact :=
      (congrArg transport.implicit.backward transport.sourceExact.symm).trans
        (transport.implicit.forwardBackward B.source)
    targetExact :=
      (congrArg transport.explicit.backward transport.targetExact.symm).trans
        (transport.explicit.forwardBackward B.target)
    differenceExact :=
      (congrArg transport.difference.backward transport.differenceExact.symm).trans
        (transport.difference.forwardBackward B.difference)
    junctionExact :=
      (congrArg transport.junction.backward transport.junctionExact.symm).trans
        (transport.junction.forwardBackward B.junction)
    provenanceExact :=
      (congrArg transport.provenance.backward transport.provenanceExact.symm).trans
        (transport.provenance.forwardBackward B.provenance) }

def compose {B C D : ConstitutiveBoundary}
    (first : BoundaryTransport B C) (second : BoundaryTransport C D) :
    BoundaryTransport B D :=
  { explicit := first.explicit.compose second.explicit
    implicit := first.implicit.compose second.implicit
    difference := first.difference.compose second.difference
    junction := first.junction.compose second.junction
    provenance := first.provenance.compose second.provenance
    sourceExact :=
      (congrArg second.implicit.forward first.sourceExact).trans second.sourceExact
    targetExact :=
      (congrArg second.explicit.forward first.targetExact).trans second.targetExact
    differenceExact :=
      (congrArg second.difference.forward first.differenceExact).trans second.differenceExact
    junctionExact :=
      (congrArg second.junction.forward first.junctionExact).trans second.junctionExact
    provenanceExact :=
      (congrArg second.provenance.forward first.provenanceExact).trans second.provenanceExact }

/- Pointwise laws quantify over all five selected carriers. They require no
   equality of structures containing functions. -/
structure ForwardAgreement {B C : ConstitutiveBoundary}
    (first second : BoundaryCarrierTransport B C) : Prop where
  explicit : (value : B.Explicit) → first.explicit.forward value = second.explicit.forward value
  implicit : (value : B.Implicit) → first.implicit.forward value = second.implicit.forward value
  difference : (value : B.Difference) → first.difference.forward value = second.difference.forward value
  junction : (witness : B.Compatible B.source B.target) →
    first.junction.forward witness = second.junction.forward witness
  provenance : (witness : B.Provenance B.difference) →
    first.provenance.forward witness = second.provenance.forward witness

theorem identity_left {B C : ConstitutiveBoundary} (transport : BoundaryTransport B C) :
    ForwardAgreement ((identity B).compose transport).toBoundaryCarrierTransport
      transport.toBoundaryCarrierTransport :=
  ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl⟩

theorem identity_right {B C : ConstitutiveBoundary} (transport : BoundaryTransport B C) :
    ForwardAgreement (transport.compose (identity C)).toBoundaryCarrierTransport
      transport.toBoundaryCarrierTransport :=
  ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl⟩

theorem compose_associative {B C D E : ConstitutiveBoundary}
    (first : BoundaryTransport B C) (second : BoundaryTransport C D)
    (third : BoundaryTransport D E) :
    ForwardAgreement ((first.compose second).compose third).toBoundaryCarrierTransport
      (first.compose (second.compose third)).toBoundaryCarrierTransport :=
  ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl⟩

theorem reverse_left {B C : ConstitutiveBoundary} (transport : BoundaryTransport B C) :
    ForwardAgreement (transport.compose transport.reverse).toBoundaryCarrierTransport
      (identity B).toBoundaryCarrierTransport :=
  ⟨transport.explicit.forwardBackward, transport.implicit.forwardBackward,
    transport.difference.forwardBackward, transport.junction.forwardBackward,
    transport.provenance.forwardBackward⟩

theorem reverse_right {B C : ConstitutiveBoundary} (transport : BoundaryTransport B C) :
    ForwardAgreement (transport.reverse.compose transport).toBoundaryCarrierTransport
      (identity C).toBoundaryCarrierTransport :=
  ⟨transport.explicit.backwardForward, transport.implicit.backwardForward,
    transport.difference.backwardForward, transport.junction.backwardForward,
    transport.provenance.backwardForward⟩

theorem reverse_reverse {B C : ConstitutiveBoundary} (transport : BoundaryTransport B C) :
    ForwardAgreement transport.reverse.reverse.toBoundaryCarrierTransport
      transport.toBoundaryCarrierTransport :=
  ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl⟩

theorem reverse_compose {B C D : ConstitutiveBoundary}
    (first : BoundaryTransport B C) (second : BoundaryTransport C D) :
    ForwardAgreement (first.compose second).reverse.toBoundaryCarrierTransport
      (second.reverse.compose first.reverse).toBoundaryCarrierTransport :=
  ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl⟩

structure BackwardAgreement {B C : ConstitutiveBoundary}
    (first second : BoundaryCarrierTransport B C) : Prop where
  explicit : (value : C.Explicit) → first.explicit.backward value = second.explicit.backward value
  implicit : (value : C.Implicit) → first.implicit.backward value = second.implicit.backward value
  difference : (value : C.Difference) → first.difference.backward value = second.difference.backward value
  junction : (witness : C.Compatible C.source C.target) →
    first.junction.backward witness = second.junction.backward witness
  provenance : (witness : C.Provenance C.difference) →
    first.provenance.backward witness = second.provenance.backward witness

theorem backward_of_forward {B C : ConstitutiveBoundary}
    {first second : BoundaryCarrierTransport B C}
    (agreement : ForwardAgreement first second) : BackwardAgreement first second :=
  ⟨ExactTypeTransport.backward_eq_of_forward_eq _ _ agreement.explicit,
    ExactTypeTransport.backward_eq_of_forward_eq _ _ agreement.implicit,
    ExactTypeTransport.backward_eq_of_forward_eq _ _ agreement.difference,
    ExactTypeTransport.backward_eq_of_forward_eq _ _ agreement.junction,
    ExactTypeTransport.backward_eq_of_forward_eq _ _ agreement.provenance⟩

theorem exists_identity (B : ConstitutiveBoundary) : Nonempty (BoundaryTransport B B) :=
  ⟨identity B⟩

theorem exists_reverse {B C : ConstitutiveBoundary} :
    Nonempty (BoundaryTransport B C) → Nonempty (BoundaryTransport C B) := by
  intro inhabited
  cases inhabited with
  | intro transport => exact ⟨transport.reverse⟩

theorem exists_compose {B C D : ConstitutiveBoundary} :
    Nonempty (BoundaryTransport B C) → Nonempty (BoundaryTransport C D) →
      Nonempty (BoundaryTransport B D) := by
  intro first second
  cases first with
  | intro first => cases second with
    | intro second => exact ⟨first.compose second⟩

end BoundaryTransport

/- The role stores its exact distinguished witness. Its source, target and
   provenance are read from the equipped boundary which indexes it. -/
structure EquippedFinalRole (B : ConstitutiveBoundary) where
  witness : B.Compatible B.source B.target
  witnessExact : witness = B.junction

namespace EquippedFinalRole

theorem ext {B : ConstitutiveBoundary} {first second : EquippedFinalRole B}
    (witnessEquality : first.witness = second.witness) : first = second := by
  cases first
  cases second
  cases witnessEquality
  rfl

theorem unique {B : ConstitutiveBoundary} (first second : EquippedFinalRole B) :
    first = second :=
  ext (first.witnessExact.trans second.witnessExact.symm)

def canonical (B : ConstitutiveBoundary) : EquippedFinalRole B := ⟨B.junction, rfl⟩

def source {B : ConstitutiveBoundary} (_ : EquippedFinalRole B) : B.Implicit := B.source

def target {B : ConstitutiveBoundary} (_ : EquippedFinalRole B) : B.Explicit := B.target

def provenance {B : ConstitutiveBoundary} (_ : EquippedFinalRole B) :
    B.Provenance B.difference := B.provenance

def transport {B C : ConstitutiveBoundary} (map : BoundaryTransport B C)
    (role : EquippedFinalRole B) : EquippedFinalRole C :=
  { witness := map.junction.forward role.witness
    witnessExact := (congrArg map.junction.forward role.witnessExact).trans map.junctionExact }

theorem source_preserved {B C : ConstitutiveBoundary}
    (map : BoundaryTransport B C) (role : EquippedFinalRole B) :
    map.implicit.forward role.source = (role.transport map).source := map.sourceExact

theorem target_preserved {B C : ConstitutiveBoundary}
    (map : BoundaryTransport B C) (role : EquippedFinalRole B) :
    map.explicit.forward role.target = (role.transport map).target := map.targetExact

theorem provenance_preserved {B C : ConstitutiveBoundary}
    (map : BoundaryTransport B C) (role : EquippedFinalRole B) :
    map.provenance.forward role.provenance = (role.transport map).provenance := map.provenanceExact

theorem transport_identity {B : ConstitutiveBoundary} (role : EquippedFinalRole B) :
    role.transport (BoundaryTransport.identity B) = role := by
  cases role
  rfl

theorem transport_compose {B C D : ConstitutiveBoundary}
    (first : BoundaryTransport B C) (second : BoundaryTransport C D)
    (role : EquippedFinalRole B) :
    (role.transport first).transport second = role.transport (first.compose second) := rfl

theorem transport_reverse {B C : ConstitutiveBoundary}
    (map : BoundaryTransport B C) (role : EquippedFinalRole B) :
    (role.transport map).transport map.reverse = role := by
  apply ext
  exact map.junction.forwardBackward role.witness

theorem transport_reverse_right {B C : ConstitutiveBoundary}
    (map : BoundaryTransport B C) (role : EquippedFinalRole C) :
    (role.transport map.reverse).transport map = role := by
  apply ext
  exact map.junction.backwardForward role.witness

def exactTransport {B C : ConstitutiveBoundary} (map : BoundaryTransport B C) :
    ExactTypeTransport (EquippedFinalRole B) (EquippedFinalRole C) :=
  { forward := fun role => role.transport map
    backward := fun role => role.transport map.reverse
    forwardBackward := fun role => transport_reverse map role
    backwardForward := fun role => transport_reverse_right map role }

end EquippedFinalRole
end RelationalPerimeter.Constitution

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Constitution.ConstitutiveBoundary
#print axioms RelationalPerimeter.Constitution.closingBoundary
#print axioms RelationalPerimeter.Constitution.BoundaryCarrierTransport
#print axioms RelationalPerimeter.Constitution.BoundaryTransport
#print axioms RelationalPerimeter.Constitution.BoundaryTransport.identity
#print axioms RelationalPerimeter.Constitution.BoundaryTransport.reverse
#print axioms RelationalPerimeter.Constitution.BoundaryTransport.compose
#print axioms RelationalPerimeter.Constitution.BoundaryTransport.ForwardAgreement
#print axioms RelationalPerimeter.Constitution.BoundaryTransport.identity_left
#print axioms RelationalPerimeter.Constitution.BoundaryTransport.identity_right
#print axioms RelationalPerimeter.Constitution.BoundaryTransport.compose_associative
#print axioms RelationalPerimeter.Constitution.BoundaryTransport.reverse_left
#print axioms RelationalPerimeter.Constitution.BoundaryTransport.reverse_right
#print axioms RelationalPerimeter.Constitution.BoundaryTransport.reverse_reverse
#print axioms RelationalPerimeter.Constitution.BoundaryTransport.reverse_compose
#print axioms RelationalPerimeter.Constitution.BoundaryTransport.BackwardAgreement
#print axioms RelationalPerimeter.Constitution.BoundaryTransport.backward_of_forward
#print axioms RelationalPerimeter.Constitution.BoundaryTransport.exists_identity
#print axioms RelationalPerimeter.Constitution.BoundaryTransport.exists_reverse
#print axioms RelationalPerimeter.Constitution.BoundaryTransport.exists_compose
#print axioms RelationalPerimeter.Constitution.EquippedFinalRole
#print axioms RelationalPerimeter.Constitution.EquippedFinalRole.ext
#print axioms RelationalPerimeter.Constitution.EquippedFinalRole.unique
#print axioms RelationalPerimeter.Constitution.EquippedFinalRole.canonical
#print axioms RelationalPerimeter.Constitution.EquippedFinalRole.source
#print axioms RelationalPerimeter.Constitution.EquippedFinalRole.target
#print axioms RelationalPerimeter.Constitution.EquippedFinalRole.provenance
#print axioms RelationalPerimeter.Constitution.EquippedFinalRole.transport
#print axioms RelationalPerimeter.Constitution.EquippedFinalRole.source_preserved
#print axioms RelationalPerimeter.Constitution.EquippedFinalRole.target_preserved
#print axioms RelationalPerimeter.Constitution.EquippedFinalRole.provenance_preserved
#print axioms RelationalPerimeter.Constitution.EquippedFinalRole.transport_identity
#print axioms RelationalPerimeter.Constitution.EquippedFinalRole.transport_compose
#print axioms RelationalPerimeter.Constitution.EquippedFinalRole.transport_reverse
#print axioms RelationalPerimeter.Constitution.EquippedFinalRole.transport_reverse_right
#print axioms RelationalPerimeter.Constitution.EquippedFinalRole.exactTransport
/- AXIOM_AUDIT_END -/
