import RelationalPerimeter.Constitution.ClosingBoundary

set_option linter.checkUnivs false

/-! Exact transports of every relational fibre. Equality transports explicitly
reindex target fibres; preserving distinguished data is a separate obligation. -/

namespace RelationalPerimeter.Constitution

universe uE uI uK uD uP

structure ConstitutiveSignature where
  Explicit : Type uE
  Implicit : Type uI
  Compatible : Implicit → Explicit → Type uK
  Difference : Type uD
  Provenance : Difference → Type uP

def ConstitutiveBoundary.signature (B : ConstitutiveBoundary) : ConstitutiveSignature :=
  ⟨B.Explicit, B.Implicit, B.Compatible, B.Difference, B.Provenance⟩

namespace ConstitutiveSignature

abbrev Node (S : ConstitutiveSignature) :=
  StrongPerimetralTurning.LocalNode S.Explicit S.Implicit S.Compatible S.Difference S.Provenance

def compatibilityReindex (S : ConstitutiveSignature) {i j : S.Implicit} {e f : S.Explicit}
    (implicitExact : i = j) (explicitExact : e = f) :
    ExactTypeTransport (S.Compatible i e) (S.Compatible j f) := by
  cases implicitExact
  cases explicitExact
  exact ExactTypeTransport.reflexive _

def provenanceReindex (S : ConstitutiveSignature) {d c : S.Difference} (differenceExact : d = c) :
    ExactTypeTransport (S.Provenance d) (S.Provenance c) := by
  cases differenceExact
  exact ExactTypeTransport.reflexive _

end ConstitutiveSignature

structure ConstitutiveSignatureTransport (S T : ConstitutiveSignature) where
  explicit : ExactTypeTransport S.Explicit T.Explicit
  implicit : ExactTypeTransport S.Implicit T.Implicit
  difference : ExactTypeTransport S.Difference T.Difference
  compatibility : (i : S.Implicit) → (e : S.Explicit) →
    ExactTypeTransport (S.Compatible i e)
      (T.Compatible (implicit.forward i) (explicit.forward e))
  provenance : (d : S.Difference) →
    ExactTypeTransport (S.Provenance d) (T.Provenance (difference.forward d))

namespace ConstitutiveSignatureTransport

variable {S T U : ConstitutiveSignature}

def identity (S : ConstitutiveSignature) : ConstitutiveSignatureTransport S S :=
  { explicit := .reflexive _
    implicit := .reflexive _
    difference := .reflexive _
    compatibility := fun _ _ => .reflexive _
    provenance := fun _ => .reflexive _ }

def compatibilityAt (map : ConstitutiveSignatureTransport S T)
    {i : S.Implicit} {e : S.Explicit} {j : T.Implicit} {f : T.Explicit}
    (implicitExact : map.implicit.forward i = j)
    (explicitExact : map.explicit.forward e = f) :
    ExactTypeTransport (S.Compatible i e) (T.Compatible j f) :=
  (map.compatibility i e).compose (T.compatibilityReindex implicitExact explicitExact)

def provenanceAt (map : ConstitutiveSignatureTransport S T)
    {d : S.Difference} {c : T.Difference} (differenceExact : map.difference.forward d = c) :
    ExactTypeTransport (S.Provenance d) (T.Provenance c) :=
  (map.provenance d).compose (T.provenanceReindex differenceExact)

def reverse (map : ConstitutiveSignatureTransport S T) : ConstitutiveSignatureTransport T S :=
  { explicit := map.explicit.reverse
    implicit := map.implicit.reverse
    difference := map.difference.reverse
    compatibility := fun i e =>
      (map.compatibilityAt (map.implicit.backwardForward i) (map.explicit.backwardForward e)).reverse
    provenance := fun d => (map.provenanceAt (map.difference.backwardForward d)).reverse }

def compose (first : ConstitutiveSignatureTransport S T)
    (second : ConstitutiveSignatureTransport T U) : ConstitutiveSignatureTransport S U :=
  { explicit := first.explicit.compose second.explicit
    implicit := first.implicit.compose second.implicit
    difference := first.difference.compose second.difference
    compatibility := fun i e => (first.compatibility i e).compose
      (second.compatibility (first.implicit.forward i) (first.explicit.forward e))
    provenance := fun d => (first.provenance d).compose
      (second.provenance (first.difference.forward d)) }

theorem compatibility_return (map : ConstitutiveSignatureTransport S T)
    (i : S.Implicit) (e : S.Explicit) (w : S.Compatible i e) :
    (map.compatibility i e).backward ((map.compatibility i e).forward w) = w :=
  (map.compatibility i e).forwardBackward w

theorem compatibility_return_target (map : ConstitutiveSignatureTransport S T)
    (i : S.Implicit) (e : S.Explicit)
    (w : T.Compatible (map.implicit.forward i) (map.explicit.forward e)) :
    (map.compatibility i e).forward ((map.compatibility i e).backward w) = w :=
  (map.compatibility i e).backwardForward w

theorem provenance_return (map : ConstitutiveSignatureTransport S T)
    (d : S.Difference) (w : S.Provenance d) :
    (map.provenance d).backward ((map.provenance d).forward w) = w :=
  (map.provenance d).forwardBackward w

theorem provenance_return_target (map : ConstitutiveSignatureTransport S T)
    (d : S.Difference) (w : T.Provenance (map.difference.forward d)) :
    (map.provenance d).forward ((map.provenance d).backward w) = w :=
  (map.provenance d).backwardForward w

theorem reindexed_compatibility_return (map : ConstitutiveSignatureTransport S T)
    {i : S.Implicit} {e : S.Explicit} {j : T.Implicit} {f : T.Explicit}
    (hi : map.implicit.forward i = j) (he : map.explicit.forward e = f)
    (w : S.Compatible i e) :
    (map.compatibilityAt hi he).backward ((map.compatibilityAt hi he).forward w) = w :=
  (map.compatibilityAt hi he).forwardBackward w

theorem reindexed_provenance_return (map : ConstitutiveSignatureTransport S T)
    {d : S.Difference} {c : T.Difference} (hd : map.difference.forward d = c)
    (w : S.Provenance d) :
    (map.provenanceAt hd).backward ((map.provenanceAt hd).forward w) = w :=
  (map.provenanceAt hd).forwardBackward w

/- Composition and identity laws are pointwise, including every fibre. -/
theorem identity_compatibility (i : S.Implicit) (e : S.Explicit) (w : S.Compatible i e) :
    ((identity S).compatibility i e).forward w = w := rfl

theorem identity_provenance (d : S.Difference) (w : S.Provenance d) :
    ((identity S).provenance d).forward w = w := rfl

theorem compose_compatibility (first : ConstitutiveSignatureTransport S T)
    (second : ConstitutiveSignatureTransport T U)
    (i : S.Implicit) (e : S.Explicit) (w : S.Compatible i e) :
    ((first.compose second).compatibility i e).forward w =
      (second.compatibility (first.implicit.forward i) (first.explicit.forward e)).forward
        ((first.compatibility i e).forward w) := rfl

theorem compose_provenance (first : ConstitutiveSignatureTransport S T)
    (second : ConstitutiveSignatureTransport T U) (d : S.Difference) (w : S.Provenance d) :
    ((first.compose second).provenance d).forward w =
      (second.provenance (first.difference.forward d)).forward ((first.provenance d).forward w) := rfl

theorem identity_left_compatibility (map : ConstitutiveSignatureTransport S T)
    (i : S.Implicit) (e : S.Explicit) (w : S.Compatible i e) :
    (((identity S).compose map).compatibility i e).forward w =
      (map.compatibility i e).forward w := rfl

theorem identity_right_compatibility (map : ConstitutiveSignatureTransport S T)
    (i : S.Implicit) (e : S.Explicit) (w : S.Compatible i e) :
    ((map.compose (identity T)).compatibility i e).forward w =
      (map.compatibility i e).forward w := rfl

theorem identity_left_provenance (map : ConstitutiveSignatureTransport S T)
    (d : S.Difference) (w : S.Provenance d) :
    (((identity S).compose map).provenance d).forward w = (map.provenance d).forward w := rfl

theorem identity_right_provenance (map : ConstitutiveSignatureTransport S T)
    (d : S.Difference) (w : S.Provenance d) :
    ((map.compose (identity T)).provenance d).forward w = (map.provenance d).forward w := rfl

theorem compose_associative_compatibility {V : ConstitutiveSignature}
    (first : ConstitutiveSignatureTransport S T) (second : ConstitutiveSignatureTransport T U)
    (third : ConstitutiveSignatureTransport U V) (i : S.Implicit) (e : S.Explicit)
    (w : S.Compatible i e) :
    (((first.compose second).compose third).compatibility i e).forward w =
      ((first.compose (second.compose third)).compatibility i e).forward w := rfl

theorem compose_associative_provenance {V : ConstitutiveSignature}
    (first : ConstitutiveSignatureTransport S T) (second : ConstitutiveSignatureTransport T U)
    (third : ConstitutiveSignatureTransport U V) (d : S.Difference) (w : S.Provenance d) :
    (((first.compose second).compose third).provenance d).forward w =
      ((first.compose (second.compose third)).provenance d).forward w := rfl

theorem compatibility_backward_reindex (map : ConstitutiveSignatureTransport S T)
    {i j : S.Implicit} {e f : S.Explicit} (hi : j = i) (he : f = e)
    (w : T.Compatible (map.implicit.forward i) (map.explicit.forward e)) :
    (S.compatibilityReindex hi he).forward ((map.compatibility j f).backward
      ((T.compatibilityReindex (congrArg map.implicit.forward hi)
        (congrArg map.explicit.forward he)).backward w)) = (map.compatibility i e).backward w := by
  cases hi
  cases he
  rfl

theorem provenance_backward_reindex (map : ConstitutiveSignatureTransport S T)
    {d c : S.Difference} (hd : c = d) (w : T.Provenance (map.difference.forward d)) :
    (S.provenanceReindex hd).forward ((map.provenance c).backward
      ((T.provenanceReindex (congrArg map.difference.forward hd)).backward w)) =
      (map.provenance d).backward w := by
  cases hd
  rfl

theorem reverse_compatibility_return (map : ConstitutiveSignatureTransport S T)
    (i : S.Implicit) (e : S.Explicit) (w : S.Compatible i e) :
    (S.compatibilityReindex (map.implicit.forwardBackward i) (map.explicit.forwardBackward e)).forward
      ((map.reverse.compatibility (map.implicit.forward i) (map.explicit.forward e)).forward
        ((map.compatibility i e).forward w)) = w := by
  simp only [reverse, compatibilityAt, ExactTypeTransport.compose, ExactTypeTransport.reverse]
  exact (map.compatibility_backward_reindex (map.implicit.forwardBackward i)
    (map.explicit.forwardBackward e) ((map.compatibility i e).forward w)).trans
      ((map.compatibility i e).forwardBackward w)

theorem reverse_provenance_return (map : ConstitutiveSignatureTransport S T)
    (d : S.Difference) (w : S.Provenance d) :
    (S.provenanceReindex (map.difference.forwardBackward d)).forward
      ((map.reverse.provenance (map.difference.forward d)).forward ((map.provenance d).forward w)) = w := by
  simp only [reverse, provenanceAt, ExactTypeTransport.compose, ExactTypeTransport.reverse]
  exact (map.provenance_backward_reindex (map.difference.forwardBackward d)
    ((map.provenance d).forward w)).trans ((map.provenance d).forwardBackward w)

theorem reverse_compatibility_return_target (map : ConstitutiveSignatureTransport S T)
    (i : T.Implicit) (e : T.Explicit) (w : T.Compatible i e) :
    (map.compatibilityAt (map.implicit.backwardForward i) (map.explicit.backwardForward e)).forward
      ((map.reverse.compatibility i e).forward w) = w :=
  (map.compatibilityAt (map.implicit.backwardForward i) (map.explicit.backwardForward e)).backwardForward w

theorem reverse_provenance_return_target (map : ConstitutiveSignatureTransport S T)
    (d : T.Difference) (w : T.Provenance d) :
    (map.provenanceAt (map.difference.backwardForward d)).forward
      ((map.reverse.provenance d).forward w) = w :=
  (map.provenanceAt (map.difference.backwardForward d)).backwardForward w

def mapNode (map : ConstitutiveSignatureTransport S T) (node : S.Node) : T.Node :=
  { explicit := map.explicit.forward node.explicit
    implicit := map.implicit.forward node.implicit
    difference := map.difference.forward node.difference
    provenance := (map.provenance node.difference).forward node.provenance
    internallyCompatible := (map.compatibility node.implicit node.explicit).forward node.internallyCompatible }

theorem mapNode_identity (node : S.Node) : (identity S).mapNode node = node := by
  cases node
  rfl

theorem mapNode_compose (first : ConstitutiveSignatureTransport S T)
    (second : ConstitutiveSignatureTransport T U) (node : S.Node) :
    (first.compose second).mapNode node = second.mapNode (first.mapNode node) := rfl

def restrictCarriers {B C : ConstitutiveBoundary}
    (map : ConstitutiveSignatureTransport B.signature C.signature)
    (sourceExact : map.implicit.forward B.source = C.source)
    (targetExact : map.explicit.forward B.target = C.target)
    (differenceExact : map.difference.forward B.difference = C.difference) :
    BoundaryCarrierTransport B C :=
  { explicit := map.explicit
    implicit := map.implicit
    difference := map.difference
    junction := map.compatibilityAt sourceExact targetExact
    provenance := map.provenanceAt differenceExact }

def restrict {B C : ConstitutiveBoundary}
    (map : ConstitutiveSignatureTransport B.signature C.signature)
    (sourceExact : map.implicit.forward B.source = C.source)
    (targetExact : map.explicit.forward B.target = C.target)
    (differenceExact : map.difference.forward B.difference = C.difference)
    (junctionExact : (map.compatibilityAt sourceExact targetExact).forward B.junction = C.junction)
    (provenanceExact : (map.provenanceAt differenceExact).forward B.provenance = C.provenance) :
    BoundaryTransport B C :=
  { toBoundaryCarrierTransport := map.restrictCarriers sourceExact targetExact differenceExact
    sourceExact := sourceExact
    targetExact := targetExact
    differenceExact := differenceExact
    junctionExact := junctionExact
    provenanceExact := provenanceExact }

theorem restrict_junction_forward {B C : ConstitutiveBoundary}
    (map : ConstitutiveSignatureTransport B.signature C.signature)
    (hs : map.implicit.forward B.source = C.source)
    (ht : map.explicit.forward B.target = C.target)
    (hd : map.difference.forward B.difference = C.difference)
    (w : B.Compatible B.source B.target) :
    (map.restrictCarriers hs ht hd).junction.forward w = (map.compatibilityAt hs ht).forward w := rfl

theorem restrict_provenance_backward {B C : ConstitutiveBoundary}
    (map : ConstitutiveSignatureTransport B.signature C.signature)
    (hs : map.implicit.forward B.source = C.source)
    (ht : map.explicit.forward B.target = C.target)
    (hd : map.difference.forward B.difference = C.difference)
    (w : C.Provenance C.difference) :
    (map.restrictCarriers hs ht hd).provenance.backward w = (map.provenanceAt hd).backward w := rfl

end ConstitutiveSignatureTransport
end RelationalPerimeter.Constitution

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Constitution.ConstitutiveSignature
#print axioms RelationalPerimeter.Constitution.ConstitutiveBoundary.signature
#print axioms RelationalPerimeter.Constitution.ConstitutiveSignature.Node
#print axioms RelationalPerimeter.Constitution.ConstitutiveSignature.compatibilityReindex
#print axioms RelationalPerimeter.Constitution.ConstitutiveSignature.provenanceReindex
#print axioms RelationalPerimeter.Constitution.ConstitutiveSignatureTransport
#print axioms RelationalPerimeter.Constitution.ConstitutiveSignatureTransport.identity
#print axioms RelationalPerimeter.Constitution.ConstitutiveSignatureTransport.compatibilityAt
#print axioms RelationalPerimeter.Constitution.ConstitutiveSignatureTransport.provenanceAt
#print axioms RelationalPerimeter.Constitution.ConstitutiveSignatureTransport.reverse
#print axioms RelationalPerimeter.Constitution.ConstitutiveSignatureTransport.compose
#print axioms RelationalPerimeter.Constitution.ConstitutiveSignatureTransport.compatibility_return
#print axioms RelationalPerimeter.Constitution.ConstitutiveSignatureTransport.compatibility_return_target
#print axioms RelationalPerimeter.Constitution.ConstitutiveSignatureTransport.provenance_return
#print axioms RelationalPerimeter.Constitution.ConstitutiveSignatureTransport.provenance_return_target
#print axioms RelationalPerimeter.Constitution.ConstitutiveSignatureTransport.reindexed_compatibility_return
#print axioms RelationalPerimeter.Constitution.ConstitutiveSignatureTransport.reindexed_provenance_return
#print axioms RelationalPerimeter.Constitution.ConstitutiveSignatureTransport.identity_compatibility
#print axioms RelationalPerimeter.Constitution.ConstitutiveSignatureTransport.identity_provenance
#print axioms RelationalPerimeter.Constitution.ConstitutiveSignatureTransport.compose_compatibility
#print axioms RelationalPerimeter.Constitution.ConstitutiveSignatureTransport.compose_provenance
#print axioms RelationalPerimeter.Constitution.ConstitutiveSignatureTransport.identity_left_compatibility
#print axioms RelationalPerimeter.Constitution.ConstitutiveSignatureTransport.identity_right_compatibility
#print axioms RelationalPerimeter.Constitution.ConstitutiveSignatureTransport.identity_left_provenance
#print axioms RelationalPerimeter.Constitution.ConstitutiveSignatureTransport.identity_right_provenance
#print axioms RelationalPerimeter.Constitution.ConstitutiveSignatureTransport.compose_associative_compatibility
#print axioms RelationalPerimeter.Constitution.ConstitutiveSignatureTransport.compose_associative_provenance
#print axioms RelationalPerimeter.Constitution.ConstitutiveSignatureTransport.reverse_compatibility_return
#print axioms RelationalPerimeter.Constitution.ConstitutiveSignatureTransport.reverse_provenance_return
#print axioms RelationalPerimeter.Constitution.ConstitutiveSignatureTransport.compatibility_backward_reindex
#print axioms RelationalPerimeter.Constitution.ConstitutiveSignatureTransport.provenance_backward_reindex
#print axioms RelationalPerimeter.Constitution.ConstitutiveSignatureTransport.reverse_compatibility_return_target
#print axioms RelationalPerimeter.Constitution.ConstitutiveSignatureTransport.reverse_provenance_return_target
#print axioms RelationalPerimeter.Constitution.ConstitutiveSignatureTransport.mapNode
#print axioms RelationalPerimeter.Constitution.ConstitutiveSignatureTransport.mapNode_identity
#print axioms RelationalPerimeter.Constitution.ConstitutiveSignatureTransport.mapNode_compose
#print axioms RelationalPerimeter.Constitution.ConstitutiveSignatureTransport.restrictCarriers
#print axioms RelationalPerimeter.Constitution.ConstitutiveSignatureTransport.restrict
#print axioms RelationalPerimeter.Constitution.ConstitutiveSignatureTransport.restrict_junction_forward
#print axioms RelationalPerimeter.Constitution.ConstitutiveSignatureTransport.restrict_provenance_backward
/- AXIOM_AUDIT_END -/
