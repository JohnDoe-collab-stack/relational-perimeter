import RelationalPerimeter.Constitution.PositiveGeneration

set_option linter.checkUnivs false

/-! Relative grammar of equipped circular roles. Interior roles read complete
links at existing positions. Final roles read a fixed chosen closing boundary.
Exhaustiveness refers to this declared grammar; it supplies no new position. -/

namespace RelationalPerimeter.Constitution

open StrongPerimetralTurning

abbrev RoleLink (P : PositiveCircularPresentation) :=
  SuccessiveLink P.Explicit P.Implicit P.Compatible P.Difference P.Provenance

structure EquippedInteriorRole (P : PositiveCircularPresentation) where
  position : NonClosingPosition P.perimeter
  link : RoleLink P
  linkExact : link = P.perimeter.linkAt position

namespace EquippedInteriorRole

variable {P : PositiveCircularPresentation}

def canonical (P : PositiveCircularPresentation) (position : NonClosingPosition P.perimeter) :
    EquippedInteriorRole P := ⟨position, P.perimeter.linkAt position, rfl⟩

theorem ext {first second : EquippedInteriorRole P}
    (positionExact : first.position = second.position) : first = second := by
  cases first with
  | mk firstPosition firstLink firstExact =>
      cases second with
      | mk secondPosition secondLink secondExact =>
          cases positionExact
          have linkExact := firstExact.trans secondExact.symm
          cases linkExact
          rfl

theorem canonical_return (role : EquippedInteriorRole P) :
    canonical P role.position = role := ext rfl

def positionTransport (P : PositiveCircularPresentation) :
    ExactTypeTransport (NonClosingPosition P.perimeter) (EquippedInteriorRole P) :=
  { forward := canonical P
    backward := fun role => role.position
    forwardBackward := fun _ => rfl
    backwardForward := canonical_return }

theorem link_readout (role : EquippedInteriorRole P) :
    role.link = P.perimeter.linkAt role.position := role.linkExact

theorem source_readout (role : EquippedInteriorRole P) :
    role.link.source = (P.perimeter.linkAt role.position).source :=
  congrArg SuccessiveLink.source role.linkExact

theorem target_readout (role : EquippedInteriorRole P) :
    role.link.target = (P.perimeter.linkAt role.position).target :=
  congrArg SuccessiveLink.target role.linkExact

def ofOccurrence {F : PositiveFormation} {source terminal : F.State}
    (history : PositiveHistory F source terminal) (positive : PositiveHistory.Occurrence history)
    (junction : ClosingWitness history.boundaryShape) (occurrence : PositiveHistory.Occurrence history) :
    EquippedInteriorRole (history.toCircular positive junction) :=
  canonical _ (history.toPosition occurrence)

theorem occurrence_link_readout {F : PositiveFormation} {source terminal : F.State}
    (history : PositiveHistory F source terminal) (positive : PositiveHistory.Occurrence history)
    (junction : ClosingWitness history.boundaryShape) (occurrence : PositiveHistory.Occurrence history) :
    (ofOccurrence history positive junction occurrence).link = history.linkAt occurrence :=
  history.deploy_link_exact occurrence

def occurrenceTransport {F : PositiveFormation} {source terminal : F.State}
    (history : PositiveHistory F source terminal) (positive : PositiveHistory.Occurrence history)
    (junction : ClosingWitness history.boundaryShape) :
    ExactTypeTransport (PositiveHistory.Occurrence history)
      (EquippedInteriorRole (history.toCircular positive junction)) :=
  (history.positionTransport).compose (positionTransport (history.toCircular positive junction))

end EquippedInteriorRole

inductive CircularRole (P : PositiveCircularPresentation)
  | interior : EquippedInteriorRole P → CircularRole P
  | final : EquippedFinalRole (closingBoundary P) → CircularRole P

namespace CircularRole

variable {P : PositiveCircularPresentation}

def classify : CircularRole P → NonClosingPosition P.perimeter ⊕ Unit
  | .interior role => .inl role.position
  | .final _ => .inr ()

def assemble (P : PositiveCircularPresentation) : NonClosingPosition P.perimeter ⊕ Unit → CircularRole P
  | .inl position => .interior (EquippedInteriorRole.canonical P position)
  | .inr _ => .final (EquippedFinalRole.canonical (closingBoundary P))

theorem assemble_classify (role : CircularRole P) : assemble P (classify role) = role := by
  cases role with
  | interior role => exact congrArg CircularRole.interior role.canonical_return
  | final role => exact congrArg CircularRole.final (EquippedFinalRole.unique _ role)

theorem classify_assemble (location : NonClosingPosition P.perimeter ⊕ Unit) :
    classify (assemble P location) = location := by
  cases location with
  | inl => rfl
  | inr point => cases point; rfl

def classificationTransport (P : PositiveCircularPresentation) :
    ExactTypeTransport (CircularRole P) (NonClosingPosition P.perimeter ⊕ Unit) :=
  { forward := classify
    backward := assemble P
    forwardBackward := assemble_classify
    backwardForward := classify_assemble }

theorem exhaustive (role : CircularRole P) :
    (∃ position, role = .interior (EquippedInteriorRole.canonical P position)) ∨
      role = .final (EquippedFinalRole.canonical (closingBoundary P)) := by
  cases role with
  | interior role => exact .inl ⟨role.position, congrArg CircularRole.interior role.canonical_return.symm⟩
  | final role => exact .inr (congrArg CircularRole.final (EquippedFinalRole.unique _ _))

theorem branches_distinct (interior : EquippedInteriorRole P)
    (final : EquippedFinalRole (closingBoundary P)) :
    (CircularRole.interior interior : CircularRole P) ≠ .final final := by
  intro equality
  cases equality

def generatedPosition : CircularRole P → Option (NonClosingPosition P.perimeter)
  | .interior role => .some role.position
  | .final _ => .none

theorem interior_generated (role : EquippedInteriorRole P) :
    generatedPosition (.interior role) = .some role.position := rfl

theorem final_no_generated_position (role : EquippedFinalRole (closingBoundary P)) :
    generatedPosition (.final role) = .none := rfl

theorem final_not_interior_position (role : EquippedFinalRole (closingBoundary P))
    (position : NonClosingPosition P.perimeter) :
    generatedPosition (.final role) ≠ .some position := by
  intro equality
  cases equality

end CircularRole
end RelationalPerimeter.Constitution

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Constitution.RoleLink
#print axioms RelationalPerimeter.Constitution.EquippedInteriorRole
#print axioms RelationalPerimeter.Constitution.EquippedInteriorRole.canonical
#print axioms RelationalPerimeter.Constitution.EquippedInteriorRole.ext
#print axioms RelationalPerimeter.Constitution.EquippedInteriorRole.canonical_return
#print axioms RelationalPerimeter.Constitution.EquippedInteriorRole.positionTransport
#print axioms RelationalPerimeter.Constitution.EquippedInteriorRole.link_readout
#print axioms RelationalPerimeter.Constitution.EquippedInteriorRole.source_readout
#print axioms RelationalPerimeter.Constitution.EquippedInteriorRole.target_readout
#print axioms RelationalPerimeter.Constitution.EquippedInteriorRole.ofOccurrence
#print axioms RelationalPerimeter.Constitution.EquippedInteriorRole.occurrence_link_readout
#print axioms RelationalPerimeter.Constitution.EquippedInteriorRole.occurrenceTransport
#print axioms RelationalPerimeter.Constitution.CircularRole
#print axioms RelationalPerimeter.Constitution.CircularRole.classify
#print axioms RelationalPerimeter.Constitution.CircularRole.assemble
#print axioms RelationalPerimeter.Constitution.CircularRole.assemble_classify
#print axioms RelationalPerimeter.Constitution.CircularRole.classify_assemble
#print axioms RelationalPerimeter.Constitution.CircularRole.classificationTransport
#print axioms RelationalPerimeter.Constitution.CircularRole.exhaustive
#print axioms RelationalPerimeter.Constitution.CircularRole.branches_distinct
#print axioms RelationalPerimeter.Constitution.CircularRole.generatedPosition
#print axioms RelationalPerimeter.Constitution.CircularRole.interior_generated
#print axioms RelationalPerimeter.Constitution.CircularRole.final_no_generated_position
#print axioms RelationalPerimeter.Constitution.CircularRole.final_not_interior_position
/- AXIOM_AUDIT_END -/
