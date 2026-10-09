import RelationalPerimeter.Constitution.SignatureTransport
import RelationalPerimeter.Constitution.PositiveGeneration

set_option linter.checkUnivs false

/-! Transport of complete spines, witnesses and structural positions. The
position inverse is over a fixed source spine, not reconstruction of its data. -/

namespace RelationalPerimeter.Constitution

open StrongPerimetralTurning

namespace ConstitutiveSignatureTransport

variable {S T : ConstitutiveSignature}

def mapSpine (map : ConstitutiveSignatureTransport S T) {node : S.Node} :
    PerimeterSpine S.Compatible node → PerimeterSpine T.Compatible (map.mapNode node)
  | .boundary node => .boundary (map.mapNode node)
  | @PerimeterSpine.advance _ _ _ _ _ _ nextNode witness tail =>
      .advance (node := map.mapNode node) (nextNode := map.mapNode nextNode)
        ((map.compatibility node.implicit nextNode.explicit).forward witness) (map.mapSpine tail)

theorem mapSpine_final (map : ConstitutiveSignatureTransport S T) {node : S.Node}
    (spine : PerimeterSpine S.Compatible node) :
    (map.mapSpine spine).finalNode = map.mapNode spine.finalNode := by
  induction spine with
  | boundary => rfl
  | advance witness tail inductionHypothesis => exact inductionHypothesis

theorem mapSpine_append (map : ConstitutiveSignatureTransport S T) {node : S.Node}
    (first : PerimeterSpine S.Compatible node)
    (second : PerimeterSpine S.Compatible first.finalNode) :
    map.mapSpine (first.append second) =
      (map.mapSpine first).appendAlong (map.mapSpine_final first) (map.mapSpine second) := by
  induction first with
  | boundary => rfl
  | @advance node nextNode witness tail inductionHypothesis =>
      exact congrArg (PerimeterSpine.advance (node := map.mapNode node) (nextNode := map.mapNode nextNode)
        ((map.compatibility node.implicit nextNode.explicit).forward witness)) (inductionHypothesis second)

def mapPosition (map : ConstitutiveSignatureTransport S T) {node : S.Node} :
    (spine : PerimeterSpine S.Compatible node) →
    NonClosingPosition spine → NonClosingPosition (map.mapSpine spine)
  | .boundary _, position => nomatch position
  | .advance _ _, .here => .here
  | .advance _ tail, .later position => .later (map.mapPosition tail position)

def restorePosition (map : ConstitutiveSignatureTransport S T) {node : S.Node} :
    (spine : PerimeterSpine S.Compatible node) →
    NonClosingPosition (map.mapSpine spine) → NonClosingPosition spine
  | .boundary _ => fun position => nomatch position
  | .advance witness tail => fun position =>
      match position with
      | .here => NonClosingPosition.here (nextCompatible := witness) (tail := tail)
      | .later position => .later (map.restorePosition tail position)

theorem position_return (map : ConstitutiveSignatureTransport S T) {node : S.Node}
    (spine : PerimeterSpine S.Compatible node) (position : NonClosingPosition spine) :
    map.restorePosition spine (map.mapPosition spine position) = position := by
  induction position with
  | here => rfl
  | later position inductionHypothesis => exact congrArg NonClosingPosition.later inductionHypothesis

theorem position_return_target (map : ConstitutiveSignatureTransport S T) {node : S.Node}
    (spine : PerimeterSpine S.Compatible node) (position : NonClosingPosition (map.mapSpine spine)) :
    map.mapPosition spine (map.restorePosition spine position) = position := by
  induction spine with
  | boundary => cases position
  | advance witness tail inductionHypothesis =>
      cases position with
      | here => rfl
      | later position => exact congrArg NonClosingPosition.later (inductionHypothesis position)

def positionTransport (map : ConstitutiveSignatureTransport S T) {node : S.Node}
    (spine : PerimeterSpine S.Compatible node) :
    ExactTypeTransport (NonClosingPosition spine) (NonClosingPosition (map.mapSpine spine)) :=
  { forward := map.mapPosition spine
    backward := map.restorePosition spine
    forwardBackward := map.position_return spine
    backwardForward := map.position_return_target spine }

theorem mapPrecedes (map : ConstitutiveSignatureTransport S T) {node : S.Node}
    {spine : PerimeterSpine S.Compatible node} {first second : NonClosingPosition spine}
    (precedes : NonClosingPrecedes spine first second) :
    NonClosingPrecedes (map.mapSpine spine) (map.mapPosition spine first) (map.mapPosition spine second) := by
  induction precedes with
  | here_later position => exact .here_later (map.mapPosition _ position)
  | later_later _ inductionHypothesis => exact .later_later inductionHypothesis

theorem restorePrecedes (map : ConstitutiveSignatureTransport S T) {node : S.Node}
    (spine : PerimeterSpine S.Compatible node)
    {first second : NonClosingPosition (map.mapSpine spine)}
    (precedes : NonClosingPrecedes (map.mapSpine spine) first second) :
    NonClosingPrecedes spine (map.restorePosition spine first) (map.restorePosition spine second) := by
  induction spine with
  | boundary => cases first
  | advance witness tail inductionHypothesis =>
      cases precedes with
      | here_later position => exact .here_later (map.restorePosition tail position)
      | later_later relation => exact .later_later (inductionHypothesis relation)

theorem mapNext (map : ConstitutiveSignatureTransport S T) {node : S.Node}
    {spine : PerimeterSpine S.Compatible node} {first second : NonClosingPosition spine}
    (next : NonClosingNext spine first second) :
    NonClosingNext (map.mapSpine spine) (map.mapPosition spine first) (map.mapPosition spine second) := by
  induction next with
  | here_next => exact .here_next
  | later_next _ inductionHypothesis => exact .later_next inductionHypothesis

theorem restoreNext (map : ConstitutiveSignatureTransport S T) {node : S.Node}
    (spine : PerimeterSpine S.Compatible node)
    {first second : NonClosingPosition (map.mapSpine spine)}
    (next : NonClosingNext (map.mapSpine spine) first second) :
    NonClosingNext spine (map.restorePosition spine first) (map.restorePosition spine second) := by
  induction spine with
  | boundary => cases first
  | advance witness tail inductionHypothesis =>
      cases tail with
      | boundary =>
          cases next with
          | later_next relation => cases relation
      | advance witness tail =>
          cases next with
          | here_next => exact .here_next
          | later_next relation => exact .later_next (inductionHypothesis relation)

theorem precedes_iff (map : ConstitutiveSignatureTransport S T) {node : S.Node}
    (spine : PerimeterSpine S.Compatible node) (first second : NonClosingPosition spine) :
    NonClosingPrecedes (map.mapSpine spine) (map.mapPosition spine first) (map.mapPosition spine second) ↔
      NonClosingPrecedes spine first second := by
  constructor
  · intro relation
    have restored := map.restorePrecedes spine relation
    rw [map.position_return, map.position_return] at restored
    exact restored
  · exact map.mapPrecedes

theorem next_iff (map : ConstitutiveSignatureTransport S T) {node : S.Node}
    (spine : PerimeterSpine S.Compatible node) (first second : NonClosingPosition spine) :
    NonClosingNext (map.mapSpine spine) (map.mapPosition spine first) (map.mapPosition spine second) ↔
      NonClosingNext spine first second := by
  constructor
  · intro relation
    have restored := map.restoreNext spine relation
    rw [map.position_return, map.position_return] at restored
    exact restored
  · exact map.mapNext

def mapLink (map : ConstitutiveSignatureTransport S T)
    (link : SuccessiveLink S.Explicit S.Implicit S.Compatible S.Difference S.Provenance) :
    SuccessiveLink T.Explicit T.Implicit T.Compatible T.Difference T.Provenance :=
  ⟨map.mapNode link.source, map.mapNode link.target,
    (map.compatibility link.source.implicit link.target.explicit).forward link.compatibility⟩

theorem mapSpine_link (map : ConstitutiveSignatureTransport S T) {node : S.Node}
    (spine : PerimeterSpine S.Compatible node) (position : NonClosingPosition spine) :
    (map.mapSpine spine).linkAt (map.mapPosition spine position) = map.mapLink (spine.linkAt position) := by
  induction position with
  | here => rfl
  | later position inductionHypothesis => exact inductionHypothesis

end ConstitutiveSignatureTransport
end RelationalPerimeter.Constitution

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Constitution.ConstitutiveSignatureTransport.mapSpine
#print axioms RelationalPerimeter.Constitution.ConstitutiveSignatureTransport.mapSpine_final
#print axioms RelationalPerimeter.Constitution.ConstitutiveSignatureTransport.mapSpine_append
#print axioms RelationalPerimeter.Constitution.ConstitutiveSignatureTransport.mapPosition
#print axioms RelationalPerimeter.Constitution.ConstitutiveSignatureTransport.restorePosition
#print axioms RelationalPerimeter.Constitution.ConstitutiveSignatureTransport.position_return
#print axioms RelationalPerimeter.Constitution.ConstitutiveSignatureTransport.position_return_target
#print axioms RelationalPerimeter.Constitution.ConstitutiveSignatureTransport.positionTransport
#print axioms RelationalPerimeter.Constitution.ConstitutiveSignatureTransport.mapPrecedes
#print axioms RelationalPerimeter.Constitution.ConstitutiveSignatureTransport.restorePrecedes
#print axioms RelationalPerimeter.Constitution.ConstitutiveSignatureTransport.mapNext
#print axioms RelationalPerimeter.Constitution.ConstitutiveSignatureTransport.restoreNext
#print axioms RelationalPerimeter.Constitution.ConstitutiveSignatureTransport.precedes_iff
#print axioms RelationalPerimeter.Constitution.ConstitutiveSignatureTransport.next_iff
#print axioms RelationalPerimeter.Constitution.ConstitutiveSignatureTransport.mapLink
#print axioms RelationalPerimeter.Constitution.ConstitutiveSignatureTransport.mapSpine_link
/- AXIOM_AUDIT_END -/
