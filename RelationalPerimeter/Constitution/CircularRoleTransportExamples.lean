import RelationalPerimeter.Constitution.CircularRoleTransport
import RelationalPerimeter.Constitution.FormationTransportExamples

namespace RelationalPerimeter.Constitution.CircularRoleTransportExamples

open FormationTransportExamples

abbrev circular := threeSteps.toCircular firstOccurrence true

abbrev movedCircular := threeSteps.transportedCircular witnessFlip firstOccurrence true

def firstInterior : EquippedInteriorRole circular :=
  EquippedInteriorRole.canonical circular (threeSteps.toPosition firstOccurrence)

def thirdInterior : EquippedInteriorRole circular :=
  EquippedInteriorRole.canonical circular (threeSteps.toPosition thirdOccurrence)

theorem repeated_complete_links : firstInterior.link = thirdInterior.link := rfl

theorem distinct_equipped_interiors : firstInterior ≠ thirdInterior := by
  intro equality
  have positionExact := congrArg EquippedInteriorRole.position equality
  cases positionExact

def interiorMap : ExactTypeTransport (EquippedInteriorRole circular)
    (EquippedInteriorRole movedCircular) :=
  threeSteps.interiorRoleTransport witnessFlip firstOccurrence true

def movedFirstInterior : EquippedInteriorRole movedCircular := interiorMap.forward firstInterior

def movedThirdInterior : EquippedInteriorRole movedCircular := interiorMap.forward thirdInterior

theorem moved_interiors_distinct : movedFirstInterior ≠ movedThirdInterior := by
  intro equality
  have restored := congrArg interiorMap.backward equality
  exact distinct_equipped_interiors
    ((interiorMap.forwardBackward firstInterior).symm.trans
      (restored.trans (interiorMap.forwardBackward thirdInterior)))

theorem compatibility_flipped : movedFirstInterior.link.compatibility = false := rfl

theorem source_internal_compatibility_flipped :
    movedFirstInterior.link.source.internallyCompatible = false := rfl

theorem source_provenance_flipped : movedFirstInterior.link.source.provenance = false := rfl

theorem target_provenance_flipped : movedFirstInterior.link.target.provenance = false := rfl

theorem first_interior_source_return : interiorMap.backward movedFirstInterior = firstInterior :=
  interiorMap.forwardBackward firstInterior

theorem third_interior_target_return :
    interiorMap.forward (interiorMap.backward movedThirdInterior) = movedThirdInterior :=
  interiorMap.backwardForward movedThirdInterior

def roleMap : ExactTypeTransport (CircularRole circular) (CircularRole movedCircular) :=
  threeSteps.circularRoleTransport witnessFlip firstOccurrence true

def finalRole : EquippedFinalRole (closingBoundary circular) :=
  EquippedFinalRole.canonical (closingBoundary circular)

def finalMap : ExactTypeTransport (EquippedFinalRole (closingBoundary circular))
    (EquippedFinalRole (closingBoundary movedCircular)) :=
  threeSteps.finalRoleTransport witnessFlip firstOccurrence true

theorem final_junction_flipped : (finalMap.forward finalRole).witness = false := rfl

theorem final_provenance_flipped : (finalMap.forward finalRole).provenance = false := rfl

theorem interior_branch_retained :
    roleMap.forward (.interior firstInterior) = .interior movedFirstInterior := rfl

theorem final_branch_retained :
    roleMap.forward (.final finalRole) = .final (finalMap.forward finalRole) := rfl

theorem moved_final_no_position :
    CircularRole.generatedPosition (roleMap.forward (.final finalRole)) = .none := rfl

theorem moved_classification_commutes (role : CircularRole circular) :
    CircularRole.classify (roleMap.forward role) =
      Sum.map (threeSteps.circularPositionTransport witnessFlip).forward id
        (CircularRole.classify role) :=
  PositiveHistory.circular_classification_commutes (F := formation) (T := signature)
    witnessFlip threeSteps firstOccurrence true role

theorem moved_generation_readout_commutes (role : CircularRole circular) :
    CircularRole.generatedPosition (roleMap.forward role) =
      Option.map (threeSteps.circularPositionTransport witnessFlip).forward
        (CircularRole.generatedPosition role) :=
  PositiveHistory.circular_generated_position_commutes (F := formation) (T := signature)
    witnessFlip threeSteps firstOccurrence true role

theorem interior_role_source_return :
    roleMap.backward (roleMap.forward (.interior firstInterior)) = .interior firstInterior :=
  roleMap.forwardBackward _

theorem final_role_target_return :
    roleMap.forward (roleMap.backward (.final (finalMap.forward finalRole))) =
      .final (finalMap.forward finalRole) := roleMap.backwardForward _

end RelationalPerimeter.Constitution.CircularRoleTransportExamples

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Constitution.CircularRoleTransportExamples.circular
#print axioms RelationalPerimeter.Constitution.CircularRoleTransportExamples.movedCircular
#print axioms RelationalPerimeter.Constitution.CircularRoleTransportExamples.firstInterior
#print axioms RelationalPerimeter.Constitution.CircularRoleTransportExamples.thirdInterior
#print axioms RelationalPerimeter.Constitution.CircularRoleTransportExamples.repeated_complete_links
#print axioms RelationalPerimeter.Constitution.CircularRoleTransportExamples.distinct_equipped_interiors
#print axioms RelationalPerimeter.Constitution.CircularRoleTransportExamples.interiorMap
#print axioms RelationalPerimeter.Constitution.CircularRoleTransportExamples.movedFirstInterior
#print axioms RelationalPerimeter.Constitution.CircularRoleTransportExamples.movedThirdInterior
#print axioms RelationalPerimeter.Constitution.CircularRoleTransportExamples.moved_interiors_distinct
#print axioms RelationalPerimeter.Constitution.CircularRoleTransportExamples.compatibility_flipped
#print axioms RelationalPerimeter.Constitution.CircularRoleTransportExamples.source_internal_compatibility_flipped
#print axioms RelationalPerimeter.Constitution.CircularRoleTransportExamples.source_provenance_flipped
#print axioms RelationalPerimeter.Constitution.CircularRoleTransportExamples.target_provenance_flipped
#print axioms RelationalPerimeter.Constitution.CircularRoleTransportExamples.first_interior_source_return
#print axioms RelationalPerimeter.Constitution.CircularRoleTransportExamples.third_interior_target_return
#print axioms RelationalPerimeter.Constitution.CircularRoleTransportExamples.roleMap
#print axioms RelationalPerimeter.Constitution.CircularRoleTransportExamples.finalRole
#print axioms RelationalPerimeter.Constitution.CircularRoleTransportExamples.finalMap
#print axioms RelationalPerimeter.Constitution.CircularRoleTransportExamples.final_junction_flipped
#print axioms RelationalPerimeter.Constitution.CircularRoleTransportExamples.final_provenance_flipped
#print axioms RelationalPerimeter.Constitution.CircularRoleTransportExamples.interior_branch_retained
#print axioms RelationalPerimeter.Constitution.CircularRoleTransportExamples.final_branch_retained
#print axioms RelationalPerimeter.Constitution.CircularRoleTransportExamples.moved_final_no_position
#print axioms RelationalPerimeter.Constitution.CircularRoleTransportExamples.moved_classification_commutes
#print axioms RelationalPerimeter.Constitution.CircularRoleTransportExamples.moved_generation_readout_commutes
#print axioms RelationalPerimeter.Constitution.CircularRoleTransportExamples.interior_role_source_return
#print axioms RelationalPerimeter.Constitution.CircularRoleTransportExamples.final_role_target_return
/- AXIOM_AUDIT_END -/
