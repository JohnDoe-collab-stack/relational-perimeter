import RelationalPerimeter

/-!
# Public-root import gate

This module is a downstream-style build check.  Its presence in the default
Lake target ensures that the public `RelationalPerimeter` module is registered,
built, and importable rather than merely valid when elaborated as a source file.
-/

namespace RelationalPerimeter.Tests.PublicRootImport

def publicEvidence :=
  RelationalPerimeter.Computation.EndogenousOperationalDecomposition.evidence

def publicFamily :=
  RelationalPerimeter.Computation.EndogenousOperationalDecomposition.family

def publicPositivePresentation :=
  RelationalPerimeter.Constitution.Examples.positive

def publicBoundaryTransport :=
  RelationalPerimeter.Constitution.BoundaryTransport.identity
    (RelationalPerimeter.Constitution.closingBoundary publicPositivePresentation)

theorem publicHistoricalRoundTrip
    (presentation : StrongPerimetralTurning.CircularPresentation) :
    StrongPerimetralTurning.CircularPresentation.ofPositive
      presentation.toPositiveCircularPresentation presentation.endpointBoundary
      presentation.closureObstruction = presentation :=
  StrongPerimetralTurning.CircularPresentation.historical_roundTrip presentation

def publicClosingBoundaryShape :=
  RelationalPerimeter.Constitution.ConstitutiveBoundary.toClosingBoundaryShape
    (RelationalPerimeter.Constitution.closingBoundary publicPositivePresentation)

def publicClosingBoundaryPointing :=
  RelationalPerimeter.Constitution.ConstitutiveBoundary.toPointedClosingBoundary
    (RelationalPerimeter.Constitution.closingBoundary publicPositivePresentation)

theorem publicClosingBoundaryRoundTrip
    (boundary : RelationalPerimeter.Constitution.ConstitutiveBoundary) :
    boundary.toPointedClosingBoundary.toConstitutiveBoundary = boundary :=
  boundary.boundary_roundTrip

def publicPositiveFormation :=
  RelationalPerimeter.Constitution.PositiveGenerationExamples.directedFormation

def publicGeneratedHistory :=
  RelationalPerimeter.Constitution.PositiveGenerationExamples.directedHistory

def publicGeneratedPosition := publicGeneratedHistory.toPosition
  RelationalPerimeter.Constitution.PositiveGenerationExamples.directedPositive

theorem publicGeneratedComposition
    {formation : RelationalPerimeter.Constitution.PositiveFormation}
    {a b c : formation.State}
    (first : RelationalPerimeter.Constitution.PositiveHistory formation a b)
    (second : RelationalPerimeter.Constitution.PositiveHistory formation b c) :
    (first.append second).deploy =
      first.deploy.appendAlong first.deploy_final second.deploy :=
  RelationalPerimeter.Constitution.PositiveHistory.deploy_append first second

def publicSignatureTransport :=
  RelationalPerimeter.Constitution.SignatureTransportExamples.flip

def publicTransportedHistory :=
  RelationalPerimeter.Constitution.FormationTransportExamples.transportedHistory

def publicTransportedCircular :=
  RelationalPerimeter.Constitution.ClosingTransportExamples.movedCircular

theorem publicTransportedHistoryReturn :
    RelationalPerimeter.Constitution.PositiveHistory.restoreSignature
      RelationalPerimeter.Constitution.FormationTransportExamples.witnessFlip publicTransportedHistory =
        RelationalPerimeter.Constitution.FormationTransportExamples.firstHistory :=
  RelationalPerimeter.Constitution.FormationTransportExamples.complete_history_return

def publicCircularRole := RelationalPerimeter.Constitution.CircularRole.interior
  RelationalPerimeter.Constitution.CircularRolesExamples.interior

def publicRoleClassification := RelationalPerimeter.Constitution.CircularRole.classify publicCircularRole

def publicRoleTransport :=
  RelationalPerimeter.Constitution.CircularRoleTransportExamples.roleMap

theorem publicRoleClassificationReturn :
    RelationalPerimeter.Constitution.CircularRole.assemble
      RelationalPerimeter.Constitution.CircularRolesExamples.falsePresentation publicRoleClassification =
        publicCircularRole := RelationalPerimeter.Constitution.CircularRole.assemble_classify publicCircularRole

end RelationalPerimeter.Tests.PublicRootImport

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Tests.PublicRootImport.publicEvidence
#print axioms RelationalPerimeter.Tests.PublicRootImport.publicFamily
#print axioms RelationalPerimeter.Tests.PublicRootImport.publicPositivePresentation
#print axioms RelationalPerimeter.Tests.PublicRootImport.publicBoundaryTransport
#print axioms RelationalPerimeter.Tests.PublicRootImport.publicHistoricalRoundTrip
#print axioms RelationalPerimeter.Tests.PublicRootImport.publicClosingBoundaryShape
#print axioms RelationalPerimeter.Tests.PublicRootImport.publicClosingBoundaryPointing
#print axioms RelationalPerimeter.Tests.PublicRootImport.publicClosingBoundaryRoundTrip
#print axioms RelationalPerimeter.Tests.PublicRootImport.publicPositiveFormation
#print axioms RelationalPerimeter.Tests.PublicRootImport.publicGeneratedHistory
#print axioms RelationalPerimeter.Tests.PublicRootImport.publicGeneratedPosition
#print axioms RelationalPerimeter.Tests.PublicRootImport.publicGeneratedComposition
#print axioms RelationalPerimeter.Tests.PublicRootImport.publicSignatureTransport
#print axioms RelationalPerimeter.Tests.PublicRootImport.publicTransportedHistory
#print axioms RelationalPerimeter.Tests.PublicRootImport.publicTransportedCircular
#print axioms RelationalPerimeter.Tests.PublicRootImport.publicTransportedHistoryReturn
#print axioms RelationalPerimeter.Tests.PublicRootImport.publicCircularRole
#print axioms RelationalPerimeter.Tests.PublicRootImport.publicRoleClassification
#print axioms RelationalPerimeter.Tests.PublicRootImport.publicRoleTransport
#print axioms RelationalPerimeter.Tests.PublicRootImport.publicRoleClassificationReturn
/- AXIOM_AUDIT_END -/
