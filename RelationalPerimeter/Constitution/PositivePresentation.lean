import RelationalPerimeter.Constitution.Primitives

/- The five primitive sorts deliberately retain separate universe parameters. -/
set_option linter.checkUnivs false

/-!
# Positive circular presentation and a separate obstruction layer

The positive presentation contains only the successive witnessed chain and its
distinguished closing junction. Endpoint data and rejection of contraction are
separate inputs. No occurrence or periodic return is created by the junction.
-/

namespace StrongPerimetralTurning

universe uE uI uK uD uP uEnd uLoop

structure PositiveCircularPresentation where
  Explicit : Type uE
  Implicit : Type uI
  Compatible : Implicit → Explicit → Type uK
  Difference : Type uD
  Provenance : Difference → Type uP
  initialNode : LocalNode Explicit Implicit Compatible Difference Provenance
  perimeter : PerimeterSpine Compatible initialNode
  perimeterPositive : NonClosingPosition perimeter
  finalJunction : Compatible perimeter.finalNode.implicit initialNode.explicit

/- The initial difference has endpoint readings without imposing their separation. -/
structure EndpointBoundary (P : PositiveCircularPresentation) where
  Endpoint : Type uEnd
  leftEndpoint : Endpoint
  rightEndpoint : Endpoint
  leftPole : P.Difference → Endpoint
  rightPole : P.Difference → Endpoint
  initialLeftPole : leftPole P.initialNode.difference = leftEndpoint
  initialRightPole : rightPole P.initialNode.difference = rightEndpoint

/- This enrichment receives the rejection that the positive layer does not require. -/
structure CircularClosureObstruction
    (P : PositiveCircularPresentation)
    (boundary : EndpointBoundary.{uE, uI, uK, uD, uP, uEnd} P) where
  TotalLoop : Type uLoop
  closeFromIdentification : boundary.leftEndpoint = boundary.rightEndpoint → TotalLoop
  loopContractsInitialDifference :
    TotalLoop → boundary.leftPole P.initialNode.difference =
      boundary.rightPole P.initialNode.difference
  rejectInitialContraction :
    P.Provenance P.initialNode.difference →
      boundary.leftPole P.initialNode.difference =
        boundary.rightPole P.initialNode.difference → False

namespace CircularClosureObstruction

theorem rejectTotalLoop
    {P : PositiveCircularPresentation} {boundary : EndpointBoundary P}
    (obstruction : CircularClosureObstruction P boundary) :
    obstruction.TotalLoop → False :=
  fun loop => obstruction.rejectInitialContraction P.initialNode.provenance
    (obstruction.loopContractsInitialDifference loop)

theorem endpointsSeparated
    {P : PositiveCircularPresentation} {boundary : EndpointBoundary P}
    (obstruction : CircularClosureObstruction P boundary) :
    boundary.leftEndpoint ≠ boundary.rightEndpoint :=
  fun equality => obstruction.rejectTotalLoop
    (obstruction.closeFromIdentification equality)

theorem noObstructionOfIdentifiedEndpoints
    {P : PositiveCircularPresentation} {boundary : EndpointBoundary P}
    (identified : boundary.leftEndpoint = boundary.rightEndpoint) :
    CircularClosureObstruction P boundary → False :=
  fun obstruction => obstruction.endpointsSeparated identified

end CircularClosureObstruction
end StrongPerimetralTurning

/- AXIOM_AUDIT_BEGIN -/
#print axioms StrongPerimetralTurning.PositiveCircularPresentation
#print axioms StrongPerimetralTurning.EndpointBoundary
#print axioms StrongPerimetralTurning.CircularClosureObstruction
#print axioms StrongPerimetralTurning.CircularClosureObstruction.rejectTotalLoop
#print axioms StrongPerimetralTurning.CircularClosureObstruction.endpointsSeparated
#print axioms StrongPerimetralTurning.CircularClosureObstruction.noObstructionOfIdentifiedEndpoints
/- AXIOM_AUDIT_END -/
