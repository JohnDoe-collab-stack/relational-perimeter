import RelationalPerimeter.Constitution.Continuation.DirectedObstruction

set_option autoImplicit false
namespace DirectedObstructionRegression
open ConstitutiveSearch.ContinuationSignatures

universe uP uQ

def directed_incompatibility_client
    {P : Type uP} {Q : Type uQ}
    (transport : P → Q) (sourceWitness : P) (rejectTarget : Q → Empty) : Empty :=
  rejectDirectedTransport transport sourceWitness rejectTarget

def bilateral_incompatibility_client
    {P : Type uP} {Q : Type uQ}
    (forward : P → Q) (backward : Q → P)
    (certificate : BilateralNegationCertificate P Q) : Empty :=
  rejectBilateralTransport forward backward certificate

universe u w
variable {S I M : Type u} {E : Type (w + 1)}
  {contract : FutureContract S I E (Type w)}
  {realization : OperationalRealization contract M}
  {left right sourceTerminal targetTerminal : S}

def executed_directed_incompatibility_client
    (grouping : ExecutedOperationalGrouping realization left right
      sourceTerminal targetTerminal)
    (preservation : DirectedTerminalReadoutPreservation
      realization sourceTerminal targetTerminal)
    (sourceWitness : contract.read sourceTerminal)
    (rejectTarget : contract.read targetTerminal → Empty) : Empty :=
  grouping.rejectDirectedEndpointIncompatibility preservation
    sourceWitness rejectTarget

def executed_bilateral_incompatibility_client
    (grouping : ExecutedOperationalGrouping realization left right
      sourceTerminal targetTerminal)
    (forwardPreservation : DirectedTerminalReadoutPreservation
      realization sourceTerminal targetTerminal)
    (backwardPreservation : DirectedTerminalReadoutPreservation
      realization targetTerminal sourceTerminal)
    (certificate : BilateralNegationCertificate
      (contract.read sourceTerminal) (contract.read targetTerminal)) : Empty :=
  grouping.rejectBilateralEndpointIncompatibility
    forwardPreservation backwardPreservation certificate

end DirectedObstructionRegression
/- AXIOM_AUDIT_BEGIN -/
#print axioms DirectedObstructionRegression.directed_incompatibility_client
#print axioms DirectedObstructionRegression.bilateral_incompatibility_client
#print axioms DirectedObstructionRegression.executed_directed_incompatibility_client
#print axioms DirectedObstructionRegression.executed_bilateral_incompatibility_client
/- AXIOM_AUDIT_END -/
