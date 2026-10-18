import RelationalPerimeter.Constitution.Continuation.ReadoutCorrespondence
import RelationalPerimeter.Constitution.Continuation.DirectedIncompatibility

/-! Executed groupings turn local readout preservation into transverse
transports.  Endpoint data can then reject those transports constructively. -/
set_option autoImplicit false
namespace ConstitutiveSearch.ContinuationSignatures

universe u w
variable {S I M : Type u} {E : Type (w + 1)}
  {contract : FutureContract S I E (Type w)}
  {realization : OperationalRealization contract M}
  {left right sourceTerminal targetTerminal : S}

namespace ExecutedOperationalGrouping

def rejectDirectedEndpointIncompatibility
    (grouping : ExecutedOperationalGrouping realization left right
      sourceTerminal targetTerminal)
    (preservation : DirectedTerminalReadoutPreservation
      realization sourceTerminal targetTerminal)
    (sourceWitness : contract.read sourceTerminal)
    (rejectTarget : contract.read targetTerminal → Empty) : Empty :=
  rejectDirectedTransport (grouping.directedReadout preservation)
    sourceWitness rejectTarget

def rejectBilateralEndpointIncompatibility
    (grouping : ExecutedOperationalGrouping realization left right
      sourceTerminal targetTerminal)
    (forwardPreservation : DirectedTerminalReadoutPreservation
      realization sourceTerminal targetTerminal)
    (backwardPreservation : DirectedTerminalReadoutPreservation
      realization targetTerminal sourceTerminal)
    (certificate : BilateralNegationCertificate
      (contract.read sourceTerminal) (contract.read targetTerminal)) : Empty :=
  rejectBilateralTransport
    (grouping.directedReadout forwardPreservation)
    (grouping.reverseDirectedReadout backwardPreservation)
    certificate

end ExecutedOperationalGrouping
end ConstitutiveSearch.ContinuationSignatures
/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.ContinuationSignatures.ExecutedOperationalGrouping.rejectDirectedEndpointIncompatibility
#print axioms ConstitutiveSearch.ContinuationSignatures.ExecutedOperationalGrouping.rejectBilateralEndpointIncompatibility
/- AXIOM_AUDIT_END -/
