import RelationalPerimeter.Constitution.Continuation.OperationalRealization

/-! Readout preservation at two computed terminals.  This layer is separate
from operational projection: equality of memories transports observations
only through the correspondence explicitly supplied here. -/
set_option genInjectivity false
namespace ConstitutiveSearch.ContinuationSignatures
universe u w
variable {S I M : Type u} {E : Type (w + 1)}
  {contract : FutureContract S I E (Type w)}

structure DirectedTerminalReadoutPreservation
    (realization : OperationalRealization contract M) (sourceTerminal targetTerminal : S) where
  memoryRead : M → Type w
  sourceForward : contract.read sourceTerminal → memoryRead (realization.project sourceTerminal)
  targetBackward : memoryRead (realization.project targetTerminal) → contract.read targetTerminal

namespace DirectedTerminalReadoutPreservation
variable {realization : OperationalRealization contract M} {sourceTerminal targetTerminal : S}

def transport
    (preservation : DirectedTerminalReadoutPreservation realization sourceTerminal targetTerminal)
    (sameMemory : realization.project sourceTerminal = realization.project targetTerminal) :
    contract.read sourceTerminal → contract.read targetTerminal := fun witness =>
  preservation.targetBackward
    (Eq.mp (congrArg preservation.memoryRead sameMemory)
      (preservation.sourceForward witness))

end DirectedTerminalReadoutPreservation

namespace ExecutedOperationalGrouping
variable {realization : OperationalRealization contract M}
  {left right sourceTerminal targetTerminal : S}

def directedReadout
    (grouping : ExecutedOperationalGrouping realization left right
      sourceTerminal targetTerminal)
    (preservation : DirectedTerminalReadoutPreservation
      realization sourceTerminal targetTerminal) :
    contract.read sourceTerminal → contract.read targetTerminal :=
  preservation.transport grouping.projectedTerminalsEqual

def reverseDirectedReadout
    (grouping : ExecutedOperationalGrouping realization left right
      sourceTerminal targetTerminal)
    (preservation : DirectedTerminalReadoutPreservation
      realization targetTerminal sourceTerminal) :
    contract.read targetTerminal → contract.read sourceTerminal :=
  preservation.transport grouping.projectedTerminalsEqual.symm

end ExecutedOperationalGrouping

structure TerminalReadoutCorrespondence
    (realization : OperationalRealization contract M) (leftTerminal rightTerminal : S) where
  memoryRead : M → Type w
  leftForward : contract.read leftTerminal → memoryRead (realization.project leftTerminal)
  leftBackward : memoryRead (realization.project leftTerminal) → contract.read leftTerminal
  rightForward : contract.read rightTerminal → memoryRead (realization.project rightTerminal)
  rightBackward : memoryRead (realization.project rightTerminal) → contract.read rightTerminal

namespace TerminalReadoutCorrespondence
variable {realization : OperationalRealization contract M} {leftTerminal rightTerminal : S}

def leftToRightPreservation
    (correspondence : TerminalReadoutCorrespondence realization leftTerminal rightTerminal) :
    DirectedTerminalReadoutPreservation realization leftTerminal rightTerminal where
  memoryRead := correspondence.memoryRead
  sourceForward := correspondence.leftForward
  targetBackward := correspondence.rightBackward

def rightToLeftPreservation
    (correspondence : TerminalReadoutCorrespondence realization leftTerminal rightTerminal) :
    DirectedTerminalReadoutPreservation realization rightTerminal leftTerminal where
  memoryRead := correspondence.memoryRead
  sourceForward := correspondence.rightForward
  targetBackward := correspondence.leftBackward

def leftToRight
    (correspondence : TerminalReadoutCorrespondence realization leftTerminal rightTerminal)
    (sameMemory : realization.project leftTerminal = realization.project rightTerminal) :
    contract.read leftTerminal → contract.read rightTerminal :=
  correspondence.leftToRightPreservation.transport sameMemory

def rightToLeft
    (correspondence : TerminalReadoutCorrespondence realization leftTerminal rightTerminal)
    (sameMemory : realization.project leftTerminal = realization.project rightTerminal) :
    contract.read rightTerminal → contract.read leftTerminal :=
  correspondence.rightToLeftPreservation.transport sameMemory.symm

end TerminalReadoutCorrespondence

def ExactRealization.terminalReadoutCorrespondence
    (realization : ExactRealization contract M) (leftTerminal rightTerminal : S) :
    TerminalReadoutCorrespondence realization.toOperational leftTerminal rightTerminal where
  memoryRead := realization.reduced.read
  leftForward := fun witness => Eq.mp (realization.read_exact leftTerminal) witness
  leftBackward := fun witness => Eq.mp (realization.read_exact leftTerminal).symm witness
  rightForward := fun witness => Eq.mp (realization.read_exact rightTerminal) witness
  rightBackward := fun witness => Eq.mp (realization.read_exact rightTerminal).symm witness

end ConstitutiveSearch.ContinuationSignatures
/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.ContinuationSignatures.DirectedTerminalReadoutPreservation
#print axioms ConstitutiveSearch.ContinuationSignatures.DirectedTerminalReadoutPreservation.transport
#print axioms ConstitutiveSearch.ContinuationSignatures.ExecutedOperationalGrouping.directedReadout
#print axioms ConstitutiveSearch.ContinuationSignatures.ExecutedOperationalGrouping.reverseDirectedReadout
#print axioms ConstitutiveSearch.ContinuationSignatures.TerminalReadoutCorrespondence
#print axioms ConstitutiveSearch.ContinuationSignatures.TerminalReadoutCorrespondence.leftToRightPreservation
#print axioms ConstitutiveSearch.ContinuationSignatures.TerminalReadoutCorrespondence.rightToLeftPreservation
#print axioms ConstitutiveSearch.ContinuationSignatures.TerminalReadoutCorrespondence.leftToRight
#print axioms ConstitutiveSearch.ContinuationSignatures.TerminalReadoutCorrespondence.rightToLeft
#print axioms ConstitutiveSearch.ContinuationSignatures.ExactRealization.terminalReadoutCorrespondence
/- AXIOM_AUDIT_END -/
