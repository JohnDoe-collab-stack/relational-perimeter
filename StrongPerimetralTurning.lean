import AbstractSegmentedTurning
import ExactTypeTransport

/- The proposition-valued definitions below are intentionally transparent,
   and the independent input families intentionally keep distinct universes. -/
set_option linter.defProp false
set_option linter.checkUnivs false

namespace StrongPerimetralTurning

universe uE uI uK uD uP uN uEnd uLoop uA uB uV

/-! ## Positive circular presentation -/

structure LocalNode
    (Explicit : Type uE)
    (Implicit : Type uI)
    (Compatible : Implicit → Explicit → Type uK)
    (Difference : Type uD)
    (Provenance : Difference → Type uP) where
  explicit : Explicit
  implicit : Implicit
  difference : Difference
  provenance : Provenance difference
  internallyCompatible : Compatible implicit explicit

inductive PerimeterSpine
    {Explicit : Type uE}
    {Implicit : Type uI}
    (Compatible : Implicit → Explicit → Type uK)
    {Difference : Type uD}
    {Provenance : Difference → Type uP} :
    LocalNode Explicit Implicit Compatible Difference Provenance → Type _
  | boundary
      (node : LocalNode Explicit Implicit Compatible Difference Provenance) :
      PerimeterSpine Compatible node
  | advance
      {node nextNode :
        LocalNode Explicit Implicit Compatible Difference Provenance}
      (nextCompatible : Compatible node.implicit nextNode.explicit)
      (tail : PerimeterSpine Compatible nextNode) :
      PerimeterSpine Compatible node

namespace PerimeterSpine

def startNode
    {Explicit : Type uE}
    {Implicit : Type uI}
    {Compatible : Implicit → Explicit → Type uK}
    {Difference : Type uD}
    {Provenance : Difference → Type uP}
    {node : LocalNode Explicit Implicit Compatible Difference Provenance}
    (_ : PerimeterSpine Compatible node) :
    LocalNode Explicit Implicit Compatible Difference Provenance :=
  node

def finalNode
    {Explicit : Type uE}
    {Implicit : Type uI}
    {Compatible : Implicit → Explicit → Type uK}
    {Difference : Type uD}
    {Provenance : Difference → Type uP}
    {node : LocalNode Explicit Implicit Compatible Difference Provenance} :
    PerimeterSpine Compatible node →
      LocalNode Explicit Implicit Compatible Difference Provenance
  | .boundary node => node
  | .advance _ tail => finalNode tail

end PerimeterSpine

inductive NonClosingPosition
    {Explicit : Type uE}
    {Implicit : Type uI}
    {Compatible : Implicit → Explicit → Type uK}
    {Difference : Type uD}
    {Provenance : Difference → Type uP} :
    {node : LocalNode Explicit Implicit Compatible Difference Provenance} →
    PerimeterSpine Compatible node → Type _
  | here
      {node nextNode :
        LocalNode Explicit Implicit Compatible Difference Provenance}
      {nextCompatible : Compatible node.implicit nextNode.explicit}
      {tail : PerimeterSpine Compatible nextNode} :
      NonClosingPosition (.advance nextCompatible tail)
  | later
      {node nextNode :
        LocalNode Explicit Implicit Compatible Difference Provenance}
      {nextCompatible : Compatible node.implicit nextNode.explicit}
      {tail : PerimeterSpine Compatible nextNode} :
      NonClosingPosition tail →
      NonClosingPosition (.advance nextCompatible tail)

/- Structural precedence between non-closing positions.  The relation carries
   only order information: no rank, distance, contiguity, or realization data
   is encoded here. -/
inductive NonClosingPrecedes
    {Explicit : Type uE}
    {Implicit : Type uI}
    {Compatible : Implicit → Explicit → Type uK}
    {Difference : Type uD}
    {Provenance : Difference → Type uP} :
    {node : LocalNode Explicit Implicit Compatible Difference Provenance} →
    (remaining : PerimeterSpine Compatible node) →
    NonClosingPosition remaining →
    NonClosingPosition remaining →
    Prop
  | here_later
      {node nextNode :
        LocalNode Explicit Implicit Compatible Difference Provenance}
      {nextCompatible : Compatible node.implicit nextNode.explicit}
      {tail : PerimeterSpine Compatible nextNode}
      (position : NonClosingPosition tail) :
      NonClosingPrecedes
        (.advance nextCompatible tail)
        .here
        (.later position)
  | later_later
      {node nextNode :
        LocalNode Explicit Implicit Compatible Difference Provenance}
      {nextCompatible : Compatible node.implicit nextNode.explicit}
      {tail : PerimeterSpine Compatible nextNode}
      {first second : NonClosingPosition tail} :
      NonClosingPrecedes tail first second →
      NonClosingPrecedes
        (.advance nextCompatible tail)
        (.later first)
        (.later second)


/- Immediate structural adjacency between non-closing positions.  Unlike
   `NonClosingPrecedes`, this relation is not transitive: it records exactly
   one canonical successor step in the perimeter spine. -/
inductive NonClosingNext
    {Explicit : Type uE}
    {Implicit : Type uI}
    {Compatible : Implicit → Explicit → Type uK}
    {Difference : Type uD}
    {Provenance : Difference → Type uP} :
    {node : LocalNode Explicit Implicit Compatible Difference Provenance} →
    (remaining : PerimeterSpine Compatible node) →
    NonClosingPosition remaining →
    NonClosingPosition remaining →
    Prop
  | here_next
      {node nextNode thirdNode :
        LocalNode Explicit Implicit Compatible Difference Provenance}
      {firstCompatible : Compatible node.implicit nextNode.explicit}
      {secondCompatible : Compatible nextNode.implicit thirdNode.explicit}
      {tail : PerimeterSpine Compatible thirdNode} :
      NonClosingNext
        (.advance firstCompatible (.advance secondCompatible tail))
        .here
        (.later .here)
  | later_next
      {node nextNode :
        LocalNode Explicit Implicit Compatible Difference Provenance}
      {nextCompatible : Compatible node.implicit nextNode.explicit}
      {tail : PerimeterSpine Compatible nextNode}
      {first second : NonClosingPosition tail} :
      NonClosingNext tail first second →
      NonClosingNext
        (.advance nextCompatible tail)
        (.later first)
        (.later second)

namespace NonClosingPrecedes

theorem ne
    {Explicit : Type uE}
    {Implicit : Type uI}
    {Compatible : Implicit → Explicit → Type uK}
    {Difference : Type uD}
    {Provenance : Difference → Type uP}
    {node : LocalNode Explicit Implicit Compatible Difference Provenance}
    {remaining : PerimeterSpine Compatible node}
    {first second : NonClosingPosition remaining}
    (precedes : NonClosingPrecedes remaining first second) : first ≠ second := by
  induction precedes with
  | here_later _ =>
      intro equality
      cases equality
  | later_later _ inductionHypothesis =>
      intro equality
      exact inductionHypothesis (NonClosingPosition.later.inj equality)

end NonClosingPrecedes

namespace NonClosingNext

theorem toPrecedes
    {Explicit : Type uE}
    {Implicit : Type uI}
    {Compatible : Implicit → Explicit → Type uK}
    {Difference : Type uD}
    {Provenance : Difference → Type uP}
    {node : LocalNode Explicit Implicit Compatible Difference Provenance}
    {remaining : PerimeterSpine Compatible node}
    {first second : NonClosingPosition remaining}
    (next : NonClosingNext remaining first second) :
    NonClosingPrecedes remaining first second := by
  induction next with
  | here_next => exact .here_later .here
  | later_next _ inductionHypothesis =>
      exact .later_later inductionHypothesis

end NonClosingNext


structure CircularPresentation where
  Explicit : Type uE
  Implicit : Type uI
  Compatible : Implicit → Explicit → Type uK
  Difference : Type uD
  Provenance : Difference → Type uP
  initialNode :
    LocalNode Explicit Implicit Compatible Difference Provenance
  perimeter : PerimeterSpine Compatible initialNode
  perimeterPositive : NonClosingPosition perimeter
  finalJunction :
    Compatible perimeter.finalNode.implicit initialNode.explicit
  Endpoint : Type uEnd
  leftEndpoint : Endpoint
  rightEndpoint : Endpoint
  leftPole : Difference → Endpoint
  rightPole : Difference → Endpoint
  initialLeftPole :
    leftPole initialNode.difference = leftEndpoint
  initialRightPole :
    rightPole initialNode.difference = rightEndpoint
  TotalLoop : Type uLoop
  closeFromIdentification : leftEndpoint = rightEndpoint → TotalLoop
  loopContractsInitialDifference :
    TotalLoop →
      leftPole initialNode.difference = rightPole initialNode.difference
  rejectInitialContraction :
    (provenance : Provenance initialNode.difference) →
    leftPole initialNode.difference = rightPole initialNode.difference → False

namespace CircularPresentation

def rejectTotalLoop (P : CircularPresentation) : P.TotalLoop → False :=
  fun loop =>
    P.rejectInitialContraction
      P.initialNode.provenance
      (P.loopContractsInitialDifference loop)

def endpointsSeparated (P : CircularPresentation) :
    P.leftEndpoint ≠ P.rightEndpoint :=
  fun equality => P.rejectTotalLoop (P.closeFromIdentification equality)

end CircularPresentation

/- The initial failure of contraction is retained as positive, proof-relevant
   data.  It will be stored in the root boundary code and inherited by every
   code produced from it. -/
structure PositiveClosureObstruction (P : CircularPresentation) where
  provenance : P.Provenance P.initialNode.difference
  rejectsContraction :
    P.leftPole P.initialNode.difference =
      P.rightPole P.initialNode.difference → False

def CircularPresentation.positiveClosureObstruction
    (P : CircularPresentation) : PositiveClosureObstruction P :=
  { provenance := P.initialNode.provenance
    rejectsContraction := P.rejectInitialContraction P.initialNode.provenance }

inductive FinalRequirement (P : CircularPresentation) : Type
  | distinguished : FinalRequirement P

def finalRequirementContractible
    (P : CircularPresentation) :
    SegmentedResidualRole.ContractibleRole (FinalRequirement P) :=
  { center := .distinguished
    contracts := fun requirement => by
      cases requirement
      rfl }

def FinalJunctionCompatibility (P : CircularPresentation) : Type _ :=
  P.Compatible
    P.perimeter.finalNode.implicit
    P.initialNode.explicit

/- This witness separates raw closing compatibility from contraction: a
   junction may be positively present while the two endpoints remain apart. -/
structure RawJunctionWithSeparatedEndpoints
    (P : CircularPresentation) where
  junction : FinalJunctionCompatibility P
  separated : P.leftEndpoint ≠ P.rightEndpoint

def CircularRequirement (P : CircularPresentation) : Type _ :=
  NonClosingPosition P.perimeter ⊕ FinalRequirement P

structure ExplicitTotalization (P : CircularPresentation) where
  common : P.Explicit
  commonIsCurrent : common = P.initialNode.explicit
  reconstruct : P.Explicit → P.Endpoint
  reconstructsLeft : reconstruct common = P.leftEndpoint
  reconstructsRight : reconstruct common = P.rightEndpoint

structure ImplicitTotalization (P : CircularPresentation) where
  absorb : P.Endpoint → P.Implicit
  reconstruct : P.Implicit → P.Endpoint
  absorbsLeftAsCurrent : absorb P.leftEndpoint = P.initialNode.implicit
  absorbsRightAsCurrent : absorb P.rightEndpoint = P.initialNode.implicit
  leftRoundTrip : reconstruct (absorb P.leftEndpoint) = P.leftEndpoint
  rightRoundTrip : reconstruct (absorb P.rightEndpoint) = P.rightEndpoint

/- These two kernels isolate the exact operational data used by the rejection
   proofs.  The public totalizations remain stronger semantic structures: the
   explicit one additionally identifies its common value with the current
   explicit value, while the implicit one identifies both absorbed endpoints
   with the current implicit value. -/
structure ExplicitContractionKernel (P : CircularPresentation) where
  common : P.Explicit
  reconstruct : P.Explicit → P.Endpoint
  reconstructsLeft : reconstruct common = P.leftEndpoint
  reconstructsRight : reconstruct common = P.rightEndpoint

structure ImplicitContractionKernel (P : CircularPresentation) where
  absorb : P.Endpoint → P.Implicit
  reconstruct : P.Implicit → P.Endpoint
  absorbsCoincide : absorb P.leftEndpoint = absorb P.rightEndpoint
  leftRoundTrip : reconstruct (absorb P.leftEndpoint) = P.leftEndpoint
  rightRoundTrip : reconstruct (absorb P.rightEndpoint) = P.rightEndpoint

namespace ExplicitTotalization

def toContractionKernel
    {P : CircularPresentation}
    (totalization : ExplicitTotalization P) :
    ExplicitContractionKernel P :=
  { common := totalization.common
    reconstruct := totalization.reconstruct
    reconstructsLeft := totalization.reconstructsLeft
    reconstructsRight := totalization.reconstructsRight }

end ExplicitTotalization

namespace ImplicitTotalization

def toContractionKernel
    {P : CircularPresentation}
    (totalization : ImplicitTotalization P) :
    ImplicitContractionKernel P :=
  { absorb := totalization.absorb
    reconstruct := totalization.reconstruct
    absorbsCoincide :=
      totalization.absorbsLeftAsCurrent.trans
        totalization.absorbsRightAsCurrent.symm
    leftRoundTrip := totalization.leftRoundTrip
    rightRoundTrip := totalization.rightRoundTrip }

end ImplicitTotalization

structure ContractedClosureDifference (P : CircularPresentation) where
  difference : P.Difference
  isInitialDifference : difference = P.initialNode.difference
  provenance : P.Provenance difference
  poleContraction : P.leftPole difference = P.rightPole difference

namespace ContractedClosureDifference

def initialProvenance
    {P : CircularPresentation}
    (contracted : ContractedClosureDifference P) :
    P.Provenance P.initialNode.difference :=
  cast (congrArg P.Provenance contracted.isInitialDifference)
    contracted.provenance

def initialPoleContraction
    {P : CircularPresentation}
    (contracted : ContractedClosureDifference P) :
    P.leftPole P.initialNode.difference =
      P.rightPole P.initialNode.difference :=
  (congrArg P.leftPole contracted.isInitialDifference).symm.trans
    (contracted.poleContraction.trans
      (congrArg P.rightPole contracted.isInitialDifference))

def endpointContraction
    {P : CircularPresentation}
    (contracted : ContractedClosureDifference P) :
    P.leftEndpoint = P.rightEndpoint :=
  P.initialLeftPole.symm.trans
    (contracted.initialPoleContraction.trans P.initialRightPole)

def toTotalLoop
    {P : CircularPresentation}
    (contracted : ContractedClosureDifference P) : P.TotalLoop :=
  P.closeFromIdentification contracted.endpointContraction

def reject
    {P : CircularPresentation}
    (contracted : ContractedClosureDifference P) : False :=
  P.rejectInitialContraction
    contracted.initialProvenance
    contracted.initialPoleContraction

end ContractedClosureDifference

def explicitKernelContractsClosureDifference
    {P : CircularPresentation}
    (kernel : ExplicitContractionKernel P) :
    ContractedClosureDifference P :=
  { difference := P.initialNode.difference
    isInitialDifference := rfl
    provenance := P.initialNode.provenance
    poleContraction :=
      P.initialLeftPole.trans
        ((kernel.reconstructsLeft.symm.trans
          kernel.reconstructsRight).trans
          P.initialRightPole.symm) }

def implicitKernelContractsClosureDifference
    {P : CircularPresentation}
    (kernel : ImplicitContractionKernel P) :
    ContractedClosureDifference P :=
  { difference := P.initialNode.difference
    isInitialDifference := rfl
    provenance := P.initialNode.provenance
    poleContraction :=
      P.initialLeftPole.trans
        ((kernel.leftRoundTrip.symm.trans
          ((congrArg kernel.reconstruct kernel.absorbsCoincide).trans
            kernel.rightRoundTrip)).trans
          P.initialRightPole.symm) }

def explicitContractionKernelRejected
    {P : CircularPresentation} : ExplicitContractionKernel P → False :=
  fun kernel => (explicitKernelContractsClosureDifference kernel).reject

def implicitContractionKernelRejected
    {P : CircularPresentation} : ImplicitContractionKernel P → False :=
  fun kernel => (implicitKernelContractsClosureDifference kernel).reject

def explicitTotalizationContractsClosureDifference
    {P : CircularPresentation}
    (totalization : ExplicitTotalization P) :
    ContractedClosureDifference P :=
  explicitKernelContractsClosureDifference totalization.toContractionKernel

def implicitTotalizationContractsClosureDifference
    {P : CircularPresentation}
    (totalization : ImplicitTotalization P) :
    ContractedClosureDifference P :=
  implicitKernelContractsClosureDifference totalization.toContractionKernel

def explicitTotalizationRejected
    {P : CircularPresentation} : ExplicitTotalization P → False :=
  fun totalization =>
    (explicitTotalizationContractsClosureDifference totalization).reject

def implicitTotalizationRejected
    {P : CircularPresentation} : ImplicitTotalization P → False :=
  fun totalization =>
    (implicitTotalizationContractsClosureDifference totalization).reject

/-! ## Returned readings and intrinsic free construction -/

inductive FreeTail : Type
  | first
  | next : FreeTail → FreeTail

inductive PerimeterCursor (P : CircularPresentation) : Type _
  | within
      {node : LocalNode
        P.Explicit P.Implicit P.Compatible P.Difference P.Provenance}
      (remaining : PerimeterSpine P.Compatible node) : PerimeterCursor P
  | beyond : FreeTail → PerimeterCursor P

def advanceCursor {P : CircularPresentation} :
    PerimeterCursor P → PerimeterCursor P
  | .within (.advance _ tail) => .within tail
  | .within (.boundary _) => .beyond .first
  | .beyond tail => .beyond (.next tail)

inductive CursorAdvance (P : CircularPresentation) :
    PerimeterCursor P → PerimeterCursor P → Type _
  | withinAdvance
      {node nextNode : LocalNode
        P.Explicit P.Implicit P.Compatible P.Difference P.Provenance}
      (nextCompatible : P.Compatible node.implicit nextNode.explicit)
      (tail : PerimeterSpine P.Compatible nextNode) :
      CursorAdvance P
        (.within (.advance nextCompatible tail))
        (.within tail)
  | leaveBoundary
      (node : LocalNode
        P.Explicit P.Implicit P.Compatible P.Difference P.Provenance) :
      CursorAdvance P (.within (.boundary node)) (.beyond .first)
  | beyondAdvance
      (tail : FreeTail) :
      CursorAdvance P (.beyond tail) (.beyond (.next tail))

inductive PositiveCursorAdvance (P : CircularPresentation) :
    PerimeterCursor P → PerimeterCursor P → Type _
  | one : CursorAdvance P a b → PositiveCursorAdvance P a b
  | followedBy :
      PositiveCursorAdvance P a b →
      CursorAdvance P b c →
      PositiveCursorAdvance P a c

def cursorAdvanceGraph
    {P : CircularPresentation}
    (cursor : PerimeterCursor P) :
    CursorAdvance P cursor (advanceCursor cursor) :=
  match cursor with
  | .within (.boundary node) => .leaveBoundary node
  | .within (.advance compatible tail) =>
      .withinAdvance compatible tail
  | .beyond tail => .beyondAdvance tail

inductive StructuralDepth : Type
  | root
  | next : StructuralDepth → StructuralDepth

inductive ProperStructuralDepth : StructuralDepth → StructuralDepth → Type
  | direct (depth : StructuralDepth) :
      ProperStructuralDepth depth (.next depth)
  | later : ProperStructuralDepth shallower deeper →
      ProperStructuralDepth shallower (.next deeper)

inductive PositiveUnaryExtension : Type
  | one
  | more : PositiveUnaryExtension → PositiveUnaryExtension

def PositiveUnaryExtension.applyDepth :
    PositiveUnaryExtension → StructuralDepth → StructuralDepth
  | .one, depth => .next depth
  | .more extension, depth => .next (extension.applyDepth depth)

def PositiveUnaryExtension.applyDepth_next
    (extension : PositiveUnaryExtension)
    (depth : StructuralDepth) :
    extension.applyDepth (.next depth) =
      .next (extension.applyDepth depth) := by
  induction extension with
  | one => rfl
  | more extension inductionHypothesis =>
      exact congrArg StructuralDepth.next inductionHypothesis

def PositiveUnaryExtension.applyDepth_ne_self :
    (depth : StructuralDepth) → (extension : PositiveUnaryExtension) →
      extension.applyDepth depth = depth → False
  | .root, .one, equality => nomatch equality
  | .root, .more _extension, equality => nomatch equality
  | .next depth, extension, equality =>
      PositiveUnaryExtension.applyDepth_ne_self depth extension
        (StructuralDepth.next.inj
          ((extension.applyDepth_next depth).symm.trans equality))

namespace ProperStructuralDepth

def toPositiveExtension
    {shallower deeper : StructuralDepth} :
    ProperStructuralDepth shallower deeper →
      Σ extension : PositiveUnaryExtension,
        PLift (deeper = extension.applyDepth shallower)
  | .direct _ => ⟨.one, ⟨rfl⟩⟩
  | .later proper =>
      let result := proper.toPositiveExtension
      ⟨.more result.1,
        ⟨congrArg StructuralDepth.next result.2.down⟩⟩

def trans : ProperStructuralDepth a b → ProperStructuralDepth b c →
    ProperStructuralDepth a c
  | left, .direct _ => .later left
  | left, .later right => .later (trans left right)

theorem irreflexive
    (depth : StructuralDepth) : ProperStructuralDepth depth depth → False :=
  fun proper =>
    let result := proper.toPositiveExtension
    result.1.applyDepth_ne_self depth result.2.down.symm

end ProperStructuralDepth

def spineDepth
    {P : CircularPresentation}
    {node : LocalNode
      P.Explicit P.Implicit P.Compatible P.Difference P.Provenance} :
    PerimeterSpine P.Compatible node → StructuralDepth
  | .boundary _ => .root
  | .advance _ tail => .next (spineDepth tail)

inductive ProperSpineSuffix
    {P : CircularPresentation} :
    {sourceNode : LocalNode
      P.Explicit P.Implicit P.Compatible P.Difference P.Provenance} →
    PerimeterSpine P.Compatible sourceNode →
    {targetNode : LocalNode
      P.Explicit P.Implicit P.Compatible P.Difference P.Provenance} →
    PerimeterSpine P.Compatible targetNode → Type _
  | direct
      {node nextNode : LocalNode
        P.Explicit P.Implicit P.Compatible P.Difference P.Provenance}
      {compatible : P.Compatible node.implicit nextNode.explicit}
      {tail : PerimeterSpine P.Compatible nextNode} :
      ProperSpineSuffix (.advance compatible tail) tail
  | later
      {node nextNode targetNode : LocalNode
        P.Explicit P.Implicit P.Compatible P.Difference P.Provenance}
      {compatible : P.Compatible node.implicit nextNode.explicit}
      {tail : PerimeterSpine P.Compatible nextNode}
      {target : PerimeterSpine P.Compatible targetNode} :
      ProperSpineSuffix tail target →
      ProperSpineSuffix (.advance compatible tail) target

namespace ProperSpineSuffix

def toStructuralDepth
    {P : CircularPresentation}
    {sourceNode targetNode : LocalNode
      P.Explicit P.Implicit P.Compatible P.Difference P.Provenance}
    {source : PerimeterSpine P.Compatible sourceNode}
    {target : PerimeterSpine P.Compatible targetNode} :
    ProperSpineSuffix source target →
      ProperStructuralDepth (spineDepth target) (spineDepth source)
  | .direct => .direct _
  | .later suffix => .later suffix.toStructuralDepth

def trans
    {P : CircularPresentation}
    {aNode bNode cNode : LocalNode
      P.Explicit P.Implicit P.Compatible P.Difference P.Provenance}
    {a : PerimeterSpine P.Compatible aNode}
    {b : PerimeterSpine P.Compatible bNode}
    {c : PerimeterSpine P.Compatible cNode} :
    ProperSpineSuffix a b → ProperSpineSuffix b c →
      ProperSpineSuffix a c
  | .direct, right => .later right
  | .later left, right => .later (trans left right)

theorem irreflexive
    {P : CircularPresentation}
    {node : LocalNode
      P.Explicit P.Implicit P.Compatible P.Difference P.Provenance}
    (spine : PerimeterSpine P.Compatible node) :
    ProperSpineSuffix spine spine → False :=
  fun suffix => ProperStructuralDepth.irreflexive _ suffix.toStructuralDepth

end ProperSpineSuffix

inductive ProperFreeTail : FreeTail → FreeTail → Type
  | direct (tail : FreeTail) : ProperFreeTail tail (.next tail)
  | later : ProperFreeTail source target →
      ProperFreeTail source (.next target)

namespace ProperFreeTail

def applyTail :
    PositiveUnaryExtension → FreeTail → FreeTail
  | .one, tail => .next tail
  | .more extension, tail => .next (applyTail extension tail)

def applyTail_next
    (extension : PositiveUnaryExtension)
    (tail : FreeTail) :
    applyTail extension (.next tail) = .next (applyTail extension tail) := by
  induction extension with
  | one => rfl
  | more extension inductionHypothesis =>
      exact congrArg FreeTail.next inductionHypothesis

def applyTail_ne_self :
    (tail : FreeTail) → (extension : PositiveUnaryExtension) →
      applyTail extension tail = tail → False
  | .first, .one, equality => nomatch equality
  | .first, .more _extension, equality => nomatch equality
  | .next tail, extension, equality =>
      applyTail_ne_self tail extension
        (FreeTail.next.inj
          ((applyTail_next extension tail).symm.trans equality))

def toPositiveExtension
    {source target : FreeTail} : ProperFreeTail source target →
    Σ extension : PositiveUnaryExtension,
      PLift (target = applyTail extension source)
  | .direct _ => ⟨.one, ⟨rfl⟩⟩
  | .later proper =>
      let result := proper.toPositiveExtension
      ⟨.more result.1, ⟨congrArg FreeTail.next result.2.down⟩⟩

def trans : ProperFreeTail a b → ProperFreeTail b c → ProperFreeTail a c
  | left, .direct _ => .later left
  | left, .later right => .later (trans left right)

theorem irreflexive (tail : FreeTail) : ProperFreeTail tail tail → False :=
  fun proper =>
    let result := proper.toPositiveExtension
    applyTail_ne_self tail result.1 result.2.down.symm

end ProperFreeTail

inductive CursorFuture (P : CircularPresentation) :
    PerimeterCursor P → PerimeterCursor P → Type _
  | withinSuffix
      {sourceNode targetNode : LocalNode
        P.Explicit P.Implicit P.Compatible P.Difference P.Provenance}
      {source : PerimeterSpine P.Compatible sourceNode}
      {target : PerimeterSpine P.Compatible targetNode} :
      ProperSpineSuffix source target →
      CursorFuture P (.within source) (.within target)
  | withinBeyond
      {sourceNode : LocalNode
        P.Explicit P.Implicit P.Compatible P.Difference P.Provenance}
      {source : PerimeterSpine P.Compatible sourceNode}
      (tail : FreeTail) : CursorFuture P (.within source) (.beyond tail)
  | beyondTail
      {source target : FreeTail} :
      ProperFreeTail source target →
      CursorFuture P (.beyond source) (.beyond target)

namespace CursorFuture

inductive Measure : Type
  | within : StructuralDepth → Measure
  | beyond : FreeTail → Measure

def measure
    {P : CircularPresentation} : PerimeterCursor P → Measure
  | .within spine => .within (spineDepth spine)
  | .beyond tail => .beyond tail

inductive ProperMeasure : Measure → Measure → Type
  | within
      {source target : StructuralDepth} :
      ProperStructuralDepth target source →
        ProperMeasure (.within source) (.within target)
  | cross
      (source : StructuralDepth) (target : FreeTail) :
      ProperMeasure (.within source) (.beyond target)
  | beyond
      {source target : FreeTail} :
      ProperFreeTail source target →
        ProperMeasure (.beyond source) (.beyond target)

namespace ProperMeasure

theorem irreflexive (point : Measure) : ProperMeasure point point → False := by
  cases point with
  | within depth =>
      intro later
      cases later with
      | within deeper => exact ProperStructuralDepth.irreflexive depth deeper
  | beyond tail =>
      intro later
      cases later with
      | beyond deeper => exact ProperFreeTail.irreflexive tail deeper

end ProperMeasure

def toProperMeasure
    {P : CircularPresentation}
    {source target : PerimeterCursor P} :
    CursorFuture P source target → ProperMeasure (measure source) (measure target)
  | .withinSuffix suffix => .within suffix.toStructuralDepth
  | .withinBeyond tail => .cross _ tail
  | .beyondTail later => .beyond later

def trans
    {P : CircularPresentation}
    {a b c : PerimeterCursor P} :
    CursorFuture P a b → CursorFuture P b c → CursorFuture P a c
  | .withinSuffix left, .withinSuffix right =>
      .withinSuffix (ProperSpineSuffix.trans left right)
  | .withinSuffix _, .withinBeyond tail => .withinBeyond tail
  | .withinBeyond _, @CursorFuture.beyondTail _ _ target right =>
      .withinBeyond target
  | .beyondTail left, .beyondTail right =>
      .beyondTail (ProperFreeTail.trans left right)

theorem irreflexive
    {P : CircularPresentation}
    (cursor : PerimeterCursor P) : CursorFuture P cursor cursor → False :=
  fun future => ProperMeasure.irreflexive (measure cursor) future.toProperMeasure

end CursorFuture

def CursorAdvance.toFuture
    {P : CircularPresentation}
    {source target : PerimeterCursor P} :
    CursorAdvance P source target → CursorFuture P source target
  | .withinAdvance _ _ => .withinSuffix .direct
  | .leaveBoundary _ => .withinBeyond .first
  | .beyondAdvance tail => .beyondTail (.direct tail)

def PositiveCursorAdvance.toFuture
    {P : CircularPresentation}
    {source target : PerimeterCursor P} :
    PositiveCursorAdvance P source target → CursorFuture P source target
  | .one step => step.toFuture
  | .followedBy previous step => previous.toFuture.trans step.toFuture

theorem positiveCursorAdvance_irreflexive
    {P : CircularPresentation}
    {cursor : PerimeterCursor P} :
    PositiveCursorAdvance P cursor cursor → False :=
  fun positive => CursorFuture.irreflexive cursor positive.toFuture

inductive ReturnedExplicit (P : CircularPresentation) : Type _
  | source : P.Explicit → ReturnedExplicit P
  | formed : PerimeterCursor P → ReturnedExplicit P

inductive ReturnedImplicit (P : CircularPresentation) : Type _
  | source : P.Implicit → ReturnedImplicit P
  | formed : PerimeterCursor P → ReturnedImplicit P

inductive ReturnedCompatible (P : CircularPresentation) :
    ReturnedImplicit P → ReturnedExplicit P → Type _
  | source
      {i : P.Implicit} {e : P.Explicit} :
      P.Compatible i e → ReturnedCompatible P (.source i) (.source e)
  | formedInternal (cursor : PerimeterCursor P) :
      ReturnedCompatible P (.formed cursor) (.formed cursor)
  | leaveBoundary
      (node : LocalNode
        P.Explicit P.Implicit P.Compatible P.Difference P.Provenance) :
      ReturnedCompatible P
        (.source node.implicit) (.formed (.beyond .first))
  | beyondAdvance (tail : FreeTail) :
      ReturnedCompatible P
        (.formed (.beyond tail)) (.formed (.beyond (.next tail)))

def explicitAt {P : CircularPresentation}
    (cursor : PerimeterCursor P) : ReturnedExplicit P :=
  match cursor with
  | .within remaining => .source remaining.startNode.explicit
  | .beyond tail => .formed (.beyond tail)

def implicitAt {P : CircularPresentation}
    (cursor : PerimeterCursor P) : ReturnedImplicit P :=
  match cursor with
  | .within remaining => .source remaining.startNode.implicit
  | .beyond tail => .formed (.beyond tail)

def CompatibleExplicitation
    (P : CircularPresentation)
    (cursor : PerimeterCursor P) : Type _ :=
  Σ e : ReturnedExplicit P, ReturnedCompatible P (implicitAt cursor) e

def internalCompatibleAt
    {P : CircularPresentation}
    (cursor : PerimeterCursor P) :
    ReturnedCompatible P (implicitAt cursor) (explicitAt cursor) :=
  match cursor with
  | .within remaining => .source remaining.startNode.internallyCompatible
  | .beyond tail => .formedInternal (.beyond tail)

def currentCompatibleExplicitation
    {P : CircularPresentation}
    (cursor : PerimeterCursor P) : CompatibleExplicitation P cursor :=
  ⟨explicitAt cursor, internalCompatibleAt cursor⟩

def stepCompatibleAt
    {P : CircularPresentation}
    (cursor : PerimeterCursor P) :
    ReturnedCompatible P
      (implicitAt cursor) (explicitAt (advanceCursor cursor)) :=
  match cursor with
  | .within (.boundary node) => .leaveBoundary node
  | .within (@PerimeterSpine.advance _ _ _ _ _ node nextNode compatible _tail) =>
      show ReturnedCompatible P
        (.source node.implicit) (.source nextNode.explicit)
      from .source compatible
  | .beyond tail => .beyondAdvance tail

def successorCompatibleExplicitation
    {P : CircularPresentation}
    (cursor : PerimeterCursor P) : CompatibleExplicitation P cursor :=
  ⟨explicitAt (advanceCursor cursor), stepCompatibleAt cursor⟩

inductive ReturnedDifference (P : CircularPresentation) : Type _
  | source : P.Difference → ReturnedDifference P
  | free : FreeTail → ReturnedDifference P

inductive ReturnedProvenance (P : CircularPresentation) :
    ReturnedDifference P → Type _
  | source
      {g : P.Difference} :
      P.Provenance g → ReturnedProvenance P (.source g)
  | free (tail : FreeTail) : ReturnedProvenance P (.free tail)

def differenceAtCursor {P : CircularPresentation}
    (cursor : PerimeterCursor P) : ReturnedDifference P :=
  match cursor with
  | .within remaining => .source remaining.startNode.difference
  | .beyond tail => .free tail

def provenanceAtCursor
    {P : CircularPresentation}
    (cursor : PerimeterCursor P) :
    ReturnedProvenance P (differenceAtCursor cursor) :=
  match cursor with
  | .within remaining => .source remaining.startNode.provenance
  | .beyond tail => .free tail

inductive FreeKAtom
    (P : CircularPresentation)
    (cursor : PerimeterCursor P) : Type _
  | explicitPole
  | implicitPole
  | currentDifference
  | admissible : CompatibleExplicitation P cursor → FreeKAtom P cursor

structure FreeKAlgebra
    (P : CircularPresentation)
    (cursor : PerimeterCursor P) where
  Carrier : Type uA
  explicitPole : Carrier
  implicitPole : Carrier
  currentDifference : Carrier
  admissible : CompatibleExplicitation P cursor → Carrier

def FreeKAtom.fold
    {P : CircularPresentation}
    {cursor : PerimeterCursor P}
    (A : FreeKAlgebra P cursor) : FreeKAtom P cursor → A.Carrier
  | .explicitPole => A.explicitPole
  | .implicitPole => A.implicitPole
  | .currentDifference => A.currentDifference
  | .admissible x => A.admissible x

/- Lean does not accept a mutually inductive family whose indices mention
   another member of the same mutual block.  The Lean-legal primitive encoding
   therefore puts the exact boundary code and exact free layer in the indices
   of `FreeConstitutionCore`.  The public dependent families below expose this
   stored data without weakening it to an external proposition. -/
inductive BoundaryDifferenceCode
    (P : CircularPresentation) : PerimeterCursor P → Type _
  | initial
      (obstruction : PositiveClosureObstruction P) :
      BoundaryDifferenceCode P (.within P.perimeter)
  | afterFormation
      {cursor : PerimeterCursor P}
      (integratedDifference : BoundaryDifferenceCode P cursor)
      (formationTerm : FreeKAtom P cursor)
      (formationTermIsSuccessor :
        formationTerm =
          .admissible (successorCompatibleExplicitation cursor)) :
      BoundaryDifferenceCode P (advanceCursor cursor)

namespace BoundaryDifferenceCode

def inheritedClosureObstruction
    {P : CircularPresentation} :
    {cursor : PerimeterCursor P} →
      BoundaryDifferenceCode P cursor → PositiveClosureObstruction P
  | _, .initial obstruction => obstruction
  | _, .afterFormation previous _ _ =>
      previous.inheritedClosureObstruction

end BoundaryDifferenceCode

structure FreeKCore
    (P : CircularPresentation)
    (cursor : PerimeterCursor P)
    (currentDifference : BoundaryDifferenceCode P cursor) where
  formationTerm : FreeKAtom P cursor
  formationTermIsSuccessor :
    formationTerm =
      .admissible (successorCompatibleExplicitation cursor)
  integratedClosureObstruction : PositiveClosureObstruction P
  integratedClosureObstructionIsCurrent :
    integratedClosureObstruction =
      currentDifference.inheritedClosureObstruction
  integratedProvenance :
    ReturnedProvenance P (differenceAtCursor cursor)
  integratedProvenanceIsCurrent :
    integratedProvenance = provenanceAtCursor cursor

inductive FreeConstitutionCore
    (P : CircularPresentation) :
    (cursor : PerimeterCursor P) → BoundaryDifferenceCode P cursor → Type _
  | root :
      FreeConstitutionCore P (.within P.perimeter)
        (.initial P.positiveClosureObstruction)
  | formed
      {cursor : PerimeterCursor P}
      {currentDifference : BoundaryDifferenceCode P cursor}
      (previous : FreeConstitutionCore P cursor currentDifference)
      (layer : FreeKCore P cursor currentDifference) :
      FreeConstitutionCore P (advanceCursor cursor)
        (.afterFormation currentDifference
          layer.formationTerm layer.formationTermIsSuccessor)

def FreeConstitution
    (P : CircularPresentation)
    (cursor : PerimeterCursor P) : Type _ :=
  Σ currentDifference : BoundaryDifferenceCode P cursor,
    FreeConstitutionCore P cursor currentDifference

namespace FreeConstitution

def root {P : CircularPresentation} :
    FreeConstitution P (.within P.perimeter) :=
  ⟨.initial P.positiveClosureObstruction, .root⟩

end FreeConstitution

inductive BoundaryDifference
    (P : CircularPresentation) :
    {cursor : PerimeterCursor P} → FreeConstitution P cursor → Type
  | exact
      {cursor : PerimeterCursor P}
      {data : FreeConstitution P cursor} :
      BoundaryDifference P data

namespace BoundaryDifference

def initial {P : CircularPresentation} :
    BoundaryDifference P FreeConstitution.root :=
  .exact

end BoundaryDifference

structure FreeK
    (P : CircularPresentation)
    {cursor : PerimeterCursor P}
    (previous : FreeConstitution P cursor)
    (_currentDifference : BoundaryDifference P previous) where
  core : FreeKCore P cursor previous.1

namespace FreeK

def canonical
    {P : CircularPresentation}
    {cursor : PerimeterCursor P}
    {previous : FreeConstitution P cursor}
    {currentDifference : BoundaryDifference P previous}
    (formationTerm : FreeKAtom P cursor)
    (formationTermIsSuccessor :
      formationTerm =
        .admissible (successorCompatibleExplicitation cursor)) :
    FreeK P previous currentDifference :=
  { core :=
      { formationTerm := formationTerm
        formationTermIsSuccessor := formationTermIsSuccessor
        integratedClosureObstruction :=
          previous.1.inheritedClosureObstruction
        integratedClosureObstructionIsCurrent := rfl
        integratedProvenance := provenanceAtCursor cursor
        integratedProvenanceIsCurrent := rfl } }

end FreeK

def FreeConstitution.formed
    {P : CircularPresentation}
    {cursor : PerimeterCursor P}
    (previous : FreeConstitution P cursor)
    (currentDifference : BoundaryDifference P previous)
    (layer : FreeK P previous currentDifference) :
    FreeConstitution P (advanceCursor cursor) :=
  ⟨.afterFormation previous.1
      (FreeKCore.formationTerm layer.core)
      (FreeKCore.formationTermIsSuccessor layer.core),
    .formed previous.2 layer.core⟩

@[simp] theorem FreeConstitution.formed_boundaryCode_exact
    {P : CircularPresentation}
    {cursor : PerimeterCursor P}
    (previous : FreeConstitution P cursor)
    (currentDifference : BoundaryDifference P previous)
    (layer : FreeK P previous currentDifference) :
    (FreeConstitution.formed previous currentDifference layer).1 =
      .afterFormation previous.1
        (FreeKCore.formationTerm layer.core)
        (FreeKCore.formationTermIsSuccessor layer.core) :=
  rfl

@[simp] theorem FreeConstitution.formed_core_exact
    {P : CircularPresentation}
    {cursor : PerimeterCursor P}
    (previous : FreeConstitution P cursor)
    (currentDifference : BoundaryDifference P previous)
    (layer : FreeK P previous currentDifference) :
    (FreeConstitution.formed previous currentDifference layer).2 =
      FreeConstitutionCore.formed previous.2 layer.core :=
  rfl

@[simp] theorem FreeConstitution.root_inheritedClosureObstruction_exact
    {P : CircularPresentation} :
    (FreeConstitution.root (P := P)).1.inheritedClosureObstruction =
      P.positiveClosureObstruction :=
  rfl

@[simp] theorem FreeConstitution.formed_inheritedClosureObstruction_exact
    {P : CircularPresentation}
    {cursor : PerimeterCursor P}
    (previous : FreeConstitution P cursor)
    (currentDifference : BoundaryDifference P previous)
    (layer : FreeK P previous currentDifference) :
    BoundaryDifferenceCode.inheritedClosureObstruction
        (FreeConstitution.formed previous currentDifference layer).1 =
      BoundaryDifferenceCode.inheritedClosureObstruction previous.1 :=
  rfl

@[simp] theorem FreeConstitution.formed_integratedClosureObstruction_exact
    {P : CircularPresentation}
    {cursor : PerimeterCursor P}
    (previous : FreeConstitution P cursor)
    (currentDifference : BoundaryDifference P previous)
    (layer : FreeK P previous currentDifference) :
    layer.core.integratedClosureObstruction =
      previous.1.inheritedClosureObstruction :=
  layer.core.integratedClosureObstructionIsCurrent

@[simp] theorem FreeConstitution.formed_integratedProvenance_exact
    {P : CircularPresentation}
    {cursor : PerimeterCursor P}
    (previous : FreeConstitution P cursor)
    (currentDifference : BoundaryDifference P previous)
    (layer : FreeK P previous currentDifference) :
    (FreeConstitution.formed previous currentDifference layer).2 =
      FreeConstitutionCore.formed previous.2 layer.core ∧
    layer.core.integratedProvenance = provenanceAtCursor cursor :=
  ⟨rfl, layer.core.integratedProvenanceIsCurrent⟩

def BoundaryDifference.afterFormation
    {P : CircularPresentation}
    {cursor : PerimeterCursor P}
    (previous : FreeConstitution P cursor)
    (integratedDifference : BoundaryDifference P previous)
    (layer : FreeK P previous integratedDifference) :
    BoundaryDifference P
      (FreeConstitution.formed previous integratedDifference layer) :=
  .exact

def FreeK.formationTerm
    {P : CircularPresentation}
    {cursor : PerimeterCursor P}
    {previous : FreeConstitution P cursor}
    {difference : BoundaryDifference P previous} :
    FreeK P previous difference → FreeKAtom P cursor :=
  fun layer => FreeKCore.formationTerm layer.core

theorem FreeK.formationTerm_is_successor
    {P : CircularPresentation}
    {cursor : PerimeterCursor P}
    {previous : FreeConstitution P cursor}
    {difference : BoundaryDifference P previous}
    (layer : FreeK P previous difference) :
    layer.formationTerm =
      .admissible (successorCompatibleExplicitation cursor) :=
  FreeKCore.formationTermIsSuccessor layer.core

def FreeConstitutionSpace (P : CircularPresentation) : Type _ :=
  Σ cursor : PerimeterCursor P, FreeConstitution P cursor

inductive FormationRecord (P : CircularPresentation) :
    {cursor : PerimeterCursor P} → FreeConstitution P cursor → Type _
  | current
      {cursor}
      {previous : FreeConstitution P cursor}
      {currentDifference : BoundaryDifference P previous}
      {layer : FreeK P previous currentDifference} :
      FormationRecord P
        (FreeConstitution.formed previous currentDifference layer)
  | preserved
      {cursor}
      {previous : FreeConstitution P cursor}
      {currentDifference : BoundaryDifference P previous}
      {layer : FreeK P previous currentDifference} :
      FormationRecord P previous →
      FormationRecord P
        (FreeConstitution.formed previous currentDifference layer)

def PositiveConstitution (P : CircularPresentation) : Type _ :=
  Σ cursor : PerimeterCursor P,
    Σ data : FreeConstitution P cursor, BoundaryDifference P data

def initialPositive (P : CircularPresentation) : PositiveConstitution P :=
  ⟨.within P.perimeter, .root, .initial⟩

def explicitRead {P : CircularPresentation}
    (d : PositiveConstitution P) : ReturnedExplicit P := explicitAt d.1

def implicitRead {P : CircularPresentation}
    (d : PositiveConstitution P) : ReturnedImplicit P := implicitAt d.1

def boundaryDifferenceReadout
    {P : CircularPresentation}
    {cursor : PerimeterCursor P}
    {data : FreeConstitution P cursor}
    (_ : BoundaryDifference P data) : ReturnedDifference P :=
  differenceAtCursor cursor

def boundaryProvenanceReadout
    {P : CircularPresentation}
    {cursor : PerimeterCursor P}
    {data : FreeConstitution P cursor}
    (_ : BoundaryDifference P data) :
    ReturnedProvenance P (differenceAtCursor cursor) :=
  provenanceAtCursor cursor

/- A historical provenance record is indexed by the complete positive origin,
   not merely by its returned readings.  Two origins with coincident readings
   therefore remain different indices.  `integrated` records the exact layer
   that consumed the origin's boundary difference; `preserved` carries this
   record through every later formation. -/
inductive HistoricalProvenanceRecord
    (P : CircularPresentation)
    (origin : PositiveConstitution P) :
    {cursor : PerimeterCursor P} → FreeConstitution P cursor → Type _
  | atOrigin :
      HistoricalProvenanceRecord P origin origin.2.1
  | integrated
      {layer : FreeK P origin.2.1 origin.2.2} :
      HistoricalProvenanceRecord P origin
        (FreeConstitution.formed origin.2.1 origin.2.2 layer)
  | preserved
      {cursor : PerimeterCursor P}
      {previous : FreeConstitution P cursor}
      {difference : BoundaryDifference P previous}
      {layer : FreeK P previous difference} :
      HistoricalProvenanceRecord P origin previous →
      HistoricalProvenanceRecord P origin
        (FreeConstitution.formed previous difference layer)

namespace HistoricalProvenanceRecord

def recordedDifference
    {P : CircularPresentation}
    {origin : PositiveConstitution P}
    {cursor : PerimeterCursor P}
    {targetData : FreeConstitution P cursor}
    (_record : HistoricalProvenanceRecord P origin targetData) :
    ReturnedDifference P :=
  boundaryDifferenceReadout origin.2.2

def recordedProvenance
    {P : CircularPresentation}
    {origin : PositiveConstitution P}
    {cursor : PerimeterCursor P}
    {targetData : FreeConstitution P cursor}
    (record : HistoricalProvenanceRecord P origin targetData) :
    ReturnedProvenance P record.recordedDifference :=
  match record with
  | .atOrigin => boundaryProvenanceReadout origin.2.2
  | .integrated (layer := layer) => layer.core.integratedProvenance
  | .preserved previousRecord => previousRecord.recordedProvenance

theorem recordedProvenance_is_origin
    {P : CircularPresentation}
    {origin : PositiveConstitution P}
    {cursor : PerimeterCursor P}
    {targetData : FreeConstitution P cursor}
    (record : HistoricalProvenanceRecord P origin targetData) :
    record.recordedProvenance =
      boundaryProvenanceReadout origin.2.2 := by
  cases record with
  | atOrigin => rfl
  | integrated =>
      exact FreeKCore.integratedProvenanceIsCurrent _
  | preserved previousRecord =>
      exact recordedProvenance_is_origin previousRecord

end HistoricalProvenanceRecord

def canonicalFreeLayer
    {P : CircularPresentation}
    (source : PositiveConstitution P) :
    FreeK P source.2.1 source.2.2 :=
  .canonical
    (.admissible (successorCompatibleExplicitation source.1)) rfl

def successorFormationTerm
    {P : CircularPresentation}
    (source : PositiveConstitution P) : FreeKAtom P source.1 :=
  .admissible (successorCompatibleExplicitation source.1)

def formationSyntax
    {P : CircularPresentation}
    (source : PositiveConstitution P) : Type _ :=
  FreeKAtom P source.1

structure FreeLayerApplication
    (P : CircularPresentation)
    (source : PositiveConstitution P) where
  algebra : FreeKAlgebra.{uA} P source.1
  realize : FreeKAtom P source.1 → algebra.Carrier
  realizesExplicitPole : realize .explicitPole = algebra.explicitPole
  realizesImplicitPole : realize .implicitPole = algebra.implicitPole
  realizesCurrentDifference :
    realize .currentDifference = algebra.currentDifference
  realizesAdmissible :
    (x : CompatibleExplicitation P source.1) →
      realize (.admissible x) = algebra.admissible x

theorem FreeLayerApplication.realize_eq_fold
    {P : CircularPresentation}
    {source : PositiveConstitution P}
    (application : FreeLayerApplication P source)
    (atom : FreeKAtom P source.1) :
    application.realize atom = FreeKAtom.fold application.algebra atom := by
  cases atom with
  | explicitPole => exact application.realizesExplicitPole
  | implicitPole => exact application.realizesImplicitPole
  | currentDifference => exact application.realizesCurrentDifference
  | admissible compatible => exact application.realizesAdmissible compatible

def canonicalFreeLayerApplication
    {P : CircularPresentation}
    (source : PositiveConstitution P) :
    FreeLayerApplication P source :=
  { algebra :=
      { Carrier := FreeKAtom P source.1
        explicitPole := .explicitPole
        implicitPole := .implicitPole
        currentDifference := .currentDifference
        admissible := .admissible }
    realize := fun atom =>
      FreeKAtom.fold
        { Carrier := FreeKAtom P source.1
          explicitPole := .explicitPole
          implicitPole := .implicitPole
          currentDifference := .currentDifference
          admissible := .admissible }
        atom
    realizesExplicitPole := rfl
    realizesImplicitPole := rfl
    realizesCurrentDifference := rfl
    realizesAdmissible := fun _ => rfl }

def formationEliminator
    {P : CircularPresentation}
    (source : PositiveConstitution P)
    (application : FreeLayerApplication P source) :
    formationSyntax source → application.algebra.Carrier :=
  application.realize

theorem formationEliminator_is_free_fold
    {P : CircularPresentation}
    (source : PositiveConstitution P)
    (application : FreeLayerApplication P source)
    (atom : formationSyntax source) :
    formationEliminator source application atom =
      FreeKAtom.fold application.algebra atom :=
  application.realize_eq_fold atom

@[simp] theorem canonicalFormationEliminator_exact
    {P : CircularPresentation}
    (source : PositiveConstitution P)
    (atom : formationSyntax source) :
    formationEliminator source (canonicalFreeLayerApplication source) atom =
      atom := by
  cases atom <;> rfl

theorem canonicalFreeLayer_is_free_elimination
    {P : CircularPresentation}
    (source : PositiveConstitution P) :
    (canonicalFreeLayer source).formationTerm =
      formationEliminator source (canonicalFreeLayerApplication source)
        (successorFormationTerm source) :=
  (canonicalFormationEliminator_exact source
    (successorFormationTerm source)).symm

def constitutionOf
    {P : CircularPresentation}
    (d : PositiveConstitution P) : FreeConstitutionSpace P :=
  ⟨advanceCursor d.1,
    .formed d.2.1 d.2.2 (canonicalFreeLayer d)⟩

def boundaryDifferenceOf
    {P : CircularPresentation}
    (d : PositiveConstitution P) :
    BoundaryDifference P (constitutionOf d).2 :=
  .afterFormation d.2.1 d.2.2 (canonicalFreeLayer d)

def canonicalTarget
    {P : CircularPresentation}
    (d : PositiveConstitution P) : PositiveConstitution P :=
  ⟨(constitutionOf d).1, (constitutionOf d).2, boundaryDifferenceOf d⟩

@[simp] theorem canonicalTarget_inheritedClosureObstruction_exact
    {P : CircularPresentation}
    (source : PositiveConstitution P) :
    (canonicalTarget source).2.1.1.inheritedClosureObstruction =
      source.2.1.1.inheritedClosureObstruction :=
  rfl

structure IntegratedDifferenceRecord
    {P : CircularPresentation}
    {cursor : PerimeterCursor P}
    {previous : FreeConstitution P cursor}
    (g : BoundaryDifference P previous)
    (target : FreeConstitution P (advanceCursor cursor)) : Type _ where
  layer : FreeK P previous g
  targetIsFormation : target = FreeConstitution.formed previous g layer

def Integrates
    {P : CircularPresentation}
    (source : PositiveConstitution P) : Type _ :=
  IntegratedDifferenceRecord source.2.2 (canonicalTarget source).2.1

namespace HistoricalProvenanceRecord

def ofIntegration
    {P : CircularPresentation}
    {source : PositiveConstitution P}
    (integration : Integrates source) :
    HistoricalProvenanceRecord P source (canonicalTarget source).2.1 := by
  exact Eq.mp
    (congrArg
      (fun targetData => HistoricalProvenanceRecord P source targetData)
      integration.targetIsFormation.symm)
    (HistoricalProvenanceRecord.integrated
      (layer := integration.layer))

end HistoricalProvenanceRecord

structure PreservesProvenance
    {P : CircularPresentation}
    (source target : PositiveConstitution P) : Type _ where
  targetIsCanonical : target = canonicalTarget source
  integrated : Integrates source

namespace PreservesProvenance

def inscribedInTarget
    {P : CircularPresentation}
    {source target : PositiveConstitution P}
    (preserves : PreservesProvenance source target) :
    HistoricalProvenanceRecord P source target.2.1 := by
  cases preserves.targetIsCanonical
  exact HistoricalProvenanceRecord.ofIntegration preserves.integrated

def exactProvenance
    {P : CircularPresentation}
    {source target : PositiveConstitution P}
    (preserves : PreservesProvenance source target) :
    ReturnedProvenance P (boundaryDifferenceReadout source.2.2) :=
  preserves.inscribedInTarget.recordedProvenance

theorem exactProvenance_is_origin
    {P : CircularPresentation}
    {source target : PositiveConstitution P}
    (preserves : PreservesProvenance source target) :
    preserves.exactProvenance =
      boundaryProvenanceReadout source.2.2 :=
  preserves.inscribedInTarget.recordedProvenance_is_origin

end PreservesProvenance

def canonicalPreservesProvenance
    {P : CircularPresentation}
    (source : PositiveConstitution P) :
    PreservesProvenance source (canonicalTarget source) :=
  { targetIsCanonical := rfl
    integrated :=
      { layer := canonicalFreeLayer source
        targetIsFormation := rfl } }

def canonicalSourceProvenanceInscribed
    {P : CircularPresentation}
    (source : PositiveConstitution P) :
    HistoricalProvenanceRecord P source (canonicalTarget source).2.1 :=
  HistoricalProvenanceRecord.ofIntegration
    (canonicalPreservesProvenance source).integrated

structure RecoveredImmediateOrigin
    (P : CircularPresentation)
    {cursor : PerimeterCursor P}
    (target : FreeConstitution P cursor) where
  origin : PositiveConstitution P
  record : HistoricalProvenanceRecord P origin target

def recoverImmediateOriginFromFormation
    {P : CircularPresentation}
    {cursor : PerimeterCursor P}
    {target : FreeConstitution P cursor}
    (formed : FormationRecord P target) :
    RecoveredImmediateOrigin P target := by
  cases formed with
  | @current cursor previous difference layer =>
      exact
        { origin := ⟨cursor, previous, difference⟩
          record := .integrated }
  | @preserved cursor previous difference layer old =>
      exact
        { origin := ⟨cursor, previous, difference⟩
          record := .integrated }

def RecoveredImmediateOrigin.provenance
    {P : CircularPresentation}
    {cursor : PerimeterCursor P}
    {target : FreeConstitution P cursor}
    (recovered : RecoveredImmediateOrigin P target) :
    ReturnedProvenance P recovered.record.recordedDifference :=
  recovered.record.recordedProvenance

structure ContinuesDifference
    {P : CircularPresentation}
    (source : PositiveConstitution P) : Type _ where
  targetBoundaryIsNext :
    (canonicalTarget source).2.2 = boundaryDifferenceOf source

def preserveRecordIntoCanonicalTarget
    {P : CircularPresentation}
    (source : PositiveConstitution P) :
    FormationRecord P source.2.1 →
      FormationRecord P (canonicalTarget source).2.1 := by
  intro old
  change FormationRecord P
    (FreeConstitution.formed source.2.1 source.2.2
      (canonicalFreeLayer source))
  exact .preserved old

def currentRecordInCanonicalTarget
    {P : CircularPresentation}
    (source : PositiveConstitution P) :
    FormationRecord P (canonicalTarget source).2.1 := by
  change FormationRecord P
    (FreeConstitution.formed source.2.1 source.2.2
      (canonicalFreeLayer source))
  exact .current

structure FreshBoundaryDifference
    {P : CircularPresentation}
    (source : PositiveConstitution P) : Type _ where
  continuation : ContinuesDifference source
  freshRecord : FormationRecord P (canonicalTarget source).2.1
  freshRecordIsCurrent :
    freshRecord = currentRecordInCanonicalTarget source
  notPreservedOld :
    (oldRecord : FormationRecord P source.2.1) →
      freshRecord ≠ preserveRecordIntoCanonicalTarget source oldRecord

/- The positive obstruction is not merely carried beside the formation.  The
   free layer consumes that exact obstruction, and the boundary code produced
   by the layer inherits it unchanged. -/
structure IntegratesClosureObstruction
    {P : CircularPresentation}
    (source : PositiveConstitution P) : Type _ where
  integratedByFormation :
    (canonicalFreeLayer source).core.integratedClosureObstruction =
      source.2.1.1.inheritedClosureObstruction
  inheritedByTarget :
    (canonicalTarget source).2.1.1.inheritedClosureObstruction =
      source.2.1.1.inheritedClosureObstruction

structure CanonicalGeneratedLaws
    {P : CircularPresentation}
    (source : PositiveConstitution P) : Type _ where
  compatibility :
    ReturnedCompatible P
      (implicitRead source) (explicitRead (canonicalTarget source))
  compatibilityIsCanonical :
    compatibility = stepCompatibleAt source.1
  preservesProvenance :
    PreservesProvenance source (canonicalTarget source)
  integratesClosureObstruction : IntegratesClosureObstruction source
  continuesDifference : ContinuesDifference source
  freshBoundaryDifference : FreshBoundaryDifference source

structure GeneratedStep
    {P : CircularPresentation}
    (source target : PositiveConstitution P) : Type _ where
  formedByFreeLayer : target = canonicalTarget source
  laws : CanonicalGeneratedLaws source

namespace GeneratedStep

def compatibility
    {P : CircularPresentation}
    {source target : PositiveConstitution P}
    (step : GeneratedStep source target) :
    ReturnedCompatible P (implicitRead source) (explicitRead target) := by
  cases step.formedByFreeLayer
  exact step.laws.compatibility

theorem compatibilityWitnessExact
    {P : CircularPresentation}
    {source target : PositiveConstitution P}
    (step : GeneratedStep source target) :
    HEq step.compatibility (stepCompatibleAt source.1) := by
  cases step.formedByFreeLayer
  exact heq_of_eq step.laws.compatibilityIsCanonical

theorem rejectsAlternativeCompatibility
    {P : CircularPresentation}
    {source target : PositiveConstitution P}
    (step : GeneratedStep source target)
    (alternative :
      ReturnedCompatible P (implicitRead source) (explicitRead target))
    (alternativeIsSeparated :
      HEq alternative (stepCompatibleAt source.1) → False) :
    step.compatibility ≠ alternative := by
  intro equality
  exact alternativeIsSeparated
    ((heq_of_eq equality.symm).trans step.compatibilityWitnessExact)

def integratesCurrentDifference
    {P : CircularPresentation}
    {source target : PositiveConstitution P}
    (step : GeneratedStep source target) : Integrates source :=
  step.laws.preservesProvenance.integrated

def preservesProvenance
    {P : CircularPresentation}
    {source target : PositiveConstitution P}
    (step : GeneratedStep source target) :
    PreservesProvenance source target := by
  cases step.formedByFreeLayer
  exact step.laws.preservesProvenance

theorem provenanceWitnessExact
    {P : CircularPresentation}
    {source target : PositiveConstitution P}
    (step : GeneratedStep source target) :
    step.preservesProvenance.exactProvenance =
      boundaryProvenanceReadout source.2.2 :=
  step.preservesProvenance.exactProvenance_is_origin

def sourceProvenanceInscribedInTarget
    {P : CircularPresentation}
    {source target : PositiveConstitution P}
    (step : GeneratedStep source target) :
    HistoricalProvenanceRecord P source target.2.1 :=
  step.preservesProvenance.inscribedInTarget

def currentFormationRecord
    {P : CircularPresentation}
    {source target : PositiveConstitution P}
    (step : GeneratedStep source target) :
    FormationRecord P target.2.1 := by
  cases step.formedByFreeLayer
  exact step.laws.freshBoundaryDifference.freshRecord

theorem currentFormationRecord_is_current
    {P : CircularPresentation}
    {source target : PositiveConstitution P}
    (step : GeneratedStep source target) :
    HEq step.currentFormationRecord
      (currentRecordInCanonicalTarget source) := by
  cases step.formedByFreeLayer
  exact heq_of_eq
    step.laws.freshBoundaryDifference.freshRecordIsCurrent

theorem rejectsAlternativeProvenance
    {P : CircularPresentation}
    {source target : PositiveConstitution P}
    (step : GeneratedStep source target)
    (alternative :
      ReturnedProvenance P (boundaryDifferenceReadout source.2.2))
    (alternativeIsSeparated :
      alternative ≠ boundaryProvenanceReadout source.2.2) :
    step.preservesProvenance.exactProvenance ≠ alternative := by
  intro equality
  exact alternativeIsSeparated
    (equality.symm.trans step.provenanceWitnessExact)

def continuesDifference
    {P : CircularPresentation}
    {source target : PositiveConstitution P}
    (step : GeneratedStep source target) : ContinuesDifference source :=
  step.laws.continuesDifference

def integratesClosureObstruction
    {P : CircularPresentation}
    {source target : PositiveConstitution P}
    (step : GeneratedStep source target) :
    IntegratesClosureObstruction source :=
  step.laws.integratesClosureObstruction

theorem inheritedClosureObstructionExact
    {P : CircularPresentation}
    {source target : PositiveConstitution P}
    (step : GeneratedStep source target) :
    target.2.1.1.inheritedClosureObstruction =
      source.2.1.1.inheritedClosureObstruction := by
  cases step.formedByFreeLayer
  exact step.laws.integratesClosureObstruction.inheritedByTarget

def freshBoundaryDifference
    {P : CircularPresentation}
    {source target : PositiveConstitution P}
    (step : GeneratedStep source target) : FreshBoundaryDifference source :=
  step.laws.freshBoundaryDifference

end GeneratedStep

def generatedStepOfFreeK
    {P : CircularPresentation}
    (source : PositiveConstitution P) :
    GeneratedStep source (canonicalTarget source) :=
  { formedByFreeLayer := rfl
    laws :=
      { compatibility := stepCompatibleAt source.1
        compatibilityIsCanonical := rfl
        preservesProvenance := canonicalPreservesProvenance source
        integratesClosureObstruction :=
          { integratedByFormation := rfl
            inheritedByTarget := rfl }
        continuesDifference := { targetBoundaryIsNext := rfl }
        freshBoundaryDifference :=
          { continuation := { targetBoundaryIsNext := rfl }
            freshRecord := currentRecordInCanonicalTarget source
            freshRecordIsCurrent := rfl
            notPreservedOld := by
              intro old equality
              cases equality } } }

def generate
    {P : CircularPresentation}
    (source : PositiveConstitution P) :
    Σ target : PositiveConstitution P, GeneratedStep source target :=
  ⟨canonicalTarget source, generatedStepOfFreeK source⟩

/-! ## Proof-relevant histories -/

inductive History
    {State : Type uA}
    (Step : State → State → Type uB) : State → State → Type _
  | root : History Step a a
  | extend : History Step a b → Step b c → History Step a c

namespace History

def append
    {State : Type uA}
    {Step : State → State → Type uB}
    {a b c : State} :
    History Step a b → History Step b c → History Step a c
  | firstHistory, .root => firstHistory
  | firstHistory, .extend continuation step =>
      .extend (append firstHistory continuation) step

def appendRootExact
    {State : Type uA}
    {Step : State → State → Type uB}
    {a b : State}
    (history : History Step a b) :
    append history (.root : History Step b b) = history :=
  rfl

def appendExtendExact
    {State : Type uA}
    {Step : State → State → Type uB}
    {a b c d : State}
    (firstHistory : History Step a b)
    (continuation : History Step b c)
    (step : Step c d) :
    append firstHistory (.extend continuation step) =
      .extend (append firstHistory continuation) step :=
  rfl

@[simp] theorem append_root
    {State : Type uA}
    {Step : State → State → Type uB}
    {a b : State}
    (history : History Step a b) :
    append history (.root : History Step b b) = history := rfl

theorem root_append
    {State : Type uA}
    {Step : State → State → Type uB}
    {a b : State}
    (history : History Step a b) :
    append (.root : History Step a a) history = history := by
  induction history with
  | root => rfl
  | extend history step ih =>
      change History.extend (append .root history) step = .extend history step
      rw [ih]

theorem append_associative
    {State : Type uA}
    {Step : State → State → Type uB}
    {a b c d : State}
    (first : History Step a b)
    (second : History Step b c)
    (third : History Step c d) :
    append (append first second) third =
      append first (append second third) := by
  induction third with
  | root => rfl
  | extend third step ih =>
      change History.extend (append (append first second) third) step =
        History.extend (append first (append second third)) step
      rw [ih]

inductive Occurrence
    {State : Type uA}
    {Step : State → State → Type uB} :
    {a b : State} → History Step a b → Type _
  | last
      {a b c : State}
      {history : History Step a b}
      {step : Step b c} : Occurrence (.extend history step)
  | earlier
      {a b c : State}
      {history : History Step a b}
      {step : Step b c} :
      Occurrence history → Occurrence (.extend history step)

/- An occurrence readout is deliberately only a post-constitutive assignment
   of values to occurrences already carried by one history.  The codomain is
   arbitrary, but no inhabitant, injectivity, faithfulness, or compatibility
   law is supplied by this abbreviation.  Such properties must be stated
   separately; the readout neither creates nor identifies occurrences.

   Conceptually, occurrences and their exact correspondences form a structural
   bus onto which independent readouts can be connected after constitution. -/
abbrev OccurrenceReadout
    {State : Type uA}
    {Step : State → State → Type uB}
    {source target : State}
    (history : History Step source target)
    (Value : Type uV) : Type _ :=
  Occurrence history → Value

/- Structural chronology of step occurrences in one history.  This relation
   carries only precedence information and introduces no numerical rank. -/
inductive OccurrencePrecedes
    {State : Type uA}
    {Step : State → State → Type uB} :
    {a b : State} →
    {history : History Step a b} →
    Occurrence history →
    Occurrence history →
    Prop
  | earlier_last
      {a b c : State}
      {history : History Step a b}
      {step : Step b c}
      (occurrence : Occurrence history) :
      OccurrencePrecedes
        (history := .extend history step)
        (.earlier occurrence)
        .last
  | earlier_earlier
      {a b c : State}
      {history : History Step a b}
      {step : Step b c}
      {first second : Occurrence history} :
      OccurrencePrecedes first second →
      OccurrencePrecedes
        (history := .extend history step)
        (.earlier first)
        (.earlier second)

/- Immediate chronology of step occurrences.  It records that the second
   occurrence is the very next generated step after the first. -/
inductive OccurrenceNext
    {State : Type uA}
    {Step : State → State → Type uB} :
    {a b : State} →
    {history : History Step a b} →
    Occurrence history →
    Occurrence history →
    Prop
  | previous_last
      {a b c d : State}
      {history : History Step a b}
      {previousStep : Step b c}
      {lastStep : Step c d} :
      OccurrenceNext
        (history := .extend (.extend history previousStep) lastStep)
        (.earlier (.last : Occurrence (.extend history previousStep)))
        .last
  | earlier_earlier
      {a b c : State}
      {history : History Step a b}
      {step : Step b c}
      {first second : Occurrence history} :
      OccurrenceNext first second →
      OccurrenceNext
        (history := .extend history step)
        (.earlier first)
        (.earlier second)

namespace OccurrenceNext

theorem toPrecedes
    {State : Type uA}
    {Step : State → State → Type uB}
    {a b : State}
    {history : History Step a b}
    {first second : Occurrence history}
    (next : OccurrenceNext first second) :
    OccurrencePrecedes first second := by
  induction next with
  | previous_last => exact .earlier_last .last
  | earlier_earlier _ inductionHypothesis =>
      exact .earlier_earlier inductionHypothesis

end OccurrenceNext

namespace OccurrencePrecedes

theorem ne
    {State : Type uA}
    {Step : State → State → Type uB}
    {a b : State}
    {history : History Step a b}
    {first second : Occurrence history}
    (precedes : OccurrencePrecedes first second) : first ≠ second := by
  induction precedes with
  | earlier_last _ =>
      intro equality
      cases equality
  | earlier_earlier _ inductionHypothesis =>
      intro equality
      exact inductionHypothesis (Occurrence.earlier.inj equality)

theorem trichotomy
    {State : Type uA}
    {Step : State → State → Type uB}
    {a b : State}
    {history : History Step a b}
    (first second : Occurrence history) :
    first = second ∨
      OccurrencePrecedes first second ∨
        OccurrencePrecedes second first := by
  induction first with
  | last =>
      cases second with
      | last => exact Or.inl rfl
      | earlier second =>
          exact Or.inr (Or.inr (.earlier_last second))
  | earlier first inductionHypothesis =>
      cases second with
      | last =>
          exact Or.inr (Or.inl (.earlier_last first))
      | earlier second =>
          rcases inductionHypothesis second with
            equality | precedes | follows
          · exact Or.inl (congrArg Occurrence.earlier equality)
          · exact Or.inr (Or.inl (.earlier_earlier precedes))
          · exact Or.inr (Or.inr (.earlier_earlier follows))

end OccurrencePrecedes

/- An exactly-one history is characterized structurally, before any numerical
   length is available: it is one extension of the root history. -/
inductive ExactlyOne
    {State : Type uA}
    {Step : State → State → Type uB}
    {source target : State} :
    History Step source target → Type _
  | single (step : Step source target) :
      ExactlyOne (.extend .root step)

structure LocatedStep
    {State : Type uA}
    (Step : State → State → Type uB) where
  source : State
  target : State
  step : Step source target

def Occurrence.locatedStep
    {State : Type uA}
    {Step : State → State → Type uB}
    {a b : State}
    {history : History Step a b} :
    Occurrence history → LocatedStep Step
  | .last (step := step) => ⟨_, _, step⟩
  | .earlier occurrence => occurrence.locatedStep

def Occurrence.gapAt
    {State : Type uA}
    {Step : State → State → Type uB}
    {source target : State}
    {history : History Step source target}
    (occurrence : Occurrence history) :
    Step occurrence.locatedStep.source occurrence.locatedStep.target :=
  occurrence.locatedStep.step

namespace ExactlyOne

def step
    {State : Type uA}
    {Step : State → State → Type uB}
    {source target : State}
    {history : History Step source target}
    (one : ExactlyOne history) : Step source target :=
  match one with
  | .single step => step

def canonicalOccurrence
    {State : Type uA}
    {Step : State → State → Type uB}
    {source target : State}
    {history : History Step source target}
    (one : ExactlyOne history) : Occurrence history :=
  match one with
  | .single _ => .last

theorem occurrence_unique
    {State : Type uA}
    {Step : State → State → Type uB}
    {source target : State}
    {history : History Step source target}
    (one : ExactlyOne history)
    (occurrence : Occurrence history) :
    occurrence = one.canonicalOccurrence := by
  cases one with
  | single step =>
      cases occurrence with
      | last => rfl
      | earlier impossible => cases impossible

theorem locatedStep_source
    {State : Type uA}
    {Step : State → State → Type uB}
    {source target : State}
    {history : History Step source target}
    (one : ExactlyOne history)
    (occurrence : Occurrence history) :
    occurrence.locatedStep.source = source := by
  cases one with
  | single step =>
      cases occurrence with
      | last => rfl
      | earlier impossible => cases impossible

theorem locatedStep_target
    {State : Type uA}
    {Step : State → State → Type uB}
    {source target : State}
    {history : History Step source target}
    (one : ExactlyOne history)
    (occurrence : Occurrence history) :
    occurrence.locatedStep.target = target := by
  cases one with
  | single step =>
      cases occurrence with
      | last => rfl
      | earlier impossible => cases impossible

end ExactlyOne

def embedLeftOccurrence
    {State : Type uA}
    {Step : State → State → Type uB}
    {a b c : State}
    {firstHistory : History Step a b}
    (occurrence : Occurrence firstHistory)
    (continuation : History Step b c) :
    Occurrence (append firstHistory continuation) :=
  match continuation with
  | .root => occurrence
  | .extend continuation _ =>
      .earlier (embedLeftOccurrence occurrence continuation)

theorem embedLeftOccurrence_injective
    {State : Type uA}
    {Step : State → State → Type uB}
    {a b c : State}
    {firstHistory : History Step a b}
    (continuation : History Step b c) :
    Function.Injective
      (fun occurrence : Occurrence firstHistory =>
        embedLeftOccurrence occurrence continuation) := by
  induction continuation with
  | root =>
      intro first second equality
      exact equality
  | extend continuation step inductionHypothesis =>
      intro first second equality
      exact inductionHypothesis (Occurrence.earlier.inj equality)

def embedRightOccurrence
    {State : Type uA}
    {Step : State → State → Type uB}
    {a b c : State}
    (firstHistory : History Step a b)
    {continuation : History Step b c} :
    Occurrence continuation → Occurrence (append firstHistory continuation)
  | @Occurrence.last _ _ _ _ _ history step =>
      (.last : Occurrence (.extend (append firstHistory history) step))
  | @Occurrence.earlier _ _ _ _ _ history step occurrence =>
      .earlier (embedRightOccurrence firstHistory occurrence)

theorem leftRightDisjoint
    {State : Type uA}
    {Step : State → State → Type uB}
    {a b c : State}
    {firstHistory : History Step a b}
    (oldOccurrence : Occurrence firstHistory)
    {continuation : History Step b c}
    (newOccurrence : Occurrence continuation) :
    embedLeftOccurrence oldOccurrence continuation ≠
      embedRightOccurrence firstHistory newOccurrence := by
  induction newOccurrence with
  | last =>
      intro equality
      cases equality
  | earlier occurrence ih =>
      intro equality
      exact ih (Occurrence.earlier.inj equality)

def splitAppendOccurrenceAux
    {State : Type uA}
    {Step : State → State → Type uB}
    {a b c : State}
    (firstHistory : History Step a b) :
    (continuation : History Step b c) →
    Occurrence (append firstHistory continuation) →
      Occurrence firstHistory ⊕ Occurrence continuation
  | .root, occurrence =>
      .inl occurrence
  | .extend previous _step, occurrence =>
      match occurrence with
      | .last => .inr .last
      | .earlier earlier =>
          match splitAppendOccurrenceAux firstHistory previous earlier with
          | .inl old => .inl old
          | .inr new => .inr (.earlier new)

def splitAppendOccurrence
    {State : Type uA}
    {Step : State → State → Type uB}
    {a b c : State}
    {firstHistory : History Step a b}
    {continuation : History Step b c} :
    Occurrence (append firstHistory continuation) →
      Occurrence firstHistory ⊕ Occurrence continuation :=
  splitAppendOccurrenceAux firstHistory continuation

def classifyAppendOccurrence
    {State : Type uA}
    {Step : State → State → Type uB}
    {a b c : State}
    (firstHistory : History Step a b) :
    (continuation : History Step b c) →
    (occurrence : Occurrence (append firstHistory continuation)) →
    (Σ old : Occurrence firstHistory,
      PLift (embedLeftOccurrence old continuation = occurrence)) ⊕
      (Σ new : Occurrence continuation,
        PLift (embedRightOccurrence firstHistory new = occurrence))
  | .root, occurrence => .inl ⟨occurrence, ⟨rfl⟩⟩
  | .extend continuation step, occurrence =>
      match occurrence with
      | .last =>
          .inr ⟨(.last : Occurrence (.extend continuation step)), ⟨rfl⟩⟩
      | .earlier occurrence =>
          match classifyAppendOccurrence firstHistory continuation occurrence with
          | .inl ⟨old, reconstruction⟩ =>
              .inl ⟨old,
                ⟨congrArg Occurrence.earlier reconstruction.down⟩⟩
          | .inr ⟨new, reconstruction⟩ =>
              .inr ⟨Occurrence.earlier new,
                ⟨congrArg Occurrence.earlier reconstruction.down⟩⟩

theorem embedRightOccurrence_injective
    {State : Type uA}
    {Step : State → State → Type uB}
    {a b c : State}
    (firstHistory : History Step a b)
    {continuation : History Step b c} :
    Function.Injective (embedRightOccurrence firstHistory :
      Occurrence continuation → Occurrence (append firstHistory continuation)) := by
  intro first
  induction first with
  | last =>
      intro second equality
      cases second with
      | last => rfl
      | earlier earlier => cases equality
  | earlier first inductionHypothesis =>
      intro second equality
      cases second with
      | last => cases equality
      | earlier second =>
          exact congrArg Occurrence.earlier
            (inductionHypothesis (Occurrence.earlier.inj equality))

theorem locatedStep_embedLeft
    {State : Type uA}
    {Step : State → State → Type uB}
    {a b c : State}
    {firstHistory : History Step a b}
    (occurrence : Occurrence firstHistory)
    (continuation : History Step b c) :
    (embedLeftOccurrence occurrence continuation).locatedStep =
      occurrence.locatedStep := by
  induction continuation with
  | root => rfl
  | extend continuation step inductionHypothesis =>
      exact inductionHypothesis

theorem locatedStep_embedRight
    {State : Type uA}
    {Step : State → State → Type uB}
    {a b c : State}
    (firstHistory : History Step a b)
    {continuation : History Step b c}
    (occurrence : Occurrence continuation) :
    (embedRightOccurrence firstHistory occurrence).locatedStep =
      occurrence.locatedStep := by
  induction occurrence with
  | last => rfl
  | earlier occurrence inductionHypothesis =>
      exact inductionHypothesis
inductive Vertex
    {State : Type uA}
    {Step : State → State → Type uB} :
    {a b : State} → History Step a b → Type _
  | root : Vertex (.root : History Step a a)
  | earlier : Vertex history → Vertex (.extend history step)
  | final : Vertex (.extend history step)

def initialVertex
    {State : Type uA}
    {Step : State → State → Type uB}
    {a b : State}
    (history : History Step a b) : Vertex history :=
  match history with
  | .root => .root
  | .extend previous _ => .earlier (initialVertex previous)

def finalVertex
    {State : Type uA}
    {Step : State → State → Type uB}
    {a b : State}
    (history : History Step a b) : Vertex history :=
  match history with
  | .root => .root
  | .extend _ _ => .final

def vertexAppendLeft
    {State : Type uA}
    {Step : State → State → Type uB}
    {source middle target : State}
    {firstHistory : History Step source middle}
    (vertex : Vertex firstHistory)
    (continuation : History Step middle target) :
    Vertex (append firstHistory continuation) :=
  match continuation with
  | .root => vertex
  | .extend previous _ =>
      .earlier (vertexAppendLeft vertex previous)

def vertexAppendRight
    {State : Type uA}
    {Step : State → State → Type uB}
    {source middle target : State}
    (firstHistory : History Step source middle)
    {continuation : History Step middle target} :
    Vertex continuation → Vertex (append firstHistory continuation) :=
  match continuation with
  | .root => fun _ => finalVertex firstHistory
  | .extend _previous _ => fun vertex =>
      match vertex with
      | .earlier previousVertex =>
          .earlier (vertexAppendRight firstHistory previousVertex)
      | .final => .final

def vertex_append_left := @vertexAppendLeft

def vertex_append_right := @vertexAppendRight

structure Positive
    {State : Type uA}
    (Step : State → State → Type uB)
    (a b : State) where
  predecessor : State
  priorHistory : History Step a predecessor
  lastStep : Step predecessor b

def Positive.toHistory
    {State : Type uA}
    {Step : State → State → Type uB}
    {a b : State}
    (positive : Positive Step a b) : History Step a b :=
  .extend positive.priorHistory positive.lastStep

def Positive.lastOccurrence
    {State : Type uA}
    {Step : State → State → Type uB}
    {a b : State}
    (positive : Positive Step a b) : Occurrence positive.toHistory :=
  .last

inductive View
    {State : Type uA}
    {Step : State → State → Type uB}
    {a : State} : {b : State} → History Step a b → Type _
  | root : View (.root : History Step a a)
  | positive {b : State} (path : Positive Step a b) : View path.toHistory

def view
    {State : Type uA}
    {Step : State → State → Type uB}
    {a b : State}
    (history : History Step a b) : View history := by
  cases history with
  | root => exact .root
  | extend priorHistory step =>
      exact .positive ⟨_, priorHistory, step⟩

def rootOrPositive
    {State : Type uA}
    {Step : State → State → Type uB}
    {source target : State}
    (history : History Step source target) :
    (PLift (target = source) ×
      PLift (HEq history (.root : History Step source source))) ⊕
      (Σ positive : History.Positive Step source target,
        PLift (history = positive.toHistory)) :=
  match history with
  | .root => .inl ⟨⟨rfl⟩, ⟨HEq.rfl⟩⟩
  | .extend priorHistory step =>
      .inr ⟨⟨_, priorHistory, step⟩, ⟨rfl⟩⟩

def appendRootOrPositive
    {State : Type uA}
    {Step : State → State → Type uB}
    {source middle target : State}
    (firstHistory : History Step source middle)
    (continuation : History Step middle target) :
    (PLift (target = middle) ×
      PLift (HEq (append firstHistory continuation) firstHistory)) ⊕
      (Σ positive : History.Positive Step middle target,
        PLift (continuation = positive.toHistory)) :=
  match continuation with
  | .root => .inl ⟨⟨rfl⟩, ⟨HEq.rfl⟩⟩
  | .extend priorHistory step =>
      .inr ⟨⟨_, priorHistory, step⟩, ⟨rfl⟩⟩

end History

abbrev GeneratedHistory
    {P : CircularPresentation}
    (source target : PositiveConstitution P) :=
  History (@GeneratedStep P) source target

theorem generatedHistory_preservesClosureObstruction
    {P : CircularPresentation}
    {source target : PositiveConstitution P}
    (history : GeneratedHistory source target) :
    target.2.1.1.inheritedClosureObstruction =
      source.2.1.1.inheritedClosureObstruction := by
  induction history with
  | root => rfl
  | extend prior step inductionHypothesis =>
      exact step.inheritedClosureObstructionExact.trans inductionHypothesis

structure RootedGeneratedHistory (P : CircularPresentation) where
  endpoint : PositiveConstitution P
  history : GeneratedHistory (initialPositive P) endpoint

/-! ## Occurrence-indexed normative adequacy -/

universe uSpec uAdequacy uRegime uFaithful

/- Normative adequacy is indexed by complete step occurrences.  No projection to
   source, target, cursor, or any returned reading is built into this layer. -/
structure NormativeAdequacy
    (P : CircularPresentation) where
  AlignmentSpec :
    Type uSpec
  RegimeAdequateAtOccurrence :
    AlignmentSpec →
    (R : RootedGeneratedHistory P → Type uRegime) →
    (H : RootedGeneratedHistory P) →
    History.Occurrence H.history →
    Type uAdequacy

/- `AdequateAlong` covers exactly the step occurrences carried by the history.
   The root history has no occurrences, so this type is vacuously inhabited
   there. Any normative obligation on the initial constitution is a separate
   notion and is deliberately not encoded here. -/
abbrev AdequateAlong
    {P : CircularPresentation}
    (N : NormativeAdequacy P)
    (S : N.AlignmentSpec)
    (R : RootedGeneratedHistory P → Type uRegime)
    (H : RootedGeneratedHistory P) : Type _ :=
  (occurrence : History.Occurrence H.history) →
    N.RegimeAdequateAtOccurrence S R H occurrence

/- A regime exit becomes specification-relative only by composing the existing
   typed diagnostic with adequacy witnesses for every step occurrence of the
   same candidate.  The `RegimeExit` kernel is intentionally unchanged. -/
structure SpecRelativeHistoryExit
    {P : CircularPresentation}
    (N : NormativeAdequacy P)
    (S : N.AlignmentSpec)
    (R : RootedGeneratedHistory P → Type uRegime)
    (Faithful : RootedGeneratedHistory P → Type uFaithful) where
  exit :
    AbstractSegmentedTurning.RegimeExit Faithful R
  adequacy :
    AdequateAlong N S R exit.candidate

def RootedGeneratedHistory.terminalClosureObstruction
    {P : CircularPresentation}
    (history : RootedGeneratedHistory P) : PositiveClosureObstruction P :=
  history.endpoint.2.1.1.inheritedClosureObstruction

theorem RootedGeneratedHistory.terminalClosureObstruction_is_initial
    {P : CircularPresentation}
    (history : RootedGeneratedHistory P) :
    history.terminalClosureObstruction = P.positiveClosureObstruction :=
  (generatedHistory_preservesClosureObstruction history.history).trans
    FreeConstitution.root_inheritedClosureObstruction_exact

theorem rootedGeneratedHistory_ext
    {P : CircularPresentation}
    {first second : RootedGeneratedHistory P}
    (endpointEquality : first.endpoint = second.endpoint)
    (historyEquality : HEq first.history second.history) : first = second := by
  cases first with
  | mk firstEndpoint firstHistory =>
      cases second with
      | mk secondEndpoint secondHistory =>
          cases endpointEquality
          have exactHistory : firstHistory = secondHistory := eq_of_heq historyEquality
          cases exactHistory
          rfl

def rootedHistoryRoot (P : CircularPresentation) : RootedGeneratedHistory P :=
  ⟨initialPositive P, .root⟩

def appendRooted
    {P : CircularPresentation}
    (rooted : RootedGeneratedHistory P)
    {target : PositiveConstitution P}
    (continuation : GeneratedHistory rooted.endpoint target) :
    RootedGeneratedHistory P :=
  ⟨target, History.append rooted.history continuation⟩

def appendGenerated
    {P : CircularPresentation}
    (rooted : RootedGeneratedHistory P)
    (generated :
      Σ target : PositiveConstitution P,
        GeneratedStep rooted.endpoint target) :
    RootedGeneratedHistory P :=
  appendRooted rooted (.extend .root generated.2)

def preserveHistoricalProvenanceIntoCanonicalTarget
    {P : CircularPresentation}
    {origin source : PositiveConstitution P} :
    HistoricalProvenanceRecord P origin source.2.1 →
      HistoricalProvenanceRecord P origin (canonicalTarget source).2.1 := by
  intro record
  change HistoricalProvenanceRecord P origin
    (FreeConstitution.formed source.2.1 source.2.2
      (canonicalFreeLayer source))
  exact .preserved record

def preserveHistoricalProvenanceAlongStep
    {P : CircularPresentation}
    {origin source target : PositiveConstitution P}
    (step : GeneratedStep source target) :
    HistoricalProvenanceRecord P origin source.2.1 →
      HistoricalProvenanceRecord P origin target.2.1 := by
  intro record
  cases step.formedByFreeLayer
  exact preserveHistoricalProvenanceIntoCanonicalTarget record

def preserveHistoricalProvenanceAlongHistory
    {P : CircularPresentation}
    {origin source target : PositiveConstitution P} :
    GeneratedHistory source target →
    HistoricalProvenanceRecord P origin source.2.1 →
      HistoricalProvenanceRecord P origin target.2.1
  | .root, record => record
  | .extend history step, record =>
      preserveHistoricalProvenanceAlongStep step
        (preserveHistoricalProvenanceAlongHistory history record)

def preserveFormationRecordAlongStep
    {P : CircularPresentation}
    {source target : PositiveConstitution P}
    (step : GeneratedStep source target) :
    FormationRecord P source.2.1 → FormationRecord P target.2.1 := by
  intro record
  cases step.formedByFreeLayer
  change FormationRecord P
    (FreeConstitution.formed source.2.1 source.2.2
      (canonicalFreeLayer source))
  exact .preserved record

def preserveFormationRecordAlongHistory
    {P : CircularPresentation}
    {source target : PositiveConstitution P} :
    GeneratedHistory source target →
      FormationRecord P source.2.1 → FormationRecord P target.2.1
  | .root, record => record
  | .extend history step, record =>
      preserveFormationRecordAlongStep step
        (preserveFormationRecordAlongHistory history record)

theorem current_ne_preserved
    {P : CircularPresentation}
    {cursor : PerimeterCursor P}
    {previous : FreeConstitution P cursor}
    {difference : BoundaryDifference P previous}
    {layer : FreeK P previous difference}
    (record : FormationRecord P previous) :
    (FormationRecord.current : FormationRecord P
      (FreeConstitution.formed previous difference layer)) ≠
      FormationRecord.preserved record := by
  intro equality
  cases equality

inductive FreshFormationRecord
    (P : CircularPresentation)
    (source : PositiveConstitution P) :
    PositiveConstitution P → Type _
  | after
      {predecessor : PositiveConstitution P}
      {target : PositiveConstitution P}
      (priorHistory : GeneratedHistory source predecessor)
      (lastStep : GeneratedStep predecessor target) :
      FreshFormationRecord P source target

namespace FreshFormationRecord

def predecessor
    {P : CircularPresentation}
    {source target : PositiveConstitution P} :
    FreshFormationRecord P source target → PositiveConstitution P
  | .after (predecessor := predecessor) _ _ => predecessor

def priorHistory
    {P : CircularPresentation}
    {source target : PositiveConstitution P}
    (fresh : FreshFormationRecord P source target) :
    GeneratedHistory source fresh.predecessor := by
  cases fresh with
  | after priorHistory _ => exact priorHistory

def freshRecord
    {P : CircularPresentation}
    {source target : PositiveConstitution P} :
    FreshFormationRecord P source target → FormationRecord P target.2.1
  | .after _ lastStep => by
      cases lastStep.formedByFreeLayer
      exact lastStep.freshBoundaryDifference.freshRecord

def lastStep
    {P : CircularPresentation}
    {source target : PositiveConstitution P}
    (fresh : FreshFormationRecord P source target) :
    GeneratedStep fresh.predecessor target := by
  cases fresh with
  | after _ lastStep => exact lastStep

theorem notFromPredecessor
    {P : CircularPresentation}
    {source target : PositiveConstitution P}
    (fresh : FreshFormationRecord P source target)
    (oldRecord : FormationRecord P fresh.predecessor.2.1) :
  fresh.freshRecord ≠
      preserveFormationRecordAlongStep fresh.lastStep oldRecord := by
  cases fresh with
  | after priorHistory lastStep =>
      cases lastStep.formedByFreeLayer
      exact lastStep.freshBoundaryDifference.notPreservedOld oldRecord

theorem notFromSource
    {P : CircularPresentation}
    {source target : PositiveConstitution P}
    (fresh : FreshFormationRecord P source target)
    (oldRecord : FormationRecord P source.2.1) :
    fresh.freshRecord ≠
      preserveFormationRecordAlongStep fresh.lastStep
        (preserveFormationRecordAlongHistory fresh.priorHistory oldRecord) :=
  fresh.notFromPredecessor _

end FreshFormationRecord

def positiveGeneratedHistory_hasFreshFormation
    {P : CircularPresentation}
    {source target : PositiveConstitution P}
    (positive : History.Positive (@GeneratedStep P) source target) :
    FreshFormationRecord P source target := by
  exact .after positive.priorHistory positive.lastStep

theorem rootedHistoryEq
    {P : CircularPresentation}
    {first second : RootedGeneratedHistory P}
    (endpointEquality : first.endpoint = second.endpoint)
    (historyEquality : HEq first.history second.history) :
    first = second := by
  cases first with
  | mk firstEndpoint firstHistory =>
      cases second with
      | mk secondEndpoint secondHistory =>
          cases endpointEquality
          cases historyEquality
          rfl

structure ConstitutivePrefix
    {P : CircularPresentation}
    (first second : RootedGeneratedHistory P) : Type _ where
  continuation : GeneratedHistory first.endpoint second.endpoint
  historyExact :
    History.append first.history continuation = second.history

structure StrictConstitutivePrefix
    {P : CircularPresentation}
    (first second : RootedGeneratedHistory P) : Type _ where
  continuation : History.Positive
    (@GeneratedStep P) first.endpoint second.endpoint
  historyExact :
    History.append first.history continuation.toHistory = second.history

def prefixReflexive
    {P : CircularPresentation}
    (history : RootedGeneratedHistory P) :
    ConstitutivePrefix history history := ⟨.root, rfl⟩

def prefixTransitive
    {P : CircularPresentation}
    {first second third : RootedGeneratedHistory P} :
    ConstitutivePrefix first second →
    ConstitutivePrefix second third →
    ConstitutivePrefix first third := by
  rintro ⟨left, leftEquality⟩ ⟨right, rightEquality⟩
  refine ⟨History.append left right, ?_⟩
  rw [← History.append_associative, leftEquality, rightEquality]

def generatedStepCursorAdvance
    {P : CircularPresentation}
    {source target : PositiveConstitution P}
    (step : GeneratedStep source target) :
    CursorAdvance P source.1 target.1 := by
  cases step.formedByFreeLayer
  exact cursorAdvanceGraph source.1

inductive CursorReach (P : CircularPresentation) :
    PerimeterCursor P → PerimeterCursor P → Type _
  | root : CursorReach P cursor cursor
  | extend :
      CursorReach P source middle →
      CursorAdvance P middle target →
      CursorReach P source target

def CursorReach.followedByStep
    {P : CircularPresentation}
    {source middle target : PerimeterCursor P} :
    CursorReach P source middle → CursorAdvance P middle target →
      PositiveCursorAdvance P source target
  | .root, step => .one step
  | .extend previous last, step =>
      .followedBy (previous.followedByStep last) step

def CursorReach.trans
    {P : CircularPresentation}
    {source middle target : PerimeterCursor P} :
    CursorReach P source middle → CursorReach P middle target →
      CursorReach P source target
  | left, .root => left
  | left, .extend previous last =>
      .extend (CursorReach.trans left previous) last

def CursorFuture.transReach
    {P : CircularPresentation}
    {source middle target : PerimeterCursor P}
    (future : CursorFuture P source middle) :
    CursorReach P middle target → CursorFuture P source target
  | .root => future
  | .extend previous last =>
      (future.transReach previous).trans last.toFuture

def generatedHistoryCursorReach
    {P : CircularPresentation}
    {source target : PositiveConstitution P} :
    GeneratedHistory source target → CursorReach P source.1 target.1
  | .root => .root
  | .extend history step =>
      .extend (generatedHistoryCursorReach history)
        (generatedStepCursorAdvance step)

def occurrenceSource_to_historyEndpoint_future
    {P : CircularPresentation}
    {source target : PositiveConstitution P}
    : (history : GeneratedHistory source target) →
    (occurrence : History.Occurrence history) →
      CursorFuture P occurrence.locatedStep.source.1 target.1
  | .root, occurrence => nomatch occurrence
  | .extend _history step, .last =>
      (generatedStepCursorAdvance step).toFuture
  | .extend history step, .earlier earlier =>
      (occurrenceSource_to_historyEndpoint_future history earlier).trans
        (generatedStepCursorAdvance step).toFuture

def occurrenceTarget_to_historyEndpoint_reach
    {P : CircularPresentation}
    {source target : PositiveConstitution P}
    : (history : GeneratedHistory source target) →
    (occurrence : History.Occurrence history) →
      CursorReach P occurrence.locatedStep.target.1 target.1
  | .root, occurrence => nomatch occurrence
  | .extend _history step, .last => .root
  | .extend history step, .earlier earlier =>
      .extend (occurrenceTarget_to_historyEndpoint_reach history earlier)
        (generatedStepCursorAdvance step)

namespace History.OccurrencePrecedes

private def earlierLast_next_or_positiveGap
    {P : CircularPresentation}
    {source target nextTarget : PositiveConstitution P}
    : (history : GeneratedHistory source target) →
    (step : GeneratedStep target nextTarget) →
    (occurrence : History.Occurrence history) →
    History.OccurrenceNext
        (.earlier occurrence)
        (.last : History.Occurrence (.extend history step)) ∨
      Nonempty (CursorFuture P
        occurrence.locatedStep.target.1
        (History.Occurrence.last : History.Occurrence
          (.extend history step)).locatedStep.source.1)
  | .root, _step, occurrence => nomatch occurrence
  | .extend _history _previousStep, step, .last => Or.inl .previous_last
  | .extend history previousStep, _step, .earlier earlier =>
      Or.inr ⟨
        ((occurrenceTarget_to_historyEndpoint_reach history earlier).followedByStep
          (generatedStepCursorAdvance previousStep)).toFuture⟩

theorem sourceCursorFuture
    {P : CircularPresentation}
    {source target : PositiveConstitution P}
    {history : GeneratedHistory source target}
    {first second : History.Occurrence history}
    (precedes : History.OccurrencePrecedes first second) :
    Nonempty (CursorFuture P
      first.locatedStep.source.1 second.locatedStep.source.1) := by
  induction precedes with
  | earlier_last occurrence =>
      exact ⟨occurrenceSource_to_historyEndpoint_future _ occurrence⟩
  | earlier_earlier _ inductionHypothesis =>
      exact inductionHypothesis

theorem next_or_positiveGap
    {P : CircularPresentation}
    {source target : PositiveConstitution P}
    {history : GeneratedHistory source target}
    {first second : History.Occurrence history}
    (precedes : History.OccurrencePrecedes first second) :
    History.OccurrenceNext first second ∨
      Nonempty (CursorFuture P
        first.locatedStep.target.1 second.locatedStep.source.1) := by
  induction precedes with
  | earlier_last occurrence =>
      exact earlierLast_next_or_positiveGap _ _ occurrence
  | earlier_earlier _ inductionHypothesis =>
      rcases inductionHypothesis with next | gap
      · exact Or.inl (.earlier_earlier next)
      · exact Or.inr gap

end History.OccurrencePrecedes

def positiveGeneratedHistory_cursorAdvance
    {P : CircularPresentation}
    {source target : PositiveConstitution P}
    (positive : History.Positive (@GeneratedStep P) source target) :
    PositiveCursorAdvance P source.1 target.1 :=
  (generatedHistoryCursorReach positive.priorHistory).followedByStep
    (generatedStepCursorAdvance positive.lastStep)

theorem positiveGeneratedHistory_source_ne_target
    {P : CircularPresentation}
    {source target : PositiveConstitution P}
    (positive : History.Positive (@GeneratedStep P) source target) :
    source ≠ target := by
  intro equality
  have cursorEquality : source.1 = target.1 := congrArg Sigma.fst equality
  exact positiveCursorAdvance_irreflexive
    (cast
      (congrArg (PositiveCursorAdvance P source.1) cursorEquality.symm)
      (positiveGeneratedHistory_cursorAdvance positive))


/- A generated history whose endpoints are equal cannot contain any step
   occurrence.  The root case has no occurrences by construction.  Any
   extended history determines a positive history, whose endpoints are forced
   to be distinct by generated cursor advance. -/
theorem generatedHistory_equalEndpoints_noOccurrence
    {P : CircularPresentation}
    {source target : PositiveConstitution P}
    (history : GeneratedHistory source target)
    (endpointEquality : source = target) :
    History.Occurrence history → False := by
  cases history with
  | root =>
      intro occurrence
      exact nomatch occurrence
  | extend priorHistory step =>
      intro _occurrence
      let positive : History.Positive (@GeneratedStep P) source target :=
        { predecessor := _
          priorHistory := priorHistory
          lastStep := step }
      exact positiveGeneratedHistory_source_ne_target positive endpointEquality


theorem append_positive_ne
    {P : CircularPresentation}
    (history : RootedGeneratedHistory P)
    {target : PositiveConstitution P}
    (positive : History.Positive
      (@GeneratedStep P) history.endpoint target) :
    appendRooted history positive.toHistory ≠ history := by
  intro equality
  have endpointEquality : target = history.endpoint :=
    congrArg RootedGeneratedHistory.endpoint equality
  exact positiveGeneratedHistory_source_ne_target positive endpointEquality.symm

theorem strictPrefix_ne
    {P : CircularPresentation}
    {first second : RootedGeneratedHistory P}
    (strict : StrictConstitutivePrefix first second) : second ≠ first := by
  intro equality
  have appendedEqualsSecond :
      appendRooted first strict.1.toHistory = second :=
    rootedHistoryEq rfl (heq_of_eq strict.2)
  exact append_positive_ne first strict.1
    (appendedEqualsSecond.trans equality)

/-! ## Canonical deployment of the non-closing perimeter -/

def positiveAtRemaining
    (P : CircularPresentation)
    {node : LocalNode
      P.Explicit P.Implicit P.Compatible P.Difference P.Provenance}
    (remaining : PerimeterSpine P.Compatible node)
    (data : FreeConstitution P (.within remaining))
    (difference : BoundaryDifference P data) : PositiveConstitution P :=
  ⟨.within remaining, data, difference⟩

def deployRemaining
    (P : CircularPresentation)
    {node : LocalNode
      P.Explicit P.Implicit P.Compatible P.Difference P.Provenance} :
    (remaining : PerimeterSpine P.Compatible node) →
    (data : FreeConstitution P (.within remaining)) →
    (difference : BoundaryDifference P data) →
    Σ target : PositiveConstitution P,
      GeneratedHistory (positiveAtRemaining P remaining data difference) target
  | @PerimeterSpine.boundary _ _ _ _ _ node, data, difference =>
      ⟨positiveAtRemaining P (.boundary node) data difference, .root⟩
  | @PerimeterSpine.advance _ _ _ _ _ node _nextNode compatible tail,
      data, difference =>
      let source :=
        positiveAtRemaining P (.advance compatible tail) data difference
      let next := canonicalTarget source
      let rest := deployRemaining P tail next.2.1 next.2.2
      ⟨rest.1,
        History.append
          (.extend .root (generatedStepOfFreeK source))
          rest.2⟩

def perimeterDeployment (P : CircularPresentation) : RootedGeneratedHistory P :=
  let deployed := deployRemaining P P.perimeter
    FreeConstitution.root BoundaryDifference.initial
  ⟨deployed.1, deployed.2⟩

def perimeterEndpoint (P : CircularPresentation) : PositiveConstitution P :=
  (perimeterDeployment P).endpoint

def perimeterHistory (P : CircularPresentation) :
    GeneratedHistory (initialPositive P) (perimeterEndpoint P) :=
  (perimeterDeployment P).history

theorem deployRemaining_finalCursor
    (P : CircularPresentation)
    {node : LocalNode
      P.Explicit P.Implicit P.Compatible P.Difference P.Provenance}
    (remaining : PerimeterSpine P.Compatible node)
    (data : FreeConstitution P (.within remaining))
    (difference : BoundaryDifference P data) :
    (deployRemaining P remaining data difference).1.1 =
      .within (.boundary remaining.finalNode) := by
  induction remaining with
  | boundary node => rfl
  | @advance node nextNode compatible tail ih =>
      change
        (deployRemaining P tail
          (canonicalTarget
            (positiveAtRemaining P (.advance compatible tail) data difference)).2.1
          (canonicalTarget
            (positiveAtRemaining P (.advance compatible tail) data difference)).2.2).1.1 =
          .within (.boundary tail.finalNode)
      exact ih _ _

theorem perimeterEndpoint_cursor_boundary
    (P : CircularPresentation) :
    (perimeterEndpoint P).1 =
      .within (.boundary P.perimeter.finalNode) :=
  deployRemaining_finalCursor P P.perimeter
    FreeConstitution.root BoundaryDifference.initial

def generate_after_perimeter
    (P : CircularPresentation) :
    Σ target : PositiveConstitution P,
      GeneratedStep (perimeterEndpoint P) target :=
  generate (perimeterEndpoint P)

theorem generate_after_perimeter_is_beyond
    (P : CircularPresentation) :
    (generate_after_perimeter P).1.1 = .beyond .first := by
  change advanceCursor (perimeterEndpoint P).1 = .beyond .first
  rw [perimeterEndpoint_cursor_boundary]
  rfl

def oneStepAfterPerimeter (P : CircularPresentation) :
    RootedGeneratedHistory P :=
  appendGenerated (perimeterDeployment P) (generate_after_perimeter P)

def oneStepAfterPerimeterStrict
    (P : CircularPresentation) :
    StrictConstitutivePrefix
      (perimeterDeployment P) (oneStepAfterPerimeter P) :=
  { continuation :=
      { predecessor := perimeterEndpoint P
        priorHistory := .root
        lastStep := (generate_after_perimeter P).2 }
    historyExact := rfl }

theorem oneStepAfterPerimeter_ne
    (P : CircularPresentation) :
    oneStepAfterPerimeter P ≠ perimeterDeployment P :=
  fun equality => strictPrefix_ne (oneStepAfterPerimeterStrict P) equality

/- The canonical perimeter and its freely generated successor instantiate the
   circle-independent boundary generator. -/
def perimetralBoundaryGenerator
    (P : CircularPresentation) :
    AbstractSegmentedTurning.BoundaryGenerator
      (RootedGeneratedHistory P) (@StrictConstitutivePrefix P) :=
  { boundary := perimeterDeployment P
    continuation := oneStepAfterPerimeter P
    generates := oneStepAfterPerimeterStrict P
    extensionIrreflexive := fun _history strict =>
      strictPrefix_ne strict rfl }

inductive GeneratedOnlyPath
    {P : CircularPresentation} :
    {source target : PositiveConstitution P} →
    GeneratedHistory source target → Prop
  | root : GeneratedOnlyPath (.root : GeneratedHistory source source)
  | extend
      {source middle : PositiveConstitution P}
      {history : GeneratedHistory source middle}
      (generated : GeneratedOnlyPath history) :
      GeneratedOnlyPath
        (.extend history (generatedStepOfFreeK middle))

def prependGeneratedOnly
    {P : CircularPresentation}
    {source target : PositiveConstitution P}
    {continuation : GeneratedHistory (canonicalTarget source) target}
    (generated : GeneratedOnlyPath continuation) :
    GeneratedOnlyPath
      (History.append
        (.extend .root (generatedStepOfFreeK source)) continuation) :=
  match generated with
  | .root => .extend .root
  | .extend previous => .extend (prependGeneratedOnly previous)

def deployRemaining_generatedOnly
    (P : CircularPresentation)
    {node : LocalNode
      P.Explicit P.Implicit P.Compatible P.Difference P.Provenance}
    (remaining : PerimeterSpine P.Compatible node)
    (data : FreeConstitution P (.within remaining))
    (difference : BoundaryDifference P data) :
    GeneratedOnlyPath (deployRemaining P remaining data difference).2 := by
  induction remaining with
  | boundary node => exact .root
  | @advance node nextNode compatible tail ih =>
      exact prependGeneratedOnly (ih _ _)

def GeneratedOnlyByFreeConstruction
    {P : CircularPresentation}
    (history : RootedGeneratedHistory P) : Prop :=
  GeneratedOnlyPath history.history

def perimeterDeployment_generatedOnly
    (P : CircularPresentation) :
    GeneratedOnlyByFreeConstruction (perimeterDeployment P) :=
  deployRemaining_generatedOnly P P.perimeter
    FreeConstitution.root BoundaryDifference.initial

inductive FreePartialPath
    (P : CircularPresentation) :
    {node : LocalNode
      P.Explicit P.Implicit P.Compatible P.Difference P.Provenance} →
    (remaining : PerimeterSpine P.Compatible node) →
    (data : FreeConstitution P (.within remaining)) →
    (difference : BoundaryDifference P data) →
    GeneratedHistory (initialPositive P)
      (positiveAtRemaining P remaining data difference) → Prop
  | root :
      FreePartialPath P P.perimeter
        FreeConstitution.root
        BoundaryDifference.initial
        (.root : GeneratedHistory (initialPositive P) (initialPositive P))
  | advance
      {node nextNode : LocalNode
        P.Explicit P.Implicit P.Compatible P.Difference P.Provenance}
      {compatible : P.Compatible node.implicit nextNode.explicit}
      {tail : PerimeterSpine P.Compatible nextNode}
      {data : FreeConstitution P (.within (.advance compatible tail))}
      {difference : BoundaryDifference P data}
      {history : GeneratedHistory (initialPositive P)
        (positiveAtRemaining P (.advance compatible tail) data difference)}
      (previous : FreePartialPath P (.advance compatible tail)
        data difference history) :
      FreePartialPath P tail
        (canonicalTarget
          (positiveAtRemaining P (.advance compatible tail) data difference)).2.1
        (canonicalTarget
          (positiveAtRemaining P (.advance compatible tail) data difference)).2.2
        (.extend history
          (generatedStepOfFreeK
            (positiveAtRemaining P (.advance compatible tail) data difference)))

namespace FreePartialPath

def rootedAt
    {P : CircularPresentation}
    {node : LocalNode
      P.Explicit P.Implicit P.Compatible P.Difference P.Provenance}
    {remaining : PerimeterSpine P.Compatible node}
    {data : FreeConstitution P (.within remaining)}
    {difference : BoundaryDifference P data}
    (history : GeneratedHistory (initialPositive P)
      (positiveAtRemaining P remaining data difference)) :
    RootedGeneratedHistory P :=
  ⟨positiveAtRemaining P remaining data difference, history⟩

def completedRooted
    {P : CircularPresentation}
    {node : LocalNode
      P.Explicit P.Implicit P.Compatible P.Difference P.Provenance}
    (remaining : PerimeterSpine P.Compatible node)
    (data : FreeConstitution P (.within remaining))
    (difference : BoundaryDifference P data)
    (history : GeneratedHistory (initialPositive P)
      (positiveAtRemaining P remaining data difference)) :
    RootedGeneratedHistory P :=
  let deployed := deployRemaining P remaining data difference
  ⟨deployed.1, History.append history deployed.2⟩

theorem completion
    {P : CircularPresentation}
    {node : LocalNode
      P.Explicit P.Implicit P.Compatible P.Difference P.Provenance}
    {remaining : PerimeterSpine P.Compatible node}
    {data : FreeConstitution P (.within remaining)}
    {difference : BoundaryDifference P data}
    {history : GeneratedHistory (initialPositive P)
      (positiveAtRemaining P remaining data difference)}
    (partialPath : FreePartialPath P remaining data difference history) :
    completedRooted remaining data difference history =
      perimeterDeployment P := by
  induction partialPath with
  | root =>
      exact rootedHistoryEq
        (first := completedRooted P.perimeter
          FreeConstitution.root BoundaryDifference.initial History.root)
        (second := perimeterDeployment P)
        rfl
        (heq_of_eq
          (History.root_append
            (deployRemaining P P.perimeter
              FreeConstitution.root BoundaryDifference.initial).2))
  | @advance node nextNode compatible tail data difference history previous ih =>
      let source :=
        positiveAtRemaining P (.advance compatible tail) data difference
      let one : GeneratedHistory source (canonicalTarget source) :=
        .extend .root (generatedStepOfFreeK source)
      let rest := deployRemaining P tail
        (canonicalTarget source).2.1 (canonicalTarget source).2.2
      have historyExact :
          History.append history (History.append one rest.2) =
            History.append (History.append history one) rest.2 :=
        (History.append_associative history one rest.2).symm
      have currentEqualsNext :
          completedRooted (.advance compatible tail) data difference history =
            completedRooted tail
              (canonicalTarget source).2.1
              (canonicalTarget source).2.2
              (.extend history (generatedStepOfFreeK source)) :=
        rootedHistoryEq rfl (heq_of_eq historyExact)
      exact currentEqualsNext.symm.trans ih

def finish
    {P : CircularPresentation}
    {node : LocalNode
      P.Explicit P.Implicit P.Compatible P.Difference P.Provenance} :
    (remaining : PerimeterSpine P.Compatible node) →
    (data : FreeConstitution P (.within remaining)) →
    (difference : BoundaryDifference P data) →
    (history : GeneratedHistory (initialPositive P)
      (positiveAtRemaining P remaining data difference)) →
    FreePartialPath P remaining data difference history →
    Σ finalData : FreeConstitution P
        (.within (.boundary remaining.finalNode)),
      Σ finalDifference : BoundaryDifference P finalData,
        Σ finalHistory : GeneratedHistory (initialPositive P)
          (positiveAtRemaining P (.boundary remaining.finalNode)
            finalData finalDifference),
          PLift (FreePartialPath P (.boundary remaining.finalNode)
            finalData finalDifference finalHistory)
  | @PerimeterSpine.boundary _ _ _ _ _ boundaryNode,
      data, difference, history, partialPath =>
      ⟨data, difference, history, ⟨partialPath⟩⟩
  | @PerimeterSpine.advance _ _ _ _ _ sourceNode _nextNode compatible tail,
      data, difference, history, partialPath =>
      finish tail
        (canonicalTarget
          (positiveAtRemaining P (.advance compatible tail)
            data difference)).2.1
        (canonicalTarget
          (positiveAtRemaining P (.advance compatible tail)
            data difference)).2.2
        (.extend history
          (generatedStepOfFreeK
            (positiveAtRemaining P (.advance compatible tail)
              data difference)))
        (.advance partialPath)

end FreePartialPath

inductive FreePartialRealization
    (P : CircularPresentation) : RootedGeneratedHistory P → Type _
  | ofPath
      {node : LocalNode
        P.Explicit P.Implicit P.Compatible P.Difference P.Provenance}
      {remaining : PerimeterSpine P.Compatible node}
      {data : FreeConstitution P (.within remaining)}
      {difference : BoundaryDifference P data}
      {history : GeneratedHistory (initialPositive P)
        (positiveAtRemaining P remaining data difference)} :
      FreePartialPath P remaining data difference history →
      FreePartialRealization P
        ⟨positiveAtRemaining P remaining data difference, history⟩

def prefixFromCompletedRooted
    {P : CircularPresentation}
    (current : RootedGeneratedHistory P)
    {target : PositiveConstitution P}
    (continuation : GeneratedHistory current.endpoint target)
    (completion : appendRooted current continuation = perimeterDeployment P) :
    ConstitutivePrefix current (perimeterDeployment P) :=
  Eq.rec
    (motive := fun completed _ => ConstitutivePrefix current completed)
    (⟨continuation, rfl⟩ :
      ConstitutivePrefix current (appendRooted current continuation))
    completion

def partial_is_prefix_of_perimeter
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P} :
    FreePartialRealization P history →
      ConstitutivePrefix history (perimeterDeployment P)
  | .ofPath partialPath => by
      exact prefixFromCompletedRooted _
        (deployRemaining P _ _ _).2 partialPath.completion

def transportFreePartialRealization
    {P : CircularPresentation}
    {first second : RootedGeneratedHistory P}
    (equality : first = second) :
    FreePartialRealization P first → FreePartialRealization P second :=
  Eq.rec
    (motive := fun target _ =>
      FreePartialRealization P first → FreePartialRealization P target)
    (fun realization => realization)
    equality

def perimeterPartialPath (P : CircularPresentation) :
    FreePartialRealization P (perimeterDeployment P) := by
  let rootPath := FreePartialPath.root (P := P)
  let finished := FreePartialPath.finish P.perimeter
    FreeConstitution.root BoundaryDifference.initial History.root rootPath
  let finishedRooted : RootedGeneratedHistory P :=
    ⟨positiveAtRemaining P (.boundary P.perimeter.finalNode)
        finished.1 finished.2.1,
      finished.2.2.1⟩
  have exactPerimeter : finishedRooted = perimeterDeployment P := by
    simpa only [finishedRooted, FreePartialPath.completedRooted,
      deployRemaining, History.append] using
      finished.2.2.2.down.completion
  exact transportFreePartialRealization exactPerimeter
    (.ofPath finished.2.2.2.down)

def perimeterIsFreePartial (P : CircularPresentation) :
    FreePartialRealization P (perimeterDeployment P) :=
  perimeterPartialPath P

def deployPositionToOccurrence
    (P : CircularPresentation)
    {node : LocalNode
      P.Explicit P.Implicit P.Compatible P.Difference P.Provenance} :
    (remaining : PerimeterSpine P.Compatible node) →
    (data : FreeConstitution P (.within remaining)) →
    (difference : BoundaryDifference P data) →
    NonClosingPosition remaining →
      History.Occurrence (deployRemaining P remaining data difference).2
  | @PerimeterSpine.advance _ _ _ _ _ sourceNode _nextNode compatible tail,
      data, difference, .here =>
      History.embedLeftOccurrence
        (.last : History.Occurrence
          (.extend .root (generatedStepOfFreeK
            (positiveAtRemaining P (.advance compatible tail) data difference))))
        (deployRemaining P tail
          (canonicalTarget
            (positiveAtRemaining P (.advance compatible tail) data difference)).2.1
          (canonicalTarget
            (positiveAtRemaining P (.advance compatible tail) data difference)).2.2).2
  | @PerimeterSpine.advance _ _ _ _ _ sourceNode _nextNode compatible tail,
      data, difference, .later position =>
      History.embedRightOccurrence
        (.extend .root (generatedStepOfFreeK
          (positiveAtRemaining P (.advance compatible tail) data difference)))
        (deployPositionToOccurrence P tail
          (canonicalTarget
            (positiveAtRemaining P (.advance compatible tail) data difference)).2.1
          (canonicalTarget
            (positiveAtRemaining P (.advance compatible tail) data difference)).2.2
          position)

def classifyDeploymentOccurrence
    {State : Type uA}
    {Step : State → State → Type uB}
    {source middle target : State}
    {firstStep : Step source middle}
    (continuation : History Step middle target)
    (occurrence : History.Occurrence
      (History.append (.extend .root firstStep) continuation)) :
    PLift (occurrence = History.embedLeftOccurrence
      (.last : History.Occurrence (.extend .root firstStep)) continuation) ⊕
      (Σ later : History.Occurrence continuation,
        PLift (occurrence = History.embedRightOccurrence
          (.extend .root firstStep) later)) := by
  cases History.classifyAppendOccurrence
      (.extend .root firstStep) continuation occurrence with
  | inl firstData =>
      rcases firstData with ⟨first, reconstruction⟩
      cases first with
      | last =>
          apply Sum.inl
          exact ⟨reconstruction.down.symm⟩
      | earlier earlier => exact nomatch earlier
  | inr laterData =>
      rcases laterData with ⟨later, reconstruction⟩
      apply Sum.inr
      exact ⟨later, ⟨reconstruction.down.symm⟩⟩

def decodeDeploymentOccurrence
    (P : CircularPresentation)
    {node : LocalNode
      P.Explicit P.Implicit P.Compatible P.Difference P.Provenance} :
    (remaining : PerimeterSpine P.Compatible node) →
    (data : FreeConstitution P (.within remaining)) →
    (difference : BoundaryDifference P data) →
    (occurrence : History.Occurrence
      (deployRemaining P remaining data difference).2) →
      Σ position : NonClosingPosition remaining,
        PLift (deployPositionToOccurrence P remaining data difference position =
          occurrence)
  | @PerimeterSpine.boundary _ _ _ _ _ boundaryNode,
      _data, _difference, occurrence => nomatch occurrence
  | @PerimeterSpine.advance _ _ _ _ _ sourceNode _nextNode compatible tail,
      data, difference, occurrence =>
      match classifyDeploymentOccurrence
          (deployRemaining P tail
            (canonicalTarget
              (positiveAtRemaining P (.advance compatible tail)
                data difference)).2.1
            (canonicalTarget
              (positiveAtRemaining P (.advance compatible tail)
                data difference)).2.2).2
          occurrence with
      | .inl hereExact =>
          ⟨NonClosingPosition.here, ⟨hereExact.down.symm⟩⟩
      | .inr ⟨later, laterExact⟩ =>
          let decoded := decodeDeploymentOccurrence P tail
              (canonicalTarget
                (positiveAtRemaining P (.advance compatible tail)
                  data difference)).2.1
              (canonicalTarget
                (positiveAtRemaining P (.advance compatible tail)
                  data difference)).2.2
              later
          ⟨NonClosingPosition.later decoded.1,
            ⟨(congrArg
              (History.embedRightOccurrence
                (.extend .root (generatedStepOfFreeK
                  (positiveAtRemaining P (.advance compatible tail)
                    data difference))))
              decoded.2.down).trans laterExact.down.symm⟩⟩

def deployOccurrenceToPosition
    (P : CircularPresentation)
    {node : LocalNode
      P.Explicit P.Implicit P.Compatible P.Difference P.Provenance}
    (remaining : PerimeterSpine P.Compatible node)
    (data : FreeConstitution P (.within remaining))
    (difference : BoundaryDifference P data)
    (occurrence : History.Occurrence
      (deployRemaining P remaining data difference).2) :
    NonClosingPosition remaining :=
  (decodeDeploymentOccurrence P remaining data difference occurrence).1

theorem deployOccurrence_position_roundTrip
    (P : CircularPresentation)
    {node : LocalNode
      P.Explicit P.Implicit P.Compatible P.Difference P.Provenance}
    (remaining : PerimeterSpine P.Compatible node)
    (data : FreeConstitution P (.within remaining))
    (difference : BoundaryDifference P data)
    (occurrence : History.Occurrence
      (deployRemaining P remaining data difference).2) :
    deployPositionToOccurrence P remaining data difference
      (deployOccurrenceToPosition P remaining data difference occurrence) =
        occurrence :=
  (decodeDeploymentOccurrence P remaining data difference occurrence).2.down

theorem deployPositionToOccurrence_injective
    (P : CircularPresentation)
    {node : LocalNode
      P.Explicit P.Implicit P.Compatible P.Difference P.Provenance}
    (remaining : PerimeterSpine P.Compatible node)
    (data : FreeConstitution P (.within remaining))
    (difference : BoundaryDifference P data) :
    Function.Injective
      (deployPositionToOccurrence P remaining data difference) := by
  induction remaining with
  | boundary node =>
      intro first
      exact nomatch first
  | @advance node nextNode compatible tail inductionHypothesis =>
      intro first second equality
      cases first with
      | here =>
          cases second with
          | here => rfl
          | later second =>
              exact False.elim (History.leftRightDisjoint
                (.last : History.Occurrence
                  (.extend .root (generatedStepOfFreeK
                    (positiveAtRemaining P (.advance compatible tail)
                      data difference))))
                (deployPositionToOccurrence P tail _ _ second) equality)
      | later first =>
          cases second with
          | here =>
              exact False.elim (History.leftRightDisjoint
                (.last : History.Occurrence
                  (.extend .root (generatedStepOfFreeK
                    (positiveAtRemaining P (.advance compatible tail)
                      data difference))))
                (deployPositionToOccurrence P tail _ _ first) equality.symm)
          | later second =>
              apply congrArg NonClosingPosition.later
              apply inductionHypothesis _ _
              exact History.embedRightOccurrence_injective _ equality

theorem deployPosition_occurrence_roundTrip
    (P : CircularPresentation)
    {node : LocalNode
      P.Explicit P.Implicit P.Compatible P.Difference P.Provenance}
    (remaining : PerimeterSpine P.Compatible node)
    (data : FreeConstitution P (.within remaining))
    (difference : BoundaryDifference P data)
    (position : NonClosingPosition remaining) :
    deployOccurrenceToPosition P remaining data difference
      (deployPositionToOccurrence P remaining data difference position) =
        position := by
  induction position with
  | @here node nextNode compatible tail =>
      apply deployPositionToOccurrence_injective P
        (.advance compatible tail) data difference
      exact deployOccurrence_position_roundTrip P _ _ _
        (deployPositionToOccurrence P (.advance compatible tail)
          data difference .here)
  | @later node nextNode compatible tail position inductionHypothesis =>
      apply deployPositionToOccurrence_injective P
        (.advance compatible tail) data difference
      exact deployOccurrence_position_roundTrip P _ _ _
        (deployPositionToOccurrence P (.advance compatible tail)
          data difference (.later position))

def requirementToOccurrence
    (P : CircularPresentation) :
    NonClosingPosition P.perimeter →
      History.Occurrence (perimeterHistory P) :=
  deployPositionToOccurrence P P.perimeter
    FreeConstitution.root BoundaryDifference.initial

def occurrenceToRequirement
    (P : CircularPresentation) :
    History.Occurrence (perimeterHistory P) →
      NonClosingPosition P.perimeter :=
  deployOccurrenceToPosition P P.perimeter
    FreeConstitution.root BoundaryDifference.initial

theorem occurrenceToRequirement_toOccurrence
    (P : CircularPresentation)
    (occurrence : History.Occurrence (perimeterHistory P)) :
    requirementToOccurrence P (occurrenceToRequirement P occurrence) =
      occurrence :=
  deployOccurrence_position_roundTrip P P.perimeter
    FreeConstitution.root BoundaryDifference.initial occurrence

theorem requirementToOccurrence_toRequirement
    (P : CircularPresentation)
    (position : NonClosingPosition P.perimeter) :
    occurrenceToRequirement P (requirementToOccurrence P position) =
      position :=
  deployPosition_occurrence_roundTrip P P.perimeter
    FreeConstitution.root BoundaryDifference.initial position

/- These maps only reindex a supplied readout along the already established
   perimeter/occurrence correspondence.  They add no values and assert no
   semantic adequacy of the supplied readout. -/
def perimeterReadout
    {P : CircularPresentation}
    {Value : Type uV}
    (readout : History.OccurrenceReadout (perimeterHistory P) Value) :
    NonClosingPosition P.perimeter → Value :=
  fun position => readout (requirementToOccurrence P position)

def occurrenceReadoutOfPerimeter
    {P : CircularPresentation}
    {Value : Type uV}
    (readout : NonClosingPosition P.perimeter → Value) :
    History.OccurrenceReadout (perimeterHistory P) Value :=
  fun occurrence => readout (occurrenceToRequirement P occurrence)

theorem occurrenceReadoutOfPerimeter_perimeterReadout
    {P : CircularPresentation}
    {Value : Type uV}
    (readout : History.OccurrenceReadout (perimeterHistory P) Value)
    (occurrence : History.Occurrence (perimeterHistory P)) :
    occurrenceReadoutOfPerimeter (perimeterReadout readout) occurrence =
      readout occurrence := by
  change readout
      (requirementToOccurrence P (occurrenceToRequirement P occurrence)) =
    readout occurrence
  rw [occurrenceToRequirement_toOccurrence]

theorem perimeterReadout_occurrenceReadoutOfPerimeter
    {P : CircularPresentation}
    {Value : Type uV}
    (readout : NonClosingPosition P.perimeter → Value)
    (position : NonClosingPosition P.perimeter) :
    perimeterReadout (occurrenceReadoutOfPerimeter readout) position =
      readout position := by
  change readout
      (occurrenceToRequirement P (requirementToOccurrence P position)) =
    readout position
  rw [requirementToOccurrence_toRequirement]

theorem requirementToOccurrence_injective
    (P : CircularPresentation) :
    Function.Injective (requirementToOccurrence P) := by
  intro first second equality
  exact (requirementToOccurrence_toRequirement P first).symm.trans
    ((congrArg (occurrenceToRequirement P) equality).trans
      (requirementToOccurrence_toRequirement P second))

def positionSourceStateAux
    (P : CircularPresentation)
    {node : LocalNode
      P.Explicit P.Implicit P.Compatible P.Difference P.Provenance} :
    (remaining : PerimeterSpine P.Compatible node) →
    (data : FreeConstitution P (.within remaining)) →
    (difference : BoundaryDifference P data) →
    NonClosingPosition remaining → PositiveConstitution P
  | @PerimeterSpine.advance _ _ _ _ _ sourceNode _nextNode compatible tail,
      data, difference, .here =>
      positiveAtRemaining P (.advance compatible tail) data difference
  | @PerimeterSpine.advance _ _ _ _ _ sourceNode _nextNode compatible tail,
      data, difference, .later position =>
      positionSourceStateAux P tail
        (canonicalTarget
          (positiveAtRemaining P (.advance compatible tail) data difference)).2.1
        (canonicalTarget
          (positiveAtRemaining P (.advance compatible tail) data difference)).2.2
        position

def positionSourceState
    (P : CircularPresentation)
    {node : LocalNode
      P.Explicit P.Implicit P.Compatible P.Difference P.Provenance}
    {remaining : PerimeterSpine P.Compatible node}
    (data : FreeConstitution P (.within remaining))
    (difference : BoundaryDifference P data)
    (position : NonClosingPosition remaining) : PositiveConstitution P :=
  positionSourceStateAux P remaining data difference position

def positionTargetState
    (P : CircularPresentation)
    {node : LocalNode
      P.Explicit P.Implicit P.Compatible P.Difference P.Provenance}
    {remaining : PerimeterSpine P.Compatible node}
    (data : FreeConstitution P (.within remaining))
    (difference : BoundaryDifference P data)
    (position : NonClosingPosition remaining) : PositiveConstitution P :=
  canonicalTarget (positionSourceState P data difference position)

private def positionSourceCursorReachAux
    (P : CircularPresentation)
    {node : LocalNode
      P.Explicit P.Implicit P.Compatible P.Difference P.Provenance}
    (remaining : PerimeterSpine P.Compatible node)
    (data : FreeConstitution P (.within remaining))
    (difference : BoundaryDifference P data)
    (position : NonClosingPosition remaining) :
    CursorReach P (.within remaining)
      (positionSourceState P data difference position).1 :=
  match remaining, position with
  | .advance _compatible _tail, .here => .root
  | .advance compatible tail, .later position =>
      let source :=
        positiveAtRemaining P (.advance compatible tail) data difference
      let target := canonicalTarget source
      have firstReach :
          CursorReach P (.within (.advance compatible tail)) target.1 :=
        .extend .root
          (generatedStepCursorAdvance (generatedStepOfFreeK source))
      CursorReach.trans firstReach
        (positionSourceCursorReachAux P tail target.2.1 target.2.2 position)

def positionSourceCursorReach
    (P : CircularPresentation)
    {node : LocalNode
      P.Explicit P.Implicit P.Compatible P.Difference P.Provenance}
    {remaining : PerimeterSpine P.Compatible node}
    (data : FreeConstitution P (.within remaining))
    (difference : BoundaryDifference P data)
    (position : NonClosingPosition remaining) :
    CursorReach P (.within remaining)
      (positionSourceState P data difference position).1 :=
  positionSourceCursorReachAux P remaining data difference position

def positionLocatedStep
    (P : CircularPresentation)
    {node : LocalNode
      P.Explicit P.Implicit P.Compatible P.Difference P.Provenance}
    {remaining : PerimeterSpine P.Compatible node}
    (data : FreeConstitution P (.within remaining))
    (difference : BoundaryDifference P data)
    (position : NonClosingPosition remaining) :
    History.LocatedStep (@GeneratedStep P) :=
  ⟨positionSourceState P data difference position,
    positionTargetState P data difference position,
    generatedStepOfFreeK (positionSourceState P data difference position)⟩

namespace NonClosingPrecedes

private theorem sourceCursorFutureAt
    {P : CircularPresentation}
    {node : LocalNode
      P.Explicit P.Implicit P.Compatible P.Difference P.Provenance}
    {remaining : PerimeterSpine P.Compatible node}
    {first second : NonClosingPosition remaining}
    (precedes : NonClosingPrecedes remaining first second)
    (data : FreeConstitution P (.within remaining))
    (difference : BoundaryDifference P data) :
    Nonempty (CursorFuture P
      (positionSourceState P data difference first).1
      (positionSourceState P data difference second).1) := by
  induction precedes with
  | @here_later node nextNode nextCompatible tail position =>
      let source :=
        positiveAtRemaining P (.advance nextCompatible tail) data difference
      let target := canonicalTarget source
      have firstFuture : CursorFuture P source.1 target.1 :=
        (generatedStepCursorAdvance (generatedStepOfFreeK source)).toFuture
      exact ⟨firstFuture.transReach
        (positionSourceCursorReach P target.2.1 target.2.2 position)⟩
  | @later_later node nextNode nextCompatible tail first second precedes inductionHypothesis =>
      let source :=
        positiveAtRemaining P (.advance nextCompatible tail) data difference
      let target := canonicalTarget source
      exact inductionHypothesis target.2.1 target.2.2

end NonClosingPrecedes

namespace NonClosingNext

/- Canonically adjacent non-closing positions meet at exactly the same
   positive constitution: the target of the first required step is the source
   of the second.  This is structural adjacency, not a numerical rank fact. -/
theorem target_eq_source
    {P : CircularPresentation}
    {node : LocalNode
      P.Explicit P.Implicit P.Compatible P.Difference P.Provenance}
    {remaining : PerimeterSpine P.Compatible node}
    {first second : NonClosingPosition remaining}
    (next : NonClosingNext remaining first second)
    (data : FreeConstitution P (.within remaining))
    (difference : BoundaryDifference P data) :
    (positionLocatedStep P data difference first).target =
      (positionLocatedStep P data difference second).source := by
  induction next with
  | @here_next node nextNode thirdNode firstCompatible secondCompatible tail =>
      rfl
  | @later_next node nextNode nextCompatible tail first second next inductionHypothesis =>
      let source :=
        positiveAtRemaining P (.advance nextCompatible tail) data difference
      exact inductionHypothesis
        (canonicalTarget source).2.1
        (canonicalTarget source).2.2

end NonClosingNext


theorem deployPosition_locatedStep
    (P : CircularPresentation)
    {node : LocalNode
      P.Explicit P.Implicit P.Compatible P.Difference P.Provenance}
    {remaining : PerimeterSpine P.Compatible node}
    (data : FreeConstitution P (.within remaining))
    (difference : BoundaryDifference P data)
    (position : NonClosingPosition remaining) :
    (deployPositionToOccurrence P remaining data difference position).locatedStep =
      positionLocatedStep P data difference position := by
  induction position with
  | @here sourceNode nextNode compatible tail =>
      exact History.locatedStep_embedLeft
        (.last : History.Occurrence
          (.extend .root (generatedStepOfFreeK
            (positiveAtRemaining P (.advance compatible tail)
              data difference))))
        (deployRemaining P tail
          (canonicalTarget
            (positiveAtRemaining P (.advance compatible tail)
              data difference)).2.1
          (canonicalTarget
            (positiveAtRemaining P (.advance compatible tail)
              data difference)).2.2).2
  | @later sourceNode nextNode compatible tail position inductionHypothesis =>
      exact (History.locatedStep_embedRight
        (.extend .root (generatedStepOfFreeK
          (positiveAtRemaining P (.advance compatible tail)
            data difference)))
        (deployPositionToOccurrence P tail _ _ position)).trans
          (inductionHypothesis _ _)

def perimeterPositionSource
    (P : CircularPresentation)
    (position : NonClosingPosition P.perimeter) : PositiveConstitution P :=
  positionSourceState P FreeConstitution.root
    BoundaryDifference.initial position

def perimeterPositionTarget
    (P : CircularPresentation)
    (position : NonClosingPosition P.perimeter) : PositiveConstitution P :=
  positionTargetState P FreeConstitution.root
    BoundaryDifference.initial position

namespace NonClosingPrecedes

theorem sourceCursorFuture
    {P : CircularPresentation}
    {first second : NonClosingPosition P.perimeter}
    (precedes : NonClosingPrecedes P.perimeter first second) :
    Nonempty (CursorFuture P
      (perimeterPositionSource P first).1
      (perimeterPositionSource P second).1) :=
  sourceCursorFutureAt precedes
    FreeConstitution.root BoundaryDifference.initial

end NonClosingPrecedes

abbrev ExactCompatibleTransport := ExactTypeTransport

abbrev ExactProvenanceTransport := ExactTypeTransport

/- A generated occurrence in a rooted history is determined by its source
   cursor.  The proof stays at the structural layer: it follows the unary
   formation depth, uses the canonical generated successor, and excludes two
   distinct depths at one cursor by `CursorFuture.irreflexive`.  No numerical
   rank or readout is used. -/
private theorem freeKCore_uniqueForCursorAgreement
    {P : CircularPresentation}
    {cursor : PerimeterCursor P}
    {code : BoundaryDifferenceCode P cursor}
    (first second : FreeKCore P cursor code) : first = second := by
  cases first with
  | mk formationTerm formationExact obstruction obstructionExact
      provenance provenanceExact =>
    cases second with
    | mk formationTerm' formationExact' obstruction' obstructionExact'
        provenance' provenanceExact' =>
      cases formationExact
      cases formationExact'
      cases obstructionExact
      cases obstructionExact'
      cases provenanceExact
      cases provenanceExact'
      rfl

private theorem freeK_uniqueForCursorAgreement
    {P : CircularPresentation}
    {cursor : PerimeterCursor P}
    {previous : FreeConstitution P cursor}
    {difference : BoundaryDifference P previous}
    (first second : FreeK P previous difference) : first = second := by
  cases first with
  | mk core =>
    cases second with
    | mk core' =>
      exact congrArg FreeK.mk
        (freeKCore_uniqueForCursorAgreement core core')

private theorem integrates_uniqueForCursorAgreement
    {P : CircularPresentation}
    {source : PositiveConstitution P}
    (first second : Integrates source) : first = second := by
  cases first with
  | mk firstLayer firstExact =>
    cases second with
    | mk secondLayer secondExact =>
      have layerExact : firstLayer = secondLayer :=
        freeK_uniqueForCursorAgreement firstLayer secondLayer
      cases layerExact
      rfl

private theorem preservesProvenance_uniqueForCursorAgreement
    {P : CircularPresentation}
    {source target : PositiveConstitution P}
    (first second : PreservesProvenance source target) : first = second := by
  cases first with
  | mk firstTarget firstIntegrated =>
    cases second with
    | mk secondTarget secondIntegrated =>
      cases firstTarget
      cases secondTarget
      exact congrArg (PreservesProvenance.mk rfl)
        (integrates_uniqueForCursorAgreement firstIntegrated secondIntegrated)

private theorem integratesClosureObstruction_uniqueForCursorAgreement
    {P : CircularPresentation}
    {source : PositiveConstitution P}
    (first second : IntegratesClosureObstruction source) : first = second := by
  cases first
  cases second
  rfl

private theorem continuesDifference_uniqueForCursorAgreement
    {P : CircularPresentation}
    {source : PositiveConstitution P}
    (first second : ContinuesDifference source) : first = second := by
  cases first
  cases second
  rfl

private theorem freshBoundaryDifference_uniqueForCursorAgreement
    {P : CircularPresentation}
    {source : PositiveConstitution P}
    (first second : FreshBoundaryDifference source) : first = second := by
  cases first with
  | mk firstContinuation firstRecord firstRecordExact firstFresh =>
    cases second with
    | mk secondContinuation secondRecord secondRecordExact secondFresh =>
      have continuationExact : firstContinuation = secondContinuation :=
        continuesDifference_uniqueForCursorAgreement
          firstContinuation secondContinuation
      have recordExact : firstRecord = secondRecord :=
        firstRecordExact.trans secondRecordExact.symm
      cases continuationExact
      cases recordExact
      rfl

private theorem canonicalGeneratedLaws_uniqueForCursorAgreement
    {P : CircularPresentation}
    {source : PositiveConstitution P}
    (first second : CanonicalGeneratedLaws source) : first = second := by
  cases first with
  | mk firstCompatibility firstCompatibilityExact firstProvenance
      firstObstruction firstDifference firstFresh =>
    cases second with
    | mk secondCompatibility secondCompatibilityExact secondProvenance
      secondObstruction secondDifference secondFresh =>
      have compatibilityExact : firstCompatibility = secondCompatibility :=
        firstCompatibilityExact.trans secondCompatibilityExact.symm
      have provenanceExact : firstProvenance = secondProvenance :=
        preservesProvenance_uniqueForCursorAgreement
          firstProvenance secondProvenance
      have obstructionExact : firstObstruction = secondObstruction :=
        integratesClosureObstruction_uniqueForCursorAgreement
          firstObstruction secondObstruction
      have differenceExact : firstDifference = secondDifference :=
        continuesDifference_uniqueForCursorAgreement
          firstDifference secondDifference
      have freshExact : firstFresh = secondFresh :=
        freshBoundaryDifference_uniqueForCursorAgreement firstFresh secondFresh
      cases compatibilityExact
      cases provenanceExact
      cases obstructionExact
      cases differenceExact
      cases freshExact
      rfl

private theorem generatedStep_uniqueForCursorAgreement
    {P : CircularPresentation}
    {source target : PositiveConstitution P}
    (first second : GeneratedStep source target) : first = second := by
  cases first with
  | mk firstTarget firstLaws =>
    cases second with
    | mk secondTarget secondLaws =>
      exact congrArg (GeneratedStep.mk firstTarget)
        (canonicalGeneratedLaws_uniqueForCursorAgreement
          firstLaws secondLaws)

private theorem locatedStep_eq_of_source_eq
    {P : CircularPresentation}
    (first second : History.LocatedStep (@GeneratedStep P))
    (sourceExact : first.source = second.source) : first = second := by
  cases first with
  | mk firstSource firstTarget firstStep =>
    cases second with
    | mk secondSource secondTarget secondStep =>
      cases sourceExact
      have targetExact : firstTarget = secondTarget :=
        firstStep.formedByFreeLayer.trans secondStep.formedByFreeLayer.symm
      cases targetExact
      exact congrArg (History.LocatedStep.mk firstSource firstTarget)
        (generatedStep_uniqueForCursorAgreement firstStep secondStep)

private def iterateStructuralDepth
    {P : CircularPresentation}
    (source : PositiveConstitution P) :
    StructuralDepth → PositiveConstitution P
  | .root => source
  | .next depth => canonicalTarget (iterateStructuralDepth source depth)

private def historyStructuralDepth
    {State : Type uA}
    {Step : State → State → Type uB}
    {source target : State} :
    History Step source target → StructuralDepth
  | .root => .root
  | .extend history _ => .next (historyStructuralDepth history)

private def rootProperDepth :
    (depth : StructuralDepth) →
      ProperStructuralDepth .root (.next depth)
  | .root => .direct .root
  | .next depth => .later (rootProperDepth depth)

private def nextProperDepth :
    {first second : StructuralDepth} →
    ProperStructuralDepth first second →
      ProperStructuralDepth (.next first) (.next second)
  | _, _, .direct depth => .direct (.next depth)
  | _, _, .later earlier => .later (nextProperDepth earlier)

private inductive StructuralDepthComparison
    (first second : StructuralDepth) : Type
  | equal : first = second → StructuralDepthComparison first second
  | forward : ProperStructuralDepth first second →
      StructuralDepthComparison first second
  | backward : ProperStructuralDepth second first →
      StructuralDepthComparison first second

private def compareStructuralDepth :
    (first second : StructuralDepth) → StructuralDepthComparison first second
  | .root, .root => .equal rfl
  | .root, .next second => .forward (rootProperDepth second)
  | .next first, .root => .backward (rootProperDepth first)
  | .next first, .next second =>
      match compareStructuralDepth first second with
      | .equal equality => .equal (congrArg StructuralDepth.next equality)
      | .forward proper => .forward (nextProperDepth proper)
      | .backward proper => .backward (nextProperDepth proper)

private def iterateStructuralDepth_future
    {P : CircularPresentation}
    (source : PositiveConstitution P) :
    {first second : StructuralDepth} →
    ProperStructuralDepth first second →
      CursorFuture P
        (iterateStructuralDepth source first).1
        (iterateStructuralDepth source second).1
  | _, _, .direct depth =>
      (generatedStepCursorAdvance
        (generatedStepOfFreeK (iterateStructuralDepth source depth))).toFuture
  | _, _, .later proper =>
      (iterateStructuralDepth_future source proper).trans
        (generatedStepCursorAdvance
          (generatedStepOfFreeK
            (iterateStructuralDepth source _))).toFuture

private theorem iterateStructuralDepth_cursor_injective
    {P : CircularPresentation}
    (source : PositiveConstitution P) :
    Function.Injective
      (fun depth => (iterateStructuralDepth source depth).1) := by
  intro first second cursorExact
  cases compareStructuralDepth first second with
  | equal depthExact => exact depthExact
  | forward proper =>
      have future := iterateStructuralDepth_future source proper
      have loop : CursorFuture P
          (iterateStructuralDepth source first).1
          (iterateStructuralDepth source first).1 :=
        cast
          (congrArg
            (CursorFuture P (iterateStructuralDepth source first).1)
            cursorExact.symm)
          future
      exact False.elim (CursorFuture.irreflexive _ loop)
  | backward proper =>
      have future := iterateStructuralDepth_future source proper
      have loop : CursorFuture P
          (iterateStructuralDepth source second).1
          (iterateStructuralDepth source second).1 :=
        cast
          (congrArg
            (CursorFuture P (iterateStructuralDepth source second).1)
            cursorExact)
          future
      exact False.elim (CursorFuture.irreflexive _ loop)

private theorem generatedHistory_endpoint_eq_iterateStructuralDepth
    {P : CircularPresentation}
    {source target : PositiveConstitution P}
    (history : GeneratedHistory source target) :
    target =
      iterateStructuralDepth source (historyStructuralDepth history) := by
  induction history with
  | root => rfl
  | extend history step inductionHypothesis =>
      exact step.formedByFreeLayer.trans
        (congrArg canonicalTarget inductionHypothesis)

private theorem rootedGeneratedHistory_endpoint_eq_of_cursor_eq
    {P : CircularPresentation}
    (first second : RootedGeneratedHistory P)
    (cursorExact : first.endpoint.1 = second.endpoint.1) :
    first.endpoint = second.endpoint := by
  have firstExact :=
    generatedHistory_endpoint_eq_iterateStructuralDepth first.history
  have secondExact :=
    generatedHistory_endpoint_eq_iterateStructuralDepth second.history
  have firstCursorExact := congrArg Sigma.fst firstExact
  have secondCursorExact := congrArg Sigma.fst secondExact
  have depthExact :
      historyStructuralDepth first.history =
        historyStructuralDepth second.history :=
    iterateStructuralDepth_cursor_injective (initialPositive P)
      (firstCursorExact.symm.trans (cursorExact.trans secondCursorExact))
  exact firstExact.trans
    ((congrArg (iterateStructuralDepth (initialPositive P)) depthExact).trans
      secondExact.symm)

private def occurrenceSourceHistory
    {State : Type uA}
    {Step : State → State → Type uB}
    {source target : State} :
    (history : History Step source target) →
    (occurrence : History.Occurrence history) →
      History Step source occurrence.locatedStep.source
  | .extend previous _step, .last => previous
  | .extend previous _step, .earlier occurrence =>
      occurrenceSourceHistory previous occurrence

theorem rootedOccurrence_source_eq_of_cursor_eq
    {P : CircularPresentation}
    (history : RootedGeneratedHistory P)
    (occurrence : History.Occurrence history.history)
    (position : NonClosingPosition P.perimeter)
    (cursorExact : occurrence.locatedStep.source.1 =
      (perimeterPositionSource P position).1) :
    occurrence.locatedStep.source = perimeterPositionSource P position := by
  let canonicalOccurrence := requirementToOccurrence P position
  let actualPrefix : RootedGeneratedHistory P :=
    { endpoint := occurrence.locatedStep.source
      history := occurrenceSourceHistory history.history occurrence }
  let canonicalPrefix : RootedGeneratedHistory P :=
    { endpoint := canonicalOccurrence.locatedStep.source
      history := occurrenceSourceHistory
        (perimeterDeployment P).history canonicalOccurrence }
  have canonicalLocatedExact : canonicalOccurrence.locatedStep =
      positionLocatedStep P FreeConstitution.root
        BoundaryDifference.initial position :=
    deployPosition_locatedStep P FreeConstitution.root
      BoundaryDifference.initial position
  have canonicalSourceExact : canonicalOccurrence.locatedStep.source =
      perimeterPositionSource P position :=
    congrArg History.LocatedStep.source canonicalLocatedExact
  have canonicalCursorExact : canonicalOccurrence.locatedStep.source.1 =
      (perimeterPositionSource P position).1 :=
    congrArg Sigma.fst canonicalSourceExact
  have prefixCursorExact : actualPrefix.endpoint.1 =
      canonicalPrefix.endpoint.1 :=
    cursorExact.trans canonicalCursorExact.symm
  exact
    (rootedGeneratedHistory_endpoint_eq_of_cursor_eq
      actualPrefix canonicalPrefix prefixCursorExact).trans
      canonicalSourceExact

/- The primitive agreement records only the exact structural address of the
   occurrence.  In a rooted generated history this cursor determines the full
   source state and therefore the canonical target and generated step. -/
structure RequirementOccurrenceAgreement
    (P : CircularPresentation)
    (history : RootedGeneratedHistory P)
    (position : NonClosingPosition P.perimeter)
    (occurrence : History.Occurrence history.history) : Type _ where
  sourceCursorExact :
    occurrence.locatedStep.source.1 =
      (perimeterPositionSource P position).1

namespace RequirementOccurrenceAgreement

def transportOccurrence
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    {position : NonClosingPosition P.perimeter}
    {first second : History.Occurrence history.history}
    (equality : first = second) :
    RequirementOccurrenceAgreement P history position first →
      RequirementOccurrenceAgreement P history position second := by
  cases equality
  exact id

private def locatedStep_stepHEq
    {P : CircularPresentation}
    {first second : History.LocatedStep (@GeneratedStep P)}
    (equality : first = second) : HEq first.step second.step := by
  cases equality
  exact HEq.rfl

private def locatedStep_compatibilityHEq
    {P : CircularPresentation}
    {first second : History.LocatedStep (@GeneratedStep P)}
    (equality : first = second) :
    HEq first.step.compatibility second.step.compatibility := by
  cases equality
  exact HEq.rfl

private def locatedStep_provenanceHEq
    {P : CircularPresentation}
    {first second : History.LocatedStep (@GeneratedStep P)}
    (equality : first = second) :
    HEq first.step.preservesProvenance.exactProvenance
      second.step.preservesProvenance.exactProvenance := by
  cases equality
  exact HEq.rfl

private def compatibleTransportOfReadoutEqualities
    {P : CircularPresentation}
    {implicitSource implicitTarget : ReturnedImplicit P}
    {explicitSource explicitTarget : ReturnedExplicit P}
    (implicitEquality : implicitSource = implicitTarget)
    (explicitEquality : explicitSource = explicitTarget) :
    ExactCompatibleTransport
      (ReturnedCompatible P implicitSource explicitSource)
      (ReturnedCompatible P implicitTarget explicitTarget) := by
  cases implicitEquality
  cases explicitEquality
  exact ExactTypeTransport.reflexive _

def sourceStateExact
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    {position : NonClosingPosition P.perimeter}
    {occurrence : History.Occurrence history.history}
    (agreement : RequirementOccurrenceAgreement P history position occurrence) :
    occurrence.locatedStep.source = perimeterPositionSource P position :=
  rootedOccurrence_source_eq_of_cursor_eq history occurrence position
    agreement.sourceCursorExact

def locatedStepExact
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    {position : NonClosingPosition P.perimeter}
    {occurrence : History.Occurrence history.history}
    (agreement : RequirementOccurrenceAgreement P history position occurrence) :
    occurrence.locatedStep =
      positionLocatedStep P FreeConstitution.root
        BoundaryDifference.initial position :=
  locatedStep_eq_of_source_eq occurrence.locatedStep
    (positionLocatedStep P FreeConstitution.root
      BoundaryDifference.initial position)
    agreement.sourceStateExact

def targetStateExact
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    {position : NonClosingPosition P.perimeter}
    {occurrence : History.Occurrence history.history}
    (agreement : RequirementOccurrenceAgreement P history position occurrence) :
    occurrence.locatedStep.target = perimeterPositionTarget P position :=
  congrArg History.LocatedStep.target agreement.locatedStepExact

def targetCursorExact
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    {position : NonClosingPosition P.perimeter}
    {occurrence : History.Occurrence history.history}
    (agreement : RequirementOccurrenceAgreement P history position occurrence) :
    occurrence.locatedStep.target.1 =
      (perimeterPositionTarget P position).1 :=
  congrArg Sigma.fst agreement.targetStateExact

def explicitReadoutExact
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    {position : NonClosingPosition P.perimeter}
    {occurrence : History.Occurrence history.history}
    (agreement : RequirementOccurrenceAgreement P history position occurrence) :
    explicitRead occurrence.locatedStep.target =
      explicitRead (perimeterPositionTarget P position) :=
  congrArg explicitRead agreement.targetStateExact

def implicitReadoutExact
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    {position : NonClosingPosition P.perimeter}
    {occurrence : History.Occurrence history.history}
    (agreement : RequirementOccurrenceAgreement P history position occurrence) :
    implicitRead occurrence.locatedStep.source =
      implicitRead (perimeterPositionSource P position) :=
  congrArg implicitRead agreement.sourceStateExact

def differenceReadoutExact
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    {position : NonClosingPosition P.perimeter}
    {occurrence : History.Occurrence history.history}
    (agreement : RequirementOccurrenceAgreement P history position occurrence) :
    boundaryDifferenceReadout occurrence.locatedStep.source.2.2 =
      boundaryDifferenceReadout
        (perimeterPositionSource P position).2.2 :=
  congrArg
    (fun state : PositiveConstitution P =>
      boundaryDifferenceReadout state.2.2)
    agreement.sourceStateExact

def stepExact
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    {position : NonClosingPosition P.perimeter}
    {occurrence : History.Occurrence history.history}
    (agreement : RequirementOccurrenceAgreement P history position occurrence) :
    HEq occurrence.locatedStep.step
      (positionLocatedStep P FreeConstitution.root
        BoundaryDifference.initial position).step :=
  locatedStep_stepHEq agreement.locatedStepExact

def compatibilityTransport
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    {position : NonClosingPosition P.perimeter}
    {occurrence : History.Occurrence history.history}
    (agreement : RequirementOccurrenceAgreement P history position occurrence) :
    ExactCompatibleTransport
      (ReturnedCompatible P
        (implicitRead occurrence.locatedStep.source)
        (explicitRead occurrence.locatedStep.target))
      (ReturnedCompatible P
        (implicitRead (perimeterPositionSource P position))
        (explicitRead (perimeterPositionTarget P position))) :=
  compatibleTransportOfReadoutEqualities
    agreement.implicitReadoutExact agreement.explicitReadoutExact

def compatibilityWitnessExact
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    {position : NonClosingPosition P.perimeter}
    {occurrence : History.Occurrence history.history}
    (agreement : RequirementOccurrenceAgreement P history position occurrence) :
    HEq occurrence.locatedStep.step.compatibility
      (stepCompatibleAt (perimeterPositionSource P position).1) :=
  (locatedStep_compatibilityHEq agreement.locatedStepExact).trans
    (GeneratedStep.compatibilityWitnessExact
      (positionLocatedStep P FreeConstitution.root
        BoundaryDifference.initial position).step)

def provenanceTransport
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    {position : NonClosingPosition P.perimeter}
    {occurrence : History.Occurrence history.history}
    (agreement : RequirementOccurrenceAgreement P history position occurrence) :
    ExactProvenanceTransport
      (ReturnedProvenance P
        (boundaryDifferenceReadout occurrence.locatedStep.source.2.2))
      (ReturnedProvenance P
        (boundaryDifferenceReadout
          (perimeterPositionSource P position).2.2)) :=
  ExactTypeTransport.ofEquality
    (congrArg (ReturnedProvenance P) agreement.differenceReadoutExact)

def provenanceWitnessExact
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    {position : NonClosingPosition P.perimeter}
    {occurrence : History.Occurrence history.history}
    (agreement : RequirementOccurrenceAgreement P history position occurrence) :
    HEq
      occurrence.locatedStep.step.preservesProvenance.exactProvenance
      (boundaryProvenanceReadout
        (perimeterPositionSource P position).2.2) :=
  (locatedStep_provenanceHEq agreement.locatedStepExact).trans
    (heq_of_eq (GeneratedStep.provenanceWitnessExact
      (positionLocatedStep P FreeConstitution.root
        BoundaryDifference.initial position).step))

end RequirementOccurrenceAgreement

def canonicalRequirementAgreement
    (P : CircularPresentation)
    (position : NonClosingPosition P.perimeter) :
    RequirementOccurrenceAgreement P (perimeterDeployment P) position
      (requirementToOccurrence P position) :=
  ⟨congrArg
    (fun located : History.LocatedStep (@GeneratedStep P) => located.source.1)
    (deployPosition_locatedStep P
      FreeConstitution.root BoundaryDifference.initial position)⟩

/- `Exact` refers to the exact realization of each non-closing requirement.
   Exact source-cursor agreement reconstructs the canonical located step and
   already forces the realization map to be
   injective; it does not assert that these occurrences exhaust the history. -/
structure ExactNonClosingRealization
    (P : CircularPresentation)
    (history : RootedGeneratedHistory P) where
  realize :
    NonClosingPosition P.perimeter → History.Occurrence history.history
  agreement :
    (position : NonClosingPosition P.perimeter) →
      RequirementOccurrenceAgreement P history position (realize position)

namespace ExactNonClosingRealization

/- Distinct perimeter requirements cannot be absorbed by one occurrence when
   exact source-cursor agreement is available.  Equality of their realized
   occurrences would identify their canonical located steps; the strict cursor
   order between distinct canonical occurrences then yields an impossible
   cursor loop.  Injectivity is therefore a theorem, not an independent field
   of `ExactNonClosingRealization`. -/
theorem realize_injective
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (realization : ExactNonClosingRealization P history) :
    Function.Injective realization.realize := by
  intro first second equality
  have canonicalFirst :=
    (canonicalRequirementAgreement P first).locatedStepExact
  have canonicalSecond :=
    (canonicalRequirementAgreement P second).locatedStepExact
  have realizedFirst := (realization.agreement first).locatedStepExact
  have realizedSecond := (realization.agreement second).locatedStepExact
  have realizedAgree :
      (realization.realize first).locatedStep =
        (realization.realize second).locatedStep :=
    congrArg (fun occurrence => occurrence.locatedStep) equality
  have stepsAgree :
      (requirementToOccurrence P first).locatedStep =
        (requirementToOccurrence P second).locatedStep :=
    canonicalFirst.trans
      ((realizedFirst.symm.trans (realizedAgree.trans realizedSecond)).trans
        canonicalSecond.symm)
  rcases History.OccurrencePrecedes.trichotomy
      (requirementToOccurrence P first)
      (requirementToOccurrence P second) with
    occurrenceEquality | forward | backward
  · exact requirementToOccurrence_injective P occurrenceEquality
  · rcases forward.sourceCursorFuture with ⟨future⟩
    exact False.elim
      (CursorFuture.irreflexive _
        (congrArg
          (fun step : History.LocatedStep (@GeneratedStep P) => step.source.1)
          stepsAgree ▸ future))
  · rcases backward.sourceCursorFuture with ⟨future⟩
    exact False.elim
      (CursorFuture.irreflexive _
        (congrArg
          (fun step : History.LocatedStep (@GeneratedStep P) => step.source.1)
          stepsAgree ▸ future))

/- A locally exact realization inside a genuine generated history must preserve
   the structural precedence of the perimeter.  The proof excludes reversed
   chronology by composing the two strict cursor futures into an impossible
   cursor loop. -/
theorem preservesPrecedence
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (realization : ExactNonClosingRealization P history)
    {first second : NonClosingPosition P.perimeter}
    (precedes : NonClosingPrecedes P.perimeter first second) :
    History.OccurrencePrecedes
      (realization.realize first) (realization.realize second) := by
  rcases History.OccurrencePrecedes.trichotomy
      (realization.realize first) (realization.realize second) with
    equality | forward | backward
  · have positionEquality : first = second :=
      realization.realize_injective equality
    exact False.elim (precedes.ne positionEquality)
  · exact forward
  · rcases precedes.sourceCursorFuture with ⟨canonicalForward⟩
    rcases backward.sourceCursorFuture with ⟨realizedBackward⟩
    have firstCursorExact := (realization.agreement first).sourceCursorExact
    have secondCursorExact := (realization.agreement second).sourceCursorExact
    have forwardRealized : CursorFuture P
        (realization.realize first).locatedStep.source.1
        (realization.realize second).locatedStep.source.1 :=
      firstCursorExact.symm ▸ secondCursorExact.symm ▸ canonicalForward
    exact False.elim
      (CursorFuture.irreflexive _
        (forwardRealized.trans realizedBackward))

/- Canonically adjacent requirements are realized by immediately adjacent
   occurrences in a genuine generated history.  Any positive gap would become
   a strict cursor future from a cursor to itself after transporting the exact
   endpoint data. -/
theorem preservesNext
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (realization : ExactNonClosingRealization P history)
    {first second : NonClosingPosition P.perimeter}
    (next : NonClosingNext P.perimeter first second) :
    History.OccurrenceNext
      (realization.realize first) (realization.realize second) := by
  have occurrencePrecedes : History.OccurrencePrecedes
      (realization.realize first) (realization.realize second) :=
    realization.preservesPrecedence next.toPrecedes
  rcases occurrencePrecedes.next_or_positiveGap with immediate | gap
  · exact immediate
  · rcases gap with ⟨future⟩
    have canonicalEndpointEquality :=
      NonClosingNext.target_eq_source next
        FreeConstitution.root BoundaryDifference.initial
    have endpointEquality :
        (realization.realize first).locatedStep.target =
          (realization.realize second).locatedStep.source :=
      (realization.agreement first).targetStateExact.trans
        (canonicalEndpointEquality.trans
          (realization.agreement second).sourceStateExact.symm)
    have cursorEquality := congrArg Sigma.fst endpointEquality
    have futureLoop : CursorFuture P
        (realization.realize second).locatedStep.source.1
        (realization.realize second).locatedStep.source.1 :=
      cursorEquality ▸ future
    exact False.elim (CursorFuture.irreflexive _ futureLoop)

/- The canonical perimeter occurrences can be read inside any exact local
   realization without introducing a second realization structure. -/
def embedPerimeterOccurrence
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (realization : ExactNonClosingRealization P history) :
    History.Occurrence (perimeterHistory P) →
      History.Occurrence history.history :=
  fun occurrence =>
    realization.realize (occurrenceToRequirement P occurrence)

theorem embedPerimeterOccurrence_locatedStep
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (realization : ExactNonClosingRealization P history)
    (occurrence : History.Occurrence (perimeterHistory P)) :
    (realization.embedPerimeterOccurrence occurrence).locatedStep =
      occurrence.locatedStep := by
  calc
    (realization.embedPerimeterOccurrence occurrence).locatedStep
        = positionLocatedStep P FreeConstitution.root
            BoundaryDifference.initial (occurrenceToRequirement P occurrence) :=
      (realization.agreement (occurrenceToRequirement P occurrence)).locatedStepExact
    _ = (requirementToOccurrence P
          (occurrenceToRequirement P occurrence)).locatedStep :=
      (canonicalRequirementAgreement P
        (occurrenceToRequirement P occurrence)).locatedStepExact.symm
    _ = occurrence.locatedStep := by
      rw [occurrenceToRequirement_toOccurrence]

theorem embedPerimeterOccurrence_injective
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (realization : ExactNonClosingRealization P history) :
    Function.Injective realization.embedPerimeterOccurrence := by
  intro first second equality
  have positionEquality :
      occurrenceToRequirement P first = occurrenceToRequirement P second :=
    realization.realize_injective equality
  calc
    first = requirementToOccurrence P (occurrenceToRequirement P first) :=
      (occurrenceToRequirement_toOccurrence P first).symm
    _ = requirementToOccurrence P (occurrenceToRequirement P second) :=
      congrArg (requirementToOccurrence P) positionEquality
    _ = second := occurrenceToRequirement_toOccurrence P second

end ExactNonClosingRealization

def positiveStepThenHistory
    {State : Type uA}
    {Step : State → State → Type uB}
    {source middle target : State}
    (first : Step source middle)
    (rest : History Step middle target) :
    Σ positive : History.Positive Step source target,
      PLift (positive.toHistory =
        History.append (.extend .root first) rest) := by
  cases rest with
  | root => exact ⟨⟨source, .root, first⟩, ⟨rfl⟩⟩
  | extend priorHistory last =>
      exact ⟨⟨_, History.append (.extend .root first) priorHistory, last⟩,
        ⟨rfl⟩⟩

def deployRemaining_positive
    (P : CircularPresentation)
    {node : LocalNode
      P.Explicit P.Implicit P.Compatible P.Difference P.Provenance}
    {remaining : PerimeterSpine P.Compatible node}
    (data : FreeConstitution P (.within remaining))
    (difference : BoundaryDifference P data)
    (_ : NonClosingPosition remaining) :
    Σ positive : History.Positive (@GeneratedStep P)
      (positiveAtRemaining P remaining data difference)
      (deployRemaining P remaining data difference).1,
      PLift (positive.toHistory =
        (deployRemaining P remaining data difference).2) := by
  cases remaining with
  | boundary node => contradiction
  | @advance node nextNode compatible tail =>
      exact positiveStepThenHistory
        (generatedStepOfFreeK
          (positiveAtRemaining P (.advance compatible tail) data difference))
        (deployRemaining P tail
          (canonicalTarget
            (positiveAtRemaining P (.advance compatible tail) data difference)).2.1
          (canonicalTarget
            (positiveAtRemaining P (.advance compatible tail) data difference)).2.2).2

def perimeterDeployment_positive
    (P : CircularPresentation) :
    Σ positive : History.Positive (@GeneratedStep P)
      (initialPositive P) (perimeterEndpoint P),
      PLift (positive.toHistory = perimeterHistory P) :=
  deployRemaining_positive P FreeConstitution.root
    BoundaryDifference.initial P.perimeterPositive

namespace History.Vertex

def boundaryReadout
    {State : Type uA}
    {Step : State → State → Type uB}
    {source target : State}
    {history : History Step source target}
    {Endpoint : Type uEnd}
    (left right : Endpoint) : Vertex history → Endpoint
  | .root => left
  | .earlier vertex => boundaryReadout left right vertex
  | .final => right

theorem initial_reads_left
    {State : Type uA}
    {Step : State → State → Type uB}
    {source target : State}
    (history : History Step source target)
    {Endpoint : Type uEnd}
    (left right : Endpoint) :
    boundaryReadout left right (History.initialVertex history) = left := by
  induction history with
  | root => rfl
  | extend history step ih => exact ih

theorem positive_final_reads_right
    {State : Type uA}
    {Step : State → State → Type uB}
    {source target : State}
    (positive : History.Positive Step source target)
    {Endpoint : Type uEnd}
    (left right : Endpoint) :
    boundaryReadout left right
      (History.finalVertex positive.toHistory) = right := rfl

theorem positive_initial_ne_final
    {State : Type uA}
    {Step : State → State → Type uB}
    {source target : State}
    (positive : History.Positive Step source target) :
    History.initialVertex positive.toHistory ≠
      History.finalVertex positive.toHistory := by
  intro equality
  cases equality

theorem positive_final_reads_right_after_history_equality
    {State : Type uA}
    {Step : State → State → Type uB}
    {source target : State}
    (positive : History.Positive Step source target)
    (history : History Step source target)
    (historyEquality : positive.toHistory = history)
    {Endpoint : Type uEnd}
    (left right : Endpoint) :
    boundaryReadout left right (History.finalVertex history) = right := by
  cases historyEquality
  exact positive_final_reads_right positive left right

theorem positive_initial_ne_final_after_history_equality
    {State : Type uA}
    {Step : State → State → Type uB}
    {source target : State}
    (positive : History.Positive Step source target)
    (history : History Step source target)
    (historyEquality : positive.toHistory = history) :
    History.initialVertex history ≠ History.finalVertex history := by
  cases historyEquality
  exact positive_initial_ne_final positive

end History.Vertex

structure ExactPerimeterRealization
    (P : CircularPresentation)
    (history : RootedGeneratedHistory P) where
  requirementToOccurrence :
    NonClosingPosition P.perimeter → History.Occurrence history.history
  occurrenceToRequirement :
    History.Occurrence history.history → NonClosingPosition P.perimeter
  occurrenceRoundTrip :
    (occurrence : History.Occurrence history.history) →
      requirementToOccurrence (occurrenceToRequirement occurrence) = occurrence
  requirementRoundTrip :
    (position : NonClosingPosition P.perimeter) →
      occurrenceToRequirement (requirementToOccurrence position) = position
  localAgreement :
    (position : NonClosingPosition P.perimeter) →
      RequirementOccurrenceAgreement P history position
        (requirementToOccurrence position)
  leftBoundary : History.Vertex history.history
  rightBoundary : History.Vertex history.history
  boundaryReadout : History.Vertex history.history → P.Endpoint
  readsLeftBoundary : boundaryReadout leftBoundary = P.leftEndpoint
  readsRightBoundary : boundaryReadout rightBoundary = P.rightEndpoint
  boundariesSeparated : leftBoundary ≠ rightBoundary
  identificationCloses : leftBoundary = rightBoundary → P.TotalLoop

def perimeterRealization (P : CircularPresentation) :
    ExactPerimeterRealization P (perimeterDeployment P) := by
  let positive := (perimeterDeployment_positive P).1
  have historyEquality := (perimeterDeployment_positive P).2.down
  exact
    { requirementToOccurrence := requirementToOccurrence P
      occurrenceToRequirement := occurrenceToRequirement P
      occurrenceRoundTrip := occurrenceToRequirement_toOccurrence P
      requirementRoundTrip := requirementToOccurrence_toRequirement P
      localAgreement := canonicalRequirementAgreement P
      leftBoundary := History.initialVertex (perimeterHistory P)
      rightBoundary := History.finalVertex (perimeterHistory P)
      boundaryReadout :=
        History.Vertex.boundaryReadout P.leftEndpoint P.rightEndpoint
      readsLeftBoundary :=
        History.Vertex.initial_reads_left (perimeterHistory P)
          P.leftEndpoint P.rightEndpoint
      readsRightBoundary :=
        History.Vertex.positive_final_reads_right_after_history_equality
          positive (perimeterHistory P) historyEquality
          P.leftEndpoint P.rightEndpoint
      boundariesSeparated :=
        History.Vertex.positive_initial_ne_final_after_history_equality
          positive (perimeterHistory P) historyEquality
      identificationCloses := fun equality =>
        P.closeFromIdentification
          ((History.Vertex.initial_reads_left (perimeterHistory P)
              P.leftEndpoint P.rightEndpoint).symm.trans
            ((congrArg
              (History.Vertex.boundaryReadout
                P.leftEndpoint P.rightEndpoint) equality).trans
              (History.Vertex.positive_final_reads_right_after_history_equality
                positive (perimeterHistory P) historyEquality
                P.leftEndpoint P.rightEndpoint))) }

/- The exact non-closing part of the perimeter is an instance of the generic
   internal-role realization.  No circular junction or totalization enters
   this adapter. -/
def perimeterInternalRoleRealization
    (P : CircularPresentation) :
    SegmentedResidualRole.ExactInternalRealization
      (NonClosingPosition P.perimeter)
      (History.Occurrence (perimeterHistory P)) :=
  { roleToOccurrence := requirementToOccurrence P
    occurrenceToRole := occurrenceToRequirement P
    occurrenceRoundTrip := occurrenceToRequirement_toOccurrence P
    roleRoundTrip := requirementToOccurrence_toRequirement P }

/-! ## Faithful refinements and the final junction -/

def transportOccurrence
    {State : Type uA}
    {Step : State → State → Type uB}
    {source target : State}
    {first second : History Step source target}
    (equality : first = second) :
    History.Occurrence first → History.Occurrence second := by
  cases equality
  exact id

theorem transportOccurrence_injective
    {State : Type uA}
    {Step : State → State → Type uB}
    {source target : State}
    {first second : History Step source target}
    (equality : first = second) :
    Function.Injective (transportOccurrence equality) := by
  cases equality
  intro left right same
  exact same

theorem locatedStep_transportOccurrence
    {State : Type uA}
    {Step : State → State → Type uB}
    {source target : State}
    {first second : History Step source target}
    (equality : first = second)
    (occurrence : History.Occurrence first) :
    (transportOccurrence equality occurrence).locatedStep =
      occurrence.locatedStep := by
  cases equality
  rfl

namespace History

/- An occurrence whose located step is exactly a generated step from the
   source of the history determines an initial one-step factorization.  The
   proof recurses on occurrence data.  A nonempty prefix before that occurrence
   would be a positive generated history returning to the same source. -/
def factorInitialGeneratedStep
    {P : CircularPresentation}
    {source middle target : PositiveConstitution P}
    (history : GeneratedHistory source target)
    (step : GeneratedStep source middle)
    (occurrence : History.Occurrence history)
    (locatedStepExact :
      occurrence.locatedStep =
        (⟨source, middle, step⟩ : History.LocatedStep (@GeneratedStep P))) :
    Σ continuation : GeneratedHistory middle target,
      { recompose : History.append (.extend .root step) continuation = history //
        transportOccurrence recompose
          (History.embedLeftOccurrence
            (.last : History.Occurrence (.extend .root step))
            continuation) = occurrence } :=
  match occurrence with
  | @Occurrence.last _ _ _ _ _ prior lastStep => by
      cases locatedStepExact
      cases prior with
      | root =>
          exact ⟨.root, ⟨rfl, rfl⟩⟩
      | extend priorHistory previousStep =>
          let positive : History.Positive (@GeneratedStep P) source source :=
            ⟨_, priorHistory, previousStep⟩
          exact False.elim
            (positiveGeneratedHistory_source_ne_target positive rfl)
  | @Occurrence.earlier _ _ _ _ _ prior lastStep earlier => by
      rcases factorInitialGeneratedStep prior step earlier locatedStepExact with
        ⟨continuation, ⟨recompose, occurrenceExact⟩⟩
      cases recompose
      exact ⟨.extend continuation lastStep, ⟨rfl,
        congrArg
          (fun occurrence =>
            History.Occurrence.earlier (step := lastStep) occurrence)
          occurrenceExact⟩⟩

/- Once the initial step has been factored, any distinct occurrence belongs to
   the right-hand continuation.  Classification is performed on occurrence
   data, while the inequality is used only to eliminate the impossible old
   branch. -/
def extractRightOccurrenceAfterSingle
    {State : Type uA}
    {Step : State → State → Type uB}
    {source middle target : State}
    (firstStep : Step source middle)
    (continuation : History Step middle target)
    {history : History Step source target}
    (recompose :
      History.append (.extend .root firstStep) continuation = history)
    (occurrence : History.Occurrence history)
    (notFirst :
      transportOccurrence recompose
        (History.embedLeftOccurrence
          (.last : History.Occurrence (.extend .root firstStep)) continuation) ≠
        occurrence) :
    Σ newOccurrence : History.Occurrence continuation,
      PLift (transportOccurrence recompose
        (History.embedRightOccurrence
          (.extend .root firstStep) newOccurrence) = occurrence) := by
  cases recompose
  cases History.classifyAppendOccurrence
      (.extend .root firstStep) continuation occurrence with
  | inl oldData =>
      rcases oldData with ⟨oldOccurrence, reconstruction⟩
      cases oldOccurrence with
      | last => exact False.elim (notFirst reconstruction.down)
      | earlier impossible => exact nomatch impossible
  | inr newData =>
      rcases newData with ⟨newOccurrence, reconstruction⟩
      exact ⟨newOccurrence, ⟨reconstruction.down⟩⟩

end History

/- Recursive structural factorization of a canonical perimeter deployment from
   exact, injective occurrences inside a genuine generated history.  No
   numerical rank or length is used. -/
def factorDeployRemainingFromExactOccurrences
    (P : CircularPresentation)
    {node : LocalNode
      P.Explicit P.Implicit P.Compatible P.Difference P.Provenance} :
    (remaining : PerimeterSpine P.Compatible node) →
    (data : FreeConstitution P (.within remaining)) →
    (difference : BoundaryDifference P data) →
    (target : PositiveConstitution P) →
    (history : GeneratedHistory
      (positiveAtRemaining P remaining data difference) target) →
    (realize : NonClosingPosition remaining → History.Occurrence history) →
    Function.Injective realize →
    ((position : NonClosingPosition remaining) →
      (realize position).locatedStep =
        positionLocatedStep P data difference position) →
    Σ continuation : GeneratedHistory
        (deployRemaining P remaining data difference).1 target,
      PLift (History.append
        (deployRemaining P remaining data difference).2 continuation = history
      )
  | .boundary node, data, difference, target, history,
      _realize, _realizeInjective, _locatedStepExact =>
      ⟨history, ⟨History.root_append history⟩⟩
  | .advance compatible tail, data, difference, target, history,
      realize, realizeInjective, locatedStepExact => by
      let source :=
        positiveAtRemaining P (.advance compatible tail) data difference
      let next := canonicalTarget source
      have firstLocatedStepExact :
          (realize (.here : NonClosingPosition (.advance compatible tail))).locatedStep =
            (⟨source, next, generatedStepOfFreeK source⟩ :
              History.LocatedStep (@GeneratedStep P)) := by
        have exactAtFirst := locatedStepExact
          (.here : NonClosingPosition (.advance compatible tail))
        dsimp [positionLocatedStep, positionSourceState,
          positionSourceStateAux, positionTargetState, source, next] at exactAtFirst
        exact exactAtFirst
      rcases History.factorInitialGeneratedStep history
          (generatedStepOfFreeK source) (realize .here) firstLocatedStepExact with
        ⟨afterFirst, ⟨firstRecompose, firstOccurrenceExact⟩⟩
      have laterNotFirst (position : NonClosingPosition tail) :
          transportOccurrence firstRecompose
            (History.embedLeftOccurrence
              (.last : History.Occurrence
                (.extend .root (generatedStepOfFreeK source))) afterFirst) ≠
              realize (.later position) := by
        intro equality
        have realizedEquality : realize .here = realize (.later position) :=
          firstOccurrenceExact.symm.trans equality
        have positionEquality := realizeInjective realizedEquality
        cases positionEquality
      let tailOccurrenceData := fun position : NonClosingPosition tail =>
        History.extractRightOccurrenceAfterSingle
          (generatedStepOfFreeK source) afterFirst firstRecompose
          (realize (.later position)) (laterNotFirst position)
      let tailRealize :
          NonClosingPosition tail → History.Occurrence afterFirst :=
        fun position => (tailOccurrenceData position).1
      have tailRealizeInjective : Function.Injective tailRealize := by
        intro first second equality
        have embeddedEquality :
            transportOccurrence firstRecompose
              (History.embedRightOccurrence
                (.extend .root (generatedStepOfFreeK source))
                (tailRealize first)) =
            transportOccurrence firstRecompose
              (History.embedRightOccurrence
                (.extend .root (generatedStepOfFreeK source))
                (tailRealize second)) :=
          congrArg
            (fun occurrence =>
              transportOccurrence firstRecompose
                (History.embedRightOccurrence
                  (.extend .root (generatedStepOfFreeK source)) occurrence))
            equality
        have realizedEquality :
            realize (.later first) = realize (.later second) :=
            (tailOccurrenceData first).2.down.symm.trans
            (embeddedEquality.trans (tailOccurrenceData second).2.down)
        exact NonClosingPosition.later.inj
          (realizeInjective realizedEquality)
      have tailLocatedStepExact
          (position : NonClosingPosition tail) :
          (tailRealize position).locatedStep =
            positionLocatedStep P next.2.1 next.2.2 position := by
        have reconstructed := (tailOccurrenceData position).2.down
        calc
          (tailRealize position).locatedStep
              = (History.embedRightOccurrence
                  (.extend .root (generatedStepOfFreeK source))
                  (tailRealize position)).locatedStep :=
                (History.locatedStep_embedRight
                  (.extend .root (generatedStepOfFreeK source))
                  (tailRealize position)).symm
          _ = (transportOccurrence firstRecompose
                (History.embedRightOccurrence
                  (.extend .root (generatedStepOfFreeK source))
                  (tailRealize position))).locatedStep :=
                (locatedStep_transportOccurrence firstRecompose
                  (History.embedRightOccurrence
                    (.extend .root (generatedStepOfFreeK source))
                    (tailRealize position))).symm
          _ = (realize (.later position)).locatedStep :=
                congrArg
                  (fun occurrence : History.Occurrence history =>
                    occurrence.locatedStep) reconstructed
          _ = positionLocatedStep P data difference (.later position) :=
                locatedStepExact (.later position)
          _ = positionLocatedStep P next.2.1 next.2.2 position := by
                rfl
      rcases factorDeployRemainingFromExactOccurrences P tail
          next.2.1 next.2.2 target afterFirst tailRealize
          tailRealizeInjective tailLocatedStepExact with
        ⟨continuation, tailRecompose⟩
      refine ⟨continuation, ⟨?_⟩⟩
      change History.append
          (History.append
            (.extend .root (generatedStepOfFreeK source))
            (deployRemaining P tail next.2.1 next.2.2).2)
          continuation = history
      calc
        History.append
            (History.append
              (.extend .root (generatedStepOfFreeK source))
              (deployRemaining P tail next.2.1 next.2.2).2)
            continuation
            = History.append
                (.extend .root (generatedStepOfFreeK source))
                (History.append
                  (deployRemaining P tail next.2.1 next.2.2).2
                  continuation) :=
              History.append_associative _ _ _
        _ = History.append
              (.extend .root (generatedStepOfFreeK source)) afterFirst :=
            congrArg
              (History.append
                (.extend .root (generatedStepOfFreeK source)))
              tailRecompose.down
        _ = history := firstRecompose

structure PerimeterExtension
    (P : CircularPresentation)
    (history : RootedGeneratedHistory P) where
  continuation :
    GeneratedHistory (perimeterEndpoint P) history.endpoint
  recompose :
    History.append (perimeterHistory P) continuation = history.history

namespace ExactNonClosingRealization

/- Exact local realization inside a genuine rooted generated history is already
   enough to reconstruct the canonical perimeter as an initial extension. -/
def toPerimeterExtension
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (realization : ExactNonClosingRealization P history) :
    PerimeterExtension P history := by
  let factor :=
    factorDeployRemainingFromExactOccurrences P P.perimeter
      FreeConstitution.root BoundaryDifference.initial history.endpoint
      history.history realization.realize realization.realize_injective
      (fun position => (realization.agreement position).locatedStepExact)
  exact
      { continuation := factor.1
        recompose := factor.2.down }

end ExactNonClosingRealization

namespace PerimeterExtension

def oldOccurrence
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (extension : PerimeterExtension P history)
    (position : NonClosingPosition P.perimeter) :
    History.Occurrence history.history :=
  transportOccurrence extension.recompose
    (History.embedLeftOccurrence
      (requirementToOccurrence P position) extension.continuation)

def newOccurrence
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (extension : PerimeterExtension P history)
    (occurrence : History.Occurrence extension.continuation) :
    History.Occurrence history.history :=
  transportOccurrence extension.recompose
    (History.embedRightOccurrence (perimeterHistory P) occurrence)

def oldOccurrenceAgreement
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (extension : PerimeterExtension P history)
    (position : NonClosingPosition P.perimeter) :
    RequirementOccurrenceAgreement P history position
      (extension.oldOccurrence position) := by
  refine ⟨?_⟩
  exact congrArg
    (fun located : History.LocatedStep (@GeneratedStep P) => located.source.1)
    ((locatedStep_transportOccurrence extension.recompose
        (History.embedLeftOccurrence
          (requirementToOccurrence P position) extension.continuation)).trans
      ((History.locatedStep_embedLeft
        (requirementToOccurrence P position) extension.continuation).trans
          (canonicalRequirementAgreement P position).locatedStepExact))

theorem oldOccurrence_injective
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (extension : PerimeterExtension P history) :
    Function.Injective extension.oldOccurrence := by
  intro first second equality
  have embeddedEquality :=
    transportOccurrence_injective extension.recompose equality
  have canonicalEquality :=
    History.embedLeftOccurrence_injective extension.continuation embeddedEquality
  exact requirementToOccurrence_injective P canonicalEquality

def toExactNonClosingRealization
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (extension : PerimeterExtension P history) :
    ExactNonClosingRealization P history :=
  { realize := extension.oldOccurrence
    agreement := extension.oldOccurrenceAgreement }

theorem old_new_occurrences_disjoint
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (extension : PerimeterExtension P history)
    (position : NonClosingPosition P.perimeter)
    (occurrence : History.Occurrence extension.continuation) :
    extension.oldOccurrence position ≠ extension.newOccurrence occurrence := by
  intro equality
  have beforeTransport :=
    transportOccurrence_injective extension.recompose equality
  exact History.leftRightDisjoint
    (requirementToOccurrence P position) occurrence beforeTransport

end PerimeterExtension

def identityPerimeterExtension (P : CircularPresentation) :
    PerimeterExtension P (perimeterDeployment P) :=
  { continuation := .root
    recompose := rfl }

def oneStepAfterPerimeter_is_extension (P : CircularPresentation) :
    PerimeterExtension P (oneStepAfterPerimeter P) :=
  { continuation := .extend .root (generate_after_perimeter P).2
    recompose := rfl }

/-! ## Direct circular residual-determination core

This is the core consumed by the canonical one-step construction.  Its label
is defined directly on the exactly-one continuation occurrence; no rich
perimeter realization or residual-labelling adapter is involved. -/
def oneStepResidualDeterminationCore
    (P : CircularPresentation) :
    SegmentedResidualRole.ResidualDeterminationCore
      (NonClosingPosition P.perimeter)
      (FinalRequirement P)
      (History.Occurrence
        (oneStepAfterPerimeter_is_extension P).continuation)
      (finalRequirementContractible P) := by
  let exactlyOne :
      History.ExactlyOne
        (oneStepAfterPerimeter_is_extension P).continuation := by
    change History.ExactlyOne
      (.extend .root (generate_after_perimeter P).2)
    exact .single (generate_after_perimeter P).2
  refine
    { newLabel := fun _ => .inr .distinguished
      newLabelInjective := ?_
      noInternalReuse := ?_ }
  · intro first second _
    exact (exactlyOne.occurrence_unique first).trans
      (exactlyOne.occurrence_unique second).symm
  · intro occurrence role equality
    cases equality

def oneStepCorePositive
    (P : CircularPresentation) :
    SegmentedResidualRole.PositiveNewPart
      (History.Occurrence
        (oneStepAfterPerimeter_is_extension P).continuation) :=
  { occurrence := .last }

def oneStepCoreResidualOccurrence
    (P : CircularPresentation) :
    SegmentedResidualRole.CoreUniqueResidualOccurrence
      (oneStepResidualDeterminationCore P) :=
  SegmentedResidualRole.positiveCore_hasUniqueResidualOccurrence
    (oneStepResidualDeterminationCore P)
    (oneStepCorePositive P)

def oneStepCoreSegmentedBoundary
    (P : CircularPresentation) :
    AbstractSegmentedTurning.CoreSegmentedBoundary
      (perimetralBoundaryGenerator P)
      (NonClosingPosition P.perimeter)
      (FinalRequirement P)
      (History.Occurrence
        (oneStepAfterPerimeter_is_extension P).continuation)
      (finalRequirementContractible P) :=
  { core := oneStepResidualDeterminationCore P
    positive := oneStepCorePositive P }

def oneStepAfterPerimeter_nonClosingRealization
    (P : CircularPresentation) :
    ExactNonClosingRealization P (oneStepAfterPerimeter P) :=
  (oneStepAfterPerimeter_is_extension P).toExactNonClosingRealization

/-! ## Independent circular specification -/

/- `CircularClosureMeaning` states the trajectory-level closure obligation
   independently of `CircularRefinement`: every strict constitutive extension
   of the canonical perimeter deployment must determine a total loop. -/
abbrev CircularClosureMeaning
    (P : CircularPresentation)
    (history : RootedGeneratedHistory P) : Type _ :=
  StrictConstitutivePrefix (perimeterDeployment P) history → P.TotalLoop

/- The canonical deployment satisfies the closure meaning because there is no
   strict constitutive prefix from it to itself. -/
def perimeterDeployment_closureMeaning
    (P : CircularPresentation) :
    CircularClosureMeaning P (perimeterDeployment P) :=
  fun strict =>
    False.elim (strictPrefix_ne strict rfl)

/- The freely generated one-step continuation fails the independent closure
   meaning directly: its canonical strict continuation would force a total
   loop, which the presentation rejects. -/
theorem oneStepAfterPerimeter_notClosureMeaning
    (P : CircularPresentation) :
    CircularClosureMeaning P (oneStepAfterPerimeter P) → False :=
  fun meaning =>
    P.rejectTotalLoop (meaning (oneStepAfterPerimeterStrict P))

/- Satisfaction of the independent circular specification has exactly two
   primitive components: minimal local exactness and trajectory closure. -/
structure CircularSpecificationSatisfaction
    (P : CircularPresentation)
    (history : RootedGeneratedHistory P) where
  «local» : ExactNonClosingRealization P history
  trajectory : CircularClosureMeaning P history

/- Positive canonical model of the independent specification. -/
def perimeterDeployment_specificationSatisfaction
    (P : CircularPresentation) :
    CircularSpecificationSatisfaction P (perimeterDeployment P) :=
  { «local» := (identityPerimeterExtension P).toExactNonClosingRealization
    trajectory := perimeterDeployment_closureMeaning P }

/- Negative canonical model: local exactness remains available, but the
   trajectory component of the same independent specification is impossible. -/
theorem oneStepAfterPerimeter_notSpecificationSatisfaction
    (P : CircularPresentation) :
    CircularSpecificationSatisfaction P (oneStepAfterPerimeter P) → False :=
  fun satisfaction =>
    oneStepAfterPerimeter_notClosureMeaning P satisfaction.trajectory

/- Carrier completeness of the independent specification: any satisfying rooted
   generated history is necessarily the canonical perimeter deployment.  The
   local component reconstructs a perimeter extension.  A positive suffix is
   excluded directly by the independent trajectory meaning and the total-loop
   obstruction. -/
theorem CircularSpecificationSatisfaction.eq_perimeter
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (satisfaction : CircularSpecificationSatisfaction P history) :
    history = perimeterDeployment P := by
  let extension : PerimeterExtension P history :=
    satisfaction.«local».toPerimeterExtension
  cases History.appendRootOrPositive
      (perimeterHistory P) extension.continuation with
  | inl rootData =>
      rcases rootData with ⟨endpointEquality, continuationEquality⟩
      exact rootedGeneratedHistory_ext endpointEquality.down
        ((heq_of_eq extension.recompose.symm).trans
          continuationEquality.down)
  | inr positiveData =>
      rcases positiveData with ⟨positive, continuationEquality⟩
      let strict :
          StrictConstitutivePrefix (perimeterDeployment P) history :=
        { continuation := positive
          historyExact := by
            exact
              (congrArg
                (History.append (perimeterHistory P))
                continuationEquality.down.symm).trans extension.recompose }
      exact False.elim
        (P.rejectTotalLoop (satisfaction.trajectory strict))

/-! ## Experimental semantic traces -/

/- `SemanticTrace` deliberately forgets global composability while retaining
   the complete located data of every generated step.  Occurrences are list
   positions, so equal located steps may still occur at distinct indices. -/
structure SemanticTrace
    (P : CircularPresentation) where
  steps : List (History.LocatedStep (@GeneratedStep P))

namespace SemanticTrace

abbrev Occurrence
    {P : CircularPresentation}
    (trace : SemanticTrace P) : Type :=
  Fin trace.steps.length

def locatedStep
    {P : CircularPresentation}
    (trace : SemanticTrace P)
    (occurrence : trace.Occurrence) :
    History.LocatedStep (@GeneratedStep P) :=
  trace.steps.get occurrence

end SemanticTrace

/- Experimental counterpart of `RequirementOccurrenceAgreement`.  It keeps
   only the exact local semantic content and does not assume a generated
   history, a circular labelling, or any regime structure. -/
structure LocatedRequirementAgreement
    (P : CircularPresentation)
    (position : NonClosingPosition P.perimeter)
    (located : History.LocatedStep (@GeneratedStep P)) where
  locatedStepExact :
    located =
      positionLocatedStep P FreeConstitution.root
        BoundaryDifference.initial position

/- Experimental exact local coverage.  Injectivity preserves occurrence
   individuation, while no global composability or ordering constraint is
   imposed beyond the explicit list positions of the semantic trace. -/
structure SemanticExactNonClosingRealization
    (P : CircularPresentation)
    (trace : SemanticTrace P) where
  realize :
    NonClosingPosition P.perimeter → trace.Occurrence
  realize_injective :
    Function.Injective realize
  agreement :
    (position : NonClosingPosition P.perimeter) →
      LocatedRequirementAgreement P position
        (trace.locatedStep (realize position))

/- Order preservation adds exactly one constraint to the experimental local
   realization: structural precedence in the perimeter must be reflected by
   the order of occurrence indices in the semantic trace. -/
def SemanticOrderPreserved
    {P : CircularPresentation}
    {trace : SemanticTrace P}
    (realization : SemanticExactNonClosingRealization P trace) :
    Prop :=
  ∀ first second,
    NonClosingPrecedes P.perimeter first second →
      realization.realize first < realization.realize second


namespace SemanticTrace

/- Occurrences strictly between two trace positions.  The subtype preserves
   occurrence individuation independently of the located-step reading. -/
abbrev Between
    {P : CircularPresentation}
    (trace : SemanticTrace P)
    (left right : trace.Occurrence) : Type :=
  { occurrence : trace.Occurrence //
      left < occurrence ∧ occurrence < right }

end SemanticTrace

/- Exact participation of the positionally intermediate occurrences in one
   generated constitutive bridge.  Exactness is occurrence-level first, with
   located-step agreement supplied afterwards. -/
structure ExactSemanticBridgeSegment
    {P : CircularPresentation}
    (trace : SemanticTrace P)
    (left right : trace.Occurrence)
    {source target : PositiveConstitution P}
    (bridge : GeneratedHistory source target) where
  forwardOccurrence :
    trace.Between left right → History.Occurrence bridge
  backwardOccurrence :
    History.Occurrence bridge → trace.Between left right
  forwardBackward :
    (occurrence : trace.Between left right) →
      backwardOccurrence (forwardOccurrence occurrence) = occurrence
  backwardForward :
    (occurrence : History.Occurrence bridge) →
      forwardOccurrence (backwardOccurrence occurrence) = occurrence
  locatedStepAgreement :
    (occurrence : trace.Between left right) →
      trace.locatedStep occurrence.1 =
        (forwardOccurrence occurrence).locatedStep

/- A constitutively effective bridge is not merely a generated history with
   matching endpoints.  Its generated occurrences must correspond exactly to
   all occurrences strictly between the two selected semantic-trace indices. -/
structure EffectiveConstitutiveBridge
    {P : CircularPresentation}
    (trace : SemanticTrace P)
    (left right : trace.Occurrence) where
  leftBeforeRight : left < right
  bridge :
    GeneratedHistory
      (trace.locatedStep left).target
      (trace.locatedStep right).source
  exactSegment :
    ExactSemanticBridgeSegment trace left right bridge

/- Between canonically adjacent requirements, an exact constitutive bridge has
   no intermediate occurrences.  Positional interleaving alone therefore does
   not establish constitutive participation. -/
theorem bridgeParticipation_between_empty_of_next
    {P : CircularPresentation}
    {trace : SemanticTrace P}
    (realization : SemanticExactNonClosingRealization P trace)
    {first second : NonClosingPosition P.perimeter}
    (next : NonClosingNext P.perimeter first second)
    (bridge : GeneratedHistory
      (trace.locatedStep (realization.realize first)).target
      (trace.locatedStep (realization.realize second)).source)
    (participates :
      trace.Between (realization.realize first) (realization.realize second) →
        History.Occurrence bridge) :
    trace.Between (realization.realize first) (realization.realize second) →
      False := by
  let firstCanonical :=
    positionLocatedStep P FreeConstitution.root
      BoundaryDifference.initial first
  let secondCanonical :=
    positionLocatedStep P FreeConstitution.root
      BoundaryDifference.initial second
  have firstExact := (realization.agreement first).locatedStepExact
  have secondExact := (realization.agreement second).locatedStepExact
  have canonicalEndpointEquality :
      firstCanonical.target = secondCanonical.source :=
    NonClosingNext.target_eq_source next
      FreeConstitution.root BoundaryDifference.initial
  have endpointEquality :
      (trace.locatedStep (realization.realize first)).target =
        (trace.locatedStep (realization.realize second)).source :=
    (congrArg
      (fun located : History.LocatedStep (@GeneratedStep P) => located.target)
      firstExact).trans
      (canonicalEndpointEquality.trans
        (congrArg
          (fun located : History.LocatedStep (@GeneratedStep P) => located.source)
          secondExact).symm)
  intro between
  exact generatedHistory_equalEndpoints_noOccurrence
    bridge endpointEquality (participates between)


/- The strong exact bridge statement is a direct corollary of the minimal
   participation theorem. -/
theorem effectiveBridge_between_empty_of_next
    {P : CircularPresentation}
    {trace : SemanticTrace P}
    (realization : SemanticExactNonClosingRealization P trace)
    {first second : NonClosingPosition P.perimeter}
    (next : NonClosingNext P.perimeter first second)
    (effective : EffectiveConstitutiveBridge trace
      (realization.realize first) (realization.realize second)) :
    trace.Between (realization.realize first) (realization.realize second) →
      False :=
  bridgeParticipation_between_empty_of_next realization next
    effective.bridge effective.exactSegment.forwardOccurrence


structure FaithfulPerimeterLabelling
    (P : CircularPresentation)
    (history : RootedGeneratedHistory P)
    (extension : PerimeterExtension P history) where
  label : History.Occurrence history.history → CircularRequirement P
  preservesNonClosingLabels :
    (position : NonClosingPosition P.perimeter) →
      label (extension.oldOccurrence position) = .inl position
  requirementFaithful :
    (first second : History.Occurrence history.history) →
      label first = label second → first = second

/- This weak positive layer contains only the constitutive extension and its
   faithful circular labelling.  It deliberately precedes every semantic
   realization and every totalization. -/
structure FaithfullyLabelledPerimeterExtension
    (P : CircularPresentation)
    (history : RootedGeneratedHistory P) where
  extension : PerimeterExtension P history
  labelling : FaithfulPerimeterLabelling P history extension

namespace FaithfullyLabelledPerimeterExtension

def continuation
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (labelled : FaithfullyLabelledPerimeterExtension P history) :
    GeneratedHistory (perimeterEndpoint P) history.endpoint :=
  labelled.extension.continuation

def label
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (labelled : FaithfullyLabelledPerimeterExtension P history) :
    History.Occurrence history.history → CircularRequirement P :=
  labelled.labelling.label

def oldOccurrence
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (labelled : FaithfullyLabelledPerimeterExtension P history)
    (position : NonClosingPosition P.perimeter) :
    History.Occurrence history.history :=
  labelled.extension.oldOccurrence position

def newOccurrence
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (labelled : FaithfullyLabelledPerimeterExtension P history)
    (occurrence : History.Occurrence labelled.continuation) :
    History.Occurrence history.history :=
  labelled.extension.newOccurrence occurrence

def preservesNonClosingLabels
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (labelled : FaithfullyLabelledPerimeterExtension P history)
    (position : NonClosingPosition P.perimeter) :
    labelled.label (labelled.oldOccurrence position) = .inl position :=
  labelled.labelling.preservesNonClosingLabels position

def requirementFaithful
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (labelled : FaithfullyLabelledPerimeterExtension P history)
    (first second : History.Occurrence history.history) :
    labelled.label first = labelled.label second → first = second :=
  labelled.labelling.requirementFaithful first second

theorem old_new_occurrences_disjoint
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (labelled : FaithfullyLabelledPerimeterExtension P history)
    (position : NonClosingPosition P.perimeter)
    (occurrence : History.Occurrence labelled.continuation) :
    labelled.oldOccurrence position ≠ labelled.newOccurrence occurrence :=
  labelled.extension.old_new_occurrences_disjoint position occurrence

/- Every faithfully labelled perimeter extension instantiates the abstract
   segmented residual-role interface. -/
def toSegmentedResidualExtension
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (labelled : FaithfullyLabelledPerimeterExtension P history) :
    SegmentedResidualRole.FaithfulExtension
      (NonClosingPosition P.perimeter)
      (FinalRequirement P)
      (History.Occurrence (perimeterHistory P))
      (History.Occurrence labelled.continuation)
      (History.Occurrence history.history)
      (perimeterInternalRoleRealization P)
      (finalRequirementContractible P) :=
  { embedOld := fun occurrence =>
      transportOccurrence labelled.extension.recompose
        (History.embedLeftOccurrence occurrence labelled.continuation)
    embedNew := labelled.newOccurrence
    oldNewDisjoint := by
      intro oldOccurrence newOccurrence equality
      have beforeTransport :=
        transportOccurrence_injective
          labelled.extension.recompose equality
      exact History.leftRightDisjoint
        oldOccurrence newOccurrence beforeTransport
    embedNewInjective := by
      intro first second equality
      have beforeTransport :=
        transportOccurrence_injective
          labelled.extension.recompose equality
      exact History.embedRightOccurrence_injective
        (perimeterHistory P) beforeTransport
    label := labelled.label
    preservesInternal := labelled.preservesNonClosingLabels
    labelFaithful := labelled.requirementFaithful }

theorem segmentedResidualExtension_embedOld_injective
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (labelled : FaithfullyLabelledPerimeterExtension P history) :
    Function.Injective labelled.toSegmentedResidualExtension.embedOld := by
  intro first second equality
  have embeddedEquality :=
    transportOccurrence_injective labelled.extension.recompose equality
  exact History.embedLeftOccurrence_injective
    labelled.continuation embeddedEquality

theorem newOccurrence_cannotReuseNonClosingRequirement
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (labelled : FaithfullyLabelledPerimeterExtension P history)
    (occurrence : History.Occurrence labelled.continuation)
    (position : NonClosingPosition P.perimeter)
    (labelEquality :
      labelled.label (labelled.newOccurrence occurrence) = .inl position) :
    False :=
  labelled.toSegmentedResidualExtension
    |>.newOccurrence_cannotReuseInternalRole
      occurrence position labelEquality

theorem newOccurrence_label_is_final
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (labelled : FaithfullyLabelledPerimeterExtension P history)
    (occurrence : History.Occurrence labelled.continuation) :
    labelled.label (labelled.newOccurrence occurrence) =
      .inr .distinguished :=
  labelled.toSegmentedResidualExtension
    |>.newOccurrence_label_is_residual occurrence

theorem continuation_occurrences_unique
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (labelled : FaithfullyLabelledPerimeterExtension P history)
    (first second : History.Occurrence labelled.continuation) :
    first = second :=
  labelled.toSegmentedResidualExtension
    |>.newOccurrences_unique first second

end FaithfullyLabelledPerimeterExtension

structure PositiveContinuation
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (extension : PerimeterExtension P history) where
  path : History.Positive
    (@GeneratedStep P) (perimeterEndpoint P) history.endpoint
  historyExact : extension.continuation = path.toHistory

namespace PositiveContinuation

def toResidualPositive
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    {labelled : FaithfullyLabelledPerimeterExtension P history}
    (positive : PositiveContinuation labelled.extension) :
    SegmentedResidualRole.PositiveNewPart
      (History.Occurrence labelled.continuation) :=
  { occurrence :=
      transportOccurrence positive.historyExact.symm
        positive.path.lastOccurrence }

end PositiveContinuation

namespace FaithfullyLabelledPerimeterExtension

def reconstructedInternalCompletion
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (labelled : FaithfullyLabelledPerimeterExtension P history)
    (positive : PositiveContinuation labelled.extension) :
    SegmentedResidualRole.ExactInternalCompletion
      labelled.toSegmentedResidualExtension.toResidualUniquenessKernel :=
  labelled.toSegmentedResidualExtension.reconstructInternalCompletion
    positive.toResidualPositive

theorem reconstructed_roleToOccurrence_agrees
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (labelled : FaithfullyLabelledPerimeterExtension P history)
    (positive : PositiveContinuation labelled.extension)
    (position : NonClosingPosition P.perimeter) :
    (labelled.reconstructedInternalCompletion positive
      |>.toExactInternalRealization).roleToOccurrence position =
        requirementToOccurrence P position :=
  labelled.toSegmentedResidualExtension
    |>.reconstructed_roleToOccurrence_agrees
      positive.toResidualPositive position

theorem reconstructed_occurrenceToRole_agrees
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (labelled : FaithfullyLabelledPerimeterExtension P history)
    (positive : PositiveContinuation labelled.extension)
    (occurrence : History.Occurrence (perimeterHistory P)) :
    (labelled.reconstructedInternalCompletion positive).occurrenceToRole
        occurrence = occurrenceToRequirement P occurrence :=
  labelled.toSegmentedResidualExtension
    |>.reconstructed_occurrenceToRole_agrees
      positive.toResidualPositive occurrence

end FaithfullyLabelledPerimeterExtension

def oneStepAfterPerimeter_positiveContinuation
    (P : CircularPresentation) :
    PositiveContinuation (oneStepAfterPerimeter_is_extension P) :=
  { path :=
      { predecessor := perimeterEndpoint P
        priorHistory := .root
        lastStep := (generate_after_perimeter P).2 }
    historyExact := rfl }

def History.exactlyOneOfPositiveAndUnique
    {State : Type uA}
    {Step : State → State → Type uB}
    {source target : State}
    (positive : History.Positive Step source target)
    (unique :
      (first second : History.Occurrence positive.toHistory) →
        first = second) :
    History.ExactlyOne positive.toHistory := by
  cases positive with
  | mk predecessor priorHistory lastStep =>
      cases priorHistory with
      | root => exact .single lastStep
      | extend previous penultimateStep =>
          have impossible := unique
            (.last : History.Occurrence
              (.extend (.extend previous penultimateStep) lastStep))
            (.earlier (.last : History.Occurrence
              (.extend previous penultimateStep)))
          cases impossible

def positiveContinuation_exactlyOne
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (labelled : FaithfullyLabelledPerimeterExtension P history)
    (positive : PositiveContinuation labelled.extension) :
    History.ExactlyOne labelled.continuation :=
  let pathExactlyOne : History.ExactlyOne positive.path.toHistory :=
    History.exactlyOneOfPositiveAndUnique positive.path fun first second =>
      transportOccurrence_injective positive.historyExact.symm
        (labelled.continuation_occurrences_unique
          (transportOccurrence positive.historyExact.symm first)
          (transportOccurrence positive.historyExact.symm second))
  cast
    (congrArg
      (fun continuation => History.ExactlyOne continuation)
      positive.historyExact.symm)
    pathExactlyOne

theorem rootContinuation_not_positive
    (P : CircularPresentation) :
    PositiveContinuation (identityPerimeterExtension P) → False := by
  intro positive
  have equality := positive.historyExact
  cases positive.path with
  | mk predecessor priorHistory lastStep =>
      cases equality

structure FinalBoundaryOccurrence
    (P : CircularPresentation)
    (history : RootedGeneratedHistory P) where
  labelled : FaithfullyLabelledPerimeterExtension P history
  positive : PositiveContinuation labelled.extension
  continuationOccurrence : History.Occurrence labelled.continuation
  occurrenceIsCanonical :
    continuationOccurrence =
      transportOccurrence positive.historyExact.symm
        positive.path.lastOccurrence
  labelIsFinal :
    labelled.label (labelled.newOccurrence continuationOccurrence) =
      .inr .distinguished

def finalBoundaryOccurrence
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (labelled : FaithfullyLabelledPerimeterExtension P history)
    (positive : PositiveContinuation labelled.extension) :
    FinalBoundaryOccurrence P history :=
  let occurrence :=
    transportOccurrence positive.historyExact.symm
      positive.path.lastOccurrence
  { labelled := labelled
    positive := positive
    continuationOccurrence := occurrence
    occurrenceIsCanonical := rfl
    labelIsFinal := labelled.newOccurrence_label_is_final occurrence }

namespace FinalBoundaryOccurrence

def historyOccurrence
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (boundary : FinalBoundaryOccurrence P history) :
    History.Occurrence history.history :=
  boundary.labelled.newOccurrence boundary.continuationOccurrence

def locatedStep
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (boundary : FinalBoundaryOccurrence P history) :
    History.LocatedStep (@GeneratedStep P) :=
  boundary.continuationOccurrence.locatedStep

def source
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (boundary : FinalBoundaryOccurrence P history) :
    PositiveConstitution P :=
  boundary.locatedStep.source

def target
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (boundary : FinalBoundaryOccurrence P history) :
    PositiveConstitution P :=
  boundary.locatedStep.target

def step
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (boundary : FinalBoundaryOccurrence P history) :
    GeneratedStep boundary.source boundary.target :=
  boundary.locatedStep.step

def step_is_generatedStep
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (boundary : FinalBoundaryOccurrence P history) :
    GeneratedStep boundary.source boundary.target :=
  boundary.step

def continuationExactlyOne
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (boundary : FinalBoundaryOccurrence P history) :
    History.ExactlyOne boundary.labelled.continuation :=
  positiveContinuation_exactlyOne boundary.labelled boundary.positive

theorem uniqueContinuationOccurrence
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (boundary : FinalBoundaryOccurrence P history)
    (occurrence : History.Occurrence boundary.labelled.continuation) :
    occurrence = boundary.continuationOccurrence :=
  boundary.labelled.continuation_occurrences_unique
    occurrence boundary.continuationOccurrence

theorem source_is_perimeterEndpoint
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (boundary : FinalBoundaryOccurrence P history) :
    boundary.source = perimeterEndpoint P :=
  boundary.continuationExactlyOne.locatedStep_source
    boundary.continuationOccurrence

theorem target_is_historyEndpoint
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (boundary : FinalBoundaryOccurrence P history) :
    boundary.target = history.endpoint :=
  boundary.continuationExactlyOne.locatedStep_target
    boundary.continuationOccurrence

theorem target_is_canonicalTarget
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (boundary : FinalBoundaryOccurrence P history) :
    boundary.target = canonicalTarget (perimeterEndpoint P) := by
  exact boundary.step.formedByFreeLayer.trans
    (congrArg canonicalTarget boundary.source_is_perimeterEndpoint)

theorem source_cursor_is_boundary
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (boundary : FinalBoundaryOccurrence P history) :
    boundary.source.1 = .within (.boundary P.perimeter.finalNode) :=
  (congrArg Sigma.fst boundary.source_is_perimeterEndpoint).trans
    (perimeterEndpoint_cursor_boundary P)

theorem target_cursor_is_beyond_first
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (boundary : FinalBoundaryOccurrence P history) :
    boundary.target.1 = .beyond .first := by
  exact (congrArg Sigma.fst boundary.target_is_canonicalTarget).trans
    (generate_after_perimeter_is_beyond P)

theorem compatibility_is_leaveBoundary
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (boundary : FinalBoundaryOccurrence P history) :
    HEq boundary.step.compatibility
      (ReturnedCompatible.leaveBoundary P.perimeter.finalNode) := by
  have exactCompatibility := boundary.step.compatibilityWitnessExact
  exact exactCompatibility.trans (by
    rw [boundary.source_cursor_is_boundary]
    rfl)

end FinalBoundaryOccurrence

/- The interpretation keeps the actual free boundary step and the invoked
   circular junction in one positive witness without identifying them.  It
   also records the exact formation, provenance and transported obstruction
   carried by the actual occurrence. -/
structure FinalClosureInterpretation
    (P : CircularPresentation)
    (history : RootedGeneratedHistory P) where
  boundary : FinalBoundaryOccurrence P history
  actualStepCompatibility :
    ReturnedCompatible P
      (implicitRead boundary.source)
      (explicitRead boundary.target)
  actualStepCompatibilityIsExact :
    actualStepCompatibility = boundary.step.compatibility
  junction : FinalJunctionCompatibility P
  junctionIsDistinguished : junction = P.finalJunction
  formationRecord : FormationRecord P boundary.target.2.1
  formationRecordIsStepExact :
    formationRecord = boundary.step.currentFormationRecord
  provenanceRecord :
    HistoricalProvenanceRecord P
      boundary.source boundary.target.2.1
  provenanceRecordIsStepExact :
    provenanceRecord = boundary.step.sourceProvenanceInscribedInTarget
  sourceObstruction : PositiveClosureObstruction P
  sourceObstructionIsExact :
    sourceObstruction =
      boundary.source.2.1.1.inheritedClosureObstruction
  targetObstruction : PositiveClosureObstruction P
  targetObstructionIsExact :
    targetObstruction =
      boundary.target.2.1.1.inheritedClosureObstruction
  targetObstructionIsInherited : targetObstruction = sourceObstruction
  targetObstructionIsInitial :
    targetObstruction = P.positiveClosureObstruction

def finalClosureInterpretation
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (boundary : FinalBoundaryOccurrence P history) :
    FinalClosureInterpretation P history :=
  { boundary := boundary
    actualStepCompatibility := boundary.step.compatibility
    actualStepCompatibilityIsExact := rfl
    junction := P.finalJunction
    junctionIsDistinguished := rfl
    formationRecord := boundary.step.currentFormationRecord
    formationRecordIsStepExact := rfl
    provenanceRecord := boundary.step.sourceProvenanceInscribedInTarget
    provenanceRecordIsStepExact := rfl
    sourceObstruction :=
      boundary.source.2.1.1.inheritedClosureObstruction
    sourceObstructionIsExact := rfl
    targetObstruction :=
      boundary.target.2.1.1.inheritedClosureObstruction
    targetObstructionIsExact := rfl
    targetObstructionIsInherited :=
      boundary.step.inheritedClosureObstructionExact
    targetObstructionIsInitial :=
      (congrArg
        (fun state : PositiveConstitution P =>
          state.2.1.1.inheritedClosureObstruction)
        boundary.target_is_historyEndpoint).trans
        (RootedGeneratedHistory.terminalClosureObstruction_is_initial history) }

namespace FinalClosureInterpretation

def actualFreeStep
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (interpretation : FinalClosureInterpretation P history) :
    GeneratedStep interpretation.boundary.source
      interpretation.boundary.target :=
  interpretation.boundary.step

def invokedFinalJunction
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (interpretation : FinalClosureInterpretation P history) :
    FinalJunctionCompatibility P :=
  interpretation.junction

theorem sourceObstructionIsInitial
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (interpretation : FinalClosureInterpretation P history) :
    interpretation.sourceObstruction = P.positiveClosureObstruction :=
  interpretation.targetObstructionIsInherited.symm.trans
    interpretation.targetObstructionIsInitial

theorem actualFreeStep_source_is_terminalImplicit
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (interpretation : FinalClosureInterpretation P history) :
    implicitRead interpretation.boundary.source =
      .source P.perimeter.finalNode.implicit := by
  rw [interpretation.boundary.source_is_perimeterEndpoint]
  change implicitAt (perimeterEndpoint P).1 = _
  rw [perimeterEndpoint_cursor_boundary]
  rfl

theorem actualFreeStep_target_is_freeExplicit
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (interpretation : FinalClosureInterpretation P history) :
    explicitRead interpretation.boundary.target =
      .formed (.beyond .first) := by
  change explicitAt interpretation.boundary.target.1 = _
  rw [interpretation.boundary.target_cursor_is_beyond_first]
  rfl

def invokedFinalJunction_source
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (_interpretation : FinalClosureInterpretation P history) : P.Implicit :=
  P.perimeter.finalNode.implicit

def invokedFinalJunction_target
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (_interpretation : FinalClosureInterpretation P history) : P.Explicit :=
  P.initialNode.explicit

theorem invokedFinalJunction_source_is_terminalImplicit
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (interpretation : FinalClosureInterpretation P history) :
    interpretation.invokedFinalJunction_source =
      P.perimeter.finalNode.implicit :=
  rfl

theorem invokedFinalJunction_target_is_initialExplicit
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (interpretation : FinalClosureInterpretation P history) :
    interpretation.invokedFinalJunction_target =
      P.initialNode.explicit :=
  rfl

end FinalClosureInterpretation

structure ConstitutiveClosureAttachment
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (interpretation : FinalClosureInterpretation P history) where
  formationRecord :
    FormationRecord P interpretation.boundary.target.2.1
  formationRecordIsExact :
    formationRecord = interpretation.formationRecord
  provenanceRecord :
    HistoricalProvenanceRecord P
      interpretation.boundary.source
      interpretation.boundary.target.2.1
  provenanceRecordIsExact :
    provenanceRecord = interpretation.provenanceRecord
  obstruction : PositiveClosureObstruction P
  obstructionIsExact : obstruction = interpretation.targetObstruction

def ConstitutiveClosureAttachment.canonical
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (interpretation : FinalClosureInterpretation P history) :
    ConstitutiveClosureAttachment interpretation :=
  { formationRecord := interpretation.formationRecord
    formationRecordIsExact := rfl
    provenanceRecord := interpretation.provenanceRecord
    provenanceRecordIsExact := rfl
    obstruction := interpretation.targetObstruction
    obstructionIsExact := rfl }

namespace ConstitutiveClosureAttachment

theorem formationRecordIsStepExact
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    {interpretation : FinalClosureInterpretation P history}
    (attachment : ConstitutiveClosureAttachment interpretation) :
    attachment.formationRecord =
      interpretation.boundary.step.currentFormationRecord :=
  attachment.formationRecordIsExact.trans
    interpretation.formationRecordIsStepExact

theorem provenanceRecordIsStepExact
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    {interpretation : FinalClosureInterpretation P history}
    (attachment : ConstitutiveClosureAttachment interpretation) :
    attachment.provenanceRecord =
      interpretation.boundary.step.sourceProvenanceInscribedInTarget :=
  attachment.provenanceRecordIsExact.trans
    interpretation.provenanceRecordIsStepExact

theorem obstructionIsInitial
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    {interpretation : FinalClosureInterpretation P history}
    (attachment : ConstitutiveClosureAttachment interpretation) :
    attachment.obstruction = P.positiveClosureObstruction :=
  attachment.obstructionIsExact.trans
    interpretation.targetObstructionIsInitial

end ConstitutiveClosureAttachment

structure BilateralClosureAttemptAt
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (interpretation : FinalClosureInterpretation P history) where
  attachment : ConstitutiveClosureAttachment interpretation
  explicitTotalization : ExplicitTotalization P
  implicitTotalization : ImplicitTotalization P

namespace BilateralClosureAttemptAt

def explicitContraction
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    {interpretation : FinalClosureInterpretation P history}
    (attempt : BilateralClosureAttemptAt interpretation) :
    ContractedClosureDifference P :=
  { difference := P.initialNode.difference
    isInitialDifference := rfl
    provenance := attempt.attachment.obstruction.provenance
    poleContraction :=
      (explicitTotalizationContractsClosureDifference
        attempt.explicitTotalization).poleContraction }

def implicitContraction
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    {interpretation : FinalClosureInterpretation P history}
    (attempt : BilateralClosureAttemptAt interpretation) :
    ContractedClosureDifference P :=
  { difference := P.initialNode.difference
    isInitialDifference := rfl
    provenance := attempt.attachment.obstruction.provenance
    poleContraction :=
      (implicitTotalizationContractsClosureDifference
        attempt.implicitTotalization).poleContraction }

structure Contractions
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    {interpretation : FinalClosureInterpretation P history}
    (attempt : BilateralClosureAttemptAt interpretation) where
  explicitSide : ContractedClosureDifference P
  explicitSideIsDerived : explicitSide = attempt.explicitContraction
  implicitSide : ContractedClosureDifference P
  implicitSideIsDerived : implicitSide = attempt.implicitContraction

def contractions
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    {interpretation : FinalClosureInterpretation P history}
    (attempt : BilateralClosureAttemptAt interpretation) :
    attempt.Contractions :=
  { explicitSide := attempt.explicitContraction
    explicitSideIsDerived := rfl
    implicitSide := attempt.implicitContraction
    implicitSideIsDerived := rfl }

def rejectExplicit
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    {interpretation : FinalClosureInterpretation P history}
    (attempt : BilateralClosureAttemptAt interpretation) : False :=
  attempt.attachment.obstruction.rejectsContraction
    attempt.explicitContraction.initialPoleContraction

def rejectImplicit
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    {interpretation : FinalClosureInterpretation P history}
    (attempt : BilateralClosureAttemptAt interpretation) : False :=
  attempt.attachment.obstruction.rejectsContraction
    attempt.implicitContraction.initialPoleContraction

end BilateralClosureAttemptAt

structure CircularRefinement
    (P : CircularPresentation)
    (history : RootedGeneratedHistory P) where
  extension : PerimeterExtension P history
  labelling : FaithfulPerimeterLabelling P history extension
  realizesNonClosing :
    (occurrence : History.Occurrence history.history) →
    (position : NonClosingPosition P.perimeter) →
    labelling.label occurrence = .inl position →
      RequirementOccurrenceAgreement P history position occurrence
  realizesFinal :
    (positive : PositiveContinuation extension) →
      BilateralClosureAttemptAt
        (finalClosureInterpretation
          (finalBoundaryOccurrence
            { extension := extension, labelling := labelling }
            positive))

namespace CircularRefinement

def toLabelled
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (refinement : CircularRefinement P history) :
    FaithfullyLabelledPerimeterExtension P history :=
  { extension := refinement.extension
    labelling := refinement.labelling }

def continuation
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (refinement : CircularRefinement P history) :
    GeneratedHistory (perimeterEndpoint P) history.endpoint :=
  refinement.extension.continuation

def recompose
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (refinement : CircularRefinement P history) :
    History.append (perimeterHistory P) refinement.continuation =
      history.history :=
  refinement.extension.recompose

def label
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (refinement : CircularRefinement P history) :
    History.Occurrence history.history → CircularRequirement P :=
  refinement.labelling.label

def preservesNonClosingLabels
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (refinement : CircularRefinement P history)
    (position : NonClosingPosition P.perimeter) :
    refinement.label (refinement.extension.oldOccurrence position) =
      .inl position :=
  refinement.labelling.preservesNonClosingLabels position

def requirementFaithful
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (refinement : CircularRefinement P history)
    (first second : History.Occurrence history.history) :
    refinement.label first = refinement.label second → first = second :=
  refinement.labelling.requirementFaithful first second

def oldOccurrence
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (refinement : CircularRefinement P history)
    (position : NonClosingPosition P.perimeter) :
    History.Occurrence history.history :=
  refinement.extension.oldOccurrence position

def newOccurrence
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (refinement : CircularRefinement P history)
    (occurrence : History.Occurrence refinement.continuation) :
    History.Occurrence history.history :=
  refinement.extension.newOccurrence occurrence

theorem old_new_occurrences_disjoint
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (refinement : CircularRefinement P history)
    (position : NonClosingPosition P.perimeter)
    (occurrence : History.Occurrence refinement.continuation) :
    refinement.oldOccurrence position ≠
      refinement.newOccurrence occurrence := by
  exact refinement.extension.old_new_occurrences_disjoint position occurrence

theorem newOccurrence_cannotReuseNonClosingRequirement
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (refinement : CircularRefinement P history)
    (newOccurrence : History.Occurrence refinement.continuation)
    (position : NonClosingPosition P.perimeter)
    (labelEquality :
      refinement.label (refinement.newOccurrence newOccurrence) =
        .inl position) : False := by
  exact refinement.toLabelled.newOccurrence_cannotReuseNonClosingRequirement
    newOccurrence position labelEquality

end CircularRefinement

def identityCircularRefinement (P : CircularPresentation) :
    CircularRefinement P (perimeterDeployment P) :=
  { extension := identityPerimeterExtension P
    labelling :=
      { label := fun occurrence =>
          .inl (occurrenceToRequirement P occurrence)
        preservesNonClosingLabels := by
          intro position
          exact congrArg Sum.inl
            (requirementToOccurrence_toRequirement P position)
        requirementFaithful := by
          intro first second labelEquality
          have positionEquality :
              occurrenceToRequirement P first =
                occurrenceToRequirement P second :=
            Sum.inl.inj labelEquality
          exact (occurrenceToRequirement_toOccurrence P first).symm.trans
            ((congrArg (requirementToOccurrence P) positionEquality).trans
              (occurrenceToRequirement_toOccurrence P second)) }
    realizesNonClosing := by
      intro occurrence position labelEquality
      have positionEquality :
          occurrenceToRequirement P occurrence = position :=
        Sum.inl.inj labelEquality
      cases positionEquality
      have roundTrip := occurrenceToRequirement_toOccurrence P occurrence
      exact RequirementOccurrenceAgreement.transportOccurrence roundTrip
        (canonicalRequirementAgreement P _)
    realizesFinal := fun positive =>
      False.elim (rootContinuation_not_positive P positive) }

/-! ## Core circular regime

This layer separates the structural regime data from the historical circular
refinement and supplies the direct core path.  The historical rich turning
wrapper remains available separately. -/

structure CoreCircularResidualContext
    (P : CircularPresentation)
    (history : RootedGeneratedHistory P) where
  extension : PerimeterExtension P history
  positive : PositiveContinuation extension

def coreCircularBoundaryType
    (P : CircularPresentation)
    (history : RootedGeneratedHistory P) : Type _ :=
  AbstractSegmentedTurning.CorePositiveResidualBoundary
    (perimetralBoundaryGenerator P)
    (fun _candidate => CoreCircularResidualContext P _candidate)
    (fun {_candidate} context =>
      History.Occurrence context.extension.continuation)
    (NonClosingPosition P.perimeter)
    (FinalRequirement P)
    (finalRequirementContractible P)
    history

def coreCircularPositiveResidualBoundary
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (extension : PerimeterExtension P history)
    (positive : PositiveContinuation extension)
    (core : SegmentedResidualRole.ResidualDeterminationCore
      (NonClosingPosition P.perimeter)
      (FinalRequirement P)
      (History.Occurrence extension.continuation)
      (finalRequirementContractible P)) :
    coreCircularBoundaryType P history :=
  { context := { extension := extension, positive := positive }
    strict :=
      { continuation := positive.path
        historyExact := by
          change History.append (perimeterHistory P)
            positive.path.toHistory = history.history
          rw [← positive.historyExact]
          exact extension.recompose }
    core := core
    positive :=
      { occurrence :=
          transportOccurrence positive.historyExact.symm
            positive.path.lastOccurrence } }

structure CoreResidualClosureInterpretation
    {P : CircularPresentation}
    (history : RootedGeneratedHistory P) where
  boundary : coreCircularBoundaryType P history
  residualOccurrence :
    History.Occurrence boundary.context.extension.continuation
  residualOccurrenceIsPositive :
    residualOccurrence = boundary.positive.occurrence
  residualLabelIsResidual :
    boundary.core.newLabel residualOccurrence =
      .inr (finalRequirementContractible P).center
  obstruction : PositiveClosureObstruction P

def coreInterpretResidual
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (boundary : coreCircularBoundaryType P history)
    (unique : SegmentedResidualRole.CoreUniqueResidualOccurrence
      boundary.core) :
    CoreResidualClosureInterpretation history :=
  { boundary := boundary
    residualOccurrence := unique.occurrence
    residualOccurrenceIsPositive :=
      (unique.unique boundary.positive.occurrence).symm
    residualLabelIsResidual := unique.labelIsResidual
    obstruction := P.positiveClosureObstruction }

structure CoreResidualClosureAttempt
    {P : CircularPresentation}
    (history : RootedGeneratedHistory P)
    (interpretation : CoreResidualClosureInterpretation history) where
  explicitTotalization : ExplicitTotalization P
  implicitTotalization : ImplicitTotalization P

def rejectCoreResidualClosureAttempt
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    {interpretation : CoreResidualClosureInterpretation history}
    (attempt : CoreResidualClosureAttempt history interpretation) : False :=
  interpretation.obstruction.rejectsContraction
    (explicitTotalizationContractsClosureDifference
      attempt.explicitTotalization).initialPoleContraction

def CoreCircularPositiveBranch
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (extension : PerimeterExtension P history)
    (positive : PositiveContinuation extension) : Type _ :=
    Σ core : SegmentedResidualRole.ResidualDeterminationCore
      (NonClosingPosition P.perimeter)
      (FinalRequirement P)
      (History.Occurrence extension.continuation)
      (finalRequirementContractible P),
    CoreResidualClosureAttempt
        _
        (coreInterpretResidual
        (coreCircularPositiveResidualBoundary extension positive core)
        (AbstractSegmentedTurning.CorePositiveResidualBoundary.uniqueResidualOccurrence
          (coreCircularPositiveResidualBoundary extension positive core)))

structure CoreCircularRefinement
    (P : CircularPresentation)
    (history : RootedGeneratedHistory P) where
  extension : PerimeterExtension P history
  positiveBranch :
    (positive : PositiveContinuation extension) →
      CoreCircularPositiveBranch extension positive

def identityCoreCircularRefinement (P : CircularPresentation) :
    CoreCircularRefinement P (perimeterDeployment P) :=
  { extension := identityPerimeterExtension P
    positiveBranch := fun positive =>
      False.elim (rootContinuation_not_positive P positive) }

def CircularRefinement.toCoreCircularRefinement
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (refinement : CircularRefinement P history) :
    CoreCircularRefinement P history :=
  { extension := refinement.extension
    positiveBranch := fun positive =>
      let richAttempt := refinement.realizesFinal positive
      let core :=
        refinement.toLabelled.toSegmentedResidualExtension
          |>.toResidualUniquenessKernel
          |>.toDeterminationCore
      ⟨core,
        { explicitTotalization := richAttempt.explicitTotalization
          implicitTotalization := richAttempt.implicitTotalization }⟩ }

theorem coreCircularRefinement_history_eq_perimeter
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (refinement : CoreCircularRefinement P history) :
    history = perimeterDeployment P := by
  cases History.appendRootOrPositive
      (perimeterHistory P) refinement.extension.continuation with
  | inl rootData =>
      rcases rootData with ⟨endpointEquality, continuationEquality⟩
      exact rootedGeneratedHistory_ext endpointEquality.down
        ((heq_of_eq refinement.extension.recompose.symm).trans
          continuationEquality.down)
  | inr positiveData =>
      rcases positiveData with ⟨positive, continuationEquality⟩
      let positiveContinuation : PositiveContinuation refinement.extension :=
        { path := positive
          historyExact := continuationEquality.down }
      rcases refinement.positiveBranch positiveContinuation with
        ⟨core, attempt⟩
      exact False.elim (rejectCoreResidualClosureAttempt attempt)

theorem circularRefinement_nonempty_iff_coreCircularRefinement_nonempty
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P} :
    Nonempty (CircularRefinement P history) ↔
      Nonempty (CoreCircularRefinement P history) := by
  constructor
  · rintro ⟨refinement⟩
    exact ⟨refinement.toCoreCircularRefinement⟩
  · rintro ⟨refinement⟩
    have historyEquality :=
      coreCircularRefinement_history_eq_perimeter refinement
    cases historyEquality
    exact ⟨identityCircularRefinement P⟩

/- Regime completeness by carrier classification: no operational field of
   `CircularRefinement` is reconstructed from the independent specification. -/
def circularSpecification_complete
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (satisfaction : CircularSpecificationSatisfaction P history) :
    CircularRefinement P history := by
  have historyEquality :
      history = perimeterDeployment P :=
    satisfaction.eq_perimeter
  cases historyEquality
  exact identityCircularRefinement P

def oneStepFaithfulLabelling
    (P : CircularPresentation) :
    FaithfulPerimeterLabelling P (oneStepAfterPerimeter P)
      (oneStepAfterPerimeter_is_extension P) :=
  { label := fun occurrence =>
      match occurrence with
      | .last => .inr .distinguished
      | .earlier earlier => .inl (occurrenceToRequirement P earlier)
    preservesNonClosingLabels := by
      intro position
      exact congrArg Sum.inl
        (requirementToOccurrence_toRequirement P position)
    requirementFaithful := by
      intro first second labelEquality
      cases first with
      | last =>
          cases second with
          | last => rfl
          | earlier earlier => cases labelEquality
      | earlier firstEarlier =>
          cases second with
          | last => cases labelEquality
          | earlier secondEarlier =>
              have positionEquality :
                  occurrenceToRequirement P firstEarlier =
                    occurrenceToRequirement P secondEarlier :=
                Sum.inl.inj labelEquality
              exact congrArg History.Occurrence.earlier
                ((occurrenceToRequirement_toOccurrence P firstEarlier).symm.trans
                  ((congrArg (requirementToOccurrence P) positionEquality).trans
                    (occurrenceToRequirement_toOccurrence P secondEarlier))) }

def oneStepFaithfullyLabelledExtension
    (P : CircularPresentation) :
    FaithfullyLabelledPerimeterExtension P (oneStepAfterPerimeter P) :=
  { extension := oneStepAfterPerimeter_is_extension P
    labelling := oneStepFaithfulLabelling P }

/- The one-step boundary occurrence is the segmented component of the
   abstract turning.  Circular closure data is absent from this adapter. -/
def oneStepSegmentedBoundary
    (P : CircularPresentation) :
    AbstractSegmentedTurning.SegmentedBoundary
      (perimetralBoundaryGenerator P)
      (NonClosingPosition P.perimeter)
      (FinalRequirement P)
      (History.Occurrence (perimeterHistory P))
      (History.Occurrence
        (oneStepFaithfullyLabelledExtension P).continuation)
      (History.Occurrence (oneStepAfterPerimeter P).history)
      (perimeterInternalRoleRealization P)
      (finalRequirementContractible P) :=
  let positive := oneStepAfterPerimeter_positiveContinuation P
  { extension :=
      (oneStepFaithfullyLabelledExtension P).toSegmentedResidualExtension
    positive :=
      { occurrence :=
          transportOccurrence positive.historyExact.symm
            positive.path.lastOccurrence } }

def oneStepResidualPositive
    (P : CircularPresentation) :
    SegmentedResidualRole.PositiveNewPart
      (History.Occurrence
        (oneStepFaithfullyLabelledExtension P).continuation) :=
  (oneStepAfterPerimeter_positiveContinuation P).toResidualPositive

/- This is the positive occurrence stored by the segmented boundary itself.
   The equality is exported so the residual result can be checked against the
   exact producer field rather than only against an adapter defined alongside
   it. -/
theorem oneStepResidualPositive_agrees_with_segmentedBoundary
    (P : CircularPresentation) :
    (oneStepResidualPositive P).occurrence =
      (oneStepSegmentedBoundary P).positive.occurrence :=
  rfl

def oneStepReconstructedInternalCompletion
    (P : CircularPresentation) :
    SegmentedResidualRole.ExactInternalCompletion
      ((oneStepFaithfullyLabelledExtension P).toSegmentedResidualExtension
        |>.toResidualUniquenessKernel) :=
  (oneStepFaithfullyLabelledExtension P).reconstructedInternalCompletion
    (oneStepAfterPerimeter_positiveContinuation P)

def oneStepReconstructedInternalRealization
    (P : CircularPresentation) :
    SegmentedResidualRole.ExactInternalRealization
      (NonClosingPosition P.perimeter)
      (History.Occurrence (perimeterHistory P)) :=
  (oneStepReconstructedInternalCompletion P).toExactInternalRealization

theorem oneStepReconstructed_roleToOccurrence_agrees
    (P : CircularPresentation)
    (position : NonClosingPosition P.perimeter) :
    (oneStepReconstructedInternalRealization P).roleToOccurrence position =
      requirementToOccurrence P position :=
  (oneStepFaithfullyLabelledExtension P)
    |>.reconstructed_roleToOccurrence_agrees
      (oneStepAfterPerimeter_positiveContinuation P) position

theorem oneStepReconstructed_occurrenceToRole_agrees
    (P : CircularPresentation)
    (occurrence : History.Occurrence (perimeterHistory P)) :
    (oneStepReconstructedInternalRealization P).occurrenceToRole occurrence =
      occurrenceToRequirement P occurrence :=
  (oneStepFaithfullyLabelledExtension P)
    |>.reconstructed_occurrenceToRole_agrees
      (oneStepAfterPerimeter_positiveContinuation P) occurrence

def oneStepWeakResidualOccurrence
    (P : CircularPresentation) :
    SegmentedResidualRole.KernelUniqueResidualOccurrence
      ((oneStepFaithfullyLabelledExtension P).toSegmentedResidualExtension
        |>.toResidualUniquenessKernel) :=
  SegmentedResidualRole.positiveKernel_hasUniqueResidualOccurrence
    ((oneStepFaithfullyLabelledExtension P).toSegmentedResidualExtension
      |>.toResidualUniquenessKernel)
    (oneStepResidualPositive P)

def oneStepPublicResidualOccurrence
    (P : CircularPresentation) :
    SegmentedResidualRole.UniqueResidualOccurrence
      (oneStepFaithfullyLabelledExtension P).toSegmentedResidualExtension :=
  SegmentedResidualRole.positiveExtension_hasUniqueResidualOccurrence
    (oneStepFaithfullyLabelledExtension P).toSegmentedResidualExtension
    (oneStepResidualPositive P)

theorem oneStepResidualOccurrence_agrees
    (P : CircularPresentation) :
    (oneStepWeakResidualOccurrence P).occurrence =
      (oneStepPublicResidualOccurrence P).occurrence :=
  rfl

theorem oneStepWeakResidualOccurrence_label_is_final
    (P : CircularPresentation) :
    let kernel :=
      (oneStepFaithfullyLabelledExtension P).toSegmentedResidualExtension
        |>.toResidualUniquenessKernel
    kernel.label
        (kernel.embedNew (oneStepWeakResidualOccurrence P).occurrence) =
      .inr FinalRequirement.distinguished :=
  (oneStepWeakResidualOccurrence P).labelIsResidual

theorem oneStepWeakResidualOccurrence_unique
    (P : CircularPresentation)
    (other : History.Occurrence
      (oneStepFaithfullyLabelledExtension P).continuation) :
    other = (oneStepWeakResidualOccurrence P).occurrence :=
  (oneStepWeakResidualOccurrence P).unique other

structure FinalJunctionRealization
    (P : CircularPresentation)
    (history : RootedGeneratedHistory P) where
  interpretation : FinalClosureInterpretation P history
  attempt : BilateralClosureAttemptAt interpretation

namespace FinalJunctionRealization

def toBilateralContractions
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (realization : FinalJunctionRealization P history) :
    realization.attempt.Contractions :=
  realization.attempt.contractions

def toExplicitContractedClosureDifference
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (realization : FinalJunctionRealization P history) :
    ContractedClosureDifference P :=
  realization.attempt.explicitContraction

def toImplicitContractedClosureDifference
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (realization : FinalJunctionRealization P history) :
    ContractedClosureDifference P :=
  realization.attempt.implicitContraction

def toContractedClosureDifference
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (realization : FinalJunctionRealization P history) :
    ContractedClosureDifference P :=
  realization.toExplicitContractedClosureDifference

def endpointEquality
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (realization : FinalJunctionRealization P history) :
    P.leftEndpoint = P.rightEndpoint :=
  realization.toContractedClosureDifference.endpointContraction

def toTotalLoop
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (realization : FinalJunctionRealization P history) : P.TotalLoop :=
  realization.toContractedClosureDifference.toTotalLoop

end FinalJunctionRealization

structure FinalLoopRealization
    (P : CircularPresentation)
    (history : RootedGeneratedHistory P) where
  witness : FinalJunctionRealization P history

def FinalJunctionRealization.toFinalLoopRealization
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (realization : FinalJunctionRealization P history) :
    FinalLoopRealization P history :=
  ⟨realization⟩

namespace FinalLoopRealization

def toTotalLoop
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
  (realization : FinalLoopRealization P history) : P.TotalLoop :=
  realization.witness.toTotalLoop

def toContractedClosureDifference
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (realization : FinalLoopRealization P history) :
    ContractedClosureDifference P :=
  realization.witness.toContractedClosureDifference

def endpointEquality
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (realization : FinalLoopRealization P history) :
    P.leftEndpoint = P.rightEndpoint :=
  realization.toContractedClosureDifference.endpointContraction

end FinalLoopRealization

structure FinalIdentification
    (P : CircularPresentation)
    (history : RootedGeneratedHistory P) where
  witness : FinalLoopRealization P history

namespace FinalLoopRealization

def toFinalIdentification
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (realization : FinalLoopRealization P history) :
    FinalIdentification P history :=
  ⟨realization⟩

end FinalLoopRealization

namespace FinalIdentification

def toTotalLoop
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (identification : FinalIdentification P history) : P.TotalLoop :=
  identification.witness.toTotalLoop

def toContractedClosureDifference
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (identification : FinalIdentification P history) :
    ContractedClosureDifference P :=
  identification.witness.toContractedClosureDifference

def endpointEquality
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (identification : FinalIdentification P history) :
    P.leftEndpoint = P.rightEndpoint :=
  identification.witness.endpointEquality

end FinalIdentification

def refinementOutcome
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (refinement : CircularRefinement P history) :
    PLift (history = perimeterDeployment P) ⊕
      FinalJunctionRealization P history := by
  cases History.appendRootOrPositive
      (perimeterHistory P) refinement.continuation with
  | inl rootData =>
      rcases rootData with ⟨endpointEquality, continuationEquality⟩
      apply Sum.inl
      exact ⟨rootedGeneratedHistory_ext endpointEquality.down
        ((heq_of_eq refinement.recompose.symm).trans
          continuationEquality.down)⟩
  | inr positiveData =>
      rcases positiveData with ⟨positive, continuationEquality⟩
      let positiveContinuation : PositiveContinuation refinement.extension :=
        { path := positive
          historyExact := continuationEquality.down }
      let boundary :=
        finalBoundaryOccurrence refinement.toLabelled positiveContinuation
      let interpretation := finalClosureInterpretation boundary
      exact .inr
        { interpretation := interpretation
          attempt := refinement.realizesFinal positiveContinuation }

def rejectFinalJunctionRealization
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (realization : FinalJunctionRealization P history) : False :=
  realization.attempt.rejectExplicit

def rejectFinalJunctionRealizationImplicit
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (realization : FinalJunctionRealization P history) : False :=
  realization.attempt.rejectImplicit

def rejectFinalLoopRealization
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (realization : FinalLoopRealization P history) : False :=
  rejectFinalJunctionRealization realization.witness

def rejectFinalIdentification
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (identification : FinalIdentification P history) : False :=
  rejectFinalLoopRealization identification.witness

/- A positive circular boundary context keeps the faithful segmented
   extension and the positive free continuation in the same dependent
   object.  No totalization is present at this level. -/
structure CircularResidualBoundaryContext
    (P : CircularPresentation)
    (history : RootedGeneratedHistory P) where
  labelled : FaithfullyLabelledPerimeterExtension P history
  positive : PositiveContinuation labelled.extension

def circularBoundaryNewOccurrence
    (P : CircularPresentation)
    {history : RootedGeneratedHistory P}
    (context : CircularResidualBoundaryContext P history) : Type _ :=
  History.Occurrence context.labelled.continuation

def circularBoundaryCombinedOccurrence
    (P : CircularPresentation)
    {history : RootedGeneratedHistory P}
    (_context : CircularResidualBoundaryContext P history) : Type _ :=
  History.Occurrence history.history

def circularPositiveResidualBoundary
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (refinement : CircularRefinement P history)
    (positive : PositiveContinuation refinement.extension) :
    AbstractSegmentedTurning.PositiveResidualBoundary
      (perimetralBoundaryGenerator P)
      (CircularResidualBoundaryContext P)
      (circularBoundaryNewOccurrence P)
      (circularBoundaryCombinedOccurrence P)
      (NonClosingPosition P.perimeter)
      (FinalRequirement P)
      (History.Occurrence (perimeterHistory P))
      (perimeterInternalRoleRealization P)
      (finalRequirementContractible P)
      history :=
  { context :=
      { labelled := refinement.toLabelled
        positive := positive }
    strict :=
      { continuation := positive.path
        historyExact := by
          change History.append (perimeterHistory P)
            positive.path.toHistory = history.history
          rw [← positive.historyExact]
          exact refinement.recompose }
    extension := refinement.toLabelled.toSegmentedResidualExtension
    positive :=
      { occurrence :=
          transportOccurrence positive.historyExact.symm
            positive.path.lastOccurrence } }

def analyzeCircularRefinementThroughResidual
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (refinement : CircularRefinement P history) :
    PLift (history = perimeterDeployment P) ⊕
      AbstractSegmentedTurning.PositiveResidualBoundary
        (perimetralBoundaryGenerator P)
        (CircularResidualBoundaryContext P)
        (circularBoundaryNewOccurrence P)
        (circularBoundaryCombinedOccurrence P)
        (NonClosingPosition P.perimeter)
        (FinalRequirement P)
        (History.Occurrence (perimeterHistory P))
        (perimeterInternalRoleRealization P)
        (finalRequirementContractible P)
        history := by
  cases History.appendRootOrPositive
      (perimeterHistory P) refinement.continuation with
  | inl rootData =>
      rcases rootData with ⟨endpointEquality, continuationEquality⟩
      apply Sum.inl
      exact ⟨rootedGeneratedHistory_ext endpointEquality.down
        ((heq_of_eq refinement.recompose.symm).trans
          continuationEquality.down)⟩
  | inr positiveData =>
      rcases positiveData with ⟨positive, continuationEquality⟩
      let positiveContinuation : PositiveContinuation refinement.extension :=
        { path := positive
          historyExact := continuationEquality.down }
      exact .inr
        (circularPositiveResidualBoundary refinement positiveContinuation)

/- The circular interpretation retains the boundary built from the unique
   residual occurrence and relates it to the canonical final-boundary view
   on which bilateral closure is attempted.  Thus the residual occurrence
   is not discarded when closure semantics is introduced. -/
structure ResidualFinalClosureInterpretation
    (P : CircularPresentation)
    (history : RootedGeneratedHistory P) where
  context : CircularResidualBoundaryContext P history
  segmentedExtension : SegmentedResidualRole.FaithfulExtension
    (NonClosingPosition P.perimeter)
    (FinalRequirement P)
    (History.Occurrence (perimeterHistory P))
    (History.Occurrence context.labelled.continuation)
    (History.Occurrence history.history)
    (perimeterInternalRoleRealization P)
    (finalRequirementContractible P)
  residualOccurrence : History.Occurrence context.labelled.continuation
  residualLabelIsFinal :
    segmentedExtension.label
        (segmentedExtension.embedNew residualOccurrence) =
      .inr (finalRequirementContractible P).center
  residualOccurrenceIsCanonical :
    residualOccurrence =
      transportOccurrence context.positive.historyExact.symm
        context.positive.path.lastOccurrence
  closure : FinalClosureInterpretation P history
  closureIsCanonical :
    closure =
      finalClosureInterpretation
        (finalBoundaryOccurrence context.labelled context.positive)
  residualOccurrenceIsClosureBoundary :
    context.labelled.newOccurrence residualOccurrence =
      closure.boundary.historyOccurrence

def interpretCircularResidual
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (boundary : AbstractSegmentedTurning.PositiveResidualBoundary
      (perimetralBoundaryGenerator P)
      (CircularResidualBoundaryContext P)
      (circularBoundaryNewOccurrence P)
      (circularBoundaryCombinedOccurrence P)
      (NonClosingPosition P.perimeter)
      (FinalRequirement P)
      (History.Occurrence (perimeterHistory P))
      (perimeterInternalRoleRealization P)
      (finalRequirementContractible P)
      history)
    (unique : SegmentedResidualRole.UniqueResidualOccurrence
      boundary.extension) :
    ResidualFinalClosureInterpretation P history :=
  let canonicalOccurrence :=
    transportOccurrence boundary.context.positive.historyExact.symm
      boundary.context.positive.path.lastOccurrence
  let canonicalBoundary :=
    finalBoundaryOccurrence boundary.context.labelled
      boundary.context.positive
  { context := boundary.context
    segmentedExtension := boundary.extension
    residualOccurrence := unique.occurrence
    residualLabelIsFinal := unique.labelIsResidual
    residualOccurrenceIsCanonical :=
      (unique.unique canonicalOccurrence).symm
    closure := finalClosureInterpretation canonicalBoundary
    closureIsCanonical := rfl
    residualOccurrenceIsClosureBoundary := by
      change boundary.context.labelled.newOccurrence unique.occurrence =
        boundary.context.labelled.newOccurrence canonicalOccurrence
      exact congrArg boundary.context.labelled.newOccurrence
        (unique.unique canonicalOccurrence).symm }

structure ResidualBilateralClosureAttempt
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (interpretation : ResidualFinalClosureInterpretation P history) where
  attempt : BilateralClosureAttemptAt interpretation.closure

theorem rejectResidualBilateralClosureAttempt
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (interpretation : ResidualFinalClosureInterpretation P history)
    (attempt : ResidualBilateralClosureAttempt interpretation) : False :=
  attempt.attempt.rejectExplicit

def circularResidualBranch
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (refinement : CircularRefinement P history)
    (positive : PositiveContinuation refinement.extension) :
    Σ boundary : AbstractSegmentedTurning.PositiveResidualBoundary
      (perimetralBoundaryGenerator P)
      (CircularResidualBoundaryContext P)
      (circularBoundaryNewOccurrence P)
      (circularBoundaryCombinedOccurrence P)
      (NonClosingPosition P.perimeter)
      (FinalRequirement P)
      (History.Occurrence (perimeterHistory P))
      (perimeterInternalRoleRealization P)
      (finalRequirementContractible P)
      history,
      ResidualBilateralClosureAttempt
        (interpretCircularResidual boundary
          boundary.uniqueResidualOccurrence) := by
  let boundary := circularPositiveResidualBoundary refinement positive
  refine ⟨boundary, ?_⟩
  refine ⟨?_⟩
  change BilateralClosureAttemptAt
    (finalClosureInterpretation
      (finalBoundaryOccurrence refinement.toLabelled positive))
  exact refinement.realizesFinal positive

def analyzeCircularRegimeWithResidualAttempt
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (refinement : CircularRefinement P history) :
    PLift (history = perimeterDeployment P) ⊕
      (Σ boundary : AbstractSegmentedTurning.PositiveResidualBoundary
        (perimetralBoundaryGenerator P)
        (CircularResidualBoundaryContext P)
        (circularBoundaryNewOccurrence P)
        (circularBoundaryCombinedOccurrence P)
        (NonClosingPosition P.perimeter)
        (FinalRequirement P)
        (History.Occurrence (perimeterHistory P))
        (perimeterInternalRoleRealization P)
        (finalRequirementContractible P)
        history,
        ResidualBilateralClosureAttempt
          (interpretCircularResidual boundary
            boundary.uniqueResidualOccurrence)) := by
  cases History.appendRootOrPositive
      (perimeterHistory P) refinement.continuation with
  | inl rootData =>
      rcases rootData with ⟨endpointEquality, continuationEquality⟩
      apply Sum.inl
      exact ⟨rootedGeneratedHistory_ext endpointEquality.down
        ((heq_of_eq refinement.recompose.symm).trans
          continuationEquality.down)⟩
  | inr positiveData =>
      rcases positiveData with ⟨positive, continuationEquality⟩
      let positiveContinuation : PositiveContinuation refinement.extension :=
        { path := positive
          historyExact := continuationEquality.down }
      exact .inr
        (circularResidualBranch refinement positiveContinuation)

/-! ## Direct core coupled circular regime

This is the production coupled path.  Its regime, interpretation, attempt,
and residual boundary are all core-level data; the historical rich regime is
not used to determine the residual occurrence. -/
def perimetralCoreCoupledRegime
    (P : CircularPresentation) :
    AbstractSegmentedTurning.CoreCoupledObstructedRegime
      (perimetralBoundaryGenerator P)
      (fun history => CoreCircularResidualContext P history)
      (fun {_history} context =>
        History.Occurrence context.extension.continuation)
      (NonClosingPosition P.perimeter)
      (FinalRequirement P)
      (finalRequirementContractible P) :=
  { Regime := CoreCircularRefinement P
    Interpretation := fun history => CoreResidualClosureInterpretation history
    Attempt := fun {history} interpretation =>
      CoreResidualClosureAttempt history interpretation
    canonicalRegime := identityCoreCircularRefinement P
    interpretResidual := fun boundary unique =>
      coreInterpretResidual boundary unique
    analyzeRegime := by
      intro candidate refinement
      cases History.appendRootOrPositive
          (perimeterHistory P) refinement.extension.continuation with
      | inl rootData =>
          rcases rootData with ⟨endpointEquality, continuationEquality⟩
          exact .inl ⟨rootedGeneratedHistory_ext endpointEquality.down
            ((heq_of_eq refinement.extension.recompose.symm).trans
              continuationEquality.down)⟩
      | inr positiveData =>
          rcases positiveData with ⟨positive, continuationEquality⟩
          let positiveContinuation : PositiveContinuation refinement.extension :=
            { path := positive
              historyExact := continuationEquality.down }
          rcases refinement.positiveBranch positiveContinuation with
            ⟨core, attempt⟩
          let boundary :=
            coreCircularPositiveResidualBoundary
              refinement.extension positiveContinuation core
          exact .inr ⟨boundary, attempt⟩
    rejectTotalization := by
      intro candidate interpretation attempt
      exact rejectCoreResidualClosureAttempt attempt }

theorem perimetralCoreCoupledInterpretation_occurrence
    (P : CircularPresentation)
    {history : RootedGeneratedHistory P}
    (boundary : coreCircularBoundaryType P history)
    (unique : SegmentedResidualRole.CoreUniqueResidualOccurrence
      boundary.core) :
    ((perimetralCoreCoupledRegime P).interpretResidual boundary unique).residualOccurrence =
      unique.occurrence := by
  rfl

def perimetralCoreObstructedRegime
    (P : CircularPresentation) :
    AbstractSegmentedTurning.ObstructedRegime
      (perimetralBoundaryGenerator P) :=
  (perimetralCoreCoupledRegime P).toObstructedRegime

def perimetralCoupledRegime
    (P : CircularPresentation) :
    AbstractSegmentedTurning.CoupledObstructedRegime
      (perimetralBoundaryGenerator P)
      (CircularResidualBoundaryContext P)
      (circularBoundaryNewOccurrence P)
      (circularBoundaryCombinedOccurrence P)
      (NonClosingPosition P.perimeter)
      (FinalRequirement P)
      (History.Occurrence (perimeterHistory P))
      (perimeterInternalRoleRealization P)
      (finalRequirementContractible P) :=
  { Regime := CircularRefinement P
    Interpretation := ResidualFinalClosureInterpretation P
    Attempt := ResidualBilateralClosureAttempt
    canonicalRegime := identityCircularRefinement P
    interpretResidual := interpretCircularResidual
    analyzeRegime := analyzeCircularRegimeWithResidualAttempt
    rejectTotalization := rejectResidualBilateralClosureAttempt }

/- A circular refinement has exactly the generic obstructed-regime shape:
   it is either the canonical perimeter or supplies a bilateral totalization
   attempt, and every such attempt is rejected. -/
def perimetralObstructedRegime
    (P : CircularPresentation) :
    AbstractSegmentedTurning.ObstructedRegime
      (perimetralBoundaryGenerator P) :=
  (perimetralCoupledRegime P).toObstructedRegime

def oneStepCoreTurning
    (P : CircularPresentation) :
    AbstractSegmentedTurning.CoreTurningConclusion
      (oneStepCoreSegmentedBoundary P)
      (perimetralCoreObstructedRegime P) :=
  AbstractSegmentedTurning.coreTurning
    (oneStepCoreSegmentedBoundary P)
    (perimetralCoreObstructedRegime P)

/- Reattach the direct core turning to the historical rich boundary type.  The
   occurrence and its uniqueness come from the core result; only the public
   rich label is checked at this boundary. -/
def oneStepCoreTurning_toPublic
    (P : CircularPresentation) :
    AbstractSegmentedTurning.TurningConclusion
      (oneStepSegmentedBoundary P)
      (perimetralCoreObstructedRegime P) :=
  let coreResult := oneStepCoreTurning P
  { uniqueResidualOccurrence :=
      { occurrence := coreResult.uniqueResidualOccurrence.occurrence
        labelIsResidual := by rfl
        unique := fun other =>
          coreResult.uniqueResidualOccurrence.unique other }
    exactRelativeClassification := coreResult.exactRelativeClassification
    generatedContinuation := coreResult.generatedContinuation
    continuationIsStrict := coreResult.continuationIsStrict
    continuationOutsideRegime := coreResult.continuationOutsideRegime
    noStrictRegimeExtension := coreResult.noStrictRegimeExtension
    totalizationRejected := coreResult.totalizationRejected }

def perimetralCoreCoupledTurning
    (P : CircularPresentation) :
    AbstractSegmentedTurning.CoreCoupledTurningConclusion
      (perimetralCoreCoupledRegime P) :=
  AbstractSegmentedTurning.coreCoupledTurning
    (perimetralCoreCoupledRegime P)

def historicalCoupledTurningOfCircularPresentation
    (P : CircularPresentation) :
    AbstractSegmentedTurning.CoupledTurningConclusion
      (perimetralCoupledRegime P) :=
  AbstractSegmentedTurning.coupledTurning (perimetralCoupledRegime P)

def coupledTurningOfCircularPresentation
    (P : CircularPresentation) :
    AbstractSegmentedTurning.CoreCoupledTurningConclusion
      (perimetralCoreCoupledRegime P) :=
  perimetralCoreCoupledTurning P

/- The historical rich turning remains available under an explicit name. -/
def historicalAbstractTurningOfCircularPresentation
    (P : CircularPresentation) :
    AbstractSegmentedTurning.TurningConclusion
      (oneStepSegmentedBoundary P)
      (perimetralObstructedRegime P) :=
  AbstractSegmentedTurning.abstractTurning
    (oneStepSegmentedBoundary P)
    (perimetralObstructedRegime P)

/- The whole circle-independent turning theorem is now instantiated by the
   direct core path, its residual occurrence, and its core obstructed regime. -/
def abstractTurningOfCircularPresentation
    (P : CircularPresentation) :
    AbstractSegmentedTurning.TurningConclusion
      (oneStepSegmentedBoundary P)
      (perimetralCoreObstructedRegime P) := by
  exact oneStepCoreTurning_toPublic P

theorem oneStepCoreResidualOccurrence_agrees_with_weak
    (P : CircularPresentation) :
    (oneStepCoreResidualOccurrence P).occurrence =
      (oneStepWeakResidualOccurrence P).occurrence :=
  rfl

theorem oneStepCoreResidualOccurrence_agrees_with_consumedTurning
    (P : CircularPresentation) :
    (oneStepCoreResidualOccurrence P).occurrence =
      ((abstractTurningOfCircularPresentation P).uniqueResidualOccurrence).occurrence :=
  rfl

/- The abstract turning consumes the same residual occurrence as the weak
   producer-facing construction.  This is a direct agreement with the
   published consumer, not an agreement between two new adapters. -/
theorem oneStepWeakResidualOccurrence_agrees_with_consumedTurning
    (P : CircularPresentation) :
    (oneStepWeakResidualOccurrence P).occurrence =
      (abstractTurningOfCircularPresentation P).uniqueResidualOccurrence.occurrence :=
  (oneStepCoreResidualOccurrence_agrees_with_weak P).symm.trans
    (oneStepCoreResidualOccurrence_agrees_with_consumedTurning P)

theorem noIntermediateRefinement
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (refinement : CircularRefinement P history) :
    history = perimeterDeployment P :=
  (historicalCoupledTurningOfCircularPresentation P).exactRelativeClassification
    |>.regimeImpliesEquality refinement

structure ExactCircularRefinementClassification
    (P : CircularPresentation)
    (history : RootedGeneratedHistory P) : Type _ where
  refinementImpliesEquality :
    CircularRefinement P history → history = perimeterDeployment P
  equalityBuildsRefinement :
    history = perimeterDeployment P → CircularRefinement P history

def exactCircularRefinementClassification
    (P : CircularPresentation)
    (history : RootedGeneratedHistory P) :
    ExactCircularRefinementClassification P history :=
  let classification :=
    (historicalCoupledTurningOfCircularPresentation P).exactRelativeClassification
  { refinementImpliesEquality :=
      classification.regimeImpliesEquality
    equalityBuildsRefinement :=
      classification.equalityBuildsRegime }

theorem oneStepAfterPerimeter_notCircularRefinement
    (P : CircularPresentation) :
    CircularRefinement P (oneStepAfterPerimeter P) → False :=
  (historicalCoupledTurningOfCircularPresentation P).continuationOutsideRegime

def strictRefinementProducesFinalJunctionRealization
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (strict : StrictConstitutivePrefix (perimeterDeployment P) history)
    (refinement : CircularRefinement P history) :
    FinalJunctionRealization P history := by
  cases refinementOutcome refinement with
  | inl equality => exact False.elim (strictPrefix_ne strict equality.down)
  | inr realization => exact realization

def strictRefinementProducesFinalLoopRealization
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (strict : StrictConstitutivePrefix (perimeterDeployment P) history)
    (refinement : CircularRefinement P history) :
    FinalLoopRealization P history :=
  FinalJunctionRealization.toFinalLoopRealization
    (strictRefinementProducesFinalJunctionRealization strict refinement)

def strictRefinementProducesFinalIdentification
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (strict : StrictConstitutivePrefix (perimeterDeployment P) history)
    (refinement : CircularRefinement P history) :
    FinalIdentification P history :=
  (strictRefinementProducesFinalLoopRealization strict refinement).toFinalIdentification

def strictRefinementProducesTotalLoop
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (strict : StrictConstitutivePrefix (perimeterDeployment P) history)
    (refinement : CircularRefinement P history) : P.TotalLoop :=
  (strictRefinementProducesFinalLoopRealization strict refinement).toTotalLoop

/- Soundness of the circular regime relative to the independent specification:
   the regime's perimeter extension supplies local exactness, while strict
   refinement closure supplies the trajectory obligation. -/
def circularRefinement_soundSpecification
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (refinement : CircularRefinement P history) :
    CircularSpecificationSatisfaction P history :=
  { «local» :=
      refinement.extension.toExactNonClosingRealization
    trajectory :=
      fun strict =>
        strictRefinementProducesTotalLoop strict refinement }

theorem noStrictSamePerimeterExtension
    (P : CircularPresentation) :
    (Σ history : RootedGeneratedHistory P,
      StrictConstitutivePrefix (perimeterDeployment P) history ×
        CircularRefinement P history) → False :=
  (historicalCoupledTurningOfCircularPresentation P).noStrictRegimeExtension

inductive PerimetrallyAdmissible
    (P : CircularPresentation) : RootedGeneratedHistory P → Type _
  | properPartial
      {history : RootedGeneratedHistory P} :
      FreePartialRealization P history → PerimetrallyAdmissible P history
  | samePerimeter
      {history : RootedGeneratedHistory P} :
      CircularRefinement P history → PerimetrallyAdmissible P history

def admissible_is_prefix_of_perimeter
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P} :
    PerimetrallyAdmissible P history →
      ConstitutivePrefix history (perimeterDeployment P)
  | .properPartial partialPath => partial_is_prefix_of_perimeter partialPath
  | .samePerimeter refinement => by
      cases noIntermediateRefinement refinement
      exact prefixReflexive _

structure StrongPerimetralTurningCertificate
    (P : CircularPresentation) where
  initialClosureObstruction : PositiveClosureObstruction P
  initialClosureObstructionIsCanonical :
    initialClosureObstruction = P.positiveClosureObstruction
  engender :
    (source : PositiveConstitution P) →
      Σ target : PositiveConstitution P, GeneratedStep source target
  obstructionTransportedByEveryStep :
    {source target : PositiveConstitution P} →
      (step : GeneratedStep source target) →
        target.2.1.1.inheritedClosureObstruction =
          source.2.1.1.inheritedClosureObstruction
  deployment : RootedGeneratedHistory P
  generatedOnly : GeneratedOnlyByFreeConstruction deployment
  terminalClosureObstructionIsInitial :
    deployment.terminalClosureObstruction = P.positiveClosureObstruction
  exactPerimeter : ExactPerimeterRealization P deployment
  absorbsPartial :
    {history : RootedGeneratedHistory P} →
      FreePartialRealization P history → ConstitutivePrefix history deployment
  noIntermediate :
    {history : RootedGeneratedHistory P} →
      CircularRefinement P history → history = deployment
  rejectsExplicitTotalization : ExplicitTotalization P → False
  rejectsImplicitTotalization : ImplicitTotalization P → False
  rejectsFinalJunction :
    {history : RootedGeneratedHistory P} →
      FinalJunctionRealization P history → False
  rejectsFinalJunctionImplicit :
    {history : RootedGeneratedHistory P} →
      FinalJunctionRealization P history → False
  finalBoundaryFromPositive :
    {history : RootedGeneratedHistory P} →
    (labelled : FaithfullyLabelledPerimeterExtension P history) →
    (positive : PositiveContinuation labelled.extension) →
      FinalBoundaryOccurrence P history
  finalInterpretationFromPositive :
    {history : RootedGeneratedHistory P} →
    (labelled : FaithfullyLabelledPerimeterExtension P history) →
    (positive : PositiveContinuation labelled.extension) →
      FinalClosureInterpretation P history
  rejectsExplicitAttemptAt :
    {history : RootedGeneratedHistory P} →
    {interpretation : FinalClosureInterpretation P history} →
      BilateralClosureAttemptAt interpretation → False
  rejectsImplicitAttemptAt :
    {history : RootedGeneratedHistory P} →
    {interpretation : FinalClosureInterpretation P history} →
      BilateralClosureAttemptAt interpretation → False
  noStrictSamePerimeter :
    (Σ history : RootedGeneratedHistory P,
      StrictConstitutivePrefix deployment history ×
        CircularRefinement P history) → False
  continuesFreelyBeyondPerimeter :
    Σ target : PositiveConstitution P,
      GeneratedStep deployment.endpoint target

def strongPerimetralTurning
    (P : CircularPresentation) : StrongPerimetralTurningCertificate P :=
  { initialClosureObstruction := P.positiveClosureObstruction
    initialClosureObstructionIsCanonical := rfl
    engender := generate
    obstructionTransportedByEveryStep :=
      GeneratedStep.inheritedClosureObstructionExact
    deployment := perimeterDeployment P
    generatedOnly := perimeterDeployment_generatedOnly P
    terminalClosureObstructionIsInitial :=
      RootedGeneratedHistory.terminalClosureObstruction_is_initial _
    exactPerimeter := perimeterRealization P
    absorbsPartial := partial_is_prefix_of_perimeter
    noIntermediate := noIntermediateRefinement
    rejectsExplicitTotalization := explicitTotalizationRejected
    rejectsImplicitTotalization := implicitTotalizationRejected
    rejectsFinalJunction := rejectFinalJunctionRealization
    rejectsFinalJunctionImplicit := rejectFinalJunctionRealizationImplicit
    finalBoundaryFromPositive := finalBoundaryOccurrence
    finalInterpretationFromPositive := fun labelled positive =>
      finalClosureInterpretation
        (finalBoundaryOccurrence labelled positive)
    rejectsExplicitAttemptAt := BilateralClosureAttemptAt.rejectExplicit
    rejectsImplicitAttemptAt := BilateralClosureAttemptAt.rejectImplicit
    noStrictSamePerimeter := noStrictSamePerimeterExtension P
    continuesFreelyBeyondPerimeter :=
      generate (perimeterDeployment P).endpoint }

/-! ## Derived structural length

`Nat` enters only here, after the constitutive boundary and its maximality have
already been proved.  It measures an already constituted history; it does not
generate either the perimeter or its deployment. -/

namespace History

def length
    {State : Type uA}
    {Step : State → State → Type uB}
    {source target : State} :
    History Step source target → Nat
  | .root => 0
  | .extend history _ => history.length + 1

@[simp] theorem length_root
    {State : Type uA}
    {Step : State → State → Type uB}
    {state : State} :
    length (.root : History Step state state) = 0 := rfl

@[simp] theorem length_extend
    {State : Type uA}
    {Step : State → State → Type uB}
    {source middle target : State}
    (history : History Step source middle)
    (step : Step middle target) :
    length (.extend history step) = length history + 1 := rfl

def length_append_exact
    {State : Type uA}
    {Step : State → State → Type uB}
    {source middle target : State}
    (firstHistory : History Step source middle)
    (continuation : History Step middle target) : PLift (
    length (append firstHistory continuation) =
      length firstHistory + length continuation) :=
  match continuation with
  | .root => ⟨rfl⟩
  | .extend previous step =>
      let inductionData := length_append_exact firstHistory previous
      ⟨(congrArg (fun value => value + 1) inductionData.down).trans
        (Nat.add_assoc _ _ 1)⟩

theorem length_append
    {State : Type uA}
    {Step : State → State → Type uB}
    {source middle target : State}
    (firstHistory : History Step source middle)
    (continuation : History Step middle target) :
    length (append firstHistory continuation) =
      length firstHistory + length continuation :=
  (length_append_exact firstHistory continuation).down

end History

private theorem self_le_add_right (left right : Nat) :
    left ≤ left + right := by
  induction right with
  | zero => exact Nat.le_refl left
  | succ right inductionHypothesis =>
      rw [Nat.add_succ]
      exact Nat.le.step inductionHypothesis

private theorem self_lt_add_positive
    (left right : Nat) :
    left < left + (right + 1) := by
  change Nat.succ left ≤ left + (right + 1)
  rw [← Nat.add_assoc]
  exact Nat.succ_le_succ (self_le_add_right left right)

theorem prefix_length_le
    {P : CircularPresentation}
    {first second : RootedGeneratedHistory P}
    (prefixWitness : ConstitutivePrefix first second) :
    first.history.length ≤ second.history.length := by
  rcases prefixWitness with ⟨continuation, equality⟩
  calc
    first.history.length ≤
        first.history.length + continuation.length :=
      self_le_add_right _ _
    _ = (History.append first.history continuation).length :=
      (History.length_append first.history continuation).symm
    _ = second.history.length := congrArg History.length equality

theorem strictPrefix_length_lt
    {P : CircularPresentation}
    {first second : RootedGeneratedHistory P}
    (strict : StrictConstitutivePrefix first second) :
    first.history.length < second.history.length := by
  rcases strict with ⟨continuation, equality⟩
  calc
    first.history.length <
        first.history.length +
          (continuation.priorHistory.length + 1) :=
      self_lt_add_positive _ _
    _ = first.history.length + continuation.toHistory.length := rfl
    _ = (History.append first.history continuation.toHistory).length :=
      (History.length_append first.history continuation.toHistory).symm
    _ = second.history.length := congrArg History.length equality

theorem partial_length_le_perimeter
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (partialPath : FreePartialRealization P history) :
    history.history.length ≤ (perimeterDeployment P).history.length :=
  prefix_length_le (partial_is_prefix_of_perimeter partialPath)

theorem admissible_length_le_perimeter
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (admissible : PerimetrallyAdmissible P history) :
    history.history.length ≤ (perimeterDeployment P).history.length :=
  prefix_length_le (admissible_is_prefix_of_perimeter admissible)

theorem samePerimeter_length_eq
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (refinement : CircularRefinement P history) :
    history.history.length = (perimeterDeployment P).history.length := by
  cases noIntermediateRefinement refinement
  rfl

theorem no_longer_samePerimeter
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (refinement : CircularRefinement P history) :
    ¬ (perimeterDeployment P).history.length < history.history.length := by
  rw [samePerimeter_length_eq refinement]
  exact Nat.lt_irrefl _

/-! ## Exact concrete interpretations

The concrete layer interprets the free generators pointwise.  Its path type is
inductive in its own right and stores no free history.  A free prefix together
with exact occurrence round trips is reconstructed from that derivation. -/

structure ConcreteContinuationAlgebra
    (P : CircularPresentation) where
  ConcreteState : Type uA
  ConcreteStep : ConcreteState → ConcreteState → Type uB
  stateAt : PositiveConstitution P → ConcreteState

  ConcreteExplicit : Type uC
  ConcreteImplicit : Type uD
  ConcreteCompatible : ConcreteImplicit → ConcreteExplicit → Type uE
  interpretExplicit : ReturnedExplicit P → ConcreteExplicit
  interpretImplicit : ReturnedImplicit P → ConcreteImplicit
  interpretCompatible :
    {implicit : ReturnedImplicit P} →
    {explicit : ReturnedExplicit P} →
    ReturnedCompatible P implicit explicit →
      ConcreteCompatible
        (interpretImplicit implicit) (interpretExplicit explicit)

  ConcreteDifference : Type uF
  ConcreteProvenance : ConcreteDifference → Type uG
  interpretDifference : ReturnedDifference P → ConcreteDifference
  interpretProvenance :
    {difference : ReturnedDifference P} →
    ReturnedProvenance P difference →
      ConcreteProvenance (interpretDifference difference)

  ConcreteIntegration : ConcreteDifference → Type uH
  ConcreteContinuation :
    ConcreteDifference → ConcreteDifference → Type uI
  ConcreteFreshBoundary :
    ConcreteDifference → ConcreteDifference → Type uJ
  ConcreteBoundaryRecord : Type uK
  boundaryRecordAt : PositiveConstitution P → ConcreteBoundaryRecord

  concreteStep :
    (source : PositiveConstitution P) →
      ConcreteStep (stateAt source) (stateAt (canonicalTarget source))
  explicitPoleStep :
    (source : PositiveConstitution P) →
      ConcreteStep (stateAt source) (stateAt (canonicalTarget source))
  implicitPoleStep :
    (source : PositiveConstitution P) →
      ConcreteStep (stateAt source) (stateAt (canonicalTarget source))
  differenceStep :
    (source : PositiveConstitution P) →
      ConcreteStep (stateAt source) (stateAt (canonicalTarget source))
  admissibleStep :
    (source : PositiveConstitution P) →
    CompatibleExplicitation P source.1 →
      ConcreteStep (stateAt source) (stateAt (canonicalTarget source))

  successorFormationExact :
    (source : PositiveConstitution P) →
      admissibleStep source (successorCompatibleExplicitation source.1) =
        concreteStep source
  compatibilityRealized :
    (source : PositiveConstitution P) →
      ConcreteCompatible
        (interpretImplicit (implicitRead source))
        (interpretExplicit (explicitRead (canonicalTarget source)))
  compatibilityRealizedExact :
    (source : PositiveConstitution P) →
      compatibilityRealized source =
        interpretCompatible (stepCompatibleAt source.1)
  differenceIntegrated :
    (source : PositiveConstitution P) →
      ConcreteIntegration
        (interpretDifference
          (boundaryDifferenceReadout source.2.2))
  provenancePreserved :
    (source : PositiveConstitution P) →
      ConcreteProvenance
        (interpretDifference
          (boundaryDifferenceReadout source.2.2))
  provenancePreservedExact :
    (source : PositiveConstitution P) →
      provenancePreserved source =
        interpretProvenance
          (boundaryProvenanceReadout source.2.2)
  differenceContinued :
    (source : PositiveConstitution P) →
      ConcreteContinuation
        (interpretDifference
          (boundaryDifferenceReadout source.2.2))
        (interpretDifference
          (boundaryDifferenceReadout (canonicalTarget source).2.2))
  boundaryFresh :
    (source : PositiveConstitution P) →
      ConcreteFreshBoundary
        (interpretDifference
          (boundaryDifferenceReadout source.2.2))
        (interpretDifference
          (boundaryDifferenceReadout (canonicalTarget source).2.2))
  boundaryRecordFresh :
    (source : PositiveConstitution P) →
      boundaryRecordAt (canonicalTarget source) ≠ boundaryRecordAt source

namespace ConcreteContinuationAlgebra

def formLayer
    {P : CircularPresentation}
    (A : ConcreteContinuationAlgebra P)
    (source : PositiveConstitution P) :
    FreeKAlgebra P source.1 :=
  { Carrier := A.ConcreteStep
      (A.stateAt source) (A.stateAt (canonicalTarget source))
    explicitPole := A.explicitPoleStep source
    implicitPole := A.implicitPoleStep source
    currentDifference := A.differenceStep source
    admissible := A.admissibleStep source }

theorem successor_fold_exact
    {P : CircularPresentation}
    (A : ConcreteContinuationAlgebra P)
    (source : PositiveConstitution P) :
    FreeKAtom.fold (A.formLayer source) (successorFormationTerm source) =
      A.concreteStep source :=
  A.successorFormationExact source

end ConcreteContinuationAlgebra

structure ConcreteStepAgreement
    {P : CircularPresentation}
    (A : ConcreteContinuationAlgebra P)
    (source : PositiveConstitution P) : Type _ where
  formedByFreeEliminator :
    FreeKAtom.fold (A.formLayer source) (successorFormationTerm source) =
      A.concreteStep source
  interpretsCompatibility :
    A.ConcreteCompatible
      (A.interpretImplicit (implicitRead source))
      (A.interpretExplicit (explicitRead (canonicalTarget source)))
  compatibilityIsExactImage :
    interpretsCompatibility =
      A.interpretCompatible (stepCompatibleAt source.1)
  integratesDifference :
    A.ConcreteIntegration
      (A.interpretDifference (boundaryDifferenceReadout source.2.2))
  preservesProvenance :
    A.ConcreteProvenance
      (A.interpretDifference (boundaryDifferenceReadout source.2.2))
  provenanceIsExactImage :
    preservesProvenance =
      A.interpretProvenance (boundaryProvenanceReadout source.2.2)
  continuesDifference :
    A.ConcreteContinuation
      (A.interpretDifference (boundaryDifferenceReadout source.2.2))
      (A.interpretDifference
        (boundaryDifferenceReadout (canonicalTarget source).2.2))
  distinguishesFreshBoundary :
    A.ConcreteFreshBoundary
      (A.interpretDifference (boundaryDifferenceReadout source.2.2))
      (A.interpretDifference
        (boundaryDifferenceReadout (canonicalTarget source).2.2))
  boundaryRecordIsFresh :
    A.boundaryRecordAt (canonicalTarget source) ≠ A.boundaryRecordAt source

def ConcreteContinuationAlgebra.stepAgreement
    {P : CircularPresentation}
    (A : ConcreteContinuationAlgebra P)
    (source : PositiveConstitution P) :
    ConcreteStepAgreement A source :=
  { formedByFreeEliminator := A.successor_fold_exact source
    interpretsCompatibility := A.compatibilityRealized source
    compatibilityIsExactImage := A.compatibilityRealizedExact source
    integratesDifference := A.differenceIntegrated source
    preservesProvenance := A.provenancePreserved source
    provenanceIsExactImage := A.provenancePreservedExact source
    continuesDifference := A.differenceContinued source
    distinguishesFreshBoundary := A.boundaryFresh source
    boundaryRecordIsFresh := A.boundaryRecordFresh source }

def ConcreteContinuationAlgebra.realizeHistory
    {P : CircularPresentation}
    (A : ConcreteContinuationAlgebra P)
    {source target : PositiveConstitution P} :
    GeneratedHistory source target →
      History A.ConcreteStep (A.stateAt source) (A.stateAt target)
  | .root => .root
  | .extend history step => by
      cases step.formedByFreeLayer
      exact .extend (A.realizeHistory history) (A.concreteStep _)

def concreteForwardOccurrence
    {P : CircularPresentation}
    (A : ConcreteContinuationAlgebra P)
    {source target : PositiveConstitution P}
    (history : GeneratedHistory source target) :
    History.Occurrence history →
      History.Occurrence (A.realizeHistory history) :=
  match history with
  | .root => fun occurrence => nomatch occurrence
  | .extend previous step => by
      cases step.formedByFreeLayer
      intro occurrence
      cases occurrence with
      | last => exact .last
      | earlier earlier =>
          exact .earlier (concreteForwardOccurrence A previous earlier)

def concreteBackwardOccurrence
    {P : CircularPresentation}
    (A : ConcreteContinuationAlgebra P)
    {source target : PositiveConstitution P}
    (history : GeneratedHistory source target) :
    History.Occurrence (A.realizeHistory history) →
      History.Occurrence history :=
  match history with
  | .root => fun occurrence => nomatch occurrence
  | .extend previous step => by
      cases step.formedByFreeLayer
      intro occurrence
      cases occurrence with
      | last => exact .last
      | earlier earlier =>
          exact .earlier (concreteBackwardOccurrence A previous earlier)

theorem concreteBackwardForward
    {P : CircularPresentation}
    (A : ConcreteContinuationAlgebra P)
    {source target : PositiveConstitution P}
    (history : GeneratedHistory source target)
    (occurrence : History.Occurrence history) :
    concreteBackwardOccurrence A history
      (concreteForwardOccurrence A history occurrence) = occurrence := by
  induction history with
  | root => cases occurrence
  | extend history step inductionHypothesis =>
      cases step.formedByFreeLayer
      cases occurrence with
      | last => rfl
      | earlier earlier =>
          exact congrArg History.Occurrence.earlier
            (inductionHypothesis earlier)

theorem concreteForwardBackward
    {P : CircularPresentation}
    (A : ConcreteContinuationAlgebra P)
    {source target : PositiveConstitution P}
    (history : GeneratedHistory source target)
    (occurrence : History.Occurrence (A.realizeHistory history)) :
    concreteForwardOccurrence A history
      (concreteBackwardOccurrence A history occurrence) = occurrence := by
  induction history with
  | root => cases occurrence
  | extend history step inductionHypothesis =>
      cases step.formedByFreeLayer
      cases occurrence with
      | last => rfl
      | earlier earlier =>
          exact congrArg History.Occurrence.earlier
            (inductionHypothesis earlier)

structure ConcreteOccurrenceAgreement
    {P : CircularPresentation}
    (A : ConcreteContinuationAlgebra P)
    {source target : PositiveConstitution P}
    {freeHistory : GeneratedHistory source target}
    {concreteHistory :
      History A.ConcreteStep (A.stateAt source) (A.stateAt target)}
    (freeOccurrence : History.Occurrence freeHistory)
    (concreteOccurrence : History.Occurrence concreteHistory) : Type _ where
  sourceExact :
    concreteOccurrence.locatedStep.source =
      A.stateAt freeOccurrence.locatedStep.source
  targetExact :
    concreteOccurrence.locatedStep.target =
      A.stateAt freeOccurrence.locatedStep.target
  stepExact :
    HEq concreteOccurrence.locatedStep.step
      (A.concreteStep freeOccurrence.locatedStep.source)
  interpretedStep : ConcreteStepAgreement A freeOccurrence.locatedStep.source

def concreteOccurrenceAgreement
    {P : CircularPresentation}
    (A : ConcreteContinuationAlgebra P)
    {source : PositiveConstitution P} :
    {target : PositiveConstitution P} →
    (history : GeneratedHistory source target) →
    (occurrence : History.Occurrence history) →
      ConcreteOccurrenceAgreement A occurrence
        (concreteForwardOccurrence A history occurrence)
  | _, .root, occurrence => nomatch occurrence
  | _, .extend previous step, .last => by
      cases step.formedByFreeLayer
      exact
        { sourceExact := rfl
          targetExact := rfl
          stepExact := HEq.rfl
          interpretedStep := A.stepAgreement _ }
  | _, .extend previous step, .earlier earlier => by
      cases step.formedByFreeLayer
      let prior := concreteOccurrenceAgreement A previous earlier
      exact
        { sourceExact := prior.sourceExact
          targetExact := prior.targetExact
          stepExact := prior.stepExact
          interpretedStep := prior.interpretedStep }

structure ExactHistoryInterpretation
    {P : CircularPresentation}
    (A : ConcreteContinuationAlgebra P)
    {source target : PositiveConstitution P}
    (freeHistory : GeneratedHistory source target)
    (concreteHistory :
      History A.ConcreteStep (A.stateAt source) (A.stateAt target)) : Type _ where
  forwardOccurrence :
    History.Occurrence freeHistory → History.Occurrence concreteHistory
  backwardOccurrence :
    History.Occurrence concreteHistory → History.Occurrence freeHistory
  forwardBackward :
    (occurrence : History.Occurrence freeHistory) →
      backwardOccurrence (forwardOccurrence occurrence) = occurrence
  backwardForward :
    (occurrence : History.Occurrence concreteHistory) →
      forwardOccurrence (backwardOccurrence occurrence) = occurrence
  occurrenceAgreement :
    (occurrence : History.Occurrence freeHistory) →
      ConcreteOccurrenceAgreement A occurrence (forwardOccurrence occurrence)

namespace ExactHistoryInterpretation

/- Readouts transport contravariantly along the exact occurrence maps.  This
   is reindexing only: structural agreement belongs to the interpretation,
   while any semantic law of the values remains an independent obligation. -/
def pullbackReadout
    {P : CircularPresentation}
    {A : ConcreteContinuationAlgebra P}
    {source target : PositiveConstitution P}
    {freeHistory : GeneratedHistory source target}
    {concreteHistory :
      History A.ConcreteStep (A.stateAt source) (A.stateAt target)}
    (interpretation :
      ExactHistoryInterpretation A freeHistory concreteHistory)
    {Value : Type uV}
    (readout : History.OccurrenceReadout concreteHistory Value) :
    History.OccurrenceReadout freeHistory Value :=
  fun occurrence => readout (interpretation.forwardOccurrence occurrence)

def pushforwardReadout
    {P : CircularPresentation}
    {A : ConcreteContinuationAlgebra P}
    {source target : PositiveConstitution P}
    {freeHistory : GeneratedHistory source target}
    {concreteHistory :
      History A.ConcreteStep (A.stateAt source) (A.stateAt target)}
    (interpretation :
      ExactHistoryInterpretation A freeHistory concreteHistory)
    {Value : Type uV}
    (readout : History.OccurrenceReadout freeHistory Value) :
    History.OccurrenceReadout concreteHistory Value :=
  fun occurrence => readout (interpretation.backwardOccurrence occurrence)

theorem pullbackReadout_pushforwardReadout
    {P : CircularPresentation}
    {A : ConcreteContinuationAlgebra P}
    {source target : PositiveConstitution P}
    {freeHistory : GeneratedHistory source target}
    {concreteHistory :
      History A.ConcreteStep (A.stateAt source) (A.stateAt target)}
    (interpretation :
      ExactHistoryInterpretation A freeHistory concreteHistory)
    {Value : Type uV}
    (readout : History.OccurrenceReadout freeHistory Value)
    (occurrence : History.Occurrence freeHistory) :
    interpretation.pullbackReadout
        (interpretation.pushforwardReadout readout) occurrence =
      readout occurrence := by
  change readout
      (interpretation.backwardOccurrence
        (interpretation.forwardOccurrence occurrence)) = readout occurrence
  rw [interpretation.forwardBackward]

theorem pushforwardReadout_pullbackReadout
    {P : CircularPresentation}
    {A : ConcreteContinuationAlgebra P}
    {source target : PositiveConstitution P}
    {freeHistory : GeneratedHistory source target}
    {concreteHistory :
      History A.ConcreteStep (A.stateAt source) (A.stateAt target)}
    (interpretation :
      ExactHistoryInterpretation A freeHistory concreteHistory)
    {Value : Type uV}
    (readout : History.OccurrenceReadout concreteHistory Value)
    (occurrence : History.Occurrence concreteHistory) :
    interpretation.pushforwardReadout
        (interpretation.pullbackReadout readout) occurrence =
      readout occurrence := by
  change readout
      (interpretation.forwardOccurrence
        (interpretation.backwardOccurrence occurrence)) = readout occurrence
  rw [interpretation.backwardForward]

def transportConcreteHistory
    {P : CircularPresentation}
    {A : ConcreteContinuationAlgebra P}
    {source target : PositiveConstitution P}
    {freeHistory : GeneratedHistory source target}
    {first second :
      History A.ConcreteStep (A.stateAt source) (A.stateAt target)}
    (equality : first = second) :
    ExactHistoryInterpretation A freeHistory first →
      ExactHistoryInterpretation A freeHistory second := by
  cases equality
  exact id

theorem forwardOccurrence_injective
    {P : CircularPresentation}
    {A : ConcreteContinuationAlgebra P}
    {source target : PositiveConstitution P}
    {freeHistory : GeneratedHistory source target}
    {concreteHistory :
      History A.ConcreteStep (A.stateAt source) (A.stateAt target)}
    (interpretation :
      ExactHistoryInterpretation A freeHistory concreteHistory) :
    Function.Injective interpretation.forwardOccurrence := by
  intro first second equality
  have transported := congrArg interpretation.backwardOccurrence equality
  rw [interpretation.forwardBackward first,
    interpretation.forwardBackward second] at transported
  exact transported

theorem backwardOccurrence_injective
    {P : CircularPresentation}
    {A : ConcreteContinuationAlgebra P}
    {source target : PositiveConstitution P}
    {freeHistory : GeneratedHistory source target}
    {concreteHistory :
      History A.ConcreteStep (A.stateAt source) (A.stateAt target)}
    (interpretation :
      ExactHistoryInterpretation A freeHistory concreteHistory) :
    Function.Injective interpretation.backwardOccurrence := by
  intro first second equality
  have transported := congrArg interpretation.forwardOccurrence equality
  rw [interpretation.backwardForward first,
    interpretation.backwardForward second] at transported
  exact transported

end ExactHistoryInterpretation

def exactlyInterpretHistory
    {P : CircularPresentation}
    (A : ConcreteContinuationAlgebra P)
    {source target : PositiveConstitution P}
    (history : GeneratedHistory source target) :
    ExactHistoryInterpretation A history (A.realizeHistory history) :=
  { forwardOccurrence := concreteForwardOccurrence A history
    backwardOccurrence := concreteBackwardOccurrence A history
    forwardBackward := concreteBackwardForward A history
    backwardForward := concreteForwardBackward A history
    occurrenceAgreement := concreteOccurrenceAgreement A history }

/-! ## Typed regime-exit diagnostics

The exact concrete interpretation and the circular-refinement regime are kept
as distinct type families on the same rooted-history carrier. The perimetral
structures below compose the abstract diagnostic with the additional positive
witness explaining its geometric origin. -/

def ExactConcreteRealization
    {P : CircularPresentation}
    (A : ConcreteContinuationAlgebra P)
    (history : RootedGeneratedHistory P) : Type _ :=
  ExactHistoryInterpretation
    A history.history (A.realizeHistory history.history)

abbrev ConcreteRegimeExit
    (P : CircularPresentation)
    (A : ConcreteContinuationAlgebra P) : Type _ :=
  AbstractSegmentedTurning.RegimeExit
    (ExactConcreteRealization A) (CircularRefinement P)

structure PerimetralRegimeExit
    (P : CircularPresentation)
    (A : ConcreteContinuationAlgebra P) where
  exit : ConcreteRegimeExit P A
  extendsPerimeter :
    StrictConstitutivePrefix (perimeterDeployment P) exit.candidate

namespace PerimetralRegimeExit

def toRegimeExit
    {P : CircularPresentation}
    {A : ConcreteContinuationAlgebra P}
    (exit : PerimetralRegimeExit P A) :
    ConcreteRegimeExit P A :=
  exit.exit

end PerimetralRegimeExit

universe vA vB vC vF vG vH vJ

abbrev UniformConcreteRegimeExit
    (P : CircularPresentation.{uE, uI, uK, uD, uP, uEnd, uLoop}) :=
  AbstractSegmentedTurning.UniformRegimeExit
    (Carrier := RootedGeneratedHistory P)
    (ConcreteContinuationAlgebra.{uE, uI, uK, uD, vA, vB, vC, vF,
      vG, vH, vJ, uE, uI, uK, uD, uP, uEnd, uLoop} P)
    (fun (A : ConcreteContinuationAlgebra.{uE, uI, uK, uD, vA, vB, vC, vF,
      vG, vH, vJ, uE, uI, uK, uD, uP, uEnd, uLoop} P)
        (candidate : RootedGeneratedHistory P) =>
      ExactConcreteRealization A candidate)
    (CircularRefinement P)

structure UniformPerimetralRegimeExit
    (P : CircularPresentation.{uE, uI, uK, uD, uP, uEnd, uLoop}) where
  exit : UniformConcreteRegimeExit.{uE, uI, uK, uD, uP, uEnd, uLoop,
    vA, vB, vC, vF, vG, vH, vJ} P
  extendsPerimeter :
    StrictConstitutivePrefix (perimeterDeployment P) exit.candidate

namespace UniformPerimetralRegimeExit

def toUniformRegimeExit
    {P : CircularPresentation.{uE, uI, uK, uD, uP, uEnd, uLoop}}
    (exit : UniformPerimetralRegimeExit P) :
    UniformConcreteRegimeExit.{uE, uI, uK, uD, uP, uEnd, uLoop,
      vA, vB, vC, vF, vG, vH, vJ} P :=
  exit.exit

def atImplementation
    {P : CircularPresentation.{uE, uI, uK, uD, uP, uEnd, uLoop}}
    (exit : UniformPerimetralRegimeExit P)
    (A : ConcreteContinuationAlgebra.{uE, uI, uK, uD, vA, vB, vC, vF,
      vG, vH, vJ, uE, uI, uK, uD, uP, uEnd, uLoop} P) :
    PerimetralRegimeExit P A :=
  { exit :=
      { candidate := exit.exit.candidate
        faithful := exit.exit.faithful A
        inadmissible := exit.exit.inadmissible }
    extendsPerimeter := exit.extendsPerimeter }

@[simp] theorem at_forget
    {P : CircularPresentation.{uE, uI, uK, uD, uP, uEnd, uLoop}}
    (exit : UniformPerimetralRegimeExit P)
    (A : ConcreteContinuationAlgebra.{uE, uI, uK, uD, vA, vB, vC, vF,
      vG, vH, vJ, uE, uI, uK, uD, uP, uEnd, uLoop} P) :
    { candidate := exit.exit.candidate
      faithful := exit.exit.faithful A
      inadmissible := exit.exit.inadmissible } =
      (atImplementation exit A).toRegimeExit := by
  rfl

@[simp] theorem at_forget_named
    {P : CircularPresentation.{uE, uI, uK, uD, uP, uEnd, uLoop}}
    (exit : UniformPerimetralRegimeExit P)
    (A : ConcreteContinuationAlgebra.{uE, uI, uK, uD, vA, vB, vC, vF,
      vG, vH, vJ, uE, uI, uK, uD, uP, uEnd, uLoop} P) :
    AbstractSegmentedTurning.UniformRegimeExit.atImplementation
        (toUniformRegimeExit exit) A =
      PerimetralRegimeExit.toRegimeExit
        (atImplementation exit A) := by
  rfl

end UniformPerimetralRegimeExit

def oneStepUniformPerimetralRegimeExit
    (P : CircularPresentation.{uE, uI, uK, uD, uP, uEnd, uLoop}) :
    UniformPerimetralRegimeExit P :=
  { exit :=
      { candidate := oneStepAfterPerimeter P
        faithful := fun A =>
          exactlyInterpretHistory A (oneStepAfterPerimeter P).history
        inadmissible := oneStepAfterPerimeter_notCircularRefinement P }
    extendsPerimeter := oneStepAfterPerimeterStrict P }

def oneStepPerimetralRegimeExit
    (P : CircularPresentation.{uE, uI, uK, uD, uP, uEnd, uLoop})
    (A : ConcreteContinuationAlgebra.{uE, uI, uK, uD, vA, vB, vC, vF,
      vG, vH, vJ, uE, uI, uK, uD, uP, uEnd, uLoop} P) :
    PerimetralRegimeExit P A :=
  UniformPerimetralRegimeExit.atImplementation
    (oneStepUniformPerimetralRegimeExit P) A

def oneStepConcreteRegimeExit
    (P : CircularPresentation)
    (A : ConcreteContinuationAlgebra P) :
    ConcreteRegimeExit P A :=
  (oneStepPerimetralRegimeExit P A).toRegimeExit

/- A history-level alignment specification is a type-valued predicate on rooted
   generated histories.  This remains independent of any particular regime. -/
abbrev HistoryAlignmentSpec
    (P : CircularPresentation) :=
  RootedGeneratedHistory P → Type _

/- The first concrete normative-adequacy instance keeps the occurrence index
   required by the generic interface, while adequacy itself is global and
   constant along occurrences: regime membership and specification satisfaction
   imply each other on the same rooted-history carrier. -/
def circularNormativeAdequacy
    (P : CircularPresentation) :
    NormativeAdequacy P where
  AlignmentSpec := HistoryAlignmentSpec P
  RegimeAdequateAtOccurrence :=
    fun S R H _occurrence =>
      (R H → S H) × (S H → R H)

/- Soundness and regime completeness provide adequacy at every occurrence of
   the same history.  No occurrence projection is introduced. -/
def circularRefinement_adequateAlong
    (P : CircularPresentation)
    (history : RootedGeneratedHistory P) :
    AdequateAlong
      (circularNormativeAdequacy P)
      (CircularSpecificationSatisfaction P)
      (CircularRefinement P)
      history :=
  fun _occurrence =>
    ⟨circularRefinement_soundSpecification,
      circularSpecification_complete⟩

/- The canonical one-step regime exit becomes specification-relative by pairing
   the existing faithful concrete realization and regime rejection with the
   already established adequacy of the circular regime to the independent
   specification. -/
def oneStepSpecRelativeHistoryExit
    (P : CircularPresentation)
    (A : ConcreteContinuationAlgebra P) :
    SpecRelativeHistoryExit
      (circularNormativeAdequacy P)
      (CircularSpecificationSatisfaction P)
      (CircularRefinement P)
      (ExactConcreteRealization A) :=
  { exit := oneStepConcreteRegimeExit P A
    adequacy :=
      circularRefinement_adequateAlong P (oneStepAfterPerimeter P) }

/- The semantic failure of the candidate remains independent of the regime-exit
   rejection.  It is inherited directly from the autonomous specification. -/
theorem oneStepSpecRelativeHistoryExit_notSpecification
    (P : CircularPresentation)
    (A : ConcreteContinuationAlgebra P) :
    CircularSpecificationSatisfaction P
      (oneStepSpecRelativeHistoryExit P A).exit.candidate → False := by
  change
    CircularSpecificationSatisfaction P (oneStepAfterPerimeter P) → False
  exact oneStepAfterPerimeter_notSpecificationSatisfaction P

inductive ConcreteFaithfulPartialPath
    (P : CircularPresentation)
    (A : ConcreteContinuationAlgebra P) :
    {node : LocalNode
      P.Explicit P.Implicit P.Compatible P.Difference P.Provenance} →
    (remaining : PerimeterSpine P.Compatible node) →
    (data : FreeConstitution P (.within remaining)) →
    (difference : BoundaryDifference P data) →
    (history : History A.ConcreteStep
      (A.stateAt (initialPositive P))
      (A.stateAt (positiveAtRemaining P remaining data difference))) →
    Type _
  | root :
      ConcreteFaithfulPartialPath P A P.perimeter
        FreeConstitution.root BoundaryDifference.initial
        (.root : History A.ConcreteStep
          (A.stateAt (initialPositive P)) (A.stateAt (initialPositive P)))
  | advance
      {node nextNode : LocalNode
        P.Explicit P.Implicit P.Compatible P.Difference P.Provenance}
      {compatible : P.Compatible node.implicit nextNode.explicit}
      {tail : PerimeterSpine P.Compatible nextNode}
      {data : FreeConstitution P (.within (.advance compatible tail))}
      {difference : BoundaryDifference P data}
      {history : History A.ConcreteStep
        (A.stateAt (initialPositive P))
        (A.stateAt
          (positiveAtRemaining P (.advance compatible tail) data difference))} :
      ConcreteFaithfulPartialPath P A
        (.advance compatible tail) data difference history →
      ConcreteFaithfulPartialPath P A tail
        (canonicalTarget
          (positiveAtRemaining P (.advance compatible tail) data difference)).2.1
        (canonicalTarget
          (positiveAtRemaining P (.advance compatible tail) data difference)).2.2
        (.extend history
          (A.concreteStep
            (positiveAtRemaining P (.advance compatible tail) data difference)))

structure ReconstructedFaithfulPartialPath
    (P : CircularPresentation)
    (A : ConcreteContinuationAlgebra P)
    {node : LocalNode
      P.Explicit P.Implicit P.Compatible P.Difference P.Provenance}
    (remaining : PerimeterSpine P.Compatible node)
    (data : FreeConstitution P (.within remaining))
    (difference : BoundaryDifference P data)
    (history : History A.ConcreteStep
      (A.stateAt (initialPositive P))
      (A.stateAt (positiveAtRemaining P remaining data difference))) where
  freeHistory : GeneratedHistory (initialPositive P)
    (positiveAtRemaining P remaining data difference)
  freePartialPath : FreePartialPath P remaining data difference freeHistory
  historyExact : A.realizeHistory freeHistory = history

namespace ConcreteFaithfulPartialPath

def reconstruct
    {P : CircularPresentation}
    {A : ConcreteContinuationAlgebra P}
    {node : LocalNode
      P.Explicit P.Implicit P.Compatible P.Difference P.Provenance}
    {remaining : PerimeterSpine P.Compatible node}
    {data : FreeConstitution P (.within remaining)}
    {difference : BoundaryDifference P data}
    {history : History A.ConcreteStep
      (A.stateAt (initialPositive P))
      (A.stateAt (positiveAtRemaining P remaining data difference))} :
    ConcreteFaithfulPartialPath P A remaining data difference history →
      ReconstructedFaithfulPartialPath P A
        remaining data difference history
  | .root =>
      { freeHistory := .root
        freePartialPath := .root
        historyExact := rfl }
  | @advance _ _ node nextNode compatible tail data difference history previous =>
      let prior := reconstruct previous
      { freeHistory := .extend prior.freeHistory
          (generatedStepOfFreeK
            (positiveAtRemaining P (.advance compatible tail) data difference))
        freePartialPath := .advance prior.freePartialPath
        historyExact := by
          change History.extend
            (A.realizeHistory prior.freeHistory) (A.concreteStep _) =
            History.extend history (A.concreteStep _)
          rw [prior.historyExact] }

end ConcreteFaithfulPartialPath

structure ConcreteFaithfulPartialRealization
    (P : CircularPresentation)
    (A : ConcreteContinuationAlgebra P) where
  node : LocalNode
    P.Explicit P.Implicit P.Compatible P.Difference P.Provenance
  remaining : PerimeterSpine P.Compatible node
  data : FreeConstitution P (.within remaining)
  difference : BoundaryDifference P data
  concreteHistory : History A.ConcreteStep
    (A.stateAt (initialPositive P))
    (A.stateAt (positiveAtRemaining P remaining data difference))
  derivation : ConcreteFaithfulPartialPath P A
    remaining data difference concreteHistory

structure FaithfulPartialInterpretation
    {P : CircularPresentation}
    (A : ConcreteContinuationAlgebra P)
    (concrete : ConcreteFaithfulPartialRealization P A) where
  history : RootedGeneratedHistory P
  freePartial : FreePartialRealization P history
  interpretedHistory : History A.ConcreteStep
    (A.stateAt (initialPositive P)) (A.stateAt history.endpoint)
  concreteHistoryExact : HEq interpretedHistory concrete.concreteHistory
  interpretation : ExactHistoryInterpretation A
    history.history interpretedHistory

def interpretEveryFaithfulPartialRealization
    {P : CircularPresentation}
    {A : ConcreteContinuationAlgebra P}
    (concrete : ConcreteFaithfulPartialRealization P A) :
    FaithfulPartialInterpretation A concrete := by
  let reconstructed := concrete.derivation.reconstruct
  let freeHistory := reconstructed.freeHistory
  let rooted : RootedGeneratedHistory P :=
    ⟨positiveAtRemaining P concrete.remaining concrete.data concrete.difference,
      freeHistory⟩
  exact
    { history := rooted
      freePartial := .ofPath reconstructed.freePartialPath
      interpretedHistory := A.realizeHistory freeHistory
      concreteHistoryExact := heq_of_eq reconstructed.historyExact
      interpretation := exactlyInterpretHistory A freeHistory }

/-! ## Autonomous non-vacuous instance -/

namespace Example

inductive Explicit where
  | first
  | second
  | third
  | fourth

inductive Implicit where
  | first
  | second
  | third
  | fourth

inductive Difference where
  | first
  | second
  | third
  | fourth

inductive Provenance : Difference → Type
  | first : Provenance .first
  | second : Provenance .second
  | third : Provenance .third
  | fourth : Provenance .fourth

inductive Compatible : Implicit → Explicit → Type
  | internalFirst : Compatible .first .first
  | internalSecond : Compatible .second .second
  | internalThird : Compatible .third .third
  | internalFourth : Compatible .fourth .fourth
  | firstToSecond : Compatible .first .second
  | secondToThird : Compatible .second .third
  | thirdToFourth : Compatible .third .fourth
  | fourthToFirst : Compatible .fourth .first

def firstNode :
    LocalNode Explicit Implicit Compatible Difference Provenance :=
  { explicit := .first
    implicit := .first
    difference := .first
    provenance := .first
    internallyCompatible := .internalFirst }

def secondNode :
    LocalNode Explicit Implicit Compatible Difference Provenance :=
  { explicit := .second
    implicit := .second
    difference := .second
    provenance := .second
    internallyCompatible := .internalSecond }

def thirdNode :
    LocalNode Explicit Implicit Compatible Difference Provenance :=
  { explicit := .third
    implicit := .third
    difference := .third
    provenance := .third
    internallyCompatible := .internalThird }

def fourthNode :
    LocalNode Explicit Implicit Compatible Difference Provenance :=
  { explicit := .fourth
    implicit := .fourth
    difference := .fourth
    provenance := .fourth
    internallyCompatible := .internalFourth }

def examplePerimeter : PerimeterSpine Compatible firstNode :=
  @PerimeterSpine.advance _ _ _ _ _ firstNode secondNode
    (.firstToSecond : Compatible .first .second)
    (@PerimeterSpine.advance _ _ _ _ _ secondNode thirdNode
      (.secondToThird : Compatible .second .third)
      (@PerimeterSpine.advance _ _ _ _ _ thirdNode fourthNode
        (.thirdToFourth : Compatible .third .fourth)
        (.boundary fourthNode)))

def examplePerimeterPositive : NonClosingPosition examplePerimeter := .here

def leftPole (_ : Difference) : Bool := false

def rightPole (_ : Difference) : Bool := true

def rejectFalseEqualsTrue : false = true → False := by
  intro equality
  cases equality

def examplePresentation : CircularPresentation :=
  { Explicit := Explicit
    Implicit := Implicit
    Compatible := Compatible
    Difference := Difference
    Provenance := Provenance
    initialNode := firstNode
    perimeter := examplePerimeter
    perimeterPositive := examplePerimeterPositive
    finalJunction := Compatible.fourthToFirst
    Endpoint := Bool
    leftEndpoint := false
    rightEndpoint := true
    leftPole := leftPole
    rightPole := rightPole
    initialLeftPole := rfl
    initialRightPole := rfl
    TotalLoop := PLift (false = true)
    closeFromIdentification := fun equality => ⟨equality⟩
    loopContractsInitialDifference := fun loop => loop.down
    rejectInitialContraction := fun _ equality => rejectFalseEqualsTrue equality }

/-! ### Experimental permutation separator -/

/- The three inhabited non-closing positions of `examplePerimeter`. -/
def exampleP1 :
    NonClosingPosition examplePresentation.perimeter :=
  .here

def exampleP2 :
    NonClosingPosition examplePresentation.perimeter :=
  .later .here

def exampleP3 :
    NonClosingPosition examplePresentation.perimeter :=
  .later (.later .here)

/- The carrier keeps the three canonical located steps but deliberately
   permutes the first two occurrences. -/
def permutedExampleTrace :
    SemanticTrace examplePresentation :=
  { steps :=
      [ positionLocatedStep examplePresentation
          FreeConstitution.root BoundaryDifference.initial exampleP2,
        positionLocatedStep examplePresentation
          FreeConstitution.root BoundaryDifference.initial exampleP1,
        positionLocatedStep examplePresentation
          FreeConstitution.root BoundaryDifference.initial exampleP3 ] }

private def permutedExampleRealize :
    NonClosingPosition examplePresentation.perimeter →
      permutedExampleTrace.Occurrence
  | .here => ⟨1, by decide⟩
  | .later .here => ⟨0, by decide⟩
  | .later (.later .here) => ⟨2, by decide⟩
  | .later (.later (.later impossible)) => nomatch impossible

private def permutedExampleDecode :
    permutedExampleTrace.Occurrence →
      NonClosingPosition examplePresentation.perimeter :=
  fun occurrence =>
    if occurrence.val = 0 then exampleP2
    else if occurrence.val = 1 then exampleP1
    else exampleP3

private theorem permutedExampleDecode_realize :
    (position : NonClosingPosition examplePresentation.perimeter) →
      permutedExampleDecode (permutedExampleRealize position) = position
  | .here => by
      change (if (1 : Nat) = 0 then exampleP2
        else if (1 : Nat) = 1 then exampleP1 else exampleP3) = exampleP1
      rfl
  | .later .here => by
      change (if (0 : Nat) = 0 then exampleP2
        else if (0 : Nat) = 1 then exampleP1 else exampleP3) = exampleP2
      rfl
  | .later (.later .here) => by
      change (if (2 : Nat) = 0 then exampleP2
        else if (2 : Nat) = 1 then exampleP1 else exampleP3) = exampleP3
      rfl
  | .later (.later (.later impossible)) => nomatch impossible

private theorem permutedExampleRealize_injective :
    Function.Injective permutedExampleRealize := by
  intro first second equality
  have decoded := congrArg permutedExampleDecode equality
  exact (permutedExampleDecode_realize first).symm.trans
    (decoded.trans (permutedExampleDecode_realize second))

private def permutedExampleAgreement :
    (position : NonClosingPosition examplePresentation.perimeter) →
      LocatedRequirementAgreement examplePresentation position
        (permutedExampleTrace.locatedStep
          (permutedExampleRealize position))
  | .here => ⟨rfl⟩
  | .later .here => ⟨rfl⟩
  | .later (.later .here) => ⟨rfl⟩
  | .later (.later (.later impossible)) => nomatch impossible

/- Exact and injective local realization survives the explicit permutation. -/
def permutedExampleRealization :
    SemanticExactNonClosingRealization
      examplePresentation permutedExampleTrace :=
  { realize := permutedExampleRealize
    realize_injective := permutedExampleRealize_injective
    agreement := permutedExampleAgreement }

@[simp] theorem permutedExample_realizes_p1_at_one :
    (permutedExampleRealization.realize exampleP1).val = 1 :=
  rfl

@[simp] theorem permutedExample_realizes_p2_at_zero :
    (permutedExampleRealization.realize exampleP2).val = 0 :=
  rfl

@[simp] theorem permutedExample_realizes_p3_at_two :
    (permutedExampleRealization.realize exampleP3).val = 2 :=
  rfl

theorem permutedExample_reverses_first_two :
    (permutedExampleRealization.realize exampleP2).val <
      (permutedExampleRealization.realize exampleP1).val := by
  change 0 < 1
  exact Nat.zero_lt_succ 0

def exampleP1_precedes_exampleP2 :
    NonClosingPrecedes
      examplePresentation.perimeter
      exampleP1
      exampleP2 :=
  .here_later .here

/- The explicit permutation is locally exact and injective, but it does not
   preserve the structural order of the first two perimeter requirements. -/
theorem permutedExample_not_order_preserved :
    ¬ SemanticOrderPreserved permutedExampleRealization := by
  intro preserved
  have forward :=
    preserved exampleP1 exampleP2 exampleP1_precedes_exampleP2
  change
    (permutedExampleRealization.realize exampleP1).val <
      (permutedExampleRealization.realize exampleP2).val
    at forward
  exact Nat.lt_asymm forward permutedExample_reverses_first_two

/-! ### Experimental interleaving separator -/

/- These two extra occurrences are genuine locally generated steps beyond the
   perimeter.  They are constructed without a `History`, so their insertion in
   the semantic trace does not reintroduce global composability. -/
def exampleExtra1Source :
    PositiveConstitution examplePresentation :=
  perimeterEndpoint examplePresentation

def exampleExtra1 :
    History.LocatedStep (@GeneratedStep examplePresentation) :=
  ⟨exampleExtra1Source,
    canonicalTarget exampleExtra1Source,
    generatedStepOfFreeK exampleExtra1Source⟩

def exampleExtra2Source :
    PositiveConstitution examplePresentation :=
  canonicalTarget exampleExtra1Source

def exampleExtra2 :
    History.LocatedStep (@GeneratedStep examplePresentation) :=
  ⟨exampleExtra2Source,
    canonicalTarget exampleExtra2Source,
    generatedStepOfFreeK exampleExtra2Source⟩

/- The required non-closing steps remain in canonical order while two genuine
   locally valid generated steps are interleaved between them. -/
def interleavedExampleTrace :
    SemanticTrace examplePresentation :=
  { steps :=
      [ positionLocatedStep examplePresentation
          FreeConstitution.root BoundaryDifference.initial exampleP1,
        exampleExtra1,
        positionLocatedStep examplePresentation
          FreeConstitution.root BoundaryDifference.initial exampleP2,
        exampleExtra2,
        positionLocatedStep examplePresentation
          FreeConstitution.root BoundaryDifference.initial exampleP3 ] }

private def interleavedExampleRealize :
    NonClosingPosition examplePresentation.perimeter →
      interleavedExampleTrace.Occurrence
  | .here => ⟨0, by decide⟩
  | .later .here => ⟨2, by decide⟩
  | .later (.later .here) => ⟨4, by decide⟩
  | .later (.later (.later impossible)) => nomatch impossible

private def interleavedExampleDecode :
    interleavedExampleTrace.Occurrence →
      NonClosingPosition examplePresentation.perimeter :=
  fun occurrence =>
    if occurrence.val = 0 then exampleP1
    else if occurrence.val = 2 then exampleP2
    else exampleP3

private theorem interleavedExampleDecode_realize :
    (position : NonClosingPosition examplePresentation.perimeter) →
      interleavedExampleDecode (interleavedExampleRealize position) = position
  | .here => by
      change (if (0 : Nat) = 0 then exampleP1
        else if (0 : Nat) = 2 then exampleP2 else exampleP3) = exampleP1
      rfl
  | .later .here => by
      change (if (2 : Nat) = 0 then exampleP1
        else if (2 : Nat) = 2 then exampleP2 else exampleP3) = exampleP2
      rfl
  | .later (.later .here) => by
      change (if (4 : Nat) = 0 then exampleP1
        else if (4 : Nat) = 2 then exampleP2 else exampleP3) = exampleP3
      rfl
  | .later (.later (.later impossible)) => nomatch impossible

private theorem interleavedExampleRealize_injective :
    Function.Injective interleavedExampleRealize := by
  intro first second equality
  have decoded := congrArg interleavedExampleDecode equality
  exact (interleavedExampleDecode_realize first).symm.trans
    (decoded.trans (interleavedExampleDecode_realize second))

private def interleavedExampleAgreement :
    (position : NonClosingPosition examplePresentation.perimeter) →
      LocatedRequirementAgreement examplePresentation position
        (interleavedExampleTrace.locatedStep
          (interleavedExampleRealize position))
  | .here => ⟨rfl⟩
  | .later .here => ⟨rfl⟩
  | .later (.later .here) => ⟨rfl⟩
  | .later (.later (.later impossible)) => nomatch impossible

/- Exact local realization survives the interleaving of two additional valid
   generated steps. -/
def interleavedExampleRealization :
    SemanticExactNonClosingRealization
      examplePresentation interleavedExampleTrace :=
  { realize := interleavedExampleRealize
    realize_injective := interleavedExampleRealize_injective
    agreement := interleavedExampleAgreement }

@[simp] theorem interleavedExample_realizes_p1_at_zero :
    (interleavedExampleRealization.realize exampleP1).val = 0 :=
  rfl

@[simp] theorem interleavedExample_realizes_p2_at_two :
    (interleavedExampleRealization.realize exampleP2).val = 2 :=
  rfl

@[simp] theorem interleavedExample_realizes_p3_at_four :
    (interleavedExampleRealization.realize exampleP3).val = 4 :=
  rfl

/- The interleaved realization preserves every structural precedence relation
   of the three non-closing requirements.  No contiguity condition is used. -/
def interleavedExample_order_preserved :
    SemanticOrderPreserved interleavedExampleRealization := by
  intro first second precedes
  cases precedes with
  | here_later position =>
      cases position with
      | here =>
          change 0 < 2
          exact Nat.zero_lt_succ 1
      | later position =>
          cases position with
          | here =>
              change 0 < 4
              exact Nat.zero_lt_succ 3
          | later impossible => nomatch impossible
  | later_later precedes =>
      cases precedes with
      | here_later position =>
          cases position with
          | here =>
              change 2 < 4
              exact Nat.succ_lt_succ
                (Nat.succ_lt_succ (Nat.zero_lt_succ 1))
          | later impossible => nomatch impossible
      | later_later precedes =>
          cases precedes with
          | here_later impossible => nomatch impossible
          | later_later deeper => cases deeper


def exampleP1_next_exampleP2 :
    NonClosingNext
      examplePresentation.perimeter
      exampleP1
      exampleP2 :=
  .here_next

def exampleP2_next_exampleP3 :
    NonClosingNext
      examplePresentation.perimeter
      exampleP2
      exampleP3 :=
  .later_next .here_next

/- The extra occurrences at indices 1 and 3 are positionally between the
   canonically adjacent required occurrences. -/
def interleavedExample_extra1_between :
    interleavedExampleTrace.Between
      (interleavedExampleRealization.realize exampleP1)
      (interleavedExampleRealization.realize exampleP2) := by
  refine ⟨⟨1, by decide⟩, ?_, ?_⟩
  · change 0 < 1
    exact Nat.zero_lt_succ 0
  · change 1 < 2
    exact Nat.succ_lt_succ (Nat.zero_lt_succ 0)

def interleavedExample_extra2_between :
    interleavedExampleTrace.Between
      (interleavedExampleRealization.realize exampleP2)
      (interleavedExampleRealization.realize exampleP3) := by
  refine ⟨⟨3, by decide⟩, ?_, ?_⟩
  · change 2 < 3
    exact Nat.succ_lt_succ
      (Nat.succ_lt_succ (Nat.zero_lt_succ 0))
  · change 3 < 4
    exact Nat.succ_lt_succ
      (Nat.succ_lt_succ
        (Nat.succ_lt_succ (Nat.zero_lt_succ 0)))

/- `extra1` may be positioned between p1 and p2, but it cannot be exactly an
   occurrence of a generated constitutive bridge between these canonically
   adjacent requirements. -/
theorem interleavedExample_no_effective_bridge_p1_p2 :
    EffectiveConstitutiveBridge
      interleavedExampleTrace
      (interleavedExampleRealization.realize exampleP1)
      (interleavedExampleRealization.realize exampleP2) → False := by
  intro effective
  exact effectiveBridge_between_empty_of_next
    interleavedExampleRealization
    exampleP1_next_exampleP2
    effective
    interleavedExample_extra1_between

/- Symmetrically, `extra2` cannot be exactly an occurrence of a generated
   constitutive bridge between p2 and p3. -/
theorem interleavedExample_no_effective_bridge_p2_p3 :
    EffectiveConstitutiveBridge
      interleavedExampleTrace
      (interleavedExampleRealization.realize exampleP2)
      (interleavedExampleRealization.realize exampleP3) → False := by
  intro effective
  exact effectiveBridge_between_empty_of_next
    interleavedExampleRealization
    exampleP2_next_exampleP3
    effective
    interleavedExample_extra2_between


def exampleCertificate :
    StrongPerimetralTurningCertificate examplePresentation :=
  strongPerimetralTurning examplePresentation

theorem exampleEndpointsSeparated : false ≠ true :=
  examplePresentation.endpointsSeparated

def examplePerimeterHasPositiveHistory :
    Σ continuation : History.Positive
      (@GeneratedStep examplePresentation)
      (initialPositive examplePresentation)
      (perimeterEndpoint examplePresentation),
      PLift (continuation.toHistory = perimeterHistory examplePresentation) :=
  perimeterDeployment_positive examplePresentation

theorem exampleNoIntermediate
    {history : RootedGeneratedHistory examplePresentation}
    (refinement : CircularRefinement examplePresentation history) :
    history = perimeterDeployment examplePresentation :=
  noIntermediateRefinement refinement

def exampleGeneratorContinuesBeyond :
    Σ target : PositiveConstitution examplePresentation,
      GeneratedStep (perimeterEndpoint examplePresentation) target :=
  generate_after_perimeter examplePresentation

def exampleBeyondHistory : RootedGeneratedHistory examplePresentation :=
  oneStepAfterPerimeter examplePresentation

def exampleBeyondStrict :
    StrictConstitutivePrefix
      (perimeterDeployment examplePresentation) exampleBeyondHistory :=
  oneStepAfterPerimeterStrict examplePresentation

theorem exampleBeyondIsNotSamePerimeter :
    CircularRefinement examplePresentation exampleBeyondHistory → False :=
  oneStepAfterPerimeter_notCircularRefinement examplePresentation

theorem exampleLengthExact :
    (perimeterHistory examplePresentation).length = 3 := rfl

theorem exampleNoLongerSamePerimeter
    {history : RootedGeneratedHistory examplePresentation}
    (refinement : CircularRefinement examplePresentation history) :
    ¬ 3 < history.history.length := by
  rw [← exampleLengthExact]
  exact no_longer_samePerimeter refinement

def exampleAfterPerimeterCursorIsBeyond :
    (exampleGeneratorContinuesBeyond.1).1 = .beyond .first :=
  generate_after_perimeter_is_beyond examplePresentation

def canonicalPositiveStep
    (source : PositiveConstitution examplePresentation) :
    History.Positive (@GeneratedStep examplePresentation)
      source (canonicalTarget source) :=
  ⟨source, .root, generatedStepOfFreeK source⟩

theorem canonicalTarget_ne_source
    (source : PositiveConstitution examplePresentation) :
    canonicalTarget source ≠ source := by
  intro equality
  exact positiveGeneratedHistory_source_ne_target
    (canonicalPositiveStep source) equality.symm

def exampleAfterFirst : PositiveConstitution examplePresentation :=
  canonicalTarget (initialPositive examplePresentation)

theorem exampleInitialObstructionStored :
    BoundaryDifferenceCode.inheritedClosureObstruction
        (FreeConstitution.root (P := examplePresentation)).1 =
      examplePresentation.positiveClosureObstruction :=
  rfl

theorem exampleAfterFirstObstructionPreserved :
    BoundaryDifferenceCode.inheritedClosureObstruction
        exampleAfterFirst.2.1.1 =
      BoundaryDifferenceCode.inheritedClosureObstruction
        (initialPositive examplePresentation).2.1.1 :=
  canonicalTarget_inheritedClosureObstruction_exact
    (initialPositive examplePresentation)

theorem exampleFormationConsumesInitialObstruction :
    FreeKCore.integratedClosureObstruction
        (canonicalFreeLayer
          (initialPositive examplePresentation)).core =
      BoundaryDifferenceCode.inheritedClosureObstruction
        (initialPositive examplePresentation).2.1.1 :=
  rfl

theorem exampleIntegratedProvenanceStored :
    FreeKCore.integratedProvenance
        (canonicalFreeLayer
          (initialPositive examplePresentation)).core =
      provenanceAtCursor
        (P := examplePresentation) (.within examplePerimeter) :=
  rfl

def exampleHistoricalFirstProvenancePreserved :
    HistoricalProvenanceRecord examplePresentation
      (initialPositive examplePresentation) exampleAfterFirst.2.1 :=
  canonicalSourceProvenanceInscribed (initialPositive examplePresentation)

theorem exampleHistoricalRecordReadsFirst :
    exampleHistoricalFirstProvenancePreserved.recordedProvenance =
      ReturnedProvenance.source Provenance.first :=
  rfl

theorem exampleCurrentTargetReadsSecond :
    boundaryProvenanceReadout exampleAfterFirst.2.2 =
      ReturnedProvenance.source Provenance.second :=
  rfl

def exampleRecoveredAfterFirst :
    RecoveredImmediateOrigin examplePresentation exampleAfterFirst.2.1 :=
  recoverImmediateOriginFromFormation
    (currentRecordInCanonicalTarget
      (initialPositive examplePresentation))

theorem exampleRecoveredAfterFirstReadsStoredProvenance :
    exampleRecoveredAfterFirst.provenance =
      ReturnedProvenance.source Provenance.first :=
  rfl

def exampleRawFinalJunctionCompatibility :
    FinalJunctionCompatibility examplePresentation :=
  examplePresentation.finalJunction

def exampleRawJunctionWithSeparatedEndpoints :
    RawJunctionWithSeparatedEndpoints examplePresentation :=
  { junction := exampleRawFinalJunctionCompatibility
    separated := exampleEndpointsSeparated }

def exampleOneStepFaithfulLabelling :
    FaithfulPerimeterLabelling examplePresentation exampleBeyondHistory
      (oneStepAfterPerimeter_is_extension examplePresentation) :=
  oneStepFaithfulLabelling examplePresentation

def examplePositiveContinuation :
    PositiveContinuation
      (oneStepAfterPerimeter_is_extension examplePresentation) :=
  oneStepAfterPerimeter_positiveContinuation examplePresentation

def exampleFinalBoundaryOccurrence :
    FinalBoundaryOccurrence examplePresentation exampleBeyondHistory :=
  finalBoundaryOccurrence
    (oneStepFaithfullyLabelledExtension examplePresentation)
    examplePositiveContinuation

def exampleFinalClosureInterpretation :
    FinalClosureInterpretation examplePresentation exampleBeyondHistory :=
  finalClosureInterpretation exampleFinalBoundaryOccurrence

theorem exampleActualFreeStep_source_is_fourth :
    implicitRead exampleFinalBoundaryOccurrence.source =
      ReturnedImplicit.source Implicit.fourth :=
  exampleFinalClosureInterpretation.actualFreeStep_source_is_terminalImplicit

theorem exampleActualFreeStep_target_is_beyondFirst :
    explicitRead exampleFinalBoundaryOccurrence.target =
      ReturnedExplicit.formed (.beyond .first) :=
  exampleFinalClosureInterpretation.actualFreeStep_target_is_freeExplicit

theorem exampleActualFreeStep_is_leaveBoundary :
    HEq exampleFinalBoundaryOccurrence.step.compatibility
      (ReturnedCompatible.leaveBoundary
        (P := examplePresentation) fourthNode) :=
  exampleFinalBoundaryOccurrence.compatibility_is_leaveBoundary

theorem exampleInvokedJunction_is_fourthToFirst :
    exampleFinalClosureInterpretation.junction = Compatible.fourthToFirst :=
  exampleFinalClosureInterpretation.junctionIsDistinguished

theorem exampleFinalObstruction_is_initial :
    exampleFinalClosureInterpretation.targetObstruction =
      examplePresentation.positiveClosureObstruction :=
  exampleFinalClosureInterpretation.targetObstructionIsInitial

theorem exampleFinalProvenance_is_origin :
    exampleFinalClosureInterpretation.provenanceRecord.recordedProvenance =
      boundaryProvenanceReadout exampleFinalBoundaryOccurrence.source.2.2 :=
  exampleFinalClosureInterpretation.provenanceRecord.recordedProvenance_is_origin

theorem exampleFinalFormationRecord_is_current :
    HEq exampleFinalClosureInterpretation.formationRecord
      (currentRecordInCanonicalTarget
        exampleFinalBoundaryOccurrence.source) :=
  (heq_of_eq
    exampleFinalClosureInterpretation.formationRecordIsStepExact).trans
      exampleFinalBoundaryOccurrence.step.currentFormationRecord_is_current

theorem exampleNoBilateralClosureAttemptAt :
    BilateralClosureAttemptAt exampleFinalClosureInterpretation → False :=
  BilateralClosureAttemptAt.rejectExplicit

theorem exampleNoImplicitBilateralClosureAttemptAt :
    BilateralClosureAttemptAt exampleFinalClosureInterpretation → False :=
  BilateralClosureAttemptAt.rejectImplicit

def exampleHistoricalFirstProvenancePreservedAfterSecond :
    HistoricalProvenanceRecord examplePresentation
      (initialPositive examplePresentation)
      (canonicalTarget exampleAfterFirst).2.1 :=
  preserveHistoricalProvenanceAlongStep
    (generatedStepOfFreeK exampleAfterFirst)
    exampleHistoricalFirstProvenancePreserved

theorem exampleHistoricalRecordAfterSecondStillReadsFirst :
    exampleHistoricalFirstProvenancePreservedAfterSecond.recordedProvenance =
      ReturnedProvenance.source Provenance.first :=
  rfl

def exampleSecondStepFreshFormation :
    FreshFormationRecord examplePresentation
      exampleAfterFirst (canonicalTarget exampleAfterFirst) :=
  positiveGeneratedHistory_hasFreshFormation
    (canonicalPositiveStep exampleAfterFirst)

theorem exampleFreshFormationRejectsPreviousRecord :
    exampleSecondStepFreshFormation.freshRecord ≠
      preserveFormationRecordAlongStep
        exampleSecondStepFreshFormation.lastStep
        (currentRecordInCanonicalTarget
          (initialPositive examplePresentation)) :=
  exampleSecondStepFreshFormation.notFromPredecessor _

def exampleConcreteAlgebra :
    ConcreteContinuationAlgebra.{0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0}
      examplePresentation :=
  { ConcreteState := PositiveConstitution examplePresentation
    ConcreteStep := @GeneratedStep examplePresentation
    stateAt := fun state => state
    ConcreteExplicit := ReturnedExplicit examplePresentation
    ConcreteImplicit := ReturnedImplicit examplePresentation
    ConcreteCompatible := ReturnedCompatible examplePresentation
    interpretExplicit := fun explicit => explicit
    interpretImplicit := fun implicit => implicit
    interpretCompatible := fun compatible => compatible
    ConcreteDifference := ReturnedDifference examplePresentation
    ConcreteProvenance := ReturnedProvenance examplePresentation
    interpretDifference := fun difference => difference
    interpretProvenance := fun provenance => provenance
    ConcreteIntegration := fun _ => PUnit
    ConcreteContinuation := fun _ _ => PUnit
    ConcreteFreshBoundary := fun _ _ => PUnit
    ConcreteBoundaryRecord := PositiveConstitution examplePresentation
    boundaryRecordAt := fun state => state
    concreteStep := generatedStepOfFreeK
    explicitPoleStep := generatedStepOfFreeK
    implicitPoleStep := generatedStepOfFreeK
    differenceStep := generatedStepOfFreeK
    admissibleStep := fun source _ => generatedStepOfFreeK source
    successorFormationExact := fun _ => rfl
    compatibilityRealized := fun source => stepCompatibleAt source.1
    compatibilityRealizedExact := fun _ => rfl
    differenceIntegrated := fun _ => ⟨⟩
    provenancePreserved := fun source =>
      boundaryProvenanceReadout source.2.2
    provenancePreservedExact := fun _ => rfl
    differenceContinued := fun _ => ⟨⟩
    boundaryFresh := fun _ => ⟨⟩
    boundaryRecordFresh := canonicalTarget_ne_source }

def exampleFirstTail : PerimeterSpine Compatible secondNode :=
  @PerimeterSpine.advance _ _ _ _ _ secondNode thirdNode
    (.secondToThird : Compatible .second .third)
    (@PerimeterSpine.advance _ _ _ _ _ thirdNode fourthNode
      (.thirdToFourth : Compatible .third .fourth)
      (.boundary fourthNode))

def exampleConcreteFirstPath :
    ConcreteFaithfulPartialPath examplePresentation exampleConcreteAlgebra
      exampleFirstTail
      (canonicalTarget (initialPositive examplePresentation)).2.1
      (canonicalTarget (initialPositive examplePresentation)).2.2
      (.extend .root
        (exampleConcreteAlgebra.concreteStep
          (initialPositive examplePresentation))) :=
  .advance .root

def exampleConcreteFirstRealization :
    ConcreteFaithfulPartialRealization
      examplePresentation exampleConcreteAlgebra :=
  { node := secondNode
    remaining := exampleFirstTail
    data := (canonicalTarget (initialPositive examplePresentation)).2.1
    difference := (canonicalTarget (initialPositive examplePresentation)).2.2
    concreteHistory :=
      .extend .root
        (exampleConcreteAlgebra.concreteStep
          (initialPositive examplePresentation))
    derivation := exampleConcreteFirstPath }

def exampleConcreteInterpretation :
    FaithfulPartialInterpretation exampleConcreteAlgebra
      exampleConcreteFirstRealization :=
  interpretEveryFaithfulPartialRealization exampleConcreteFirstRealization

end Example

end StrongPerimetralTurning

/- AXIOM_AUDIT_BEGIN -/
#print axioms StrongPerimetralTurning.CircularPresentation.rejectTotalLoop
#print axioms StrongPerimetralTurning.CircularPresentation.positiveClosureObstruction
#print axioms StrongPerimetralTurning.RawJunctionWithSeparatedEndpoints
#print axioms StrongPerimetralTurning.ExplicitTotalization.toContractionKernel
#print axioms StrongPerimetralTurning.ImplicitTotalization.toContractionKernel
#print axioms StrongPerimetralTurning.explicitKernelContractsClosureDifference
#print axioms StrongPerimetralTurning.implicitKernelContractsClosureDifference
#print axioms StrongPerimetralTurning.explicitContractionKernelRejected
#print axioms StrongPerimetralTurning.implicitContractionKernelRejected
#print axioms StrongPerimetralTurning.ContractedClosureDifference.endpointContraction
#print axioms StrongPerimetralTurning.ContractedClosureDifference.reject
#print axioms StrongPerimetralTurning.explicitTotalizationContractsClosureDifference
#print axioms StrongPerimetralTurning.implicitTotalizationContractsClosureDifference
#print axioms StrongPerimetralTurning.explicitTotalizationRejected
#print axioms StrongPerimetralTurning.implicitTotalizationRejected
#print axioms StrongPerimetralTurning.FreeConstitution.formed_boundaryCode_exact
#print axioms StrongPerimetralTurning.FreeConstitution.formed_core_exact
#print axioms StrongPerimetralTurning.FreeConstitution.root_inheritedClosureObstruction_exact
#print axioms StrongPerimetralTurning.FreeConstitution.formed_inheritedClosureObstruction_exact
#print axioms StrongPerimetralTurning.FreeConstitution.formed_integratedClosureObstruction_exact
#print axioms StrongPerimetralTurning.FreeConstitution.formed_integratedProvenance_exact
#print axioms StrongPerimetralTurning.canonicalTarget_inheritedClosureObstruction_exact
#print axioms StrongPerimetralTurning.generate
#print axioms StrongPerimetralTurning.canonicalFormationEliminator_exact
#print axioms StrongPerimetralTurning.formationEliminator_is_free_fold
#print axioms StrongPerimetralTurning.canonicalFreeLayer_is_free_elimination
#print axioms StrongPerimetralTurning.HistoricalProvenanceRecord
#print axioms StrongPerimetralTurning.HistoricalProvenanceRecord.ofIntegration
#print axioms StrongPerimetralTurning.HistoricalProvenanceRecord.recordedProvenance
#print axioms StrongPerimetralTurning.HistoricalProvenanceRecord.recordedProvenance_is_origin
#print axioms StrongPerimetralTurning.PreservesProvenance.inscribedInTarget
#print axioms StrongPerimetralTurning.PreservesProvenance.exactProvenance_is_origin
#print axioms StrongPerimetralTurning.canonicalSourceProvenanceInscribed
#print axioms StrongPerimetralTurning.recoverImmediateOriginFromFormation
#print axioms StrongPerimetralTurning.RecoveredImmediateOrigin.provenance
#print axioms StrongPerimetralTurning.GeneratedStep.compatibilityWitnessExact
#print axioms StrongPerimetralTurning.GeneratedStep.provenanceWitnessExact
#print axioms StrongPerimetralTurning.GeneratedStep.integratesClosureObstruction
#print axioms StrongPerimetralTurning.GeneratedStep.inheritedClosureObstructionExact
#print axioms StrongPerimetralTurning.GeneratedStep.sourceProvenanceInscribedInTarget
#print axioms StrongPerimetralTurning.GeneratedStep.currentFormationRecord
#print axioms StrongPerimetralTurning.GeneratedStep.rejectsAlternativeCompatibility
#print axioms StrongPerimetralTurning.GeneratedStep.rejectsAlternativeProvenance
#print axioms StrongPerimetralTurning.generatedHistory_preservesClosureObstruction
#print axioms StrongPerimetralTurning.preserveFormationRecordAlongHistory
#print axioms StrongPerimetralTurning.preserveHistoricalProvenanceAlongStep
#print axioms StrongPerimetralTurning.preserveHistoricalProvenanceAlongHistory
#print axioms StrongPerimetralTurning.positiveGeneratedHistory_hasFreshFormation
#print axioms StrongPerimetralTurning.FreshFormationRecord.notFromSource
#print axioms StrongPerimetralTurning.append_positive_ne
#print axioms StrongPerimetralTurning.positiveGeneratedHistory_source_ne_target
#print axioms StrongPerimetralTurning.positiveGeneratedHistory_cursorAdvance
#print axioms StrongPerimetralTurning.positiveCursorAdvance_irreflexive
#print axioms StrongPerimetralTurning.CursorFuture.irreflexive
#print axioms StrongPerimetralTurning.ProperSpineSuffix.irreflexive
#print axioms StrongPerimetralTurning.ProperFreeTail.irreflexive
#print axioms StrongPerimetralTurning.ProperStructuralDepth.irreflexive
#print axioms StrongPerimetralTurning.partial_is_prefix_of_perimeter
#print axioms StrongPerimetralTurning.rootedOccurrence_source_eq_of_cursor_eq
#print axioms StrongPerimetralTurning.RequirementOccurrenceAgreement.locatedStepExact
#print axioms StrongPerimetralTurning.RequirementOccurrenceAgreement.compatibilityTransport
#print axioms StrongPerimetralTurning.RequirementOccurrenceAgreement.provenanceWitnessExact
#print axioms StrongPerimetralTurning.History.embedLeftOccurrence_injective
#print axioms StrongPerimetralTurning.locatedStep_transportOccurrence
#print axioms StrongPerimetralTurning.PerimeterExtension.oldOccurrenceAgreement
#print axioms StrongPerimetralTurning.PerimeterExtension.oldOccurrence_injective
#print axioms StrongPerimetralTurning.PerimeterExtension.toExactNonClosingRealization
#print axioms StrongPerimetralTurning.identityCircularRefinement
#print axioms StrongPerimetralTurning.CoreCircularResidualContext
#print axioms StrongPerimetralTurning.coreCircularBoundaryType
#print axioms StrongPerimetralTurning.coreCircularPositiveResidualBoundary
#print axioms StrongPerimetralTurning.CoreResidualClosureInterpretation
#print axioms StrongPerimetralTurning.coreInterpretResidual
#print axioms StrongPerimetralTurning.CoreResidualClosureAttempt
#print axioms StrongPerimetralTurning.rejectCoreResidualClosureAttempt
#print axioms StrongPerimetralTurning.CoreCircularPositiveBranch
#print axioms StrongPerimetralTurning.CoreCircularRefinement
#print axioms StrongPerimetralTurning.identityCoreCircularRefinement
#print axioms StrongPerimetralTurning.CircularRefinement.toCoreCircularRefinement
#print axioms StrongPerimetralTurning.coreCircularRefinement_history_eq_perimeter
#print axioms StrongPerimetralTurning.circularRefinement_nonempty_iff_coreCircularRefinement_nonempty
#print axioms StrongPerimetralTurning.oneStepAfterPerimeter_is_extension
#print axioms StrongPerimetralTurning.oneStepResidualDeterminationCore
#print axioms StrongPerimetralTurning.oneStepCorePositive
#print axioms StrongPerimetralTurning.oneStepCoreResidualOccurrence
#print axioms StrongPerimetralTurning.oneStepCoreSegmentedBoundary
#print axioms StrongPerimetralTurning.oneStepAfterPerimeter_nonClosingRealization
#print axioms StrongPerimetralTurning.CircularClosureMeaning
#print axioms StrongPerimetralTurning.perimeterDeployment_closureMeaning
#print axioms StrongPerimetralTurning.oneStepAfterPerimeter_notClosureMeaning
#print axioms StrongPerimetralTurning.CircularSpecificationSatisfaction
#print axioms StrongPerimetralTurning.perimeterDeployment_specificationSatisfaction
#print axioms StrongPerimetralTurning.oneStepAfterPerimeter_notSpecificationSatisfaction
#print axioms StrongPerimetralTurning.oneStepAfterPerimeterStrict
#print axioms StrongPerimetralTurning.oneStepAfterPerimeter_ne
#print axioms StrongPerimetralTurning.perimetralBoundaryGenerator
#print axioms StrongPerimetralTurning.occurrenceToRequirement_toOccurrence
#print axioms StrongPerimetralTurning.requirementToOccurrence_toRequirement
#print axioms StrongPerimetralTurning.deployOccurrence_position_roundTrip
#print axioms StrongPerimetralTurning.classifyDeploymentOccurrence
#print axioms StrongPerimetralTurning.decodeDeploymentOccurrence
#print axioms StrongPerimetralTurning.deployPosition_occurrence_roundTrip
#print axioms StrongPerimetralTurning.deployPositionToOccurrence_injective
#print axioms StrongPerimetralTurning.requirementToOccurrence_injective
#print axioms StrongPerimetralTurning.ExactNonClosingRealization
#print axioms StrongPerimetralTurning.SemanticTrace
#print axioms StrongPerimetralTurning.SemanticTrace.locatedStep
#print axioms StrongPerimetralTurning.LocatedRequirementAgreement
#print axioms StrongPerimetralTurning.SemanticExactNonClosingRealization
#print axioms StrongPerimetralTurning.NonClosingPrecedes
#print axioms StrongPerimetralTurning.SemanticOrderPreserved
#print axioms StrongPerimetralTurning.perimeterRealization
#print axioms StrongPerimetralTurning.finalRequirementContractible
#print axioms StrongPerimetralTurning.perimeterInternalRoleRealization
#print axioms StrongPerimetralTurning.FaithfullyLabelledPerimeterExtension.toSegmentedResidualExtension
#print axioms StrongPerimetralTurning.FaithfullyLabelledPerimeterExtension.segmentedResidualExtension_embedOld_injective
#print axioms StrongPerimetralTurning.FaithfullyLabelledPerimeterExtension.newOccurrence_cannotReuseNonClosingRequirement
#print axioms StrongPerimetralTurning.FaithfullyLabelledPerimeterExtension.newOccurrence_label_is_final
#print axioms StrongPerimetralTurning.FaithfullyLabelledPerimeterExtension.continuation_occurrences_unique
#print axioms StrongPerimetralTurning.PositiveContinuation.toResidualPositive
#print axioms StrongPerimetralTurning.FaithfullyLabelledPerimeterExtension.reconstructedInternalCompletion
#print axioms StrongPerimetralTurning.FaithfullyLabelledPerimeterExtension.reconstructed_roleToOccurrence_agrees
#print axioms StrongPerimetralTurning.FaithfullyLabelledPerimeterExtension.reconstructed_occurrenceToRole_agrees
#print axioms StrongPerimetralTurning.oneStepSegmentedBoundary
#print axioms StrongPerimetralTurning.oneStepResidualPositive
#print axioms StrongPerimetralTurning.oneStepResidualPositive_agrees_with_segmentedBoundary
#print axioms StrongPerimetralTurning.oneStepReconstructedInternalCompletion
#print axioms StrongPerimetralTurning.oneStepReconstructedInternalRealization
#print axioms StrongPerimetralTurning.oneStepReconstructed_roleToOccurrence_agrees
#print axioms StrongPerimetralTurning.oneStepReconstructed_occurrenceToRole_agrees
#print axioms StrongPerimetralTurning.oneStepWeakResidualOccurrence
#print axioms StrongPerimetralTurning.oneStepPublicResidualOccurrence
#print axioms StrongPerimetralTurning.oneStepResidualOccurrence_agrees
#print axioms StrongPerimetralTurning.oneStepWeakResidualOccurrence_label_is_final
#print axioms StrongPerimetralTurning.oneStepWeakResidualOccurrence_unique
#print axioms StrongPerimetralTurning.positiveContinuation_exactlyOne
#print axioms StrongPerimetralTurning.finalBoundaryOccurrence
#print axioms StrongPerimetralTurning.FinalBoundaryOccurrence.compatibility_is_leaveBoundary
#print axioms StrongPerimetralTurning.finalClosureInterpretation
#print axioms StrongPerimetralTurning.FinalClosureInterpretation.sourceObstructionIsInitial
#print axioms StrongPerimetralTurning.ConstitutiveClosureAttachment.formationRecordIsStepExact
#print axioms StrongPerimetralTurning.ConstitutiveClosureAttachment.provenanceRecordIsStepExact
#print axioms StrongPerimetralTurning.ConstitutiveClosureAttachment.obstructionIsInitial
#print axioms StrongPerimetralTurning.BilateralClosureAttemptAt.explicitContraction
#print axioms StrongPerimetralTurning.BilateralClosureAttemptAt.implicitContraction
#print axioms StrongPerimetralTurning.BilateralClosureAttemptAt.rejectExplicit
#print axioms StrongPerimetralTurning.BilateralClosureAttemptAt.rejectImplicit
#print axioms StrongPerimetralTurning.refinementOutcome
#print axioms StrongPerimetralTurning.NormativeAdequacy
#print axioms StrongPerimetralTurning.AdequateAlong
#print axioms StrongPerimetralTurning.SpecRelativeHistoryExit
#print axioms StrongPerimetralTurning.RootedGeneratedHistory.terminalClosureObstruction
#print axioms StrongPerimetralTurning.RootedGeneratedHistory.terminalClosureObstruction_is_initial
#print axioms StrongPerimetralTurning.FinalJunctionRealization.toBilateralContractions
#print axioms StrongPerimetralTurning.FinalJunctionRealization.toExplicitContractedClosureDifference
#print axioms StrongPerimetralTurning.FinalJunctionRealization.toImplicitContractedClosureDifference
#print axioms StrongPerimetralTurning.FinalJunctionRealization.toContractedClosureDifference
#print axioms StrongPerimetralTurning.FinalJunctionRealization.endpointEquality
#print axioms StrongPerimetralTurning.FinalJunctionRealization.toTotalLoop
#print axioms StrongPerimetralTurning.rejectFinalJunctionRealization
#print axioms StrongPerimetralTurning.rejectFinalJunctionRealizationImplicit
#print axioms StrongPerimetralTurning.circularPositiveResidualBoundary
#print axioms StrongPerimetralTurning.analyzeCircularRefinementThroughResidual
#print axioms StrongPerimetralTurning.interpretCircularResidual
#print axioms StrongPerimetralTurning.circularResidualBranch
#print axioms StrongPerimetralTurning.rejectResidualBilateralClosureAttempt
#print axioms StrongPerimetralTurning.analyzeCircularRegimeWithResidualAttempt
#print axioms StrongPerimetralTurning.perimetralCoreCoupledRegime
#print axioms StrongPerimetralTurning.perimetralCoreCoupledInterpretation_occurrence
#print axioms StrongPerimetralTurning.perimetralCoreObstructedRegime
#print axioms StrongPerimetralTurning.perimetralCoupledRegime
#print axioms StrongPerimetralTurning.perimetralObstructedRegime
#print axioms StrongPerimetralTurning.oneStepCoreTurning
#print axioms StrongPerimetralTurning.oneStepCoreTurning_toPublic
#print axioms StrongPerimetralTurning.perimetralCoreCoupledTurning
#print axioms StrongPerimetralTurning.historicalCoupledTurningOfCircularPresentation
#print axioms StrongPerimetralTurning.coupledTurningOfCircularPresentation
#print axioms StrongPerimetralTurning.historicalAbstractTurningOfCircularPresentation
#print axioms StrongPerimetralTurning.abstractTurningOfCircularPresentation
#print axioms StrongPerimetralTurning.oneStepCoreResidualOccurrence_agrees_with_weak
#print axioms StrongPerimetralTurning.oneStepCoreResidualOccurrence_agrees_with_consumedTurning
#print axioms StrongPerimetralTurning.oneStepWeakResidualOccurrence_agrees_with_consumedTurning
#print axioms StrongPerimetralTurning.strictRefinementProducesFinalJunctionRealization
#print axioms StrongPerimetralTurning.FinalLoopRealization.endpointEquality
#print axioms StrongPerimetralTurning.FinalLoopRealization.toFinalIdentification
#print axioms StrongPerimetralTurning.strictRefinementProducesFinalLoopRealization
#print axioms StrongPerimetralTurning.rejectFinalLoopRealization
#print axioms StrongPerimetralTurning.CircularRefinement.newOccurrence_cannotReuseNonClosingRequirement
#print axioms StrongPerimetralTurning.strictRefinementProducesFinalIdentification
#print axioms StrongPerimetralTurning.strictRefinementProducesTotalLoop
#print axioms StrongPerimetralTurning.noIntermediateRefinement
#print axioms StrongPerimetralTurning.exactCircularRefinementClassification
#print axioms StrongPerimetralTurning.oneStepAfterPerimeter_notCircularRefinement
#print axioms StrongPerimetralTurning.noStrictSamePerimeterExtension
#print axioms StrongPerimetralTurning.admissible_is_prefix_of_perimeter
#print axioms StrongPerimetralTurning.strongPerimetralTurning
#print axioms StrongPerimetralTurning.partial_length_le_perimeter
#print axioms StrongPerimetralTurning.prefix_length_le
#print axioms StrongPerimetralTurning.History.length_append
#print axioms StrongPerimetralTurning.History.OccurrenceReadout
#print axioms StrongPerimetralTurning.perimeterReadout
#print axioms StrongPerimetralTurning.occurrenceReadoutOfPerimeter
#print axioms StrongPerimetralTurning.occurrenceReadoutOfPerimeter_perimeterReadout
#print axioms StrongPerimetralTurning.perimeterReadout_occurrenceReadoutOfPerimeter
#print axioms StrongPerimetralTurning.admissible_length_le_perimeter
#print axioms StrongPerimetralTurning.ConcreteContinuationAlgebra.realizeHistory
#print axioms StrongPerimetralTurning.concreteForwardOccurrence
#print axioms StrongPerimetralTurning.concreteBackwardOccurrence
#print axioms StrongPerimetralTurning.concreteOccurrenceAgreement
#print axioms StrongPerimetralTurning.exactlyInterpretHistory
#print axioms StrongPerimetralTurning.ExactHistoryInterpretation.forwardOccurrence_injective
#print axioms StrongPerimetralTurning.ExactHistoryInterpretation.pullbackReadout
#print axioms StrongPerimetralTurning.ExactHistoryInterpretation.pushforwardReadout
#print axioms StrongPerimetralTurning.ExactHistoryInterpretation.pullbackReadout_pushforwardReadout
#print axioms StrongPerimetralTurning.ExactHistoryInterpretation.pushforwardReadout_pullbackReadout
#print axioms StrongPerimetralTurning.ConcreteFaithfulPartialPath.reconstruct
#print axioms StrongPerimetralTurning.interpretEveryFaithfulPartialRealization
#print axioms StrongPerimetralTurning.Example.permutedExampleTrace
#print axioms StrongPerimetralTurning.Example.permutedExampleRealization
#print axioms StrongPerimetralTurning.Example.permutedExample_realizes_p1_at_one
#print axioms StrongPerimetralTurning.Example.permutedExample_realizes_p2_at_zero
#print axioms StrongPerimetralTurning.Example.permutedExample_realizes_p3_at_two
#print axioms StrongPerimetralTurning.Example.permutedExample_reverses_first_two
#print axioms StrongPerimetralTurning.Example.exampleP1_precedes_exampleP2
#print axioms StrongPerimetralTurning.Example.permutedExample_not_order_preserved
#print axioms StrongPerimetralTurning.Example.exampleExtra1Source
#print axioms StrongPerimetralTurning.Example.exampleExtra1
#print axioms StrongPerimetralTurning.Example.exampleExtra2Source
#print axioms StrongPerimetralTurning.Example.exampleExtra2
#print axioms StrongPerimetralTurning.Example.interleavedExampleTrace
#print axioms StrongPerimetralTurning.Example.interleavedExampleRealization
#print axioms StrongPerimetralTurning.Example.interleavedExample_realizes_p1_at_zero
#print axioms StrongPerimetralTurning.Example.interleavedExample_realizes_p2_at_two
#print axioms StrongPerimetralTurning.Example.interleavedExample_realizes_p3_at_four
#print axioms StrongPerimetralTurning.Example.interleavedExample_order_preserved
#print axioms StrongPerimetralTurning.Example.exampleCertificate
#print axioms StrongPerimetralTurning.Example.exampleBeyondIsNotSamePerimeter
#print axioms StrongPerimetralTurning.Example.exampleConcreteFirstPath
#print axioms StrongPerimetralTurning.Example.exampleConcreteFirstRealization
#print axioms StrongPerimetralTurning.Example.exampleConcreteInterpretation
#print axioms StrongPerimetralTurning.Example.exampleFreshFormationRejectsPreviousRecord
#print axioms StrongPerimetralTurning.Example.exampleHistoricalFirstProvenancePreserved
#print axioms StrongPerimetralTurning.Example.exampleHistoricalRecordReadsFirst
#print axioms StrongPerimetralTurning.Example.exampleCurrentTargetReadsSecond
#print axioms StrongPerimetralTurning.Example.exampleHistoricalRecordAfterSecondStillReadsFirst
#print axioms StrongPerimetralTurning.Example.exampleInitialObstructionStored
#print axioms StrongPerimetralTurning.Example.exampleAfterFirstObstructionPreserved
#print axioms StrongPerimetralTurning.Example.exampleFormationConsumesInitialObstruction
#print axioms StrongPerimetralTurning.Example.exampleIntegratedProvenanceStored
#print axioms StrongPerimetralTurning.Example.exampleRecoveredAfterFirstReadsStoredProvenance
#print axioms StrongPerimetralTurning.Example.exampleRawFinalJunctionCompatibility
#print axioms StrongPerimetralTurning.Example.exampleRawJunctionWithSeparatedEndpoints
#print axioms StrongPerimetralTurning.Example.exampleFinalBoundaryOccurrence
#print axioms StrongPerimetralTurning.Example.exampleFinalClosureInterpretation
#print axioms StrongPerimetralTurning.Example.exampleActualFreeStep_source_is_fourth
#print axioms StrongPerimetralTurning.Example.exampleActualFreeStep_target_is_beyondFirst
#print axioms StrongPerimetralTurning.Example.exampleActualFreeStep_is_leaveBoundary
#print axioms StrongPerimetralTurning.Example.exampleInvokedJunction_is_fourthToFirst
#print axioms StrongPerimetralTurning.Example.exampleFinalObstruction_is_initial
#print axioms StrongPerimetralTurning.Example.exampleFinalProvenance_is_origin
#print axioms StrongPerimetralTurning.Example.exampleFinalFormationRecord_is_current
#print axioms StrongPerimetralTurning.Example.exampleNoBilateralClosureAttemptAt
#print axioms StrongPerimetralTurning.Example.exampleNoImplicitBilateralClosureAttemptAt
#print axioms StrongPerimetralTurning.ExactConcreteRealization
#print axioms StrongPerimetralTurning.ConcreteRegimeExit
#print axioms StrongPerimetralTurning.PerimetralRegimeExit
#print axioms StrongPerimetralTurning.PerimetralRegimeExit.toRegimeExit
#print axioms StrongPerimetralTurning.UniformConcreteRegimeExit
#print axioms StrongPerimetralTurning.UniformPerimetralRegimeExit
#print axioms StrongPerimetralTurning.UniformPerimetralRegimeExit.toUniformRegimeExit
#print axioms StrongPerimetralTurning.UniformPerimetralRegimeExit.atImplementation
#print axioms StrongPerimetralTurning.UniformPerimetralRegimeExit.at_forget
#print axioms StrongPerimetralTurning.UniformPerimetralRegimeExit.at_forget_named
#print axioms StrongPerimetralTurning.oneStepUniformPerimetralRegimeExit
#print axioms StrongPerimetralTurning.oneStepPerimetralRegimeExit
#print axioms StrongPerimetralTurning.oneStepConcreteRegimeExit
#print axioms StrongPerimetralTurning.HistoryAlignmentSpec
#print axioms StrongPerimetralTurning.circularNormativeAdequacy
#print axioms StrongPerimetralTurning.circularRefinement_adequateAlong
#print axioms StrongPerimetralTurning.oneStepSpecRelativeHistoryExit
#print axioms StrongPerimetralTurning.oneStepSpecRelativeHistoryExit_notSpecification

#print axioms StrongPerimetralTurning.NonClosingNext
#print axioms StrongPerimetralTurning.NonClosingNext.target_eq_source
#print axioms StrongPerimetralTurning.generatedHistory_equalEndpoints_noOccurrence
#print axioms StrongPerimetralTurning.SemanticTrace.Between
#print axioms StrongPerimetralTurning.ExactSemanticBridgeSegment
#print axioms StrongPerimetralTurning.EffectiveConstitutiveBridge
#print axioms StrongPerimetralTurning.bridgeParticipation_between_empty_of_next
#print axioms StrongPerimetralTurning.effectiveBridge_between_empty_of_next
#print axioms StrongPerimetralTurning.Example.exampleP1_next_exampleP2
#print axioms StrongPerimetralTurning.Example.exampleP2_next_exampleP3
#print axioms StrongPerimetralTurning.Example.interleavedExample_extra1_between
#print axioms StrongPerimetralTurning.Example.interleavedExample_extra2_between
#print axioms StrongPerimetralTurning.Example.interleavedExample_no_effective_bridge_p1_p2
#print axioms StrongPerimetralTurning.Example.interleavedExample_no_effective_bridge_p2_p3

#print axioms StrongPerimetralTurning.History.OccurrencePrecedes
#print axioms StrongPerimetralTurning.History.OccurrenceNext
#print axioms StrongPerimetralTurning.History.OccurrenceNext.toPrecedes
#print axioms StrongPerimetralTurning.History.OccurrencePrecedes.ne
#print axioms StrongPerimetralTurning.History.OccurrencePrecedes.trichotomy
#print axioms StrongPerimetralTurning.CursorReach.trans
#print axioms StrongPerimetralTurning.CursorFuture.transReach
#print axioms StrongPerimetralTurning.occurrenceSource_to_historyEndpoint_future
#print axioms StrongPerimetralTurning.occurrenceTarget_to_historyEndpoint_reach
#print axioms StrongPerimetralTurning.History.OccurrencePrecedes.sourceCursorFuture
#print axioms StrongPerimetralTurning.History.OccurrencePrecedes.next_or_positiveGap
#print axioms StrongPerimetralTurning.NonClosingPrecedes.ne
#print axioms StrongPerimetralTurning.NonClosingNext.toPrecedes
#print axioms StrongPerimetralTurning.positionSourceCursorReach
#print axioms StrongPerimetralTurning.NonClosingPrecedes.sourceCursorFuture
#print axioms StrongPerimetralTurning.ExactNonClosingRealization.realize_injective
#print axioms StrongPerimetralTurning.ExactNonClosingRealization.preservesPrecedence
#print axioms StrongPerimetralTurning.ExactNonClosingRealization.preservesNext
#print axioms StrongPerimetralTurning.ExactNonClosingRealization.embedPerimeterOccurrence
#print axioms StrongPerimetralTurning.ExactNonClosingRealization.embedPerimeterOccurrence_locatedStep
#print axioms StrongPerimetralTurning.ExactNonClosingRealization.embedPerimeterOccurrence_injective
#print axioms StrongPerimetralTurning.History.factorInitialGeneratedStep
#print axioms StrongPerimetralTurning.History.extractRightOccurrenceAfterSingle
#print axioms StrongPerimetralTurning.factorDeployRemainingFromExactOccurrences
#print axioms StrongPerimetralTurning.ExactNonClosingRealization.toPerimeterExtension
#print axioms StrongPerimetralTurning.CircularSpecificationSatisfaction.eq_perimeter
#print axioms StrongPerimetralTurning.circularSpecification_complete
#print axioms StrongPerimetralTurning.circularRefinement_soundSpecification
/- AXIOM_AUDIT_END -/
