import Init

/-!
# Positive successive primitives

The historical namespace is retained for downstream compatibility. This module
contains only witnessed nodes, the successive spine, positions and their order.
It imports neither circular obstruction nor generated-history machinery.
-/

namespace StrongPerimetralTurning

universe uE uI uK uD uP

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


end StrongPerimetralTurning

/- AXIOM_AUDIT_BEGIN -/
#print axioms StrongPerimetralTurning.LocalNode
#print axioms StrongPerimetralTurning.PerimeterSpine
#print axioms StrongPerimetralTurning.PerimeterSpine.startNode
#print axioms StrongPerimetralTurning.PerimeterSpine.finalNode
#print axioms StrongPerimetralTurning.NonClosingPosition
#print axioms StrongPerimetralTurning.NonClosingPrecedes
#print axioms StrongPerimetralTurning.NonClosingNext
#print axioms StrongPerimetralTurning.NonClosingPrecedes.ne
#print axioms StrongPerimetralTurning.NonClosingNext.toPrecedes
/- AXIOM_AUDIT_END -/
