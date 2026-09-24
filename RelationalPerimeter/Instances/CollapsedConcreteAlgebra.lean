import StrongPerimetralTurning

/-!
# Collapsed concrete interpretation

This instance makes explicit a limit of concrete interpretation.  All
constituted states, explicit and implicit readings, differences, and
compatibility witnesses are sent to one-point carriers.  The boundary record
remains separate because `ConcreteContinuationAlgebra` requires each generated
boundary to be fresh.  Exact interpretation of history occurrences therefore
coexists with collapse of the free-level state and target distinctions.
-/

namespace RelationalPerimeter.Instances.CollapsedConcreteAlgebra

open StrongPerimetralTurning

/-- Every generated step gives a positive history from its source. -/
def canonicalPositiveHistory
    {P : CircularPresentation}
    (source : PositiveConstitution P) :
    History.Positive (@GeneratedStep P) source (canonicalTarget source) :=
  ⟨source, .root, generatedStepOfFreeK source⟩

/-- A canonical generated target is constructively distinct from its source. -/
theorem canonicalTarget_ne_source
    {P : CircularPresentation}
    (source : PositiveConstitution P) :
    canonicalTarget source ≠ source :=
  fun equality =>
    positiveGeneratedHistory_source_ne_target
      (canonicalPositiveHistory source) equality.symm

/--
A concrete algebra whose semantic carriers are all one-point types.  Only the
fresh boundary record retains the free constitution needed by the algebraic
interface.
-/
def collapsedConcreteAlgebra
    (P : CircularPresentation) :
    ConcreteContinuationAlgebra.{0, 0, 0, 0, 0, 0, 0, 0, 0, _} P :=
  { ConcreteState := PUnit
    ConcreteStep := fun _ _ => PUnit
    stateAt := fun _ => ⟨⟩
    ConcreteExplicit := PUnit
    ConcreteImplicit := PUnit
    ConcreteCompatible := fun _ _ => PUnit
    interpretExplicit := fun _ => ⟨⟩
    interpretImplicit := fun _ => ⟨⟩
    interpretCompatible := fun _ => ⟨⟩
    ConcreteDifference := PUnit
    ConcreteProvenance := fun _ => PUnit
    interpretDifference := fun _ => ⟨⟩
    interpretProvenance := fun _ => ⟨⟩
    ConcreteIntegration := fun _ => PUnit
    ConcreteContinuation := fun _ _ => PUnit
    ConcreteFreshBoundary := fun _ _ => PUnit
    ConcreteBoundaryRecord := PositiveConstitution P
    boundaryRecordAt := fun state => state
    concreteStep := fun _ => ⟨⟩
    explicitPoleStep := fun _ => ⟨⟩
    implicitPoleStep := fun _ => ⟨⟩
    differenceStep := fun _ => ⟨⟩
    admissibleStep := fun _ _ => ⟨⟩
    successorFormationExact := fun _ => rfl
    compatibilityRealized := fun _ => ⟨⟩
    compatibilityRealizedExact := fun _ => rfl
    differenceIntegrated := fun _ => ⟨⟩
    provenancePreserved := fun _ => ⟨⟩
    provenancePreservedExact := fun _ => rfl
    differenceContinued := fun _ => ⟨⟩
    boundaryFresh := fun _ => ⟨⟩
    boundaryRecordFresh := canonicalTarget_ne_source }

/-- Every free constitution has the same concrete state in this algebra. -/
theorem stateAt_collapses
    {P : CircularPresentation}
    (first second : PositiveConstitution P) :
    (collapsedConcreteAlgebra P).stateAt first =
      (collapsedConcreteAlgebra P).stateAt second :=
  rfl

/-- Every returned explicit target has the same concrete interpretation. -/
theorem explicitTarget_collapses
    {P : CircularPresentation}
    (first second : ReturnedExplicit P) :
    (collapsedConcreteAlgebra P).interpretExplicit first =
      (collapsedConcreteAlgebra P).interpretExplicit second :=
  rfl

/-- Occurrence interpretation nevertheless retains its exact round trips. -/
def exactHistoryInterpretation
    {P : CircularPresentation}
    {source target : PositiveConstitution P}
    (history : GeneratedHistory source target) :
    ExactHistoryInterpretation
      (collapsedConcreteAlgebra P) history
      ((collapsedConcreteAlgebra P).realizeHistory history) :=
  exactlyInterpretHistory (collapsedConcreteAlgebra P) history

end RelationalPerimeter.Instances.CollapsedConcreteAlgebra

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Instances.CollapsedConcreteAlgebra.canonicalPositiveHistory
#print axioms RelationalPerimeter.Instances.CollapsedConcreteAlgebra.canonicalTarget_ne_source
#print axioms RelationalPerimeter.Instances.CollapsedConcreteAlgebra.collapsedConcreteAlgebra
#print axioms RelationalPerimeter.Instances.CollapsedConcreteAlgebra.stateAt_collapses
#print axioms RelationalPerimeter.Instances.CollapsedConcreteAlgebra.explicitTarget_collapses
#print axioms RelationalPerimeter.Instances.CollapsedConcreteAlgebra.exactHistoryInterpretation
/- AXIOM_AUDIT_END -/
