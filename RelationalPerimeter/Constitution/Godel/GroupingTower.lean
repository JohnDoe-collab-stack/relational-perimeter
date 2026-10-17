import RelationalPerimeter.Constitution.Godel.PerimetralCorrespondence
import RelationalPerimeter.Constitution.PerimeterPersistence

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Gödel occurrence persistence along the constitutive tower

This module contains only the positive depth extensions and occurrence
transports shared by the authoritative runtime.  Runtime phases and their
resources live in `Constitution.Reals.ConstitutiveRuntime`; no homogeneous
schedule of labels or payload-bearing legacy journal is retained here.
-/

namespace StrongPerimetralTurning
namespace GodelGroupingTower

open ConstitutiveSearch.OccurrencePersistence
open ConstitutiveSearch.PerimeterPersistence.Iterated

universe uSource uTarget

/-- Positively extend any existing depth by a supplied finite number of steps. -/
def extendDepthBy :
    (source extra : Nat) -> DepthExtension source (source + extra)
  | source, 0 => .refl source
  | source, Nat.succ extra => .step (extendDepthBy source extra)

/-- Forward maps of exact transports are injective. -/
theorem exactForwardInjective
    {Source : Type uSource}
    {Target : Type uTarget}
    (transport : ExactTypeTransport Source Target) :
    Function.Injective transport.forward := by
  intro first second equality
  calc
    first = transport.backward (transport.forward first) :=
      (transport.forwardBackward first).symm
    _ = transport.backward (transport.forward second) :=
      congrArg transport.backward equality
    _ = second := transport.forwardBackward second

/-- Backward maps of exact transports are injective. -/
theorem exactBackwardInjective
    {Source : Type uSource}
    {Target : Type uTarget}
    (transport : ExactTypeTransport Source Target) :
    Function.Injective transport.backward := by
  intro first second equality
  calc
    first = transport.forward (transport.backward first) :=
      (transport.backwardForward first).symm
    _ = transport.forward (transport.backward second) :=
      congrArg transport.forward equality
    _ = second := transport.backwardForward second

/--
Extend an actual occurrence from one generated history to a supplied later
depth through the shared finite index.
-/
def extendOccurrence
    (P : CircularPresentation)
    {sourceDepth targetDepth : Nat}
    (depth : DepthExtension sourceDepth targetDepth)
    (occurrence : History.Occurrence (iteratedHistory P sourceDepth).history) :
    History.Occurrence (iteratedHistory P targetDepth).history :=
  (iteratedOccurrenceSpoke P targetDepth).forward
    (IteratedCarrier.embedFrom depth
      ((iteratedOccurrenceSpoke P sourceDepth).backward occurrence))

theorem extendOccurrence_injective
    (P : CircularPresentation)
    {sourceDepth targetDepth : Nat}
    (depth : DepthExtension sourceDepth targetDepth) :
    Function.Injective (extendOccurrence P depth) := by
  intro first second equality
  have embeddedEquality :
      IteratedCarrier.embedFrom depth
          ((iteratedOccurrenceSpoke P sourceDepth).backward first) =
        IteratedCarrier.embedFrom depth
          ((iteratedOccurrenceSpoke P sourceDepth).backward second) := by
    exact exactForwardInjective (iteratedOccurrenceSpoke P targetDepth) equality
  have indexedEquality :=
    IteratedCarrier.embedFrom_injective depth embeddedEquality
  exact exactBackwardInjective
    (iteratedOccurrenceSpoke P sourceDepth) indexedEquality

theorem extendOccurrence_ne
    (P : CircularPresentation)
    {sourceDepth targetDepth : Nat}
    (depth : DepthExtension sourceDepth targetDepth)
    {first second :
      History.Occurrence (iteratedHistory P sourceDepth).history}
    (distinct : first ≠ second) :
    extendOccurrence P depth first ≠ extendOccurrence P depth second := by
  intro equality
  exact distinct (extendOccurrence_injective P depth equality)

/-! ## Persistence of the three distinct occurrences produced by Gödel -/

/-- The three established Gödel occurrences, transported into one later depth. -/
structure PersistedGodelOccurrences
    {coding : GodelDiagonalSyntax}
    {unprovabilityFormula : coding.UnaryFormula}
    {interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula}
    (execution :
      ExecutedGodelProduction coding unprovabilityFormula interpretation)
    (targetDepth : Nat) where
  production :
    History.Occurrence
      (iteratedHistory (godelPerimetralPresentation execution) targetDepth).history
  certification :
    History.Occurrence
      (iteratedHistory (godelPerimetralPresentation execution) targetDepth).history
  continuation :
    History.Occurrence
      (iteratedHistory (godelPerimetralPresentation execution) targetDepth).history
  productionCertificationDistinct : production ≠ certification
  productionContinuationDistinct : production ≠ continuation
  certificationContinuationDistinct : certification ≠ continuation

/--
Transport the already produced Gödel occurrences; the construction consumes
the affirmative constitution instead of manufacturing a second triple.
-/
def persistGodelOccurrences
    {coding : GodelDiagonalSyntax}
    {unprovabilityFormula : coding.UnaryFormula}
    {interpretation :
      GodelProvabilityInterpretation coding unprovabilityFormula}
    (execution :
      ExecutedGodelProduction coding unprovabilityFormula interpretation)
    {targetDepth : Nat}
    (depth : DepthExtension 1 targetDepth) :
    PersistedGodelOccurrences execution targetDepth := by
  let affirmative := godelAffirmativeConstitution execution
  exact
  { production := extendOccurrence
      (godelPerimetralPresentation execution) depth
      affirmative.productionOccurrence
    certification := extendOccurrence
      (godelPerimetralPresentation execution) depth
      affirmative.certificationOccurrence
    continuation := extendOccurrence
      (godelPerimetralPresentation execution) depth
      affirmative.continuationOccurrence
    productionCertificationDistinct :=
      extendOccurrence_ne
        (godelPerimetralPresentation execution) depth
        affirmative.productionCertificationDistinct
    productionContinuationDistinct :=
      extendOccurrence_ne
        (godelPerimetralPresentation execution) depth
        affirmative.productionContinuationDistinct
    certificationContinuationDistinct :=
      extendOccurrence_ne
        (godelPerimetralPresentation execution) depth
        affirmative.certificationContinuationDistinct }

end GodelGroupingTower
end StrongPerimetralTurning

/- AXIOM_AUDIT_BEGIN -/
#print axioms StrongPerimetralTurning.GodelGroupingTower.extendDepthBy
#print axioms StrongPerimetralTurning.GodelGroupingTower.exactForwardInjective
#print axioms StrongPerimetralTurning.GodelGroupingTower.exactBackwardInjective
#print axioms StrongPerimetralTurning.GodelGroupingTower.extendOccurrence
#print axioms StrongPerimetralTurning.GodelGroupingTower.extendOccurrence_injective
#print axioms StrongPerimetralTurning.GodelGroupingTower.extendOccurrence_ne
#print axioms StrongPerimetralTurning.GodelGroupingTower.PersistedGodelOccurrences
#print axioms StrongPerimetralTurning.GodelGroupingTower.persistGodelOccurrences
/- AXIOM_AUDIT_END -/
