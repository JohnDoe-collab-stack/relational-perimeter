import RelationalPerimeter.Constitution.Godel.RealCorrespondence
import RelationalPerimeter.Instances.HeytingArithmetic.RelationalCompleteness

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Effective-real correspondence on the Heyting-arithmetic Gödel perimeter

This module closes the generic parameters of the runtime/effective-real
correspondence with the repository's concrete executed Gödel production for
Heyting arithmetic.  The numerical presentation is received independently;
Gödel fixes the perimeter and rejects total same-regime closure, while the
runtime constructs and retains the source, grouping, limit, and readout data.
-/

namespace RelationalPerimeter.HeytingArithmetic

open StrongPerimetralTurning
open StrongPerimetralTurning.GodelRealCorrespondence
open RelationalPerimeter.Constitution.Reals.RuntimeCorrespondence
open RelationalPerimeter.Constitution.Reals.EffectiveCauchyReal

/-- Canonical runtime realization of a presentation on the concrete HA perimeter. -/
def heytingArithmeticPresentationRuntime
    (presentation : EffectiveDyadicPresentation) :
    RuntimeReal heytingArithmeticGodelPresentation 1 :=
  presentationToGodelRuntime heytingArithmeticGodelExecution presentation

/-- Canonical runtime realization of an external effective Cauchy carrier. -/
def heytingArithmeticEffectiveCauchyRuntime
    (real : Carrier) : RuntimeReal heytingArithmeticGodelPresentation 1 :=
  carrierToGodelRuntime heytingArithmeticGodelExecution real

/--
The complete presentation-level result: concrete Gödel rejection, positive
runtime completion, exact numerical round trip, retained finite futures, and
directed provenance of every readout.
-/
def heytingArithmeticPresentationCorrespondence
    (presentation : EffectiveDyadicPresentation) :
    PresentationResult heytingArithmeticGodelExecution presentation :=
  realizePresentation heytingArithmeticGodelExecution presentation

/--
The complete external-carrier result, including equivalence with the received
constructive effective Cauchy real.
-/
def heytingArithmeticEffectiveCauchyCorrespondence
    (real : Carrier) :
    CarrierResult heytingArithmeticGodelExecution real :=
  realizeCarrier heytingArithmeticGodelExecution real

end RelationalPerimeter.HeytingArithmetic

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.HeytingArithmetic.heytingArithmeticPresentationRuntime
#print axioms RelationalPerimeter.HeytingArithmetic.heytingArithmeticEffectiveCauchyRuntime
#print axioms RelationalPerimeter.HeytingArithmetic.heytingArithmeticPresentationCorrespondence
#print axioms RelationalPerimeter.HeytingArithmetic.heytingArithmeticEffectiveCauchyCorrespondence
/- AXIOM_AUDIT_END -/
