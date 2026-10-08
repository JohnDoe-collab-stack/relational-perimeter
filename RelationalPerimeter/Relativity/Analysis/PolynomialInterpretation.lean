import RelationalPerimeter.Relativity.Analysis.ConstructiveContinuum
import RelationalPerimeter.Relativity.Analysis.PolynomialCalculus

/-!
Polynomial evaluation on the constructed analytic representations. The
agreement witnesses are produced recursively from the actual operations.
Agreement does not identify encodings. Faithfulness on rational points and
respect for coordinate agreement are proved here; analytic differentiability
and integration are not inferred from the formal derivative laws.
-/
set_option genInjectivity false
namespace RelationalPerimeter.Relativity.Analysis.Polynomial

def interpret {dimension : Nat} (point : Fin dimension → CauchyRepresentation) :
    Polynomial dimension → CauchyRepresentation
  | .coefficient value => CauchyRepresentation.constant value
  | .coordinate axis => point axis
  | .sum left right => CauchyRepresentation.add (interpret point left) (interpret point right)
  | .product left right => CauchyRepresentation.mul (interpret point left) (interpret point right)

def interpretationAgreement {dimension : Nat} (left right : Fin dimension → CauchyRepresentation)
    (coordinates : ∀ axis, Agreement (left axis) (right axis)) :
    (polynomial : Polynomial dimension) → Agreement (interpret left polynomial) (interpret right polynomial)
  | .coefficient value => Agreement.reflexive (CauchyRepresentation.constant value)
  | .coordinate axis => coordinates axis
  | .sum first second => CauchyRepresentation.addAgreement
      (interpretationAgreement left right coordinates first)
      (interpretationAgreement left right coordinates second)
  | .product first second => CauchyRepresentation.mulAgreement
      (interpretationAgreement left right coordinates first)
      (interpretationAgreement left right coordinates second)

def rationalReading {dimension : Nat} (point : Fin dimension → Rational) :
    (polynomial : Polynomial dimension) →
      Agreement (interpret (fun axis => CauchyRepresentation.constant (point axis)) polynomial)
        (CauchyRepresentation.constant (evaluate point polynomial))
  | .coefficient value => Agreement.reflexive (CauchyRepresentation.constant value)
  | .coordinate axis => Agreement.reflexive (CauchyRepresentation.constant (point axis))
  | .sum left right => Agreement.compose
      (CauchyRepresentation.addAgreement (rationalReading point left) (rationalReading point right))
      (CauchyRepresentation.constantAddition (evaluate point left) (evaluate point right))
  | .product left right => Agreement.compose
      (CauchyRepresentation.mulAgreement (rationalReading point left) (rationalReading point right))
      (CauchyRepresentation.constantProduct (evaluate point left) (evaluate point right))

end RelationalPerimeter.Relativity.Analysis.Polynomial

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Relativity.Analysis.Polynomial.interpret
#print axioms RelationalPerimeter.Relativity.Analysis.Polynomial.interpretationAgreement
#print axioms RelationalPerimeter.Relativity.Analysis.Polynomial.rationalReading
/- AXIOM_AUDIT_END -/
