import RelationalPerimeter.Relativity.ExactArithmetic

/-!
Executable polynomial expressions, exact rational evaluation and formal
differentiation. Jet evaluation shares each child's produced value and slope.
The formal derivative and primitive laws below are algebraic: connecting
them to limits on the analytic domain is still required separately.
-/
set_option genInjectivity false
namespace RelationalPerimeter.Relativity.Analysis

inductive Polynomial (dimension : Nat) where
  | coefficient (value : Rational)
  | coordinate (axis : Fin dimension)
  | sum (left right : Polynomial dimension)
  | product (left right : Polynomial dimension)

namespace Polynomial

def evaluate {dimension : Nat} (point : Fin dimension → Rational) : Polynomial dimension → Rational
  | .coefficient value => value
  | .coordinate axis => point axis
  | .sum left right => Rational.add (evaluate point left) (evaluate point right)
  | .product left right => Rational.mul (evaluate point left) (evaluate point right)

def formalDerivative {dimension : Nat} (axis : Fin dimension) : Polynomial dimension → Polynomial dimension
  | .coefficient _ => .coefficient Rational.zero
  | .coordinate other => .coefficient (if other = axis then Rational.one else Rational.zero)
  | .sum left right => .sum (formalDerivative axis left) (formalDerivative axis right)
  | .product left right => .sum (.product (formalDerivative axis left) right)
      (.product left (formalDerivative axis right))

structure Jet where
  value : Rational
  slope : Rational

def evaluateJet {dimension : Nat} (point : Fin dimension → Rational) (axis : Fin dimension) :
    Polynomial dimension → Jet
  | .coefficient value => ⟨value, Rational.zero⟩
  | .coordinate other => ⟨point other, if other = axis then Rational.one else Rational.zero⟩
  | .sum left right =>
    let leftProduced := evaluateJet point axis left
    let rightProduced := evaluateJet point axis right
    ⟨Rational.add leftProduced.value rightProduced.value,
     Rational.add leftProduced.slope rightProduced.slope⟩
  | .product left right =>
    let leftProduced := evaluateJet point axis left
    let rightProduced := evaluateJet point axis right
    ⟨Rational.mul leftProduced.value rightProduced.value,
     Rational.add (Rational.mul leftProduced.slope rightProduced.value)
       (Rational.mul leftProduced.value rightProduced.slope)⟩

theorem jet_exact {dimension : Nat} (point : Fin dimension → Rational) (axis : Fin dimension)
    (polynomial : Polynomial dimension) :
    (evaluateJet point axis polynomial).value = evaluate point polynomial ∧
    (evaluateJet point axis polynomial).slope = evaluate point (formalDerivative axis polynomial) := by
  induction polynomial with
  | coefficient => exact ⟨rfl, rfl⟩
  | coordinate => exact ⟨rfl, rfl⟩
  | sum left right ihl ihr =>
    dsimp only [evaluateJet, evaluate, formalDerivative]
    constructor
    · rw [ihl.1, ihr.1]
    · rw [ihl.2, ihr.2]
  | product left right ihl ihr =>
    dsimp only [evaluateJet, evaluate, formalDerivative]
    constructor
    · rw [ihl.1, ihr.1]
    · rw [ihl.1, ihr.1, ihl.2, ihr.2]

end Polynomial

namespace UnivariateSeries

def evaluate (point : Rational) : List Rational → Rational
  | [] => Rational.zero
  | coefficient :: tail => Rational.add coefficient (Rational.mul point (evaluate point tail))

def weightedFrom (start : Nat) : List Rational → List Rational
  | [] => []
  | coefficient :: tail => Rational.mul (Rational.ofNat start) coefficient :: weightedFrom (start + 1) tail

def integrateFrom (start : Nat) : List Rational → List Rational
  | [] => []
  | coefficient :: tail => Rational.mul coefficient (Rational.inverseNatSucc start) :: integrateFrom (start + 1) tail

def formalDerivative : List Rational → List Rational
  | [] => []
  | _ :: tail => weightedFrom 1 tail

def primitive (coefficients : List Rational) : List Rational := Rational.zero :: integrateFrom 0 coefficients

theorem weighted_integrate (start : Nat) (coefficients : List Rational) :
    weightedFrom (start + 1) (integrateFrom start coefficients) = coefficients := by
  induction coefficients generalizing start with
  | nil => rfl
  | cons coefficient tail ih =>
    dsimp only [weightedFrom, integrateFrom]
    rw [← Rational.mul_assoc, Rational.mul_comm (Rational.ofNat (start + 1)) coefficient,
      Rational.mul_assoc, Rational.nat_succ_inverse, Rational.mul_one, ih]

theorem derivative_primitive (coefficients : List Rational) : formalDerivative (primitive coefficients) = coefficients :=
  weighted_integrate 0 coefficients

theorem primitive_zero (coefficients : List Rational) : evaluate Rational.zero (primitive coefficients) = Rational.zero := by
  unfold primitive
  rw [evaluate, Rational.zero_mul, Rational.add_zero]

end UnivariateSeries
end RelationalPerimeter.Relativity.Analysis

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Relativity.Analysis.Polynomial
#print axioms RelationalPerimeter.Relativity.Analysis.Polynomial.evaluate
#print axioms RelationalPerimeter.Relativity.Analysis.Polynomial.formalDerivative
#print axioms RelationalPerimeter.Relativity.Analysis.Polynomial.evaluateJet
#print axioms RelationalPerimeter.Relativity.Analysis.Polynomial.jet_exact
#print axioms RelationalPerimeter.Relativity.Analysis.UnivariateSeries.evaluate
#print axioms RelationalPerimeter.Relativity.Analysis.UnivariateSeries.integrateFrom
#print axioms RelationalPerimeter.Relativity.Analysis.UnivariateSeries.formalDerivative
#print axioms RelationalPerimeter.Relativity.Analysis.UnivariateSeries.primitive
#print axioms RelationalPerimeter.Relativity.Analysis.UnivariateSeries.weighted_integrate
#print axioms RelationalPerimeter.Relativity.Analysis.UnivariateSeries.derivative_primitive
#print axioms RelationalPerimeter.Relativity.Analysis.UnivariateSeries.primitive_zero
/- AXIOM_AUDIT_END -/
