import RelationalPerimeter.Constitution.HeytingArithmetic.Coding

/-!
# Substitution on Goedel codes

The transformation is total on naturals.  Invalid inputs are sent to the code
of falsity; valid formula codes commute exactly with syntactic substitution.
-/

namespace RelationalPerimeter
namespace HeytingArithmetic

/-- Code of the result of replacing every free variable by a numeral. -/
def substituteNumeralCode (formulaCode value : Nat) : Nat :=
  match decodeFormula formulaCode with
  | none => RawFormula.falsum.code
  | some formula => (formula.instantiateNumeral value).code

/-- Self-substitution used by the diagonal construction. -/
def diagonalSubstitutionCode (formulaCode : Nat) : Nat :=
  substituteNumeralCode formulaCode formulaCode

/-- Coding commutes exactly with numeral substitution on genuine syntax. -/
theorem substituteNumeralCode_code
    (formula : RawFormula)
    (value : Nat) :
    substituteNumeralCode formula.code value =
      (formula.instantiateNumeral value).code := by
  rw [substituteNumeralCode, decodeFormula_code]

/-- The self-substitution code has the expected syntactic value. -/
theorem diagonalSubstitutionCode_code (formula : RawFormula) :
    diagonalSubstitutionCode formula.code =
      (formula.instantiateNumeral formula.code).code := by
  exact substituteNumeralCode_code formula formula.code

/-- Applying a predicate to the code of a sentence, as closed syntax. -/
def applyQuote (predicate : Predicate) (sentence : Sentence) : Sentence :=
  predicate.applyNumeral sentence.quote

/-- Quoted application has the expected standard-model semantics. -/
theorem models_applyQuote
    (predicate : Predicate)
    (sentence : Sentence) :
    (applyQuote predicate sentence).models ↔
      predicate.raw.Holds
        (pushEnvironment emptyEnvironment sentence.quote) :=
  predicate.models_applyNumeral sentence.quote

end HeytingArithmetic
end RelationalPerimeter

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.HeytingArithmetic.substituteNumeralCode
#print axioms RelationalPerimeter.HeytingArithmetic.substituteNumeralCode_code
#print axioms RelationalPerimeter.HeytingArithmetic.diagonalSubstitutionCode
#print axioms RelationalPerimeter.HeytingArithmetic.diagonalSubstitutionCode_code
#print axioms RelationalPerimeter.HeytingArithmetic.applyQuote
#print axioms RelationalPerimeter.HeytingArithmetic.models_applyQuote
/- AXIOM_AUDIT_END -/
