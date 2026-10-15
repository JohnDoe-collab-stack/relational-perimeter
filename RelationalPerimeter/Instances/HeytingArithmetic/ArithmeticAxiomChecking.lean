import RelationalPerimeter.Instances.HeytingArithmetic.ProofDecoding

/-!
# Constructive recognition of hypotheses and standard arithmetic postulates

Scoping is recomputed from raw syntax by the certified decoders.  In
particular, the postulate recognizer never pattern-matches dependently on a
proposition carrying scoping evidence.
-/

namespace RelationalPerimeter
namespace HeytingArithmetic

def contextMemberWitness
    {bound : Nat}
    (formula : ScopedFormula bound) :
    (context : FormulaContext bound) -> Option (ContextMember formula context)
  | FormulaContext.nil => none
  | FormulaContext.cons head tail =>
      if sameRaw : formula.raw = head.raw then
        let same : formula = head :=
          ScopedFormula.eq_of_raw_eq sameRaw
        match same with
        | rfl => some ContextMember.here
      else
        match contextMemberWitness formula tail with
        | none => none
        | some witness => some (ContextMember.there witness)

structure PackedStandardArithmeticAxiom (bound : Nat) where
  formula : ScopedFormula bound
  witness : StandardArithmeticAxiom formula

def packedInductionCandidate
    {bound : Nat}
    (body : ScopedFormula (Nat.succ bound)) :
    PackedStandardArithmeticAxiom bound :=
  { formula := ScopedFormula.induction body
    witness := StandardArithmeticAxiom.induction body }

def scopedTermCandidate (bound : Nat) (raw : RawTerm) :
    Option (ScopedTerm bound) :=
  match RawTerm.wellScopedDecision bound raw with
  | isFalse _notScoped => none
  | isTrue isScoped => some { raw := raw, isScoped := isScoped }

def scopedFormulaCandidate (bound : Nat) (raw : RawFormula) :
    Option (ScopedFormula bound) :=
  match RawFormula.wellScopedDecision bound raw with
  | isFalse _notScoped => none
  | isTrue isScoped => some { raw := raw, isScoped := isScoped }

def inductionAxiomCandidateFromBodyRaw
    (bound : Nat)
    (bodyRaw : RawFormula) :
    Option (PackedStandardArithmeticAxiom bound) :=
  Option.map packedInductionCandidate
    (scopedFormulaCandidate (Nat.succ bound) bodyRaw)

def successorNotZeroCandidateFromCode
    (bound termCode : Nat) :
    Option (PackedStandardArithmeticAxiom bound) :=
  Option.map
    (fun term =>
      { formula := ScopedFormula.neg
          (ScopedFormula.equal term.succ (ScopedTerm.zero bound))
        witness := StandardArithmeticAxiom.successorNotZero term })
    (decodeScopedTerm bound termCode)

def successorInjectiveCandidateFromCodes
    (bound leftCode rightCode : Nat) :
    Option (PackedStandardArithmeticAxiom bound) :=
  Option.bind (decodeScopedTerm bound leftCode) (fun left =>
    Option.map
      (fun right =>
        { formula := ScopedFormula.impl
            (ScopedFormula.equal left.succ right.succ)
            (ScopedFormula.equal left right)
          witness :=
            StandardArithmeticAxiom.successorInjective left right })
      (decodeScopedTerm bound rightCode))

def addZeroCandidateFromCode
    (bound termCode : Nat) :
    Option (PackedStandardArithmeticAxiom bound) :=
  Option.map
    (fun term =>
      { formula := ScopedFormula.equal
          (ScopedTerm.add term (ScopedTerm.zero bound)) term
        witness := StandardArithmeticAxiom.addZero term })
    (decodeScopedTerm bound termCode)

def addSuccessorCandidateFromCodes
    (bound leftCode rightCode : Nat) :
    Option (PackedStandardArithmeticAxiom bound) :=
  Option.bind (decodeScopedTerm bound leftCode) (fun left =>
    Option.map
      (fun right =>
        { formula := ScopedFormula.equal
            (ScopedTerm.add left right.succ)
            (ScopedTerm.succ (ScopedTerm.add left right))
          witness := StandardArithmeticAxiom.addSuccessor left right })
      (decodeScopedTerm bound rightCode))

def multiplyZeroCandidateFromCode
    (bound termCode : Nat) :
    Option (PackedStandardArithmeticAxiom bound) :=
  Option.map
    (fun term =>
      { formula := ScopedFormula.equal
          (ScopedTerm.mul term (ScopedTerm.zero bound))
          (ScopedTerm.zero bound)
        witness := StandardArithmeticAxiom.multiplyZero term })
    (decodeScopedTerm bound termCode)

def multiplySuccessorCandidateFromCodes
    (bound leftCode rightCode : Nat) :
    Option (PackedStandardArithmeticAxiom bound) :=
  Option.bind (decodeScopedTerm bound leftCode) (fun left =>
    Option.map
      (fun right =>
        { formula := ScopedFormula.equal
            (ScopedTerm.mul left right.succ)
            (ScopedTerm.add (ScopedTerm.mul left right) left)
          witness :=
            StandardArithmeticAxiom.multiplySuccessor left right })
      (decodeScopedTerm bound rightCode))

def inductionCandidateFromCode
    (bound bodyCode : Nat) :
    Option (PackedStandardArithmeticAxiom bound) :=
  Option.map packedInductionCandidate
    (decodeScopedFormula (Nat.succ bound) bodyCode)

/-! ## Total access to prefix-coded parameter lists -/

def codedListHead : Nat -> Nat
  | 0 => 0
  | Nat.succ encoded => (natUnpair encoded).1

def codedListTail : Nat -> Nat
  | 0 => 0
  | Nat.succ encoded => (natUnpair encoded).2

def codedListEntry (code : Nat) : Nat -> Nat
  | 0 => codedListHead code
  | Nat.succ index => codedListEntry (codedListTail code) index

/-- Reconstruct one standard postulate candidate from its numeric payload.
    Exact payload equality is checked separately against the reconstructed
    witness, so all accesses remain total on malformed inputs. -/
def standardArithmeticAxiomCandidateFromCode
    (bound parameterCode : Nat) :
    Option (PackedStandardArithmeticAxiom bound) :=
  let tag := codedListEntry parameterCode 0
  let first := codedListEntry parameterCode 1
  let second := codedListEntry parameterCode 2
  match tag with
  | 0 => successorNotZeroCandidateFromCode bound first
  | 1 => successorInjectiveCandidateFromCodes bound first second
  | 2 => addZeroCandidateFromCode bound first
  | 3 => addSuccessorCandidateFromCodes bound first second
  | 4 => multiplyZeroCandidateFromCode bound first
  | 5 => multiplySuccessorCandidateFromCodes bound first second
  | 6 => inductionCandidateFromCode bound first
  | _ => none

end HeytingArithmetic
end RelationalPerimeter

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.HeytingArithmetic.contextMemberWitness
#print axioms RelationalPerimeter.HeytingArithmetic.packedInductionCandidate
#print axioms RelationalPerimeter.HeytingArithmetic.scopedTermCandidate
#print axioms RelationalPerimeter.HeytingArithmetic.scopedFormulaCandidate
#print axioms RelationalPerimeter.HeytingArithmetic.inductionAxiomCandidateFromBodyRaw
#print axioms RelationalPerimeter.HeytingArithmetic.decodeScopedTerm
#print axioms RelationalPerimeter.HeytingArithmetic.decodeScopedFormula
#print axioms RelationalPerimeter.HeytingArithmetic.successorNotZeroCandidateFromCode
#print axioms RelationalPerimeter.HeytingArithmetic.successorInjectiveCandidateFromCodes
#print axioms RelationalPerimeter.HeytingArithmetic.addZeroCandidateFromCode
#print axioms RelationalPerimeter.HeytingArithmetic.addSuccessorCandidateFromCodes
#print axioms RelationalPerimeter.HeytingArithmetic.multiplyZeroCandidateFromCode
#print axioms RelationalPerimeter.HeytingArithmetic.multiplySuccessorCandidateFromCodes
#print axioms RelationalPerimeter.HeytingArithmetic.inductionCandidateFromCode
#print axioms RelationalPerimeter.HeytingArithmetic.codedListEntry
#print axioms RelationalPerimeter.HeytingArithmetic.standardArithmeticAxiomCandidateFromCode
/- AXIOM_AUDIT_END -/
