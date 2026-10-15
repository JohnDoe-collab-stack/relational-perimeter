import RelationalPerimeter

/-!
# Public-root import gate

This module is a downstream-style build check.  Its presence in the default
Lake target ensures that the public `RelationalPerimeter` module is registered,
built, and importable rather than merely valid when elaborated as a source file.
-/

namespace RelationalPerimeter.Tests.PublicRootImport

open ConstitutiveSearch.EndogenousDecomposition
open RelationalPerimeter.Computation.EndogenousOperationalDecomposition

def publicEvidence :=
  RelationalPerimeter.Computation.EndogenousOperationalDecomposition.evidence

def publicFamily :=
  RelationalPerimeter.Computation.EndogenousOperationalDecomposition.family

def publicSuccinctnessEvidence :=
  RelationalPerimeter.Computation.EndogenousOperationalDecomposition.constitutiveNormalizerSuccinctnessEvidence

def publicArithmeticGodelCorrespondence
    (theory :
      StrongPerimetralTurning.EffectivelyPresentedSoundArithmeticTheory) :
    StrongPerimetralTurning.ArithmeticGodelPerimetralCorrespondence theory :=
  StrongPerimetralTurning.arithmeticGodelPerimetralCorrespondence theory

def publicArithmeticGodelCausalParticipation
    (theory :
      StrongPerimetralTurning.EffectivelyPresentedSoundArithmeticTheory) :
    StrongPerimetralTurning.ArithmeticExecutedGodelCausalParticipation
      (StrongPerimetralTurning.arithmeticGodelPerimetralCorrespondence
        theory).effective.execution :=
  (StrongPerimetralTurning.arithmeticGodelPerimetralCorrespondence
    theory).executedCausalParticipation

def publicArithmeticGodelExecutedOccurrenceCorrespondence
    (theory :
      StrongPerimetralTurning.EffectivelyPresentedSoundArithmeticTheory) :
    StrongPerimetralTurning.ArithmeticExecutedGodelOccurrenceCorrespondence
      (publicArithmeticGodelCausalParticipation theory) :=
  (publicArithmeticGodelCausalParticipation
    theory).executedOccurrenceCorrespondence

def publicArithmeticGodelCausalClosureRejection
    (theory :
      StrongPerimetralTurning.EffectivelyPresentedSoundArithmeticTheory) :
    StrongPerimetralTurning.ArithmeticExecutedGodelCausalClosureMeaning
        (publicArithmeticGodelCausalParticipation theory) →
      Empty :=
  (StrongPerimetralTurning.arithmeticGodelPerimetralCorrespondence
    theory).causalClosureIsImpossible

def publicArithmeticGodelDirectedClosureRejection
    (theory :
      StrongPerimetralTurning.EffectivelyPresentedSoundArithmeticTheory) :
    StrongPerimetralTurning.ArithmeticExecutedGodelDirectedClosureMeaning
        (publicArithmeticGodelCausalParticipation theory) →
      Empty :=
  (StrongPerimetralTurning.arithmeticGodelPerimetralCorrespondence
    theory).directedClosureIsImpossible

def publicSemanticallyDefinedArithmeticGodelCorrespondence
    (theory :
      StrongPerimetralTurning.SemanticallyDefinedProofArithmeticTheory) :
    StrongPerimetralTurning.SemanticallyDefinedArithmeticGodelPerimetralCorrespondence
      theory :=
  StrongPerimetralTurning.semanticallyDefinedArithmeticGodelPerimetralCorrespondence
    theory

def publicSemanticallyDefinedArithmeticGodelConclusion
    (theory :
      StrongPerimetralTurning.SemanticallyDefinedProofArithmeticTheory) :
    StrongPerimetralTurning.SemanticallyDefinedArithmeticGodelPerimetralConclusion
      theory :=
  StrongPerimetralTurning.semanticallyDefinedArithmeticGodelPerimetralConclusion
    theory

def publicSemanticallyDefinedArithmeticGodelDiagnostic
    (theory :
      StrongPerimetralTurning.SemanticallyDefinedProofArithmeticTheory) :
    StrongPerimetralTurning.SemanticallyDefinedArithmeticGodelDiagnostic
      theory :=
  StrongPerimetralTurning.semanticallyDefinedArithmeticGodelDiagnostic theory

def publicSemanticallyDefinedArithmeticGodelNegationRejection
    (theory :
      StrongPerimetralTurning.SemanticallyDefinedProofArithmeticTheory) :
    StrongPerimetralTurning.CheckedArithmeticProof
        theory.encodeSentence theory.proofCheck
        (StrongPerimetralTurning.FirstOrderArithmeticFormula.negation
          (publicSemanticallyDefinedArithmeticGodelConclusion theory).correspondence.effective.execution.exit.witness.production.sentence) →
      Empty :=
  (publicSemanticallyDefinedArithmeticGodelConclusion
    theory).producedNegationHasNoCheckedDerivation

def publicSemanticallyDefinedArithmeticRejectsProoflessChecker
    (theory :
      StrongPerimetralTurning.SemanticallyDefinedProofArithmeticTheory)
    (proofless :
      (proofCode sentenceCode : Nat) →
        theory.proofCheck proofCode sentenceCode = false) : Empty :=
  theory.rejectProoflessChecker proofless

def publicHeytingArithmeticEffectiveGodelSystem :=
  RelationalPerimeter.HeytingArithmetic.heytingArithmeticEffectiveGodelSystem

def publicHeytingArithmeticGodelCorrespondence :=
  RelationalPerimeter.HeytingArithmetic.heytingArithmeticGodelPerimetralCorrespondence

def publicHeytingArithmeticCausalParticipation :=
  RelationalPerimeter.HeytingArithmetic.heytingArithmeticCausalParticipation

def publicHeytingArithmeticExecutedOccurrenceCorrespondence :=
  RelationalPerimeter.HeytingArithmetic.heytingArithmeticExecutedOccurrenceCorrespondence

def publicHeytingArithmeticStrictContinuation :=
  RelationalPerimeter.HeytingArithmetic.heytingArithmeticStrictContinuation

def publicHeytingArithmeticCausalClosureRejection :=
  RelationalPerimeter.HeytingArithmetic.heytingArithmeticCausalClosureIsImpossible

def publicHeytingArithmeticNegationRejection :=
  RelationalPerimeter.HeytingArithmetic.heytingArithmeticProducedNegationIsUnprovable

theorem publicIndependentAddressingBound
    (input : Nat) (addressing : IndependentProfileAddressing input) :
    2 ^ (input + 1) <= addressing.slotCount :=
  independent_profile_addressing_requires_exponential_slots input addressing

theorem publicNormalizerProgramSize (input : Nat) :
    (constitutiveNormalizerSuccinctnessEvidence input).program.program.codeSize =
      input + 1 :=
  constitutive_normalizer_program_code_size_exact input

theorem publicNormalizerMetricAgreement (input : Nat) :
    let certificate := constitutiveNormalizerSuccinctnessEvidence input
    certificate.program.program.codeSize =
      compiledLocalSize
        (authoritativeNormalizerProgramReturnedCodes
          certificate.program.program certificate.program.authoritative) :=
  constitutive_normalizer_code_metric_exact input

end RelationalPerimeter.Tests.PublicRootImport

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Tests.PublicRootImport.publicEvidence
#print axioms RelationalPerimeter.Tests.PublicRootImport.publicFamily
#print axioms RelationalPerimeter.Tests.PublicRootImport.publicSuccinctnessEvidence
#print axioms RelationalPerimeter.Tests.PublicRootImport.publicArithmeticGodelCorrespondence
#print axioms RelationalPerimeter.Tests.PublicRootImport.publicArithmeticGodelCausalParticipation
#print axioms RelationalPerimeter.Tests.PublicRootImport.publicArithmeticGodelExecutedOccurrenceCorrespondence
#print axioms RelationalPerimeter.Tests.PublicRootImport.publicArithmeticGodelCausalClosureRejection
#print axioms RelationalPerimeter.Tests.PublicRootImport.publicArithmeticGodelDirectedClosureRejection
#print axioms RelationalPerimeter.Tests.PublicRootImport.publicSemanticallyDefinedArithmeticGodelCorrespondence
#print axioms RelationalPerimeter.Tests.PublicRootImport.publicSemanticallyDefinedArithmeticGodelConclusion
#print axioms RelationalPerimeter.Tests.PublicRootImport.publicSemanticallyDefinedArithmeticGodelDiagnostic
#print axioms RelationalPerimeter.Tests.PublicRootImport.publicSemanticallyDefinedArithmeticGodelNegationRejection
#print axioms RelationalPerimeter.Tests.PublicRootImport.publicSemanticallyDefinedArithmeticRejectsProoflessChecker
#print axioms RelationalPerimeter.Tests.PublicRootImport.publicHeytingArithmeticEffectiveGodelSystem
#print axioms RelationalPerimeter.Tests.PublicRootImport.publicHeytingArithmeticGodelCorrespondence
#print axioms RelationalPerimeter.Tests.PublicRootImport.publicHeytingArithmeticCausalParticipation
#print axioms RelationalPerimeter.Tests.PublicRootImport.publicHeytingArithmeticExecutedOccurrenceCorrespondence
#print axioms RelationalPerimeter.Tests.PublicRootImport.publicHeytingArithmeticStrictContinuation
#print axioms RelationalPerimeter.Tests.PublicRootImport.publicHeytingArithmeticCausalClosureRejection
#print axioms RelationalPerimeter.Tests.PublicRootImport.publicHeytingArithmeticNegationRejection
#print axioms RelationalPerimeter.Tests.PublicRootImport.publicIndependentAddressingBound
#print axioms RelationalPerimeter.Tests.PublicRootImport.publicNormalizerProgramSize
#print axioms RelationalPerimeter.Tests.PublicRootImport.publicNormalizerMetricAgreement
/- AXIOM_AUDIT_END -/
