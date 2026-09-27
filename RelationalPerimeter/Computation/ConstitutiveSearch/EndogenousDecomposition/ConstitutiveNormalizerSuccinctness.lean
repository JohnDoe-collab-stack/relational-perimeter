import RelationalPerimeter.Computation.ConstitutiveSearch.EndogenousDecomposition.ConstitutiveNormalizerProgram
import RelationalPerimeter.Computation.ConstitutiveSearch.EndogenousDecomposition.IndependentProfileAddressing
import RelationalPerimeter.Computation.ConstitutiveSearch.EndogenousDecomposition.MeasuredAccounting

/-!
# Constitutive normalizer succinctness

The public execution constitutes an exact Boolean structural-profile carrier.
Any interface retaining those profiles as independently addressable cases needs
at least `2^(input+1)` finite slots.  The same execution produces an
authoritative normalizer program with exactly `input+1` transport atoms, and
that program acts on every accepted structural payload exactly as the existing
normalizer does.

The comparison is deliberately typed and metric-specific.  It establishes a
succinct executed representation relative to independent finite profile
addressing; it does not claim a universal lower bound for every representation,
nor a general time- or memory-complexity separation.
-/

namespace ConstitutiveSearch.EndogenousDecomposition

set_option maxHeartbeats 800000

/-- The unique public dependent role history for one input. -/
abbrev PublicConstitutiveRoles (input : Nat) :=
  (executeConstitutiveResolution input).feedbackRoleHistory

/-- Closed certificate joining the exact structural case space, its finite
independent-addressing lower bound, and the authoritative executed normalizer.
The constructor is private so clients consume the built witness rather than
assembling causal fields independently. -/
structure ConstitutiveNormalizerSuccinctness (input : Nat) : Type 3 where
  private mk ::
  program :
    AuthoritativeConstitutiveNormalizerProgram
      (PublicConstitutiveRoles input)
  stageCountExact :
    operationalStageCount (PublicConstitutiveRoles input) = input + 1
  structuralCaseCountExact :
    structuralWidth (PublicConstitutiveRoles input) = 2 ^ (input + 1)
  pendingCaseCountExact :
    pendingWidth (PublicConstitutiveRoles input) = 2 ^ (input + 1)
  retainedCaseCountExact :
    executedWidth (PublicConstitutiveRoles input) = 1
  structuralComplete :
    forall profile,
      List.Mem profile (structuralFrontier (PublicConstitutiveRoles input))
  structuralNoDuplicates :
    (structuralFrontier (PublicConstitutiveRoles input)).Nodup
  pendingComplete :
    forall profile,
      List.Mem profile (pendingFrontier (PublicConstitutiveRoles input))
  pendingNoDuplicates :
    (pendingFrontier (PublicConstitutiveRoles input)).Nodup
  everyProfileAccepted :
    forall profile,
      StructuralAcceptedPayload (PublicConstitutiveRoles input) profile
  programInterpreterExact :
    forall profile payload,
      interpretConstitutiveNormalizerProgram program.program profile payload =
        normalizeStructuralAcceptedPayload
          (PublicConstitutiveRoles input) profile payload
  programReturnsExecutedCodes :
    authoritativeNormalizerProgramReturnedCodes
        program.program program.authoritative =
      (executeConstitutiveResolution input).history.returnedCodes
  programCodeSizeExact :
    program.program.codeSize = input + 1
  programCodeMetricExact :
    program.program.codeSize =
      compiledLocalSize
        (authoritativeNormalizerProgramReturnedCodes
          program.program program.authoritative)
  returnedCodeAtomCountExact :
    compiledLocalSize
        (authoritativeNormalizerProgramReturnedCodes
          program.program program.authoritative) = input + 1
  independentAddressingLowerBound :
    forall addressing : IndependentProfileAddressing
        (PublicConstitutiveRoles input),
      2 ^ (input + 1) <= addressing.slotCount
  derivedWidthReadoutBound :
    WidthTraceAtMost 2
      (executedWidthTrace (PublicConstitutiveRoles input))
  instrumentedWorkBound :
    (executeConstitutiveResolution input).instrumentedWork <=
      resolutionInstrumentedPolynomial.eval input

/-- Construct the certificate entirely from the public execution. -/
def publicConstitutiveNormalizerSuccinctness
    (input : Nat) : ConstitutiveNormalizerSuccinctness input := by
  let run := executeConstitutiveResolution input
  let roles : ThreadedConstitutiveRoleHistory run.constitutiveFeedbackHistory :=
    run.feedbackRoleHistory
  let program := buildAuthoritativeConstitutiveNormalizerProgram roles
  have stageCount : operationalStageCount roles = input + 1 :=
    operationalStageCount_eq_historyCount roles
  have structuralCount : structuralWidth roles = 2 ^ (input + 1) :=
    Eq.trans (structuralWidth_eq_two_pow_stageCount roles)
      (congrArg (fun count => 2 ^ count) stageCount)
  have pendingCount : pendingWidth roles = 2 ^ (input + 1) :=
    Eq.trans (pendingWidth_eq_two_pow_stageCount roles)
      (congrArg (fun count => 2 ^ count) stageCount)
  refine
    { program := program
      stageCountExact := stageCount
      structuralCaseCountExact := structuralCount
      pendingCaseCountExact := pendingCount
      retainedCaseCountExact := executedWidth_eq_one roles
      structuralComplete := structuralFrontier_complete roles
      structuralNoDuplicates := structuralFrontier_nodup roles
      pendingComplete := pendingFrontier_complete roles
      pendingNoDuplicates := pendingFrontier_nodup roles
      everyProfileAccepted := everyStructuralObligationHasAcceptedPayload roles
      programInterpreterExact := ?_
      programReturnsExecutedCodes := ?_
      programCodeSizeExact := ?_
      programCodeMetricExact := ?_
      returnedCodeAtomCountExact := ?_
      independentAddressingLowerBound := ?_
      derivedWidthReadoutBound := executedWidthTrace_le_two roles
      instrumentedWorkBound := run.instrumentedWork_polynomial_bound }
  · intro profile payload
    exact interpretAuthoritativeConstitutiveNormalizerProgram_exact
      program.program program.authoritative profile payload
  · exact Eq.trans
      (authoritativeNormalizerProgramReturnedCodes_exact
        program.program program.authoritative)
      (congrArg SequentialHistory.returnedCodes
        run.historyFromCausalExecution.symm)
  · exact Eq.trans
      (buildConstitutiveNormalizerProgram_codeSize roles)
      stageCount
  · exact authoritativeNormalizerProgram_codeSize_eq_compiledLocalSize
      program.program program.authoritative
  · exact Eq.trans
      (authoritativeNormalizerProgram_compiledSize_eq_stageCount
        program.program program.authoritative)
      stageCount
  · intro addressing
    exact Eq.mp
      (congrArg (fun width => width <= addressing.slotCount)
        (congrArg (fun count => 2 ^ count) stageCount))
      (independentProfileAddressing_slots_ge_two_pow_stageCount addressing)

/-- Exact raw-program metric: one stored transport atom per public stage. -/
theorem public_constitutive_normalizer_programCodeSize_exact (input : Nat) :
    (publicConstitutiveNormalizerSuccinctness input).program.program.codeSize =
      input + 1 :=
  (publicConstitutiveNormalizerSuccinctness input).programCodeSizeExact

/-- The raw dependent-program metric agrees exactly with `compiledLocalSize`
after authoritative erasure. -/
theorem public_constitutive_normalizer_codeMetric_exact (input : Nat) :
    let certificate := publicConstitutiveNormalizerSuccinctness input
    certificate.program.program.codeSize =
      compiledLocalSize
        (authoritativeNormalizerProgramReturnedCodes
          certificate.program.program certificate.program.authoritative) :=
  (publicConstitutiveNormalizerSuccinctness input).programCodeMetricExact

/-- Public lower bound for every independently addressing representation of
the exact structural profiles. -/
theorem public_independent_profile_slots_exponential (input : Nat)
    (addressing : IndependentProfileAddressing
      (PublicConstitutiveRoles input)) :
    2 ^ (input + 1) <= addressing.slotCount :=
  (publicConstitutiveNormalizerSuccinctness input).independentAddressingLowerBound
    addressing

/-- Exact code-atom size of the public authoritative normalizer. -/
theorem public_constitutive_normalizer_codeSize_exact (input : Nat) :
    let certificate := publicConstitutiveNormalizerSuccinctness input
    compiledLocalSize
        (authoritativeNormalizerProgramReturnedCodes
          certificate.program.program certificate.program.authoritative) =
      input + 1 :=
  (publicConstitutiveNormalizerSuccinctness input).returnedCodeAtomCountExact

/-- The public program computes the canonical normalizer for every profile and
accepted payload. -/
theorem public_constitutive_normalizer_interpreter_exact (input : Nat)
    (profile : StructuralObligation (PublicConstitutiveRoles input))
    (payload : StructuralAcceptedPayload
      (PublicConstitutiveRoles input) profile) :
    let certificate := publicConstitutiveNormalizerSuccinctness input
    interpretConstitutiveNormalizerProgram certificate.program.program
        profile payload =
      normalizeStructuralAcceptedPayload
        (PublicConstitutiveRoles input) profile payload :=
  (publicConstitutiveNormalizerSuccinctness input).programInterpreterExact
    profile payload

/-- The program erases to the exact code list returned by the public run. -/
theorem public_constitutive_normalizer_returns_executed_codes (input : Nat) :
    let certificate := publicConstitutiveNormalizerSuccinctness input
    authoritativeNormalizerProgramReturnedCodes
        certificate.program.program certificate.program.authoritative =
      (executeConstitutiveResolution input).history.returnedCodes :=
  (publicConstitutiveNormalizerSuccinctness input).programReturnsExecutedCodes

/-- The existing instrumented polynomial bound is carried by the same closed
public certificate; it is not inferred from the code-size comparison. -/
theorem public_constitutive_normalizer_instrumentedWork_bound (input : Nat) :
    (executeConstitutiveResolution input).instrumentedWork <=
      resolutionInstrumentedPolynomial.eval input :=
  (publicConstitutiveNormalizerSuccinctness input).instrumentedWorkBound

end ConstitutiveSearch.EndogenousDecomposition

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.EndogenousDecomposition.PublicConstitutiveRoles
#print axioms ConstitutiveSearch.EndogenousDecomposition.ConstitutiveNormalizerSuccinctness
#print axioms ConstitutiveSearch.EndogenousDecomposition.publicConstitutiveNormalizerSuccinctness
#print axioms ConstitutiveSearch.EndogenousDecomposition.public_constitutive_normalizer_programCodeSize_exact
#print axioms ConstitutiveSearch.EndogenousDecomposition.public_constitutive_normalizer_codeMetric_exact
#print axioms ConstitutiveSearch.EndogenousDecomposition.public_independent_profile_slots_exponential
#print axioms ConstitutiveSearch.EndogenousDecomposition.public_constitutive_normalizer_codeSize_exact
#print axioms ConstitutiveSearch.EndogenousDecomposition.public_constitutive_normalizer_interpreter_exact
#print axioms ConstitutiveSearch.EndogenousDecomposition.public_constitutive_normalizer_returns_executed_codes
#print axioms ConstitutiveSearch.EndogenousDecomposition.public_constitutive_normalizer_instrumentedWork_bound
/- AXIOM_AUDIT_END -/
