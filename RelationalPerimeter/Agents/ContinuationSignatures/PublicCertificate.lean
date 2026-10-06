import RelationalPerimeter.Agents.ContinuationSignatures.FusedExecution
import RelationalPerimeter.Computation.ConstitutiveSearch.EndogenousDecomposition.ProducedProfileContinuation

/-! Closed certificate for the declared read-only role contract. General agent
memory minimality, quantum continuations, and total-cost bounds are not claims
of this certificate. The rich execution is evidence, not restart memory. -/
set_option genInjectivity false
set_option maxHeartbeats 2000000
namespace ConstitutiveSearch.ContinuationSignatures
open SAT EndogenousDecomposition

variable {state : CausalConstitutiveState} {run : CausalConstitutiveStageExecution state}

theorem varied_read_negated (role : RelationalConstitutiveRoleStage run) :
    roleRead role (freeVariable run) (variedLeftSource role) =
      !(roleRead role (freeVariable run) (leftSource role)) := by
  change Assignment.flipAt run.selected (Assignment.flipAt (freeVariable run)
    run.sourceContinuation.1) (freeVariable run) =
      !(Assignment.flipAt run.selected run.sourceContinuation.1 (freeVariable run))
  rw [Assignment.flipAt_other _ _ _ (freeVariable_selected_ne run),
    Assignment.flipAt_other _ _ _ (freeVariable_selected_ne run), Assignment.flipAt_selected]

def roleReadCoverage (role : RelationalConstitutiveRoleStage run) :
    PositiveCoverage (roleReadRealization role (freeVariable run)) where
  representative value :=
    if same : roleRead role (freeVariable run) (leftSource role) = value then
      ⟨leftSource role, same⟩
    else
      ⟨variedLeftSource role, by
        change roleRead role (freeVariable run) (variedLeftSource role) = value
        rw [varied_read_negated]
        cases actual : roleRead role (freeVariable run) (leftSource role) <;>
          cases value <;> first | rfl | exact False.elim (same actual)⟩

structure LocalSignatureCertificate (role : RelationalConstitutiveRoleStage run) where
  private mk ::
  grouped : produceRoleSignature role (freeVariable run) (leftSource role) =
    produceRoleSignature role (freeVariable run) (pairedRightSource role)
  sourcesDistinct : leftSource role ≠ pairedRightSource role
  threeSourcesDistinct : leftSource role ≠ pairedRightSource role ∧
    variedLeftSource role ≠ leftSource role ∧ variedLeftSource role ≠ pairedRightSource role
  separator : FutureSeparator (roleReadContract role (freeVariable run))
    (variedLeftSource role) (leftSource role)
  exact : ∀ left right,
    produceRoleSignature role (freeVariable run) left = produceRoleSignature role (freeVariable run) right ↔
      FutureEquivalent (roleReadContract role (freeVariable run)) left right
  necessary : ∀ {Memory : Type} (realization : ExactRealization (roleReadContract role (freeVariable run)) Memory)
    (left right : AcceptedRoleSource role), realization.project left = realization.project right →
      produceRoleSignature role (freeVariable run) left = produceRoleSignature role (freeVariable run) right
  coverage : PositiveCoverage (roleReadRealization role (freeVariable run))

def localCertificate (role : RelationalConstitutiveRoleStage run) : LocalSignatureCertificate role where
  grouped := paired_signatures_equal role _
  sourcesDistinct := paired_sources_distinct role
  threeSourcesDistinct := three_sources_distinct role
  separator := varied_separator role
  exact := produceRoleSignature_exact role _
  necessary := fun realization _ _ same => produceRoleSignature_minimal role _ realization same
  coverage := roleReadCoverage role

def publicSignedExecution (input : Nat) (mode : PayloadMode) :=
  executeSigned (resolutionLength input) (ProducedContinuation.publicOrigin input) mode

theorem publicSignedExecution_erases (input : Nat) (mode : PayloadMode) :
    (publicSignedExecution input mode).core =
      MasterResources.execute (resolutionLength input) (ProducedContinuation.publicOrigin input) :=
  executeSigned_erases _ _ _

theorem publicSignedExecution_grouped (input : Nat) :
    (publicSignedExecution input .left).readings = (publicSignedExecution input .pairedRight).readings :=
  executeSigned_pair_readings _ _

theorem publicSignedExecution_distinguished (input : Nat) :
    (publicSignedExecution input .variedLeft).readings.head? ≠
      (publicSignedExecution input .left).readings.head? :=
  executeSigned_varied_head input _

theorem publicSignedExecution_linear_data (input : Nat) (mode : PayloadMode) :
    (publicSignedExecution input mode).readings.length = input + 1 :=
  executeSigned_readings_length _ _ _

/-- Runtime output consists only of evaluated bits. Rich supports and source
payloads are not fields of this value. No physical memory bound is asserted. -/
def publicSignatureMemory (input : Nat) (mode : PayloadMode) : List Bool :=
  executeReadings (resolutionLength input) (ProducedContinuation.publicOrigin input) mode

theorem publicSignatureMemory_exact (input : Nat) (mode : PayloadMode) :
    publicSignatureMemory input mode = (publicSignedExecution input mode).readings :=
  executeReadings_exact _ _ _

/-- Closed scientific witness for this read-only consumer, separate from the
data-only runtime output. The exact executor and head independence are pinned
alongside the local exactness, necessity, and separating continuation. -/
structure PublicSignatureCertificate (input : Nat) (mode : PayloadMode) : Type 3 where
  private mk ::
  execution : SignatureExecutionResult (resolutionLength input) (ProducedContinuation.publicOrigin input)
  executionExact : execution = publicSignedExecution input mode
  memoryExact : publicSignatureMemory input mode = execution.readings
  erasure : execution.core =
    MasterResources.execute (resolutionLength input) (ProducedContinuation.publicOrigin input)
  headExact : execution.readings.head? =
    some (signatureRead (cursorSignature (ProducedContinuation.publicOrigin input) mode))
  horizonIndependent : ∀ first second,
    (executeSigned (first + 1) (ProducedContinuation.publicOrigin input) mode).readings.head? =
      (executeSigned (second + 1) (ProducedContinuation.publicOrigin input) mode).readings.head?
  localWitness : LocalSignatureCertificate (cursorRole (ProducedContinuation.publicOrigin input))

def publicSignatureCertificate (input : Nat) (mode : PayloadMode) :
    PublicSignatureCertificate input mode where
  execution := publicSignedExecution input mode
  executionExact := rfl
  memoryExact := publicSignatureMemory_exact input mode
  erasure := publicSignedExecution_erases input mode
  headExact := executeSigned_head_exact input _ mode
  horizonIndependent := fun first second => executeSigned_head_horizon_independent first second _ mode
  localWitness := localCertificate _

end ConstitutiveSearch.ContinuationSignatures
/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.ContinuationSignatures.roleReadCoverage
#print axioms ConstitutiveSearch.ContinuationSignatures.localCertificate
#print axioms ConstitutiveSearch.ContinuationSignatures.publicSignedExecution
#print axioms ConstitutiveSearch.ContinuationSignatures.publicSignedExecution_erases
#print axioms ConstitutiveSearch.ContinuationSignatures.publicSignedExecution_grouped
#print axioms ConstitutiveSearch.ContinuationSignatures.publicSignedExecution_distinguished
#print axioms ConstitutiveSearch.ContinuationSignatures.publicSignedExecution_linear_data
#print axioms ConstitutiveSearch.ContinuationSignatures.publicSignatureMemory
#print axioms ConstitutiveSearch.ContinuationSignatures.publicSignatureMemory_exact
#print axioms ConstitutiveSearch.ContinuationSignatures.publicSignatureCertificate
/- AXIOM_AUDIT_END -/
