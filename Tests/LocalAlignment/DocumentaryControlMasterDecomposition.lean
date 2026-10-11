import Tests.LocalAlignment.DocumentaryControlProducedImage
import Tests.LocalAlignment.DocumentaryControlRoleFormation
import RelationalPerimeter.Computation.ConstitutiveSearch.EndogenousDecomposition.PrefixLocalOperationalProduction

/-! Form the executed role and its license, map its actual constituted sources,
then deduplicate their actual image. No prescribed singleton replaces the map.
Role opening and positive occurrence formation use the retained endpoints. -/
set_option genInjectivity false
set_option maxHeartbeats 8000000
namespace ConstitutiveSearch.Agent.Local.Documentary.ControlMasterDecomposition
open SAT Extensive EndogenousDecomposition Control ControlBindings ControlMasterData

def outputCode {source : CausalConstitutiveState} {run : CausalConstitutiveStageExecution source}
    {role : RelationalConstitutiveRoleStage run} (atom : RoleStageAtom role)
    (occurrence : RoleConstitutedOccurrence role) : Code Label (Actual (producedRoleOutput atom occurrence)) :=
  .step .controlInspect (fun _ => eliminateRoleConstitutedOccurrence role occurrence
    (motive := fun occurrence => Code Label (Actual (producedRoleOutput atom occurrence)))
    ((ControlMeasuredTransport.mapCode run.selected atom.returnedRelation role.executedInput).bind
      (fun output => .done ⟨output.1, by rw [output.2]; rfl⟩))
    (.step .masterConstructionReturn (fun _ => .done ⟨role.completedOutput, rfl⟩)))

theorem output_finite {source : CausalConstitutiveState} {run : CausalConstitutiveStageExecution source}
    {role : RelationalConstitutiveRoleStage run} (atom : RoleStageAtom role)
    (occurrence : RoleConstitutedOccurrence role) : Finite (outputCode atom occurrence) := by
  apply finite_step
  have canonical := roleConstitutedOccurrence_roundTrip occurrence
  cases found : occurrence.position with
  | left =>
    rw [found] at canonical
    cases canonical
    apply finite_bind (ControlMeasuredTransport.map_finite _ _ _); intro output; exact finite_done _
  | right =>
    rw [found] at canonical
    cases canonical
    exact finite_step _ _ (finite_done _)

def compareCode {source : CausalConstitutiveState} {run : CausalConstitutiveStageExecution source}
    {role : RelationalConstitutiveRoleStage run} {atom : RoleStageAtom role}
    (license : ExecutedRoleReductionLicense role atom)
    (left right : ProducedOutputImage.Value (roleOpeningFiniteCarrier role) (producedRoleOutput atom)) :
    Code Label (Actual (ProducedOutputImage.decEq (roleOpeningFiniteCarrier role)
      (producedRoleOutput atom) (producedRoleOutputs_converge license) left right)) :=
  .step .naturalComparison (fun _ => .done
    ⟨.isTrue (ProducedOutputImage.value_eq (producedRoleOutputs_converge license) left right), rfl⟩)

def imageCode {source : CausalConstitutiveState} {run : CausalConstitutiveStageExecution source}
    {role : RelationalConstitutiveRoleStage run} {atom : RoleStageAtom role}
    (license : ExecutedRoleReductionLicense role atom) : Code Label (Actual (producedRoleOutputRegime license)) :=
  ControlProducedImage.code (roleOpeningFiniteCarrier role) (producedRoleOutput atom) (outputCode atom)
    (ProducedOutputImage.decEq (roleOpeningFiniteCarrier role) (producedRoleOutput atom)
      (producedRoleOutputs_converge license)) (compareCode license)

theorem image_finite {source : CausalConstitutiveState} {run : CausalConstitutiveStageExecution source}
    {role : RelationalConstitutiveRoleStage run} {atom : RoleStageAtom role}
    (license : ExecutedRoleReductionLicense role atom) : Finite (imageCode license) :=
  ControlProducedImage.finite (roleOpeningFiniteCarrier role) (producedRoleOutput atom) (outputCode atom)
    (output_finite atom) _ (compareCode license) (fun _ _ => finite_step _ _ (finite_done _))

def roleCode {source : CausalConstitutiveState} (stage : CausalConstitutiveStageExecution source) :
    Code Label (Actual (relationalConstitutiveRoleStage stage)) :=
  ControlRoleFormation.roleCode stage

def licenseFromParts {source : CausalConstitutiveState} {run : CausalConstitutiveStageExecution source}
    (role : RelationalConstitutiveRoleStage run)
    (left : RoleConstitutedOccurrence role) (leftActual : left = roleConstitutedOccurrenceAt role .left)
    (leftConstitution : RoleConstitutionEvidence role left)
    (leftConstitutionActual : leftConstitution = roleConstitutionEvidence role left)
    (right : RoleConstitutedOccurrence role) (rightActual : right = roleConstitutedOccurrenceAt role .right)
    (rightConstitution : RoleConstitutionEvidence role right)
    (_rightConstitutionActual : rightConstitution = roleConstitutionEvidence role right) :
    ExecutedRoleReductionLicense role (compileRoleStageAtom role) := by
  constructor
  case transformedOccurrence => exact left
  case transformedOccurrenceExact => exact leftActual
  case transformedConstitution => exact leftConstitution
  case retainedOccurrence => exact right
  case retainedOccurrenceExact => exact rightActual
  case retainedConstitution => exact rightConstitution
  case transformedOutputExact =>
    cases leftConstitutionActual; cases leftActual
    exact (executedRoleReductionLicense role).transformedOutputExact
  case preservesCriterion => exact (compileRoleStageAtom role).preservesAccepted
  case transformedAccepted =>
    cases leftConstitutionActual; cases leftActual
    exact (executedRoleReductionLicense role).transformedAccepted
  case retainedAccepted => exact role.preservation
  case actionChangesSource => exact (executedRoleReductionLicense role).actionChangesSource
  case occurrencesRemainDistinct =>
    cases leftActual; cases rightActual
    exact (executedRoleReductionLicense role).occurrencesRemainDistinct

theorem license_from_parts_actual {source : CausalConstitutiveState} {run : CausalConstitutiveStageExecution source}
    (role : RelationalConstitutiveRoleStage run)
    (left : RoleConstitutedOccurrence role) (leftActual : left = roleConstitutedOccurrenceAt role .left)
    (leftConstitution : RoleConstitutionEvidence role left)
    (leftConstitutionActual : leftConstitution = roleConstitutionEvidence role left)
    (right : RoleConstitutedOccurrence role) (rightActual : right = roleConstitutedOccurrenceAt role .right)
    (rightConstitution : RoleConstitutionEvidence role right)
    (rightConstitutionActual : rightConstitution = roleConstitutionEvidence role right) :
    licenseFromParts role left leftActual leftConstitution leftConstitutionActual right rightActual rightConstitution
      rightConstitutionActual = executedRoleReductionLicense role := by
  cases leftConstitutionActual; cases rightConstitutionActual; cases leftActual; cases rightActual; rfl

def licenseCode {source : CausalConstitutiveState} {run : CausalConstitutiveStageExecution source}
    (role : RelationalConstitutiveRoleStage run) (endpoints : ControlRoleFormation.Endpoints run) :
    Code Label (Actual (executedRoleReductionLicense role)) :=
  (ControlRoleFormation.identityCode role endpoints .left).bind (fun left =>
  (ControlRoleFormation.evidenceCode role left.1).bind (fun leftConstitution =>
  (ControlRoleFormation.identityCode role endpoints .right).bind (fun right =>
  (ControlRoleFormation.evidenceCode role right.1).bind (fun rightConstitution =>
    .step .masterConstructionReturn (fun _ => .done
      ⟨licenseFromParts role left.1 left.2 leftConstitution.1 leftConstitution.2
        right.1 right.2 rightConstitution.1 rightConstitution.2,
        license_from_parts_actual _ _ _ _ _ _ _ _ _⟩)))))

theorem license_bounded {source : CausalConstitutiveState} {run : CausalConstitutiveStageExecution source}
    (role : RelationalConstitutiveRoleStage run) (endpoints : ControlRoleFormation.Endpoints run) :
    Within (licenseCode role endpoints) (8 + (1 + (8 + (1 + 1)))) := by
  apply within_bind (ControlRoleFormation.identity_bounded role endpoints .left); intro left
  apply within_bind (ControlRoleFormation.evidence_bounded role left.1); intro leftConstitution
  apply within_bind (more := 2) (ControlRoleFormation.identity_bounded role endpoints .right); intro right
  apply within_bind (more := 1) (ControlRoleFormation.evidence_bounded role right.1); intro rightConstitution
  exact within_step _ _ (within_done _)

def decompositionFromParts {source : CausalConstitutiveState} (stage : CausalConstitutiveStageExecution source)
    (role : RelationalConstitutiveRoleStage stage) (roleActual : role = relationalConstitutiveRoleStage stage)
    (license : ExecutedRoleReductionLicense role (compileRoleStageAtom role))
    (_licenseActual : license = executedRoleReductionLicense role)
    (image : ObligationRegime (roleOpeningFiniteCarrier role)) (imageActual : image = producedRoleOutputRegime license) :
    ExecutedStageDecomposition stage := by
  constructor
  case role => exact role
  case roleExact => exact roleActual
  case license => exact license
  case outputRegime => exact image
  case outputRegimeExact => exact imageActual

theorem decomposition_from_parts_actual {source : CausalConstitutiveState} (stage : CausalConstitutiveStageExecution source)
    (role : RelationalConstitutiveRoleStage stage) (roleActual : role = relationalConstitutiveRoleStage stage)
    (license : ExecutedRoleReductionLicense role (compileRoleStageAtom role))
    (licenseActual : license = executedRoleReductionLicense role)
    (image : ObligationRegime (roleOpeningFiniteCarrier role)) (imageActual : image = producedRoleOutputRegime license) :
    decompositionFromParts stage role roleActual license licenseActual image imageActual = executedStageDecomposition stage := by
  cases roleActual; cases licenseActual; cases imageActual; rfl

def decompositionCode {source : CausalConstitutiveState} (stage : CausalConstitutiveStageExecution source)
    (endpoints : ControlRoleFormation.Endpoints stage) :
    Code Label (Actual (executedStageDecomposition stage)) :=
  (roleCode stage).bind (fun role => (licenseCode role.1 endpoints).bind (fun license =>
    (imageCode license.1).bind (fun image => .step .masterConstructionReturn (fun _ => .done
      ⟨decompositionFromParts stage role.1 role.2 license.1 license.2 image.1 image.2,
        decomposition_from_parts_actual _ _ _ _ _ _ _⟩))))

theorem decomposition_finite {source : CausalConstitutiveState} (stage : CausalConstitutiveStageExecution source)
    (endpoints : ControlRoleFormation.Endpoints stage) : Finite (decompositionCode stage endpoints) := by
  apply finite_bind
  · obtain ⟨value, labels, trace, _⟩ := ControlRoleFormation.role_bounded stage
    exact ⟨value, labels, trace⟩
  · intro role
    apply finite_bind
    · obtain ⟨value, labels, trace, _⟩ := license_bounded role endpoints
      exact ⟨value, labels, trace⟩
    · intro license
      apply finite_bind (image_finite _); intro image; exact finite_step _ _ (finite_done _)

def fromParts {source : CausalConstitutiveState} (context : ConstitutedOperationalPrefix source)
    (stage : CausalConstitutiveStageExecution source) (decomposition : ExecutedStageDecomposition stage)
    (actual : decomposition = executedStageDecomposition stage) : ExecutedStageOperationalProduction context stage := by
  constructor
  case priorContext => exact context
  case priorContextExact => rfl
  case decomposition => exact decomposition
  case decompositionExact => exact actual

theorem from_parts_actual {source : CausalConstitutiveState} (context : ConstitutedOperationalPrefix source)
    (stage : CausalConstitutiveStageExecution source) (decomposition : ExecutedStageDecomposition stage)
    (actual : decomposition = executedStageDecomposition stage) :
    fromParts context stage decomposition actual = prefixLocalOperationalProducer context stage := by cases actual; rfl

def code {source : CausalConstitutiveState} (context : ConstitutedOperationalPrefix source)
    (stage : CausalConstitutiveStageExecution source) (endpoints : ControlRoleFormation.Endpoints stage) :
    Code Label (Actual (prefixLocalOperationalProducer context stage)) :=
  .step .masterDecompose (fun _ => (decompositionCode stage endpoints).bind (fun decomposition =>
    .step .masterConstructionReturn (fun _ => .done
      ⟨fromParts context stage decomposition.1 decomposition.2, from_parts_actual _ _ _ _⟩)))

theorem finite {source : CausalConstitutiveState} (context : ConstitutedOperationalPrefix source)
    (stage : CausalConstitutiveStageExecution source) (endpoints : ControlRoleFormation.Endpoints stage) :
    Finite (code context stage endpoints) := by
  apply finite_step; apply finite_bind (decomposition_finite _ _); intro decomposition
  exact finite_step _ _ (finite_done _)

end ConstitutiveSearch.Agent.Local.Documentary.ControlMasterDecomposition

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMasterDecomposition.outputCode
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMasterDecomposition.output_finite
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMasterDecomposition.compareCode
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMasterDecomposition.imageCode
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMasterDecomposition.image_finite
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMasterDecomposition.roleCode
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMasterDecomposition.licenseFromParts
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMasterDecomposition.license_from_parts_actual
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMasterDecomposition.licenseCode
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMasterDecomposition.license_bounded
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMasterDecomposition.decompositionFromParts
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMasterDecomposition.decomposition_from_parts_actual
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMasterDecomposition.decompositionCode
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMasterDecomposition.decomposition_finite
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMasterDecomposition.fromParts
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMasterDecomposition.from_parts_actual
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMasterDecomposition.code
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlMasterDecomposition.finite
/- AXIOM_AUDIT_END -/
