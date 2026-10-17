import RelationalPerimeter.Constitution.Reals.ReciprocalRuntime

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Reciprocal closure of the same real carrier

This is the concrete CertifiedService realization, not an assumed interface.
Both certificate fields are derived from the reciprocal producer. Numerical
unit laws and downstream presentation/carrier transports are separate work.
-/
namespace RelationalPerimeter.Constitution.Reals.RelationalRealInverse
open StrongPerimetralTurning HeterogeneousRealRuntime RelationalRealAddition RelationalRealOrder
variable {P : CircularPresentation} {baseDepth : Nat}

def certificate (source : Real P baseDepth) (witness : Apartness source (zero P baseDepth)) : CertifiedService P baseDepth where
  service := ReciprocalRuntime.inverseEnvironment source witness
  coherence := ReciprocalRuntime.inverseCoherent source witness
  uniform archive p step := ReciprocalRuntime.inverseUniform source witness step (canonicalStep _ p)

def inverse (source : Real P baseDepth) (witness : Apartness source (zero P baseDepth)) : Real P baseDepth :=
  .certified (certificate source witness)

theorem environment_inverse (source : Real P baseDepth) (witness : Apartness source (zero P baseDepth)) :
    environment (inverse source witness) = ReciprocalRuntime.inverseEnvironment source witness := rfl

theorem source_anchor (source : Real P baseDepth) (witness : Apartness source (zero P baseDepth)) :
    (environment (inverse source witness)).initialArchive.source = ReciprocalDomain.sourceSuccessor witness := rfl

def inverse_coherent (source : Real P baseDepth) (witness : Apartness source (zero P baseDepth)) :
    Coherent (environment (inverse source witness)) := ReciprocalRuntime.inverseCoherent source witness

theorem packetSameTarget {source : Real P baseDepth} {witness : Apartness source (zero P baseDepth)}
    {archive : (environment (inverse source witness)).Archive} {p : Nat}
    (step : Step (environment (inverse source witness)) archive p) :
    step.code = step.resource.action.action.result.code ∧
      step.next.last = some step.resource.action.action.result.code ∧
      step.liveEvent.code = step.resource.action.action.result.code := by
  dsimp only [inverse, certificate, environment, ReciprocalRuntime.inverseEnvironment] at archive step
  have exact : step.code = step.resource.action.action.result.code := step.resource.code_is_action
  exact ⟨exact, congrArg some exact, exact⟩

theorem richEventReflectsArchive {source : Real P baseDepth} {witness : Apartness source (zero P baseDepth)}
    {first second : (environment (inverse source witness)).Archive} (p : Nat)
    (same : (richContract (environment (inverse source witness))).event first p =
      (richContract (environment (inverse source witness))).event second p) : first = second :=
  congrArg ReciprocalRuntime.RichEvent.archive same

end RelationalPerimeter.Constitution.Reals.RelationalRealInverse

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealInverse.certificate
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealInverse.inverse
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealInverse.environment_inverse
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealInverse.source_anchor
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealInverse.inverse_coherent
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealInverse.packetSameTarget
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealInverse.richEventReflectsArchive
/- AXIOM_AUDIT_END -/
