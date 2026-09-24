import RelationalPerimeter.Instances.GrowingFeedback

/-!
# Non-confirmatory executable trace

This file exposes one closed computation for inspection.  It is a smoke test,
not a proof: the general claims are carried by the theorems in the imported
modules and by the regression files under `Tests/`.
-/

namespace RelationalPerimeter.Smoke.EndogenousOperationalTrace

open RelationalPerimeter.Instances.GrowingReconstruction
open RelationalPerimeter.Instances.GrowingFeedback

/--
Stable observation of the stage-three run.  In order, the fields are:
candidate count, attempt count, failure count, reconstructed-relation flag,
absorbed-left result, retained-right result, next attempts with the produced
decision, and next attempts after forgetting that decision.
-/
def traceData : List Nat :=
  [ (candidates 3).length
  , (growingRun 3).attempts
  , (growingRun 3).failedAttempts
  , match (growingRun 3).relation? with
    | none => 0
    | some _relation => 1
  , stageReduction 3 (.inl 7)
  , stageReduction 3 (.inr 8)
  , (reconstructionFromState (retainedState 0)).attempts
  , (reconstructionFromState (forgottenState 0)).attempts
  ]

#eval IO.println ("SMOKE_TRACE_V1 data=" ++ toString traceData)

end RelationalPerimeter.Smoke.EndogenousOperationalTrace

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Smoke.EndogenousOperationalTrace.traceData
/- AXIOM_AUDIT_END -/
