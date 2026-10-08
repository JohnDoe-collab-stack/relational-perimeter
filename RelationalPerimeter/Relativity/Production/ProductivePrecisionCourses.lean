import RelationalPerimeter.Relativity.Production.ProductiveWindowCompleteness

/-!
# Coherent finite courses of produced precision windows

Each local request receives a realized certificate, produces one extension
from its stored prefix, and intersects its actual precision window with the
received constraint. The same produced bracket satisfies both conditions.
The forward runner passes this certificate to the next request. Its head
has no future parameter. These are instrumental courses, not a physical
domain, an erasure permission, or a bound on the existing producer's cost.
-/
set_option genInjectivity false
namespace RelationalPerimeter.Relativity.Production
open Arithmetic Analysis

structure ProductivePrecisionContinuation {source presentation coarse}
    (received : @ProductiveWindowCertificate source presentation coarse)
    (precision : Precision) where
  window : ReadingWindow
  certificate : ProductiveWindowCertificate presentation window
  refinement : WindowRefinement coarse window
  diameter : Rational.Le window.span precision.value
  depthExact : certificate.depth = received.depth + precision.half.denominator
  runExact : certificate.realization =
    received.realization.evolve presentation.rule precision.half.denominator

/-- Request from the actual received prefix. Reindex its returned certificate
in the original family by a proof, without realizing that family's origin. -/
def ProductiveWindowCertificate.continuePrecision {source presentation window}
    (received : @ProductiveWindowCertificate source presentation window)
    (precision : Precision) : ProductivePrecisionContinuation received precision := by
  let current : RelativePathPresentation source := ⟨received.realization, presentation.rule⟩
  let request := current.requestWindow precision
  have exactRun : request.certificate.realization =
      presentation.realize (received.depth + precision.half.denominator) :=
    (congrArg (fun run => run.evolve presentation.rule precision.half.denominator)
      received.realizationExact).trans
      (relative_evolution_compose presentation.stored presentation.rule
        received.depth precision.half.denominator)
  have bounds := relative_evolution_brackets received.realization presentation.rule
    precision.half.denominator
  have oldInside : window.BracketContains request.certificate.realization.state.reading :=
    ⟨rational_strict_le received.inside.1 bounds.1,
      rational_le_strict bounds.2 received.inside.2⟩
  have lower := window_intersection_contains (bracket_contains_endpoints oldInside).1
    (bracket_contains_endpoints request.certificate.inside).1
  have upper := window_intersection_contains (bracket_contains_endpoints oldInside).2
    (bracket_contains_endpoints request.certificate.inside).2
  exact ⟨window.intersection request.window,
    ⟨received.depth + precision.half.denominator, request.certificate.realization,
      exactRun, lower.1, upper.2⟩,
    window_intersection_left _ _,
    Rational.le_trans (window_intersection_right _ _).span_le request.diameter, rfl, rfl⟩

theorem productive_precision_continuation_uses_the_received_prefix {source presentation window}
    (received : @ProductiveWindowCertificate source presentation window) (precision : Precision) :
    (received.continuePrecision precision).certificate.realization =
      received.realization.evolve presentation.rule precision.half.denominator := rfl

theorem productive_precision_continuation_depth {source presentation window}
    (received : @ProductiveWindowCertificate source presentation window) (precision : Precision) :
    (received.continuePrecision precision).certificate.depth =
      received.depth + precision.half.denominator := rfl

structure ProductiveWindowEndpoint {source} (presentation : RelativePathPresentation source) where
  window : ReadingWindow
  certificate : ProductiveWindowCertificate presentation window

inductive ProductivePrecisionCourse {source} (presentation : RelativePathPresentation source) :
    {window : ReadingWindow} → ProductiveWindowCertificate presentation window → List Precision → Type where
  | done {window} (received : ProductiveWindowCertificate presentation window) :
      ProductivePrecisionCourse presentation received []
  | step {window precision requests} {received : ProductiveWindowCertificate presentation window}
      (head : ProductivePrecisionContinuation received precision)
      (tail : ProductivePrecisionCourse presentation head.certificate requests) :
      ProductivePrecisionCourse presentation received (precision :: requests)

def ProductiveWindowCertificate.runPrecisions {source presentation window}
    (received : @ProductiveWindowCertificate source presentation window) :
    (requests : List Precision) → ProductivePrecisionCourse presentation received requests
  | [] => .done received
  | precision :: rest =>
      let head := received.continuePrecision precision
      let tail := head.certificate.runPrecisions rest
      .step head tail

def ProductivePrecisionCourse.endpoint {source presentation window received requests}
    (course : @ProductivePrecisionCourse source presentation window received requests) :
    ProductiveWindowEndpoint presentation :=
  match course with
  | .done certificate => ⟨_, certificate⟩
  | .step _ tail => tail.endpoint

def ProductivePrecisionCourse.headProduction {source presentation window received precision requests}
    (course : @ProductivePrecisionCourse source presentation window received (precision :: requests)) :
    ProductivePrecisionContinuation received precision :=
  match course with
  | .step head _ => head

theorem productive_precision_head_exact {source presentation window}
    (received : @ProductiveWindowCertificate source presentation window)
    (precision : Precision) (future : List Precision) :
    (received.runPrecisions (precision :: future)).headProduction =
      received.continuePrecision precision := rfl

theorem productive_precision_head_horizon_independent {source presentation window}
    (received : @ProductiveWindowCertificate source presentation window)
    (precision : Precision) (firstFuture secondFuture : List Precision) :
    (received.runPrecisions (precision :: firstFuture)).headProduction =
      (received.runPrecisions (precision :: secondFuture)).headProduction := rfl

def precisionCourseSteps : List Precision → Nat
  | [] => 0
  | precision :: rest => precision.half.denominator + precisionCourseSteps rest

theorem ProductivePrecisionCourse.depthExact {source presentation window received requests}
    (course : @ProductivePrecisionCourse source presentation window received requests) :
    course.endpoint.certificate.depth = received.depth + precisionCourseSteps requests := by
  induction course with
  | done certificate => exact (Nat.add_zero _).symm
  | step head tail ih =>
      change tail.endpoint.certificate.depth = _
      rw [ih, head.depthExact]
      exact Nat.add_assoc _ _ _

theorem ProductivePrecisionCourse.runExact {source presentation window received requests}
    (course : @ProductivePrecisionCourse source presentation window received requests) :
    course.endpoint.certificate.realization =
      received.realization.evolve presentation.rule (precisionCourseSteps requests) := by
  induction course with
  | done certificate => rfl
  | step head tail ih =>
      change tail.endpoint.certificate.realization = _
      rw [ih, head.runExact]
      exact relative_evolution_compose ..

theorem ProductivePrecisionCourse.refinement {source presentation window received requests}
    (course : @ProductivePrecisionCourse source presentation window received requests) :
    WindowRefinement window course.endpoint.window := by
  induction course with
  | done certificate => exact .identity _
  | step head tail ih => exact head.refinement.compose ih

theorem ProductivePrecisionCourse.noLaterEscape {source presentation window received requests}
    (course : @ProductivePrecisionCourse source presentation window received requests)
    (index : Nat) (enough : course.endpoint.certificate.depth ≤ index) :
    window.Contains (presentation.numeric.approximate index) :=
  course.refinement.contains
    (productive_certificate_all_later_indices course.endpoint.certificate index enough)

def ProductivePrecisionCourse.append {source presentation window received first}
    (course : @ProductivePrecisionCourse source presentation window received first)
    {second : List Precision}
    (suffix : ProductivePrecisionCourse presentation course.endpoint.certificate second) :
    ProductivePrecisionCourse presentation received (first ++ second) :=
  match course with
  | .done _ => suffix
  | .step head tail => .step head (tail.append suffix)
termination_by structural course

theorem productive_precision_append_returns_suffix {source presentation window received first}
    (course : @ProductivePrecisionCourse source presentation window received first)
    {second : List Precision}
    (suffix : ProductivePrecisionCourse presentation course.endpoint.certificate second) :
    (course.append suffix).endpoint = suffix.endpoint := by
  induction course with
  | done certificate => rfl
  | step head tail ih => exact ih suffix

/-- Preserve the received course, then execute only the additional requests
from its returned endpoint. Appending its records does not replay producers. -/
def ProductivePrecisionCourse.continue {source presentation window received first}
    (course : @ProductivePrecisionCourse source presentation window received first)
    (second : List Precision) : ProductivePrecisionCourse presentation received (first ++ second) :=
  let returned := course.endpoint
  let suffix := returned.certificate.runPrecisions second
  course.append suffix

theorem productive_precision_continued_endpoint_exact {source presentation window received first}
    (course : @ProductivePrecisionCourse source presentation window received first)
    (second : List Precision) :
    (course.continue second).endpoint =
      (course.endpoint.certificate.runPrecisions second).endpoint :=
  productive_precision_append_returns_suffix ..

theorem productive_precision_continued_run_exact {source presentation window received first}
    (course : @ProductivePrecisionCourse source presentation window received first)
    (second : List Precision) :
    (course.continue second).endpoint.certificate.realization =
      course.endpoint.certificate.realization.evolve presentation.rule (precisionCourseSteps second) := by
  rw [productive_precision_continued_endpoint_exact]
  exact ProductivePrecisionCourse.runExact _

end RelationalPerimeter.Relativity.Production
/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Relativity.Production.ProductivePrecisionContinuation
#print axioms RelationalPerimeter.Relativity.Production.ProductiveWindowCertificate.continuePrecision
#print axioms RelationalPerimeter.Relativity.Production.productive_precision_continuation_uses_the_received_prefix
#print axioms RelationalPerimeter.Relativity.Production.productive_precision_continuation_depth
#print axioms RelationalPerimeter.Relativity.Production.ProductiveWindowEndpoint
#print axioms RelationalPerimeter.Relativity.Production.ProductivePrecisionCourse
#print axioms RelationalPerimeter.Relativity.Production.ProductiveWindowCertificate.runPrecisions
#print axioms RelationalPerimeter.Relativity.Production.ProductivePrecisionCourse.endpoint
#print axioms RelationalPerimeter.Relativity.Production.ProductivePrecisionCourse.headProduction
#print axioms RelationalPerimeter.Relativity.Production.productive_precision_head_exact
#print axioms RelationalPerimeter.Relativity.Production.productive_precision_head_horizon_independent
#print axioms RelationalPerimeter.Relativity.Production.precisionCourseSteps
#print axioms RelationalPerimeter.Relativity.Production.ProductivePrecisionCourse.depthExact
#print axioms RelationalPerimeter.Relativity.Production.ProductivePrecisionCourse.runExact
#print axioms RelationalPerimeter.Relativity.Production.ProductivePrecisionCourse.refinement
#print axioms RelationalPerimeter.Relativity.Production.ProductivePrecisionCourse.noLaterEscape
#print axioms RelationalPerimeter.Relativity.Production.ProductivePrecisionCourse.append
#print axioms RelationalPerimeter.Relativity.Production.productive_precision_append_returns_suffix
#print axioms RelationalPerimeter.Relativity.Production.ProductivePrecisionCourse.continue
#print axioms RelationalPerimeter.Relativity.Production.productive_precision_continued_endpoint_exact
#print axioms RelationalPerimeter.Relativity.Production.productive_precision_continued_run_exact
/- AXIOM_AUDIT_END -/
