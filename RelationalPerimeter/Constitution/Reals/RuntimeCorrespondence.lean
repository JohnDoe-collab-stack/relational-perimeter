import RelationalPerimeter.Constitution.Reals.AuthoritativeRuntime

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Runtime and effective-dyadic correspondence

This module separates the authoritative executed runtime from its numerical
presentation.  Runtime histories and resources remain primitive.  The
presentation is obtained only by executing canonical limit requests and
reading their retained responses.

The reverse construction receives an effective presentation as context and
builds a canonical runtime family for it.  Its round trip is numerical and
provenance-respecting; it does not reconstruct an erased rich history.
-/

namespace RelationalPerimeter.Constitution.Reals.RuntimeCorrespondence

open StrongPerimetralTurning
open ProducedCompleteness
open AuthoritativeRuntime

/-! ## Effective dyadic presentations -/

/--
An effective dyadic presentation computes every approximation and supplies
positive coherence for arbitrary received refinements.
-/
structure EffectiveDyadicPresentation where
  approximation : Nat -> SignedDyadicCode
  coherent :
    (coarse leftPrecision rightPrecision : Nat) ->
    PrecisionExtension coarse leftPrecision ->
    PrecisionExtension coarse rightPrecision ->
      Near coarse
        (approximation leftPrecision)
        (approximation rightPrecision)

namespace EffectiveDyadicPresentation

/-- Positive equivalence of two effective presentations. -/
structure Equivalent
    (first second : EffectiveDyadicPresentation) where
  responseThreshold : Nat -> Nat
  near :
    (precision leftResponse rightResponse : Nat) ->
    PrecisionExtension (responseThreshold precision) leftResponse ->
    PrecisionExtension (responseThreshold precision) rightResponse ->
      Near precision
        (first.approximation leftResponse)
        (second.approximation rightResponse)

def Equivalent.refl
    (presentation : EffectiveDyadicPresentation) :
    Equivalent presentation presentation where
  responseThreshold := fun precision => precision
  near := fun precision leftResponse rightResponse leftBeyond rightBeyond =>
    presentation.coherent precision leftResponse rightResponse
      leftBeyond rightBeyond

def Equivalent.symm
    {first second : EffectiveDyadicPresentation}
    (equivalent : Equivalent first second) :
    Equivalent second first where
  responseThreshold := equivalent.responseThreshold
  near := fun precision leftResponse rightResponse leftBeyond rightBeyond =>
    (equivalent.near precision rightResponse leftResponse
      rightBeyond leftBeyond).symm

private def firstThresholdExtension (first second : Nat) :
    PrecisionExtension first (first + second) where
  extra := second
  exact := rfl

private def secondThresholdExtension (first second : Nat) :
    PrecisionExtension second (first + second) where
  extra := first
  exact := Nat.add_comm second first

/-- Composition calculates a shared response threshold before using `Near`. -/
def Equivalent.trans
    {first middle last : EffectiveDyadicPresentation}
    (left : Equivalent first middle)
    (right : Equivalent middle last) :
    Equivalent first last where
  responseThreshold := fun precision =>
    left.responseThreshold (Nat.succ precision) +
      right.responseThreshold (Nat.succ precision)
  near := by
    intro precision leftResponse rightResponse leftBeyond rightBeyond
    let leftThreshold := left.responseThreshold (Nat.succ precision)
    let rightThreshold := right.responseThreshold (Nat.succ precision)
    let leftToCombined :=
      firstThresholdExtension leftThreshold rightThreshold
    let rightToCombined :=
      secondThresholdExtension leftThreshold rightThreshold
    have leftNear := left.near
      (Nat.succ precision) leftResponse (leftThreshold + rightThreshold)
      (leftToCombined.trans leftBeyond) leftToCombined
    have rightNear := right.near
      (Nat.succ precision) (leftThreshold + rightThreshold) rightResponse
      rightToCombined (rightToCombined.trans rightBeyond)
    exact Near.compose leftNear rightNear

/-- A constant runtime presentation normalizes its code at each precision. -/
def constant (code : SignedDyadicCode) : EffectiveDyadicPresentation where
  approximation := fun precision => code.raise precision
  coherent := by
    intro coarse leftPrecision rightPrecision _leftBeyond _rightBeyond
    exact
      ((SameValue.raiseExact code leftPrecision).symm.trans
        (SameValue.raiseExact code rightPrecision)).toNear coarse

/-- Every response of a constant presentation retains its generating value. -/
def constantApproximationSameValue
    (code : SignedDyadicCode)
    (precision : Nat) :
    SameValue ((constant code).approximation precision) code :=
  (SameValue.raiseExact code precision).symm

/-- Exactly equal dyadic values generate equivalent constant presentations. -/
def constantEquivalent
    {left right : SignedDyadicCode}
    (same : SameValue left right) :
    Equivalent (constant left) (constant right) where
  responseThreshold := fun precision => precision
  near := by
    intro precision leftResponse rightResponse _leftBeyond _rightBeyond
    exact
      ((SameValue.raiseExact left leftResponse).symm.trans
        (same.trans (SameValue.raiseExact right rightResponse))).toNear precision

end EffectiveDyadicPresentation

/-! ## Runtime reals and execution-derived readouts -/

/--
One authoritative runtime real at a fixed presentation and base depth.  The
stored producer is required to be the canonical runtime completeness
construction for its received family.
-/
structure RuntimeReal (P : CircularPresentation) (baseDepth : Nat) where
  family : ExecutedCauchyFamily P baseDepth
  produced : RuntimeProducedRelationalReal family
  producedExact : produced =
    AuthoritativeRuntime.ExecutedCauchyFamily.completeViaRuntime family

namespace RuntimeReal

def ofFamily
    {P : CircularPresentation}
    {baseDepth : Nat}
    (family : ExecutedCauchyFamily P baseDepth) :
    RuntimeReal P baseDepth where
  family := family
  produced :=
    AuthoritativeRuntime.ExecutedCauchyFamily.completeViaRuntime family
  producedExact := rfl

def initial
    {P : CircularPresentation}
    {baseDepth : Nat}
    (real : RuntimeReal P baseDepth) : Runtime real.family :=
  initialState real.family

def initialReachable
    {P : CircularPresentation}
    {baseDepth : Nat}
    (real : RuntimeReal P baseDepth) : Reachable real.family real.initial :=
  .initial

/-- The canonical executed limit step used by the numerical presentation. -/
def stepAt
    {P : CircularPresentation}
    {baseDepth : Nat}
    (real : RuntimeReal P baseDepth)
    (precision : Nat) :
    ExecutedStep real.family real.initial (.limit precision) :=
  real.produced.produce real.initial real.initialReachable precision

theorem stepAt_is_perform
    {P : CircularPresentation}
    {baseDepth : Nat}
    (real : RuntimeReal P baseDepth)
    (precision : Nat) :
    real.stepAt precision =
      perform real.family real.initial (.limit precision) :=
  real.produced.produceCanonical real.initial real.initialReachable precision

/-- Numerical readout obtained from the response owned by the canonical step. -/
def readout
    {P : CircularPresentation}
    {baseDepth : Nat}
    (real : RuntimeReal P baseDepth)
    (precision : Nat) : SignedDyadicCode :=
  (real.stepAt precision).response.readout

/-- Directed provenance for one numerical readout. -/
structure ReadoutOrigin
    {P : CircularPresentation}
    {baseDepth : Nat}
    (real : RuntimeReal P baseDepth)
    (precision : Nat) where
  step : ExecutedStep real.family real.initial (.limit precision)
  stepIsProduced : step = real.stepAt precision
  stepIsCanonical : step =
    perform real.family real.initial (.limit precision)
  readoutExact : step.response.readout = real.readout precision

def readoutOrigin
    {P : CircularPresentation}
    {baseDepth : Nat}
    (real : RuntimeReal P baseDepth)
    (precision : Nat) : ReadoutOrigin real precision where
  step := real.stepAt precision
  stepIsProduced := rfl
  stepIsCanonical := real.stepAt_is_perform precision
  readoutExact := rfl

/-- Arbitrary-refinement coherence derived from the executed Cauchy law. -/
def readoutsNear
    {P : CircularPresentation}
    {baseDepth : Nat}
    (real : RuntimeReal P baseDepth)
    (coarse leftPrecision rightPrecision : Nat)
    (leftExtension : PrecisionExtension coarse leftPrecision)
    (rightExtension : PrecisionExtension coarse rightPrecision) :
    Near coarse (real.readout leftPrecision) (real.readout rightPrecision) := by
  change Near coarse
    (real.stepAt leftPrecision).response.readout
    (real.stepAt rightPrecision).response.readout
  rw [real.stepAt_is_perform, real.stepAt_is_perform]
  let left :=
    (perform real.family real.initial (.limit leftPrecision)).response.limitProduction
  let right :=
    (perform real.family real.initial (.limit rightPrecision)).response.limitProduction
  change Near coarse left.readout right.readout
  rw [left.readout_is_source, right.readout_is_source]
  exact real.family.cauchy coarse
    left.sourceAt.request right.sourceAt.request
    (by
      rw [left.sourceAtExact]
      exact real.family.modulusMonotone leftExtension)
    (by
      rw [right.sourceAtExact]
      exact real.family.modulusMonotone rightExtension)
    (by
      rw [left.sourceAtExact]
      exact leftExtension)
    (by
      rw [right.sourceAtExact]
      exact rightExtension)
    left.source.execution right.source.execution

end RuntimeReal

/-- Execute each precision request before exposing the numerical presentation. -/
def runtimeToPresentation
    {P : CircularPresentation}
    {baseDepth : Nat}
    (real : RuntimeReal P baseDepth) : EffectiveDyadicPresentation where
  approximation := real.readout
  coherent := real.readoutsNear

/-! ## Canonical realization of a received presentation -/

def presentationProducer
    (presentation : EffectiveDyadicPresentation) : SourceProducer where
  calculate := fun request => presentation.approximation request.precision

def presentationFamily
    (P : CircularPresentation)
    (baseDepth : Nat)
    (presentation : EffectiveDyadicPresentation) :
    ExecutedCauchyFamily P baseDepth where
  producer := presentationProducer presentation
  termCoherent := fun _term coarse leftPrecision rightPrecision
      leftBeyond rightBeyond =>
    presentation.coherent coarse leftPrecision rightPrecision
      leftBeyond rightBeyond
  modulus := fun precision => precision
  modulusMonotone := fun extension => extension
  cauchy := by
    intro precision firstJournal secondJournal firstRequest secondRequest
      firstIndex secondIndex firstPrecision secondPrecision first second
    rw [first.readout_is_storedAction, second.readout_is_storedAction]
    rw [sourceProgram_actionCode_exact, sourceProgram_actionCode_exact]
    exact presentation.coherent precision
      firstRequest.precision secondRequest.precision
      firstPrecision secondPrecision

def presentationToRuntime
    (P : CircularPresentation)
    (baseDepth : Nat)
    (presentation : EffectiveDyadicPresentation) : RuntimeReal P baseDepth :=
  RuntimeReal.ofFamily (presentationFamily P baseDepth presentation)

theorem presentation_roundtrip_readout_exact
    (P : CircularPresentation)
    (baseDepth precision : Nat)
    (presentation : EffectiveDyadicPresentation) :
    (runtimeToPresentation
      (presentationToRuntime P baseDepth presentation)).approximation precision =
        presentation.approximation precision := by
  change
    ((presentationToRuntime P baseDepth presentation).stepAt precision).response.readout =
      presentation.approximation precision
  rw [RuntimeReal.stepAt_is_perform]
  exact
    (perform
      (presentationToRuntime P baseDepth presentation).family
      (presentationToRuntime P baseDepth presentation).initial
      (.limit precision)).response.limit_readout_is_calculated

def presentation_roundtrip_equivalent
    (P : CircularPresentation)
    (baseDepth : Nat)
    (presentation : EffectiveDyadicPresentation) :
    EffectiveDyadicPresentation.Equivalent
      (runtimeToPresentation
        (presentationToRuntime P baseDepth presentation))
      presentation where
  responseThreshold := fun precision => precision
  near := by
    intro precision leftResponse rightResponse leftBeyond rightBeyond
    rw [presentation_roundtrip_readout_exact]
    exact presentation.coherent precision leftResponse rightResponse
      leftBeyond rightBeyond

/-! ## Numerical runtime equivalence and exact correspondence -/

structure RuntimeReadoutEquivalent
    {P : CircularPresentation}
    {baseDepth : Nat}
    (first second : RuntimeReal P baseDepth) where
  responseThreshold : Nat -> Nat
  near :
    (precision leftResponse rightResponse : Nat) ->
    PrecisionExtension (responseThreshold precision) leftResponse ->
    PrecisionExtension (responseThreshold precision) rightResponse ->
      Near precision
        (first.readout leftResponse)
        (second.readout rightResponse)

def RuntimeReadoutEquivalent.refl
    {P : CircularPresentation}
    {baseDepth : Nat}
    (real : RuntimeReal P baseDepth) :
    RuntimeReadoutEquivalent real real where
  responseThreshold := fun precision => precision
  near := real.readoutsNear

def RuntimeReadoutEquivalent.toPresentation
    {P : CircularPresentation}
    {baseDepth : Nat}
    {first second : RuntimeReal P baseDepth}
    (equivalent : RuntimeReadoutEquivalent first second) :
    EffectiveDyadicPresentation.Equivalent
      (runtimeToPresentation first) (runtimeToPresentation second) where
  responseThreshold := equivalent.responseThreshold
  near := equivalent.near

def RuntimeReadoutEquivalent.ofPresentation
    {P : CircularPresentation}
    {baseDepth : Nat}
    {first second : RuntimeReal P baseDepth}
    (equivalent : EffectiveDyadicPresentation.Equivalent
      (runtimeToPresentation first) (runtimeToPresentation second)) :
    RuntimeReadoutEquivalent first second where
  responseThreshold := equivalent.responseThreshold
  near := equivalent.near

def RuntimeReadoutEquivalent.symm
    {P : CircularPresentation}
    {baseDepth : Nat}
    {first second : RuntimeReal P baseDepth}
    (equivalent : RuntimeReadoutEquivalent first second) :
    RuntimeReadoutEquivalent second first :=
  RuntimeReadoutEquivalent.ofPresentation equivalent.toPresentation.symm

def RuntimeReadoutEquivalent.trans
    {P : CircularPresentation}
    {baseDepth : Nat}
    {first middle last : RuntimeReal P baseDepth}
    (left : RuntimeReadoutEquivalent first middle)
    (right : RuntimeReadoutEquivalent middle last) :
    RuntimeReadoutEquivalent first last :=
  RuntimeReadoutEquivalent.ofPresentation
    (left.toPresentation.trans right.toPresentation)

/-- The internal correspondence is biconditional exactly at readout level. -/
def runtimeReadoutCorrespondence
    {P : CircularPresentation}
    {baseDepth : Nat}
    (first second : RuntimeReal P baseDepth) :
    (RuntimeReadoutEquivalent first second ->
      EffectiveDyadicPresentation.Equivalent
        (runtimeToPresentation first) (runtimeToPresentation second)) ×
    (EffectiveDyadicPresentation.Equivalent
        (runtimeToPresentation first) (runtimeToPresentation second) ->
      RuntimeReadoutEquivalent first second) :=
  ⟨RuntimeReadoutEquivalent.toPresentation,
    RuntimeReadoutEquivalent.ofPresentation⟩

def runtime_roundtrip_readout_equivalent
    {P : CircularPresentation}
    {baseDepth : Nat}
    (real : RuntimeReal P baseDepth) :
    RuntimeReadoutEquivalent
      (presentationToRuntime P baseDepth (runtimeToPresentation real))
      real :=
  RuntimeReadoutEquivalent.ofPresentation
    (presentation_roundtrip_equivalent P baseDepth
      (runtimeToPresentation real))

/-! ## Finite limit futures over retained authoritative traces -/

/--
A common future query separates requested accuracy from the response precision
chosen beyond the equivalence threshold.
-/
structure LimitQuery (threshold : Nat -> Nat) where
  accuracy : Nat
  leftResponse : Nat
  rightResponse : Nat
  leftBeyond : PrecisionExtension (threshold accuracy) leftResponse
  rightBeyond : PrecisionExtension (threshold accuracy) rightResponse

def leftLimitRequests
    {P : CircularPresentation}
    {baseDepth : Nat}
    (family : ExecutedCauchyFamily P baseDepth)
    {threshold : Nat -> Nat} :
    List (LimitQuery threshold) -> List (RuntimeRequest family)
  | [] => []
  | query :: remaining =>
      .limit query.leftResponse :: leftLimitRequests family remaining

def rightLimitRequests
    {P : CircularPresentation}
    {baseDepth : Nat}
    (family : ExecutedCauchyFamily P baseDepth)
    {threshold : Nat -> Nat} :
    List (LimitQuery threshold) -> List (RuntimeRequest family)
  | [] => []
  | query :: remaining =>
      .limit query.rightResponse :: rightLimitRequests family remaining

theorem limitStep_nextDepth
    {P : CircularPresentation}
    {baseDepth : Nat}
    {family : ExecutedCauchyFamily P baseDepth}
    {state : Runtime family}
    {precision : Nat}
    (step : ExecutedStep family state (.limit precision)) :
    step.next.journal.absoluteDepth =
      state.journal.absoluteDepth + 12 := by
  rw [step.next_journal]
  exact step.response.limit_depth

theorem RuntimeReal.limitStep_readout_eq
    {P : CircularPresentation}
    {baseDepth : Nat}
    (real : RuntimeReal P baseDepth)
    {state : Runtime real.family}
    {precision : Nat}
    (step : ExecutedStep real.family state (.limit precision)) :
    step.response.readout = real.readout precision := by
  change step.response.readout = (real.stepAt precision).response.readout
  rw [real.stepAt_is_perform]
  exact step.response.limit_readout_is_calculated.trans
    ((perform real.family real.initial
      (.limit precision)).response.limit_readout_is_calculated).symm

/--
Positive pairing of the two exact `RunTrace`s retained by authoritative runs.
Every constructor records equal depths and a `Near` witness for the two
executed response readouts.  It never identifies the rich steps.
-/
inductive PairedLimitTrace
    {P : CircularPresentation}
    {baseDepth : Nat}
    (first second : RuntimeReal P baseDepth)
    (threshold : Nat -> Nat) :
    {firstState : Runtime first.family} ->
    {secondState : Runtime second.family} ->
    (queries : List (LimitQuery threshold)) ->
    {firstFinal : Runtime first.family} ->
    {secondFinal : Runtime second.family} ->
    RunTrace first.family firstState
      (leftLimitRequests first.family queries) firstFinal ->
    RunTrace second.family secondState
      (rightLimitRequests second.family queries) secondFinal -> Type
  | done
      (firstState : Runtime first.family)
      (secondState : Runtime second.family)
      (depthExact : firstState.journal.absoluteDepth =
        secondState.journal.absoluteDepth) :
      PairedLimitTrace first second threshold
        (queries := []) (.done firstState) (.done secondState)
  | step
      {firstState : Runtime first.family}
      {secondState : Runtime second.family}
      {query : LimitQuery threshold}
      {remaining : List (LimitQuery threshold)}
      {firstFinal : Runtime first.family}
      {secondFinal : Runtime second.family}
      (firstStep : ExecutedStep first.family firstState
        (.limit query.leftResponse))
      (secondStep : ExecutedStep second.family secondState
        (.limit query.rightResponse))
      (firstLater : RunTrace first.family firstStep.next
        (leftLimitRequests first.family remaining) firstFinal)
      (secondLater : RunTrace second.family secondStep.next
        (rightLimitRequests second.family remaining) secondFinal)
      (startDepthExact : firstState.journal.absoluteDepth =
        secondState.journal.absoluteDepth)
      (readoutNear : Near query.accuracy
        firstStep.response.readout secondStep.response.readout)
      (later : PairedLimitTrace first second threshold
        (queries := remaining) firstLater secondLater) :
      PairedLimitTrace first second threshold
        (queries := query :: remaining)
        (.step firstStep firstLater) (.step secondStep secondLater)

namespace PairedLimitTrace

theorem terminalDepthExact
    {P : CircularPresentation}
    {baseDepth : Nat}
    {first second : RuntimeReal P baseDepth}
    {threshold : Nat -> Nat}
    {firstState : Runtime first.family}
    {secondState : Runtime second.family}
    {queries : List (LimitQuery threshold)}
    {firstFinal : Runtime first.family}
    {secondFinal : Runtime second.family}
    {firstTrace : RunTrace first.family firstState
      (leftLimitRequests first.family queries) firstFinal}
    {secondTrace : RunTrace second.family secondState
      (rightLimitRequests second.family queries) secondFinal}
    (paired : PairedLimitTrace first second threshold
      (queries := queries) firstTrace secondTrace) :
    firstFinal.journal.absoluteDepth = secondFinal.journal.absoluteDepth := by
  induction paired with
  | done _ _ depthExact => exact depthExact
  | step firstStep secondStep firstLater secondLater startDepthExact
      readoutNear later inductionHypothesis =>
      exact inductionHypothesis

end PairedLimitTrace

private def pairRunTraces
    {P : CircularPresentation}
    {baseDepth : Nat}
    {first second : RuntimeReal P baseDepth}
    (equivalent : RuntimeReadoutEquivalent first second) :
    {firstState : Runtime first.family} ->
    {secondState : Runtime second.family} ->
    (startDepthExact : firstState.journal.absoluteDepth =
      secondState.journal.absoluteDepth) ->
    {queries : List (LimitQuery equivalent.responseThreshold)} ->
    {firstFinal : Runtime first.family} ->
    {secondFinal : Runtime second.family} ->
    (firstTrace : RunTrace first.family firstState
      (leftLimitRequests first.family queries) firstFinal) ->
    (secondTrace : RunTrace second.family secondState
      (rightLimitRequests second.family queries) secondFinal) ->
      PairedLimitTrace first second equivalent.responseThreshold
        (queries := queries) firstTrace secondTrace
  | firstState, secondState, startDepthExact, [], _, _, firstTrace,
      secondTrace => by
      cases firstTrace
      cases secondTrace
      exact .done firstState secondState startDepthExact
  | firstState, secondState, startDepthExact, query :: remaining, _, _,
      firstTrace, secondTrace => by
      cases firstTrace with
      | step firstStep firstLater =>
          cases secondTrace with
          | step secondStep secondLater =>
              have readoutNear : Near query.accuracy
                  firstStep.response.readout secondStep.response.readout := by
                rw [first.limitStep_readout_eq firstStep,
                  second.limitStep_readout_eq secondStep]
                exact equivalent.near query.accuracy
                  query.leftResponse query.rightResponse
                  query.leftBeyond query.rightBeyond
              have nextDepthExact :
                  firstStep.next.journal.absoluteDepth =
                    secondStep.next.journal.absoluteDepth := by
                calc
                  firstStep.next.journal.absoluteDepth =
                      firstState.journal.absoluteDepth + 12 :=
                    limitStep_nextDepth firstStep
                  _ = secondState.journal.absoluteDepth + 12 :=
                    congrArg (fun depth => depth + 12) startDepthExact
                  _ = secondStep.next.journal.absoluteDepth :=
                    (limitStep_nextDepth secondStep).symm
              exact .step firstStep secondStep firstLater secondLater
                startDepthExact readoutNear
                (pairRunTraces equivalent nextDepthExact
                  firstLater secondLater)

/--
All finite limit futures are paired on the exact traces retained by `run`.
This is the future-level counterpart of numerical readout equivalence.
-/
structure LimitFutureEquivalent
    {P : CircularPresentation}
    {baseDepth : Nat}
    (first second : RuntimeReal P baseDepth) where
  responseThreshold : Nat -> Nat
  traces :
    (queries : List (LimitQuery responseThreshold)) ->
      PairedLimitTrace first second responseThreshold
        (queries := queries)
        (run first.family first.initial
          (leftLimitRequests first.family queries)).traceEvidence
        (run second.family second.initial
          (rightLimitRequests second.family queries)).traceEvidence

def RuntimeReadoutEquivalent.toLimitFuture
    {P : CircularPresentation}
    {baseDepth : Nat}
    {first second : RuntimeReal P baseDepth}
    (equivalent : RuntimeReadoutEquivalent first second) :
    LimitFutureEquivalent first second where
  responseThreshold := equivalent.responseThreshold
  traces := fun queries =>
    pairRunTraces equivalent
      (firstState := first.initial) (secondState := second.initial) rfl
      (run first.family first.initial
        (leftLimitRequests first.family queries)).traceEvidence
      (run second.family second.initial
        (rightLimitRequests second.family queries)).traceEvidence

/-- A singleton paired future derives, rather than assumes, each readout law. -/
def LimitFutureEquivalent.toReadouts
    {P : CircularPresentation}
    {baseDepth : Nat}
    {first second : RuntimeReal P baseDepth}
    (equivalent : LimitFutureEquivalent first second) :
    RuntimeReadoutEquivalent first second where
  responseThreshold := equivalent.responseThreshold
  near := by
    intro precision leftResponse rightResponse leftBeyond rightBeyond
    let query : LimitQuery equivalent.responseThreshold :=
      { accuracy := precision
        leftResponse := leftResponse
        rightResponse := rightResponse
        leftBeyond := leftBeyond
        rightBeyond := rightBeyond }
    have paired := equivalent.traces [query]
    cases paired with
    | step firstStep secondStep firstLater secondLater startDepthExact
        readoutNear later =>
        rw [first.limitStep_readout_eq
              (perform first.family first.initial (.limit leftResponse)),
          second.limitStep_readout_eq
              (perform second.family second.initial (.limit rightResponse))]
          at readoutNear
        exact readoutNear

/-- Readout equivalence and finite limit-future equivalence are interderivable. -/
def limitFutureCorrespondence
    {P : CircularPresentation}
    {baseDepth : Nat}
    (first second : RuntimeReal P baseDepth) :
    (RuntimeReadoutEquivalent first second ->
      LimitFutureEquivalent first second) ×
    (LimitFutureEquivalent first second ->
      RuntimeReadoutEquivalent first second) :=
  ⟨RuntimeReadoutEquivalent.toLimitFuture,
    LimitFutureEquivalent.toReadouts⟩


/-- Constant realizations stay numerical presentations of the common runtime. -/
def constantRuntime (P : CircularPresentation) (baseDepth : Nat) (code : SignedDyadicCode) :
    RuntimeReal P baseDepth :=
  presentationToRuntime P baseDepth (EffectiveDyadicPresentation.constant code)

def constantRuntimeReadoutSameValue
    (P : CircularPresentation) (baseDepth : Nat) (code : SignedDyadicCode)
    {state : Runtime (constantRuntime P baseDepth code).family} {precision : Nat}
    (step : ExecutedStep (constantRuntime P baseDepth code).family state (.limit precision)) :
    SameValue step.response.readout code := by
  rw [step.response.limit_readout_is_calculated]
  exact (SameValue.raiseExact code precision).symm

def constantRuntimeEquivalent
    (P : CircularPresentation) (baseDepth : Nat)
    {first second : SignedDyadicCode} (same : SameValue first second) :
    RuntimeReadoutEquivalent
      (constantRuntime P baseDepth first) (constantRuntime P baseDepth second) where
  responseThreshold := fun precision => precision
  near := by
    intro precision leftResponse rightResponse leftBeyond rightBeyond
    change Near precision
      ((runtimeToPresentation (presentationToRuntime P baseDepth
        (EffectiveDyadicPresentation.constant first))).approximation leftResponse)
      ((runtimeToPresentation (presentationToRuntime P baseDepth
        (EffectiveDyadicPresentation.constant second))).approximation rightResponse)
    rw [presentation_roundtrip_readout_exact, presentation_roundtrip_readout_exact]
    exact (EffectiveDyadicPresentation.constantEquivalent same).near
      precision leftResponse rightResponse leftBeyond rightBeyond


end RelationalPerimeter.Constitution.Reals.RuntimeCorrespondence

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Constitution.Reals.RuntimeCorrespondence.EffectiveDyadicPresentation
#print axioms RelationalPerimeter.Constitution.Reals.RuntimeCorrespondence.EffectiveDyadicPresentation.Equivalent
#print axioms RelationalPerimeter.Constitution.Reals.RuntimeCorrespondence.EffectiveDyadicPresentation.Equivalent.trans
#print axioms RelationalPerimeter.Constitution.Reals.RuntimeCorrespondence.EffectiveDyadicPresentation.constant
#print axioms RelationalPerimeter.Constitution.Reals.RuntimeCorrespondence.EffectiveDyadicPresentation.constantApproximationSameValue
#print axioms RelationalPerimeter.Constitution.Reals.RuntimeCorrespondence.EffectiveDyadicPresentation.constantEquivalent
#print axioms RelationalPerimeter.Constitution.Reals.RuntimeCorrespondence.RuntimeReal
#print axioms RelationalPerimeter.Constitution.Reals.RuntimeCorrespondence.RuntimeReal.ofFamily
#print axioms RelationalPerimeter.Constitution.Reals.RuntimeCorrespondence.RuntimeReal.ReadoutOrigin
#print axioms RelationalPerimeter.Constitution.Reals.RuntimeCorrespondence.RuntimeReal.readoutOrigin
#print axioms RelationalPerimeter.Constitution.Reals.RuntimeCorrespondence.RuntimeReal.readoutsNear
#print axioms RelationalPerimeter.Constitution.Reals.RuntimeCorrespondence.runtimeToPresentation
#print axioms RelationalPerimeter.Constitution.Reals.RuntimeCorrespondence.presentationFamily
#print axioms RelationalPerimeter.Constitution.Reals.RuntimeCorrespondence.presentationToRuntime
#print axioms RelationalPerimeter.Constitution.Reals.RuntimeCorrespondence.presentation_roundtrip_readout_exact
#print axioms RelationalPerimeter.Constitution.Reals.RuntimeCorrespondence.presentation_roundtrip_equivalent
#print axioms RelationalPerimeter.Constitution.Reals.RuntimeCorrespondence.RuntimeReadoutEquivalent
#print axioms RelationalPerimeter.Constitution.Reals.RuntimeCorrespondence.RuntimeReadoutEquivalent.refl
#print axioms RelationalPerimeter.Constitution.Reals.RuntimeCorrespondence.RuntimeReadoutEquivalent.symm
#print axioms RelationalPerimeter.Constitution.Reals.RuntimeCorrespondence.RuntimeReadoutEquivalent.trans
#print axioms RelationalPerimeter.Constitution.Reals.RuntimeCorrespondence.runtimeReadoutCorrespondence
#print axioms RelationalPerimeter.Constitution.Reals.RuntimeCorrespondence.runtime_roundtrip_readout_equivalent
#print axioms RelationalPerimeter.Constitution.Reals.RuntimeCorrespondence.LimitQuery
#print axioms RelationalPerimeter.Constitution.Reals.RuntimeCorrespondence.leftLimitRequests
#print axioms RelationalPerimeter.Constitution.Reals.RuntimeCorrespondence.rightLimitRequests
#print axioms RelationalPerimeter.Constitution.Reals.RuntimeCorrespondence.PairedLimitTrace
#print axioms RelationalPerimeter.Constitution.Reals.RuntimeCorrespondence.PairedLimitTrace.terminalDepthExact
#print axioms RelationalPerimeter.Constitution.Reals.RuntimeCorrespondence.LimitFutureEquivalent
#print axioms RelationalPerimeter.Constitution.Reals.RuntimeCorrespondence.RuntimeReadoutEquivalent.toLimitFuture
#print axioms RelationalPerimeter.Constitution.Reals.RuntimeCorrespondence.LimitFutureEquivalent.toReadouts
#print axioms RelationalPerimeter.Constitution.Reals.RuntimeCorrespondence.limitFutureCorrespondence
#print axioms RelationalPerimeter.Constitution.Reals.RuntimeCorrespondence.constantRuntime
#print axioms RelationalPerimeter.Constitution.Reals.RuntimeCorrespondence.constantRuntimeReadoutSameValue
#print axioms RelationalPerimeter.Constitution.Reals.RuntimeCorrespondence.constantRuntimeEquivalent
/- AXIOM_AUDIT_END -/
