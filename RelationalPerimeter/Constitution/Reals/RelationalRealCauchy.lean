import RelationalPerimeter.Constitution.Reals.RelationalRealAddition

set_option autoImplicit false
set_option linter.unusedVariables false

/-!
# Executed Cauchy families in the common real carrier

This is an adapter of a received ExecutedCauchyFamily, not a new limit
construction or completeness for arbitrary sequences of Real. A term owns
the authoritative raw source execution at its fixed index. The limit is the
existing authoritative leaf. Both laws below consume the current Steps,
including the source execution actually owned by the received limit Step.
-/
namespace RelationalPerimeter.Constitution.Reals.RelationalRealCauchy
open StrongPerimetralTurning ConstitutiveRuntime ProducedCompleteness
open RuntimeCorrespondence HeterogeneousRealRuntime RelationalRealAddition

variable {P : CircularPresentation} {baseDepth : Nat}

/-- The same accessible authoritative archives can serve a term and its limit. -/
abbrev TermArchive (family : ExecutedCauchyFamily P baseDepth) :=
  LeafArchive (RuntimeReal.ofFamily family)

/-- The rich event keeps its incoming occurrence and the one raw execution. -/
structure TermRichEvent (family : ExecutedCauchyFamily P baseDepth) (term : Nat) where
  archive : TermArchive family
  precision : Nat
  resource : AuthoritativeRuntime.RawSourceStep family archive.state
    { term := term, precision := precision }

def TermRichEvent.project {family : ExecutedCauchyFamily P baseDepth} {term : Nat}
    (event : TermRichEvent family term) : AuthoritativeRuntime.CommonEvent :=
  .executed event.resource.event

/-- The source route never reads modulus; this closed constant captures none. -/
def sourceEnvironment (producer : SourceProducer) : CommonRealRuntime.Environment :=
  { producer := producer, modulus := fun _ => 0 }

/-- Only producer and term are static executable inputs; memory is unchanged. -/
def termLiveStep (producer : SourceProducer) (term : Nat)
    (memory : AuthoritativeRuntime.ReducedState) (precision : Nat) :
    LiveStep AuthoritativeRuntime.ReducedState AuthoritativeRuntime.CommonEvent :=
  let transition := CommonRealRuntime.performReal
    { environment := sourceEnvironment producer, memory := memory }
    (.source { term := term, precision := precision })
  ⟨transition.next.memory, transition.event⟩

/-- The closed dummy modulus has no effect on the existing source route. -/
theorem termLiveStep_is_source (family : ExecutedCauchyFamily P baseDepth)
    (term : Nat) (memory : AuthoritativeRuntime.ReducedState) (precision : Nat) :
    termLiveStep family.producer term memory precision =
      let transition := CommonRealRuntime.performReal
        { environment := CommonRealRuntime.environmentOfFamily family, memory := memory }
        (.source { term := term, precision := precision })
      ⟨transition.next.memory, transition.event⟩ := rfl

theorem termNextProjection (family : ExecutedCauchyFamily P baseDepth)
    (term : Nat) (archive : TermArchive family) (precision : Nat) :
    AuthoritativeRuntime.project
        (AuthoritativeRuntime.performRawSource family archive.state
          { term := term, precision := precision }).next =
      (termLiveStep family.producer term
        (AuthoritativeRuntime.project archive.state) precision).next :=
  congrArg CommonRealRuntime.Runtime.memory
    (CommonRealRuntime.rawNextProjection family
      (AuthoritativeRuntime.performRawSource family archive.state
        { term := term, precision := precision }))

theorem termEventProjection (family : ExecutedCauchyFamily P baseDepth)
    (term : Nat) (archive : TermArchive family) (precision : Nat) :
    AuthoritativeRuntime.CommonEvent.executed
        (AuthoritativeRuntime.performRawSource family archive.state
          { term := term, precision := precision }).event =
      (termLiveStep family.producer term
        (AuthoritativeRuntime.project archive.state) precision).event :=
  CommonRealRuntime.rawEventProjection family
    (AuthoritativeRuntime.performRawSource family archive.state
      { term := term, precision := precision })

/-- Exact identity is only for this fixed producer/index and the projected contract. -/
theorem termMemorySeparates (producer : SourceProducer) (term : Nat)
    (first second : AuthoritativeRuntime.ReducedState) (precision : Nat)
    (readExact : first.last = second.last)
    (eventExact : (termLiveStep producer term first precision).event =
      (termLiveStep producer term second precision).event) : first = second :=
  AuthoritativeRuntime.ReducedState.extensionality first second
    (congrArg leafEventStart eventExact) readExact

def termEnvironment (family : ExecutedCauchyFamily P baseDepth) (term : Nat) :
    Service P baseDepth where
  Archive := TermArchive family
  Memory := AuthoritativeRuntime.ReducedState
  Event := AuthoritativeRuntime.CommonEvent
  RichEvent := TermRichEvent family term
  Read := Option AuthoritativeRuntime.Observation
  Resource archive precision := AuthoritativeRuntime.RawSourceStep family archive.state
    { term := term, precision := precision }
  initialArchive := ⟨AuthoritativeRuntime.initialState family, .initial⟩
  execute archive precision := AuthoritativeRuntime.performRawSource family archive.state
    { term := term, precision := precision }
  next {archive} {precision} step := ⟨step.next, .rawSource archive.reachable step⟩
  richEvent {archive} {precision} step := ⟨archive, precision, step⟩
  code {archive} {precision} step := step.execution.readout
  readArchive archive := AuthoritativeRuntime.read archive.state
  project archive := AuthoritativeRuntime.project archive.state
  projectEvent := TermRichEvent.project
  readLive := AuthoritativeRuntime.readLive
  liveStep := termLiveStep family.producer term
  answer := leafAnswer
  nextExact := termNextProjection family term
  eventExact := termEventProjection family term
  readExact _ := rfl
  answerExact _ := rfl
  separates := termMemorySeparates family.producer term

def termCoherent (family : ExecutedCauchyFamily P baseDepth) (term : Nat) :
    Coherent (termEnvironment family term) where
  near := by
    intro firstArchive secondArchive coarse first second firstStep secondStep firstBeyond secondBeyond
    exact ExecutedCauchyFamily.ProducedSourceAt.sameTermExecutedNear
      term coarse first second firstBeyond secondBeyond
      firstStep.resource.execution secondStep.resource.execution

/-- Fixed-precision uniformity consumes both owned source results, not a replay. -/
theorem termUniform (family : ExecutedCauchyFamily P baseDepth) (term : Nat)
    {firstArchive secondArchive : (termEnvironment family term).Archive} {precision : Nat}
    (first : Step (termEnvironment family term) firstArchive precision)
    (second : Step (termEnvironment family term) secondArchive precision) :
    first.code = second.code :=
  first.resource.readoutExact.trans second.resource.readoutExact.symm

def termCertificate (family : ExecutedCauchyFamily P baseDepth) (term : Nat) :
    CertifiedService P baseDepth where
  service := termEnvironment family term
  coherence := termCoherent family term
  uniform _archive precision step := termUniform family term step (canonicalStep _ precision)

def termReal (family : ExecutedCauchyFamily P baseDepth) (term : Nat) : Real P baseDepth :=
  .certified (termCertificate family term)

/-- This leaf executes the old source/grouping/action/store route without change. -/
def limitReal (family : ExecutedCauchyFamily P baseDepth) : Real P baseDepth :=
  .leaf (RuntimeReal.ofFamily family)

/-- Cauchy on arbitrary current term archives and actual received Steps. -/
def termsCauchy (family : ExecutedCauchyFamily P baseDepth)
    (precision firstTerm secondTerm firstPrecision secondPrecision : Nat)
    {firstArchive : (environment (termReal family firstTerm)).Archive}
    {secondArchive : (environment (termReal family secondTerm)).Archive}
    (first : Step (environment (termReal family firstTerm)) firstArchive firstPrecision)
    (second : Step (environment (termReal family secondTerm)) secondArchive secondPrecision)
    (firstIndex : PrecisionExtension (family.modulus precision) firstTerm)
    (secondIndex : PrecisionExtension (family.modulus precision) secondTerm)
    (firstBeyond : PrecisionExtension precision firstPrecision)
    (secondBeyond : PrecisionExtension precision secondPrecision) :
    Near precision first.code second.code :=
  family.cauchy precision
    { term := firstTerm, precision := firstPrecision }
    { term := secondTerm, precision := secondPrecision }
    firstIndex secondIndex firstBeyond secondBeyond
    first.resource.execution second.resource.execution

/-- Only project the resource of this received response; no producer is called. -/
theorem limitStepReadout {family : ExecutedCauchyFamily P baseDepth}
    {archive : (environment (limitReal family)).Archive} {precision : Nat}
    (step : Step (environment (limitReal family)) archive precision) :
    step.code = step.resource.response.limitProduction.readout := by
  change step.resource.response.readout = _
  rcases step.resource.response with ⟨resource⟩
  cases resource
  rfl

/-- The diagonal source is the one inside the actual received limit Step. -/
def termLimitNear (family : ExecutedCauchyFamily P baseDepth)
    (precision term termPrecision limitPrecision : Nat)
    {termArchive : (environment (termReal family term)).Archive}
    {limitArchive : (environment (limitReal family)).Archive}
    (termStep : Step (environment (termReal family term)) termArchive termPrecision)
    (limitStep : Step (environment (limitReal family)) limitArchive limitPrecision)
    (indexBeyond : PrecisionExtension (family.modulus precision) term)
    (termBeyond : PrecisionExtension precision termPrecision)
    (limitBeyond : PrecisionExtension precision limitPrecision) :
    Near precision termStep.code limitStep.code := by
  let production := limitStep.resource.response.limitProduction
  rw [limitStepReadout limitStep]
  change Near precision termStep.code production.readout
  rw [production.readout_is_source]
  exact family.cauchy precision
    { term := term, precision := termPrecision } production.sourceAt.request
    indexBeyond
    (by rw [production.sourceAtExact]; exact family.modulusMonotone limitBeyond)
    termBeyond
    (by rw [production.sourceAtExact]; exact limitBeyond)
    termStep.resource.execution production.source.execution

/-- Scope is exactly the received executed family, not all arbitrary Real sequences. -/
structure InternalCompleteness (family : ExecutedCauchyFamily P baseDepth) where
  terms : Nat → Real P baseDepth
  termsExact : (term : Nat) → terms term = termReal family term
  modulus : Nat → Nat
  modulusExact : (precision : Nat) → modulus precision = family.modulus precision
  limit : Real P baseDepth
  limitExact : limit = limitReal family
  cauchy : (precision firstTerm secondTerm firstPrecision secondPrecision : Nat) →
    {firstArchive : (environment (terms firstTerm)).Archive} →
    {secondArchive : (environment (terms secondTerm)).Archive} →
    (first : Step (environment (terms firstTerm)) firstArchive firstPrecision) →
    (second : Step (environment (terms secondTerm)) secondArchive secondPrecision) →
    PrecisionExtension (modulus precision) firstTerm →
    PrecisionExtension (modulus precision) secondTerm →
    PrecisionExtension precision firstPrecision → PrecisionExtension precision secondPrecision →
    Near precision first.code second.code
  converges : (precision term termPrecision limitPrecision : Nat) →
    {termArchive : (environment (terms term)).Archive} →
    {limitArchive : (environment limit).Archive} →
    (termStep : Step (environment (terms term)) termArchive termPrecision) →
    (limitStep : Step (environment limit) limitArchive limitPrecision) →
    PrecisionExtension (modulus precision) term →
    PrecisionExtension precision termPrecision → PrecisionExtension precision limitPrecision →
    Near precision termStep.code limitStep.code

def internalCompleteness (family : ExecutedCauchyFamily P baseDepth) :
    InternalCompleteness family where
  terms := termReal family
  termsExact _ := rfl
  modulus := family.modulus
  modulusExact _ := rfl
  limit := limitReal family
  limitExact := rfl
  cauchy := termsCauchy family
  converges := termLimitNear family

end RelationalPerimeter.Constitution.Reals.RelationalRealCauchy

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealCauchy.TermArchive
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealCauchy.TermRichEvent
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealCauchy.TermRichEvent.project
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealCauchy.sourceEnvironment
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealCauchy.termLiveStep
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealCauchy.termLiveStep_is_source
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealCauchy.termNextProjection
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealCauchy.termEventProjection
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealCauchy.termMemorySeparates
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealCauchy.termEnvironment
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealCauchy.termCoherent
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealCauchy.termUniform
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealCauchy.termCertificate
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealCauchy.termReal
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealCauchy.limitReal
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealCauchy.termsCauchy
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealCauchy.limitStepReadout
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealCauchy.termLimitNear
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealCauchy.InternalCompleteness
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealCauchy.internalCompleteness
/- AXIOM_AUDIT_END -/
