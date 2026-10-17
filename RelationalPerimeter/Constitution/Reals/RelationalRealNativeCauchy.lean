import RelationalPerimeter.Constitution.Reals.RelationalRealNativeLimitRuntime

set_option autoImplicit false
set_option linter.unusedVariables false

/-!
# Native Cauchy families of closed real behaviours

The family owns native Real terms and a law on received current Steps.
Its effective presentation is downstream and forgets histories. The native
limit owns the actual diagonal Step consumed by grouping. Convergence extracts
that very resource without executing another diagonal. The effective source
realization is a numerical correspondence only, never its constitution.
-/
namespace RelationalPerimeter.Constitution.Reals.RelationalRealNativeCauchy
open StrongPerimetralTurning ProducedCompleteness RuntimeCorrespondence
open HeterogeneousRealRuntime RelationalRealAddition RelationalRealCauchy
open RelationalRealFamilyTransport RelationalRealLimitUniqueness

variable {P : CircularPresentation} {baseDepth : Nat}

/-- An observation produces two native Steps and retains their one Cauchy result. -/
structure PairObservation (family : NativeCauchyFamily P baseDepth) (p n m r s : Nat)
    (aa : (environment (family.terms n)).Archive) (ba : (environment (family.terms m)).Archive)
    (hn : PrecisionExtension (family.modulus p) n) (hm : PrecisionExtension (family.modulus p) m)
    (hr : PrecisionExtension p r) (hs : PrecisionExtension p s) where
  private mk ::
  archives : (environment (family.terms n)).Archive × (environment (family.terms m)).Archive
  archivesExact : archives = ⟨aa, ba⟩
  first : Step (environment (family.terms n)) aa r
  second : Step (environment (family.terms m)) ba s
  firstExact : first = executeAt (family.terms n) aa r
  secondExact : second = executeAt (family.terms m) ba s
  near : Near p first.code second.code
  nearExact : near = family.cauchy p n m r s first second hn hm hr hs
  numerical : Near p (readout (family.terms n) r) (readout (family.terms m) s)
  numericalExact : numerical = LimitGrouping.transportNear
    (currentReadout _ _ _ first) (currentReadout _ _ _ second) near

def observePair (family : NativeCauchyFamily P baseDepth) (p n m r s : Nat)
    (aa : (environment (family.terms n)).Archive) (ba : (environment (family.terms m)).Archive)
    (hn : PrecisionExtension (family.modulus p) n) (hm : PrecisionExtension (family.modulus p) m)
    (hr : PrecisionExtension p r) (hs : PrecisionExtension p s) :
    PairObservation family p n m r s aa ba hn hm hr hs :=
  let first := executeAt (family.terms n) aa r
  let second := executeAt (family.terms m) ba s
  let near := family.cauchy p n m r s first second hn hm hr hs
  let numerical := LimitGrouping.transportNear (currentReadout _ _ _ first) (currentReadout _ _ _ second) near
  ⟨⟨aa, ba⟩, rfl, first, second, rfl, rfl, near, rfl, numerical, rfl⟩

/-- Numerical convenience uses fresh declared initial native contexts. It does
not recover earlier archives or the original positive Cauchy witness. -/
def toEffectiveFamily (family : NativeCauchyFamily P baseDepth) : EffectiveFamily where
  terms n := toPresentation (family.terms n)
  modulus := family.modulus
  modulusMonotone := family.modulusMonotone
  cauchy p n m r s hn hm hr hs :=
    (observePair family p n m r s (environment (family.terms n)).initialArchive
      (environment (family.terms m)).initialArchive hn hm hr hs).numerical

abbrev realizedFamily (family : NativeCauchyFamily P baseDepth) :=
  realizeFamily P baseDepth (toEffectiveFamily family)

theorem realizedTermCode (family : NativeCauchyFamily P baseDepth) (n p : Nat)
    {archive : (environment (termReal (realizedFamily family) n)).Archive}
    (step : Step (environment (termReal (realizedFamily family) n)) archive p) :
    step.code = readout (family.terms n) p :=
  realizedTermAt (toEffectiveFamily family) n p step

def realizedTermEquivalent (family : NativeCauchyFamily P baseDepth) (n : Nat) :
    Equivalent (termReal (realizedFamily family) n) (family.terms n) :=
  Equivalent.ofExact (fun p => by
    change SameValue (executeReal (termReal (realizedFamily family) n) p).code (readout (family.terms n) p)
    rw [realizedTermCode family n p]
    exact SameValue.refl _)

def realizedTermFutures (family : NativeCauchyFamily P baseDepth) (n : Nat) :
    NumericalFutureEquivalent (termReal (realizedFamily family) n) (family.terms n) :=
  (realizedTermEquivalent family n).toFutures

/-- Downstream uniform-code view only; native constitution/convergence do not
call this proposition-level canonical-reference bridge. -/
theorem sourceReadoutExact (family : NativeCauchyFamily P baseDepth) {s : Nat}
    {la : (environment (nativeLimit family)).Archive}
    (step : Step (environment (nativeLimit family)) la s) :
    step.resource.diagonal.code = readout (family.terms (family.modulus s)) s :=
  currentReadout _ _ _ step.resource.diagonal

theorem diagonalReadoutExact (family : NativeCauchyFamily P baseDepth) {s : Nat}
    {la : (environment (nativeLimit family)).Archive}
    (step : Step (environment (nativeLimit family)) la s)
    {da : (environment (family.terms (family.modulus s))).Archive}
    (diagonal : Step (environment (family.terms (family.modulus s))) da s) :
    diagonal.code = step.resource.diagonal.code :=
  (currentReadout _ _ _ diagonal).trans (sourceReadoutExact family step).symm

/-- The actual grouped native source is retained by this current limit Step. -/
theorem sourceToLimit (family : NativeCauchyFamily P baseDepth) {s : Nat}
    {la : (environment (nativeLimit family)).Archive}
    (step : Step (environment (nativeLimit family)) la s) :
    step.resource.diagonal.code = step.code := step.resource.codeExact.symm

/-- Both Steps are received. The diagonal is extracted from the actual limit
production, with its owned bank archive, never independently reconstructed. -/
structure LimitObservation (family : NativeCauchyFamily P baseDepth) (p n r s : Nat)
    {ta : (environment (family.terms n)).Archive} {la : (environment (nativeLimit family)).Archive}
    (term : Step (environment (family.terms n)) ta r)
    (lim : Step (environment (nativeLimit family)) la s)
    (hn : PrecisionExtension (family.modulus p) n)
    (hr : PrecisionExtension p r) (hs : PrecisionExtension p s) where
  private mk ::
  termStep : Step (environment (family.terms n)) ta r
  termExact : termStep = term
  limitStep : Step (environment (nativeLimit family)) la s
  limitExact : limitStep = lim
  diagonalArchive : (environment (family.terms (family.modulus s))).Archive
  archiveExact : diagonalArchive = la.bank (family.modulus s)
  diagonal : Step (environment (family.terms (family.modulus s))) (la.bank (family.modulus s)) s
  diagonalExact : diagonal = lim.resource.diagonal
  nativeNear : Near p term.code diagonal.code
  nativeNearExact : nativeNear = family.cauchy p n (family.modulus s) r s term diagonal
    hn (family.modulusMonotone hs) hr hs
  near : Near p term.code lim.code
  nearExact : near = LimitGrouping.transportNear rfl
    ((congrArg Step.code diagonalExact).trans (sourceToLimit family lim)) nativeNear

def observeLimit (family : NativeCauchyFamily P baseDepth) (p n r s : Nat)
    {ta : (environment (family.terms n)).Archive} {la : (environment (nativeLimit family)).Archive}
    (term : Step (environment (family.terms n)) ta r)
    (lim : Step (environment (nativeLimit family)) la s)
    (hn : PrecisionExtension (family.modulus p) n)
    (hr : PrecisionExtension p r) (hs : PrecisionExtension p s) :
    LimitObservation family p n r s term lim hn hr hs :=
  let diagonal := lim.resource.diagonal
  let nativeNear := family.cauchy p n (family.modulus s) r s term diagonal
    hn (family.modulusMonotone hs) hr hs
  let near := LimitGrouping.transportNear rfl (sourceToLimit family lim) nativeNear
  ⟨term, rfl, lim, rfl, la.bank (family.modulus s), rfl, diagonal, rfl, nativeNear, rfl, near, rfl⟩


/-- Native convergence is positive and consumes current native/candidate Steps.
It contains no terminal equivalence and does not identify their occurrences. -/
structure NativeCandidate (family : NativeCauchyFamily P baseDepth) where
  real : Real P baseDepth
  threshold : Nat → Nat
  converges : (p n r s : Nat) →
    {ta : (environment (family.terms n)).Archive} → {a : (environment real).Archive} →
    (term : Step (environment (family.terms n)) ta r) →
    (candidate : Step (environment real) a s) →
    PrecisionExtension (family.modulus p) n → PrecisionExtension p r →
    PrecisionExtension (threshold p) s → Near p term.code candidate.code

/-- Convergence consumes the native diagonal already owned by the limit. -/
def nativeAuthoritative (family : NativeCauchyFamily P baseDepth) : NativeCandidate family where
  real := nativeLimit family
  threshold := fun p => p
  converges := by
    intro p n r s ta la term lim hn hr hs
    exact (observeLimit family p n r s term lim hn hr hs).near

/-- An old source-term Step is not a native Step. Its adapter owns one newly
executed native counterpart before consuming the native candidate law. -/
structure CandidateObservation {family : NativeCauchyFamily P baseDepth}
    (candidate : NativeCandidate family) (p n r s : Nat)
    {ta : (environment (termReal (realizedFamily family) n)).Archive}
    {a : (environment candidate.real).Archive}
    (term : Step (environment (termReal (realizedFamily family) n)) ta r)
    (response : Step (environment candidate.real) a s)
    (na : (environment (family.terms n)).Archive)
    (hn : PrecisionExtension (family.modulus p) n) (hr : PrecisionExtension p r)
    (hs : PrecisionExtension (candidate.threshold p) s) where
  private mk ::
  sourceStep : Step (environment (termReal (realizedFamily family) n)) ta r
  sourceExact : sourceStep = term
  responseStep : Step (environment candidate.real) a s
  responseExact : responseStep = response
  nativeArchive : (environment (family.terms n)).Archive
  archiveExact : nativeArchive = na
  nativeStep : Step (environment (family.terms n)) na r
  nativeExact : nativeStep = executeAt (family.terms n) na r
  nativeNear : Near p nativeStep.code response.code
  nativeNearExact : nativeNear = candidate.converges p n r s nativeStep response hn hr hs
  near : Near p term.code response.code
  nearExact : near = alignOwnedNear term.code response.code
    ((currentReadout _ _ _ nativeStep).trans (realizedTermCode family n r term).symm) rfl nativeNear

def observeCandidate {family : NativeCauchyFamily P baseDepth}
    (candidate : NativeCandidate family) (p n r s : Nat)
    {ta : (environment (termReal (realizedFamily family) n)).Archive}
    {a : (environment candidate.real).Archive}
    (term : Step (environment (termReal (realizedFamily family) n)) ta r)
    (response : Step (environment candidate.real) a s)
    (na : (environment (family.terms n)).Archive)
    (hn : PrecisionExtension (family.modulus p) n) (hr : PrecisionExtension p r)
    (hs : PrecisionExtension (candidate.threshold p) s) :
    CandidateObservation candidate p n r s term response na hn hr hs :=
  let nativeStep := executeAt (family.terms n) na r
  let nativeNear := candidate.converges p n r s nativeStep response hn hr hs
  let near := alignOwnedNear term.code response.code
    ((currentReadout _ _ _ nativeStep).trans (realizedTermCode family n r term).symm) rfl nativeNear
  ⟨term, rfl, response, rfl, na, rfl, nativeStep, rfl, nativeNear, rfl, near, rfl⟩

/-- Projection into the old uniqueness interface. It explicitly observes a
fresh native counterpart; it does not cast/recover the source Step as native. -/
def asExecutedCandidate {family : NativeCauchyFamily P baseDepth} (candidate : NativeCandidate family) :
    LimitCandidate (realizedFamily family) where
  real := candidate.real
  threshold := candidate.threshold
  converges := by
    intro p n r s ta a term response hn hr hs
    exact (observeCandidate candidate p n r s term response
      (environment (family.terms n)).initialArchive hn hr hs).near

/-- The shared mediator of this theorem is the executed realized source term.
The two native counterparts are additional explicitly declared observations,
not a claim that the original native histories were recovered or shared. -/
def nativeUnique {family : NativeCauchyFamily P baseDepth} (first second : NativeCandidate family) :
    Equivalent first.real second.real × NumericalFutureEquivalent first.real second.real :=
  unique (asExecutedCandidate first) (asExecutedCandidate second)

def nativeAuthoritativeUnique {family : NativeCauchyFamily P baseDepth} (candidate : NativeCandidate family) :
    Equivalent (nativeLimit family) candidate.real × NumericalFutureEquivalent (nativeLimit family) candidate.real :=
  nativeUnique (nativeAuthoritative family) candidate

/-- The old effective source limit is only a downstream numerical view. -/
def nativeProducedLimitCorrespondence (family : NativeCauchyFamily P baseDepth) :
    Equivalent (limitReal (realizedFamily family)) (nativeLimit family) ×
      NumericalFutureEquivalent (limitReal (realizedFamily family)) (nativeLimit family) :=
  authoritativeUnique (asExecutedCandidate (nativeAuthoritative family))

/-- Concrete native completeness: the produced limit, native-term comparison,
rich convergence observation and uniqueness are all derived, not assumed. -/
structure NativeCompleteness (family : NativeCauchyFamily P baseDepth) where
  realized : ExecutedCauchyFamily P baseDepth
  realizedExact : realized = realizedFamily family
  limit : Real P baseDepth
  limitExact : limit = nativeLimit family
  richService : Service P baseDepth
  richServiceExact : richService = nativeEnvironment family
  effectiveLimit : Equivalent (limitReal realized) limit × NumericalFutureEquivalent (limitReal realized) limit
  termsEquivalent : (n : Nat) → Equivalent (termReal realized n) (family.terms n)
  termsFutures : (n : Nat) → NumericalFutureEquivalent (termReal realized n) (family.terms n)
  candidate : NativeCandidate family
  candidateExact : candidate = nativeAuthoritative family
  convergence : (p n r s : Nat) →
    {ta : (environment (family.terms n)).Archive} → {la : (environment (nativeLimit family)).Archive} →
    (term : Step (environment (family.terms n)) ta r) →
    (lim : Step (environment (nativeLimit family)) la s) →
    (hn : PrecisionExtension (family.modulus p) n) →
    (hr : PrecisionExtension p r) → (hs : PrecisionExtension p s) →
    LimitObservation family p n r s term lim hn hr hs
  uniqueness : (other : NativeCandidate family) →
    Equivalent limit other.real × NumericalFutureEquivalent limit other.real

def nativeCompleteness (family : NativeCauchyFamily P baseDepth) : NativeCompleteness family where
  realized := realizedFamily family
  realizedExact := rfl
  limit := nativeLimit family
  limitExact := rfl
  richService := nativeEnvironment family
  richServiceExact := rfl
  effectiveLimit := nativeProducedLimitCorrespondence family
  termsEquivalent := realizedTermEquivalent family
  termsFutures := realizedTermFutures family
  candidate := nativeAuthoritative family
  candidateExact := rfl
  convergence := observeLimit family
  uniqueness := nativeAuthoritativeUnique


end RelationalPerimeter.Constitution.Reals.RelationalRealNativeCauchy

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealNativeCauchy.PairObservation
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealNativeCauchy.observePair
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealNativeCauchy.toEffectiveFamily
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealNativeCauchy.realizedFamily
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealNativeCauchy.realizedTermCode
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealNativeCauchy.realizedTermEquivalent
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealNativeCauchy.realizedTermFutures
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealNativeCauchy.sourceReadoutExact
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealNativeCauchy.diagonalReadoutExact
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealNativeCauchy.sourceToLimit
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealNativeCauchy.LimitObservation
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealNativeCauchy.observeLimit
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealNativeCauchy.NativeCandidate
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealNativeCauchy.nativeAuthoritative
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealNativeCauchy.CandidateObservation
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealNativeCauchy.observeCandidate
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealNativeCauchy.asExecutedCandidate
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealNativeCauchy.nativeUnique
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealNativeCauchy.nativeAuthoritativeUnique
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealNativeCauchy.nativeProducedLimitCorrespondence
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealNativeCauchy.NativeCompleteness
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealNativeCauchy.nativeCompleteness
/- AXIOM_AUDIT_END -/
