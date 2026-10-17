import RelationalPerimeter.Constitution.Reals.RelationalRealCauchy

set_option autoImplicit false
set_option linter.unusedVariables false

/-!
# Uniqueness through one shared executed family term

Two received candidates converge on actual current-archive Steps of the same
executed family. No equivalence is an input field. A rich mediation owns the
three executions and both convergences, and its trace continues their exact
successors before forgetting the mediator in a numerical projection.
-/
namespace RelationalPerimeter.Constitution.Reals.RelationalRealLimitUniqueness
open StrongPerimetralTurning ProducedCompleteness RuntimeCorrespondence
open HeterogeneousRealRuntime RelationalRealAddition RelationalRealCauchy

variable {P : CircularPresentation} {baseDepth : Nat}
variable {family : ExecutedCauchyFamily P baseDepth}

/-- A positive received convergence law, not an assumed terminal equivalence. -/
structure LimitCandidate (family : ExecutedCauchyFamily P baseDepth) where
  real : Real P baseDepth
  threshold : Nat → Nat
  converges : (precision term termPrecision response : Nat) →
    {termArchive : TermArchive family} → {archive : (environment real).Archive} →
    (termStep : Step (environment (termReal family term)) termArchive termPrecision) →
    (candidateStep : Step (environment real) archive response) →
    PrecisionExtension (family.modulus precision) term →
    PrecisionExtension precision termPrecision → PrecisionExtension (threshold precision) response →
    Near precision termStep.code candidateStep.code

def authoritative (family : ExecutedCauchyFamily P baseDepth) : LimitCandidate family where
  real := limitReal family
  threshold := fun precision => precision
  converges := termLimitNear family

def uniquenessThreshold (first second : LimitCandidate family) (precision : Nat) : Nat :=
  first.threshold (Nat.succ precision) + second.threshold (Nat.succ precision)

def firstExtension (first second : LimitCandidate family)
    (query : LimitQuery (uniquenessThreshold first second)) :
    PrecisionExtension (first.threshold (Nat.succ query.accuracy)) query.leftResponse :=
  (PrecisionExtension.first _ _).trans query.leftBeyond

def secondExtension (first second : LimitCandidate family)
    (query : LimitQuery (uniquenessThreshold first second)) :
    PrecisionExtension (second.threshold (Nat.succ query.accuracy)) query.rightResponse :=
  (PrecisionExtension.second _ _).trans query.rightBeyond

/-- Rich incoming archives are data, not merely erased indices of Steps. -/
structure Mediation (first second : LimitCandidate family)
    (termArchive : TermArchive family)
    (firstArchive : (environment first.real).Archive) (secondArchive : (environment second.real).Archive)
    (query : LimitQuery (uniquenessThreshold first second)) where
  private mk ::
  archives : TermArchive family × (environment first.real).Archive × (environment second.real).Archive
  archivesExact : archives = ⟨termArchive, firstArchive, secondArchive⟩
  termStep : Step (environment (termReal family (family.modulus (Nat.succ query.accuracy))))
    termArchive (Nat.succ query.accuracy)
  firstStep : Step (environment first.real) firstArchive query.leftResponse
  secondStep : Step (environment second.real) secondArchive query.rightResponse
  termExact : termStep = executeAt (termReal family (family.modulus (Nat.succ query.accuracy)))
    termArchive (Nat.succ query.accuracy)
  firstExact : firstStep = executeAt first.real firstArchive query.leftResponse
  secondExact : secondStep = executeAt second.real secondArchive query.rightResponse
  firstNear : Near (Nat.succ query.accuracy) termStep.code firstStep.code
  firstNearExact : firstNear = first.converges (Nat.succ query.accuracy)
    (family.modulus (Nat.succ query.accuracy)) (Nat.succ query.accuracy) query.leftResponse
    termStep firstStep (.refl _) (.refl _) (firstExtension first second query)
  secondNear : Near (Nat.succ query.accuracy) termStep.code secondStep.code
  secondNearExact : secondNear = second.converges (Nat.succ query.accuracy)
    (family.modulus (Nat.succ query.accuracy)) (Nat.succ query.accuracy) query.rightResponse
    termStep secondStep (.refl _) (.refl _) (secondExtension first second query)
  near : Near query.accuracy firstStep.code secondStep.code
  nearExact : near = Near.compose firstNear.symm secondNear

/-- Produce all three Steps once, then consume the same term in both laws. -/
def mediate (first second : LimitCandidate family) (termArchive : TermArchive family)
    (firstArchive : (environment first.real).Archive) (secondArchive : (environment second.real).Archive)
    (query : LimitQuery (uniquenessThreshold first second)) :
    Mediation first second termArchive firstArchive secondArchive query :=
  let termStep := executeAt (termReal family (family.modulus (Nat.succ query.accuracy)))
    termArchive (Nat.succ query.accuracy)
  let firstStep := executeAt first.real firstArchive query.leftResponse
  let secondStep := executeAt second.real secondArchive query.rightResponse
  let firstNear := first.converges (Nat.succ query.accuracy)
    (family.modulus (Nat.succ query.accuracy)) (Nat.succ query.accuracy) query.leftResponse
    termStep firstStep (.refl _) (.refl _) (firstExtension first second query)
  let secondNear := second.converges (Nat.succ query.accuracy)
    (family.modulus (Nat.succ query.accuracy)) (Nat.succ query.accuracy) query.rightResponse
    termStep secondStep (.refl _) (.refl _) (secondExtension first second query)
  ⟨⟨termArchive, firstArchive, secondArchive⟩, rfl,
    termStep, firstStep, secondStep, rfl, rfl, rfl,
    firstNear, rfl, secondNear, rfl, Near.compose firstNear.symm secondNear, rfl⟩

set_option genSizeOf false in
/-- The mediator archive is shared across changing indices at successive queries. -/
inductive UniquenessTrace (first second : LimitCandidate family) :
    TermArchive family → (environment first.real).Archive → (environment second.real).Archive →
    List (LimitQuery (uniquenessThreshold first second)) → Type
  | done (termArchive : TermArchive family)
      (firstArchive : (environment first.real).Archive) (secondArchive : (environment second.real).Archive) :
      UniquenessTrace first second termArchive firstArchive secondArchive []
  | step {termArchive : TermArchive family}
      {firstArchive : (environment first.real).Archive} {secondArchive : (environment second.real).Archive}
      {query : LimitQuery (uniquenessThreshold first second)}
      {remaining : List (LimitQuery (uniquenessThreshold first second))}
      (packet : Mediation first second termArchive firstArchive secondArchive query)
      (later : UniquenessTrace first second packet.termStep.next packet.firstStep.next packet.secondStep.next remaining) :
      UniquenessTrace first second termArchive firstArchive secondArchive (query :: remaining)

def produceTrace (first second : LimitCandidate family) :
    (termArchive : TermArchive family) → (firstArchive : (environment first.real).Archive) →
    (secondArchive : (environment second.real).Archive) →
    (queries : List (LimitQuery (uniquenessThreshold first second))) →
    UniquenessTrace first second termArchive firstArchive secondArchive queries
  | termArchive, firstArchive, secondArchive, [] => .done termArchive firstArchive secondArchive
  | termArchive, firstArchive, secondArchive, query :: remaining =>
      let packet := mediate first second termArchive firstArchive secondArchive query
      .step packet (produceTrace first second packet.termStep.next packet.firstStep.next packet.secondStep.next remaining)

namespace UniquenessTrace

def toNumerical {first second : LimitCandidate family} :
    {termArchive : TermArchive family} → {firstArchive : (environment first.real).Archive} →
    {secondArchive : (environment second.real).Archive} →
    {queries : List (LimitQuery (uniquenessThreshold first second))} →
    UniquenessTrace first second termArchive firstArchive secondArchive queries →
    NumericalTrace first.real second.real (uniquenessThreshold first second) firstArchive secondArchive queries
  | _, _, _, [], .done _ firstArchive secondArchive => .done firstArchive secondArchive
  | _, _, _, _ :: _, .step packet later =>
      .step packet.firstStep packet.secondStep packet.firstExact packet.secondExact packet.near later.toNumerical

def length {first second : LimitCandidate family} :
    {termArchive : TermArchive family} → {firstArchive : (environment first.real).Archive} →
    {secondArchive : (environment second.real).Archive} →
    {queries : List (LimitQuery (uniquenessThreshold first second))} →
    UniquenessTrace first second termArchive firstArchive secondArchive queries → Nat
  | _, _, _, [], .done _ _ _ => 0
  | _, _, _, _ :: _, .step _ later => Nat.succ later.length

def final {first second : LimitCandidate family} :
    {termArchive : TermArchive family} → {firstArchive : (environment first.real).Archive} →
    {secondArchive : (environment second.real).Archive} →
    {queries : List (LimitQuery (uniquenessThreshold first second))} →
    UniquenessTrace first second termArchive firstArchive secondArchive queries →
    TermArchive family × (environment first.real).Archive × (environment second.real).Archive
  | _, _, _, [], .done termArchive firstArchive secondArchive => ⟨termArchive, firstArchive, secondArchive⟩
  | _, _, _, _ :: _, .step _ later => later.final

end UniquenessTrace

theorem produceTrace_length (first second : LimitCandidate family) (termArchive : TermArchive family)
    (firstArchive : (environment first.real).Archive) (secondArchive : (environment second.real).Archive)
    (queries : List (LimitQuery (uniquenessThreshold first second))) :
    (produceTrace first second termArchive firstArchive secondArchive queries).length = queries.length := by
  induction queries generalizing termArchive firstArchive secondArchive with
  | nil => rfl
  | cons query remaining ih => exact congrArg Nat.succ (ih _ _ _)

/-- One chronological rich trace is produced for the whole list before projection. -/
def numericalFutures (first second : LimitCandidate family) : NumericalFutureEquivalent first.real second.real where
  threshold := uniquenessThreshold first second
  traces firstArchive secondArchive queries :=
    let rich := produceTrace first second (termEnvironment family 0).initialArchive firstArchive secondArchive queries
    rich.toNumerical

def uniqueness (first second : LimitCandidate family) : Equivalent first.real second.real :=
  (numericalFutures first second).toEquivalent

/-- The two terminal views share this one numerical-future construction. -/
def unique (first second : LimitCandidate family) :
    Equivalent first.real second.real × NumericalFutureEquivalent first.real second.real :=
  let futures := numericalFutures first second
  ⟨futures.toEquivalent, futures⟩

def authoritativeUnique (candidate : LimitCandidate family) :
    Equivalent (limitReal family) candidate.real × NumericalFutureEquivalent (limitReal family) candidate.real :=
  unique (authoritative family) candidate

end RelationalPerimeter.Constitution.Reals.RelationalRealLimitUniqueness

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealLimitUniqueness.LimitCandidate
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealLimitUniqueness.authoritative
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealLimitUniqueness.uniquenessThreshold
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealLimitUniqueness.firstExtension
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealLimitUniqueness.secondExtension
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealLimitUniqueness.Mediation
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealLimitUniqueness.mediate
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealLimitUniqueness.UniquenessTrace
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealLimitUniqueness.produceTrace
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealLimitUniqueness.UniquenessTrace.toNumerical
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealLimitUniqueness.UniquenessTrace.length
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealLimitUniqueness.UniquenessTrace.final
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealLimitUniqueness.produceTrace_length
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealLimitUniqueness.numericalFutures
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealLimitUniqueness.uniqueness
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealLimitUniqueness.unique
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealLimitUniqueness.authoritativeUnique
/- AXIOM_AUDIT_END -/
