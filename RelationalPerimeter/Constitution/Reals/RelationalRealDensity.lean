import RelationalPerimeter.Constitution.Reals.RelationalRealOrderedField
import RelationalPerimeter.Constitution.Reals.DyadicDensity

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-! Finite executed density and natural bounds. The selector is not a new
persistent service: its stored output generates native constant runtimes.
Rich witnesses/archives never enter those constants' compact environments. -/
namespace RelationalPerimeter.Constitution.Reals.RelationalRealDensity
open StrongPerimetralTurning RuntimeCorrespondence HeterogeneousRealRuntime
open RelationalRealAddition RelationalRealOrder ConstitutiveRuntime DyadicDensity
variable {P : CircularPresentation} {baseDepth : Nat}

structure Held {α : Type} (original : α) where
  private mk ::
  value : α
  exact : value = original

def dyadic (P : CircularPresentation) (baseDepth : Nat) (code : SignedDyadicCode) : Real P baseDepth :=
  .leaf (constantRuntime P baseDepth code)

def dyadicStepSame {code : SignedDyadicCode} {archive : (environment (dyadic P baseDepth code)).Archive}
    {p : Nat} (step : Step (environment (dyadic P baseDepth code)) archive p) : SameValue step.code code :=
  constantRuntimeReadoutSameValue P baseDepth code step.resource

def densityProgram {a b : Real P baseDepth} (origin : StrictOrder a b) : Program Unit where
  ReceivedContext _ := Held origin
  SearchResult _ := Held origin
  ActionResult _ _ := Bisection origin.separation
  Accepted _ _ acted := StrictSeparation (origin.accuracy + 1) origin.pair.left.code acted.code ×
    StrictSeparation (origin.accuracy + 1) acted.code origin.pair.right.code
  Authorization _ _ _ _ := Unit
  Decomposition _ _ acted _ _ := Held acted
  Continuation _ _ acted _ _ _ := Held acted
  Stored _ _ acted := Held acted
  stamp _ := .limit origin.accuracy
  receive _ := ⟨origin, rfl⟩
  search _ received := received
  act _ searched := by
    let result := bisect searched.value.separation
    rw [searched.exact] at result
    exact result
  preserves _ _ acted := ⟨acted.leftMargin, acted.rightMargin⟩
  authorize _ _ _ _ := ()
  decompose _ _ acted _ _ := ⟨acted, rfl⟩
  resume _ _ _ _ _ decomposed := decomposed
  store _ _ _ _ _ _ continued := continued
  actionCode acted := acted.code
  read stored := stored.value.code
  readStoredExact stored := congrArg Bisection.code stored.exact

def densityMargins {a b : Real P baseDepth} {origin : StrictOrder a b} {journal : Journal P baseDepth}
    (action : ExecutedRequest (densityProgram origin) P journal ()) :
    StrictSeparation (origin.accuracy + 1) origin.pair.left.code action.readout ×
      StrictSeparation (origin.accuracy + 1) action.readout origin.pair.right.code := by
  rw [action.readout_is_storedAction]
  exact action.memory.continued.authorized.accepted

theorem densityReceivesWitness {a b : Real P baseDepth} {origin : StrictOrder a b} {journal : Journal P baseDepth}
    (action : ExecutedRequest (densityProgram origin) P journal ()) :
    action.memory.continued.authorized.acted.searched.received.context.value = origin :=
  congrArg Held.value action.receivedContext_is_produced

structure Density {a b : Real P baseDepth} (origin : StrictOrder a b) (journal : Journal P baseDepth) where
  private mk ::
  action : ExecutedRequest (densityProgram origin) P journal ()
  target : Real P baseDepth
  targetExact : target = dyadic P baseDepth action.readout
  left : ComparisonAttempt (environment a) (environment target) origin.pair.left.next
    (environment target).initialArchive (origin.accuracy + 3) (origin.accuracy + 6)
  right : ComparisonAttempt (environment target) (environment b) left.pair.right.next
    origin.pair.right.next (origin.accuracy + 3) (origin.accuracy + 6)
  leftNear : Near (origin.accuracy + 3) origin.pair.left.code left.pair.left.code
  rightNear : Near (origin.accuracy + 3) origin.pair.right.code right.pair.right.code
  leftMargin : StrictSeparation (origin.accuracy + 3) left.pair.left.code left.pair.right.code
  rightMargin : StrictSeparation (origin.accuracy + 3) right.pair.left.code right.pair.right.code

def produceDensity {a b : Real P baseDepth} (origin : StrictOrder a b) (journal : Journal P baseDepth) :
    Density origin journal := by
  let action := execute (densityProgram origin) P journal ()
  let target := dyadic P baseDepth action.readout
  let left := produceComparison (environment a) (environment target) origin.pair.left.next
    (environment target).initialArchive (origin.accuracy + 3) (origin.accuracy + 6) (PrecisionExtension.refl _)
  let right := produceComparison (environment target) (environment b) left.pair.right.next
    origin.pair.right.next (origin.accuracy + 3) (origin.accuracy + 6) (PrecisionExtension.refl _)
  let first := (coherent a).near (origin.accuracy + 3) _ _ origin.pair.left left.pair.left
    origin.beyond (PrecisionExtension.first _ 3)
  let second := (coherent b).near (origin.accuracy + 3) _ _ origin.pair.right right.pair.right
    origin.beyond (PrecisionExtension.first _ 3)
  have lo := strengthenSeparation (densityMargins action).1 first
    ((dyadicStepSame left.pair.right).symm.toNear (origin.accuracy + 3))
  have hi := strengthenSeparation (densityMargins action).2
    ((dyadicStepSame right.pair.left).symm.toNear (origin.accuracy + 3)) second
  exact ⟨action, target, rfl, left, right, first, second, lo, hi⟩

def Density.orders {a b : Real P baseDepth} {origin : StrictOrder a b} {journal : Journal P baseDepth}
    (packet : Density origin journal) : StrictOrder a packet.target × StrictOrder packet.target b :=
  ⟨packet.left.forward packet.leftMargin, packet.right.forward packet.rightMargin⟩

def dense {a b : Real P baseDepth} (origin : StrictOrder a b) : Density origin (Journal.root P baseDepth) :=
  produceDensity origin (Journal.root P baseDepth)

def boundProgram {source : Real P baseDepth} {archive : (environment source).Archive}
    (probe : Step (environment source) archive 2) : Program Unit where
  ReceivedContext _ := Held probe
  SearchResult _ := Held probe
  ActionResult _ _ := NaturalBounds probe.code
  Accepted _ _ acted := StrictSeparation 0 probe.code (naturalCode acted.upper) ×
    StrictSeparation 0 (negativeNaturalCode acted.lower) probe.code
  Authorization _ _ _ _ := Unit
  Decomposition _ _ acted _ _ := Held acted
  Continuation _ _ acted _ _ _ := Held acted
  Stored _ _ acted := Held acted
  stamp _ := .limit 2
  receive _ := ⟨probe, rfl⟩
  search _ received := received
  act _ searched := by
    let result := naturalBounds searched.value.code
    rw [searched.exact] at result
    exact result
  preserves _ _ acted := ⟨acted.upperMargin, acted.lowerMargin⟩
  authorize _ _ _ _ := ()
  decompose _ _ acted _ _ := ⟨acted, rfl⟩
  resume _ _ _ _ _ decomposed := decomposed
  store _ _ _ _ _ _ continued := continued
  actionCode acted := naturalCode acted.upper
  read stored := naturalCode stored.value.upper
  readStoredExact stored := congrArg (fun result => naturalCode result.upper) stored.exact

def boundMargins {source : Real P baseDepth} {archive : (environment source).Archive}
    {probe : Step (environment source) archive 2} {journal : Journal P baseDepth}
    (action : ExecutedRequest (boundProgram probe) P journal ()) :
    StrictSeparation 0 probe.code (naturalCode action.stored.value.upper) ×
      StrictSeparation 0 (negativeNaturalCode action.stored.value.lower) probe.code := by
  rw [action.stored.exact]
  exact action.memory.continued.authorized.accepted

/-- Bilateral executed Archimedean bound: -M < source < N, with M,N natural.
The source chain is current archive -> probe -> lower comparison -> upper.
No fresh probe or initial source archive can replace these successors. -/
structure NaturalBound (source : Real P baseDepth) (archive : (environment source).Archive)
    (journal : Journal P baseDepth) where
  private mk ::
  probe : Step (environment source) archive 2
  action : ExecutedRequest (boundProgram probe) P journal ()
  lowerTarget : Real P baseDepth
  lowerExact : lowerTarget = dyadic P baseDepth (negativeNaturalCode action.stored.value.lower)
  upperTarget : Real P baseDepth
  upperExact : upperTarget = dyadic P baseDepth (naturalCode action.stored.value.upper)
  lower : ComparisonAttempt (environment lowerTarget) (environment source)
    (environment lowerTarget).initialArchive probe.next 2 5
  upper : ComparisonAttempt (environment source) (environment upperTarget)
    lower.pair.right.next (environment upperTarget).initialArchive 2 5
  lowerNear : Near 2 probe.code lower.pair.right.code
  upperNear : Near 2 probe.code upper.pair.left.code
  lowerMargin : StrictSeparation 2 lower.pair.left.code lower.pair.right.code
  upperMargin : StrictSeparation 2 upper.pair.left.code upper.pair.right.code

def produceNaturalBound (source : Real P baseDepth) (archive : (environment source).Archive)
    (journal : Journal P baseDepth) : NaturalBound source archive journal := by
  let probe := executeAt source archive 2
  let action := execute (boundProgram probe) P journal ()
  let lowerTarget := dyadic P baseDepth (negativeNaturalCode action.stored.value.lower)
  let upperTarget := dyadic P baseDepth (naturalCode action.stored.value.upper)
  let lower := produceComparison (environment lowerTarget) (environment source)
    (environment lowerTarget).initialArchive probe.next 2 5 (PrecisionExtension.refl _)
  let upper := produceComparison (environment source) (environment upperTarget)
    lower.pair.right.next (environment upperTarget).initialArchive 2 5 (PrecisionExtension.refl _)
  let lowerNear := (coherent source).near 2 _ _ probe lower.pair.right (PrecisionExtension.refl _) (PrecisionExtension.first _ 3)
  let upperNear := (coherent source).near 2 _ _ probe upper.pair.left (PrecisionExtension.refl _) (PrecisionExtension.first _ 3)
  have lo := strengthenSeparation (boundMargins action).2
    ((dyadicStepSame lower.pair.left).symm.toNear 2) lowerNear
  have hi := strengthenSeparation (boundMargins action).1 upperNear
    ((dyadicStepSame upper.pair.right).symm.toNear 2)
  exact ⟨probe, action, lowerTarget, rfl, upperTarget, rfl, lower, upper, lowerNear, upperNear, lo, hi⟩

def NaturalBound.orders {source : Real P baseDepth} {archive : (environment source).Archive}
    {journal : Journal P baseDepth} (packet : NaturalBound source archive journal) :
    StrictOrder packet.lowerTarget source × StrictOrder source packet.upperTarget :=
  ⟨packet.lower.forward packet.lowerMargin, packet.upper.forward packet.upperMargin⟩

def archimedean (source : Real P baseDepth) : NaturalBound source (environment source).initialArchive
    (Journal.root P baseDepth) := produceNaturalBound source (environment source).initialArchive (Journal.root P baseDepth)

end RelationalPerimeter.Constitution.Reals.RelationalRealDensity

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealDensity.Held
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealDensity.dyadic
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealDensity.dyadicStepSame
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealDensity.densityProgram
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealDensity.densityMargins
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealDensity.densityReceivesWitness
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealDensity.Density
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealDensity.produceDensity
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealDensity.Density.orders
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealDensity.dense
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealDensity.boundProgram
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealDensity.boundMargins
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealDensity.NaturalBound
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealDensity.produceNaturalBound
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealDensity.NaturalBound.orders
#print axioms RelationalPerimeter.Constitution.Reals.RelationalRealDensity.archimedean
/- AXIOM_AUDIT_END -/
