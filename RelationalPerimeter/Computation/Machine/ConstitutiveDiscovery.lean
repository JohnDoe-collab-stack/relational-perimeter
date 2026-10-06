import RelationalPerimeter.Computation.Machine.LiveSearchFrontier

/-! The candidate clause is realized from the received positive constitution.
The current layer comes from the generated witness, not a depth recipe. The
transmitted seed still supplies the action labels. This is a realization of the
same canonical family, not a new search criterion or an information-novelty claim. -/
set_option genInjectivity false
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace ConstitutiveSearch.ReconfigurableMachine.LiveReduction.ConstitutiveDiscovery
open SAT EndogenousDecomposition ConstitutiveGeneration StrongPerimetralTurning
open StrongPerimetralTurning.Example

structure Decoys where
  last : Nat
  clause : Clause
  work : ComparisonWork

theorem measured_ext {α : Type} {expected : α} (one two : MeasuredValue expected)
    (value : one.value = two.value) (work : one.work = two.work) : one = two := by
  cases one; cases two; cases value; cases work; rfl

def initialDecoys : Decoys := ⟨0, [Literal.positive 0], ⟨3, 0⟩⟩

def emitFormation {P : CircularPresentation} {cursor : PerimeterCursor P}
    (atom : FreeKAtom P cursor) (previous : Decoys) : Decoys :=
  match atom with
  | .explicitPole => previous
  | .implicitPole => previous
  | .currentDifference => previous
  | .admissible _ =>
      ⟨previous.last + 2,
        Literal.positive (previous.last + 2) ::
          Literal.positive (previous.last + 1) :: previous.clause,
        previous.work.visit.visit.visit.visit⟩

def foldFormations {P : CircularPresentation} :
    {cursor : PerimeterCursor P} → {difference : BoundaryDifferenceCode P cursor} →
      FreeConstitutionCore P cursor difference → Decoys
  | _, _, .root => initialDecoys
  | _, _, .formed previous layer => emitFormation layer.formationTerm (foldFormations previous)

theorem foldFormations_exact {P : CircularPresentation} {cursor : PerimeterCursor P}
    {difference : BoundaryDifferenceCode P cursor} (core : FreeConstitutionCore P cursor difference) :
    foldFormations core =
      ⟨2 * formationDepth core,
        (constructMeasuredDecoyClause (2 * formationDepth core + 1)).value,
        (constructMeasuredDecoyClause (2 * formationDepth core + 1)).work⟩ := by
  induction core with
  | root => rfl
  | formed previous layer ih =>
      simp only [formationDepth]
      rw [foldFormations, layer.formationTermIsSuccessor]
      dsimp only [emitFormation]
      rw [ih]
      rw [Nat.mul_succ]
      rfl

def previousCore {P : CircularPresentation} :
    {cursor : PerimeterCursor P} → {difference : BoundaryDifferenceCode P cursor} →
      FreeConstitutionCore P cursor difference → Decoys
  | _, _, .root => initialDecoys
  | _, _, .formed previous _ => foldFormations previous

def previousFormations {P : CircularPresentation} (target : PositiveConstitution P) : Decoys :=
  previousCore target.2.1.2

def receivedDecoys {P : CircularPresentation} {source : PositiveConstitution P}
    (target : PositiveConstitution P) (step : GeneratedStep source target) : Decoys :=
  emitFormation step.integratesCurrentDifference.layer.formationTerm (previousFormations target)

theorem receivedDecoys_exact {P : CircularPresentation} {source : PositiveConstitution P}
    (target : PositiveConstitution P) (step : GeneratedStep source target) :
    receivedDecoys target step = foldFormations target.2.1.2 := by
  cases step.formedByFreeLayer
  unfold receivedDecoys previousFormations
  rw [FreeK.formationTerm_is_successor]
  change emitFormation _ (foldFormations source.2.1.2) =
    emitFormation (canonicalFreeLayer source).formationTerm (foldFormations source.2.1.2)
  rw [FreeK.formationTerm_is_successor]

def measuredClause {depth : Nat} (generation : Generation depth) (seed : Nat)
    (seedExact : seed = generatedSearchSeed generation.full) :
    MeasuredValue (distinctDecoyClause (seed + 1)) :=
  let produced := receivedDecoys generation.target generation.generated
  ⟨produced.clause, by
    dsimp only [produced]
    rw [receivedDecoys_exact, foldFormations_exact]
    change (constructMeasuredDecoyClause (2 * positiveDepth generation.target + 1)).value = _
    have same : seed = 2 * positiveDepth generation.target := seedExact
    rw [← same]
    exact (constructMeasuredDecoyClause (seed + 1)).valueExact,
    produced.work⟩

theorem measuredClause_exact {depth : Nat} (generation : Generation depth) (seed : Nat)
    (seedExact : seed = generatedSearchSeed generation.full) :
    measuredClause generation seed seedExact = constructMeasuredDecoyClause (seed + 1) := by
  have data := receivedDecoys_exact generation.target generation.generated
  have fields := data.trans (foldFormations_exact generation.target.2.1.2)
  have work : (measuredClause generation seed seedExact).work =
      (constructMeasuredDecoyClause (seed + 1)).work := by
    change (receivedDecoys generation.target generation.generated).work = _
    rw [fields]
    change (constructMeasuredDecoyClause (2 * positiveDepth generation.target + 1)).work = _
    have same : seed = 2 * positiveDepth generation.target := seedExact
    rw [← same]
  have value := (measuredClause generation seed seedExact).valueExact.trans
    (constructMeasuredDecoyClause (seed + 1)).valueExact.symm
  exact measured_ext _ _ value work

def measuredFormula {depth : Nat} (generation : Generation depth) (seed : Nat)
    (seedExact : seed = generatedSearchSeed generation.full) :
    MeasuredValue (distinctGrowingDiscoveryFormula seed) :=
  let decoys := measuredClause generation seed seedExact
  let selected := growingDiscoverySplitVar seed
  let anchor := growingDiscoveryAnchorVar seed
  let positive := measuredCons (measuredLiteral (.positive selected))
    (measuredCons (measuredLiteral (.positive anchor)) measuredEmptyList)
  let negative := measuredCons (measuredLiteral (.negative selected))
    (measuredCons (measuredLiteral (.positive anchor)) measuredEmptyList)
  measuredCons decoys (measuredCons positive (measuredCons negative measuredEmptyList))

theorem measuredFormula_exact {depth : Nat} (generation : Generation depth) (seed : Nat)
    (seedExact : seed = generatedSearchSeed generation.full) :
    measuredFormula generation seed seedExact = constructMeasuredFormula seed := by
  unfold measuredFormula constructMeasuredFormula
  rw [measuredClause_exact]

def rootFromFormula (seed : Nat) (formula : MeasuredValue (distinctGrowingDiscoveryFormula seed)) :
    MeasuredValue (distinctGrowingDiscoveryRoot seed) :=
  let root := GeneratedStructuralBranchContext.root formula.value
  let indexed := Eq.rec (motive := fun formula _ => GeneratedStructuralBranchContext formula)
    root formula.valueExact
  ⟨indexed, by
    dsimp only [indexed, root]
    cases formula with | mk value same work => cases same; rfl,
    formula.work.visit⟩

def measuredRoot {depth : Nat} (generation : Generation depth) (seed : Nat)
    (seedExact : seed = generatedSearchSeed generation.full) :
    MeasuredValue (distinctGrowingDiscoveryRoot seed) :=
  rootFromFormula seed (measuredFormula generation seed seedExact)

theorem measuredRoot_exact {depth : Nat} (generation : Generation depth) (seed : Nat)
    (seedExact : seed = generatedSearchSeed generation.full) :
    measuredRoot generation seed seedExact = constructMeasuredOperationalRoot seed := by
  exact congrArg (rootFromFormula seed) (measuredFormula_exact generation seed seedExact)

def extractionFromRoot {depth : Nat} (generation : Generation depth) (seed : Nat)
    (seedExact : seed = generatedSearchSeed generation.full)
    (realized : MeasuredValue (distinctGrowingDiscoveryRoot seed)) : GeneratedExtractionBundle generation.full :=
  let same := seedExact.trans (generatedSearchSeed_exact generation.full)
  let indexed := Eq.rec
    (motive := fun index _ => GeneratedStructuralBranchContext (distinctGrowingDiscoveryFormula index))
    realized.value same
  have rootExact : indexed = (constructStage (depth + 1)).operationalRoot := by
    cases same
    dsimp only [indexed]
    exact realized.valueExact.trans (constructStage (depth + 1)).operationalRootExact.symm
  let candidates := runCandidateExtraction indexed
  ⟨indexed, rootExact, candidates, by
    dsimp only [candidates]; rw [rootExact]; rfl, realized.work⟩

def extraction (front : Frontier) : GeneratedExtractionBundle front.generation.full :=
  extractionFromRoot front.generation front.searchSeed front.seedExact
    (measuredRoot front.generation front.searchSeed front.seedExact)

theorem extraction_exact (front : Frontier) :
    extraction front = measuredGeneratedExtractionFromSeed front.generation.full front.searchSeed front.seedExact := by
  exact congrArg (extractionFromRoot front.generation front.searchSeed front.seedExact)
    (measuredRoot_exact front.generation front.searchSeed front.seedExact)

def runExtracted (front : Frontier) (generated : GeneratedExtractionBundle front.generation.full)
    (exactGenerated : generated = measuredGeneratedExtraction front.generation.full) :
    FeedbackDiscoveryFromDataRun front.depth front.generation.full front.provenance :=
  let filtering := filterCandidatesByProvenance front.provenance generated.extraction.candidates
  let candidates := filtering.retained
  let produced := exploreRecordedCandidates generated.operationalRoot candidates
  let outcome := Eq.rec (motive := fun state _ => RecordedDiscoveryOutcome state)
    produced generated.operationalRootExact
  { generated := generated
    generatedExact := exactGenerated
    filtering := filtering
    filteringExact := rfl
    candidates := candidates
    candidatesExact := rfl
    outcome := outcome
    outcomeExact := exploreRecordedCandidates_transport_exact generated.operationalRootExact candidates }

def discover (front : Frontier) : FeedbackDiscoveryFromDataRun front.depth front.generation.full front.provenance :=
  runExtracted front (extraction front)
    ((extraction_exact front).trans (measuredGeneratedExtractionFromSeed_eq _ _ _))

theorem runExtracted_congr (front : Frontier)
    {one two : GeneratedExtractionBundle front.generation.full} (same : one = two)
    (first : one = measuredGeneratedExtraction front.generation.full)
    (second : two = measuredGeneratedExtraction front.generation.full) :
    runExtracted front one first = runExtracted front two second := by
  cases same; rfl

theorem discovery_exact (front : Frontier) : discover front = LiveReduction.discover front := by
  exact runExtracted_congr front (extraction_exact front) _ _

end ConstitutiveSearch.ReconfigurableMachine.LiveReduction.ConstitutiveDiscovery
/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.ReconfigurableMachine.LiveReduction.ConstitutiveDiscovery.initialDecoys
#print axioms ConstitutiveSearch.ReconfigurableMachine.LiveReduction.ConstitutiveDiscovery.emitFormation
#print axioms ConstitutiveSearch.ReconfigurableMachine.LiveReduction.ConstitutiveDiscovery.foldFormations
#print axioms ConstitutiveSearch.ReconfigurableMachine.LiveReduction.ConstitutiveDiscovery.foldFormations_exact
#print axioms ConstitutiveSearch.ReconfigurableMachine.LiveReduction.ConstitutiveDiscovery.receivedDecoys
#print axioms ConstitutiveSearch.ReconfigurableMachine.LiveReduction.ConstitutiveDiscovery.receivedDecoys_exact
#print axioms ConstitutiveSearch.ReconfigurableMachine.LiveReduction.ConstitutiveDiscovery.previousCore
#print axioms ConstitutiveSearch.ReconfigurableMachine.LiveReduction.ConstitutiveDiscovery.previousFormations
#print axioms ConstitutiveSearch.ReconfigurableMachine.LiveReduction.ConstitutiveDiscovery.measuredClause
#print axioms ConstitutiveSearch.ReconfigurableMachine.LiveReduction.ConstitutiveDiscovery.measuredClause_exact
#print axioms ConstitutiveSearch.ReconfigurableMachine.LiveReduction.ConstitutiveDiscovery.measuredFormula_exact
#print axioms ConstitutiveSearch.ReconfigurableMachine.LiveReduction.ConstitutiveDiscovery.measuredFormula
#print axioms ConstitutiveSearch.ReconfigurableMachine.LiveReduction.ConstitutiveDiscovery.rootFromFormula
#print axioms ConstitutiveSearch.ReconfigurableMachine.LiveReduction.ConstitutiveDiscovery.measuredRoot
#print axioms ConstitutiveSearch.ReconfigurableMachine.LiveReduction.ConstitutiveDiscovery.measuredRoot_exact
#print axioms ConstitutiveSearch.ReconfigurableMachine.LiveReduction.ConstitutiveDiscovery.extraction_exact
#print axioms ConstitutiveSearch.ReconfigurableMachine.LiveReduction.ConstitutiveDiscovery.extractionFromRoot
#print axioms ConstitutiveSearch.ReconfigurableMachine.LiveReduction.ConstitutiveDiscovery.extraction
#print axioms ConstitutiveSearch.ReconfigurableMachine.LiveReduction.ConstitutiveDiscovery.runExtracted
#print axioms ConstitutiveSearch.ReconfigurableMachine.LiveReduction.ConstitutiveDiscovery.discover
#print axioms ConstitutiveSearch.ReconfigurableMachine.LiveReduction.ConstitutiveDiscovery.discovery_exact
/- AXIOM_AUDIT_END -/
