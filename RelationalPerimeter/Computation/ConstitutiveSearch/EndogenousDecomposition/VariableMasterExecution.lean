import RelationalPerimeter.Computation.ConstitutiveSearch.EndogenousDecomposition.MasterResourceExecution
import RelationalPerimeter.Computation.ConstitutiveSearch.SAT.StructuralGlobalContextRelation

/-!
# Search-dependent frontiers within the master resource execution

The received formula is problem data, not a supplied partition. The selected
variable is read from the executed master head. Generated contexts are opened
before relation search, and the actual retained frontier is passed to the next
head. SAT acceptance and formation remain separate. Failure is relative to
the selected flip search; no claim of global irreducibility is made.

This extends the master executor without altering its audited canonical
regrouping. The frontier engine traverses its explicit input frontier; it is
not a theorem of non-extensive cost for arbitrary received formulas.
-/
set_option genInjectivity false
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace ConstitutiveSearch.EndogenousDecomposition.VariableMaster
open SAT Resources

abbrev States (formula : Cnf) := List (GeneratedStructuralBranchContext formula)

structure Opening (formula : Cnf) (source : States formula) where
  frontier : States formula
  preservation : AcceptedFrontierPreservation (generatedStructuralBranchSystem formula)
    source frontier

/-- Freshness is checked on the received constituted provenance, not assumed. -/
def openFrontier (formula : Cnf) (selected : Var) :
    (source : States formula) → Opening formula source
  | [] => ⟨[], .identity _ []⟩
  | parent :: rest =>
      let tail := openFrontier formula selected rest
      if freshCheck : structuralDecisionsAvoidCheck selected parent.context.decisions = true then
        let fresh := structuralDecisionsAvoid_of_check_true _ _ freshCheck
        let left := parent.child selected false fresh
        let right := parent.child selected true fresh
        ⟨left :: right :: tail.frontier,
          tail.preservation.prepend |>.trans
            (.expandHead (generatedStructuralSplit parent selected fresh))⟩
      else
        ⟨parent :: tail.frontier, tail.preservation.prepend⟩

def nextCursor (cursor : MasterResources.Cursor) : MasterResources.Cursor :=
  (MasterResources.continueWithReferences cursor.headResources.1 .here
    (.prior (.prior (.prior (.prior cursor.fresh))))).1

/-- Both values are read from one master resource production. -/
structure MasterHead (cursor : MasterResources.Cursor) where
  private mk ::
  head : CausalOperationalHead cursor.state cursor.context
  headExact : head = cursor.head
  next : MasterResources.Cursor
  nextExact : next = nextCursor cursor
  boundaryExact : next.boundary =
    ⟨cursor.depth + 1, head.stage.next, head.run.nextRun.next, head.production.nextContext⟩

def masterHead (cursor : MasterResources.Cursor) : MasterHead cursor :=
  let discovered := cursor.support.extend (MasterResources.discover cursor.source)
  let applied := discovered.extend
    (MasterResources.applyStage .here (.prior cursor.fresh))
  let decomposed := applied.extend
    (MasterResources.decompose (.prior (.prior cursor.past)) .here)
  let assembled := decomposed.extend (MasterResources.assemble .here)
  ⟨(assembled.read .here).down, rfl,
    (MasterResources.continueWithReferences assembled .here
      (.prior (.prior (.prior (.prior cursor.fresh))))).1, rfl, rfl⟩

def selected {cursor : MasterResources.Cursor} (resources : MasterHead cursor) : Var :=
  resources.head.stage.discovery.var

abbrev Reduction (formula : Cnf) (var : Var) {source : States formula}
    (opening : Opening formula source) :=
  AcceptedIrreducibleFrontierReduction (system := generatedStructuralBranchSystem formula)
    (generatedStructuralFlipAtSearch formula var)
    (generatedStructuralFlipAtAction formula var)
    opening.frontier

inductive Kind : Type 3 where
  | cursor
  | frontier (formula : Cnf)
  | head (cursor : MasterResources.Cursor)
  | opening (formula : Cnf) (var : Var) (source : States formula)
  | reduction (formula : Cnf) (var : Var) (source : States formula)
      (opening : Opening formula source)

def Value : Kind → Type 3
  | .cursor => MasterResources.Cursor
  | .frontier formula => ULift.{3} (States formula)
  | .head cursor => MasterHead cursor
  | .opening formula _ source => ULift.{3} (Opening formula source)
  | .reduction formula var _ opening => ULift.{3} (Reduction formula var opening)

def produceHead {context : List Kind} (cursor : Ref context .cursor) :
    Producer Value context where
  inputKinds := [.cursor]
  inputs := .cons cursor .nil
  outputKind := fun args => .head args.1
  operation := fun args => masterHead args.1

def produceOpening {context : List Kind} {cursor : MasterResources.Cursor}
    {formula : Cnf} (head : Ref context (.head cursor))
    (frontier : Ref context (.frontier formula)) : Producer Value context where
  inputKinds := [.head cursor, .frontier formula]
  inputs := .cons head (.cons frontier .nil)
  outputKind := fun args => .opening formula (selected args.1) args.2.1.down
  operation := fun args => ⟨openFrontier formula (selected args.1) args.2.1.down⟩

def produceReduction {context : List Kind} {formula : Cnf} {var : Var}
    {source : States formula} (opening : Ref context (.opening formula var source)) :
    Producer Value context where
  inputKinds := [.opening formula var source]
  inputs := .cons opening .nil
  outputKind := fun args => .reduction formula var source args.1.down
  operation := fun args => ⟨normalizeGeneratedStructuralFrontierByFlip formula var
    args.1.down.frontier⟩

def produceNextFrontier {context : List Kind} {formula : Cnf} {var : Var}
    {source : States formula} {opening : Opening formula source}
    (reduction : Ref context (.reduction formula var source opening)) :
    Producer Value context where
  inputKinds := [.reduction formula var source opening]
  inputs := .cons reduction .nil
  outputKind := fun _ => .frontier formula
  operation := fun args => ⟨args.1.down.retained⟩

def produceNextCursor {context : List Kind} {cursor : MasterResources.Cursor}
    (head : Ref context (.head cursor)) : Producer Value context where
  inputKinds := [.head cursor]
  inputs := .cons head .nil
  outputKind := fun _ => .cursor
  operation := fun args => args.1.next

def initialSupport (cursor : MasterResources.Cursor) (formula : Cnf)
    (source : States formula) : Support Value [.frontier formula, .cursor] :=
  .given (⟨source⟩, cursor, PUnit.unit)

structure Step (cursor : MasterResources.Cursor) (formula : Cnf) (source : States formula) where
  private mk ::
  resources : MasterHead cursor
  resourcesExact : resources = masterHead cursor
  opening : Opening formula source
  openingExact : opening = openFrontier formula (selected resources) source
  reduction : Reduction formula (selected resources) opening
  reductionExact : reduction = normalizeGeneratedStructuralFrontierByFlip formula
    (selected resources) opening.frontier
  next : MasterResources.Cursor
  nextExact : next = resources.next
  frontier : States formula
  frontierExact : frontier = reduction.retained

set_option maxHeartbeats 2000000 in
def step (cursor : MasterResources.Cursor) (formula : Cnf) (source : States formula) :
    Step cursor formula source :=
  let initial := initialSupport cursor formula source
  let head := initial.extend (produceHead (.prior .here))
  let opening := head.extend (produceOpening .here (.prior .here))
  let reduced := opening.extend (produceReduction .here)
  let nextFrontier := reduced.extend (produceNextFrontier .here)
  let support := nextFrontier.extend (produceNextCursor (.prior (.prior (.prior .here))))
  ⟨support.read (.prior (.prior (.prior (.prior .here)))), rfl,
    (support.read (.prior (.prior (.prior .here)))).down, rfl,
    (support.read (.prior (.prior .here))).down, rfl,
    support.read .here, rfl, (support.read (.prior .here)).down, rfl⟩

def Step.preservation {cursor : MasterResources.Cursor} {formula : Cnf} {source : States formula}
    (produced : Step cursor formula source) :
    AcceptedFrontierPreservation (generatedStructuralBranchSystem formula) source produced.frontier :=
  produced.frontierExact.symm ▸ (produced.opening.preservation.trans produced.reduction.preservation)

theorem step_frontier_exact (cursor : MasterResources.Cursor) (formula : Cnf)
    (source : States formula) :
    (step cursor formula source).frontier =
      (normalizeGeneratedStructuralFrontierByFlip formula (selected (masterHead cursor))
        (openFrontier formula (selected (masterHead cursor)) source).frontier).retained := by
  let produced := step cursor formula source
  calc
    produced.frontier = produced.reduction.retained := produced.frontierExact
    _ = (normalizeGeneratedStructuralFrontierByFlip formula (selected produced.resources)
        produced.opening.frontier).retained := congrArg (fun reduction => reduction.retained) produced.reductionExact
    _ = _ := by rw [produced.openingExact, produced.resourcesExact]

theorem step_viable_iff (cursor : MasterResources.Cursor) (formula : Cnf) (source : States formula) :
    FrontierViable (generatedStructuralBranchSystem formula) source ↔
      FrontierViable (generatedStructuralBranchSystem formula) (step cursor formula source).frontier :=
  (step cursor formula source).preservation.viable_iff

theorem step_next_exact (cursor : MasterResources.Cursor) (formula : Cnf) (source : States formula) :
    (step cursor formula source).next = nextCursor cursor :=
  (step cursor formula source).nextExact.trans (step cursor formula source).resources.nextExact

/-- A tail is indexed by both the actual master successor and retained problem. -/
inductive History : (count : Nat) → (cursor : MasterResources.Cursor) →
    (formula : Cnf) → States formula → Type 3 where
  | nil (cursor : MasterResources.Cursor) (formula : Cnf) (source : States formula) :
      History 0 cursor formula source
  | cons {count : Nat} {cursor : MasterResources.Cursor} {formula : Cnf} {source : States formula}
      (head : Step cursor formula source)
      (tail : History count head.next formula head.frontier) :
      History (count + 1) cursor formula source

def execute : (count : Nat) → (cursor : MasterResources.Cursor) →
    (formula : Cnf) → (source : States formula) → History count cursor formula source
  | 0, cursor, formula, source => .nil cursor formula source
  | count + 1, cursor, formula, source =>
      let produced := step cursor formula source
      .cons produced (execute count produced.next formula produced.frontier)

def Step.assemble {count : Nat} {cursor : MasterResources.Cursor} {formula : Cnf}
    {source : States formula} (head : Step cursor formula source)
    (rest : CausalOperationalExecutionHistory (_count := count) head.next.state head.next.context ×
      MasterResources.Cursor) :
    CausalOperationalExecutionHistory (_count := count + 1) cursor.state cursor.context ×
      MasterResources.Cursor :=
  let produced := head.resources.head
  let same := (congrArg MasterResources.Cursor.boundary head.nextExact).trans
    head.resources.boundaryExact
  let transported := MasterResources.transportHistory same rest.1
  (CausalOperationalExecutionHistory.step produced.stage produced.run produced.production transported,
    rest.2)

set_option maxHeartbeats 2000000 in
theorem Step.assemble_master {count : Nat} {cursor : MasterResources.Cursor} {formula : Cnf}
    {source : States formula} (produced : Step cursor formula source) :
    produced.assemble (MasterResources.execute count produced.next) =
      MasterResources.execute (count + 1) cursor := by
  rw [MasterResources.execute_succ]
  rcases produced with ⟨resources, resourcesExact, opening, openingExact,
    reduction, reductionExact, next, nextExact, frontier, frontierExact⟩
  cases resourcesExact
  cases nextExact
  rfl

def History.erasure : {count : Nat} → {cursor : MasterResources.Cursor} →
    {formula : Cnf} → {source : States formula} → History count cursor formula source →
    CausalOperationalExecutionHistory (_count := count) cursor.state cursor.context × MasterResources.Cursor
  | _, cursor, _, _, .nil _ _ _ => (.nil cursor.state cursor.context, cursor)
  | _, _, _, _, .cons head tail => head.assemble tail.erasure

def History.finish : {count : Nat} → {cursor : MasterResources.Cursor} →
    {formula : Cnf} → {source : States formula} → History count cursor formula source → States formula
  | _, _, _, source, .nil _ _ _ => source
  | _, _, _, _, .cons _ tail => tail.finish

def History.preservation : {count : Nat} → {cursor : MasterResources.Cursor} →
    {formula : Cnf} → {source : States formula} → (history : History count cursor formula source) →
    AcceptedFrontierPreservation (generatedStructuralBranchSystem formula) source history.finish
  | _, _, _, _, .nil _ _ _ => .identity _ _
  | _, _, _, _, .cons head tail => head.preservation.trans tail.preservation

theorem execute_erases (count : Nat) (cursor : MasterResources.Cursor)
    (formula : Cnf) (source : States formula) :
    (execute count cursor formula source).erasure = MasterResources.execute count cursor := by
  induction count generalizing cursor source with
  | zero => rfl
  | succ count ih =>
      change (step cursor formula source).assemble
        (execute count (step cursor formula source).next formula
          (step cursor formula source).frontier).erasure = _
      rw [ih]
      exact (step cursor formula source).assemble_master

theorem execute_viable_iff (count : Nat) (cursor : MasterResources.Cursor)
    (formula : Cnf) (source : States formula) :
    FrontierViable (generatedStructuralBranchSystem formula) source ↔
      FrontierViable (generatedStructuralBranchSystem formula)
        (execute count cursor formula source).finish :=
  (execute count cursor formula source).preservation.viable_iff

/-- The first production is constructed without receiving the horizon or tail. -/
def executeHead (cursor : MasterResources.Cursor) (formula : Cnf) (source : States formula) :=
  step cursor formula source

theorem head_horizon_independent (cursor : MasterResources.Cursor)
    (formula : Cnf) (source : States formula) (count : Nat) :
    execute (count + 1) cursor formula source =
      History.cons (executeHead cursor formula source)
        (execute count (executeHead cursor formula source).next formula
          (executeHead cursor formula source).frontier) := rfl

end ConstitutiveSearch.EndogenousDecomposition.VariableMaster
/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableMaster.openFrontier
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableMaster.produceHead
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableMaster.produceOpening
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableMaster.produceReduction
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableMaster.produceNextFrontier
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableMaster.produceNextCursor
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableMaster.step
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableMaster.Step.preservation
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableMaster.masterHead
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableMaster.step_frontier_exact
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableMaster.step_viable_iff
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableMaster.step_next_exact
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableMaster.execute
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableMaster.Step.assemble_master
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableMaster.execute_erases
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableMaster.execute_viable_iff
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableMaster.head_horizon_independent
/- AXIOM_AUDIT_END -/
