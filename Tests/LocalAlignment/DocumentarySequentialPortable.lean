import Tests.LocalAlignment.DocumentaryAssignmentCodec

/-! A finite positive class whose loader constructs the complete dependent
SequentialAssignment. Bounds describe the declared class of reader recipes;
they do not test arbitrary functions or infer safety from matching bits. -/
set_option genInjectivity false
set_option maxHeartbeats 4000000
namespace ConstitutiveSearch.Agent.Local.Documentary.SequentialPortable
open SAT EndogenousDecomposition PortableAssignment

/-- Arithmetic readout of the next constituted variable, used only by the loader. -/
def limit (depth : Nat) : Nat := 2 * (depth + 4) + 2

theorem limit_exact (depth : Nat) : limit depth = stageSelectedVar (depth + 1) := by
  unfold limit stageSelectedVar growingDiscoverySplitVar
  rw [constructStage_searchIndex]
  change 2 * (depth + 4) + 2 = 2 * constitutedOperationalIndex (depth + 1) + 2
  rw [constitutedOperationalIndex_exact]

theorem limit_monotone {earlier later : Nat} (above : earlier ≤ later) :
    limit earlier ≤ limit later :=
  Nat.add_le_add_right (Nat.mul_le_mul_left 2 (Nat.add_le_add_right above 4)) 2

theorem limit_positive (depth : Nat) : 0 < limit depth :=
  Nat.lt_of_lt_of_le (Nat.zero_lt_succ 1) (Nat.le_add_left 2 (2 * (depth + 4)))

def Safe (depth : Nat) : Code → Prop
  | [] => True
  | .visit :: prior => Safe depth prior
  | .flip selected :: prior => (0 < selected ∧ selected < limit depth) ∧ Safe depth prior

instance safeDecidable (depth : Nat) : (code : Code) → Decidable (Safe depth code)
  | [] => isTrue True.intro
  | .visit :: prior => safeDecidable depth prior
  | .flip selected :: prior =>
      @instDecidableAnd _ _ (inferInstance : Decidable (0 < selected ∧ selected < limit depth))
        (safeDecidable depth prior)

theorem safe_monotone {earlier later : Nat} (above : earlier ≤ later)
    (code : Code) (safe : Safe earlier code) : Safe later code := by
  induction code with
  | nil => trivial
  | cons command prior ih =>
      cases command with
      | visit => exact ih safe
      | flip selected =>
          change (0 < selected ∧ selected < limit earlier) ∧ Safe earlier prior at safe
          exact ⟨⟨safe.1.1, Nat.lt_of_lt_of_le safe.1.2 (limit_monotone above)⟩, ih safe.2⟩

theorem safe_zero (depth : Nat) (code : Code) (safe : Safe depth code) :
    (interpret code).assignment 0 = true := by
  induction code with
  | nil => rfl
  | cons command prior ih =>
      cases command with
      | visit => exact ih safe
      | flip selected =>
          change (0 < selected ∧ selected < limit depth) ∧ Safe depth prior at safe
          change Assignment.flipAt selected (interpret prior).assignment 0 = true
          unfold Assignment.flipAt
          rw [if_neg (Nat.ne_of_lt safe.1.1)]
          exact ih safe.2

theorem safe_above (depth : Nat) (code : Code) (safe : Safe depth code)
    (query : Var) (above : limit depth ≤ query) :
    (interpret code).assignment query = alternatingAssignmentBit query := by
  induction code with
  | nil => rfl
  | cons command prior ih =>
      cases command with
      | visit => exact ih safe
      | flip selected =>
          change (0 < selected ∧ selected < limit depth) ∧ Safe depth prior at safe
          change Assignment.flipAt selected (interpret prior).assignment query = _
          unfold Assignment.flipAt
          rw [if_neg (Ne.symm (Nat.ne_of_lt (Nat.lt_of_lt_of_le safe.1.2 above)))]
          exact ih safe.2

theorem selected_bound {depth futureDepth : Nat} (above : depth + 1 ≤ futureDepth) :
    limit depth ≤ stageSelectedVar futureDepth := by
  rw [limit_exact]
  rcases Nat.lt_or_eq_of_le above with higher | same
  · exact Nat.le_of_lt (stageSelectedVar_strict higher)
  · rw [same]; exact Nat.le_refl _

/-- The dependent proofs are constructed from the validated finite recipe. -/
def assemble (depth : Nat) (code : Code) (safe : Safe depth code) : SequentialAssignment depth :=
  { assignment := (interpret code).assignment
    reader := (interpret code).reader
    zeroTrue := safe_zero depth code safe
    futureSelectedFalse := by
      intro futureDepth above
      rw [safe_above depth code safe _ (selected_bound above)]
      exact (initialSequentialAssignment depth).futureSelectedFalse futureDepth above
    futureAnchorTrue := by
      intro futureDepth above
      have bounded : limit depth ≤ stageAnchorVar futureDepth := by
        rw [stageAnchorVar_eq_selected_succ]
        exact Nat.le_trans (selected_bound above) (Nat.le_succ _)
      rw [safe_above depth code safe _ bounded]
      exact (initialSequentialAssignment depth).futureAnchorTrue futureDepth above }

theorem assembled_bundle (depth : Nat) (code : Code) (safe : Safe depth code) :
    sequential (assemble depth code safe) = interpret code := rfl

theorem sequential_injective {depth} {left right : SequentialAssignment depth}
    (same : sequential left = sequential right) : left = right := by
  cases left
  cases right
  cases same
  rfl

structure Formed {depth} (value : SequentialAssignment depth) where
  code : Code
  safe : Safe depth code
  exact : interpret code = sequential value

def initial_formed (depth : Nat) : Formed (initialSequentialAssignment depth) :=
  ⟨[], True.intro, rfl⟩

theorem assembled_exact {depth value} (formed : @Formed depth value) :
    assemble depth formed.code formed.safe = value :=
  sequential_injective (formed.exact)

theorem reflect_safe {depth root selected}
    {source target : GeneratedStructuralBranchContext root}
    (label : Var) (code : TransportCode (GeneratedStructuralFlipAtRelation selected) source target)
    (prior : Code) (positive : 0 < label) (below : label < limit depth)
    (safe : Safe depth prior) : Safe depth (reflect label code prior) := by
  induction code generalizing prior with
  | identity => exact safe
  | atom => exact ⟨⟨positive, below⟩, safe⟩
  | compose first second ihFirst ihSecond => exact ihSecond _ (ihFirst _ safe)

theorem stage_safe {depth input} (stage : SequentialStageRun depth input)
    (prior : Code) (safe : Safe depth prior) :
    Safe (depth + 1) (reflect stage.discovery.var stage.execution.code prior) := by
  have actual : stage.discovery.var = stageSelectedVar (depth + 1) :=
    (stage_variable_exact stage).trans (sequentialStage_selected_exact stage)
  apply reflect_safe _ _ prior
  · rw [actual, ← limit_exact]; exact limit_positive depth
  · rw [actual, limit_exact]; exact stageSelectedVar_strict (Nat.lt_succ_self (depth + 1))
  · exact safe_monotone (Nat.le_succ depth) prior safe

def stage_formed {depth input} (stage : SequentialStageRun depth input)
    (prior : Formed input) : Formed stage.next :=
  ⟨reflect stage.discovery.var stage.execution.code prior.code,
    stage_safe stage prior.code prior.safe,
    stage_recipe_exact stage prior.code prior.exact⟩

abbrev Raw := Nat × Code
abbrev Loaded := (depth : Nat) × SequentialAssignment depth

def envelope : ControlCodec.Codec Raw :=
  (ControlCodec.natural.product (ControlCodec.natural.product
    (ControlCodec.natural.product AssignmentCodec.codes))).via
    (fun data => (89, 1, data))
    (fun data => match data.1 with
      | 89 => match data.2.1 with | 1 => some data.2.2 | _ => none
      | _ => none)
    (fun _ => rfl)

def save (depth : Nat) (code : Code) : List UInt8 :=
  ControlCodec.bytes (envelope.words (depth, code))

def load (bytes : List UInt8) : Option Raw := do
  let words ← ControlCodec.fromBytes bytes
  let (data, tail) ← envelope.read words
  match tail with | [] => some data | _ :: _ => none

theorem byte_roundtrip (depth : Nat) (code : Code) :
    load (save depth code) = some (depth, code) := by
  unfold load save
  rw [ControlCodec.bytes_exact]
  dsimp only [Bind.bind, Option.bind]
  have actual := envelope.exact (depth, code) []
  rw [PortableCheckpoint.append_empty] at actual
  rw [actual]

def validate (data : Raw) : Option Loaded :=
  if safe : Safe data.1 data.2 then some ⟨data.1, assemble data.1 data.2 safe⟩ else none

def restore (bytes : List UInt8) : Option Loaded := (load bytes).bind validate

theorem validation_exact {depth} (code : Code) (safe : Safe depth code) :
    validate (depth, code) = some ⟨depth, assemble depth code safe⟩ := by
  unfold validate
  rw [dif_pos safe]

theorem formed_roundtrip {depth value} (formed : @Formed depth value) :
    restore (save depth formed.code) = some (⟨depth, value⟩ : Loaded) := by
  unfold restore
  rw [byte_roundtrip]
  change validate (depth, formed.code) = _
  rw [validation_exact formed.code formed.safe, assembled_exact formed]

theorem all_loaded_consumers {depth value} (formed : @Formed depth value) {Result : Type u}
    (future : Loaded → Result) :
    (restore (save depth formed.code)).map future = some (future ⟨depth, value⟩) := by
  rw [formed_roundtrip]
  rfl

/-- A dependent consumer can request a fixed depth; a different depth is rejected. -/
def restoreAt (depth : Nat) (bytes : List UInt8) : Option (SequentialAssignment depth) := do
  let ⟨found, value⟩ ← restore bytes
  if same : found = depth then some (same ▸ value) else none

theorem restore_at_exact {depth value} (formed : @Formed depth value) :
    restoreAt depth (save depth formed.code) = some value := by
  unfold restoreAt
  rw [formed_roundtrip]
  dsimp only [Bind.bind, Option.bind]
  rw [dif_pos (Eq.refl depth)]

theorem all_typed_consumers {depth value} (formed : @Formed depth value) {Result : Type u}
    (future : SequentialAssignment depth → Result) :
    (restoreAt depth (save depth formed.code)).map future = some (future value) := by
  rw [restore_at_exact]
  rfl

end ConstitutiveSearch.Agent.Local.Documentary.SequentialPortable

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Agent.Local.Documentary.SequentialPortable.limit
#print axioms ConstitutiveSearch.Agent.Local.Documentary.SequentialPortable.limit_exact
#print axioms ConstitutiveSearch.Agent.Local.Documentary.SequentialPortable.limit_monotone
#print axioms ConstitutiveSearch.Agent.Local.Documentary.SequentialPortable.limit_positive
#print axioms ConstitutiveSearch.Agent.Local.Documentary.SequentialPortable.Safe
#print axioms ConstitutiveSearch.Agent.Local.Documentary.SequentialPortable.safeDecidable
#print axioms ConstitutiveSearch.Agent.Local.Documentary.SequentialPortable.safe_monotone
#print axioms ConstitutiveSearch.Agent.Local.Documentary.SequentialPortable.safe_zero
#print axioms ConstitutiveSearch.Agent.Local.Documentary.SequentialPortable.safe_above
#print axioms ConstitutiveSearch.Agent.Local.Documentary.SequentialPortable.selected_bound
#print axioms ConstitutiveSearch.Agent.Local.Documentary.SequentialPortable.assemble
#print axioms ConstitutiveSearch.Agent.Local.Documentary.SequentialPortable.assembled_bundle
#print axioms ConstitutiveSearch.Agent.Local.Documentary.SequentialPortable.sequential_injective
#print axioms ConstitutiveSearch.Agent.Local.Documentary.SequentialPortable.Formed
#print axioms ConstitutiveSearch.Agent.Local.Documentary.SequentialPortable.initial_formed
#print axioms ConstitutiveSearch.Agent.Local.Documentary.SequentialPortable.assembled_exact
#print axioms ConstitutiveSearch.Agent.Local.Documentary.SequentialPortable.reflect_safe
#print axioms ConstitutiveSearch.Agent.Local.Documentary.SequentialPortable.stage_safe
#print axioms ConstitutiveSearch.Agent.Local.Documentary.SequentialPortable.stage_formed
#print axioms ConstitutiveSearch.Agent.Local.Documentary.SequentialPortable.Raw
#print axioms ConstitutiveSearch.Agent.Local.Documentary.SequentialPortable.Loaded
#print axioms ConstitutiveSearch.Agent.Local.Documentary.SequentialPortable.envelope
#print axioms ConstitutiveSearch.Agent.Local.Documentary.SequentialPortable.save
#print axioms ConstitutiveSearch.Agent.Local.Documentary.SequentialPortable.load
#print axioms ConstitutiveSearch.Agent.Local.Documentary.SequentialPortable.byte_roundtrip
#print axioms ConstitutiveSearch.Agent.Local.Documentary.SequentialPortable.validate
#print axioms ConstitutiveSearch.Agent.Local.Documentary.SequentialPortable.restore
#print axioms ConstitutiveSearch.Agent.Local.Documentary.SequentialPortable.validation_exact
#print axioms ConstitutiveSearch.Agent.Local.Documentary.SequentialPortable.formed_roundtrip
#print axioms ConstitutiveSearch.Agent.Local.Documentary.SequentialPortable.all_loaded_consumers
#print axioms ConstitutiveSearch.Agent.Local.Documentary.SequentialPortable.restoreAt
#print axioms ConstitutiveSearch.Agent.Local.Documentary.SequentialPortable.restore_at_exact
#print axioms ConstitutiveSearch.Agent.Local.Documentary.SequentialPortable.all_typed_consumers
/- AXIOM_AUDIT_END -/
