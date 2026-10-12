import Tests.LocalAlignment.DocumentaryControlDeferred

/-! Positive realizations of the actual binding function. The finite table and
constructed assemblies close the interface. Capture consumes these paid queries,
including the actual reference transports, and preserves the whole original table. -/
set_option genInjectivity false
set_option backward.match.sparseCases false
set_option maxHeartbeats 4000000
namespace ConstitutiveSearch.Agent.Local.Documentary.ControlBindingReader
open Resources Program Snapshot Control ControlBindings ControlMasterData ControlDeferred
variable {context : List SourceKey} {sources : Support SourceValue context}
  {contract : Contract} {rules : Deduction.Policy}

universe u v
structure ReferenceReader {Kind : Type u} {Value : Kind → Type v} {oldKinds newKinds : List Kind}
    {old : Support Value oldKinds} {new : Support Value newKinds} (extension : Support.Extension old new) where
  readCode : {kind : Kind} → (ref : Ref oldKinds kind) → Code Label (Actual (extension.references ref))
  finite : ∀ {kind} (ref : Ref oldKinds kind), Finite (readCode ref)

@[inline] def identityReferenceReader {Kind : Type u} {Value : Kind → Type v} {kinds : List Kind}
    (support : Support Value kinds) : ReferenceReader (Support.Extension.identity support) :=
  ⟨fun ref => .step .referenceIdentity (fun _ => .done ⟨ref, rfl⟩),
    fun _ => finite_step _ _ (finite_done _)⟩

@[inline] def shiftedReferenceReader {Kind : Type u} {Value : Kind → Type v} {kinds : List Kind}
    {fresh : Kind} {old : Support Value kinds} {new : Support Value (fresh :: kinds)}
    (extension : Support.Extension old new)
    (actual : ∀ {kind} (ref : Ref kinds kind), extension.references ref = Ref.prior ref) :
    ReferenceReader extension :=
  ⟨fun ref => .step .referenceShift (fun _ => .done ⟨.prior ref, (actual ref).symm⟩),
    fun _ => finite_step _ _ (finite_done _)⟩

@[inline] def shiftedAlignedReferenceReader {Kind : Type u} {Value : Kind → Type v}
    {kinds newKinds : List Kind} {old : Support Value kinds} {new : Support Value newKinds}
    (fresh : Kind) (sameKinds : newKinds = fresh :: kinds) (extension : Support.Extension old new)
    (actual : ∀ {kind} (ref : Ref kinds kind), extension.references ref =
      (sameKinds.symm ▸ Ref.prior (added := fresh) ref)) : ReferenceReader extension :=
  ⟨fun ref => .step .referenceShift (fun _ => .done
      ⟨sameKinds.symm ▸ Ref.prior (added := fresh) ref, (actual ref).symm⟩),
    fun _ => finite_step _ _ (finite_done _)⟩

@[inline] def recipeReferenceReader {Kind : Type u} {Value : Kind → Type v} {oldKinds newKinds : List Kind}
    {old : Support Value oldKinds} {new : Support Value newKinds} {extension : Support.Extension old new}
    (recipe : ExtensionRecipe extension) : ReferenceReader extension :=
  ⟨fun ref => referenceCode recipe ref, fun ref => reference_finite recipe ref⟩

structure Reader {store : Deduction.Store sources contract rules} {slots : List Specification}
    (bindings : {spec : Specification} → Ref slots spec → Option (Occurrence store)) where
  readCode : {spec : Specification} → (slot : Ref slots spec) → Code Label (Actual (bindings slot))
  finite : ∀ {spec} (slot : Ref slots spec), Finite (readCode slot)

@[inline] def tableCode {store : Deduction.Store sources contract rules} {slots : List Specification}
    (table : Bindings store slots) {spec : Specification} (slot : Ref slots spec) :
    Code Label (Actual (table.read slot)) :=
  (ControlBindings.readCode table slot).bind (fun actual => .done ⟨actual.1, actual.2.symm⟩)

theorem table_finite {store : Deduction.Store sources contract rules} {slots : List Specification}
    (table : Bindings store slots) {spec : Specification} (slot : Ref slots spec) :
    Finite (tableCode table slot) := by
  apply finite_bind ⟨_, _, ⟨ControlBindings.readTrace table slot⟩⟩
  intro actual; exact finite_done _

@[inline] def tableReader {store : Deduction.Store sources contract rules} {slots : List Specification}
    (table : Bindings store slots) : Reader table.read :=
  ⟨fun slot => tableCode table slot, fun slot => table_finite table slot⟩

@[inline] def tailCode {store : Deduction.Store sources contract rules} {head : Specification}
    {rest : List Specification} {bindings : {spec : Specification} → Ref (head :: rest) spec → Option (Occurrence store)}
    (reader : Reader bindings) {spec : Specification} (slot : Ref rest spec) :
    Code Label (Actual (bindings (.prior slot))) :=
  .step .referenceShift (fun _ => reader.readCode (.prior slot))

theorem tail_finite {store : Deduction.Store sources contract rules} {head : Specification}
    {rest : List Specification} {bindings : {spec : Specification} → Ref (head :: rest) spec → Option (Occurrence store)}
    (reader : Reader bindings) {spec : Specification} (slot : Ref rest spec) :
    Finite (tailCode reader slot) := finite_step _ _ (reader.finite (.prior slot))

@[inline] def tailReader {store : Deduction.Store sources contract rules} {head : Specification}
    {rest : List Specification} {bindings : {spec : Specification} → Ref (head :: rest) spec → Option (Occurrence store)}
    (reader : Reader bindings) : Reader (fun slot => bindings (.prior slot)) :=
  ⟨fun slot => tailCode reader slot, fun slot => tail_finite reader slot⟩

@[inline] def assembledCode {slots : List Specification} {fresh : Specification}
    (before : Frame sources contract rules slots) (prior : Reader before.bindings)
    (dossier : Dossier.State sources contract) (after : Deduction.Store sources contract rules)
    (extension : Support.Extension before.store.2.resources after.2.resources)
    (referenceReader : ReferenceReader extension) (output : Option (Occurrence after))
    {spec : Specification} (slot : Ref (fresh :: slots) spec) :
    Code Label (Actual ((assemble before dossier after extension output).bindings slot)) :=
  .step .binding (fun _ => match slot with
    | .here => .done ⟨output, rfl⟩
    | .prior old => (prior.readCode old).bind (fun loaded => match found : loaded.1 with
        | none => .done ⟨none, by
            obtain ⟨value, actual⟩ := loaded; cases actual
            dsimp only at found
            change none = (before.bindings old).map _
            rw [found]; rfl⟩
        | some occurrence => (referenceReader.readCode occurrence.2).bind (fun moved =>
            .step .formationValues (fun _ =>
              let realized : Occurrence after := ⟨occurrence.1, moved.1⟩
              .step .formationValues (fun _ => .done ⟨some realized, by
                obtain ⟨_, actual⟩ := moved; cases actual
                obtain ⟨value, actual⟩ := loaded; cases actual
                dsimp only at found
                change some _ = (before.bindings old).map _
                rw [found]; rfl⟩)))))

theorem assembled_finite {slots : List Specification} {fresh : Specification}
    (before : Frame sources contract rules slots) (prior : Reader before.bindings)
    (dossier : Dossier.State sources contract) (after : Deduction.Store sources contract rules)
    (extension : Support.Extension before.store.2.resources after.2.resources)
    (referenceReader : ReferenceReader extension) (output : Option (Occurrence after))
    {spec : Specification} (slot : Ref (fresh :: slots) spec) :
    Finite (assembledCode before prior dossier after extension referenceReader output slot) := by
  apply finite_step
  cases slot with
  | here => exact finite_done _
  | prior old =>
      apply finite_bind (prior.finite old); intro loaded
      split
      · exact finite_done _
      · apply finite_bind (referenceReader.finite _); intro moved
        apply finite_step; apply finite_step; exact finite_done _

@[inline] def assembledReader {slots : List Specification} {fresh : Specification}
    (before : Frame sources contract rules slots) (prior : Reader before.bindings)
    (dossier : Dossier.State sources contract) (after : Deduction.Store sources contract rules)
    (extension : Support.Extension before.store.2.resources after.2.resources)
    (referenceReader : ReferenceReader extension) (output : Option (Occurrence after)) :
    Reader (assemble (spec := fresh) before dossier after extension output).bindings :=
  ⟨fun slot => assembledCode before prior dossier after extension referenceReader output slot,
    fun slot => assembled_finite before prior dossier after extension referenceReader output slot⟩

def captureCode {store : Deduction.Store sources contract rules} :
    (slots : List Specification) →
    (bindings : {spec : Specification} → Ref slots spec → Option (Occurrence store)) →
    Reader bindings → Code Label (Actual (Bindings.capture slots bindings))
  | [], _, _ => .step .controlInspect (fun _ => .step .formationValues (fun _ => .done ⟨.nil, rfl⟩))
  | _ :: rest, bindings, reader => .step .controlInspect (fun _ =>
      (reader.readCode .here).bind (fun head =>
        .step .controlClosure (fun _ =>
          (captureCode rest (fun old => bindings (.prior old)) (tailReader reader)).bind (fun tail =>
            .step .formationValues (fun _ => .done ⟨.cons head.1 tail.1, by
              obtain ⟨_, actual⟩ := tail; cases actual
              obtain ⟨_, actual⟩ := head; cases actual; rfl⟩)))))

theorem capture_finite {store : Deduction.Store sources contract rules}
    (slots : List Specification)
    (bindings : {spec : Specification} → Ref slots spec → Option (Occurrence store))
    (reader : Reader bindings) : Finite (captureCode slots bindings reader) := by
  induction slots with
  | nil => exact finite_step _ _ (finite_step _ _ (finite_done _))
  | cons head rest ih =>
      apply finite_step
      apply finite_bind (reader.finite .here); intro found
      apply finite_step
      apply finite_bind (ih _ (tailReader reader)); intro tail
      exact finite_step _ _ (finite_done _)

@[inline] def retarget {store : Deduction.Store sources contract rules} {slots : List Specification}
    {left right : {spec : Specification} → Ref slots spec → Option (Occurrence store)}
    (same : @left = @right) (reader : Reader left) : Reader right := by
  cases same; exact reader

end ConstitutiveSearch.Agent.Local.Documentary.ControlBindingReader

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlBindingReader.ReferenceReader
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlBindingReader.identityReferenceReader
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlBindingReader.shiftedReferenceReader
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlBindingReader.shiftedAlignedReferenceReader
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlBindingReader.recipeReferenceReader
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlBindingReader.Reader
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlBindingReader.tableCode
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlBindingReader.table_finite
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlBindingReader.tableReader
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlBindingReader.tailCode
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlBindingReader.tail_finite
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlBindingReader.tailReader
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlBindingReader.assembledCode
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlBindingReader.assembled_finite
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlBindingReader.assembledReader
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlBindingReader.captureCode
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlBindingReader.capture_finite
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlBindingReader.retarget
/- AXIOM_AUDIT_END -/
