import Tests.LocalAlignment.DocumentaryControlMasterData
import Tests.LocalAlignment.DocumentaryControlReference

/-! Actual restored binding reads and closed justification readers. A reader
for an arbitrary received knowledge function is an explicit interface; the
empty, quotation and derived constructors close it constructively. -/
set_option genInjectivity false
set_option maxHeartbeats 4000000
namespace ConstitutiveSearch.Agent.Local.Documentary.ControlDeferred
open Resources Program Snapshot Control ControlBindings ControlMasterData
variable {context : List SourceKey} {sources : Support SourceValue context}
  {contract : Contract} {rules : Deduction.Policy} {slots : List Specification}

def restoreCode (before : FrameData sources contract rules slots) : Code Label (Actual before.restore) :=
  .step .frameRestore (fun _ => .done ⟨⟨before.dossier, before.store, before.bindings.read⟩, rfl⟩)

theorem restore_bounded (before : FrameData sources contract rules slots) :
    Within (restoreCode before) 1 := within_step _ _ (within_done _)

def bindingCode (before : FrameData sources contract rules slots) {spec : Specification}
    (slot : Ref slots spec) : Code Label (Actual (before.restore.bindings slot)) :=
  (ControlBindings.readCode before.bindings slot).bind (fun loaded => .done ⟨loaded.1, loaded.2.symm⟩)

theorem binding_bounded (before : FrameData sources contract rules slots) {spec : Specification}
    (slot : Ref slots spec) : Within (bindingCode before slot) (slot.position + 1) := by
  apply within_weaken
  · apply within_bind (more := 0)
      (show Within (ControlBindings.readCode before.bindings slot) (slot.position + 1) from
        ⟨_, _, ⟨ControlBindings.readTrace before.bindings slot⟩,
          by rw [ControlBindings.replicate_length]; exact Nat.le_refl _⟩)
    intro loaded
    exact within_done _
  · exact Nat.le_of_eq (Nat.add_zero _)

abbrev EvidenceReader {kinds : List Deduction.Kind}
    (knowledge : Deduction.Knowledge sources contract rules kinds) :=
  {kind : Deduction.Kind} → (ref : Ref kinds kind) → Code Label (Actual (knowledge.valid ref))

abbrev ReaderFinite {kinds : List Deduction.Kind}
    {knowledge : Deduction.Knowledge sources contract rules kinds} (reader : EvidenceReader knowledge) :=
  ∀ {kind} (ref : Ref kinds kind), Finite (reader ref)

def emptyReader : EvidenceReader (Deduction.empty sources contract rules) := fun ref => nomatch ref

theorem empty_finite : ReaderFinite (emptyReader (sources := sources) (contract := contract) (rules := rules)) :=
  fun ref => nomatch ref

def quotationReader {kinds : List Deduction.Kind}
    (knowledge : Deduction.Knowledge sources contract rules kinds) (reader : EvidenceReader knowledge)
    (output : Output sources contract) : EvidenceReader (Deduction.quote knowledge output) :=
  fun ref => .step .justificationCell (fun _ => match ref with
    | .here => .step .justificationReturn (fun _ => .done ⟨.quotation output.item output.evidence, rfl⟩)
    | .prior old => (reader old).bind (fun actual => .done ⟨actual.1, actual.2⟩))

theorem quotation_finite {kinds : List Deduction.Kind}
    (knowledge : Deduction.Knowledge sources contract rules kinds) (reader : EvidenceReader knowledge)
    (readerFinite : ReaderFinite reader) (output : Output sources contract) :
    ReaderFinite (quotationReader knowledge reader output) := by
  intro kind ref
  apply finite_step
  cases ref with
  | here => exact finite_step _ _ (finite_done _)
  | prior old =>
    apply finite_bind (readerFinite old)
    intro actual
    exact finite_done _

def derivedReader {kinds : List Deduction.Kind} {left right : Deduction.Kind}
    (knowledge : Deduction.Knowledge sources contract rules kinds) (reader : EvidenceReader knowledge)
    (request : Deduction.Request rules) (leftRef : Ref kinds left) (rightRef : Ref kinds right)
    (action : Deduction.FormationAction knowledge request leftRef rightRef)
    (permission : Ref rules.allowed request.2.position) : EvidenceReader (Deduction.incorporateDerived action permission) :=
  fun ref => .step .justificationCell (fun _ => match ref with
    | .here => (reader leftRef).bind (fun leftEvidence =>
      (reader rightRef).bind (fun rightEvidence =>
      (ControlReference.positionCode leftRef).bind (fun leftPosition =>
      (ControlReference.positionCode rightRef).bind (fun rightPosition =>
      .step .justificationReturn (fun _ =>
        have kindActual : Deduction.Kind.derived request.1 request.2.position
            left leftPosition.1 right rightPosition.1 = Deduction.derivedKind request leftRef rightRef := by
          rw [leftPosition.2, rightPosition.2]; rfl
        let tree := Deduction.Justified.derived request permission leftPosition.1 rightPosition.1
          leftEvidence.1 rightEvidence.1
        let reindexed := kindActual ▸ tree
        .done ⟨action.value.symm ▸ reindexed, by
          obtain ⟨_, actual⟩ := rightPosition; cases actual
          obtain ⟨_, actual⟩ := leftPosition; cases actual
          obtain ⟨_, actual⟩ := rightEvidence; cases actual
          obtain ⟨_, actual⟩ := leftEvidence; cases actual; rfl⟩)))))
    | .prior old => (reader old).bind (fun evidence => .done
      ⟨(action.old_value old).symm ▸ evidence.1, by obtain ⟨_, actual⟩ := evidence; cases actual; rfl⟩))

theorem derived_finite {kinds : List Deduction.Kind} {left right : Deduction.Kind}
    (knowledge : Deduction.Knowledge sources contract rules kinds) (reader : EvidenceReader knowledge)
    (readerFinite : ReaderFinite reader)
    (request : Deduction.Request rules) (leftRef : Ref kinds left) (rightRef : Ref kinds right)
    (action : Deduction.FormationAction knowledge request leftRef rightRef)
    (permission : Ref rules.allowed request.2.position) :
    ReaderFinite (derivedReader knowledge reader request leftRef rightRef action permission) := by
  intro kind ref; apply finite_step
  cases ref with
  | here =>
    apply finite_bind (readerFinite leftRef); intro leftEvidence
    apply finite_bind (readerFinite rightRef); intro rightEvidence
    apply finite_bind
    · obtain ⟨value, labels, trace, _⟩ := ControlReference.position_bounded leftRef
      exact ⟨value, labels, trace⟩
    · intro leftPosition
      apply finite_bind
      · obtain ⟨value, labels, trace, _⟩ := ControlReference.position_bounded rightRef
        exact ⟨value, labels, trace⟩
      · intro rightPosition; exact finite_step _ _ (finite_done _)
  | prior old => apply finite_bind (readerFinite old); intro evidence; exact finite_done _

/-- This class closes the received reader interface by the actual documentary
constructors, including the retained rule permission and formation action. -/
inductive KnowledgeRecipe : {kinds : List Deduction.Kind} →
    Deduction.Knowledge sources contract rules kinds → Type 3 where
  | empty : KnowledgeRecipe (Deduction.empty sources contract rules)
  | quotation {kinds : List Deduction.Kind} {knowledge : Deduction.Knowledge sources contract rules kinds}
      (prior : KnowledgeRecipe knowledge) (output : Output sources contract) :
      KnowledgeRecipe (Deduction.quote knowledge output)
  | derived {kinds : List Deduction.Kind} {knowledge : Deduction.Knowledge sources contract rules kinds}
      {left right : Deduction.Kind} (prior : KnowledgeRecipe knowledge)
      (request : Deduction.Request rules) (leftRef : Ref kinds left) (rightRef : Ref kinds right)
      (action : Deduction.FormationAction knowledge request leftRef rightRef)
      (permission : Ref rules.allowed request.2.position) : KnowledgeRecipe (Deduction.incorporateDerived action permission)

def recipeReader {kinds : List Deduction.Kind} {knowledge : Deduction.Knowledge sources contract rules kinds}
    (recipe : KnowledgeRecipe knowledge) : EvidenceReader knowledge := fun ref =>
  .step .controlInspect (fun _ => match kinds, knowledge, recipe with
    | _, _, .empty => nomatch ref
    | _, _, .quotation prior output => quotationReader _ (recipeReader prior) output ref
    | _, _, .derived prior request left right action permission =>
      derivedReader _ (recipeReader prior) request left right action permission ref)
termination_by structural recipe

theorem recipe_finite {kinds : List Deduction.Kind} {knowledge : Deduction.Knowledge sources contract rules kinds}
    (recipe : KnowledgeRecipe knowledge) : ReaderFinite (recipeReader recipe) := by
  induction recipe with
  | empty => intro kind ref; nomatch ref
  | quotation prior output previous =>
    intro kind ref; apply finite_step
    exact quotation_finite _ _ previous output ref
  | derived prior request left right action permission previous =>
    intro kind ref; apply finite_step
    exact derived_finite _ _ previous request left right action permission ref

universe u v

/-- A finite representation of the three constructed extension operations.
Arbitrary received extension functions require their own representation. -/
inductive ExtensionRecipe {Kind : Type u} {Value : Kind → Type v} :
    {oldKinds newKinds : List Kind} → {old : Support Value oldKinds} → {new : Support Value newKinds} →
      Support.Extension old new → Type (max u v) where
  | identity {kinds : List Kind} (support : Support Value kinds) : ExtensionRecipe (Support.Extension.identity support)
  | produced {kinds : List Kind} (support : Support Value kinds) (producer : Producer Value kinds) :
      ExtensionRecipe (Support.Extension.produced support producer)
  | compose {firstKinds middleKinds lastKinds : List Kind}
      {first : Support Value firstKinds} {middle : Support Value middleKinds} {last : Support Value lastKinds}
      {one : Support.Extension first middle} {two : Support.Extension middle last}
      (firstRecipe : ExtensionRecipe one) (secondRecipe : ExtensionRecipe two) : ExtensionRecipe (one.compose two)

def referenceCode {Kind : Type u} {Value : Kind → Type v} {oldKinds newKinds : List Kind}
    {old : Support Value oldKinds} {new : Support Value newKinds} {extension : Support.Extension old new}
    (recipe : ExtensionRecipe extension) {kind : Kind} (ref : Ref oldKinds kind) :
    Code Label (Actual (extension.references ref)) :=
  .step .controlInspect (fun _ => match recipe with
  | .identity _ => .step .referenceIdentity (fun _ => .done ⟨ref, rfl⟩)
  | .produced _ _ => .step .referenceShift (fun _ => .done ⟨.prior ref, rfl⟩)
  | .compose one two => .step .referenceComposition (fun _ =>
    (referenceCode one ref).bind (fun first =>
    (referenceCode two first.1).bind (fun second => .done
      ⟨second.1, by obtain ⟨_, actual⟩ := second; cases actual
                    obtain ⟨_, actual⟩ := first; cases actual; rfl⟩))))

theorem reference_finite {Kind : Type u} {Value : Kind → Type v} {oldKinds newKinds : List Kind}
    {old : Support Value oldKinds} {new : Support Value newKinds} {extension : Support.Extension old new}
    (recipe : ExtensionRecipe extension) {kind : Kind} (ref : Ref oldKinds kind) : Finite (referenceCode recipe ref) := by
  induction recipe with
  | identity _ => exact finite_step _ _ (finite_step _ _ (finite_done _))
  | produced _ _ => exact finite_step _ _ (finite_step _ _ (finite_done _))
  | compose one two firstFinite secondFinite =>
    apply finite_step; apply finite_step; apply finite_bind (firstFinite ref); intro first
    apply finite_bind (secondFinite first.1); intro second; exact finite_done _

end ConstitutiveSearch.Agent.Local.Documentary.ControlDeferred

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlDeferred.restoreCode
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlDeferred.restore_bounded
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlDeferred.bindingCode
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlDeferred.binding_bounded
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlDeferred.EvidenceReader
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlDeferred.ReaderFinite
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlDeferred.emptyReader
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlDeferred.empty_finite
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlDeferred.quotationReader
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlDeferred.quotation_finite
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlDeferred.derivedReader
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlDeferred.derived_finite
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlDeferred.KnowledgeRecipe
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlDeferred.recipeReader
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlDeferred.recipe_finite
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlDeferred.ExtensionRecipe
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlDeferred.referenceCode
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlDeferred.reference_finite
/- AXIOM_AUDIT_END -/
