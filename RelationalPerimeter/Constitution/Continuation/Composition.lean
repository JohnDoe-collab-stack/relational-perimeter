import RelationalPerimeter.Constitution.Continuation.Minimality

/-! A reduced transition is constructed, not chosen from a fibre representative.
The generic contract below covers arbitrary finite read-only interactions. -/
set_option genInjectivity false
namespace ConstitutiveSearch.ContinuationSignatures
universe u v

def readOnlyContract {S : Type u} {O : Type v} (read : S → O) :
    FutureContract S (ULift.{u} Unit) (ULift.{v} Unit) O where
  next source _ := source
  event _ _ := ⟨()⟩
  read := read
  Allow _ _ := ULift.{u} Unit
  decision _ _ := .inl ⟨()⟩

theorem readOnly_futures {S : Type u} {O : Type v} (read : S → O) {left right : S}
    (same : read left = read right) : FutureEquivalent (readOnlyContract read) left right := by
  intro requests
  induction requests with
  | nil => exact congrArg Outcome.stop same
  | cons _ _ ih =>
      change Outcome.step (read left) true (ULift.up () : ULift.{v} Unit) _ =
        Outcome.step (read right) true (ULift.up () : ULift.{v} Unit) _
      rw [same]
      exact congrArg (Outcome.step _ true ⟨()⟩) ih

def readOnlyBasis {S : Type u} {O : Type v} (read : S → O) :
    FiniteFutureBasis (readOnlyContract read) where
  tests := [[]]
  complete _left _right agree :=
    readOnly_futures read (congrArg Outcome.read (agree [] (.head _)))

def readOnlyRealization {S : Type u} {O : Type u} (read : S → O) :
    ExactRealization (readOnlyContract read) O where
  reduced := readOnlyContract (fun value => value)
  project := read
  forward _ _ witness := witness
  backward _ _ witness := witness
  backward_forward _ _ _ := rfl
  forward_backward _ _ _ := rfl
  next_exact _ _ := rfl
  event_exact _ _ := rfl
  read_exact _ := rfl

/-- Generic executable operations on signatures require positive local algorithms. -/
structure SignatureDynamics {S I : Type u} {E O : Type v}
    {contract : FutureContract S I E O} (basis : FiniteFutureBasis contract) where
  update : List (Outcome E O) → I → List (Outcome E O)
  update_exact : ∀ source input,
    update (producedSignature basis source) input = producedSignature basis (contract.next source input)

def SignatureDynamics.run {S I : Type u} {E O : Type v}
    {contract : FutureContract S I E O} {basis : FiniteFutureBasis contract}
    (dynamics : SignatureDynamics basis) : List (Outcome E O) → List I → List (Outcome E O)
  | signature, [] => signature
  | signature, input :: rest => dynamics.run (dynamics.update signature input) rest

theorem SignatureDynamics.run_exact {S I : Type u} {E O : Type v}
    {contract : FutureContract S I E O} {basis : FiniteFutureBasis contract}
    (dynamics : SignatureDynamics basis) (source : S) (requests : List I) :
    dynamics.run (producedSignature basis source) requests =
      producedSignature basis (Grouping.Continuation.run contract.next source requests) := by
  induction requests generalizing source with
  | nil => rfl
  | cons input rest ih =>
      change dynamics.run (dynamics.update (producedSignature basis source) input) rest = _
      rw [dynamics.update_exact]
      exact ih _

end ConstitutiveSearch.ContinuationSignatures
/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.ContinuationSignatures.readOnlyContract
#print axioms ConstitutiveSearch.ContinuationSignatures.readOnlyBasis
#print axioms ConstitutiveSearch.ContinuationSignatures.readOnlyRealization
#print axioms ConstitutiveSearch.ContinuationSignatures.SignatureDynamics.run
#print axioms ConstitutiveSearch.ContinuationSignatures.SignatureDynamics.run_exact
/- AXIOM_AUDIT_END -/
