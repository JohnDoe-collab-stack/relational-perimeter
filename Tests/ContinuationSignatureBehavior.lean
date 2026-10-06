import RelationalPerimeter.Constitution.Continuation.Composition

/-! Independent contract checks: nonempty final read, distinct rights, and
unbounded finite transition sequences. These are core fixtures, not a second
scientific instance of relational role constitution. -/
set_option genInjectivity false
namespace Tests.ContinuationSignatureBehavior
open ConstitutiveSearch.ContinuationSignatures

def rightsContract : FutureContract Bool Unit Unit Unit where
  next source _ := source
  event _ _ := ()
  read _ := ()
  Allow source _ := if source then Unit else Empty
  decision source _ := match source with
    | true => .inl ()
    | false => .inr (fun impossible => nomatch impossible)

theorem disjoint_rights_not_equivalent : ¬ FutureEquivalent rightsContract false true := by
  intro same
  have rights := same.enabled ()
  cases rights

def toggleContract : FutureContract Bool Bool Unit Bool where
  next source input := if input then !source else source
  event _ _ := ()
  read source := source
  Allow _ _ := Unit
  decision _ _ := .inl ()

def toggleBasis : FiniteFutureBasis toggleContract where
  tests := [[]]
  complete left right agree := by
    have same : left = right := congrArg Outcome.read (agree [] (.head _))
    cases same
    exact FutureEquivalent.refl _ _

def toggleDynamics : SignatureDynamics toggleBasis where
  update signature input := match signature with
    | [] => []
    | first :: rest => match first with
      | .stop value => .stop (if input then !value else value) :: rest
      | .step value right event tail => .step value right event tail :: rest
  update_exact _ _ := rfl

theorem empty_sequence_observes : ¬ FutureEquivalent toggleContract false true := by
  intro same
  cases same.read

theorem all_lengths_covered (source : Bool) (requests : List Bool) :
    toggleDynamics.run (producedSignature toggleBasis source) requests =
      producedSignature toggleBasis (ConstitutiveSearch.Grouping.Continuation.run
        toggleContract.next source requests) := toggleDynamics.run_exact source requests

def positive_separator : FutureSeparator toggleContract false true :=
  separate toggleBasis false true (fun same => empty_sequence_observes (signature_sound toggleBasis same))

theorem separator_is_initial_read : positive_separator.requests = [] := rfl

end Tests.ContinuationSignatureBehavior
/- AXIOM_AUDIT_BEGIN -/
#print axioms Tests.ContinuationSignatureBehavior.disjoint_rights_not_equivalent
#print axioms Tests.ContinuationSignatureBehavior.empty_sequence_observes
#print axioms Tests.ContinuationSignatureBehavior.all_lengths_covered
#print axioms Tests.ContinuationSignatureBehavior.positive_separator
#print axioms Tests.ContinuationSignatureBehavior.separator_is_initial_read
/- AXIOM_AUDIT_END -/
