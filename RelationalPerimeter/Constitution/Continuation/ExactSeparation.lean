import RelationalPerimeter.Constitution.Continuation.Minimality

/-! Exact realizations must preserve every distinction already exhibited by
the independently fixed future contract.  The separator is positive finite
data; no specialized diagonal content is imported by this generic layer. -/
set_option genInjectivity false
namespace ConstitutiveSearch.ContinuationSignatures
universe u v
variable {S M I : Type u} {E O : Type v}
  {contract : FutureContract S I E O}

theorem ExactRealization.distinct_memory_of_not_future_equivalent
    (realization : ExactRealization contract M)
    {left right : S}
    (different : ¬ FutureEquivalent contract left right) :
    realization.project left ≠ realization.project right := by
  intro same
  exact different (realization.equal_memory_same_futures same)

theorem ExactRealization.distinct_memory_of_separator
    (realization : ExactRealization contract M)
    {left right : S}
    (separator : FutureSeparator contract left right) :
    realization.project left ≠ realization.project right :=
  realization.distinct_memory_of_not_future_equivalent separator.not_equivalent

end ConstitutiveSearch.ContinuationSignatures
/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.ContinuationSignatures.ExactRealization.distinct_memory_of_not_future_equivalent
#print axioms ConstitutiveSearch.ContinuationSignatures.ExactRealization.distinct_memory_of_separator
/- AXIOM_AUDIT_END -/
