import RelationalPerimeter.Computation.ConstitutiveSearch.AcceptedRelationalTransport

/-!
# Automatic normalization of viable frontiers

This is the hardened counterpart of finite frontier normalization.  Executable
relation search may absorb states only through total transports that preserve
acceptance.  Every reduction step carries both directions needed to preserve
frontier viability.

As before, an unresolved search means only that the current engine found no
relation witness.
-/

namespace ConstitutiveSearch

universe uRelation uState uContinuation

namespace AcceptingFrontierTransport

/-- Swap the first two frontier states without changing continuation payloads. -/
def swapFirstTwo
    {system : SearchSystem}
    {first second : system.State}
    {rest : List system.State} :
    AcceptingFrontierTransport
      system
      (first :: second :: rest)
      (second :: first :: rest) :=
  { map := fun frontier =>
      match frontier with
      | .head firstContinuation =>
          .tail (.head firstContinuation)
      | .tail (.head secondContinuation) =>
          .head secondContinuation
      | .tail (.tail restContinuation) =>
          .tail (.tail restContinuation)
    preservesAccept := by
      intro frontier accepted
      cases frontier with
      | head firstContinuation =>
          exact accepted
      | tail tailContinuation =>
          cases tailContinuation with
          | head secondContinuation =>
              exact accepted
          | tail restContinuation =>
              exact accepted }

/-- Lift an acceptance-preserving frontier transport under one fixed head. -/
def prepend
    {system : SearchSystem}
    {head : system.State}
    {source target : List system.State}
    (transport : AcceptingFrontierTransport system source target) :
    AcceptingFrontierTransport
      system
      (head :: source)
      (head :: target) :=
  { map := fun frontier =>
      match frontier with
      | .head headContinuation =>
          .head headContinuation
      | .tail tailContinuation =>
          .tail (transport.map tailContinuation)
    preservesAccept := by
      intro frontier accepted
      cases frontier with
      | head headContinuation =>
          exact accepted
      | tail tailContinuation =>
          exact transport.preservesAccept tailContinuation accepted }

end AcceptingFrontierTransport

namespace AcceptedFrontierPreservation

/-- Swapping two frontier heads preserves viability in both directions. -/
def swapFirstTwo
    {system : SearchSystem}
    {first second : system.State}
    {rest : List system.State} :
    AcceptedFrontierPreservation
      system
      (first :: second :: rest)
      (second :: first :: rest) :=
  { forward :=
      AcceptingFrontierTransport.swapFirstTwo
        (system := system)
        (first := first)
        (second := second)
        (rest := rest)
    backward :=
      AcceptingFrontierTransport.swapFirstTwo
        (system := system)
        (first := second)
        (second := first)
        (rest := rest) }

/-- Lift a viability preservation witness under one fixed head state. -/
def prepend
    {system : SearchSystem}
    {head : system.State}
    {source target : List system.State}
    (preservation : AcceptedFrontierPreservation system source target) :
    AcceptedFrontierPreservation
      system
      (head :: source)
      (head :: target) :=
  { forward := preservation.forward.prepend
    backward := preservation.backward.prepend }

end AcceptedFrontierPreservation

/-- Finite routing syntax produced inside the relation search. Source and target
frontiers stay indexed by their constituted states; absorption stores the actual
positive relation witness, not a supplied width or an unlicensed constant map. -/
inductive AcceptedFrontierCode {system : SearchSystem.{uState, uContinuation}}
    {Relation : system.State → system.State → Type uRelation}
    (action : AcceptedRelationalAction system Relation) :
    List system.State → List system.State → Type (max uState uRelation) where
  | identity (source : List system.State) : AcceptedFrontierCode action source source
  | swap {first second : system.State} {rest : List system.State} :
      AcceptedFrontierCode action (first :: second :: rest) (second :: first :: rest)
  | absorbFirst {first second : system.State} {rest : List system.State}
      (relation : Relation first second) :
      AcceptedFrontierCode action (first :: second :: rest) (second :: rest)
  | absorbSecond {first second : system.State} {rest : List system.State}
      (relation : Relation second first) :
      AcceptedFrontierCode action (first :: second :: rest) (first :: rest)
  | prepend {source target : List system.State} (head : system.State)
      (code : AcceptedFrontierCode action source target) :
      AcceptedFrontierCode action (head :: source) (head :: target)
  | compose {source middle target : List system.State}
      (first : AcceptedFrontierCode action source middle)
      (second : AcceptedFrontierCode action middle target) :
      AcceptedFrontierCode action source target

def AcceptedFrontierCode.eval {system : SearchSystem}
    {Relation : system.State → system.State → Type uRelation}
    {action : AcceptedRelationalAction system Relation} :
    {source target : List system.State} → AcceptedFrontierCode action source target →
      AcceptedFrontierPreservation system source target
  | _, _, .identity source => .identity system source
  | _, _, .swap => .swapFirstTwo
  | _, _, .absorbFirst relation => action.absorbFirstIntoSecond relation
  | _, _, .absorbSecond relation => action.absorbSecondIntoFirst relation
  | _, _, .prepend _ code => code.eval.prepend
  | _, _, .compose first second => first.eval.trans second.eval

/--
Result of inserting one state into an already search-irreducible frontier.

The retained frontier is viability-equivalent to the source frontier under the
hardened semantics.
-/
structure AcceptedInsertIrreducibleReduction
    {system : SearchSystem}
    {Relation : system.State → system.State → Type uRelation}
    (search : RelationSearch Relation)
    (action : AcceptedRelationalAction system Relation)
    (state : system.State)
    (rest : List system.State) where
  retained : List system.State
  code : AcceptedFrontierCode action (state :: rest) retained
  irreducible : SearchIrreducible search retained
  retainedFromSource :
    ∀ candidate : system.State,
      candidate ∈ retained →
        candidate = state ∨ candidate ∈ rest

namespace AcceptedInsertIrreducibleReduction

def preservation {system : SearchSystem}
    {Relation : system.State → system.State → Type uRelation}
    {search : RelationSearch Relation} {action : AcceptedRelationalAction system Relation}
    {state : system.State} {rest : List system.State}
    (reduction : AcceptedInsertIrreducibleReduction search action state rest) :
    AcceptedFrontierPreservation system (state :: rest) reduction.retained := reduction.code.eval

/-- Width is derived only after the certified insertion has been constructed. -/
def width
    {system : SearchSystem}
    {Relation : system.State → system.State → Type uRelation}
    {search : RelationSearch Relation}
    {action : AcceptedRelationalAction system Relation}
    {state : system.State}
    {rest : List system.State}
    (reduction :
      AcceptedInsertIrreducibleReduction search action state rest) : Nat :=
  reduction.retained.length

/-- Insertion preserves frontier viability exactly. -/
theorem viable_iff
    {system : SearchSystem}
    {Relation : system.State → system.State → Type uRelation}
    {search : RelationSearch Relation}
    {action : AcceptedRelationalAction system Relation}
    {state : system.State}
    {rest : List system.State}
    (reduction :
      AcceptedInsertIrreducibleReduction search action state rest) :
    FrontierViable system (state :: rest) ↔
      FrontierViable system reduction.retained :=
  reduction.preservation.viable_iff

end AcceptedInsertIrreducibleReduction

/--
Insert one state into an irreducible frontier using executable relation search.

Only positive relation witnesses cause absorption.  Unresolved comparisons keep
both states and continue recursively.
-/
def insertAcceptedIntoIrreducible
    {system : SearchSystem}
    {Relation : system.State → system.State → Type uRelation}
    (search : RelationSearch Relation)
    (action : AcceptedRelationalAction system Relation)
    (state : system.State) :
    (rest : List system.State) →
      SearchIrreducible search rest →
        AcceptedInsertIrreducibleReduction search action state rest
  | [], _ =>
      { retained := [state]
        code := .identity [state]
        irreducible := SearchIrreducible.singleton search state
        retainedFromSource := fun candidate member => by
          cases member with
          | head => exact Or.inl rfl
          | tail _ impossible => cases impossible }
  | current :: tail, restIrreducible =>
      let currentAgainstTail := restIrreducible.1
      let tailIrreducible := restIrreducible.2
      match classification : search.classifyPairCertified state current with
      | .bidirectional forward _backward _forwardFound _backwardFound =>
          { retained := current :: tail
            code := .absorbFirst forward
            irreducible := restIrreducible
            retainedFromSource := fun _candidate member =>
              Or.inr member }
      | .forwardOnly forward _forwardFound _backwardNotFound =>
          { retained := current :: tail
            code := .absorbFirst forward
            irreducible := restIrreducible
            retainedFromSource := fun _candidate member =>
              Or.inr member }
      | .backwardOnly backward _forwardNotFound _backwardFound =>
          let recursive :=
            insertAcceptedIntoIrreducible
              search action state tail tailIrreducible
          { retained := recursive.retained
            code := .compose (.absorbSecond backward) recursive.code
            irreducible := recursive.irreducible
            retainedFromSource := fun candidate member => by
              cases recursive.retainedFromSource candidate member with
              | inl inserted =>
                  exact Or.inl inserted
              | inr tailMember =>
                  exact Or.inr
                    (List.mem_cons_of_mem current tailMember) }
      | .unresolved forwardNotFound backwardNotFound =>
          let recursive :=
            insertAcceptedIntoIrreducible
              search action state tail tailIrreducible
          have currentAgainstRetained :
              ∀ other : system.State,
                other ∈ recursive.retained →
                  search.find current other = none ∧
                    search.find other current = none := by
            intro other member
            cases recursive.retainedFromSource other member with
            | inl inserted =>
                cases inserted
                exact ⟨backwardNotFound, forwardNotFound⟩
            | inr tailMember =>
                exact currentAgainstTail other tailMember
          { retained := current :: recursive.retained
            code := .compose .swap (.prepend current recursive.code)
            irreducible :=
              ⟨currentAgainstRetained, recursive.irreducible⟩
            retainedFromSource := fun candidate member => by
              cases member with
              | head =>
                  exact Or.inr List.mem_cons_self
              | tail _ recursiveMember =>
                  cases recursive.retainedFromSource
                      candidate recursiveMember with
                  | inl inserted =>
                      exact Or.inl inserted
                  | inr tailMember =>
                      exact Or.inr
                        (List.mem_cons_of_mem current tailMember) }

/-- Hardened finite frontier reduction to a search-relative irreducible frontier. -/
structure AcceptedIrreducibleFrontierReduction
    {system : SearchSystem}
    {Relation : system.State → system.State → Type uRelation}
    (search : RelationSearch Relation)
    (action : AcceptedRelationalAction system Relation)
    (source : List system.State) where
  retained : List system.State
  code : AcceptedFrontierCode action source retained
  irreducible : SearchIrreducible search retained

namespace AcceptedIrreducibleFrontierReduction

def preservation {system : SearchSystem}
    {Relation : system.State → system.State → Type uRelation}
    {search : RelationSearch Relation} {action : AcceptedRelationalAction system Relation}
    {source : List system.State}
    (reduction : AcceptedIrreducibleFrontierReduction search action source) :
    AcceptedFrontierPreservation system source reduction.retained := reduction.code.eval

/-- Width is derived from the retained frontier. -/
def width
    {system : SearchSystem}
    {Relation : system.State → system.State → Type uRelation}
    {search : RelationSearch Relation}
    {action : AcceptedRelationalAction system Relation}
    {source : List system.State}
    (reduction :
      AcceptedIrreducibleFrontierReduction search action source) : Nat :=
  reduction.retained.length

/-- Complete normalization preserves viability exactly. -/
theorem viable_iff
    {system : SearchSystem}
    {Relation : system.State → system.State → Type uRelation}
    {search : RelationSearch Relation}
    {action : AcceptedRelationalAction system Relation}
    {source : List system.State}
    (reduction :
      AcceptedIrreducibleFrontierReduction search action source) :
    FrontierViable system source ↔
      FrontierViable system reduction.retained :=
  reduction.preservation.viable_iff

end AcceptedIrreducibleFrontierReduction

/--
Normalize any finite frontier by executable relation search while preserving
viability in both directions.
-/
def normalizeAcceptedFrontier
    {system : SearchSystem}
    {Relation : system.State → system.State → Type uRelation}
    (search : RelationSearch Relation)
    (action : AcceptedRelationalAction system Relation) :
    (source : List system.State) →
      AcceptedIrreducibleFrontierReduction search action source
  | [] =>
      { retained := []
        code := .identity []
        irreducible := SearchIrreducible.nil search }
  | state :: tail =>
      let tailReduction :=
        normalizeAcceptedFrontier search action tail
      let inserted :=
        insertAcceptedIntoIrreducible
          search
          action
          state
          tailReduction.retained
          tailReduction.irreducible
      { retained := inserted.retained
        code := .compose (.prepend state tailReduction.code) inserted.code
        irreducible := inserted.irreducible }

/-- Operational width produced by this exact hardened normalization engine. -/
def normalizedAcceptedWidth
    {system : SearchSystem}
    {Relation : system.State → system.State → Type uRelation}
    (search : RelationSearch Relation)
    (action : AcceptedRelationalAction system Relation)
    (source : List system.State) : Nat :=
  (normalizeAcceptedFrontier search action source).width

end ConstitutiveSearch

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.AcceptedFrontierCode
#print axioms ConstitutiveSearch.AcceptedFrontierCode.eval
#print axioms ConstitutiveSearch.AcceptedInsertIrreducibleReduction.preservation
#print axioms ConstitutiveSearch.AcceptedIrreducibleFrontierReduction.preservation
#print axioms ConstitutiveSearch.AcceptingFrontierTransport.swapFirstTwo
#print axioms ConstitutiveSearch.AcceptingFrontierTransport.prepend
#print axioms ConstitutiveSearch.AcceptedFrontierPreservation.swapFirstTwo
#print axioms ConstitutiveSearch.AcceptedFrontierPreservation.prepend
#print axioms ConstitutiveSearch.AcceptedInsertIrreducibleReduction
#print axioms ConstitutiveSearch.AcceptedInsertIrreducibleReduction.viable_iff
#print axioms ConstitutiveSearch.insertAcceptedIntoIrreducible
#print axioms ConstitutiveSearch.AcceptedIrreducibleFrontierReduction
#print axioms ConstitutiveSearch.AcceptedIrreducibleFrontierReduction.viable_iff
#print axioms ConstitutiveSearch.normalizeAcceptedFrontier
#print axioms ConstitutiveSearch.normalizedAcceptedWidth
/- AXIOM_AUDIT_END -/
