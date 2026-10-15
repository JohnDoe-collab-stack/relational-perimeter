import RelationalPerimeter.Instances.HeytingArithmetic.PrimitiveRecursive

/-!
# Arithmetic formula tools for constructive representability

This module contains only reusable infrastructure.  It gives finite vectors of
arithmetic terms, simultaneous graph application, blocks of existential
quantifiers, and the ordinary arithmetic formula defining one value of
Goedel's beta sequence.

The beta relation is ordinary arithmetic. Its finite-sequence witness is
constructed internally by the constructive factorial encoding in
`ConstructiveBetaEncoding`, without quotienting finite containers.
-/

namespace RelationalPerimeter
namespace HeytingArithmetic

/-! ## Total access to finite vectors -/

/-- Total access agrees with proof-indexed access inside the extent. -/
theorem NatVector.getD_eq_get
    {length index : Nat}
    (values : NatVector length)
    (bounded : index < length) :
    values.getD index = values.get index bounded := by
  induction values generalizing index with
  | nil =>
      exact (Nat.not_lt_zero index bounded).elim
  | @cons length head tail inductionHypothesis =>
      cases index with
      | zero => rfl
      | succ index =>
          exact inductionHypothesis (Nat.lt_of_succ_lt_succ bounded)

/-- Total access into a tabulation returns its generating component. -/
theorem NatVector.tabulateD_getD
    (length : Nat)
    (values : Nat -> Nat)
    (index : Nat)
    (bounded : index < length) :
    (NatVector.tabulateD length values).getD index = values index := by
  induction length generalizing values index with
  | zero => exact (Nat.not_lt_zero index bounded).elim
  | succ length inductionHypothesis =>
      cases index with
      | zero => rfl
      | succ index =>
          exact inductionHypothesis
            (fun inner => values (Nat.succ inner))
            index
            (Nat.lt_of_succ_lt_succ bounded)

/-- Tail access agrees with access at the successor position. -/
theorem NatVector.tailD_get
    {length index : Nat}
    (values : NatVector (Nat.succ length))
    (bounded : index < length) :
    values.tailD.get index bounded =
      values.get (Nat.succ index) (Nat.succ_lt_succ bounded) := by
  exact (NatVector.getD_eq_get values.tailD bounded).symm.trans
    ((NatVector.tabulateD_getD length
      (fun inner => values.getD (Nat.succ inner)) index bounded).trans
      (NatVector.getD_eq_get values (Nat.succ_lt_succ bounded)))

/-- Forget the length index while retaining all entries in order. -/
def NatVector.toList {length : Nat} (values : NatVector length) : List Nat :=
  match values with
  | NatVector.nil => []
  | NatVector.cons head tail => head :: tail.toList

/-- Forgetting the index preserves the statically known length. -/
theorem NatVector.toList_length
    {length : Nat}
    (values : NatVector length) :
    values.toList.length = length := by
  induction values with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      exact congrArg Nat.succ inductionHypothesis

/-- A length-indexed vector of raw arithmetic terms. -/
inductive RawTermVector : Nat -> Type
  | nil : RawTermVector 0
  | cons {length : Nat} :
      RawTerm -> RawTermVector length -> RawTermVector (Nat.succ length)

/-- Total access to a term vector, with arithmetic zero as the default. -/
def RawTermVector.getD
    {length : Nat}
    (terms : RawTermVector length) :
    Nat -> RawTerm
  | 0 =>
      match terms with
      | RawTermVector.nil => RawTerm.zero
      | RawTermVector.cons head _tail => head
  | Nat.succ index =>
      match terms with
      | RawTermVector.nil => RawTerm.zero
      | RawTermVector.cons _head tail => tail.getD index

/-- Pointwise scoping of a finite term vector. -/
def RawTermVector.WellScoped
    {length : Nat}
    (terms : RawTermVector length)
    (bound : Nat) : Prop :=
  match terms with
  | RawTermVector.nil => True
  | RawTermVector.cons head tail =>
      head.WellScoped bound ∧ tail.WellScoped bound

/-- Evaluation of a finite vector of terms. -/
def RawTermVector.evaluate
    {length : Nat}
    (terms : RawTermVector length)
    (environment : Environment) :
    NatVector length :=
  match terms with
  | RawTermVector.nil => NatVector.nil
  | RawTermVector.cons head tail =>
      NatVector.cons (head.evaluate environment) (tail.evaluate environment)

/-- Total access commutes with evaluation. -/
theorem RawTermVector.evaluate_getD
    {length : Nat}
    (terms : RawTermVector length)
    (environment : Environment)
    (index : Nat) :
    (terms.evaluate environment).getD index =
      (terms.getD index).evaluate environment := by
  induction terms generalizing index with
  | nil =>
      cases index <;> rfl
  | cons head tail inductionHypothesis =>
      cases index with
      | zero => rfl
      | succ index => exact inductionHypothesis index

/-- Every total vector component is scoped when the vector is scoped. -/
theorem RawTermVector.getD_wellScoped
    {length bound : Nat}
    (terms : RawTermVector length)
    (scopeProof : terms.WellScoped bound)
    (index : Nat) :
    (terms.getD index).WellScoped bound := by
  induction terms generalizing index with
  | nil =>
      cases index <;> exact trivial
  | cons head tail inductionHypothesis =>
      cases index with
      | zero => exact scopeProof.1
      | succ index => exact inductionHypothesis scopeProof.2 index

/-- Consecutive variables beginning at `start`. -/
def RawTermVector.variables :
    (start length : Nat) -> RawTermVector length
  | _start, 0 => RawTermVector.nil
  | start, Nat.succ length =>
      RawTermVector.cons
        (RawTerm.bvar start)
        (RawTermVector.variables (Nat.succ start) length)

/-- Consecutive variables are scoped below any common upper bound. -/
theorem RawTermVector.variables_wellScoped
    (start length bound : Nat)
    (bounded : start + length <= bound) :
    (RawTermVector.variables start length).WellScoped bound :=
  Nat.rec
    (motive := fun length =>
      (start : Nat) ->
      start + length <= bound ->
        (RawTermVector.variables start length).WellScoped bound)
    (fun _start _bounded => trivial)
    (fun length inductionHypothesis start bounded =>
      And.intro
        (Nat.lt_of_lt_of_le
          (Nat.lt_add_of_pos_right (Nat.succ_pos length))
          bounded)
        (inductionHypothesis
          (Nat.succ start)
          (Eq.mp
            (congrArg
              (fun lower => lower <= bound)
              ((Nat.succ_add start length).trans
                (Nat.add_succ start length).symm).symm)
            bounded)))
    length start bounded

/-! ## Environments and existential blocks -/

/-- Positive decomposition of a statically nonempty vector. -/
structure NatVector.Uncons
    {length : Nat}
    (values : NatVector (Nat.succ length)) : Type where
  head : Nat
  tail : NatVector length
  rebuild : NatVector.cons head tail = values

/-- Every statically nonempty vector has a constructor decomposition. -/
def NatVector.uncons
    {length : Nat}
    (values : NatVector (Nat.succ length)) :
    NatVector.Uncons values where
  head := values.getD 0
  tail := values.tailD
  rebuild := values.rebuildD

/-- Prefix an environment by all entries of a finite vector. -/
def prependEnvironment
    {length : Nat}
    (values : NatVector length)
    (environment : Environment)
    (index : Nat) : Nat :=
  match values, index with
  | NatVector.nil, index => environment index
  | NatVector.cons head _tail, 0 => head
  | NatVector.cons _head tail, Nat.succ inner =>
      prependEnvironment tail environment inner

/-- Prefix an environment by an ordinary list, in De Bruijn order. -/
def prependListEnvironment : List Nat -> Environment -> Environment
  | [], environment => environment
  | head :: tail, environment =>
      pushEnvironment (prependListEnvironment tail environment) head

/-- The indexed and unindexed prefix constructions agree pointwise. -/
theorem prependListEnvironment_toList
    {length : Nat}
    (values : NatVector length)
    (environment : Environment)
    (index : Nat) :
    prependListEnvironment values.toList environment index =
      prependEnvironment values environment index := by
  induction values generalizing index with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      cases index with
      | zero => rfl
      | succ index => exact inductionHypothesis index

/-- Looking inside the prefix returns the corresponding vector entry. -/
theorem prependEnvironment_get
    {length index : Nat}
    (values : NatVector length)
    (environment : Environment)
    (bounded : index < length) :
    prependEnvironment values environment index =
      values.get index bounded := by
  induction values generalizing index with
  | nil => exact (Nat.not_lt_zero index bounded).elim
  | cons head tail inductionHypothesis =>
      cases index with
      | zero => rfl
      | succ index =>
          exact inductionHypothesis (Nat.lt_of_succ_lt_succ bounded)

/-- Variables beyond the prefix are read from the original environment. -/
theorem prependEnvironment_shift
    {length : Nat}
    (values : NatVector length)
    (environment : Environment)
    (index : Nat) :
    prependEnvironment values environment (length + index) =
      environment index := by
  induction values with
  | nil => exact congrArg environment (Nat.zero_add index)
  | @cons length head tail inductionHypothesis =>
      exact Eq.mpr
        (congrArg
          (fun position =>
            prependEnvironment (NatVector.cons head tail) environment position =
              environment index)
          (Nat.succ_add length index))
        inductionHypothesis

/-- Bind `count` consecutive variables around a formula. -/
def RawFormula.existsMany : Nat -> RawFormula -> RawFormula
  | 0, body => body
  | Nat.succ count, body => (RawFormula.ex body).existsMany count

/-- One explicit unfolding equation for a nonempty existential block. -/
theorem RawFormula.existsMany_succ
    (count : Nat)
    (body : RawFormula) :
    body.existsMany (Nat.succ count) =
      (RawFormula.ex body).existsMany count :=
  rfl

/-- One direction of the definitional environment rearrangement for a prefix. -/
theorem RawFormula.prependConsHoldsForward
    (body : RawFormula)
    {length : Nat}
    (headValue : Nat)
    (tailValues : NatVector length)
    (environment : Environment) :
    body.Holds
        (pushEnvironment
          (prependEnvironment tailValues environment)
          headValue) ->
      body.Holds
        (prependEnvironment
          (NatVector.cons headValue tailValues)
          environment) :=
  (body.holds_congr
    (pushEnvironment (prependEnvironment tailValues environment) headValue)
    (prependEnvironment
      (NatVector.cons headValue tailValues) environment)
    (fun index => by cases index <;> rfl)).mp

/-- Reverse environment rearrangement for a prefixed vector. -/
theorem RawFormula.prependConsHoldsBackward
    (body : RawFormula)
    {length : Nat}
    (headValue : Nat)
    (tailValues : NatVector length)
    (environment : Environment) :
    body.Holds
        (prependEnvironment
          (NatVector.cons headValue tailValues)
          environment) ->
      body.Holds
        (pushEnvironment
          (prependEnvironment tailValues environment)
          headValue) :=
  (body.holds_congr
    (pushEnvironment (prependEnvironment tailValues environment) headValue)
    (prependEnvironment
      (NatVector.cons headValue tailValues) environment)
    (fun index => by cases index <;> rfl)).mpr

/-- Forward semantics of a block of existential binders. -/
theorem RawFormula.existsManyForward
    (count : Nat)
    (body : RawFormula)
    (environment : Environment) :
    (body.existsMany count).Holds environment ->
      Exists fun values : NatVector count =>
        body.Holds (prependEnvironment values environment) :=
  Nat.rec
    (motive := fun count =>
      (body : RawFormula) ->
      (environment : Environment) ->
      (body.existsMany count).Holds environment ->
        Exists fun values : NatVector count =>
          body.Holds (prependEnvironment values environment))
    (fun _body _environment bodyHolds =>
      Exists.intro NatVector.nil bodyHolds)
    (fun _count previous body environment blockHolds =>
      match previous (RawFormula.ex body) environment blockHolds with
          | Exists.intro tailValues existentialHolds =>
              match existentialHolds with
              | Exists.intro headValue bodyHolds =>
                  Exists.intro
                    (NatVector.cons headValue tailValues)
                    (body.prependConsHoldsForward
                      headValue tailValues environment bodyHolds))
    count body environment

/-- Backward semantics of a block of existential binders. -/
theorem RawFormula.existsManyBackwardFromList :
    (values : List Nat) ->
    (body : RawFormula) ->
    (environment : Environment) ->
    body.Holds (prependListEnvironment values environment) ->
      (body.existsMany values.length).Holds environment
  | [], _body, _environment, bodyHolds => bodyHolds
  | headValue :: tailValues, body, environment, bodyHolds =>
      RawFormula.existsManyBackwardFromList
        tailValues
        (RawFormula.ex body)
        environment
        (Exists.intro headValue bodyHolds)

/-- Backward semantics specialized to an already supplied positive vector. -/
theorem RawFormula.existsManyBackwardFromVector
    {count : Nat}
    (values : NatVector count)
    (body : RawFormula)
    (environment : Environment)
    (bodyHolds : body.Holds (prependEnvironment values environment)) :
    (body.existsMany count).Holds environment :=
  let listHolds : body.Holds
      (prependListEnvironment values.toList environment) :=
    (body.holds_congr
      (prependListEnvironment values.toList environment)
      (prependEnvironment values environment)
      (prependListEnvironment_toList values environment)).mpr bodyHolds
  let blockHolds := RawFormula.existsManyBackwardFromList
    values.toList body environment listHolds
  Eq.mp
    (congrArg
      (fun length => (body.existsMany length).Holds environment)
      (values.toList_length))
    blockHolds

/-- Backward semantics of a block of existential binders. -/
theorem RawFormula.existsManyBackward
    (count : Nat)
    (body : RawFormula)
    (environment : Environment) :
    (Exists fun values : NatVector count =>
      body.Holds (prependEnvironment values environment)) ->
        (body.existsMany count).Holds environment :=
  fun witness =>
    match witness with
    | Exists.intro values bodyHolds =>
        RawFormula.existsManyBackwardFromVector
          values body environment bodyHolds

/-- A block of existentials binds exactly its prefixed environment. -/
theorem RawFormula.existsMany_holds
    (count : Nat)
    (body : RawFormula)
    (environment : Environment) :
    (body.existsMany count).Holds environment ↔
      Exists fun values : NatVector count =>
        body.Holds (prependEnvironment values environment) :=
  Iff.intro
    (RawFormula.existsManyForward count body environment)
    (RawFormula.existsManyBackward count body environment)

/-- Existential blocks remove the corresponding number of free variables. -/
theorem RawFormula.existsMany_wellScoped
    (count bound : Nat)
    (body : RawFormula)
    (scopeProof : body.WellScoped (count + bound)) :
    (body.existsMany count).WellScoped bound := by
  induction count generalizing body bound with
  | zero =>
      exact Eq.mp
        (congrArg (fun available => body.WellScoped available)
          (Nat.zero_add bound))
        scopeProof
  | succ count inductionHypothesis =>
    apply inductionHypothesis (body := RawFormula.ex body) (bound := bound)
    change body.WellScoped (Nat.succ (count + bound))
    exact Eq.mp
      (congrArg (fun available => body.WellScoped available)
        (Nat.succ_add count bound))
      scopeProof

/-! ## Graph application by ordinary substitution -/

/-- Environment convention for a graph: output first, then all inputs. -/
def graphEnvironment
    {arity : Nat}
    (inputs : NatVector arity)
    (output : Nat) :
    Environment
  | 0 => output
  | Nat.succ index => inputs.getD index

/-- A raw graph formula paired with its exact arity scoping certificate. -/
structure ArithmeticGraph (arity : Nat) where
  raw : RawFormula
  isScoped : raw.WellScoped (Nat.succ arity)

/-- Semantic graph holding under the output-first convention. -/
def ArithmeticGraph.Holds
    {arity : Nat}
    (graph : ArithmeticGraph arity)
    (inputs : NatVector arity)
    (output : Nat) :
    Prop :=
  graph.raw.Holds (graphEnvironment inputs output)

/-- Substitute an output term and an input vector into a graph formula. -/
def ArithmeticGraph.apply
    {arity : Nat}
    (graph : ArithmeticGraph arity)
    (output : RawTerm)
    (inputs : RawTermVector arity) :
    RawFormula :=
  graph.raw.substitute fun index =>
    match index with
    | 0 => output
    | Nat.succ inputIndex => inputs.getD inputIndex

/-- Graph application has the expected pointwise semantics. -/
theorem ArithmeticGraph.apply_holds
    {arity : Nat}
    (graph : ArithmeticGraph arity)
    (output : RawTerm)
    (inputs : RawTermVector arity)
    (environment : Environment) :
    (graph.apply output inputs).Holds environment ↔
      graph.Holds
        (inputs.evaluate environment)
        (output.evaluate environment) := by
  apply Iff.trans
    (graph.raw.holds_substitute
      (fun index =>
        match index with
        | 0 => output
        | Nat.succ inputIndex => inputs.getD inputIndex)
      environment)
  apply graph.raw.holds_iff_of_scoped_agreement graph.isScoped
  intro index bounded
  cases index with
  | zero => rfl
  | succ index =>
      exact (RawTermVector.evaluate_getD inputs environment index).symm

/-- Graph application preserves any common target scope. -/
theorem ArithmeticGraph.apply_wellScoped
    {arity bound : Nat}
    (graph : ArithmeticGraph arity)
    (output : RawTerm)
    (inputs : RawTermVector arity)
    (outputScoped : output.WellScoped bound)
    (inputsScoped : inputs.WellScoped bound) :
    (graph.apply output inputs).WellScoped bound :=
  graph.raw.wellScoped_substitute
    graph.isScoped
    (fun index =>
      match index with
      | 0 => output
      | Nat.succ inputIndex => inputs.getD inputIndex)
    (by
      intro index bounded
      cases index with
      | zero => exact outputScoped
      | succ inputIndex =>
          exact inputs.getD_wellScoped inputsScoped inputIndex)

/-! ## The arithmetic beta relation -/

/-- Shift a term below one newly introduced binder. -/
def RawTerm.shift (term : RawTerm) : RawTerm :=
  term.rename Nat.succ

/-- Shifting a scoped term places it below one additional binder. -/
theorem RawTerm.shift_wellScoped
    {bound : Nat}
    (term : RawTerm)
    (scopeProof : term.WellScoped bound) :
    term.shift.WellScoped (Nat.succ bound) :=
  term.wellScoped_rename scopeProof Nat.succ
    (fun _index bounded => Nat.succ_lt_succ bounded)

/-- A shifted term ignores the freshly pushed value. -/
theorem RawTerm.shift_evaluate
    (term : RawTerm)
    (environment : Environment)
    (value : Nat) :
    term.shift.evaluate (pushEnvironment environment value) =
      term.evaluate environment := by
  unfold RawTerm.shift
  rw [RawTerm.evaluate_rename]
  exact term.evaluate_congr
    (fun index => pushEnvironment environment value (Nat.succ index))
    environment
    (fun _index => rfl)

/-- Constructive positive difference, proved without library quotient machinery. -/
theorem natExistsAddSuccEqOfLt
    {smaller larger : Nat}
    (strict : smaller < larger) :
    Exists fun gap : Nat => smaller + Nat.succ gap = larger := by
  induction smaller generalizing larger with
  | zero =>
      cases larger with
      | zero => exact (Nat.not_lt_zero 0 strict).elim
      | succ larger =>
          exact Exists.intro larger (Nat.zero_add (Nat.succ larger))
  | succ smaller inductionHypothesis =>
      cases larger with
      | zero => exact (Nat.not_lt_zero (Nat.succ smaller) strict).elim
      | succ larger =>
          have earlier : smaller < larger :=
            Nat.lt_of_succ_lt_succ strict
          cases inductionHypothesis earlier with
          | intro gap equality =>
              exact Exists.intro gap (by
                rw [Nat.succ_add]
                exact congrArg Nat.succ equality)

/-- A positive addend gives a strictly larger natural. -/
theorem natLtAddSucc (value gap : Nat) :
    value < value + Nat.succ gap := by
  induction gap with
  | zero =>
      rw [Nat.add_one]
      exact Nat.lt_succ_self value
  | succ gap inductionHypothesis =>
      rw [Nat.add_succ]
      exact Nat.lt_trans inductionHypothesis
        (Nat.lt_succ_self (value + Nat.succ gap))

/-- Ordinary arithmetic strict order, expressed using one existential gap. -/
def lessThanFormula (left right : RawTerm) : RawFormula :=
  RawFormula.ex
    (RawFormula.equal
      (RawTerm.add left.shift (RawTerm.succ (RawTerm.bvar 0)))
      right.shift)

/-- The strict-order formula preserves the common term scope. -/
theorem lessThanFormula_wellScoped
    {bound : Nat}
    (left right : RawTerm)
    (leftScoped : left.WellScoped bound)
    (rightScoped : right.WellScoped bound) :
    (lessThanFormula left right).WellScoped bound :=
  And.intro
    (And.intro
      (left.shift_wellScoped leftScoped)
      (Nat.zero_lt_succ bound))
    (right.shift_wellScoped rightScoped)

/-- The strict-order formula has its standard natural-number semantics. -/
theorem lessThanFormula_holds
    (left right : RawTerm)
    (environment : Environment) :
    (lessThanFormula left right).Holds environment ↔
      left.evaluate environment < right.evaluate environment := by
  change
    (Exists fun gap : Nat =>
      left.shift.evaluate (pushEnvironment environment gap) + Nat.succ gap =
        right.shift.evaluate (pushEnvironment environment gap)) ↔
      left.evaluate environment < right.evaluate environment
  constructor
  · intro witness
    cases witness with
    | intro gap equality =>
        have normalized :
            left.evaluate environment + Nat.succ gap =
              right.evaluate environment :=
          Eq.trans
            (congrArg
              (fun value => value + Nat.succ gap)
              (left.shift_evaluate environment gap).symm)
            (Eq.trans equality (right.shift_evaluate environment gap))
        exact Eq.mp
          (congrArg
            (fun rightValue => left.evaluate environment < rightValue)
            normalized)
          (natLtAddSucc (left.evaluate environment) gap)
  · intro strict
    cases natExistsAddSuccEqOfLt strict with
    | intro gap equality =>
        exact Exists.intro gap
          (Eq.trans
            (congrArg
              (fun value => value + Nat.succ gap)
              (left.shift_evaluate environment gap))
            (Eq.trans equality (right.shift_evaluate environment gap).symm))

/-! ## Structural Euclidean division -/

/--
Fuel-structural Euclidean division.  The first component is the quotient and
the second the remainder.  The definition recurses only on the dividend and
therefore needs no well-founded or quotient principle.
-/
def constructiveDivMod (modulus : Nat) : Nat -> Nat × Nat
  | 0 => (0, 0)
  | Nat.succ dividend =>
      let previous := constructiveDivMod modulus dividend
      if Nat.succ previous.2 < modulus then
        (previous.1, Nat.succ previous.2)
      else
        (Nat.succ previous.1, 0)

/-- Quotient computed by structural Euclidean division. -/
def constructiveQuotient (dividend modulus : Nat) : Nat :=
  (constructiveDivMod modulus dividend).1

/-- Remainder computed by structural Euclidean division. -/
def constructiveRemainder (dividend modulus : Nat) : Nat :=
  (constructiveDivMod modulus dividend).2

/-- Positive correctness data carried by structural Euclidean division. -/
structure ConstructiveDivModCorrect
    (dividend modulus : Nat) : Type where
  equation :
    dividend =
      (constructiveDivMod modulus dividend).1 * modulus +
        (constructiveDivMod modulus dividend).2
  bounded : (constructiveDivMod modulus dividend).2 < modulus

/-- One unfolding equation for the branch that grows the remainder. -/
theorem constructiveDivMod_succ_of_lt
    (dividend modulus : Nat)
    (grows : Nat.succ (constructiveDivMod modulus dividend).2 < modulus) :
    constructiveDivMod modulus (Nat.succ dividend) =
      ((constructiveDivMod modulus dividend).1,
        Nat.succ (constructiveDivMod modulus dividend).2) := by
  change
    (if Nat.succ (constructiveDivMod modulus dividend).2 < modulus then
      ((constructiveDivMod modulus dividend).1,
        Nat.succ (constructiveDivMod modulus dividend).2)
    else
      (Nat.succ (constructiveDivMod modulus dividend).1, 0)) = _
  exact if_pos grows

/-- One unfolding equation for the branch that closes a full modulus. -/
theorem constructiveDivMod_succ_of_not_lt
    (dividend modulus : Nat)
    (full : Not (Nat.succ (constructiveDivMod modulus dividend).2 < modulus)) :
    constructiveDivMod modulus (Nat.succ dividend) =
      (Nat.succ (constructiveDivMod modulus dividend).1, 0) := by
  change
    (if Nat.succ (constructiveDivMod modulus dividend).2 < modulus then
      ((constructiveDivMod modulus dividend).1,
        Nat.succ (constructiveDivMod modulus dividend).2)
    else
      (Nat.succ (constructiveDivMod modulus dividend).1, 0)) = _
  exact if_neg full

/--
The structural division algorithm builds its equation and remainder bound in
the same recursion that computes the pair.  The correctness object lives in
`Type`, so no propositional extensionality is needed to compile the recursion.
-/
def constructiveDivModCorrect
    (modulus : Nat)
    (positive : 0 < modulus) :
    (dividend : Nat) -> ConstructiveDivModCorrect dividend modulus
  | 0 =>
      { equation := by
          change 0 = 0 * modulus + 0
          exact (Eq.trans (Nat.add_zero (0 * modulus))
            (Nat.zero_mul modulus)).symm
        bounded := positive }
  | Nat.succ dividend =>
      let previous := constructiveDivModCorrect modulus positive dividend
      if grows : Nat.succ (constructiveDivMod modulus dividend).2 < modulus then
        let stepEquality :=
          constructiveDivMod_succ_of_lt dividend modulus grows
        let branchEquation :
              Nat.succ dividend =
                (constructiveDivMod modulus dividend).1 * modulus +
                  Nat.succ (constructiveDivMod modulus dividend).2 :=
          Eq.trans
            (congrArg Nat.succ previous.equation)
            (Nat.add_succ
              ((constructiveDivMod modulus dividend).1 * modulus)
              (constructiveDivMod modulus dividend).2).symm
        { equation :=
            Eq.mp
              (congrArg
                (fun result =>
                  Nat.succ dividend = result.1 * modulus + result.2)
                stepEquality.symm)
              branchEquation
          bounded :=
            Eq.mp
              (congrArg (fun result => result.2 < modulus) stepEquality.symm)
              grows }
      else
        let stepEquality :=
          constructiveDivMod_succ_of_not_lt dividend modulus grows
        let fillsModulus :
            Nat.succ (constructiveDivMod modulus dividend).2 = modulus :=
          Nat.le_antisymm
            (Nat.succ_le_of_lt previous.bounded)
            (Nat.le_of_not_gt grows)
        let branchEquation :
              Nat.succ dividend =
                Nat.succ (constructiveDivMod modulus dividend).1 * modulus + 0 :=
          Eq.trans
            (congrArg Nat.succ previous.equation)
            (Eq.trans
              (Nat.add_succ
                ((constructiveDivMod modulus dividend).1 * modulus)
                (constructiveDivMod modulus dividend).2).symm
              (Eq.trans
                (congrArg
                  (fun value =>
                    (constructiveDivMod modulus dividend).1 * modulus + value)
                  fillsModulus)
                (Eq.trans
                  (Nat.succ_mul
                    (constructiveDivMod modulus dividend).1 modulus).symm
                  (Nat.add_zero
                    (Nat.succ
                      (constructiveDivMod modulus dividend).1 * modulus)).symm)))
        { equation :=
            Eq.mp
              (congrArg
                (fun result =>
                  Nat.succ dividend = result.1 * modulus + result.2)
                stepEquality.symm)
              branchEquation
          bounded :=
            Eq.mp
              (congrArg (fun result => result.2 < modulus) stepEquality.symm)
              positive }

/-- Equation and bound certified by structural Euclidean division. -/
theorem constructiveDivMod_spec
    (dividend modulus : Nat)
    (positive : 0 < modulus) :
    dividend =
        constructiveQuotient dividend modulus * modulus +
          constructiveRemainder dividend modulus ∧
      constructiveRemainder dividend modulus < modulus :=
  let correctness := constructiveDivModCorrect modulus positive dividend
  And.intro correctness.equation correctness.bounded

/-- A bounded remainder cannot bridge one whole modulus. -/
theorem boundedSums_ne_of_quotient_lt
    {modulus leftQuotient rightQuotient leftRemainder rightRemainder : Nat}
    (quotientLt : leftQuotient < rightQuotient)
    (leftBound : leftRemainder < modulus) :
    leftQuotient * modulus + leftRemainder ≠
      rightQuotient * modulus + rightRemainder := by
  intro sameSums
  have successorBound : Nat.succ leftQuotient <= rightQuotient := quotientLt
  have strictlySmaller :
      leftQuotient * modulus + leftRemainder <
        rightQuotient * modulus + rightRemainder := calc
    leftQuotient * modulus + leftRemainder <
        leftQuotient * modulus + modulus :=
      Nat.add_lt_add_left leftBound _
    _ = Nat.succ leftQuotient * modulus :=
      (Nat.succ_mul leftQuotient modulus).symm
    _ <= rightQuotient * modulus :=
      Nat.mul_le_mul_right modulus successorBound
    _ <= rightQuotient * modulus + rightRemainder :=
      Nat.le_add_right _ _
  exact Nat.ne_of_lt strictlySmaller sameSums

/-- Left cancellation for natural addition, rebuilt by structural recursion. -/
theorem natAddLeftCancel
    (prefixValue left right : Nat)
    (equality : prefixValue + left = prefixValue + right) :
    left = right := by
  induction prefixValue with
  | zero =>
      exact Eq.trans
        (Nat.zero_add left).symm
        (Eq.trans equality (Nat.zero_add right))
  | succ prefixValue inductionHypothesis =>
      apply inductionHypothesis
      exact Nat.succ.inj
        (Eq.trans
          (Nat.succ_add prefixValue left).symm
          (Eq.trans equality (Nat.succ_add prefixValue right)))

/-- Bounded quotient/remainder decompositions have a unique remainder. -/
theorem boundedRemainder_unique
    {dividend modulus leftQuotient rightQuotient leftRemainder rightRemainder : Nat}
    (leftEquation :
      dividend = leftQuotient * modulus + leftRemainder)
    (rightEquation :
      dividend = rightQuotient * modulus + rightRemainder)
    (leftBound : leftRemainder < modulus)
    (rightBound : rightRemainder < modulus) :
    leftRemainder = rightRemainder := by
  have sameSums :
      leftQuotient * modulus + leftRemainder =
        rightQuotient * modulus + rightRemainder :=
    leftEquation.symm.trans rightEquation
  match Nat.lt_trichotomy leftQuotient rightQuotient with
  | Or.inl leftEarlier =>
      exact (boundedSums_ne_of_quotient_lt
        leftEarlier leftBound sameSums).elim
  | Or.inr (Or.inl sameQuotient) =>
      cases sameQuotient
      exact natAddLeftCancel
        (leftQuotient * modulus) leftRemainder rightRemainder sameSums
  | Or.inr (Or.inr rightEarlier) =>
      exact (boundedSums_ne_of_quotient_lt
        rightEarlier rightBound sameSums.symm).elim

/-- `remainder` is the remainder of `dividend` modulo positive `modulus`. -/
def remainderFormula
    (dividend modulus remainder : RawTerm) :
    RawFormula :=
  RawFormula.conj
    (lessThanFormula remainder modulus)
    (RawFormula.ex
      (RawFormula.equal
        dividend.shift
        (RawTerm.add
          (RawTerm.mul (RawTerm.bvar 0) modulus.shift)
          remainder.shift)))

/-- The remainder formula preserves the common scope of its terms. -/
theorem remainderFormula_wellScoped
    {bound : Nat}
    (dividend modulus remainder : RawTerm)
    (dividendScoped : dividend.WellScoped bound)
    (modulusScoped : modulus.WellScoped bound)
    (remainderScoped : remainder.WellScoped bound) :
    (remainderFormula dividend modulus remainder).WellScoped bound :=
  And.intro
    (lessThanFormula_wellScoped
      remainder modulus remainderScoped modulusScoped)
    (And.intro
      (dividend.shift_wellScoped dividendScoped)
      (And.intro
        (And.intro
          (Nat.zero_lt_succ bound)
          (modulus.shift_wellScoped modulusScoped))
        (remainder.shift_wellScoped remainderScoped)))

/-- Arithmetic remainder is characterized by a bounded quotient equation. -/
theorem remainderFormula_holds
    (dividend modulus remainder : RawTerm)
    (environment : Environment) :
    (remainderFormula dividend modulus remainder).Holds environment ↔
      remainder.evaluate environment < modulus.evaluate environment ∧
      Exists fun quotient : Nat =>
        dividend.evaluate environment =
          quotient * modulus.evaluate environment +
            remainder.evaluate environment := by
  change
    ((lessThanFormula remainder modulus).Holds environment ∧
      Exists fun quotient : Nat =>
        dividend.shift.evaluate (pushEnvironment environment quotient) =
          quotient * modulus.shift.evaluate
              (pushEnvironment environment quotient) +
            remainder.shift.evaluate
              (pushEnvironment environment quotient)) ↔ _
  constructor
  · intro formulaHolds
    exact And.intro
      ((lessThanFormula_holds remainder modulus environment).mp formulaHolds.1)
      (match formulaHolds.2 with
      | Exists.intro quotient equation =>
          Exists.intro quotient
            (Eq.trans
              (dividend.shift_evaluate environment quotient).symm
              (Eq.trans equation
                ((congrArg
                    (fun left => quotient * left +
                      remainder.shift.evaluate
                        (pushEnvironment environment quotient))
                    (modulus.shift_evaluate environment quotient)).trans
                  (congrArg
                    (fun right => quotient * modulus.evaluate environment + right)
                    (remainder.shift_evaluate environment quotient))))))
  · intro characterization
    exact And.intro
      ((lessThanFormula_holds remainder modulus environment).mpr characterization.1)
      (match characterization.2 with
      | Exists.intro quotient equation =>
          Exists.intro quotient
            (Eq.trans
              (dividend.shift_evaluate environment quotient)
              (Eq.trans equation
                ((congrArg
                    (fun left => quotient * left +
                      remainder.evaluate environment)
                    (modulus.shift_evaluate environment quotient).symm).trans
                  (congrArg
                    (fun right => quotient *
                      modulus.shift.evaluate
                        (pushEnvironment environment quotient) + right)
                    (remainder.shift_evaluate environment quotient).symm)))))

/-- Bounded quotient equations are exactly natural remainders. -/
theorem remainder_characterization
    (dividend modulus remainder : Nat)
    (positive : 0 < modulus) :
    (remainder < modulus ∧
      Exists fun quotient : Nat =>
        dividend = quotient * modulus + remainder) ↔
      remainder = constructiveRemainder dividend modulus := by
  have canonical := constructiveDivMod_spec dividend modulus positive
  constructor
  · intro characterization
    cases characterization with
    | intro bounded witness =>
        cases witness with
        | intro quotient equality =>
            exact boundedRemainder_unique
              equality
              canonical.1
              bounded
              canonical.2
  · intro equality
    rw [equality]
    constructor
    · exact canonical.2
    · exact Exists.intro
        (constructiveQuotient dividend modulus)
        canonical.1

/-- The modulus used by one component of Goedel's beta sequence. -/
def betaModulusTerm (coefficient index : RawTerm) : RawTerm :=
  RawTerm.succ
    (RawTerm.mul (RawTerm.succ index) coefficient)

/-- Arithmetic formula for one beta-sequence lookup. -/
def betaValueFormula
    (dividend coefficient index value : RawTerm) :
    RawFormula :=
  remainderFormula
    dividend
    (betaModulusTerm coefficient index)
    value

/-- The beta lookup formula preserves the common scope of its four terms. -/
theorem betaValueFormula_wellScoped
    {bound : Nat}
    (dividend coefficient index value : RawTerm)
    (dividendScoped : dividend.WellScoped bound)
    (coefficientScoped : coefficient.WellScoped bound)
    (indexScoped : index.WellScoped bound)
    (valueScoped : value.WellScoped bound) :
    (betaValueFormula dividend coefficient index value).WellScoped bound :=
  remainderFormula_wellScoped
    dividend
    (betaModulusTerm coefficient index)
    value
    dividendScoped
    (And.intro indexScoped coefficientScoped)
    valueScoped

/-- The beta lookup formula computes the intended remainder. -/
theorem betaValueFormula_holds
    (dividend coefficient index value : RawTerm)
    (environment : Environment) :
    (betaValueFormula dividend coefficient index value).Holds environment ↔
      value.evaluate environment =
        constructiveRemainder
          (dividend.evaluate environment)
          ((index.evaluate environment + 1) *
            coefficient.evaluate environment + 1) := by
  apply Iff.trans
    (remainderFormula_holds
      dividend
      (betaModulusTerm coefficient index)
      value
      environment)
  change
    (value.evaluate environment <
        Nat.succ
          (Nat.succ (index.evaluate environment) *
            coefficient.evaluate environment) ∧
      Exists fun quotient : Nat =>
        dividend.evaluate environment =
          quotient *
              Nat.succ
                (Nat.succ (index.evaluate environment) *
                  coefficient.evaluate environment) +
            value.evaluate environment) ↔ _
  apply Iff.trans
    (remainder_characterization
      (dividend.evaluate environment)
      (Nat.succ
        (Nat.succ (index.evaluate environment) *
          coefficient.evaluate environment))
      (value.evaluate environment)
      (Nat.succ_pos _))
  let modulusEquality :
      Nat.succ
          (Nat.succ (index.evaluate environment) *
            coefficient.evaluate environment) =
        (index.evaluate environment + 1) *
            coefficient.evaluate environment + 1 :=
    Eq.trans
      (congrArg Nat.succ
        (congrArg
          (fun factor => factor * coefficient.evaluate environment)
          (Nat.succ_eq_add_one (index.evaluate environment))))
      (Nat.succ_eq_add_one
        ((index.evaluate environment + 1) *
          coefficient.evaluate environment))
  let remainderEquality :=
    congrArg
      (constructiveRemainder (dividend.evaluate environment))
      modulusEquality
  exact Iff.intro
    (fun equality => equality.trans remainderEquality)
    (fun equality => equality.trans remainderEquality.symm)

end HeytingArithmetic
end RelationalPerimeter

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.HeytingArithmetic.RawFormula.existsMany_holds
#print axioms RelationalPerimeter.HeytingArithmetic.RawFormula.existsManyForward
#print axioms RelationalPerimeter.HeytingArithmetic.RawFormula.existsManyBackward
#print axioms RelationalPerimeter.HeytingArithmetic.NatVector.uncons
#print axioms RelationalPerimeter.HeytingArithmetic.betaValueFormula_holds
#print axioms RelationalPerimeter.HeytingArithmetic.constructiveDivMod_spec
#print axioms RelationalPerimeter.HeytingArithmetic.RawTermVector.variables_wellScoped
/- AXIOM_AUDIT_END -/
