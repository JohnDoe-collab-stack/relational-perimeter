import RelationalPerimeter.Instances.HeytingArithmetic.InternalExistentialElimination
import RelationalPerimeter.Instances.HeytingArithmetic.InternalPRRepresentability

/-!
# Object-level replacement of a selected free variable

The selected De Bruijn variable is abstracted into the newest variable,
allowing the ordinary equality-substitution rule to replace it everywhere in
an arbitrary formula, including below quantifiers.
-/

namespace RelationalPerimeter
namespace HeytingArithmetic

private theorem RawTerm.numeral_rename_any
    (value : Nat) (rho : Renaming) :
    (RawTerm.numeral value).rename rho = RawTerm.numeral value := by
  induction value with
  | zero => rfl
  | succ value inductionHypothesis =>
      exact congrArg RawTerm.succ inductionHypothesis

private theorem RawTerm.numeral_substitute_any
    (value : Nat) (substitution : Substitution) :
    (RawTerm.numeral value).substitute substitution =
      RawTerm.numeral value := by
  induction value with
  | zero => rfl
  | succ value inductionHypothesis =>
      exact congrArg RawTerm.succ inductionHypothesis

theorem RawTerm.renameSucc_substituteLift
    (term : RawTerm)
    (substitution : Substitution) :
    (term.rename Nat.succ).substitute (liftSubstitution substitution) =
      (term.substitute substitution).rename Nat.succ := by
  induction term with
  | bvar index => rfl
  | zero => rfl
  | succ body inductionHypothesis =>
      exact congrArg RawTerm.succ inductionHypothesis
  | add left right leftHypothesis rightHypothesis =>
      exact congrArgTwo RawTerm.add leftHypothesis rightHypothesis
  | mul left right leftHypothesis rightHypothesis =>
      exact congrArgTwo RawTerm.mul leftHypothesis rightHypothesis

theorem liftSubstitution_compose
    (first second : Substitution)
    (index : Nat) :
    (liftSubstitution first index).substitute (liftSubstitution second) =
      liftSubstitution (fun inner => (first inner).substitute second) index := by
  cases index with
  | zero => rfl
  | succ index => exact (first index).renameSucc_substituteLift second

theorem RawTerm.rename_congr
    (term : RawTerm)
    (first second : Renaming)
    (pointwise : (index : Nat) -> first index = second index) :
    term.rename first = term.rename second := by
  induction term with
  | bvar index => exact congrArg RawTerm.bvar (pointwise index)
  | zero => rfl
  | succ body inductionHypothesis =>
      exact congrArg RawTerm.succ inductionHypothesis
  | add left right leftHypothesis rightHypothesis =>
      exact congrArgTwo RawTerm.add leftHypothesis rightHypothesis
  | mul left right leftHypothesis rightHypothesis =>
      exact congrArgTwo RawTerm.mul leftHypothesis rightHypothesis

theorem RawFormula.rename_congr
    (formula : RawFormula)
    (first second : Renaming)
    (pointwise : (index : Nat) -> first index = second index) :
    formula.rename first = formula.rename second := by
  induction formula generalizing first second with
  | falsum => rfl
  | equal left right =>
      exact congrArgTwo RawFormula.equal
        (left.rename_congr first second pointwise)
        (right.rename_congr first second pointwise)
  | conj left right leftHypothesis rightHypothesis =>
      exact congrArgTwo RawFormula.conj
        (leftHypothesis first second pointwise)
        (rightHypothesis first second pointwise)
  | disj left right leftHypothesis rightHypothesis =>
      exact congrArgTwo RawFormula.disj
        (leftHypothesis first second pointwise)
        (rightHypothesis first second pointwise)
  | impl left right leftHypothesis rightHypothesis =>
      exact congrArgTwo RawFormula.impl
        (leftHypothesis first second pointwise)
        (rightHypothesis first second pointwise)
  | all body inductionHypothesis =>
      apply congrArg RawFormula.all
      apply inductionHypothesis (liftRenaming first) (liftRenaming second)
      intro index
      cases index with
      | zero => rfl
      | succ index => exact congrArg Nat.succ (pointwise index)
  | ex body inductionHypothesis =>
      apply congrArg RawFormula.ex
      apply inductionHypothesis (liftRenaming first) (liftRenaming second)
      intro index
      cases index with
      | zero => rfl
      | succ index => exact congrArg Nat.succ (pointwise index)

theorem RawTerm.substitute_compose
    (term : RawTerm)
    (first second : Substitution) :
    (term.substitute first).substitute second =
      term.substitute (fun index => (first index).substitute second) := by
  induction term with
  | bvar index => rfl
  | zero => rfl
  | succ body inductionHypothesis =>
      exact congrArg RawTerm.succ inductionHypothesis
  | add left right leftHypothesis rightHypothesis =>
      exact congrArgTwo RawTerm.add leftHypothesis rightHypothesis
  | mul left right leftHypothesis rightHypothesis =>
      exact congrArgTwo RawTerm.mul leftHypothesis rightHypothesis

theorem RawTerm.substitute_congr
    (term : RawTerm)
    (first second : Substitution)
    (pointwise : (index : Nat) -> first index = second index) :
    term.substitute first = term.substitute second := by
  induction term with
  | bvar index => exact pointwise index
  | zero => rfl
  | succ body inductionHypothesis =>
      exact congrArg RawTerm.succ inductionHypothesis
  | add left right leftHypothesis rightHypothesis =>
      exact congrArgTwo RawTerm.add leftHypothesis rightHypothesis
  | mul left right leftHypothesis rightHypothesis =>
      exact congrArgTwo RawTerm.mul leftHypothesis rightHypothesis

theorem RawFormula.substitute_congr
    (formula : RawFormula)
    (first second : Substitution)
    (pointwise : (index : Nat) -> first index = second index) :
    formula.substitute first = formula.substitute second := by
  induction formula generalizing first second with
  | falsum => rfl
  | equal left right =>
      exact congrArgTwo RawFormula.equal
        (left.substitute_congr first second pointwise)
        (right.substitute_congr first second pointwise)
  | conj left right leftHypothesis rightHypothesis =>
      exact congrArgTwo RawFormula.conj
        (leftHypothesis first second pointwise)
        (rightHypothesis first second pointwise)
  | disj left right leftHypothesis rightHypothesis =>
      exact congrArgTwo RawFormula.disj
        (leftHypothesis first second pointwise)
        (rightHypothesis first second pointwise)
  | impl left right leftHypothesis rightHypothesis =>
      exact congrArgTwo RawFormula.impl
        (leftHypothesis first second pointwise)
        (rightHypothesis first second pointwise)
  | all body inductionHypothesis =>
      apply congrArg RawFormula.all
      apply inductionHypothesis (liftSubstitution first)
        (liftSubstitution second)
      intro current
      cases current with
      | zero => rfl
      | succ index =>
          exact congrArg (fun term => term.rename Nat.succ)
            (pointwise index)
  | ex body inductionHypothesis =>
      apply congrArg RawFormula.ex
      apply inductionHypothesis (liftSubstitution first)
        (liftSubstitution second)
      intro current
      cases current with
      | zero => rfl
      | succ index =>
          exact congrArg (fun term => term.rename Nat.succ)
            (pointwise index)

theorem RawFormula.substitute_compose
    (formula : RawFormula)
    (first second : Substitution) :
    (formula.substitute first).substitute second =
      formula.substitute (fun index => (first index).substitute second) := by
  induction formula generalizing first second with
  | falsum => rfl
  | equal left right =>
      exact congrArgTwo RawFormula.equal
        (left.substitute_compose first second)
        (right.substitute_compose first second)
  | conj left right leftHypothesis rightHypothesis =>
      exact congrArgTwo RawFormula.conj
        (leftHypothesis first second) (rightHypothesis first second)
  | disj left right leftHypothesis rightHypothesis =>
      exact congrArgTwo RawFormula.disj
        (leftHypothesis first second) (rightHypothesis first second)
  | impl left right leftHypothesis rightHypothesis =>
      exact congrArgTwo RawFormula.impl
        (leftHypothesis first second) (rightHypothesis first second)
  | all body inductionHypothesis =>
      exact congrArg RawFormula.all
        ((inductionHypothesis (liftSubstitution first)
          (liftSubstitution second)).trans
          (body.substitute_congr _ _
            (liftSubstitution_compose first second)))
  | ex body inductionHypothesis =>
      exact congrArg RawFormula.ex
        ((inductionHypothesis (liftSubstitution first)
          (liftSubstitution second)).trans
          (body.substitute_congr _ _
            (liftSubstitution_compose first second)))

def abstractVariableRenamingAt (selected : Nat) : Nat -> Renaming
  | 0, index => if index = selected then 0 else Nat.succ index
  | Nat.succ _depth, 0 => 0
  | Nat.succ depth, Nat.succ index =>
      Nat.succ (abstractVariableRenamingAt selected depth index)

def replaceVariableSubstitutionAt
    (selected : Nat)
    (replacement : RawTerm) : Nat -> Substitution
  | 0, index => if index = selected then replacement else RawTerm.bvar index
  | Nat.succ _depth, 0 => RawTerm.bvar 0
  | Nat.succ depth, Nat.succ index =>
      (replaceVariableSubstitutionAt selected replacement depth index).rename
        Nat.succ

theorem abstractVariableRenamingAt_scoped
    (selected depth bound index : Nat)
    (bounded : index < depth + bound) :
    abstractVariableRenamingAt selected depth index <
      depth + Nat.succ bound := by
  induction depth generalizing index with
  | zero =>
      simp only [Nat.zero_add] at bounded ⊢
      unfold abstractVariableRenamingAt
      split
      · exact Nat.zero_lt_succ bound
      · exact Nat.succ_lt_succ bounded
  | succ depth inductionHypothesis =>
      rw [Nat.succ_add] at bounded ⊢
      cases index with
      | zero => exact Nat.zero_lt_succ _
      | succ index =>
          exact Nat.succ_lt_succ
            (inductionHypothesis index
              (Nat.lt_of_succ_lt_succ bounded))

theorem replaceVariableSubstitutionAt_scoped
    (selected depth bound index : Nat)
    (replacement : RawTerm)
    (replacementScoped : replacement.WellScoped bound)
    (bounded : index < depth + bound) :
    (replaceVariableSubstitutionAt selected replacement depth index).WellScoped
      (depth + bound) := by
  induction depth generalizing index with
  | zero =>
      simp only [Nat.zero_add] at bounded ⊢
      unfold replaceVariableSubstitutionAt
      split
      · exact replacementScoped
      · exact bounded
  | succ depth inductionHypothesis =>
      rw [Nat.succ_add] at bounded ⊢
      cases index with
      | zero => exact Nat.zero_lt_succ _
      | succ index =>
          exact RawTerm.wellScoped_rename
            _
            (inductionHypothesis index
              (Nat.lt_of_succ_lt_succ bounded))
            Nat.succ (fun _ inner => Nat.succ_lt_succ inner)

theorem abstractVariable_pointwise
    (selected depth index : Nat)
    (replacement : RawTerm) :
    (RawTerm.bvar
      (abstractVariableRenamingAt selected depth index)).substitute
        (termSubstitutionAtDepth replacement depth) =
      (RawTerm.bvar index).substitute
        (replaceVariableSubstitutionAt selected replacement depth) := by
  induction depth generalizing index with
  | zero =>
      by_cases same : index = selected
      · subst index
        change
          singleTermSubstitution replacement
              (if selected = selected then 0 else Nat.succ selected) =
            (if selected = selected then replacement else
              RawTerm.bvar selected)
        rw [if_pos rfl, if_pos rfl]
        rfl
      · change
          singleTermSubstitution replacement
              (if index = selected then 0 else Nat.succ index) =
            (if index = selected then replacement else RawTerm.bvar index)
        rw [if_neg same, if_neg same]
        rfl
  | succ depth inductionHypothesis =>
      cases index with
      | zero => rfl
      | succ index =>
          change
            ((RawTerm.bvar
              (abstractVariableRenamingAt selected depth index)).rename
                Nat.succ).substitute
              (liftSubstitution (termSubstitutionAtDepth replacement depth)) =
            ((RawTerm.bvar index).substitute
              (replaceVariableSubstitutionAt selected replacement depth)).rename
                Nat.succ
          rw [RawTerm.renameSucc_substituteLift]
          exact congrArg (fun term => term.rename Nat.succ)
            (inductionHypothesis index)

theorem RawTerm.abstractVariable_instantiateAt
    (term : RawTerm)
    (selected depth : Nat)
    (replacement : RawTerm) :
    (term.rename (abstractVariableRenamingAt selected depth)).substitute
        (termSubstitutionAtDepth replacement depth) =
      term.substitute
        (replaceVariableSubstitutionAt selected replacement depth) := by
  induction term with
  | bvar index => exact abstractVariable_pointwise selected depth index replacement
  | zero => rfl
  | succ body inductionHypothesis =>
      exact congrArg RawTerm.succ inductionHypothesis
  | add left right leftHypothesis rightHypothesis =>
      exact congrArgTwo RawTerm.add leftHypothesis rightHypothesis
  | mul left right leftHypothesis rightHypothesis =>
      exact congrArgTwo RawTerm.mul leftHypothesis rightHypothesis

theorem RawFormula.abstractVariable_instantiateAt
    (formula : RawFormula)
    (selected depth : Nat)
    (replacement : RawTerm) :
    (formula.rename (abstractVariableRenamingAt selected depth)).substitute
        (termSubstitutionAtDepth replacement depth) =
      formula.substitute
        (replaceVariableSubstitutionAt selected replacement depth) := by
  induction formula generalizing depth with
  | falsum => rfl
  | equal left right =>
      exact congrArgTwo RawFormula.equal
        (left.abstractVariable_instantiateAt selected depth replacement)
        (right.abstractVariable_instantiateAt selected depth replacement)
  | conj left right leftHypothesis rightHypothesis =>
      exact congrArgTwo RawFormula.conj
        (leftHypothesis depth) (rightHypothesis depth)
  | disj left right leftHypothesis rightHypothesis =>
      exact congrArgTwo RawFormula.disj
        (leftHypothesis depth) (rightHypothesis depth)
  | impl left right leftHypothesis rightHypothesis =>
      exact congrArgTwo RawFormula.impl
        (leftHypothesis depth) (rightHypothesis depth)
  | all body inductionHypothesis =>
      apply congrArg RawFormula.all
      calc
        (body.rename (liftRenaming
              (abstractVariableRenamingAt selected depth))).substitute
            (liftSubstitution (termSubstitutionAtDepth replacement depth)) =
            (body.rename
              (abstractVariableRenamingAt selected (Nat.succ depth))).substitute
              (liftSubstitution
                (termSubstitutionAtDepth replacement depth)) := by
          exact congrArg
            (fun renamed : RawFormula => renamed.substitute
              (liftSubstitution (termSubstitutionAtDepth replacement depth)))
            (body.rename_congr _ _ (fun index => by cases index <;> rfl))
        _ = body.substitute
              (replaceVariableSubstitutionAt selected replacement
                (Nat.succ depth)) := inductionHypothesis (Nat.succ depth)
        _ = body.substitute
              (liftSubstitution
                (replaceVariableSubstitutionAt selected replacement depth)) := by
          apply body.substitute_congr
          intro index
          cases index <;> rfl
  | ex body inductionHypothesis =>
      apply congrArg RawFormula.ex
      calc
        (body.rename (liftRenaming
              (abstractVariableRenamingAt selected depth))).substitute
            (liftSubstitution (termSubstitutionAtDepth replacement depth)) =
            (body.rename
              (abstractVariableRenamingAt selected (Nat.succ depth))).substitute
              (liftSubstitution
                (termSubstitutionAtDepth replacement depth)) := by
          exact congrArg
            (fun renamed : RawFormula => renamed.substitute
              (liftSubstitution (termSubstitutionAtDepth replacement depth)))
            (body.rename_congr _ _ (fun index => by cases index <;> rfl))
        _ = body.substitute
              (replaceVariableSubstitutionAt selected replacement
                (Nat.succ depth)) := inductionHypothesis (Nat.succ depth)
        _ = body.substitute
              (liftSubstitution
                (replaceVariableSubstitutionAt selected replacement depth)) := by
          apply body.substitute_congr
          intro index
          cases index <;> rfl

def ScopedFormula.abstractVariable
    {bound : Nat}
    (formula : ScopedFormula bound)
    (selected : Nat) : ScopedFormula (Nat.succ bound) :=
  { raw := formula.raw.rename (abstractVariableRenamingAt selected 0)
    isScoped := by
      simpa only [Nat.zero_add] using formula.raw.wellScoped_rename
        formula.isScoped (abstractVariableRenamingAt selected 0)
        (fun index bounded => by
          have normalized : index < 0 + bound := by
            simpa only [Nat.zero_add] using bounded
          simpa only [Nat.zero_add] using
            abstractVariableRenamingAt_scoped selected 0 bound index
              normalized) }

def ScopedFormula.replaceVariable
    {bound : Nat}
    (formula : ScopedFormula bound)
    (selected : Nat)
    (replacement : ScopedTerm bound) : ScopedFormula bound :=
  { raw := formula.raw.substitute
      (replaceVariableSubstitutionAt selected replacement.raw 0)
    isScoped := by
      apply formula.raw.wellScoped_substitute formula.isScoped
      intro index bounded
      have normalized : index < 0 + bound := by
        simpa only [Nat.zero_add] using bounded
      simpa only [Nat.zero_add] using
        replaceVariableSubstitutionAt_scoped selected 0 bound index
          replacement.raw replacement.isScoped normalized }

theorem ScopedFormula.abstractVariable_instantiate
    {bound : Nat}
    (formula : ScopedFormula bound)
    (selected : Nat)
    (replacement : ScopedTerm bound) :
    (formula.abstractVariable selected).instantiate replacement =
      formula.replaceVariable selected replacement := by
  apply ScopedFormula.eq_of_raw_eq
  exact formula.raw.abstractVariable_instantiateAt selected 0 replacement.raw

def replaceVariableUsingEquality
    {bound : Nat}
    {context : FormulaContext bound}
    (formula : ScopedFormula bound)
    (selected : Nat)
    (bounded : selected < bound)
    (replacement : ScopedTerm bound)
    (equality : Derivation LogicMode.intuitionistic haTheory context
      (ScopedFormula.equal (ScopedTerm.bvar selected bounded) replacement))
    (atLeft : Derivation LogicMode.intuitionistic haTheory context formula) :
    Derivation LogicMode.intuitionistic haTheory context
      (formula.replaceVariable selected replacement) := by
  let selectedTerm := ScopedTerm.bvar selected bounded
  have abstractAtSelected : Derivation LogicMode.intuitionistic haTheory context
      ((formula.abstractVariable selected).instantiate selectedTerm) := by
    rw [formula.abstractVariable_instantiate selected selectedTerm]
    have unchanged : formula.replaceVariable selected selectedTerm = formula := by
      apply ScopedFormula.eq_of_raw_eq
      apply RawFormula.substitute_eq_self_of_scoped_agreement
        formula.raw formula.isScoped
      intro index bounded
      unfold replaceVariableSubstitutionAt
      split
      · rename_i same
        exact congrArg RawTerm.bvar same.symm
      · rfl
    exact Derivation.castConclusion unchanged.symm atLeft
  let transported := Derivation.equalitySubstitution
    (formula.abstractVariable selected) equality abstractAtSelected
  rw [formula.abstractVariable_instantiate selected replacement] at transported
  exact transported

inductive VariableNumeralEqualities
    {bound : Nat}
    (context : FormulaContext bound) :
    (offset : Nat) -> {length : Nat} -> NatVector length -> Type
  | nil (offset : Nat) :
      VariableNumeralEqualities context offset NatVector.nil
  | cons
      {offset length : Nat}
      {head : Nat}
      {tail : NatVector length}
      (bounded : offset < bound)
      (headProof : Derivation LogicMode.intuitionistic haTheory context
        (ScopedFormula.equal (ScopedTerm.bvar offset bounded)
          (ScopedTerm.numeral bound head)))
      (tailProof : VariableNumeralEqualities context (Nat.succ offset) tail) :
      VariableNumeralEqualities context offset (NatVector.cons head tail)

def ScopedFormula.replaceVariables
    {bound length : Nat}
    (formula : ScopedFormula bound)
    (offset : Nat)
    (values : NatVector length) : ScopedFormula bound :=
  match values with
  | NatVector.nil => formula
  | NatVector.cons head tail =>
      (formula.replaceVariable offset (ScopedTerm.numeral bound head)).replaceVariables
        (Nat.succ offset) tail

def VariableNumeralEqualities.transport
    {bound : Nat}
    {context : FormulaContext bound}
    {offset length : Nat}
    {values : NatVector length}
    (equalities : VariableNumeralEqualities context offset values)
    (formula : ScopedFormula bound)
    (proof : Derivation LogicMode.intuitionistic haTheory context formula) :
    Derivation LogicMode.intuitionistic haTheory context
      (formula.replaceVariables offset values) :=
  match equalities with
  | .nil _offset => proof
  | .cons bounded headProof tailProof =>
      tailProof.transport
        (formula.replaceVariable offset
          (ScopedTerm.numeral bound _))
        (replaceVariableUsingEquality formula offset bounded
          (ScopedTerm.numeral bound _) headProof proof)

def RawTermVector.substitute
    {length : Nat}
    (terms : RawTermVector length)
    (substitution : Substitution) : RawTermVector length :=
  match terms with
  | RawTermVector.nil => RawTermVector.nil
  | RawTermVector.cons head tail =>
      RawTermVector.cons (head.substitute substitution)
        (tail.substitute substitution)

theorem RawTermVector.getD_substitute
    {length : Nat}
    (terms : RawTermVector length)
    (substitution : Substitution)
    (index : Nat) :
    (terms.substitute substitution).getD index =
      (terms.getD index).substitute substitution := by
  induction terms generalizing index with
  | nil => cases index <;> rfl
  | cons head tail inductionHypothesis =>
      cases index with
      | zero => rfl
      | succ index => exact inductionHypothesis index

def RawTerm.replaceVariables
    {length : Nat}
    (term : RawTerm)
    (offset : Nat)
    (values : NatVector length) : RawTerm :=
  match values with
  | NatVector.nil => term
  | NatVector.cons head tail =>
      (term.substitute
        (replaceVariableSubstitutionAt offset
          (RawTerm.numeral head) 0)).replaceVariables
        (Nat.succ offset) tail

def RawFormula.replaceVariables
    {length : Nat}
    (formula : RawFormula)
    (offset : Nat)
    (values : NatVector length) : RawFormula :=
  match values with
  | NatVector.nil => formula
  | NatVector.cons head tail =>
      (formula.substitute
        (replaceVariableSubstitutionAt offset
          (RawTerm.numeral head) 0)).replaceVariables
        (Nat.succ offset) tail

def RawTermVector.replaceVariables
    {arity length : Nat}
    (terms : RawTermVector arity)
    (offset : Nat)
    (values : NatVector length) : RawTermVector arity :=
  match terms with
  | RawTermVector.nil => RawTermVector.nil
  | RawTermVector.cons head tail =>
      RawTermVector.cons (head.replaceVariables offset values)
        (tail.replaceVariables offset values)

theorem RawTermVector.replaceVariables_nil
    {arity : Nat}
    (terms : RawTermVector arity)
    (offset : Nat) :
    terms.replaceVariables offset NatVector.nil = terms := by
  induction terms with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      exact congrArgTwo RawTermVector.cons rfl inductionHypothesis

theorem RawTermVector.replaceVariables_cons
    {arity length : Nat}
    (terms : RawTermVector arity)
    (offset head : Nat)
    (tail : NatVector length) :
    terms.replaceVariables offset (NatVector.cons head tail) =
      (terms.substitute
        (replaceVariableSubstitutionAt offset (RawTerm.numeral head) 0)).replaceVariables
          (Nat.succ offset) tail := by
  induction terms with
  | nil => rfl
  | cons term terms inductionHypothesis =>
      exact congrArgTwo RawTermVector.cons rfl inductionHypothesis

theorem ScopedFormula.replaceVariables_raw
    {bound length : Nat}
    (formula : ScopedFormula bound)
    (offset : Nat)
    (values : NatVector length) :
    (formula.replaceVariables offset values).raw =
      formula.raw.replaceVariables offset values := by
  induction values generalizing formula offset with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      exact inductionHypothesis
        (formula.replaceVariable offset (ScopedTerm.numeral bound head))
        (Nat.succ offset)

theorem ArithmeticGraph.apply_substitute
    {arity : Nat}
    (graph : ArithmeticGraph arity)
    (output : RawTerm)
    (inputs : RawTermVector arity)
    (substitution : Substitution) :
    (graph.apply output inputs).substitute substitution =
      graph.apply (output.substitute substitution)
        (inputs.substitute substitution) := by
  apply Eq.trans (graph.raw.substitute_compose _ substitution)
  apply graph.raw.substitute_congr
  intro index
  cases index with
  | zero => rfl
  | succ index =>
      exact (inputs.getD_substitute substitution index).symm

theorem ArithmeticGraph.apply_replaceVariables
    {arity length : Nat}
    (graph : ArithmeticGraph arity)
    (output : RawTerm)
    (inputs : RawTermVector arity)
    (offset : Nat)
    (values : NatVector length) :
    (graph.apply output inputs).replaceVariables offset values =
      graph.apply (output.replaceVariables offset values)
        (inputs.replaceVariables offset values) := by
  induction values generalizing output inputs offset with
  | nil =>
      rw [RawFormula.replaceVariables, RawTerm.replaceVariables,
        RawTermVector.replaceVariables_nil]
  | cons head tail inductionHypothesis =>
      rw [RawFormula.replaceVariables, RawTerm.replaceVariables,
        RawTermVector.replaceVariables_cons]
      exact Eq.trans
        (congrArg (fun formula =>
          formula.replaceVariables (Nat.succ offset) tail)
          (graph.apply_substitute output inputs
            (replaceVariableSubstitutionAt offset
              (RawTerm.numeral head) 0)))
        (inductionHypothesis
          (output.substitute
            (replaceVariableSubstitutionAt offset
              (RawTerm.numeral head) 0))
          (inputs.substitute
            (replaceVariableSubstitutionAt offset
              (RawTerm.numeral head) 0))
          (Nat.succ offset))

theorem RawTerm.renameSucc_replaceVariableZero
    (term : RawTerm)
    (replacement : RawTerm) :
    (term.rename Nat.succ).substitute
        (replaceVariableSubstitutionAt 0 replacement 0) =
      term.rename Nat.succ := by
  induction term with
  | bvar index => rfl
  | zero => rfl
  | succ body inductionHypothesis =>
      exact congrArg RawTerm.succ inductionHypothesis
  | add left right leftHypothesis rightHypothesis =>
      exact congrArgTwo RawTerm.add leftHypothesis rightHypothesis
  | mul left right leftHypothesis rightHypothesis =>
      exact congrArgTwo RawTerm.mul leftHypothesis rightHypothesis

theorem RawTerm.renameSucc_replaceVariables
    {length : Nat}
    (term : RawTerm)
    (offset : Nat)
    (values : NatVector length) :
    (term.rename Nat.succ).replaceVariables (Nat.succ offset) values =
      (term.replaceVariables offset values).rename Nat.succ := by
  induction values generalizing term offset with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      have one :
          (term.rename Nat.succ).substitute
              (replaceVariableSubstitutionAt (Nat.succ offset)
                (RawTerm.numeral head) 0) =
            (term.substitute
              (replaceVariableSubstitutionAt offset
                (RawTerm.numeral head) 0)).rename Nat.succ := by
        induction term with
        | bvar index =>
            by_cases same : index = offset
            · subst index
              change
                (if Nat.succ offset = Nat.succ offset then
                    RawTerm.numeral head else RawTerm.bvar (Nat.succ offset)) =
                  (if offset = offset then RawTerm.numeral head else
                    RawTerm.bvar offset).rename Nat.succ
              rw [if_pos rfl, if_pos rfl,
                RawTerm.numeral_rename_any]
            · change
                (if Nat.succ index = Nat.succ offset then
                    RawTerm.numeral head else RawTerm.bvar (Nat.succ index)) =
                  (if index = offset then RawTerm.numeral head else
                    RawTerm.bvar index).rename Nat.succ
              rw [if_neg (fun equality => same (Nat.succ.inj equality)),
                if_neg same]
              rfl
        | zero => rfl
        | succ body bodyHypothesis =>
            exact congrArg RawTerm.succ bodyHypothesis
        | add left right leftHypothesis rightHypothesis =>
            exact congrArgTwo RawTerm.add leftHypothesis rightHypothesis
        | mul left right leftHypothesis rightHypothesis =>
            exact congrArgTwo RawTerm.mul leftHypothesis rightHypothesis
      exact Eq.trans
        (congrArg (fun current =>
          current.replaceVariables (Nat.succ (Nat.succ offset)) tail) one)
        (inductionHypothesis
          (term.substitute
            (replaceVariableSubstitutionAt offset
              (RawTerm.numeral head) 0))
          (Nat.succ offset))

theorem RawTerm.raise_replaceVariables_below
    {count : Nat}
    (term : RawTerm)
    (values : NatVector count) :
    (term.raise count).replaceVariables 0 values = term.raise count := by
  induction values generalizing term with
  | nil => rfl
  | @cons count head tail inductionHypothesis =>
      change
        (((term.raise count).rename Nat.succ).substitute
          (replaceVariableSubstitutionAt 0 (RawTerm.numeral head) 0)).replaceVariables
            1 tail =
          (term.raise count).rename Nat.succ
      rw [RawTerm.renameSucc_replaceVariableZero]
      rw [RawTerm.renameSucc_replaceVariables]
      exact congrArg (fun current => current.rename Nat.succ)
        (inductionHypothesis term)

theorem RawTerm.numeral_replaceVariables
    {length : Nat}
    (value offset : Nat)
    (values : NatVector length) :
    (RawTerm.numeral value).replaceVariables offset values =
      RawTerm.numeral value := by
  induction values generalizing offset with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      change
        ((RawTerm.numeral value).substitute
          (replaceVariableSubstitutionAt offset
            (RawTerm.numeral head) 0)).replaceVariables
            (Nat.succ offset) tail =
          RawTerm.numeral value
      rw [RawTerm.numeral_substitute_any]
      exact inductionHypothesis (Nat.succ offset)

private theorem RawTermVector.variables_substitute_above
    (selected : Nat)
    (replacement : RawTerm)
    (start length : Nat)
    (above : selected < start) :
    (RawTermVector.variables start length).substitute
        (replaceVariableSubstitutionAt selected replacement 0) =
      RawTermVector.variables start length := by
  induction length generalizing start with
  | zero => rfl
  | succ length inductionHypothesis =>
      apply congrArgTwo RawTermVector.cons
      · change
          replaceVariableSubstitutionAt selected replacement 0 start =
            RawTerm.bvar start
        unfold replaceVariableSubstitutionAt
        exact if_neg (Nat.ne_of_gt above)
      · exact inductionHypothesis (Nat.succ start)
          (Nat.lt_trans above (Nat.lt_succ_self start))

theorem RawTermVector.variables_replaceVariables
    {length : Nat}
    (offset : Nat)
    (values : NatVector length) :
    (RawTermVector.variables offset length).replaceVariables offset values =
      values.numeralTerms := by
  induction values generalizing offset with
  | nil => rfl
  | @cons length head tail inductionHypothesis =>
      apply congrArgTwo RawTermVector.cons
      · change
          (if offset = offset then RawTerm.numeral head else
            RawTerm.bvar offset).replaceVariables (Nat.succ offset) tail =
              RawTerm.numeral head
        rw [if_pos rfl, RawTerm.numeral_replaceVariables]
      · rw [RawTermVector.replaceVariables_cons]
        have unchanged :
            (RawTermVector.variables (Nat.succ offset) length).substitute
                (replaceVariableSubstitutionAt offset
                  (RawTerm.numeral head) 0) =
              RawTermVector.variables (Nat.succ offset) length :=
          RawTermVector.variables_substitute_above offset
            (RawTerm.numeral head) (Nat.succ offset) length
            (Nat.lt_succ_self offset)
        rw [unchanged]
        exact inductionHypothesis (Nat.succ offset)

end HeytingArithmetic
end RelationalPerimeter

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.HeytingArithmetic.abstractVariableRenamingAt
#print axioms RelationalPerimeter.HeytingArithmetic.replaceVariableSubstitutionAt
#print axioms RelationalPerimeter.HeytingArithmetic.RawFormula.abstractVariable_instantiateAt
#print axioms RelationalPerimeter.HeytingArithmetic.abstractVariable_pointwise
#print axioms RelationalPerimeter.HeytingArithmetic.RawTerm.abstractVariable_instantiateAt
#print axioms RelationalPerimeter.HeytingArithmetic.RawFormula.rename_congr
#print axioms RelationalPerimeter.HeytingArithmetic.RawFormula.substitute_congr
#print axioms RelationalPerimeter.HeytingArithmetic.RawFormula.substitute_compose
#print axioms RelationalPerimeter.HeytingArithmetic.ScopedFormula.abstractVariable_instantiate
#print axioms RelationalPerimeter.HeytingArithmetic.VariableNumeralEqualities.transport
#print axioms RelationalPerimeter.HeytingArithmetic.replaceVariableUsingEquality
#print axioms RelationalPerimeter.HeytingArithmetic.ArithmeticGraph.apply_replaceVariables
#print axioms RelationalPerimeter.HeytingArithmetic.ArithmeticGraph.apply_substitute
#print axioms RelationalPerimeter.HeytingArithmetic.RawTerm.replaceVariables
#print axioms RelationalPerimeter.HeytingArithmetic.RawFormula.replaceVariables
#print axioms RelationalPerimeter.HeytingArithmetic.RawTermVector.replaceVariables
#print axioms RelationalPerimeter.HeytingArithmetic.ScopedFormula.replaceVariables
#print axioms RelationalPerimeter.HeytingArithmetic.RawTermVector.replaceVariables_nil
#print axioms RelationalPerimeter.HeytingArithmetic.RawTermVector.replaceVariables_cons
#print axioms RelationalPerimeter.HeytingArithmetic.RawTerm.renameSucc_replaceVariables
#print axioms RelationalPerimeter.HeytingArithmetic.RawTerm.numeral_replaceVariables
#print axioms RelationalPerimeter.HeytingArithmetic.RawTermVector.variables_substitute_above
#print axioms RelationalPerimeter.HeytingArithmetic.RawTerm.raise_replaceVariables_below
#print axioms RelationalPerimeter.HeytingArithmetic.RawTermVector.variables_replaceVariables
/- AXIOM_AUDIT_END -/
