/-!
# Exact arithmetic for native finite threshold networks

The activation vector carries its exact length. Weighted evaluation is a
structural recursion over declared incoming edges; no numerical approximation
or external result is stored in this layer.
-/
set_option genInjectivity false
namespace ConstitutiveSearch.NativeMechanism

abbrev Activation := Int

structure SizedActivations (count : Nat) where
  values : List Activation
  lengthExact : values.length = count

theorem lengthAppend : (left right : List Activation) ->
    (left ++ right).length = left.length + right.length
  | left, right => by
      induction left with
      | nil => exact (Nat.zero_add right.length).symm
      | cons _ tail ih =>
          change Nat.succ ((tail ++ right).length) =
            Nat.succ tail.length + right.length
          rw [Nat.succ_add]
          exact congrArg Nat.succ ih

def SizedActivations.empty : SizedActivations 0 :=
  { values := []
    lengthExact := rfl }

def SizedActivations.snoc
    (values : SizedActivations count) (value : Activation) :
    SizedActivations (count + 1) :=
  { values := values.values ++ [value]
    lengthExact := by
      rw [lengthAppend, values.lengthExact]
      rfl }

def SizedActivations.read (values : SizedActivations count)
    (index : Fin count) : Activation :=
  values.values.get (index.cast values.lengthExact.symm)

theorem getAppendLast (values : List Activation) (value : Activation) :
    (values ++ [value]).get ⟨values.length, by
      rw [lengthAppend]
      exact Nat.lt_succ_self values.length⟩ = value := by
  induction values with
  | nil => rfl
  | cons _ rest ih =>
      change (rest ++ [value]).get ⟨rest.length, _⟩ = value
      exact ih

theorem getAppendPrior : (values : List Activation) ->
    (value : Activation) -> (index : Nat) ->
    (within : index < values.length) ->
    (values ++ [value]).get ⟨index, by
      rw [lengthAppend]
      exact Nat.lt_trans within (Nat.lt_succ_self values.length)⟩ =
      values.get ⟨index, within⟩
  | [], _, _, within => False.elim (Nat.not_lt_zero _ within)
  | _ :: _, _, 0, _ => rfl
  | _ :: rest, value, index + 1, within =>
      getAppendPrior rest value index (Nat.lt_of_succ_lt_succ within)

theorem SizedActivations.read_snoc_last
    (values : SizedActivations count) (value : Activation) :
    (values.snoc value).read (Fin.last count) = value := by
  cases values with
  | mk entries lengthExact =>
      cases lengthExact
      exact getAppendLast entries value

theorem SizedActivations.read_snoc_castSucc
    (values : SizedActivations count) (value : Activation)
    (index : Fin count) :
    (values.snoc value).read index.castSucc = values.read index := by
  unfold SizedActivations.read SizedActivations.snoc
  exact getAppendPrior values.values value index.val (by
    rw [values.lengthExact]
    exact index.isLt)

def replaceAt : List Activation -> Nat -> Activation -> List Activation
  | [], _, _ => []
  | _ :: rest, 0, replacement => replacement :: rest
  | head :: rest, index + 1, replacement =>
      head :: replaceAt rest index replacement

theorem replaceAt_length : (values : List Activation) ->
    (index : Nat) -> (replacement : Activation) ->
    (replaceAt values index replacement).length = values.length
  | [], _, _ => rfl
  | _ :: _, 0, _ => rfl
  | _ :: rest, index + 1, replacement =>
      congrArg Nat.succ (replaceAt_length rest index replacement)

def SizedActivations.replace (values : SizedActivations count)
    (index : Fin count) (replacement : Activation) : SizedActivations count :=
  { values := replaceAt values.values index.val replacement
    lengthExact := (replaceAt_length values.values index.val replacement).trans
      values.lengthExact }

theorem takeLength : (values : List Activation) -> (limit : Nat) ->
    limit ≤ values.length -> (values.take limit).length = limit
  | _, 0, _ => rfl
  | [], limit + 1, within => False.elim (Nat.not_succ_le_zero limit within)
  | _ :: rest, limit + 1, within =>
      congrArg Nat.succ
        (takeLength rest limit (Nat.le_of_succ_le_succ within))

def SizedActivations.prefix (values : SizedActivations count)
    (limit : Nat) (within : limit ≤ count) : SizedActivations limit :=
  { values := values.values.take limit
    lengthExact := takeLength values.values limit (by
      rw [values.lengthExact]
      exact within) }

structure Threshold where
  level : Int

def fires (threshold : Threshold) (value : Int) : Bool :=
  decide (threshold.level <= value)

def asActivation : Bool -> Activation
  | false => 0
  | true => 1

inductive SourceIndex (inputCount produced : Nat) where
  | receivedInput : Fin inputCount -> SourceIndex inputCount produced
  | priorNeuron : Fin produced -> SourceIndex inputCount produced

structure WeightedInput (inputCount produced : Nat) where
  source : SourceIndex inputCount produced
  weight : Int

def weightedSum
    (read : SourceIndex inputCount produced -> Activation) :
    List (WeightedInput inputCount produced) -> Int
  | [] => 0
  | edge :: rest =>
      read edge.source * edge.weight + weightedSum read rest

structure NeuronSpec (inputCount produced : Nat) where
  inputs : List (WeightedInput inputCount produced)
  bias : Int
  threshold : Threshold

def sourceValue
    (inputs : SizedActivations inputCount)
    (prior : SizedActivations produced) :
    SourceIndex inputCount produced -> Activation
  | .receivedInput index => inputs.read index
  | .priorNeuron index => prior.read index

def fireNeuron (spec : NeuronSpec inputCount produced)
    (inputs : SizedActivations inputCount)
    (prior : SizedActivations produced) : Activation :=
  asActivation (fires spec.threshold
    (weightedSum (sourceValue inputs prior) spec.inputs + spec.bias))

end ConstitutiveSearch.NativeMechanism
/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.NativeMechanism.SizedActivations
#print axioms ConstitutiveSearch.NativeMechanism.lengthAppend
#print axioms ConstitutiveSearch.NativeMechanism.SizedActivations.snoc
#print axioms ConstitutiveSearch.NativeMechanism.SizedActivations.read
#print axioms ConstitutiveSearch.NativeMechanism.getAppendLast
#print axioms ConstitutiveSearch.NativeMechanism.getAppendPrior
#print axioms ConstitutiveSearch.NativeMechanism.SizedActivations.read_snoc_last
#print axioms ConstitutiveSearch.NativeMechanism.SizedActivations.read_snoc_castSucc
#print axioms ConstitutiveSearch.NativeMechanism.replaceAt
#print axioms ConstitutiveSearch.NativeMechanism.replaceAt_length
#print axioms ConstitutiveSearch.NativeMechanism.SizedActivations.replace
#print axioms ConstitutiveSearch.NativeMechanism.takeLength
#print axioms ConstitutiveSearch.NativeMechanism.SizedActivations.prefix
#print axioms ConstitutiveSearch.NativeMechanism.weightedSum
#print axioms ConstitutiveSearch.NativeMechanism.fireNeuron
/- AXIOM_AUDIT_END -/
