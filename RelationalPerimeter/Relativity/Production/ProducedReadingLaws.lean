import RelationalPerimeter.Relativity.Production.RecurringFutures

/-!
# Numerical laws derived from the existing positive productions

This is a downstream diagnostic, not a new source of events or admissions.
Eliminating the stored formation reconstructs a numerical derivation from its
actual received root. It does not execute any signal or comparison again.
Calibration resources remain exactly the calibration of that root.
The numerical grammar is a necessary closure law, not a converse realizer
of admitted arrivals or requests. Only the stored-formation eliminators
connect its witnesses to actual productions.

The derivation forgets occurrence identity, arrivals and rich path effects;
it cannot replace the constitutive history or authorize physical grouping.
In particular arbitrary finite production does not imply dense numerical
readings. The final separation concerns the declared zero/unit candidate,
not the impossibility of a continuous domain in the framework.
-/
set_option genInjectivity false
set_option genSizeOf false
namespace RelationalPerimeter.Relativity.Production
open ConstitutiveSearch.Resources
open Arithmetic

set_option maxHeartbeats 1000000 in
inductive ReadingGeneration (input : Received) : Rational → Type where
  | initial : ReadingGeneration input input.reading
  | relay {value : Rational} (past : ReadingGeneration input value) :
      ReadingGeneration input (Rational.add value input.calibration.increment)
  | difference {first second : Rational} (one : ReadingGeneration input first)
      (two : ReadingGeneration input second) :
      ReadingGeneration input (Rational.sub second first)

def GeneratedResource (input : Received) : (kind : Kind) → Value kind → Type
  | .reading, value => ReadingGeneration input value
  | .payload, _ => PUnit
  | .calibration, value => PLift (value = input.calibration)
  | .signal, value => ReadingGeneration input value.reading

def Formed.receivedRoot {context} {values : Values Value context}
    (past : Formed values) : Received := by
  cases past with
  | received input => exact input
  | produced old _ => exact old.receivedRoot
termination_by structural past

def Produces.generatedResource {context kind} {values : Values Value context}
    {instruction : Instruction context kind} {output : Value kind}
    (input : Received)
    (prior : ∀ {k} (ref : Ref context k), GeneratedResource input k (read values ref))
    (role : Produces values instruction output) : GeneratedResource input kind output := by
  cases role with
  | emitted reading _ => exact prior reading
  | relayed signal calibration =>
      have exactCalibration := (prior calibration).down
      change ReadingGeneration input (Rational.add _ (read values calibration).increment)
      rw [exactCalibration]
      exact .relay (prior signal)
  | received signal => exact prior signal

def Formed.generatedResource {context} {values : Values Value context}
    (past : Formed values) {kind} (ref : Ref context kind) :
    GeneratedResource past.receivedRoot kind (read values ref) := by
  cases past with
  | received input =>
      cases ref with
      | here => exact .initial
      | prior old => cases old with
        | here => exact PUnit.unit
        | prior old => cases old with
          | here => exact ⟨rfl⟩
          | prior old => cases old
  | produced prior role =>
      cases ref with
      | here => exact role.generatedResource prior.receivedRoot (fun ref => prior.generatedResource ref)
      | prior old => exact prior.generatedResource old
termination_by structural past

def InstrumentFormation.receivedRoot {context} {values : Values Value context}
    (past : InstrumentFormation values) : Received := by
  cases past with
  | @compared source _ _ _ => exact source.formation.receivedRoot
  | produced old _ => exact old.receivedRoot
termination_by structural past

def InstrumentFormation.generatedResource {context} {values : Values Value context}
    (past : InstrumentFormation values) {kind} (ref : Ref context kind) :
    GeneratedResource past.receivedRoot kind (read values ref) := by
  cases past with
  | @compared source pair output role =>
      cases ref with
      | here =>
          change ReadingGeneration source.formation.receivedRoot output
          exact (role.output_exact.trans pair.gap_exact).symm ▸
            ReadingGeneration.difference (source.formation.generatedResource pair.first)
              (source.formation.generatedResource pair.second)
      | prior old => exact source.formation.generatedResource old
  | produced prior role =>
      cases ref with
      | here => exact role.generatedResource prior.receivedRoot (fun ref => prior.generatedResource ref)
      | prior old => exact prior.generatedResource old
termination_by structural past

def RecurringFormation.receivedRoot {context} {values : Values Value context}
    (past : RecurringFormation values) : Received := by
  cases past with
  | fromCursor source => exact source.formation.receivedRoot
  | fromInstrument source => exact source.formation.receivedRoot
  | signal old _ => exact old.receivedRoot
  | comparison old _ _ _ => exact old.receivedRoot
termination_by structural past

def RecurringFormation.generatedResource {context} {values : Values Value context}
    (past : RecurringFormation values) {kind} (ref : Ref context kind) :
    GeneratedResource past.receivedRoot kind (read values ref) := by
  cases past with
  | fromCursor source => exact source.formation.generatedResource ref
  | fromInstrument source => exact source.formation.generatedResource ref
  | signal prior role =>
      cases ref with
      | here => exact role.generatedResource prior.receivedRoot (fun ref => prior.generatedResource ref)
      | prior old => exact prior.generatedResource old
  | comparison prior first second role =>
      cases ref with
      | here =>
          cases role
          exact .difference (prior.generatedResource first) (prior.generatedResource second)
      | prior old => exact prior.generatedResource old
termination_by structural past

def RecurringCursor.generatedReading (source : RecurringCursor) (ref : Ref source.kinds .reading) :
    ReadingGeneration source.formation.receivedRoot (source.read ref) :=
  source.formation.generatedResource ref

theorem recurring_extend_keeps_received_root (source : RecurringCursor) {kind}
    {action : RecurringAction source kind} (determination : RecurringDetermination source action) :
    (source.extend determination).formation.receivedRoot = source.formation.receivedRoot := by
  cases action with
  | signal instruction => cases determination with
    | mk output role => cases role <;> rfl
  | compare pair => cases determination with
    | mk output role => cases role <;> rfl

theorem RecurringStep.received_root_exact {source target : RecurringCursor}
    (step : RecurringStep source target) :
    target.formation.receivedRoot = source.formation.receivedRoot := by
  cases step with
  | mk kind action determination exactTarget =>
      cases exactTarget
      exact recurring_extend_keeps_received_root source determination

theorem recurring_history_received_root {source target : RecurringCursor}
    (history : RecurringHistory source target) :
    target.formation.receivedRoot = source.formation.receivedRoot := by
  induction history with
  | root => rfl
  | extend prior step ih => exact step.received_root_exact.trans ih

def recurring_history_generated_reading {source target : RecurringCursor}
    (history : RecurringHistory source target) (ref : Ref target.kinds .reading) :
    ReadingGeneration source.formation.receivedRoot (target.read ref) :=
  recurring_history_received_root history ▸ target.generatedReading ref

/-- Consume the already returned execution and cursor. This entry does not
run requests; the diagnostic is not a second productive continuation. -/
def RecurringRequestedExecution.generatedReading {source : RecurringCursor}
    (execution : RecurringRequestedExecution source) (ref : Ref execution.cursor.kinds .reading) :
    ReadingGeneration source.formation.receivedRoot (execution.cursor.read ref) :=
  recurring_history_generated_reading execution.history ref

/-- Fresh-request convenience entry: run the declared requests once, then
diagnose the returned execution. Use `generatedReading` when it is stored. -/
def recurring_requests_generated_reading (source : RecurringCursor) (requests : List RecurringRequest)
    (ref : Ref (runRecurringRequests source requests).cursor.kinds .reading) :
    ReadingGeneration source.formation.receivedRoot ((runRecurringRequests source requests).cursor.read ref) :=
  (runRecurringRequests source requests).generatedReading ref

/-- Signed numerical readout only; different balances and different source
occurrences may have the same reading. -/
def integralReading (balance : Balance) : Rational :=
  Rational.sub (Rational.ofNat balance.positive) (Rational.ofNat balance.negative)

theorem integral_reading_zero : integralReading Balance.zero = Rational.zero := Rational.sub_self _

theorem integral_reading_one : integralReading Balance.one = Rational.one := Rational.sub_zero _

private theorem rational_add_exchange (a b c d : Rational) :
    Rational.add (Rational.add a b) (Rational.add c d) =
      Rational.add (Rational.add a c) (Rational.add b d) := by
  rw [Rational.add_assoc, ← Rational.add_assoc b c d, Rational.add_comm b c,
    Rational.add_assoc c b d, ← Rational.add_assoc]

theorem integral_reading_add (a b : Balance) :
    integralReading (Balance.add a b) = Rational.add (integralReading a) (integralReading b) := by
  unfold integralReading Balance.add Rational.sub
  rw [← Rational.nat_add, ← Rational.nat_add, Rational.neg_add]
  exact rational_add_exchange ..

theorem integral_reading_neg (a : Balance) :
    integralReading a.neg = Rational.neg (integralReading a) := (Rational.neg_sub ..).symm

structure IntegralReading (value : Rational) where
  balance : Balance
  exact : value = integralReading balance

/-- Eliminate the numerical derivation, not the executor. These coefficients
certify a reading; they neither store nor reconstruct physical occurrences. -/
def ReadingGeneration.integral {input : Received} {value : Rational}
    (derivation : ReadingGeneration input value) (zero : input.reading = Rational.zero)
    (unit : input.calibration.increment = Rational.one) : IntegralReading value := by
  cases derivation with
  | initial => exact ⟨Balance.zero, zero.trans integral_reading_zero.symm⟩
  | relay prior =>
      let old := prior.integral zero unit
      refine ⟨Balance.add old.balance Balance.one, ?_⟩
      exact (congrArg (fun value => Rational.add value input.calibration.increment) old.exact).trans
        ((congrArg (Rational.add (integralReading old.balance)) unit).trans
          ((congrArg (Rational.add (integralReading old.balance)) integral_reading_one.symm).trans
            (integral_reading_add ..).symm))
  | difference one two =>
      let first := one.integral zero unit
      let second := two.integral zero unit
      refine ⟨Balance.add second.balance first.balance.neg, ?_⟩
      exact (congrArg (fun value => Rational.sub value _) second.exact).trans
        ((congrArg (Rational.sub (integralReading second.balance)) first.exact).trans
          ((congrArg (Rational.add (integralReading second.balance))
            (integral_reading_neg first.balance).symm).trans (integral_reading_add ..).symm))
termination_by structural derivation

theorem integral_reading_representation (balance : Balance) :
    Fraction.Agree (integralReading balance).representation
      (Fraction.ofParts balance.positive balance.negative 0) := by
  apply Fraction.trans (Rational.sub_representation_agrees ..)
  apply Fraction.trans (Fraction.add_congr (Rational.normalize_agrees _)
    (Fraction.neg_congr (Rational.normalize_agrees _)))
  unfold Fraction.Agree Fraction.add Fraction.neg Fraction.nat Fraction.ofParts
    Balance.Agree Balance.scale Balance.add Balance.neg Balance.nat
  exact_natural

private theorem double_ne_successor_double (a b : Nat) : a * 2 ≠ 1 + b * 2 := by
  induction a generalizing b with
  | zero =>
      intro same
      rw [Nat.zero_mul, Nat.add_comm] at same
      exact Nat.noConfusion same
  | succ a ih =>
      cases b with
      | zero =>
          intro same
          rw [Nat.succ_mul, Nat.zero_mul, Nat.add_zero] at same
          exact Nat.noConfusion (Nat.succ.inj same)
      | succ b =>
          intro same
          rw [Nat.succ_mul, Nat.succ_mul, ← Nat.add_assoc] at same
          exact ih b (Natural.add_cancel_right 2 same)

theorem integral_reading_ne_half (balance : Balance) :
    integralReading balance ≠ Rational.ofParts 1 0 1 := by
  intro same
  have raw := Fraction.trans (Fraction.symm (integral_reading_representation balance))
    (Fraction.trans ((Rational.equal_iff_agree ..).mp same) (Rational.normalize_agrees _))
  change balance.positive * 2 + 0 = 1 + balance.negative * 2 at raw
  rw [Nat.add_zero] at raw
  exact double_ne_successor_double balance.positive balance.negative raw

private theorem natural_integral_gap (p n : Nat) : p ≤ n ∨ n + 1 ≤ p := by
  induction p generalizing n with
  | zero => exact .inl (Nat.zero_le _)
  | succ p ih =>
      cases n with
      | zero => exact .inr (Nat.succ_le_succ (Nat.zero_le _))
      | succ n =>
          cases ih n with
          | inl below => exact .inl (Nat.succ_le_succ below)
          | inr above => exact .inr (Nat.succ_le_succ above)

/-- A genuine open numerical gap in this candidate, not only non-attainment
of one prescribed rational value. It says nothing about physical location. -/
theorem integral_reading_gap (balance : Balance) :
    Rational.Le (integralReading balance) Rational.zero ∨
      Rational.Le Rational.one (integralReading balance) := by
  cases natural_integral_gap balance.positive balance.negative with
  | inl below =>
      apply Or.inl
      apply (Fraction.le_congr (integral_reading_representation balance)
        (Rational.normalize_agrees Fraction.zero)).mpr
      change balance.positive * 1 + 0 ≤ 0 + balance.negative * 1
      rw [Nat.mul_one, Nat.mul_one, Nat.add_zero, Nat.zero_add]
      exact below
  | inr above =>
      apply Or.inr
      apply (Fraction.le_congr (Rational.normalize_agrees Fraction.one)
        (integral_reading_representation balance)).mpr
      change 1 + balance.negative * 1 ≤ balance.positive * 1 + 0
      rw [Nat.mul_one, Nat.mul_one, Nat.add_zero, Nat.add_comm 1]
      exact above

theorem generated_unit_reading_gap {input : Received} {value : Rational}
    (derivation : ReadingGeneration input value) (zero : input.reading = Rational.zero)
    (unit : input.calibration.increment = Rational.one) :
    Rational.Le value Rational.zero ∨ Rational.Le Rational.one value := by
  let witness := derivation.integral zero unit
  exact witness.exact.symm ▸ integral_reading_gap witness.balance

theorem generated_unit_reading_between {input : Received} {value : Rational}
    (derivation : ReadingGeneration input value) (zero : input.reading = Rational.zero)
    (unit : input.calibration.increment = Rational.one)
    (lower : Rational.Le Rational.zero value) (upper : Rational.Le value Rational.one) :
    value = Rational.zero ∨ value = Rational.one := by
  cases generated_unit_reading_gap derivation zero unit with
  | inl below => exact .inl (Rational.le_antisymm below lower)
  | inr above => exact .inr (Rational.le_antisymm upper above)

theorem generated_unit_reading_ne_half {input : Received} {value : Rational}
    (derivation : ReadingGeneration input value) (zero : input.reading = Rational.zero)
    (unit : input.calibration.increment = Rational.one) : value ≠ Rational.ofParts 1 0 1 := by
  let witness := derivation.integral zero unit
  rw [witness.exact]
  exact integral_reading_ne_half witness.balance

theorem recurring_unit_history_ne_half {source target : RecurringCursor}
    (history : RecurringHistory source target)
    (zero : source.formation.receivedRoot.reading = Rational.zero)
    (unit : source.formation.receivedRoot.calibration.increment = Rational.one)
    (ref : Ref target.kinds .reading) : target.read ref ≠ Rational.ofParts 1 0 1 :=
  generated_unit_reading_ne_half (recurring_history_generated_reading history ref) zero unit

end RelationalPerimeter.Relativity.Production
/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Relativity.Production.ReadingGeneration
#print axioms RelationalPerimeter.Relativity.Production.GeneratedResource
#print axioms RelationalPerimeter.Relativity.Production.Formed.receivedRoot
#print axioms RelationalPerimeter.Relativity.Production.Produces.generatedResource
#print axioms RelationalPerimeter.Relativity.Production.Formed.generatedResource
#print axioms RelationalPerimeter.Relativity.Production.InstrumentFormation.receivedRoot
#print axioms RelationalPerimeter.Relativity.Production.InstrumentFormation.generatedResource
#print axioms RelationalPerimeter.Relativity.Production.RecurringFormation.receivedRoot
#print axioms RelationalPerimeter.Relativity.Production.RecurringFormation.generatedResource
#print axioms RelationalPerimeter.Relativity.Production.RecurringCursor.generatedReading
#print axioms RelationalPerimeter.Relativity.Production.recurring_extend_keeps_received_root
#print axioms RelationalPerimeter.Relativity.Production.RecurringStep.received_root_exact
#print axioms RelationalPerimeter.Relativity.Production.recurring_history_received_root
#print axioms RelationalPerimeter.Relativity.Production.recurring_history_generated_reading
#print axioms RelationalPerimeter.Relativity.Production.RecurringRequestedExecution.generatedReading
#print axioms RelationalPerimeter.Relativity.Production.recurring_requests_generated_reading
#print axioms RelationalPerimeter.Relativity.Production.integralReading
#print axioms RelationalPerimeter.Relativity.Production.integral_reading_zero
#print axioms RelationalPerimeter.Relativity.Production.integral_reading_one
#print axioms RelationalPerimeter.Relativity.Production.integral_reading_add
#print axioms RelationalPerimeter.Relativity.Production.integral_reading_neg
#print axioms RelationalPerimeter.Relativity.Production.IntegralReading
#print axioms RelationalPerimeter.Relativity.Production.ReadingGeneration.integral
#print axioms RelationalPerimeter.Relativity.Production.integral_reading_representation
#print axioms RelationalPerimeter.Relativity.Production.integral_reading_ne_half
#print axioms RelationalPerimeter.Relativity.Production.integral_reading_gap
#print axioms RelationalPerimeter.Relativity.Production.generated_unit_reading_gap
#print axioms RelationalPerimeter.Relativity.Production.generated_unit_reading_between
#print axioms RelationalPerimeter.Relativity.Production.generated_unit_reading_ne_half
#print axioms RelationalPerimeter.Relativity.Production.recurring_unit_history_ne_half
/- AXIOM_AUDIT_END -/
