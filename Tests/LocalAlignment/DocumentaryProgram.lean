import Tests.LocalAlignment.DocumentaryDeduction

/-! Received finite programs with typed backward dependencies. Goal criteria are
independent of permission. Bindings retain actual produced occurrences, including
permitted outputs that fail their requested criterion. A missing dependency never
becomes a fabricated premise. The completion witness consumes the actual trace. -/
set_option genInjectivity false
set_option maxHeartbeats 4000000
namespace ConstitutiveSearch.Agent.Local.Documentary.Program
open Resources EndogenousDecomposition

inductive Specification where
  | quotation (demand : Documentary.Demand)
  | conclusion (demand : Deduction.Demand)

def Holds : Specification → Deduction.Kind → Int → Prop
  | .quotation demand, kind, value => match kind with
    | .quotation item => value = Int.ofNat item.passage.value ∧ Documentary.Meets demand item
    | .derived _ _ _ _ _ _ => False
  | .conclusion demand, kind, value => Deduction.Meets demand kind value

inductive Instruction (context : List SourceKey) (policy : Deduction.Policy)
    (slots : List Specification) : Specification → Type where
  | quotation (task : Dossier.Obligation context) : Instruction context policy slots (.quotation task.demand)
  | conclusion {left right : Specification} (request : Deduction.Request policy)
      (leftRef : Ref slots left) (rightRef : Ref slots right) (demand : Deduction.Demand) :
      Instruction context policy slots (.conclusion demand)

def Instruction.quotations {context policy slots spec} : Instruction context policy slots spec → Nat
  | .quotation _ => 1
  | .conclusion _ _ _ _ => 0

inductive Script (context : List SourceKey) (policy : Deduction.Policy) :
    List Specification → List Specification → Type where
  | done {slots} : Script context policy slots slots
  | cons {before spec after} (instruction : Instruction context policy before spec)
      (tail : Script context policy (spec :: before) after) : Script context policy before after

def Script.length {context policy before after} : Script context policy before after → Nat
  | .done => 0
  | .cons _ tail => tail.length + 1

def Script.quotations {context policy before after} : Script context policy before after → Nat
  | .done => 0
  | .cons instruction tail => instruction.quotations + tail.quotations

/-- These are primitive permissions and closure laws on received specifications,
not completed conclusions, assignments, stores or execution certificates. -/
structure Compatible (policy : Deduction.Policy) (request : Deduction.Request policy)
    (left right : Specification) (demand : Deduction.Demand) where
  permission : Ref policy.allowed request.2.position
  law : ∀ (leftKind rightKind : Deduction.Kind) (leftPosition rightPosition : Nat)
    (leftValue rightValue : Int), Holds left leftKind leftValue → Holds right rightKind rightValue →
    Deduction.Meets demand
      (.derived request.1 request.2.position leftKind leftPosition rightKind rightPosition)
      (Deduction.evaluate request.1.operation leftValue rightValue)

def Ready {context} (sources : Support SourceValue context) (contract : Contract)
    {policy : Deduction.Policy} {slots spec} : Instruction context policy slots spec → Type
  | .quotation task => Dossier.PairAdmissible sources contract task
  | .conclusion (left := left) (right := right) request _ _ demand =>
      Compatible policy request left right demand

inductive Admissible {context} (sources : Support SourceValue context) (contract : Contract)
    {policy : Deduction.Policy} : {before after : List Specification} →
      Script context policy before after → Type where
  | done {slots} : Admissible sources contract (@Script.done context policy slots)
  | cons {before spec after instruction tail}
      (head : @Ready context sources contract policy before spec instruction)
      (rest : @Admissible context sources contract policy (spec :: before) after tail) :
      Admissible sources contract (.cons instruction tail)

abbrev Occurrence {context sources contract policy} (store : @Deduction.Store context sources contract policy) :=
  (kind : Deduction.Kind) × Ref store.1 kind

structure Frame {context} (sources : Support SourceValue context) (contract : Contract)
    (policy : Deduction.Policy) (slots : List Specification) where
  dossier : Dossier.State sources contract
  store : Deduction.Store sources contract policy
  bindings : {spec : Specification} → Ref slots spec → Option (Occurrence store)

structure Realized {context sources contract policy slots spec}
    (frame : @Frame context sources contract policy slots) (slot : Ref slots spec) where
  occurrence : Occurrence frame.store
  actual : frame.bindings slot = some occurrence
  meets : Holds spec occurrence.1 (frame.store.2.resources.read occurrence.2)

abbrev Complete {context sources contract policy slots}
    (frame : @Frame context sources contract policy slots) :=
  {spec : Specification} → (slot : Ref slots spec) → Realized frame slot

def holdsDecision (spec : Specification) (kind : Deduction.Kind) (value : Int) : Decidable (Holds spec kind value) :=
  match spec with
  | .conclusion demand => Deduction.meetsDecision demand kind value
  | .quotation demand => match kind with
    | .derived _ _ _ _ _ _ => .isFalse (fun impossible => impossible)
    | .quotation item =>
        match decEq value (Int.ofNat item.passage.value) with
        | .isFalse unequal => .isFalse (fun correct => unequal correct.1)
        | .isTrue exactValue => match meetsDecision demand item with
          | .isFalse incorrect => .isFalse (fun correct => incorrect correct.2)
          | .isTrue correct => .isTrue ⟨exactValue, correct⟩

inductive Verdict {context sources contract policy slots}
    (frame : @Frame context sources contract policy slots) where
  | complete (witness : Complete frame)
  | incomplete (impossible : Complete frame → False)

/-- Checking the bindings reads the actual store. It never searches for a
numerically equal replacement occurrence. -/
def verdict {context sources contract policy} : (slots : List Specification) →
    (frame : @Frame context sources contract policy slots) → Verdict frame
  | [], _ => .complete (fun ref => nomatch ref)
  | spec :: rest, frame =>
      match found : frame.bindings .here with
      | none => .incomplete (fun complete => by
          have impossible := found.symm.trans (complete .here).actual
          cases impossible)
      | some occurrence => match holdsDecision spec occurrence.1 (frame.store.2.resources.read occurrence.2) with
        | .isFalse incorrect => .incomplete (fun complete =>
            incorrect ((Option.some.inj ((complete .here).actual.symm.trans found)) ▸ (complete .here).meets))
        | .isTrue correct =>
            let tail : Frame sources contract policy rest :=
              ⟨frame.dossier, frame.store, fun old => frame.bindings (.prior old)⟩
            match verdict rest tail with
            | .incomplete impossible => .incomplete (fun complete => impossible
                (fun old => ⟨(complete (.prior old)).occurrence, (complete (.prior old)).actual,
                  (complete (.prior old)).meets⟩))
            | .complete complete => .complete (fun ref => match ref with
              | .here => ⟨occurrence, found, correct⟩
              | .prior old => ⟨(complete old).occurrence, (complete old).actual, (complete old).meets⟩)

def succeeded {context sources contract policy slots}
    (frame : @Frame context sources contract policy slots) : Bool :=
  match verdict slots frame with
  | .complete _ => true
  | .incomplete _ => false

theorem succeeded_correct {context sources contract policy slots}
    (frame : @Frame context sources contract policy slots) (passed : succeeded frame = true) : Nonempty (Complete frame) := by
  unfold succeeded at passed
  split at passed
  · exact ⟨‹Complete frame›⟩
  · cases passed

theorem forbidden_rule_incompatible {context sources contract policy slots demand}
    (frame : @Frame context sources contract policy slots) (slot : Ref slots (.conclusion demand))
    (position : Nat) (pinned : demand.rulePosition = some position)
    (absent : resolvePermission policy.allowed position = none) : Complete frame → False :=
  fun complete => Deduction.forbidden_rule_incompatible frame.store.2 demand position pinned absent
    ⟨(complete slot).occurrence.1, (complete slot).occurrence.2, (complete slot).meets⟩

def transport {context sources contract policy before after}
    (old : @Deduction.Knowledge context sources contract policy before)
    (new : Deduction.Knowledge sources contract policy after)
    (extension : Support.Extension old.resources new.resources)
    (occurrence : Occurrence ⟨before, old⟩) : Occurrence ⟨after, new⟩ :=
  ⟨occurrence.1, extension.references occurrence.2⟩

def assemble {context sources contract policy slots spec}
    (before : @Frame context sources contract policy slots)
    (dossier : Dossier.State sources contract) (after : Deduction.Store sources contract policy)
    (extension : Support.Extension before.store.2.resources after.2.resources)
    (output : Option (Occurrence after)) : Frame sources contract policy (spec :: slots) :=
  ⟨dossier, after, fun ref => match ref with
    | .here => output
    | .prior old => (before.bindings old).map (transport before.store.2 after.2 extension)⟩

structure Delivery {context sources contract policy spec}
    (store : @Deduction.Store context sources contract policy) (output : Option (Occurrence store)) where
  occurrence : Occurrence store
  actual : output = some occurrence
  meets : Holds spec occurrence.1 (store.2.resources.read occurrence.2)

def assemble_complete {context sources contract policy slots spec}
    (before : @Frame context sources contract policy slots)
    (dossier : Dossier.State sources contract) (after : Deduction.Store sources contract policy)
    (extension : Support.Extension before.store.2.resources after.2.resources)
    (output : Option (Occurrence after)) (old : Complete before)
    (fresh : @Delivery context sources contract policy spec after output) :
    Complete (assemble (spec := spec) before dossier after extension output) :=
  fun slot => match slot with
  | .here => ⟨fresh.occurrence, fresh.actual, fresh.meets⟩
  | .prior prior =>
      let realized := old prior
      ⟨transport before.store.2 after.2 extension realized.occurrence,
        congrArg (Option.map (transport before.store.2 after.2 extension)) realized.actual,
        (extension.reads realized.occurrence.2).symm ▸ realized.meets⟩

inductive Event where
  | quoted
  | derived
  | refused
  | missing

structure Step {context sources contract policy slots spec}
    (before : @Frame context sources contract policy slots)
    (instruction : Instruction context policy slots spec) where
  private mk ::
  next : Frame sources contract policy (spec :: slots)
  extension : Support.Extension before.store.2.resources next.store.2.resources
  previous : ∀ {oldSpec} (old : Ref slots oldSpec),
    next.bindings (.prior old) =
      (before.bindings old).map (transport before.store.2 next.store.2 extension)
  depth : next.dossier.cursor.depth = before.dossier.cursor.depth + instruction.quotations
  event : Event
  progress : Ready sources contract instruction → Complete before → Complete next

theorem packet_output_meets {context cursor sources contract demand left right stage memory}
    (packet : @Master.Completion context cursor sources contract demand left right stage memory) :
    Documentary.Meets demand packet.output.item := by
  have correct := packet.meets
  rw [packet.resultExact] at correct
  exact correct

def quotationStep {context sources contract policy slots}
    (before : @Frame context sources contract policy slots) (task : Dossier.Obligation context)
    (produced : Dossier.Step before.dossier task) : Step before (.quotation task) :=
  match produced with
  | ⟨stage, .complete packet⟩ =>
      let after : Deduction.Store sources contract policy := ⟨_, Deduction.quote before.store.2 packet.output⟩
      let extension := Support.Extension.produced before.store.2.resources (Deduction.quotationProducer packet.output)
      let output : Option (Occurrence after) := some ⟨_, .here⟩
      let dossier : Dossier.State sources contract := ⟨stage.next, packet.result.1⟩
      let next := assemble before dossier after extension output
      ⟨next, extension, fun _ => rfl, Dossier.Step.depth ⟨stage, .complete packet⟩, .quoted,
        fun _ complete => assemble_complete (spec := .quotation task.demand) before dossier after extension output complete
          ⟨⟨_, .here⟩, rfl, rfl, packet_output_meets packet⟩⟩
  | ⟨stage, .blocked leftImpossible rightImpossible⟩ =>
      let extension := Support.Extension.identity before.store.2.resources
      let dossier : Dossier.State sources contract := ⟨stage.next, before.dossier.memory⟩
      let next := assemble before dossier before.store extension none
      ⟨next, extension, fun _ => rfl, Dossier.Step.depth ⟨stage, .blocked leftImpossible rightImpossible⟩,
        .refused, fun ready _ => match ready with
          | .left permission meets => False.elim (leftImpossible permission meets)
          | .right permission meets => False.elim (rightImpossible permission meets)⟩

def deductionStep {context sources contract policy slots left right}
    (before : @Frame context sources contract policy slots) (request : Deduction.Request policy)
    (leftSlot : Ref slots left) (rightSlot : Ref slots right) (demand : Deduction.Demand)
    (leftOccurrence rightOccurrence : Occurrence before.store)
    (leftActual : before.bindings leftSlot = some leftOccurrence)
    (rightActual : before.bindings rightSlot = some rightOccurrence)
    (decision : Deduction.Decision before.store.2 request leftOccurrence.2 rightOccurrence.2) :
    Step before (.conclusion request leftSlot rightSlot demand) :=
  match decision with
  | .accepted action permission =>
      let after : Deduction.Store sources contract policy := ⟨_, Deduction.incorporateDerived action permission⟩
      let extension := action.transport
      let output : Option (Occurrence after) := some ⟨_, .here⟩
      let next := assemble before before.dossier after extension output
      ⟨next, extension, fun _ => rfl, (Nat.add_zero _).symm, .derived,
        fun ready complete =>
              let compatible := ready.law
              have leftMeets := (complete leftSlot).meets
              have leftSame := Option.some.inj ((complete leftSlot).actual.symm.trans leftActual)
              have rightMeets := (complete rightSlot).meets
              have rightSame := Option.some.inj ((complete rightSlot).actual.symm.trans rightActual)
              assemble_complete (spec := .conclusion demand) before before.dossier after extension output complete
                ⟨⟨_, .here⟩, rfl, action.value.symm ▸ compatible leftOccurrence.1 rightOccurrence.1
                  leftOccurrence.2.position rightOccurrence.2.position
                  (before.store.2.resources.read leftOccurrence.2) (before.store.2.resources.read rightOccurrence.2)
                  (leftSame ▸ leftMeets) (rightSame ▸ rightMeets)⟩⟩
  | .refused absent =>
      let extension := Support.Extension.identity before.store.2.resources
      let next := assemble before before.dossier before.store extension none
      ⟨next, extension, fun _ => rfl, (Nat.add_zero _).symm, .refused,
        fun ready _ => False.elim
          (resolvePermission_none policy.allowed request.2.position absent ready.permission)⟩

def decisionExtension {context sources contract policy kinds left right knowledge request leftRef rightRef}
    (decision : @Deduction.Decision context sources contract policy kinds left right knowledge request leftRef rightRef) :
    Support.Extension knowledge.resources decision.result.1.2.resources :=
  match decision with
  | .accepted action _ => action.transport
  | .refused _ => Support.Extension.identity knowledge.resources

def decisionOutput {context sources contract policy kinds left right knowledge request leftRef rightRef}
    (decision : @Deduction.Decision context sources contract policy kinds left right knowledge request leftRef rightRef) :
    Option (Occurrence decision.result.1) :=
  match decision with
  | .accepted _ _ => some ⟨_, .here⟩
  | .refused _ => none

/-- Package the actual assembled parts. Equalities align the dependent types;
the stored frame and extension are not reconstructed by the certificate. -/
def deductionStepFromParts {context sources contract policy slots left right}
    (before : @Frame context sources contract policy slots) (request : Deduction.Request policy)
    (leftSlot : Ref slots left) (rightSlot : Ref slots right) (demand : Deduction.Demand)
    (leftOccurrence rightOccurrence : Occurrence before.store)
    (leftActual : before.bindings leftSlot = some leftOccurrence)
    (rightActual : before.bindings rightSlot = some rightOccurrence)
    (decision : Deduction.Decision before.store.2 request leftOccurrence.2 rightOccurrence.2)
    (after : Deduction.Store sources contract policy)
    (afterActual : after = decision.result.1)
    (extension : Support.Extension before.store.2.resources after.2.resources)
    (extensionActual :
      extension = (afterActual.symm ▸ decisionExtension decision))
    (output : Option (Occurrence after))
    (outputActual : output = (afterActual.symm ▸ decisionOutput decision))
    (next : Frame sources contract policy (.conclusion demand :: slots))
    (nextActual : next = assemble before before.dossier after extension output) :
    Step before (.conclusion request leftSlot rightSlot demand) :=
  let original := match decision with
    | .accepted action permission => Event.derived
    | .refused _ => Event.refused
  ⟨next, nextActual.symm ▸ extension,
    fun old => by cases nextActual; rfl,
    by cases nextActual; exact (Nat.add_zero _).symm,
    original, fun ready complete => by
      cases decision with
      | accepted action permission =>
          let compatible := ready.law
          have leftMeets := (complete leftSlot).meets
          have leftSame := Option.some.inj ((complete leftSlot).actual.symm.trans leftActual)
          have rightMeets := (complete rightSlot).meets
          have rightSame := Option.some.inj ((complete rightSlot).actual.symm.trans rightActual)
          let fresh : @Delivery context sources contract policy (.conclusion demand) after output :=
            (fun (selected : Option (Occurrence after)) (found : output = selected) =>
              match selected with
              | none => False.elim (by
                  cases afterActual
                  have impossible := outputActual.symm.trans found
                  cases impossible)
              | some occurrence => ⟨occurrence, found, by
                  cases afterActual
                  have same := Option.some.inj (outputActual.symm.trans found)
                  cases same
                  exact action.value.symm ▸ compatible leftOccurrence.1 rightOccurrence.1
                    leftOccurrence.2.position rightOccurrence.2.position
                    (before.store.2.resources.read leftOccurrence.2) (before.store.2.resources.read rightOccurrence.2)
                    (leftSame ▸ leftMeets) (rightSame ▸ rightMeets)⟩) output rfl
          exact nextActual.symm ▸ (fun {spec} slot =>
            assemble_complete (spec := .conclusion demand) before before.dossier after extension output complete fresh slot)
      | refused absent =>
          exact False.elim (resolvePermission_none policy.allowed request.2.position absent ready.permission)⟩

theorem deductionStepFromParts_actual {context sources contract policy slots left right}
    (before : @Frame context sources contract policy slots) (request : Deduction.Request policy)
    (leftSlot : Ref slots left) (rightSlot : Ref slots right) (demand : Deduction.Demand)
    (leftOccurrence rightOccurrence : Occurrence before.store)
    (leftActual : before.bindings leftSlot = some leftOccurrence)
    (rightActual : before.bindings rightSlot = some rightOccurrence)
    (decision : Deduction.Decision before.store.2 request leftOccurrence.2 rightOccurrence.2)
    (after : Deduction.Store sources contract policy) (afterActual : after = decision.result.1)
    (extension : Support.Extension before.store.2.resources after.2.resources)
    (extensionActual : extension = (afterActual.symm ▸ decisionExtension decision))
    (output : Option (Occurrence after))
    (outputActual : output = (afterActual.symm ▸ decisionOutput decision))
    (next : Frame sources contract policy (.conclusion demand :: slots))
    (nextActual : next = assemble before before.dossier after extension output) :
    deductionStepFromParts before request leftSlot rightSlot demand leftOccurrence rightOccurrence
      leftActual rightActual decision after afterActual extension extensionActual output outputActual next nextActual =
      deductionStep before request leftSlot rightSlot demand leftOccurrence rightOccurrence leftActual rightActual decision := by
  cases nextActual
  cases decision <;> cases afterActual <;> cases extensionActual <;> cases outputActual <;> rfl

def missingStep {context sources contract policy slots left right}
    (before : @Frame context sources contract policy slots) (request : Deduction.Request policy)
    (leftSlot : Ref slots left) (rightSlot : Ref slots right) (demand : Deduction.Demand)
    (missing : Complete before → False) : Step before (.conclusion request leftSlot rightSlot demand) :=
  let extension := Support.Extension.identity before.store.2.resources
  let next := assemble before before.dossier before.store extension none
  ⟨next, extension, fun _ => rfl, (Nat.add_zero _).symm, .missing,
    fun _ complete => False.elim (missing complete)⟩

def step {context sources contract policy slots spec}
    (before : @Frame context sources contract policy slots)
    (instruction : Instruction context policy slots spec) : Step before instruction :=
  match instruction with
  | .quotation task => quotationStep before task (Dossier.step before.dossier task)
  | .conclusion request leftSlot rightSlot demand =>
      match leftActual : before.bindings leftSlot with
      | none => missingStep before request leftSlot rightSlot demand
          (fun complete => by
            have impossible := leftActual.symm.trans (complete leftSlot).actual
            cases impossible)
      | some leftOccurrence => match rightActual : before.bindings rightSlot with
        | none => missingStep before request leftSlot rightSlot demand
            (fun complete => by
              have impossible := rightActual.symm.trans (complete rightSlot).actual
              cases impossible)
        | some rightOccurrence => deductionStep before request leftSlot rightSlot demand
            leftOccurrence rightOccurrence leftActual rightActual
            (Deduction.execute before.store.2 request leftOccurrence.2 rightOccurrence.2)

inductive Execution {context sources contract policy} : {before after : List Specification} →
    (start : Frame sources contract policy before) → Script context policy before after →
      Frame sources contract policy after → Type 3 where
  | done {before start} : @Execution context sources contract policy before before start .done start
  | cons {before spec after start instruction tail finish}
      (produced : @Step context sources contract policy before spec start instruction)
      (actual : produced = step start instruction)
      (rest : @Execution context sources contract policy (spec :: before) after produced.next tail finish) :
      Execution start (.cons instruction tail) finish

def execute {context sources contract policy before after}
    (start : @Frame context sources contract policy before) (script : Script context policy before after) :
    (finish : Frame sources contract policy after) × Execution start script finish :=
  match script with
  | .done => ⟨start, .done⟩
  | .cons instruction tail =>
      let produced := step start instruction
      let rest := execute produced.next tail
      ⟨rest.1, .cons produced rfl rest.2⟩

def Execution.complete {context sources contract policy before after start script finish}
    (trace : @Execution context sources contract policy before after start script finish)
    (admissible : Admissible sources contract script) (initial : Complete start) : Complete finish :=
  match trace, admissible with
  | .done, .done => initial
  | .cons produced _ rest, .cons ready remaining => rest.complete remaining (produced.progress ready initial)

theorem accomplish {context sources contract policy before after}
    (start : @Frame context sources contract policy before) (script : Script context policy before after)
    (admissible : Admissible sources contract script) (initial : Complete start) :
    Nonempty (Complete (execute start script).1) :=
  ⟨(execute start script).2.complete admissible initial⟩

def Execution.extension {context sources contract policy before after start script finish}
    (trace : @Execution context sources contract policy before after start script finish) :
    Support.Extension start.store.2.resources finish.store.2.resources :=
  match trace with
  | .done => .identity start.store.2.resources
  | .cons produced _ rest => produced.extension.compose rest.extension

def Execution.events {context sources contract policy before after start script finish}
    (trace : @Execution context sources contract policy before after start script finish) : List Event :=
  match trace with
  | .done => []
  | .cons produced _ rest => produced.event :: rest.events

theorem Execution.depth {context sources contract policy before after start script finish}
    (trace : @Execution context sources contract policy before after start script finish) :
    finish.dossier.cursor.depth = start.dossier.cursor.depth + script.quotations := by
  induction trace with
  | done => exact (Nat.add_zero _).symm
  | cons produced actual rest tail =>
      rw [Script.quotations, tail, produced.depth, Nat.add_assoc]

theorem Execution.length {context sources contract policy before after start script finish}
    (trace : @Execution context sources contract policy before after start script finish) :
    trace.events.length = script.length := by
  induction trace with
  | done => rfl
  | cons produced actual rest tail => exact congrArg (fun n => n + 1) tail

def Script.append {context policy before middle after}
    (first : Script context policy before middle) (last : Script context policy middle after) :
    Script context policy before after :=
  match first with
  | .done => last
  | .cons instruction tail => .cons instruction (tail.append last)

def Script.previous {context policy before after}
    (script : Script context policy before after) {spec} (old : Ref before spec) : Ref after spec :=
  match script with
  | .done => old
  | .cons _ tail => tail.previous (.prior old)

theorem Execution.bindings {context sources contract policy before after start script finish}
    (trace : @Execution context sources contract policy before after start script finish)
    {spec} (old : Ref before spec) :
    finish.bindings (script.previous old) =
      (start.bindings old).map (transport start.store.2 finish.store.2 trace.extension) := by
  induction trace with
  | @done before start =>
      change start.bindings old = (start.bindings old).map _
      cases start.bindings old <;> rfl
  | @cons before spec after start instruction tailScript finish produced actual rest tail =>
      rw [Script.previous, tail, produced.previous]
      cases start.bindings old <;> rfl

theorem execute_append {context sources contract policy before middle after}
    (start : @Frame context sources contract policy before)
    (first : Script context policy before middle) (last : Script context policy middle after) :
    (execute start (first.append last)).1 = (execute (execute start first).1 last).1 := by
  induction first with
  | done => rfl
  | cons instruction tail ih => exact ih (start := (step start instruction).next) last

theorem execute_after_context_erasure {context sources contract policy before after}
    {Context : Type} (state : @Frame context sources contract policy before × Context)
    (reset : Context → Context) (script : Script context policy before after) :
    execute (state.1, reset state.2).1 script = execute state.1 script := rfl

end ConstitutiveSearch.Agent.Local.Documentary.Program
/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Program.Specification
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Program.Holds
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Program.Instruction
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Program.Instruction.quotations
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Program.Script
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Program.Script.length
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Program.Script.quotations
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Program.Compatible
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Program.Ready
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Program.Admissible
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Program.Occurrence
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Program.Frame
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Program.Realized
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Program.Complete
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Program.holdsDecision
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Program.Verdict
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Program.verdict
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Program.succeeded
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Program.succeeded_correct
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Program.forbidden_rule_incompatible
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Program.transport
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Program.assemble
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Program.Delivery
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Program.assemble_complete
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Program.Event
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Program.Step
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Program.packet_output_meets
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Program.quotationStep
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Program.deductionStep
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Program.deductionStepFromParts
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Program.decisionExtension
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Program.decisionOutput
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Program.deductionStepFromParts_actual
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Program.missingStep
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Program.step
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Program.Execution
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Program.execute
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Program.Execution.complete
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Program.accomplish
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Program.Execution.extension
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Program.Execution.events
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Program.Execution.depth
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Program.Execution.length
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Program.Script.append
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Program.Script.previous
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Program.Execution.bindings
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Program.execute_append
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Program.execute_after_context_erasure
/- AXIOM_AUDIT_END -/
