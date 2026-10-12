import Tests.LocalAlignment.DocumentaryControlRunner

/-! Positive trace statistics for the retained forwarding layers. These are
proof observations, never a traversal needed by the executable consumer.
Every new event starts at zero. Forwarding keeps the old event and adds one
actual callback layer, rather than instrumenting its administration anew. -/
set_option genInjectivity false
set_option maxHeartbeats 3000000
namespace ConstitutiveSearch.Agent.Local.Documentary.ControlAdministrationStats
open Control ControlBindings
universe u v

def adminNodes {Label : Type} {Value : Type u} {code : Code Label Value} {labels value} :
    Eval code labels value → Nat
  | .done => 0
  | .step rest => adminNodes rest
  | .admin rest => adminNodes rest + 1

def forwardLayers {Label : Type} {Value : Type u} {code : Code Label Value} {labels value} :
    Eval code labels value → Nat
  | .done => 0
  | .step rest => forwardLayers rest
  | @Eval.admin _ _ _ _ forwards _ _ rest => forwards + forwardLayers rest

theorem distribute (n a b : Nat) : n * (a + b) = n * a + n * b := by
  induction b with
  | zero => rw [Nat.add_zero, Nat.mul_zero, Nat.add_zero]
  | succ b previous => rw [Nat.add_succ, Nat.mul_succ, previous, Nat.mul_succ, Nat.add_assoc]

theorem trace_success_cost {Value : Type u} {code : Code Label Value} {fuel output tape}
    (trace : ControlRunner.Trace code fuel output tape) :
    match output with
    | none => True
    | some actual => tape.cost =
        4 + 8 * actual.labels.length + 7 * adminNodes actual.trace + 3 * forwardLayers actual.trace := by
  induction trace with
  | done => rfl
  | stop => exact True.intro
  | businessNone => exact True.intro
  | adminNone => exact True.intro
  | @businessSome label next fuel child actual rest previous =>
    change 4 + (child.cost + 4) =
      4 + 8 * (actual.labels.length + 1) + 7 * adminNodes actual.trace + 3 * forwardLayers actual.trace
    rw [previous, Nat.mul_succ]
    conv => lhs; simp only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    try (conv => rhs; simp only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm])
    try (conv => lhs; simp only [← Nat.add_assoc, Nat.reduceAdd])
    try (conv => rhs; simp only [← Nat.add_assoc, Nat.reduceAdd])
  | @adminSome event next forwards fuel child actual rest previous =>
    change (ControlRunner.adminPrefix event forwards).cost + (child.cost + 3) =
      4 + 8 * actual.labels.length + 7 * (adminNodes actual.trace + 1) +
        3 * (forwards + forwardLayers actual.trace)
    rw [ControlRunner.admin_prefix_cost, previous, Nat.mul_succ, distribute]
    conv => lhs; simp only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    try (conv => rhs; simp only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm])
    try (conv => lhs; simp only [← Nat.add_assoc, Nat.reduceAdd])
    try (conv => rhs; simp only [← Nat.add_assoc, Nat.reduceAdd])
    try (conv => lhs; simp only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm])
    try (conv => rhs; simp only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm])
    rw [Nat.add_left_comm 3 (3 * forwards) _]
    rw [← Nat.add_assoc 3 8 _]
    exact congrArg (fun value => 3 * forwards + value)
      (Nat.add_left_comm 11 (8 * actual.labels.length) _)

theorem success_cost {Value : Type u} {code : Code Label Value} {fuel actual tape}
    (trace : ControlRunner.Trace code fuel (some actual) tape) :
    tape.cost = 4 + 8 * actual.labels.length + 7 * adminNodes actual.trace + 3 * forwardLayers actual.trace :=
  trace_success_cost trace

theorem bind_forward_nodes {Label : Type} {Value : Type u} {Next : Type v}
    {code : Code Label Value} {continuation : Value → Code Label Next} {labels after value next}
    (first : Eval code labels value) (second : Eval (continuation value) after next) :
    adminNodes (first.bindForward second) = adminNodes first + adminNodes second + (2 * labels.length + 1) := by
  induction first with
  | done =>
    change adminNodes second + 1 = 0 + adminNodes second + (2 * 0 + 1)
    rw [Nat.zero_add]
  | step rest previous =>
    dsimp only [Eval.bindForward, adminNodes, List.length_cons]
    rw [previous]
    rw [Nat.mul_succ]
    repeat rw [Nat.add_assoc]
  | @admin event received forwards labels value rest previous =>
    dsimp only [Eval.bindForward, adminNodes]
    rw [previous]
    rw [Nat.add_right_comm (adminNodes rest) 1 (adminNodes second), Nat.add_right_comm (adminNodes rest + adminNodes second) 1 (2 * labels.length + 1)]

theorem bind_forward_layers {Label : Type} {Value : Type u} {Next : Type v}
    {code : Code Label Value} {continuation : Value → Code Label Next} {labels after value next}
    (first : Eval code labels value) (second : Eval (continuation value) after next) :
    forwardLayers (first.bindForward second) = forwardLayers first + adminNodes first + forwardLayers second := by
  induction first with
  | done =>
    change 0 + forwardLayers second = 0 + 0 + forwardLayers second
    rfl
  | step rest previous =>
    dsimp only [Eval.bindForward, forwardLayers, adminNodes]
    rw [Nat.zero_add, Nat.zero_add]
    exact previous second
  | @admin event next forwards labels value rest previous =>
    dsimp only [Eval.bindForward, forwardLayers, adminNodes]
    rw [previous]
    rw [Nat.add_assoc forwards 1 (forwardLayers rest + adminNodes rest + forwardLayers second)]
    rw [Nat.add_assoc (forwardLayers rest) (adminNodes rest) (forwardLayers second)]
    rw [Nat.add_left_comm 1 (forwardLayers rest) (adminNodes rest + forwardLayers second)]
    rw [Nat.add_left_comm 1 (adminNodes rest) (forwardLayers second)]
    repeat rw [Nat.add_assoc]

theorem bind_nodes {Label : Type} {Value : Type u} {Next : Type v}
    {code : Code Label Value} {continuation : Value → Code Label Next} {labels after value next}
    (first : Eval code labels value) (second : Eval (continuation value) after next) :
    adminNodes (first.bind second) = adminNodes first + adminNodes second + 2 * (labels.length + 1) := by
  dsimp only [Eval.bind, adminNodes]
  rw [bind_forward_nodes]
  rw [Nat.mul_succ]
  repeat rw [Nat.add_assoc]

theorem bind_layers {Label : Type} {Value : Type u} {Next : Type v}
    {code : Code Label Value} {continuation : Value → Code Label Next} {labels after value next}
    (first : Eval code labels value) (second : Eval (continuation value) after next) :
    forwardLayers (first.bind second) = forwardLayers first + adminNodes first + forwardLayers second := by
  change 0 + forwardLayers (first.bindForward second) = _
  rw [Nat.zero_add]
  exact bind_forward_layers first second

theorem forward_event {Label : Type} {Value : Type u} {Next : Type v}
    (event : Event) (received : Unit → Code Label Value) (forwards : Nat)
    (continuation : Value → Code Label Next) :
    (Code.admin event received forwards).bindForward continuation =
      .admin event (fun _ => (received ()).bindForward continuation) (forwards + 1) := rfl

def identityBinds : Nat → Code Label Unit
  | 0 => .done ()
  | n + 1 => (identityBinds n).bind (fun _ => .done ())

def identityTrace : (n : Nat) → Eval (identityBinds n) [] ()
  | 0 => .done
  | n + 1 => (identityTrace n).bind .done

theorem identity_nodes (n : Nat) : adminNodes (identityTrace n) = 2 * n := by
  induction n with
  | zero => rfl
  | succ n previous =>
    have computed := bind_nodes (identityTrace n) (Eval.done (value := ()))
    change adminNodes (identityTrace (n + 1)) = adminNodes (identityTrace n) + 0 + 2 * (0 + 1) at computed
    rw [computed, previous]
    change 2 * n + 0 + 2 * (0 + 1) = 2 * (n + 1)
    rw [Nat.add_zero, Nat.mul_succ]

theorem identity_layers_successor (n : Nat) : forwardLayers (identityTrace (n + 1)) = n * (n + 1) := by
  induction n with
  | zero => rfl
  | succ n previous =>
    have computed := bind_layers (identityTrace (n + 1)) (Eval.done (value := ()))
    change forwardLayers (identityTrace (n + 1 + 1)) = forwardLayers (identityTrace (n + 1)) + adminNodes (identityTrace (n + 1)) + 0 at computed
    rw [computed]
    change forwardLayers (identityTrace (n + 1)) + adminNodes (identityTrace (n + 1)) + 0 = (n + 1) * (n + 1 + 1)
    rw [previous, identity_nodes, Nat.add_zero]
    have double : 2 * (n + 1) = (n + 1) + (n + 1) :=
      (Nat.succ_mul 1 (n + 1)).trans (congrArg (fun x => x + (n + 1)) (Nat.one_mul (n + 1)))
    have total : (n + 2) * (n + 1) = n * (n + 1) + 2 * (n + 1) := by
      rw [Nat.succ_mul (n + 1) (n + 1), Nat.succ_mul n (n + 1), double, Nat.add_assoc]
    exact total.symm.trans (Nat.mul_comm (n + 2) (n + 1))

theorem identity_layers (n : Nat) : forwardLayers (identityTrace n) = n * (n - 1) := by
  cases n with
  | zero => rfl
  | succ n =>
    have reduced : n + 1 - 1 = n := rfl
    exact (identity_layers_successor n).trans ((Nat.mul_comm n (n + 1)).trans (congrArg (fun x => (n + 1) * x) reduced.symm))

end ConstitutiveSearch.Agent.Local.Documentary.ControlAdministrationStats

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlAdministrationStats.adminNodes
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlAdministrationStats.forwardLayers
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlAdministrationStats.distribute
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlAdministrationStats.trace_success_cost
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlAdministrationStats.success_cost
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlAdministrationStats.bind_forward_nodes
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlAdministrationStats.bind_forward_layers
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlAdministrationStats.bind_nodes
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlAdministrationStats.bind_layers
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlAdministrationStats.forward_event
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlAdministrationStats.identityBinds
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlAdministrationStats.identityTrace
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlAdministrationStats.identity_nodes
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlAdministrationStats.identity_layers_successor
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlAdministrationStats.identity_layers
/- AXIOM_AUDIT_END -/
