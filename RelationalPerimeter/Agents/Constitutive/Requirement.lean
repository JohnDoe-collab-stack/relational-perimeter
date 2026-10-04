import RelationalPerimeter.Constitution.Resources.ConstructedSupport
import RelationalPerimeter.Computation.ConstitutiveSearch.SAT.ConstraintTransport

/-! Received scope, positive permissions and the finite interaction language.
The scope controls restitution, not the discovery engine's variable choices. -/
set_option genInjectivity false
namespace ConstitutiveSearch.Agent
open SAT Resources

inductive ScopeKind where
  | received
  | realized

def ScopeValue : ScopeKind → Type
  | .received => List Var
  | .realized => List Var

def scopeProducer : Producer ScopeValue [.received] where
  inputKinds := [.received]
  inputs := .cons .here .nil
  outputKind := fun _ => .realized
  operation := fun args => args.1

def scopeSupport (scope : List Var) : Support ScopeValue [.realized, .received] :=
  (Support.given (Value := ScopeValue) (context := [.received]) (scope, PUnit.unit)).extend scopeProducer

structure Requirement where
  private mk ::
  scope : List Var
  nonempty : scope ≠ []
  resources : Support ScopeValue [.realized, .received]
  resourcesExact : resources = scopeSupport scope

def receive : (scope : List Var) → Option Requirement
  | [] => none
  | head :: tail => some ⟨head :: tail, (by intro impossible; cases impossible),
      scopeSupport (head :: tail), rfl⟩

def Requirement.realizedScope (requirement : Requirement) : List Var :=
  requirement.resources.read .here

theorem Requirement.scope_exact (requirement : Requirement) :
    requirement.realizedScope = requirement.scope := by
  unfold Requirement.realizedScope
  rw [requirement.resourcesExact]
  rfl

def resolvePermission : (scope : List Var) → (var : Var) → Option (Ref scope var)
  | [], _ => none
  | head :: tail, var =>
      if same : head = var then some (same ▸ Ref.here)
      else (resolvePermission tail var).map Ref.prior

theorem resolvePermission_none : ∀ (scope : List Var) (var : Var),
    resolvePermission scope var = none → Ref scope var → False
  | [], _, _, witness => nomatch witness
  | head :: tail, var, absent, witness => by
      rw [resolvePermission] at absent
      split at absent
      · cases absent
      · cases witness with
        | here => contradiction
        | prior prior =>
          have noTail : resolvePermission tail var = none := by
            cases found : resolvePermission tail var with
            | none => rfl
            | some permission => rw [found] at absent; cases absent
          exact resolvePermission_none tail var noTail prior

def Requirement.permission (requirement : Requirement) (var : Var) :=
  resolvePermission requirement.realizedScope var

inductive Request where
  | advance (steps : Nat)
  | inspect (handle : Nat) (var : Var)
  | obtain (handle : Nat) (var : Var)
  | propose (handle : Nat) (var : Var) (value : Bool)

inductive Refusal where
  | outsideScope
  | missingHandle
  | incorrectValue
  deriving DecidableEq, Repr

inductive InitializationRefusal where
  | emptyScope
  | invalidSelection
  deriving DecidableEq, Repr

theorem receive_empty : receive [] = none := rfl
theorem receive_nonempty (head : Var) (tail : List Var) :
    (receive (head :: tail)).isSome = true := rfl

end ConstitutiveSearch.Agent
/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Agent.scopeProducer
#print axioms ConstitutiveSearch.Agent.scopeSupport
#print axioms ConstitutiveSearch.Agent.receive
#print axioms ConstitutiveSearch.Agent.Requirement.scope_exact
#print axioms ConstitutiveSearch.Agent.resolvePermission
#print axioms ConstitutiveSearch.Agent.resolvePermission_none
#print axioms ConstitutiveSearch.Agent.Request
#print axioms ConstitutiveSearch.Agent.receive_empty
#print axioms ConstitutiveSearch.Agent.receive_nonempty
/- AXIOM_AUDIT_END -/
