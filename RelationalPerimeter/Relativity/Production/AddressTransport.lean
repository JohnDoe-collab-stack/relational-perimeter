import RelationalPerimeter.Relativity.Production.ReferenceRenaming
import RelationalPerimeter.Relativity.Production.PortAdmissions

/-!
# Addresses carried by exact occurrence transports

The numerical permutation follows typed references. It also covers absent or
wrong-sort ports, so a refusal is transported without changing its request
constructor or its requested kind. No address creates an occurrence.
-/
set_option genInjectivity false
namespace RelationalPerimeter.Relativity.Production
open ConstitutiveSearch.Resources

structure AddressTransport {source target : List Kind}
    (references : ReferenceTransport source target) where
  forward : Nat → Nat
  backward : Nat → Nat
  forwardBackward : ∀ position, backward (forward position) = position
  backwardForward : ∀ position, forward (backward position) = position
  positions : ∀ {kind} (ref : Ref source kind),
    (references.forward ref).position = forward ref.position

theorem AddressTransport.backward_positions {source target} {references : ReferenceTransport source target}
    (addresses : AddressTransport references) {kind} (ref : Ref target kind) :
    (references.backward ref).position = addresses.backward ref.position := by
  have same := addresses.positions (references.backward ref)
  rw [references.backwardForward ref] at same
  have returned := congrArg addresses.backward same
  rw [addresses.forwardBackward] at returned
  exact returned.symm

def AddressTransport.reverse {source target} {references : ReferenceTransport source target}
    (addresses : AddressTransport references) : AddressTransport references.reverse :=
  ⟨addresses.backward, addresses.forward, addresses.backwardForward,
    addresses.forwardBackward, addresses.backward_positions⟩

def liftAddress (mapping : Nat → Nat) : Nat → Nat
  | 0 => 0
  | position + 1 => mapping position + 1

def AddressTransport.extend {source target} {references : ReferenceTransport source target}
    (addresses : AddressTransport references) (added : Kind) :
    AddressTransport (references.extend added) where
  forward := liftAddress addresses.forward
  backward := liftAddress addresses.backward
  forwardBackward := by
    intro position
    cases position with
    | zero => rfl
    | succ old => exact congrArg Nat.succ (addresses.forwardBackward old)
  backwardForward := by
    intro position
    cases position with
    | zero => rfl
    | succ old => exact congrArg Nat.succ (addresses.backwardForward old)
  positions := by
    intro kind ref
    cases ref with
    | here => rfl
    | prior old => exact congrArg Nat.succ (addresses.positions old)

def swapAddress : Nat → Nat
  | 0 => 1
  | 1 => 0
  | position + 2 => position + 2

theorem swapAddress_returns (position : Nat) : swapAddress (swapAddress position) = position := by
  cases position with
  | zero => rfl
  | succ old => cases old <;> rfl

def swapAddresses (context : List Kind) (one two : Kind) :
    AddressTransport (swapTransport context one two) where
  forward := swapAddress
  backward := swapAddress
  forwardBackward := swapAddress_returns
  backwardForward := swapAddress_returns
  positions := by
    intro kind ref
    cases ref with
    | here => rfl
    | prior old => cases old <;> rfl

def LocalRequest.rename (mapping : Nat → Nat) : LocalRequest → LocalRequest
  | .emit reading payload => .emit (mapping reading) (mapping payload)
  | .relay signal calibration => .relay (mapping signal) (mapping calibration)
  | .receive signal => .receive (mapping signal)
  | .inspect kind position => .inspect kind (mapping position)

theorem LocalRequest.rename_returns (forward backward : Nat → Nat)
    (returned : ∀ position, backward (forward position) = position) (request : LocalRequest) :
    (request.rename forward).rename backward = request := by
  cases request with
  | emit reading payload =>
    change LocalRequest.emit (backward (forward reading)) (backward (forward payload)) = _
    rw [returned reading, returned payload]
  | relay signal calibration =>
    change LocalRequest.relay (backward (forward signal)) (backward (forward calibration)) = _
    rw [returned signal, returned calibration]
  | receive signal => exact congrArg LocalRequest.receive (returned signal)
  | inspect kind position => exact congrArg (LocalRequest.inspect kind) (returned position)

def ReferenceAt.transport {source target} {references : ReferenceTransport source target}
    (addresses : AddressTransport references) {kind position}
    (located : ReferenceAt source kind position) : ReferenceAt target kind (addresses.forward position) :=
  ⟨references.forward located.ref,
    (addresses.positions located.ref).trans (congrArg addresses.forward located.exactPosition)⟩

theorem ReferenceAt.unique {context kind position} (one two : ReferenceAt context kind position) :
    one = two := by
  cases one with
  | mk first firstExact =>
    cases two with
    | mk second secondExact =>
      have same := reference_position_injective first second (firstExact.trans secondExact.symm)
      cases same
      rfl

def LocalAdmission.transport {source target : Cursor}
    {references : ReferenceTransport source.kinds target.kinds} (addresses : AddressTransport references) :
    (request : LocalRequest) → LocalAdmission source request →
      LocalAdmission target (request.rename addresses.forward)
  | .emit _ _, admitted => ⟨ReferenceAt.transport addresses admitted.1, ReferenceAt.transport addresses admitted.2⟩
  | .relay _ _, admitted => ⟨ReferenceAt.transport addresses admitted.1, ReferenceAt.transport addresses admitted.2⟩
  | .receive _, admitted => ReferenceAt.transport addresses admitted
  | .inspect _ _, admitted => ReferenceAt.transport addresses admitted

def LocalAdmission.returned {source target : Cursor}
    {references : ReferenceTransport source.kinds target.kinds} (addresses : AddressTransport references)
    (request : LocalRequest) (admitted : LocalAdmission target (request.rename addresses.forward)) :
    LocalAdmission source request :=
  (request.rename_returns addresses.forward addresses.backward addresses.forwardBackward) ▸
    LocalAdmission.transport addresses.reverse (request.rename addresses.forward) admitted

theorem LocalAdmission.unique (source : Cursor) (request : LocalRequest)
    (one two : LocalAdmission source request) : one = two := by
  cases request with
  | emit reading payload => exact Prod.ext (one.1.unique two.1) (one.2.unique two.2)
  | relay signal calibration => exact Prod.ext (one.1.unique two.1) (one.2.unique two.2)
  | receive signal => exact ReferenceAt.unique one two
  | inspect kind position => exact ReferenceAt.unique one two

theorem transported_admission_exact {source target : Cursor}
    {references : ReferenceTransport source.kinds target.kinds} (addresses : AddressTransport references)
    (request : LocalRequest) :
    admissionEnabled target (request.rename addresses.forward) = admissionEnabled source request := by
  unfold admissionEnabled
  cases decideAdmission source request with
  | inl admitted =>
    cases decideAdmission target (request.rename addresses.forward) with
    | inl _ => rfl
    | inr impossible => exact False.elim (impossible (LocalAdmission.transport addresses request admitted))
  | inr impossible =>
    cases decideAdmission target (request.rename addresses.forward) with
    | inl admitted => exact False.elim (impossible (LocalAdmission.returned addresses request admitted))
    | inr _ => rfl

end RelationalPerimeter.Relativity.Production
/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Relativity.Production.AddressTransport
#print axioms RelationalPerimeter.Relativity.Production.AddressTransport.backward_positions
#print axioms RelationalPerimeter.Relativity.Production.AddressTransport.reverse
#print axioms RelationalPerimeter.Relativity.Production.liftAddress
#print axioms RelationalPerimeter.Relativity.Production.AddressTransport.extend
#print axioms RelationalPerimeter.Relativity.Production.swapAddress
#print axioms RelationalPerimeter.Relativity.Production.swapAddress_returns
#print axioms RelationalPerimeter.Relativity.Production.swapAddresses
#print axioms RelationalPerimeter.Relativity.Production.LocalRequest.rename
#print axioms RelationalPerimeter.Relativity.Production.LocalRequest.rename_returns
#print axioms RelationalPerimeter.Relativity.Production.ReferenceAt.transport
#print axioms RelationalPerimeter.Relativity.Production.ReferenceAt.unique
#print axioms RelationalPerimeter.Relativity.Production.LocalAdmission.transport
#print axioms RelationalPerimeter.Relativity.Production.LocalAdmission.returned
#print axioms RelationalPerimeter.Relativity.Production.LocalAdmission.unique
#print axioms RelationalPerimeter.Relativity.Production.transported_admission_exact
/- AXIOM_AUDIT_END -/
