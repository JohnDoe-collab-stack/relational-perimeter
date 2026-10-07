import RelationalPerimeter.Computation.Machine.Fabric
import RelationalPerimeter.Computation.ConstitutiveSearch.SAT.StructuralGlobalContextRelation

/-! The configured circuit contains only routing constructors and finite gates.
Its source and target widths are read from the actual certified production.
Packet slots are interface addresses, not constitutive source identities.
No SAT context, assignment callback or relation search is stored in the circuit. -/
set_option genInjectivity false
set_option autoImplicit false
namespace ConstitutiveSearch.ConnectedFabric
open SAT

structure Packet where
  slot : Nat
  bits : Signals
  deriving DecidableEq

inductive FrontierCircuit where
  | identity
  | swap
  | absorbFirst (gates : List Gate)
  | absorbSecond (gates : List Gate)
  | prepend (code : FrontierCircuit)
  | compose (first second : FrontierCircuit)

def Packet.lift (packet : Packet) : Packet := ⟨packet.slot + 1, packet.bits⟩

def FrontierCircuit.fire : FrontierCircuit → Packet → Packet
  | .identity, packet => packet
  | .swap, ⟨0, bits⟩ => ⟨1, bits⟩
  | .swap, ⟨1, bits⟩ => ⟨0, bits⟩
  | .swap, ⟨slot + 2, bits⟩ => ⟨slot + 2, bits⟩
  | .absorbFirst gates, ⟨0, bits⟩ => ⟨0, ConnectedFabric.fire gates bits⟩
  | .absorbFirst _, ⟨slot + 1, bits⟩ => ⟨slot, bits⟩
  | .absorbSecond _, ⟨0, bits⟩ => ⟨0, bits⟩
  | .absorbSecond gates, ⟨1, bits⟩ => ⟨0, ConnectedFabric.fire gates bits⟩
  | .absorbSecond _, ⟨slot + 2, bits⟩ => ⟨slot + 1, bits⟩
  | .prepend _, ⟨0, bits⟩ => ⟨0, bits⟩
  | .prepend code, ⟨slot + 1, bits⟩ => (code.fire ⟨slot, bits⟩).lift
  | .compose first second, packet => second.fire (first.fire packet)

def senseFrontier {formula : Cnf} (scope : Scope) :
    {frontier : List (GeneratedStructuralBranchContext formula)} →
    FrontierContinuation (generatedStructuralBranchSystem formula) frontier → Packet
  | _, .head continuation => ⟨0, sense scope continuation.1⟩
  | _, .tail continuation => (senseFrontier scope continuation).lift

theorem senseFrontier_slot_lt {formula : Cnf} (scope : Scope) :
    {frontier : List (GeneratedStructuralBranchContext formula)} →
    (continuation : FrontierContinuation (generatedStructuralBranchSystem formula) frontier) →
    (senseFrontier scope continuation).slot < frontier.length
  | _, .head _ => Nat.zero_lt_succ _
  | _, .tail continuation => Nat.succ_lt_succ (senseFrontier_slot_lt scope continuation)

private theorem sensed_length (scope : Scope) (assignment : Assignment) :
    (sense scope assignment).length = scope.length := by
  induction scope with
  | nil => rfl
  | cons _ _ ih => exact congrArg Nat.succ ih

theorem senseFrontier_bits_length {formula : Cnf} (scope : Scope)
    {frontier : List (GeneratedStructuralBranchContext formula)}
    (continuation : FrontierContinuation (generatedStructuralBranchSystem formula) frontier) :
    (senseFrontier scope continuation).bits.length = scope.length := by
  induction continuation with
  | head continuation => exact sensed_length scope continuation.1
  | tail continuation ih => exact ih

def lowerFrontier {formula : Cnf} (scope : Scope) (selected : Var) :
    {source target : List (GeneratedStructuralBranchContext formula)} →
    AcceptedFrontierCode (generatedStructuralFlipAtAction formula selected) source target → FrontierCircuit
  | _, _, .identity _ => .identity
  | _, _, .swap => .swap
  | _, _, .absorbFirst _relation => .absorbFirst (configure scope selected)
  | _, _, .absorbSecond _relation => .absorbSecond (configure scope selected)
  | _, _, .prepend _ code => .prepend (lowerFrontier scope selected code)
  | _, _, .compose first second => .compose (lowerFrontier scope selected first)
      (lowerFrontier scope selected second)

theorem lowerFrontier_exact {formula : Cnf} (scope : Scope) (selected : Var) :
    {source target : List (GeneratedStructuralBranchContext formula)} →
    (code : AcceptedFrontierCode (generatedStructuralFlipAtAction formula selected) source target) →
    (continuation : FrontierContinuation (generatedStructuralBranchSystem formula) source) →
    (lowerFrontier scope selected code).fire (senseFrontier scope continuation) =
      senseFrontier scope (code.eval.forward.map continuation)
  | _, _, .identity _, _ => rfl
  | _, _, .swap, .head _ => rfl
  | _, _, .swap, .tail (.head _) => rfl
  | _, _, .swap, .tail (.tail rest) => rfl
  | _, _, .absorbFirst _, .head continuation => by
      change Packet.mk 0 (fire (configure scope selected) (sense scope continuation.1)) = _
      rw [configure_exact]
      rfl
  | _, _, .absorbFirst _, .tail _ => rfl
  | _, _, .absorbSecond _, .head _ => rfl
  | _, _, .absorbSecond _, .tail (.head continuation) => by
      change Packet.mk 0 (fire (configure scope selected) (sense scope continuation.1)) = _
      rw [configure_exact]
      rfl
  | _, _, .absorbSecond _, .tail (.tail _) => rfl
  | _, _, .prepend _ _, .head _ => rfl
  | _, _, .prepend _ code, .tail continuation => by
      change ((lowerFrontier scope selected code).fire (senseFrontier scope continuation)).lift = _
      exact congrArg Packet.lift (lowerFrontier_exact scope selected code continuation)
  | _, _, .compose first second, continuation => by
      change (lowerFrontier scope selected second).fire
        ((lowerFrontier scope selected first).fire (senseFrontier scope continuation)) = _
      rw [lowerFrontier_exact scope selected first continuation]
      exact lowerFrontier_exact scope selected second (first.eval.forward.map continuation)
termination_by structural _ _ code _ => code

theorem circuit_preserves_SAT {formula : Cnf} (scope : Scope) (selected : Var)
    {source target : List (GeneratedStructuralBranchContext formula)}
    (code : AcceptedFrontierCode (generatedStructuralFlipAtAction formula selected) source target)
    (continuation : FrontierContinuation (generatedStructuralBranchSystem formula) source)
    (accepted : FrontierAccept (generatedStructuralBranchSystem formula) source continuation) :
    (lowerFrontier scope selected code).fire (senseFrontier scope continuation) =
      senseFrontier scope (code.eval.forward.map continuation) ∧
    FrontierAccept (generatedStructuralBranchSystem formula) target
      (code.eval.forward.map continuation) :=
  ⟨lowerFrontier_exact scope selected code continuation,
    code.eval.forward.preservesAccept continuation accepted⟩

end ConstitutiveSearch.ConnectedFabric
/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.ConnectedFabric.FrontierCircuit.fire
#print axioms ConstitutiveSearch.ConnectedFabric.senseFrontier_slot_lt
#print axioms ConstitutiveSearch.ConnectedFabric.senseFrontier_bits_length
#print axioms ConstitutiveSearch.ConnectedFabric.senseFrontier
#print axioms ConstitutiveSearch.ConnectedFabric.lowerFrontier
#print axioms ConstitutiveSearch.ConnectedFabric.lowerFrontier_exact
#print axioms ConstitutiveSearch.ConnectedFabric.circuit_preserves_SAT
/- AXIOM_AUDIT_END -/
