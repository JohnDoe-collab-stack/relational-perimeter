import RelationalPerimeter.Agents.Constitutive.Persistence

/-! Raw input is checked after the master roles have been formed. The runtime
session stores only the restart memory, not the selection code or rich source. -/
set_option genInjectivity false
set_option maxHeartbeats 4000000
namespace ConstitutiveSearch.Agent
open SAT Resources EndogenousDecomposition Grouping

def parseCode : (shape : Binary.Shape) → List Bool → Option (Binary.Profile shape)
  | .empty, [] => some ()
  | .empty, _ :: _ => none
  | .more _, [] => none
  | .more shape, bit :: rest => (parseCode shape rest).map (fun tail => (bit, tail))

def writeCode : (shape : Binary.Shape) → Binary.Profile shape → List Bool
  | .empty, _ => []
  | .more shape, profile => profile.1 :: writeCode shape profile.2

def codeArity : Binary.Shape → Nat
  | .empty => 0
  | .more shape => codeArity shape + 1

theorem parse_length : ∀ (shape : Binary.Shape) (code : List Bool) (profile : Binary.Profile shape),
    parseCode shape code = some profile → code.length = codeArity shape
  | .empty, [], _, _ => rfl
  | .empty, _ :: _, _, impossible => by cases impossible
  | .more _, [], _, impossible => by cases impossible
  | .more shape, bit :: rest, profile, accepted => by
      cases found : parseCode shape rest with
      | none => rw [parseCode, found] at accepted; cases accepted
      | some tail => exact congrArg Nat.succ (parse_length shape rest tail found)

theorem role_code_arity : {count : Nat} → {state : CausalConstitutiveState} →
    {run : CausalConstitutiveExecutionHistory count state} →
    (roles : RelationalConstitutiveRoleHistory run) → codeArity (CertifiedRoleGrouping.roleShape roles) = count
  | _, _, _, .nil => rfl
  | _, _, _, .step _ rest => congrArg Nat.succ (role_code_arity rest)

theorem parse_write : ∀ (shape : Binary.Shape) (profile : Binary.Profile shape),
    parseCode shape (writeCode shape profile) = some profile
  | .empty, profile => by cases profile; rfl
  | .more shape, profile => by
      change (parseCode shape (writeCode shape profile.2)).map _ = _
      rw [parse_write shape profile.2]
      rfl

def decodeSelection {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    (roles : RelationalConstitutiveRoleHistory run) (code : List Bool) :
    Option (RoleOccurrenceProfile roles) :=
  (parseCode (CertifiedRoleGrouping.roleShape roles) code).map (CertifiedRoleGrouping.decode roles)

def encodeSelection {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    (roles : RelationalConstitutiveRoleHistory run) (profile : RoleOccurrenceProfile roles) : List Bool :=
  writeCode (CertifiedRoleGrouping.roleShape roles) (CertifiedRoleGrouping.encode roles profile)

theorem wrong_selection_length {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    (roles : RelationalConstitutiveRoleHistory run) (code : List Bool) (different : code.length ≠ count) :
    decodeSelection roles code = none := by
  unfold decodeSelection
  cases found : parseCode (CertifiedRoleGrouping.roleShape roles) code with
  | none => rfl
  | some profile => exact False.elim (different ((parse_length _ _ profile found).trans (role_code_arity roles)))

theorem decode_encode {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    (roles : RelationalConstitutiveRoleHistory run) (profile : RoleOccurrenceProfile roles) :
    decodeSelection roles (encodeSelection roles profile) = some profile := by
  unfold decodeSelection encodeSelection
  rw [parse_write]
  change some (CertifiedRoleGrouping.decode roles (CertifiedRoleGrouping.encode roles profile)) = _
  exact congrArg some (CertifiedRoleGrouping.decode_encode roles profile)

structure Prepared (input : Nat) (scope : List Var) (code : List Bool) : Type 3 where
  private mk ::
  master : UnifiedMaster.Instance input
  masterExact : master = UnifiedMaster.publicInstance input
  requirement : Requirement
  received : receive scope = some requirement
  profile : RoleOccurrenceProfile master.roles
  decoded : decodeSelection master.roles code = some profile

def prepare (input : Nat) (scope : List Var) (code : List Bool) :
    Except InitializationRefusal (Prepared input scope code) :=
  match received : receive scope with
  | none => .error .emptyScope
  | some requirement =>
      let master := UnifiedMaster.publicInstance input
      match decoded : decodeSelection master.roles code with
      | none => .error .invalidSelection
      | some profile => .ok ⟨master, rfl, requirement, received, profile, decoded⟩

def Prepared.memory {input : Nat} {scope : List Var} {code : List Bool}
    (prepared : Prepared input scope code) : Memory :=
  start prepared.master prepared.requirement prepared.profile

theorem Prepared.prepare_exact {input : Nat} {scope : List Var} {code : List Bool}
    (prepared : Prepared input scope code) : prepare input scope code = .ok prepared := by
  rcases prepared with ⟨master, masterExact, requirement, received, profile, decoded⟩
  cases masterExact
  dsimp only [prepare]
  split
  · rename_i absent
    cases absent.symm.trans received
  · rename_i actualRequirement actualReceived
    have sameRequirement := Option.some.inj (actualReceived.symm.trans received)
    cases sameRequirement
    split
    · rename_i absent
      cases absent.symm.trans decoded
    · rename_i actualProfile actualDecoded
      have sameProfile := Option.some.inj (actualDecoded.symm.trans decoded)
      cases sameProfile
      rfl

/-- Initialization and continuation are certified together, but the received
code and selected profile remain outside the runtime memory. -/
structure InitializationCertificate {input : Nat} {scope : List Var} {code : List Bool}
    (prepared : Prepared input scope code) : Type 3 where
  initialized : prepare input scope code = .ok prepared
  masterExact : prepared.master = UnifiedMaster.publicInstance input
  received : receive scope = some prepared.requirement
  decoded : decodeSelection prepared.master.roles code = some prepared.profile
  memoryExact : prepared.memory = start prepared.master prepared.requirement prepared.profile
  continuation : Certificate prepared.master prepared.requirement

def Prepared.certificate {input : Nat} {scope : List Var} {code : List Bool}
    (prepared : Prepared input scope code) : InitializationCertificate prepared :=
  ⟨prepared.prepare_exact, prepared.masterExact, prepared.received, prepared.decoded, rfl,
    certify prepared.master prepared.requirement⟩

def initializeAgent (input : Nat) (scope : List Var) (code : List Bool) : Except InitializationRefusal Memory :=
  (prepare input scope code).map Prepared.memory

structure Session : Type 3 where
  private mk ::
  memory : Memory

def Session.ofMaster {input : Nat} (master : UnifiedMaster.Instance input)
    (requirement : Requirement) (profile : RoleOccurrenceProfile master.roles) : Session :=
  ⟨start master requirement profile⟩

def publicAgent (input : Nat) (scope : List Var) (code : List Bool) : Except InitializationRefusal Session :=
  (initializeAgent input scope code).map Session.mk

def Session.execute (session : Session) (request : Request) : Session × Event :=
  let produced := executeInput session.memory request
  (⟨produced.1⟩, produced.2)

/-- Access to the shared proof-carrying production, without supplying an
independent authorization or replaying the rich archive. -/
def Session.produce (session : Session) (request : Request) :
    (result : Memory × Event) × RequestEvidence session.memory request result :=
  executeProducedInput session.memory request

def Session.executeAll (session : Session) (requests : List Request) : Session × List Event :=
  let produced := executeRequests session.memory requests
  (⟨produced.1⟩, produced.2)

theorem Session.execute_exact (session : Session) (request : Request) :
    ((session.execute request).1.memory, (session.execute request).2) = executeInput session.memory request := rfl

theorem Session.executeAll_exact (session : Session) (requests : List Request) :
    ((session.executeAll requests).1.memory, (session.executeAll requests).2) =
      executeRequests session.memory requests := rfl

theorem initialize_empty (input : Nat) (code : List Bool) :
    initializeAgent input [] code = .error .emptyScope := rfl

theorem initialize_invalid_selection (input : Nat) (scope : List Var) (code : List Bool)
    (requirement : Requirement) (received : receive scope = some requirement)
    (invalid : decodeSelection (UnifiedMaster.publicInstance input).roles code = none) :
    initializeAgent input scope code = .error .invalidSelection := by
  dsimp only [initializeAgent, prepare]
  split
  · rename_i absent
    cases absent.symm.trans received
  · split
    · rfl
    · rename_i profile decoded
      cases decoded.symm.trans invalid

theorem initialize_wrong_length (input : Nat) (scope : List Var) (code : List Bool)
    (requirement : Requirement) (received : receive scope = some requirement)
    (different : code.length ≠ resolutionLength input) :
    initializeAgent input scope code = .error .invalidSelection :=
  initialize_invalid_selection input scope code requirement received
    (wrong_selection_length (UnifiedMaster.publicInstance input).roles code different)

def singletonRequirement (var : Var) : Requirement :=
  (receive [var]).get (by rfl)

theorem singleton_permission (var : Var) :
    (singletonRequirement var).permission var = some (.here : Ref [var] var) := by
  change resolvePermission [var] var = _
  rw [resolvePermission, dif_pos rfl]

def firstAuthorization {input : Nat} (master : UnifiedMaster.Instance input)
    (requirement : Requirement) (profile : RoleOccurrenceProfile master.roles)
    (var : Var) (permission : Ref requirement.realizedScope var) :
    Σ value, Authorization requirement (start master requirement profile).register 0 var value :=
  let found := resolvePresent _ 0 (resolveHandle_present _ _ (by
    rw [start_register_length]
    exact Nat.zero_lt_succ input))
  ⟨found.val.1.read var, ⟨permission, found.val, found.property, rfl⟩⟩

theorem initialized_codes_admitted (input : Nat) (var : Var)
    (profile : RoleOccurrenceProfile (UnifiedMaster.publicInstance input).roles) :
    (initializeAgent input [var]
      (encodeSelection (UnifiedMaster.publicInstance input).roles profile)).isOk = true := by
  unfold initializeAgent prepare
  dsimp only [receive]
  split
  · rename_i absent
    have impossible := absent.symm.trans (decode_encode _ profile)
    cases impossible
  · rfl

def publicSession (input : Nat) (var : Var) : Session :=
  let master := UnifiedMaster.publicInstance input
  .ofMaster master (singletonRequirement var) master.distinctPair.left

theorem ofMaster_forgets_profile {input : Nat} (master : UnifiedMaster.Instance input)
    (requirement : Requirement) (left right : RoleOccurrenceProfile master.roles) :
    Session.ofMaster master requirement left = Session.ofMaster master requirement right :=
  congrArg Session.mk (initial_memories_equal master requirement left right)

theorem valid_initialization {input : Nat} {scope : List Var} {code : List Bool}
    (prepared : Prepared input scope code) (formed : prepare input scope code = .ok prepared) :
    initializeAgent input scope code = .ok prepared.memory := by
  unfold initializeAgent
  rw [formed]
  rfl

end ConstitutiveSearch.Agent
/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Agent.parseCode
#print axioms ConstitutiveSearch.Agent.writeCode
#print axioms ConstitutiveSearch.Agent.codeArity
#print axioms ConstitutiveSearch.Agent.parse_length
#print axioms ConstitutiveSearch.Agent.role_code_arity
#print axioms ConstitutiveSearch.Agent.wrong_selection_length
#print axioms ConstitutiveSearch.Agent.parse_write
#print axioms ConstitutiveSearch.Agent.decodeSelection
#print axioms ConstitutiveSearch.Agent.encodeSelection
#print axioms ConstitutiveSearch.Agent.decode_encode
#print axioms ConstitutiveSearch.Agent.prepare
#print axioms ConstitutiveSearch.Agent.Prepared.memory
#print axioms ConstitutiveSearch.Agent.Prepared.certificate
#print axioms ConstitutiveSearch.Agent.Prepared.prepare_exact
#print axioms ConstitutiveSearch.Agent.InitializationCertificate
#print axioms ConstitutiveSearch.Agent.initialize_invalid_selection
#print axioms ConstitutiveSearch.Agent.initialize_wrong_length
#print axioms ConstitutiveSearch.Agent.initializeAgent
#print axioms ConstitutiveSearch.Agent.publicAgent
#print axioms ConstitutiveSearch.Agent.Session.ofMaster
#print axioms ConstitutiveSearch.Agent.Session.execute
#print axioms ConstitutiveSearch.Agent.Session.produce
#print axioms ConstitutiveSearch.Agent.Session.executeAll
#print axioms ConstitutiveSearch.Agent.Session.execute_exact
#print axioms ConstitutiveSearch.Agent.Session.executeAll_exact
#print axioms ConstitutiveSearch.Agent.initialize_empty
#print axioms ConstitutiveSearch.Agent.singletonRequirement
#print axioms ConstitutiveSearch.Agent.singleton_permission
#print axioms ConstitutiveSearch.Agent.firstAuthorization
#print axioms ConstitutiveSearch.Agent.initialized_codes_admitted
#print axioms ConstitutiveSearch.Agent.publicSession
#print axioms ConstitutiveSearch.Agent.ofMaster_forgets_profile
#print axioms ConstitutiveSearch.Agent.valid_initialization
/- AXIOM_AUDIT_END -/
