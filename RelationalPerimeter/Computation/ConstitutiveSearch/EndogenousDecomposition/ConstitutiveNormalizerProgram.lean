import RelationalPerimeter.Computation.ConstitutiveSearch.EndogenousDecomposition.ExecutedOperationalReductionHistory
import RelationalPerimeter.Computation.ConstitutiveSearch.EndogenousDecomposition.ExecutedLocalSchedule

/-!
# Executed normalizer program

This module reifies the exact transport program consumed by structural-profile
normalization.  The raw syntax is indexed by the authoritative role history;
authority is a separate proposition equating every stored instruction with the
code actually returned by the corresponding execution.  The interpreter acts
on arbitrary accepted structural payloads, before any one profile is selected.
-/

namespace ConstitutiveSearch.EndogenousDecomposition

open SAT

/-- One typed instruction at an executed stage.  Its endpoints are the actual
schedule endpoints, so an unrelated transport cannot inhabit this field. -/
structure ConstitutiveNormalizerInstruction
    {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    (_run : ThreadedConstitutiveStageRun state stage) where
  code :
    TransportCode
      (GeneratedStructuralFlipAtRelation
        (rootFormula := distinctGrowingDiscoveryFormula
          (constructStage (depth + 1)).searchIndex)
        stage.schedule.entry.var)
      stage.schedule.entry.source
      stage.schedule.entry.target

/-- The instruction is authoritative exactly when it is the code returned by
the execution stored at this stage. -/
def ConstitutiveNormalizerInstruction.IsAuthoritative
    {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    {run : ThreadedConstitutiveStageRun state stage}
    (instruction : ConstitutiveNormalizerInstruction run) : Prop :=
  instruction.code = stage.execution.code

/-- The actual returned code, reified as one instruction. -/
def authoritativeNormalizerInstruction
    {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    (run : ThreadedConstitutiveStageRun state stage) :
    ConstitutiveNormalizerInstruction run :=
  ⟨stage.execution.code⟩

/-- The canonical instruction stores the returned execution code itself.  This
is definitional, not a later propositional comparison with a recompiled code. -/
theorem authoritativeNormalizerInstruction_code_exact
    {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    (run : ThreadedConstitutiveStageRun state stage) :
    (authoritativeNormalizerInstruction run).code = stage.execution.code :=
  rfl

theorem authoritativeNormalizerInstruction_isAuthoritative
    {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    (run : ThreadedConstitutiveStageRun state stage) :
    (authoritativeNormalizerInstruction run).IsAuthoritative :=
  rfl

/-- View an accepted left payload at the scheduled source.  This is
definitionally exact: `DiscoverySchedule.entry` is reconstructed from the
indexed discovery and does not carry an independently variable endpoint. -/
def leftPayloadAtScheduleSource
    {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    (run : ThreadedConstitutiveStageRun state stage)
    (payload : LocalAcceptedPayload run false) :
    { continuation : GeneratedStructuralBranchContinuation
        stage.schedule.entry.source //
      GeneratedStructuralBranchAccept
        stage.schedule.entry.source continuation } :=
  payload

/-- View an accepted schedule-target payload as the retained right sibling.
The two indices are definitionally identical for the singleton schedule type. -/
def scheduleTargetAsRetainedPayload
    {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    (run : ThreadedConstitutiveStageRun state stage)
    (payload :
      { continuation : GeneratedStructuralBranchContinuation
          stage.schedule.entry.target //
        GeneratedStructuralBranchAccept
          stage.schedule.entry.target continuation }) :
    RetainedAcceptedPayload run :=
  payload

/-- The scheduled source is exactly the left child constituted by the
discovery stored at the same stage. -/
theorem scheduledSource_from_discovery_exact
    {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    (_run : ThreadedConstitutiveStageRun state stage) :
    stage.schedule.entry.source =
      (constructStage (depth + 1)).operationalRoot.child
        stage.discovery.var false stage.discovery.fresh :=
  rfl

/-- The scheduled target is exactly the retained right child constituted by
the same discovery. -/
theorem scheduledTarget_from_discovery_exact
    {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    (_run : ThreadedConstitutiveStageRun state stage) :
    stage.schedule.entry.target =
      (constructStage (depth + 1)).operationalRoot.child
        stage.discovery.var true stage.discovery.fresh :=
  rfl

/-- Execute one stored instruction on an arbitrary local structural payload.
The left case evaluates the stored transport; the already retained right case
is carried unchanged. -/
def interpretConstitutiveNormalizerInstruction
    {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    (run : ThreadedConstitutiveStageRun state stage)
    (instruction : ConstitutiveNormalizerInstruction run) :
    (choice : Bool) -> LocalAcceptedPayload run choice ->
      RetainedAcceptedPayload run
  | false, payload =>
      let source := leftPayloadAtScheduleSource run payload
      let transport := instruction.code.eval
          (generatedStructuralFlipAtAction
            (distinctGrowingDiscoveryFormula
              (constructStage (depth + 1)).searchIndex)
            stage.schedule.entry.var)
      scheduleTargetAsRetainedPayload run
        ⟨transport.map source.1,
          transport.preservesAccept source.1 source.2⟩
  | true, payload => payload

/-- The left computation equation exposes literal evaluation of the stored
instruction.  In particular, an interpreter that bypasses `instruction.code`
cannot retain this definitional equation. -/
theorem interpretConstitutiveNormalizerInstruction_false
    {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    (run : ThreadedConstitutiveStageRun state stage)
    (instruction : ConstitutiveNormalizerInstruction run)
    (payload : LocalAcceptedPayload run false) :
    interpretConstitutiveNormalizerInstruction run instruction false payload =
      let source := leftPayloadAtScheduleSource run payload
      let transport := instruction.code.eval
          (generatedStructuralFlipAtAction
            (distinctGrowingDiscoveryFormula
              (constructStage (depth + 1)).searchIndex)
            stage.schedule.entry.var)
      scheduleTargetAsRetainedPayload run
        ⟨transport.map source.1,
          transport.preservesAccept source.1 source.2⟩ :=
  rfl

/-- The retained right payload is definitionally unchanged by one local
instruction. -/
theorem interpretConstitutiveNormalizerInstruction_true
    {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    (run : ThreadedConstitutiveStageRun state stage)
    (instruction : ConstitutiveNormalizerInstruction run)
    (payload : LocalAcceptedPayload run true) :
    interpretConstitutiveNormalizerInstruction run instruction true payload =
      payload :=
  rfl

/-- On every accepted source continuation, the returned execution code and the
discovered relation induce the same retained continuation.  The statement
passes through both explicit schedule/discovery adapters. -/
theorem executedCode_map_eq_discoveredMap
    {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    (run : ThreadedConstitutiveStageRun state stage)
    (payload : LocalAcceptedPayload run false) :
    (interpretConstitutiveNormalizerInstruction run
      (authoritativeNormalizerInstruction run) false payload).1 =
        stage.discovery.relation.mapContinuation payload.1 := by
  rw [interpretConstitutiveNormalizerInstruction_false]
  unfold authoritativeNormalizerInstruction
  rw [executedDiscoverySchedule_code stage.execution]
  rfl

/-- An authoritative instruction computes exactly the existing local
normalizer, including its accepted-payload witness. -/
theorem interpretAuthoritativeNormalizerInstruction_exact
    {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    (run : ThreadedConstitutiveStageRun state stage)
    (instruction : ConstitutiveNormalizerInstruction run)
    (authoritative : instruction.IsAuthoritative) :
    forall (choice : Bool) (payload : LocalAcceptedPayload run choice),
      interpretConstitutiveNormalizerInstruction run instruction choice payload =
        normalizeLocalAcceptedPayload run choice payload := by
  intro choice payload
  cases choice with
  | false =>
      cases instruction with
      | mk code =>
          change code = stage.execution.code at authoritative
          cases authoritative
          rw [executedDiscoverySchedule_code stage.execution]
          rfl
  | true => rfl

/-- A raw program has exactly one instruction for each role-stage constructor.
The explicit head role keeps the dependent tail tied to the state produced by
the hidden `headRun`; no independently assembled list can be substituted. -/
inductive ConstitutiveNormalizerProgram :
    {depth count : Nat} ->
    {assignment : SequentialAssignment depth} ->
    {state : ThreadedConstitutiveState depth assignment} ->
    {run : ConstitutiveExecutionHistory (count := count) state} ->
    (roles : ThreadedConstitutiveRoleHistory run) -> Type 2 where
  | nil {depth : Nat}
      {assignment : SequentialAssignment depth}
      {state : ThreadedConstitutiveState depth assignment} :
      ConstitutiveNormalizerProgram
        (ThreadedConstitutiveRoleHistory.nil (state := state))
  | step {depth count : Nat}
      {assignment : SequentialAssignment depth}
      {state : ThreadedConstitutiveState depth assignment}
      {stage : SequentialStageRun depth assignment}
      {headRun : ThreadedConstitutiveStageRun state stage}
      {tailRun : ConstitutiveExecutionHistory (count := count) headRun.nextRun.next}
      (headRole : ThreadedConstitutiveRoleStage headRun)
      (instruction : ConstitutiveNormalizerInstruction headRun)
      {tailRoles : ThreadedConstitutiveRoleHistory tailRun}
      (tail : ConstitutiveNormalizerProgram tailRoles) :
      ConstitutiveNormalizerProgram
        (ThreadedConstitutiveRoleHistory.step headRole tailRoles)

/-- Reify the returned execution code at every stage of the role history. -/
def buildConstitutiveNormalizerProgram :
    {depth count : Nat} ->
    {assignment : SequentialAssignment depth} ->
    {state : ThreadedConstitutiveState depth assignment} ->
    {run : ConstitutiveExecutionHistory (count := count) state} ->
    (roles : ThreadedConstitutiveRoleHistory run) ->
      ConstitutiveNormalizerProgram roles
  | _, _, _, _, _, .nil => .nil
  | _, _, _, _, _, @ThreadedConstitutiveRoleHistory.step
      _ _ _ _ _ headRun _ headRole tailRoles =>
      .step headRole (authoritativeNormalizerInstruction headRun)
        (buildConstitutiveNormalizerProgram tailRoles)

/-- Construction follows the role history by reduction and places the exact
returned instruction at its head. -/
theorem buildConstitutiveNormalizerProgram_step
    {depth count : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    {headRun : ThreadedConstitutiveStageRun state stage}
    {tailRun : ConstitutiveExecutionHistory (count := count) headRun.nextRun.next}
    (headRole : ThreadedConstitutiveRoleStage headRun)
    (tailRoles : ThreadedConstitutiveRoleHistory tailRun) :
    buildConstitutiveNormalizerProgram
        (ThreadedConstitutiveRoleHistory.step headRole tailRoles) =
      ConstitutiveNormalizerProgram.step headRole
        (authoritativeNormalizerInstruction headRun)
        (buildConstitutiveNormalizerProgram tailRoles) :=
  rfl

/-- Number of transport atoms stored by a raw dependent program.  This counts
only run-specific code data; the common interpreter, dependent indices and
proofs are not included in this metric. -/
def ConstitutiveNormalizerProgram.codeSize :
    {depth count : Nat} ->
    {assignment : SequentialAssignment depth} ->
    {state : ThreadedConstitutiveState depth assignment} ->
    {run : ConstitutiveExecutionHistory (count := count) state} ->
    {roles : ThreadedConstitutiveRoleHistory run} ->
      ConstitutiveNormalizerProgram roles -> Nat
  | _, _, _, _, _, _, .nil => 0
  | _, _, _, _, _, _, .step _ instruction tail =>
      instruction.code.size + tail.codeSize

/-- The program constructed from an executed role history contains exactly one
transport atom per stage. -/
theorem buildConstitutiveNormalizerProgram_codeSize :
    forall {depth count : Nat}
      {assignment : SequentialAssignment depth}
      {state : ThreadedConstitutiveState depth assignment}
      {run : ConstitutiveExecutionHistory (count := count) state}
      (roles : ThreadedConstitutiveRoleHistory run),
      (buildConstitutiveNormalizerProgram roles).codeSize =
        operationalStageCount roles
  | _, _, _, _, _, .nil => rfl
  | _, _, _, _, _, @ThreadedConstitutiveRoleHistory.step
      _ _ _ _ stage _ _ headRole tailRoles => by
      rw [buildConstitutiveNormalizerProgram_step headRole tailRoles]
      change stage.execution.code.size +
          (buildConstitutiveNormalizerProgram tailRoles).codeSize =
        operationalStageCount tailRoles + 1
      rw [executedDiscoverySchedule_code stage.execution]
      rw [ConstitutedLocalWitness.code_size]
      calc
        1 + (buildConstitutiveNormalizerProgram tailRoles).codeSize =
            (buildConstitutiveNormalizerProgram tailRoles).codeSize + 1 :=
          Nat.add_comm _ _
        _ = operationalStageCount tailRoles + 1 :=
          congrArg (fun size => size + 1)
            (buildConstitutiveNormalizerProgram_codeSize tailRoles)

/-- Recursive authority predicate for the whole program. -/
def ConstitutiveNormalizerProgram.IsAuthoritative :
    {depth count : Nat} ->
    {assignment : SequentialAssignment depth} ->
    {state : ThreadedConstitutiveState depth assignment} ->
    {run : ConstitutiveExecutionHistory (count := count) state} ->
    {roles : ThreadedConstitutiveRoleHistory run} ->
      ConstitutiveNormalizerProgram roles -> Prop
  | _, _, _, _, _, _, .nil => True
  | _, _, _, _, _, _, .step _ instruction tail =>
      instruction.IsAuthoritative ∧ tail.IsAuthoritative

theorem buildConstitutiveNormalizerProgram_isAuthoritative :
    forall {depth count : Nat}
      {assignment : SequentialAssignment depth}
      {state : ThreadedConstitutiveState depth assignment}
      {run : ConstitutiveExecutionHistory (count := count) state}
      (roles : ThreadedConstitutiveRoleHistory run),
      (buildConstitutiveNormalizerProgram roles).IsAuthoritative
  | _, _, _, _, _, .nil => True.intro
  | _, _, _, _, _, @ThreadedConstitutiveRoleHistory.step
      _ _ _ _ _ _ _ _ tailRoles =>
      ⟨rfl, buildConstitutiveNormalizerProgram_isAuthoritative tailRoles⟩

/-- A program bundled with the recursive proof that every instruction came
from the indexed execution. -/
structure AuthoritativeConstitutiveNormalizerProgram
    {depth count : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {run : ConstitutiveExecutionHistory (count := count) state}
    (roles : ThreadedConstitutiveRoleHistory run) where
  program : ConstitutiveNormalizerProgram roles
  authoritative : program.IsAuthoritative

def buildAuthoritativeConstitutiveNormalizerProgram
    {depth count : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {run : ConstitutiveExecutionHistory (count := count) state}
    (roles : ThreadedConstitutiveRoleHistory run) :
    AuthoritativeConstitutiveNormalizerProgram roles :=
  ⟨buildConstitutiveNormalizerProgram roles,
    buildConstitutiveNormalizerProgram_isAuthoritative roles⟩

/-- Erase an authoritative program to the ordinary list of compiled local
atoms.  Construction of each atom consumes the corresponding authority proof;
a raw, unrelated instruction cannot be erased through this interface. -/
def authoritativeNormalizerProgramReturnedCodes :
    {depth count : Nat} ->
    {assignment : SequentialAssignment depth} ->
    {state : ThreadedConstitutiveState depth assignment} ->
    {run : ConstitutiveExecutionHistory (count := count) state} ->
    {roles : ThreadedConstitutiveRoleHistory run} ->
    (program : ConstitutiveNormalizerProgram roles) ->
      program.IsAuthoritative -> List CompiledLocalAtom
  | _, _, _, _, _, _, .nil, _ => []
  | _, _, _, _, _, _, @ConstitutiveNormalizerProgram.step
      _ _ _ _ stage _ _ _ instruction _ tail, authority =>
      ⟨⟨_, stage.schedule.entry⟩, instruction.code,
        Eq.trans authority.1
          (executedDiscoverySchedule_code stage.execution)⟩ ::
        authoritativeNormalizerProgramReturnedCodes tail authority.2

/-- The raw program metric and the existing erased-code metric count exactly
the same stored transport atoms. -/
theorem authoritativeNormalizerProgram_codeSize_eq_compiledLocalSize
    {depth count : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {run : ConstitutiveExecutionHistory (count := count) state}
    {roles : ThreadedConstitutiveRoleHistory run}
    (program : ConstitutiveNormalizerProgram roles)
    (authority : program.IsAuthoritative) :
    program.codeSize =
      compiledLocalSize
        (authoritativeNormalizerProgramReturnedCodes program authority) := by
  induction program with
  | nil => rfl
  | step _ instruction tail inductionHypothesis =>
      change _ ∧ _ at authority
      change instruction.code.size + tail.codeSize =
        instruction.code.size +
          compiledLocalSize
            (authoritativeNormalizerProgramReturnedCodes tail authority.2)
      exact congrArg (Nat.add instruction.code.size)
        (inductionHypothesis authority.2)

/-- Erasure is exactly the code list already read from the authoritative
execution history, not merely a list of the same length. -/
theorem authoritativeNormalizerProgramReturnedCodes_exact
    {depth count : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {run : ConstitutiveExecutionHistory (count := count) state}
    {roles : ThreadedConstitutiveRoleHistory run}
    (program : ConstitutiveNormalizerProgram roles)
    (authority : program.IsAuthoritative) :
    authoritativeNormalizerProgramReturnedCodes program authority =
      run.toSequentialHistory.returnedCodes := by
  induction program with
  | nil => rfl
  | @step depth count assignment state stage headRun tailRun headRole
      instruction tailRoles tail inductionHypothesis =>
      change _ ∧ _ at authority
      let returned : CompiledLocalAtom :=
        ⟨⟨_, stage.schedule.entry⟩, instruction.code,
          Eq.trans authority.1
            (executedDiscoverySchedule_code stage.execution)⟩
      let expected : CompiledLocalAtom :=
        ⟨⟨_, stage.schedule.entry⟩, stage.execution.code,
          executedDiscoverySchedule_code stage.execution⟩
      have headExact : returned = expected :=
        Eq.trans (CompiledLocalAtom.canonical returned).symm
          (CompiledLocalAtom.canonical expected)
      change
        returned ::
            authoritativeNormalizerProgramReturnedCodes tail authority.2 =
          expected :: _
      exact Eq.trans
        (congrArg (fun headCode =>
          headCode :: authoritativeNormalizerProgramReturnedCodes tail authority.2)
          headExact)
        (congrArg (fun codes => expected :: codes)
          (inductionHypothesis authority.2))

/-- The compiled atom metric of an authoritative program is exactly the number
of constituted stages.  This is a statement about this explicit code metric,
not a universal time or memory bound. -/
theorem authoritativeNormalizerProgram_compiledSize_eq_stageCount
    {depth count : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {run : ConstitutiveExecutionHistory (count := count) state}
    {roles : ThreadedConstitutiveRoleHistory run}
    (program : ConstitutiveNormalizerProgram roles)
    (authority : program.IsAuthoritative) :
    compiledLocalSize
        (authoritativeNormalizerProgramReturnedCodes program authority) =
      operationalStageCount roles :=
  Eq.trans
    (congrArg compiledLocalSize
      (authoritativeNormalizerProgramReturnedCodes_exact program authority))
    (Eq.trans
      (returnedCodes_size run.toSequentialHistory)
      (operationalStageCount_eq_historyCount roles).symm)

/-- Interpret a raw program on every accepted structural profile. -/
def interpretConstitutiveNormalizerProgram :
    {depth count : Nat} ->
    {assignment : SequentialAssignment depth} ->
    {state : ThreadedConstitutiveState depth assignment} ->
    {run : ConstitutiveExecutionHistory (count := count) state} ->
    {roles : ThreadedConstitutiveRoleHistory run} ->
    ConstitutiveNormalizerProgram roles ->
    (profile : StructuralObligation roles) ->
      StructuralAcceptedPayload roles profile ->
        OperationalAcceptedPayload roles
  | _, _, _, _, _, _, .nil, _, _ => ()
  | _, _, _, _, _, _, @ConstitutiveNormalizerProgram.step
      _ _ _ _ _ headRun _ _ instruction _ tail, profile, payload =>
      ⟨interpretConstitutiveNormalizerInstruction headRun instruction
          profile.1 payload.1,
        interpretConstitutiveNormalizerProgram tail profile.2 payload.2⟩

/-- Program interpretation equals the canonical structural normalization when
the recursive authority predicate holds. -/
theorem interpretAuthoritativeConstitutiveNormalizerProgram_exact
    {depth count : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {run : ConstitutiveExecutionHistory (count := count) state}
    {roles : ThreadedConstitutiveRoleHistory run}
    (program : ConstitutiveNormalizerProgram roles)
    (authority : program.IsAuthoritative)
    (profile : StructuralObligation roles)
    (payload : StructuralAcceptedPayload roles profile) :
    interpretConstitutiveNormalizerProgram program profile payload =
      normalizeStructuralAcceptedPayload roles profile payload := by
  induction program with
  | nil => rfl
  | step headRole instruction tail inductionHypothesis =>
      change _ ∧ _ at authority
      cases profile with
      | mk choice rest =>
          cases choice with
          | false =>
              cases payload with
              | mk headPayload tailPayload =>
                  change
                    (interpretConstitutiveNormalizerInstruction _ instruction false
                        headPayload,
                      interpretConstitutiveNormalizerProgram tail rest tailPayload) =
                    (normalizeLocalAcceptedPayload _ false headPayload,
                      normalizeStructuralAcceptedPayload _ rest tailPayload)
                  exact Eq.trans
                    (congrArg
                      (fun headValue =>
                        (headValue,
                          interpretConstitutiveNormalizerProgram tail rest tailPayload))
                      (interpretAuthoritativeNormalizerInstruction_exact _ instruction
                        authority.1 false headPayload))
                    (congrArg
                      (fun tailValue =>
                        (normalizeLocalAcceptedPayload _ false headPayload, tailValue))
                      (inductionHypothesis authority.2 rest tailPayload))
          | true =>
              cases payload with
              | mk headPayload tailPayload =>
                  change
                    (interpretConstitutiveNormalizerInstruction _ instruction true
                        headPayload,
                      interpretConstitutiveNormalizerProgram tail rest tailPayload) =
                    (normalizeLocalAcceptedPayload _ true headPayload,
                      normalizeStructuralAcceptedPayload _ rest tailPayload)
                  exact Eq.trans
                    (congrArg
                      (fun headValue =>
                        (headValue,
                          interpretConstitutiveNormalizerProgram tail rest tailPayload))
                      (interpretAuthoritativeNormalizerInstruction_exact _ instruction
                        authority.1 true headPayload))
                    (congrArg
                      (fun tailValue =>
                        (normalizeLocalAcceptedPayload _ true headPayload, tailValue))
                      (inductionHypothesis authority.2 rest tailPayload))

end ConstitutiveSearch.EndogenousDecomposition

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.EndogenousDecomposition.ConstitutiveNormalizerInstruction
#print axioms ConstitutiveSearch.EndogenousDecomposition.ConstitutiveNormalizerInstruction.IsAuthoritative
#print axioms ConstitutiveSearch.EndogenousDecomposition.authoritativeNormalizerInstruction
#print axioms ConstitutiveSearch.EndogenousDecomposition.authoritativeNormalizerInstruction_code_exact
#print axioms ConstitutiveSearch.EndogenousDecomposition.authoritativeNormalizerInstruction_isAuthoritative
#print axioms ConstitutiveSearch.EndogenousDecomposition.leftPayloadAtScheduleSource
#print axioms ConstitutiveSearch.EndogenousDecomposition.scheduleTargetAsRetainedPayload
#print axioms ConstitutiveSearch.EndogenousDecomposition.scheduledSource_from_discovery_exact
#print axioms ConstitutiveSearch.EndogenousDecomposition.scheduledTarget_from_discovery_exact
#print axioms ConstitutiveSearch.EndogenousDecomposition.interpretConstitutiveNormalizerInstruction
#print axioms ConstitutiveSearch.EndogenousDecomposition.interpretConstitutiveNormalizerInstruction_false
#print axioms ConstitutiveSearch.EndogenousDecomposition.interpretConstitutiveNormalizerInstruction_true
#print axioms ConstitutiveSearch.EndogenousDecomposition.executedCode_map_eq_discoveredMap
#print axioms ConstitutiveSearch.EndogenousDecomposition.interpretAuthoritativeNormalizerInstruction_exact
#print axioms ConstitutiveSearch.EndogenousDecomposition.ConstitutiveNormalizerProgram
#print axioms ConstitutiveSearch.EndogenousDecomposition.buildConstitutiveNormalizerProgram
#print axioms ConstitutiveSearch.EndogenousDecomposition.buildConstitutiveNormalizerProgram_step
#print axioms ConstitutiveSearch.EndogenousDecomposition.ConstitutiveNormalizerProgram.codeSize
#print axioms ConstitutiveSearch.EndogenousDecomposition.buildConstitutiveNormalizerProgram_codeSize
#print axioms ConstitutiveSearch.EndogenousDecomposition.ConstitutiveNormalizerProgram.IsAuthoritative
#print axioms ConstitutiveSearch.EndogenousDecomposition.buildConstitutiveNormalizerProgram_isAuthoritative
#print axioms ConstitutiveSearch.EndogenousDecomposition.AuthoritativeConstitutiveNormalizerProgram
#print axioms ConstitutiveSearch.EndogenousDecomposition.buildAuthoritativeConstitutiveNormalizerProgram
#print axioms ConstitutiveSearch.EndogenousDecomposition.authoritativeNormalizerProgramReturnedCodes
#print axioms ConstitutiveSearch.EndogenousDecomposition.authoritativeNormalizerProgram_codeSize_eq_compiledLocalSize
#print axioms ConstitutiveSearch.EndogenousDecomposition.authoritativeNormalizerProgramReturnedCodes_exact
#print axioms ConstitutiveSearch.EndogenousDecomposition.authoritativeNormalizerProgram_compiledSize_eq_stageCount
#print axioms ConstitutiveSearch.EndogenousDecomposition.interpretConstitutiveNormalizerProgram
#print axioms ConstitutiveSearch.EndogenousDecomposition.interpretAuthoritativeConstitutiveNormalizerProgram_exact
/- AXIOM_AUDIT_END -/
