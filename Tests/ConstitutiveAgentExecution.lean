import RelationalPerimeter
set_option genInjectivity false
set_option maxHeartbeats 2000000
namespace Tests.ConstitutiveAgentExecution
open ConstitutiveSearch.Agent ConstitutiveSearch.EndogenousDecomposition

theorem actual_output_registered (memory : Memory) :
    (step memory).1.register = memory.register ++
      [resumedTarget (LiveContinuation.produce memory.live)] := executed_step_register_exact memory

theorem admitted_obtain (memory : Memory) (handle var : Nat)
    (permission : ConstitutiveSearch.Resources.Ref memory.requirement.realizedScope var) :
    (executeInput memory (.obtain handle var)).2.message =
      .answer handle var (obtainedAuthorization memory handle var permission).1 :=
  obtain_produces_and_returns memory handle var permission

theorem obtain_exact_size (memory : Memory) (handle var : Nat)
    (permission : ConstitutiveSearch.Resources.Ref memory.requirement.realizedScope var)
    (missing : memory.register.length ≤ handle) :
    (executeInput memory (.obtain handle var)).1.register.length = handle + 1 :=
  obtain_register_exact memory handle var permission missing

theorem obtain_exact_work (memory : Memory) (handle var : Nat)
    (permission : ConstitutiveSearch.Resources.Ref memory.requirement.realizedScope var) :
    (executeInput memory (.obtain handle var)).2.productions.length = needed memory.register.length handle :=
  obtain_work_exact memory handle var permission

def every_target_has_produced_origin (target : AnswerTarget) :
    TargetOrigin target.root target.context target.continuation := target.origin

theorem every_target_criterion_is_derived (target : AnswerTarget) :
    ConstitutiveSearch.SAT.GeneratedStructuralBranchAccept target.context target.continuation :=
  target.origin.accepted

theorem entire_head_is_shared (memory : Memory) (request : Request) (rest : List Request) :
    executeRequests memory (request :: rest) =
      let head := executeProducedInput memory request
      let tail := executeRequests head.1.1 rest
      (tail.1, head.1.2 :: tail.2) := executeRequests_head_entire memory request rest

theorem refusal_has_no_state_effect (memory : Memory) (request : Request) (handle var : Nat) (reason : Refusal)
    (refused : (executeInput memory request).2.message = .refused handle var reason) :
    (executeInput memory request).1 = memory := refusal_preserves_memory memory request handle var reason refused

theorem stable_old_handles (count : Nat) (memory : Memory) (handle var : Nat)
    (within : handle < memory.register.length) :
    readRegister (runSteps count memory).1.register handle var = readRegister memory.register handle var :=
  runSteps_old_read count memory handle var within

theorem same_head_different_future (memory : Memory) (request : Request) (one two : List Request) :
    (executeRequests memory (request :: one)).2.head? =
      (executeRequests memory (request :: two)).2.head? := head_horizon_independent memory request one two

theorem cached_obtain_does_not_replay (memory : Memory) (handle var : Nat)
    (within : handle < memory.register.length) :
    (executeInput memory (.obtain handle var)).2.productions = [] :=
  cached_obtain_runs_no_stage memory handle var within

theorem every_future_preserves_old_read (memory : Memory) (requests : List Request) (handle var : Nat)
    (within : handle < memory.register.length) :
    readRegister (executeRequests memory requests).1.register handle var = readRegister memory.register handle var :=
  all_future_old_reads memory requests handle var within

def scenario : List Request := [.inspect 0 0, .obtain 2 0, .inspect 2 0,
  .inspect 200 0, .inspect 0 1, .advance 1]

-- Forces both creation of missing targets and subsequent reuse without a run.
#eval (publicAgent 0 [0] [false]).map fun session =>
  let result := session.executeAll scenario
  (result.1.memory.register.length,
    result.2.map (fun event => (event.productions.length, event.message)))

-- Both proposals are made from the value actually returned by an inspection.
#eval (publicAgent 0 [0] [false]).map fun session =>
  match (session.execute (.inspect 0 0)).2.message with
  | .answer _ _ value =>
      ((session.execute (.propose 0 0 value)).2.message,
       (session.execute (.propose 0 0 (!value))).2.message)
  | other => (other, other)

end Tests.ConstitutiveAgentExecution
/- AXIOM_AUDIT_BEGIN -/
#print axioms Tests.ConstitutiveAgentExecution.actual_output_registered
#print axioms Tests.ConstitutiveAgentExecution.admitted_obtain
#print axioms Tests.ConstitutiveAgentExecution.obtain_exact_size
#print axioms Tests.ConstitutiveAgentExecution.obtain_exact_work
#print axioms Tests.ConstitutiveAgentExecution.every_target_has_produced_origin
#print axioms Tests.ConstitutiveAgentExecution.every_target_criterion_is_derived
#print axioms Tests.ConstitutiveAgentExecution.entire_head_is_shared
#print axioms Tests.ConstitutiveAgentExecution.refusal_has_no_state_effect
#print axioms Tests.ConstitutiveAgentExecution.stable_old_handles
#print axioms Tests.ConstitutiveAgentExecution.same_head_different_future
#print axioms Tests.ConstitutiveAgentExecution.cached_obtain_does_not_replay
#print axioms Tests.ConstitutiveAgentExecution.every_future_preserves_old_read
#print axioms Tests.ConstitutiveAgentExecution.scenario
/- AXIOM_AUDIT_END -/
