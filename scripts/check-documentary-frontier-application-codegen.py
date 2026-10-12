#!/usr/bin/env python3
"""Named compiled paths of executable transports and their actual consumers.
Textual mutations exercise this checker; they are not corrupted executions.
The ordinary exported Assignment closure is a readout boundary. Effective
queries use the attached paid Reader. Boxing, bootstrap and physical costs are open.
"""
from pathlib import Path
import re
import runpy
import sys
sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parent.parent
BASE = 'Agent_Local_Documentary_'

def make_check(functions, select):
    previous = runpy.run_path(str(ROOT / 'scripts/check-documentary-frontier-evaluation-codegen.py'))
    native_suffixes = previous['NATIVE_SUFFIXES']
    native = previous['NATIVE']
    expanded = runpy.run_path(str(ROOT / 'scripts/check-documentary-expanded-control-codegen.py'))
    obsolete_suffixes = tuple(BASE + name for name in (
        'ControlCompletion_assignmentCode','ControlCompletion_expandedDecideCode','ControlCompletion_completeCode',
        'ControlMaster_expandedSearchCode','ControlFrontierOpening_code','ControlFrontierEvaluation_code','ControlStagePreservation_code'))
    obsolete = r'\b\w*(?:' + '|'.join(map(re.escape,obsolete_suffixes)) + r')(?:___redArg)?\s*\('
    scope = [name for name in functions if not name.endswith('___boxed') and (
        'closed__' not in name or
        (name.startswith('_init_') and name.endswith('ControlSeedApplication_code___redArg___lam__6___closed__0'))) and (
        BASE + 'ControlFrontierApplication_' in name or
        BASE + 'ControlFrontierExecutableEvaluation_' in name or
        BASE + 'ControlFrontierExecutableOpening_' in name or
        BASE + 'ControlStageExecution_' in name or
        BASE + 'ControlSeedApplication_' in name or
        BASE + 'ControlMaster_executable' in name or
        BASE + 'ControlMaster_expandedRunCode' in name or
        BASE + 'ControlCompletion_executed' in name)]
    if not scope:
        raise ValueError('Executable routing compiled bodies missing')
    paths = [
        ('ControlFrontierApplication_forwardCode___redArg', r'lean_ctor_get\(v_execution_\d+_, 5\)'),
        ('ControlFrontierApplication_backwardCode___redArg', r'lean_ctor_get\(v_execution_\d+_, 6\)'),
        ('ControlFrontierApplication_forwardCode___redArg', r'lean_apply_4\(v_forward_\d+_, v_input_\d+_, v___x_\d+_, v_reader_\d+_, lean_box\(0\)\)'),
        ('ControlFrontierApplication_backwardCode___redArg', r'lean_apply_4\(v_backward_\d+_, v_input_\d+_, v___x_\d+_, v_reader_\d+_, lean_box\(0\)\)'),
        ('ControlFrontierApplication_transForward___redArg___lam__3', r'lean_ctor_get\(v_left_\d+_, 5\)'),
        ('ControlFrontierApplication_transForward___redArg___lam__3', r'lean_apply_4\(v_forward_\d+_, v_input_\d+_, v_budget_\d+_, v_reader_\d+_, lean_box\(0\)\)'),
        ('ControlFrontierApplication_transForward___redArg___lam__2', r'lean_ctor_get\(v_right_\d+_, 5\)'),
        ('ControlFrontierApplication_transForward___redArg___lam__2', r'lean_ctor_get\(v_first_\d+_, 0\)'),
        ('ControlFrontierApplication_transForward___redArg___lam__2', r'lean_ctor_get\(v_first_\d+_, 1\)'),
        ('ControlFrontierApplication_transForward___redArg___lam__2', r'lean_apply_4\(v_forward_\d+_, v_continuation_\d+_, v___x_\d+_, v_reader_\d+_, lean_box\(0\)\)'),
        ('ControlFrontierApplication_transBackward___redArg___lam__0', r'lean_ctor_get\(v_right_\d+_, 6\)'),
        ('ControlFrontierApplication_transBackward___redArg___lam__0', r'lean_apply_4\(v_backward_\d+_, v_input_\d+_, v_budget_\d+_, v_reader_\d+_, lean_box\(0\)\)'),
        ('ControlFrontierApplication_transBackward___redArg___lam__2', r'lean_ctor_get\(v_left_\d+_, 6\)'),
        ('ControlFrontierApplication_transBackward___redArg___lam__2', r'lean_ctor_get\(v_first_\d+_, 0\)'),
        ('ControlFrontierApplication_transBackward___redArg___lam__2', r'lean_ctor_get\(v_first_\d+_, 1\)'),
        ('ControlFrontierApplication_transBackward___redArg___lam__2', r'lean_apply_4\(v_backward_\d+_, v_continuation_\d+_, v___x_\d+_, v_reader_\d+_, lean_box\(0\)\)'),
        ('ControlFrontierApplication_prependForward___redArg___lam__3', r'lean_ctor_get\(v_child_\d+_, 5\)'),
        ('ControlFrontierApplication_prependForward___redArg___lam__0', r'lean_ctor_get\(v_output_\d+_, 0\)'),
        ('ControlFrontierApplication_prependForward___redArg___lam__0', r'lean_ctor_get\(v_output_\d+_, 1\)'),
        ('ControlFrontierApplication_flipContinuationCode___redArg___lam__2', r'ControlAssignmentApplication_flipReaderCode\(v_input_\d+_, v_selected_\d+_, v_reader_\d+_\)'),
        ('ControlFrontierApplication_flipContinuationCode___redArg___lam__1', r'lean_ctor_set\([^,]+, 0, v_assignment_\d+_\)'),
        ('ControlFrontierApplication_flipContinuationCode___redArg___lam__1', r'lean_ctor_set\([^,]+, 1, v_executable_\d+_\)'),
        ('ControlFrontierExecutableEvaluation_code___lam__8', r'ControlFrontierApplication_prependCode\([^;]*v_received_\d+_\)'),
        ('ControlFrontierExecutableEvaluation_code___lam__10', r'ControlFrontierApplication_transCode\([^;]*v_first_\d+_, v_second_\d+_\)'),
        ('ControlFrontierExecutableEvaluation_code___lam__4', r'lean_closure_set\([^,]+, 5, v_first_\d+_\)'),
        ('ControlFrontierExecutableEvaluation_code___lam__4', r'ControlFrontierExecutableEvaluation_code\([^;]*v_middle_\d+_, v_x_\d+_, v_second_\d+_\)'),
        ('ControlFrontierExecutableEvaluation_code___lam__9', r'ControlFrontierExecutableEvaluation_code\([^;]*v_x_\d+_, v_middle_\d+_, v_first_\d+_\)'),
        ('ControlFrontierApplication_expandForward___redArg___lam__6', r'lean_ctor_get\(v_reader_\d+_, 0\)'),
        ('ControlFrontierApplication_expandForward___redArg___lam__6', r'lean_apply_1\(v_readCode_\d+_, v_selected_\d+_\)'),
        ('ControlFrontierApplication_expandForward___redArg', r'lean_closure_set\([^,]+, 2, v_right_\d+_\)'),
        ('ControlFrontierApplication_expandForward___redArg', r'lean_closure_set\([^,]+, 4, v_left_\d+_\)'),
        ('ControlFrontierApplication_expandForward___redArg___lam__3', r'= 116;'),
        ('ControlStageExecution_code___redArg___lam__2', r'lean_ctor_get\(v_stage_\d+_, 4\)'),
        ('ControlStageExecution_code___redArg___lam__2', r'lean_ctor_get\(v_reduction_\d+_, 1\)'),
        ('ControlStageExecution_code___redArg___lam__2', r'ControlFrontierExecutableEvaluation_code\([^;]*v_frontier_\d+_, v_retained_\d+_, v_code_\d+_\)'),
        ('ControlStageExecution_code___redArg___lam__2', r'lean_closure_set\([^,]+, 4, v_opening_\d+_\)'),
        ('ControlStageExecution_code___redArg___lam__1', r'ControlFrontierApplication_transCode\([^;]*v_opening_\d+_, v_reduced_\d+_\)'),
        ('ControlCompletion_executedCompleteCode___redArg', r'lean_ctor_get\(v_reader_\d+_, 0\)'),
        ('ControlCompletion_executedCompleteCode___redArg', r'lean_apply_1\(v_readCode_\d+_, v___x_\d+_\)'),
        ('ControlCompletion_executedCompleteCode___redArg___lam__6', r'lean_box\(v_bit_\d+_\)'),
        ('ControlCompletion_executedCompleteCode___redArg___lam__6', r'lean_closure_set\([^,]+, 3, v___x_\d+_\)'),
        ('ControlCompletion_executedCompleteCode___redArg___lam__6', r'lean_closure_set\([^,]+, 6, v_continuation_\d+_\)'),
        ('ControlCompletion_executedDecideCode___redArg___lam__1', r'lean_ctor_get\(v_payload_\d+_, 5\)'),
        ('ControlCompletion_executedDecideCode___redArg___lam__1', r'lean_apply_4\(v_forward_\d+_, v_input_\d+_, v___x_\d+_, v_reader_\d+_, lean_box\(0\)\)'),
        ('ControlCompletion_executedDecideCode___redArg___lam__2', r'lean_ctor_get\(v_applied_\d+_, 0\)'),
        ('ControlCompletion_executedDecideCode___redArg___lam__2', r'lean_ctor_get\(v_applied_\d+_, 1\)'),
        ('ControlCompletion_executedDecideCode___redArg___lam__2', r'ControlCompletion_executedCompleteCode___redArg\([^;]*v_continuation_\d+_, v_reader_\d+_\)'),
        ('ControlCompletion_executedDecideCode___redArg___lam__3', r'lean_ctor_get\(v_produced_\d+_, 0\)'),
        ('ControlCompletion_executedDecideCode___redArg___lam__3', r'lean_ctor_get\(v_produced_\d+_, 1\)'),
        ('ControlSeedApplication_code___redArg___lam__3', r'ControlAssignmentApplication_constantReaderCode\(v_right_\d+_\)'),
        ('ControlMaster_executableSearchCode___lam__5', r'lean_ctor_get\(v_producedOpening_\d+_, 0\)'),
        ('ControlMaster_executableSearchCode___lam__5', r'lean_ctor_get\(v_producedOpening_\d+_, 1\)'),
        ('ControlMaster_executableSearchCode___lam__5', r'lean_closure_set\([^,]+, 3, v_opening_\d+_\)'),
        ('ControlMaster_executableSearchCode___lam__5', r'lean_closure_set\([^,]+, 4, v_execution_\d+_\)'),
        ('ControlMaster_executableSearchCode___lam__4', r'lean_ctor_get\(v_opening_\d+_, 0\)'),
        ('ControlMaster_executableSearchCode___lam__4', r'ControlFrontierNormalization_code___redArg\(v___x_\d+_, v_frontier_\d+_\)'),
        ('ControlMaster_executableSearchCode___lam__2', r'lean_ctor_set\(v_stage_\d+_, 3, v_opening_\d+_\)'),
        ('ControlMaster_executableSearchCode___lam__2', r'lean_ctor_set\(v_stage_\d+_, 4, v_actualReduction_\d+_\)'),
        ('ControlMaster_executableSearchCode___lam__2', r'ControlStageExecution_code___redArg\(v_stage_\d+_, v_execution_\d+_\)'),
        ('ControlMaster_executableSearchCode___lam__0', r'lean_ctor_set\([^,]+, 0, v_stage_\d+_\)'),
        ('ControlMaster_executableSearchCode___lam__0', r'lean_ctor_set\([^,]+, 1, v_payload_\d+_\)'),
        ('ControlMaster_expandedRunCode___lam__2', r'lean_ctor_get\(v_actual_\d+_, 0\)'),
        ('ControlMaster_expandedRunCode___lam__2', r'lean_ctor_get\(v_actual_\d+_, 1\)'),
        ('ControlMaster_expandedRunCode___lam__2', r'ControlCompletion_executedDecideCode___redArg\([^;]*v_stage_\d+_, v_memory_\d+_, v_payload_\d+_\)'),
    ]
    paths = [(select(functions, BASE + suffix), pattern) for suffix,pattern in paths]
    backward_scope = [name for name in scope if re.search(r'ControlFrontierApplication_absorb(?:First|Second)Backward(?:_|$)', name)]
    if not backward_scope:
        raise ValueError('Absorption backward inclusions missing')
    forbidden_back = r'Control(?:FrontierApplication_flipContinuationCode|AssignmentApplication_(?:flipReaderCode|flipReadCode|flippedReader|constantReaderCode))'
    edge_rules = [
        ('ControlFrontierExecutableEvaluation_code', 'ControlFrontierApplication_' + operator, 1)
        for operator in ('identityCode','swapCode','absorbFirstCode','absorbSecondCode','prependCode','transCode')]
    edge_rules += [
        ('ControlFrontierExecutableOpening_code','ControlFrontierOpening_childCode',2),
        ('ControlFrontierExecutableOpening_code','ControlFrontierOpening_freshnessCode',1),
        ('ControlFrontierExecutableOpening_code','ControlFrontierOpening_splitCode',1),
        ('ControlFrontierExecutableOpening_code','ControlFrontierApplication_expandCode',1),
        ('ControlFrontierExecutableOpening_code','ControlFrontierApplication_transCode',1),
        ('ControlFrontierApplication_identityCode','ControlFrontierOpening_identityCode',1),
        ('ControlFrontierApplication_swapCode','ControlFrontierEvaluation_swapCode',1),
        ('ControlFrontierApplication_absorbFirstCode','ControlFrontierEvaluation_transportCode',1),
        ('ControlFrontierApplication_absorbSecondCode','ControlFrontierEvaluation_transportCode',1),
        ('ControlFrontierApplication_flipContinuationCode','ControlAssignmentApplication_flipReaderCode',1),
        ('ControlStageExecution_code','ControlFrontierExecutableEvaluation_code',1),
        ('ControlStageExecution_code','ControlFrontierApplication_transCode',1),
        # One paid Code is cached for both false-reader branches; its named
        # initializer is included above, together with the dynamic true site.
        ('ControlSeedApplication_code','ControlAssignmentApplication_constantReaderCode',2),
        ('ControlCompletion_executedDecideCode','ControlSeedApplication_code',1),
        ('ControlCompletion_executedDecideCode','ControlCompletion_executedCompleteCode',1),
        ('ControlMaster_executableSearchCode','ControlMasterHead_code',1),
        ('ControlMaster_executableSearchCode','ControlFrontierExecutableOpening_code',1),
        ('ControlMaster_executableSearchCode','ControlFrontierNormalization_code',1),
        ('ControlMaster_executableSearchCode','ControlStageExecution_code',1),
        ('ControlMaster_expandedRunCode','ControlMaster_executableSearchCode',1),
        ('ControlMaster_expandedRunCode','ControlCompletion_executedDecideCode',1),
    ]
    edges = []
    for caller,callee,expected in edge_rules:
        owners = [name for name in scope if BASE + caller in name]
        pattern = r'\b\w*' + re.escape(BASE + callee) + r'(?:___redArg)?\s*\('
        if not owners:
            raise ValueError('Executable consumer missing: ' + caller)
        edges.append((owners,pattern,expected))

    def check(current):
        for name in scope:
            if re.search(native, current[name]) or re.search(obsolete,current[name]) or re.search(expanded['FORBIDDEN'],current[name]) or re.search(expanded['OPENING_NATIVE'],current[name]):
                raise ValueError('Native routing producer replayed: ' + name)
        for name,pattern in paths:
            if not re.search(pattern,current[name]):
                raise ValueError('Actual routing/reader path dropped: ' + name)
        for name in backward_scope:
            if re.search(forbidden_back,current[name]):
                raise ValueError('Absorption inclusion replaced by reader reconstruction or inverse flip: ' + name)
        for owners,pattern,expected in edges:
            if sum(len(re.findall(pattern,current[name])) for name in owners) != expected:
                raise ValueError('Actual paid producer/consumer omitted or duplicated: ' + pattern)

    mutations = [(name,functions[name] + ' lp_forbidden_' + suffix + '();')
                 for name in scope for suffix in native_suffixes + obsolete_suffixes]
    mutations += [(name,re.sub(pattern,'lp_dropped_actual_path',functions[name])) for name,pattern in paths]
    mutations += [(name,functions[name] + ' lp_ControlFrontierApplication_flipContinuationCode();') for name in backward_scope]
    for owners,pattern,_ in edges:
        for name in owners:
            matches = list(re.finditer(pattern,functions[name]))
            if matches:
                mutations.append((name,re.sub(pattern,'lp_dropped_unique_edge(',functions[name])))
                mutations.append((name,functions[name] + matches[0].group() + ');'))
    return check,mutations,scope

def main():
    agent = runpy.run_path(str(ROOT / 'scripts/check-agent-codegen.py'))
    functions = {}
    for path in sorted((ROOT / '.lake/build/ir').rglob('*.c')):
        functions.update(agent['bodies_with_objects'](path.read_text(encoding='utf-8')))
    check,mutations,scope = make_check(functions,agent['shared']['select'])
    check(functions)
    for name,body in mutations:
        current = dict(functions)
        current[name] = body
        try:
            check(current)
        except ValueError:
            pass
        else:
            raise ValueError('Executable routing textual mutation accepted: ' + name)
    print('DOCUMENTARY_FRONTIER_APPLICATION_CODEGEN_OK: ' + str(len(mutations)) +
          ' textual mutations rejected in ' + str(len(scope)) +
          ' named bodies; actual payload directions and ordered child readers; '
          'backward absorption by inclusion; bootstrap and physical costs remain open')

if __name__ == '__main__':
    try:
        main()
    except (OSError,ValueError,KeyError) as error:
        print('DOCUMENTARY_FRONTIER_APPLICATION_CODEGEN_ERROR: ' + str(error),file=sys.stderr)
        sys.exit(1)
