#!/usr/bin/env python3
"""Named C guards for actual routing evaluation and complete stage preservation.
Textual mutation fixtures exercise these guards; they are not corrupt compiled
executions. Deferred map/Assignment applications and bound bootstraps are open.
"""
from pathlib import Path
import re
import runpy
import sys
sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parent.parent
BASE = 'Agent_Local_Documentary_'
NATIVE_SUFFIXES = (
    'ConstitutiveSearch_AcceptedFrontierCode_eval',
    'ConstitutiveSearch_FrontierCompletion_absorbFirstIntoSecond',
    'ConstitutiveSearch_FrontierCompletion_absorbSecondIntoFirst',
    'ConstitutiveSearch_ContinuationTransport_trans',
    'ConstitutiveSearch_AcceptingContinuationTransport_trans',
    'ConstitutiveSearch_SAT_Assignment_flipAt',
    'ConstitutiveSearch_AcceptedIrreducibleFrontierReduction_preservation',
    'ConstitutiveSearch_Agent_Local_Documentary_Master_Stage_preservation',
    'ConstitutiveSearch_SAT_GeneratedStructuralFlipAtRelation_toAcceptingTransport',
    'ConstitutiveSearch_SAT_GeneratedStructuralFlipAtRelation_mapContinuation',
    'ConstitutiveSearch_SAT_generatedStructuralFlipAtAction',
    'ConstitutiveSearch_normalizeAcceptedFrontier',
    'ConstitutiveSearch_SAT_normalizeGeneratedStructuralFrontierByFlip',
    'ConstitutiveSearch_SAT_generatedStructuralFlipAtSearch',
    'ConstitutiveSearch_Agent_Local_Documentary_Control_execute',
    'ConstitutiveSearch_Agent_Local_Documentary_Control_runCtl',
) + tuple('ConstitutiveSearch_AcceptedFrontierPreservation_' + name for name in
          ('identity', 'swapFirstTwo', 'prepend', 'trans', 'absorbFirstIntoSecond', 'absorbSecondIntoFirst')) + tuple(
          'ConstitutiveSearch_AcceptingFrontierTransport_' + name for name in
          ('identity', 'swapFirstTwo', 'prepend', 'trans', 'absorbFirstIntoSecond', 'absorbSecondIntoFirst'))
# Reject producer references as well as calls, including closure addresses.
NATIVE = r'\b\w*(?:' + '|'.join(map(re.escape, NATIVE_SUFFIXES)) + r')(?:___\w+)?\b'


def make_check(functions, select):
    scope = [name for name in functions if not name.endswith('___boxed') and 'closed__' not in name and (
        BASE + 'ControlFrontierEvaluation_' in name or BASE + 'ControlStagePreservation_' in name or
        BASE + 'ControlCompletion_expandedDecideCode' in name or BASE + 'ControlCompletion_expandedDecideBound' in name or
        BASE + 'ControlMaster_expandedRunCode' in name or
        re.search(BASE + r'ControlFrontierOpening_(?:identityCode|prependCode|transCode)(?:_|$)', name))]
    if not scope:
        raise ValueError('Routing evaluation compiled bodies missing')
    paths = (
        ('ControlFrontierEvaluation_swapCode___lam__0', r'lean_ctor_set\([^,]+, 0, v_forward_\d+_\)'),
        ('ControlFrontierEvaluation_swapCode___lam__0', r'lean_ctor_set\([^,]+, 1, v_backward_\d+_\)'),
        ('ControlFrontierEvaluation_swapCode___lam__1', r'lean_closure_set\(v_backward_\d+_, 1, v_second_\d+_\)'),
        ('ControlFrontierEvaluation_swapCode___lam__1', r'lean_closure_set\(v_backward_\d+_, 2, v_first_\d+_\)'),
        ('ControlFrontierEvaluation_swapCode___lam__2', r'lean_closure_set\(v_forward_\d+_, 1, v_first_\d+_\)'),
        ('ControlFrontierEvaluation_swapCode___lam__2', r'lean_closure_set\(v_forward_\d+_, 2, v_second_\d+_\)'),
        ('ControlFrontierEvaluation_transportCode___redArg', r'lean_closure_set\(v_map_\d+_, 0, v_selected_\d+_\)'),
        ('ControlFrontierEvaluation_transportCode___redArg___lam__0', r'lean_nat_dec_eq\(v___y_\d+_, v_selected_\d+_\)'),
        ('ControlFrontierEvaluation_transportCode___redArg___lam__0', r'lean_apply_1\(v_continuation_\d+_, v___y_\d+_\)'),
        ('ControlFrontierEvaluation_transportCode___redArg___lam__1', r'lean_ctor_set\([^,]+, 0, v_map_\d+_\)'),
        ('ControlFrontierEvaluation_absorbFirstCode___redArg___lam__1', r'lean_closure_set\(v_forward_\d+_, 5, v_transport_\d+_\)'),
        ('ControlFrontierEvaluation_absorbFirstCode___redArg___lam__1', r'lean_closure_set\([^,]+, 0, v_forward_\d+_\)'),
        ('ControlFrontierEvaluation_absorbFirstCode___redArg___lam__1', r'lean_closure_set\([^,]+, 1, v_backward_\d+_\)'),
        ('ControlFrontierEvaluation_absorbSecondCode___redArg___lam__3', r'lean_closure_set\(v_forward_\d+_, 5, v_transport_\d+_\)'),
        ('ControlFrontierEvaluation_absorbSecondCode___redArg___lam__3', r'lean_closure_set\([^,]+, 0, v_forward_\d+_\)'),
        ('ControlFrontierEvaluation_absorbSecondCode___redArg___lam__3', r'lean_closure_set\([^,]+, 1, v_backward_\d+_\)'),
        ('ControlFrontierEvaluation_absorbFirstFunction___redArg', r'lean_apply_1\(v_transport_\d+_, v_a_\d+_\)'),
        ('ControlFrontierEvaluation_absorbSecondFunction___redArg', r'lean_apply_1\(v_transport_\d+_, v_a_\d+_\)'),
        ('ControlFrontierEvaluation_code___redArg___lam__6', r'ControlFrontierEvaluation_absorbFirstCode___redArg\(v_first_\d+_, v_second_\d+_, v_rest_\d+_, v_transport_\d+_\)'),
        ('ControlFrontierEvaluation_code___redArg___lam__10', r'ControlFrontierEvaluation_absorbSecondCode___redArg\(v_first_\d+_, v_second_\d+_, v_rest_\d+_, v_transport_\d+_\)'),
        ('ControlFrontierEvaluation_code___redArg___lam__11', r'ControlFrontierOpening_prependCode___redArg\(v_head_\d+_, v_source_\d+_, v_target_\d+_, v_childPreservation_\d+_\)'),
        ('ControlFrontierEvaluation_code___redArg___lam__12', r'ControlFrontierEvaluation_code___redArg\(v_selected_\d+_, v_source_\d+_, v_code_\d+_\)'),
        ('ControlFrontierEvaluation_code___redArg___lam__15', r'ControlFrontierOpening_transCode___redArg\(v_firstPreservation_\d+_, v_secondPreservation_\d+_\)'),
        ('ControlFrontierEvaluation_code___redArg___lam__16', r'lean_closure_set\([^,]+, 0, v_firstPreservation_\d+_\)'),
        ('ControlFrontierEvaluation_code___redArg___lam__16', r'ControlFrontierEvaluation_code___redArg\(v_selected_\d+_, v_middle_\d+_, v_second_\d+_\)'),
        ('ControlFrontierEvaluation_code___redArg___lam__17', r'ControlFrontierEvaluation_code___redArg\(v_selected_\d+_, v_x_\d+_, v_first_\d+_\)'),
        ('ControlStagePreservation_code___redArg___lam__2', r'v_opening_\d+_ = lean_ctor_get\(v_stage_\d+_, 3\)'),
        ('ControlStagePreservation_code___redArg___lam__2', r'v_reduction_\d+_ = lean_ctor_get\(v_stage_\d+_, 4\)'),
        ('ControlStagePreservation_code___redArg___lam__2', r'v_preservation_\d+_ = lean_ctor_get\(v_opening_\d+_, 1\)'),
        ('ControlStagePreservation_code___redArg___lam__2', r'v_code_\d+_ = lean_ctor_get\(v_reduction_\d+_, 1\)'),
        ('ControlStagePreservation_code___redArg___lam__2', r'lean_closure_set\([^,]+, 0, v_preservation_\d+_\)'),
        ('ControlStagePreservation_code___redArg___lam__2', r'ControlFrontierEvaluation_code___redArg\(v___x_\d+_, v_frontier_\d+_, v_code_\d+_\)'),
        ('ControlStagePreservation_code___redArg___lam__1', r'ControlFrontierOpening_transCode___redArg\(v_preservation_\d+_, v_reduced_\d+_\)'),
        ('ControlStagePreservation_code___redArg___lam__0', r'lean_ctor_set\([^,]+, 0, v_composed_\d+_\)'),
        ('ControlFrontierOpening_transCode___redArg___lam__2', r'lean_ctor_set\([^,]+, 0, v_forward_\d+_\)'),
        ('ControlFrontierOpening_transCode___redArg___lam__2', r'lean_ctor_set\([^,]+, 1, v_backward_\d+_\)'),
        ('ControlCompletion_expandedDecideCode___redArg___lam__0', r'lean_closure_set\([^,]+, 0, v_actualPreservation_\d+_\)'),
        ('ControlCompletion_expandedDecideCode___redArg___lam__0', r'lean_closure_set\([^,]+, 1, v_input_\d+_\)'),
        ('ControlCompletion_expandedDecideCode___redArg___lam__0', r'lean_closure_set\([^,]+, 7, v_stage_\d+_\)'),
        ('ControlCompletion_expandedDecideCode___redArg___lam__1', r'ControlStagePreservation_code___redArg\(v_stage_\d+_\)'),
        ('ControlCompletion_expandedDecideCode___redArg___lam__3', r'v_forward_\d+_ = lean_ctor_get\(v_actualPreservation_\d+_, 0\)'),
        ('ControlCompletion_expandedDecideCode___redArg___lam__3', r'v_retained_\d+_ = lean_apply_1\(v_forward_\d+_, v_input_\d+_\)'),
        ('ControlCompletion_expandedDecideCode___redArg___lam__3', r'ControlCompletion_completeCode___redArg\(v_context_\d+_, v_sources_\d+_, v_demand_\d+_, v_left_\d+_, v_right_\d+_, v_stage_\d+_, v_memory_\d+_, v_retained_\d+_\)'),
        ('ControlMaster_expandedRunCode___lam__2', r'lean_closure_set\([^,]+, 0, v_actual_\d+_\)'),
        ('ControlMaster_expandedRunCode___lam__2', r'ControlCompletion_expandedDecideCode___redArg\(v_context_\d+_, v_sources_\d+_, v_demand_\d+_, v_left_\d+_, v_right_\d+_, v_actual_\d+_, v_memory_\d+_\)'),
    )
    paths = [(select(functions, BASE + suffix), pattern) for suffix, pattern in paths]
    ordered = [select(functions, BASE + 'ControlFrontierOpening_transCode___redArg___lam__' + str(n)) for n in (0, 1)]
    consumers = [name for name in scope if BASE + 'ControlCompletion_expandedDecideCode' in name]
    entry = select(functions, BASE + 'ControlStagePreservation_code___redArg')
    owners = [name for name in consumers if re.search(re.escape(entry) + r'\s*\(', functions[name])]
    if len(owners) != 1:
        raise ValueError('Expected one actual Stage consumer')
    owner = owners[0]
    master_consumers = [name for name in scope if BASE + 'ControlMaster_expandedRunCode' in name]
    decide = select(functions, BASE + 'ControlCompletion_expandedDecideCode___redArg')
    master_owners = [name for name in master_consumers if re.search(re.escape(decide) + r'\s*\(', functions[name])]
    if len(master_owners) != 1:
        raise ValueError('Expected one actual expanded decision consumer')
    master_owner = master_owners[0]

    def check(current):
        for name in scope:
            if re.search(NATIVE, current[name]):
                raise ValueError('Native preservation producer replayed: ' + name)
        for names, target, original_owner in ((consumers, entry, owner), (master_consumers, decide, master_owner)):
            if sum(len(re.findall(re.escape(target) + r'\s*\(', current[name])) for name in names) != 1 or not re.search(
                    re.escape(target) + r'\s*\(', current[original_owner]):
                raise ValueError('Actual controlled consumer omitted or duplicated')
        for name, pattern in paths:
            if not re.search(pattern, current[name]):
                raise ValueError('Actual preservation data path dropped: ' + name)
        for name, directions in zip(ordered, (('left', 'right', 'backward'), ('right', 'left', 'forward'))):
            body = current[name]
            field = '1' if directions[2] == 'backward' else '0'
            outer = re.search(r'(v_\w+) = lean_ctor_get\(v_' + directions[0] + r'_\d+_, ' + field + r'\)', body)
            inner = re.search(r'(v_\w+) = lean_ctor_get\(v_' + directions[1] + r'_\d+_, ' + field + r'\)', body)
            applied = re.search(r'(v_\w+) = lean_apply_1\(' + re.escape(inner[1]) + r', v_continuation_\d+_\)', body) if inner else None
            if not outer or not inner or not applied or not re.search(
                    r'lean_apply_1\(' + re.escape(outer[1]) + ', ' + re.escape(applied[1]) + r'\)', body):
                raise ValueError('Actual forward/backward composition order lost: ' + name)

    mutations = [(name, functions[name] + ' lp_forbidden_' + suffix + '();') for name in scope for suffix in NATIVE_SUFFIXES]
    mutations.extend((name, re.sub(pattern, 'lp_dropped_data_path', functions[name])) for name, pattern in paths)
    for original_owner, entry_point in ((owner, entry), (master_owner, decide)):
        mutations.extend(((original_owner, functions[original_owner] + entry_point + '();'),
                          (original_owner, functions[original_owner].replace(entry_point, 'lp_substituted_producer'))))
    for name in ordered:
        mutations.append((name, re.sub(r'lean_apply_1\(v_\w+, v___x_\d+_\)', 'lp_substituted_order()', functions[name])))
    for name, field in zip(ordered, ('1', '0')):
        mutations.append((name, re.sub(r'(lean_ctor_get\(v_(?:left|right)_\d+_, )' + field + r'(\))',
                                      r'\g<1>' + ('0' if field == '1' else '1') + r'\g<2>', functions[name])))
    return check, mutations, scope


def main():
    agent = runpy.run_path(str(ROOT / 'scripts/check-agent-codegen.py'))
    functions = {}
    for path in sorted((ROOT / '.lake/build/ir').rglob('*.c')):
        functions.update(agent['bodies_with_objects'](path.read_text(encoding='utf-8')))
    check, mutations, scope = make_check(functions, agent['shared']['select'])
    check(functions)
    for name, body in mutations:
        current = dict(functions)
        current[name] = body
        try:
            check(current)
        except ValueError:
            pass
        else:
            raise ValueError('Routing evaluation mutation accepted: ' + name)
    print('DOCUMENTARY_FRONTIER_EVALUATION_CODEGEN_OK: ' + str(len(mutations)) +
          ' textual mutations rejected; no native preservation producer references in ' + str(len(scope)) +
          ' named bodies; actual recursive packets, both maps, ordered composition and whole same Stage; '
          'unique expanded consumers; deferred invocations and bootstrap costs remain open')

if __name__ == '__main__':
    try:
        main()
    except (OSError, ValueError, KeyError) as error:
        print('DOCUMENTARY_FRONTIER_EVALUATION_CODEGEN_ERROR: ' + str(error), file=sys.stderr)
        sys.exit(1)
