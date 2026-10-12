#!/usr/bin/env python3
"""Guard the paid ceiling payloads and their actual documentary consumers.

Whole original functions remain data. These named C checks distinguish their
stored fields from the realized executors, actual Nat ceilings and Readers
consumed by compositions and completion. They supplement the complete reviewed
runtime inventory and Lean laws; mutations are textual fixtures, not binaries.
"""
from pathlib import Path
import re
import runpy
import sys

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parent.parent
BASE = 'ConstitutiveSearch_Agent_Local_Documentary_'
V = r'v_\w+'


def make_max_stack_check(functions, select, parameters):
    """Five max producer bodies; the shared Arithmetic return graph is checked separately.

    Only the paid Cell callback examines both received naturals. Its native
    reconstruction in the right-zero case is predecessor-left plus one, not a
    whole-input maximum. The positive allocation callback constructs one Unit
    cons and descends directly with the two actual predecessors.
    """
    suffixes = {
        'wrapper': 'ControlReaderCeiling_maxCode',
        'factory': 'ControlReaderCeiling_descendMax',
        'boxed': 'ControlReaderCeiling_descendMax___lam__1___boxed',
        'cell': 'ControlReaderCeiling_descendMax___lam__1',
        'push': 'ControlReaderCeiling_descendMax___lam__0',
    }
    names = {key: select(functions, BASE + suffix) for key, suffix in suffixes.items()}
    returns = select(functions, BASE + 'ControlArithmetic_returns')
    arities = {'wrapper': 2, 'factory': 3, 'boxed': 4, 'cell': 4, 'push': 4}
    p = {key: parameters[name] for key, name in names.items()}
    for key, arity in arities.items():
        if len(p[key]) != arity:
            raise ValueError('Changed max-stack arity: ' + key)
    references = {'wrapper': {names['factory']}, 'factory': {names['boxed']},
                  'boxed': {names['cell']}, 'cell': {returns, names['push']},
                  'push': {names['factory']}}
    calls = {'wrapper': [names['factory']], 'factory': [], 'boxed': [names['cell']],
             'cell': [returns, returns], 'push': [names['factory']]}
    primitive_counts = {
        'wrapper': {'lean_box': 1},
        'factory': {'lean_alloc_closure': 1, 'lean_closure_set': 3, 'lean_box': 1,
                    'lean_alloc_ctor': 1, 'lean_ctor_set': 2},
        'boxed': {'lean_dec': 1},
        'cell': {'lean_unsigned_to_nat': 2, 'lean_nat_dec_eq': 2, 'lean_nat_sub': 2,
                 'lean_nat_add': 1, 'lean_dec': 3, 'lean_alloc_closure': 1,
                 'lean_closure_set': 3, 'lean_alloc_ctor': 1, 'lean_ctor_set': 2,
                 'lean_ctor_set_uint8': 1, 'sizeof': 1},
        'push': {'lean_box': 1, 'lean_alloc_ctor': 1, 'lean_ctor_set': 2},
    }
    assignment_counts = {'wrapper': 2, 'factory': 4, 'boxed': 1, 'cell': 12, 'push': 3}
    sensitive = re.compile(r'\b(?:lean_apply\w*|\w*Control_Code_bind\w*|'
                           r'\w*ControlNaturalStackAgreement\w*|\w*historical\w*|'
                           r'\w*Control(?:ReaderCeiling|Arithmetic)_\w*__trace\w*|'
                           r'\w*ControlArithmetic_businessLabels\w*|'
                           r'\w*(?:List_length|Nat_max|Nat_min)\w*)\b')
    required, ownership, orderings, closure_last_capture = [], [], [], {}

    def rule(key, pattern):
        required.append((names[key], pattern))

    def owned(key, pattern, count=1):
        ownership.append((names[key], pattern, count))

    def assignment(key, expression):
        match = re.search(r'(\w+) = ' + expression + r';', functions[names[key]])
        if match is None:
            raise ValueError('Received max-stack assignment missing: ' + key + '/' + expression)
        rule(key, re.escape(match[0]))
        return match

    def returned(key, callee, arguments):
        match = assignment(key, re.escape(callee) + r'\(' + ', '.join(map(re.escape, arguments)) + r'\)')
        rule(key, r'\breturn ' + re.escape(match[1]) + r';')
        orderings.append((names[key], re.escape(match[0]), r'\breturn ' + re.escape(match[1]) + r';'))
        return match

    def closure(key, callee, captures):
        match = assignment(key, r'lean_alloc_closure\(\(void\*\)\(' + re.escape(callee) + r'\), 4, 3\)')
        for slot, value in enumerate(captures):
            rule(key, r'lean_closure_set\(' + re.escape(match[1]) + ', ' + str(slot) + ', ' + re.escape(value) + r'\);')
        orderings.append((names[key], re.escape(match[0]),
                          *(r'lean_closure_set\(' + re.escape(match[1]) + ', ' + str(slot) + ', ' +
                            re.escape(value) + r'\);' for slot, value in enumerate(captures))))
        closure_last_capture[match[1]] = (r'lean_closure_set\(' + re.escape(match[1]) + ', ' +
                                         str(len(captures) - 1) + ', ' + re.escape(captures[-1]) + r'\);')
        return match[1]

    nil = assignment('wrapper', r'lean_box\(0\)')
    entry = returned('wrapper', names['factory'], [p['wrapper'][0], p['wrapper'][1], nil[1]])
    orderings.append((names['wrapper'], re.escape(nil[0]), re.escape(entry[0])))
    callback = closure('factory', names['boxed'], p['factory'])
    tag = assignment('factory', '17')
    boxed = assignment('factory', r'lean_box\(' + re.escape(tag[1]) + r'\)')
    step = assignment('factory', r'lean_alloc_ctor\(1, 2, 0\)')
    rule('factory', r'lean_ctor_set\(' + re.escape(step[1]) + ', 0, ' + re.escape(boxed[1]) + r'\);')
    rule('factory', r'lean_ctor_set\(' + re.escape(step[1]) + ', 1, ' + re.escape(callback) + r'\);')
    rule('factory', r'\breturn ' + re.escape(step[1]) + r';')
    orderings.append((names['factory'], closure_last_capture[callback], re.escape(tag[0]),
                      re.escape(boxed[0]), re.escape(step[0]),
                      r'lean_ctor_set\(' + re.escape(step[1]) + ', 0, ' + re.escape(boxed[1]) + r'\);',
                      r'lean_ctor_set\(' + re.escape(step[1]) + ', 1, ' + re.escape(callback) + r'\);',
                      r'\breturn ' + re.escape(step[1]) + r';'))
    cell_result = returned('boxed', names['cell'], p['boxed'])
    left_release = r'lean_dec\(' + re.escape(p['boxed'][0]) + r'\);'
    owned('boxed', left_release)
    orderings.append((names['boxed'], re.escape(cell_result[0]), left_release,
                      r'\breturn ' + re.escape(cell_result[1]) + r';'))
    zero = assignment('cell', r'lean_unsigned_to_nat\(0u\)')
    one = assignment('cell', r'lean_unsigned_to_nat\(1u\)')
    left_zero = assignment('cell', r'lean_nat_dec_eq\(' + re.escape(p['cell'][0]) + ', ' + re.escape(zero[1]) + r'\)')
    left_pred = assignment('cell', r'lean_nat_sub\(' + re.escape(p['cell'][0]) + ', ' + re.escape(one[1]) + r'\)')
    right_zero = assignment('cell', r'lean_nat_dec_eq\(' + re.escape(p['cell'][1]) + ', ' + re.escape(zero[1]) + r'\)')
    reconstructed = assignment('cell', r'lean_nat_add\(' + re.escape(left_pred[1]) + ', ' + re.escape(one[1]) + r'\)')
    right_pred = assignment('cell', r'lean_nat_sub\(' + re.escape(p['cell'][1]) + ', ' + re.escape(one[1]) + r'\)')
    owned('cell', r'lean_dec\(' + re.escape(p['cell'][1]) + r'\);', 2)
    owned('cell', r'lean_dec\(' + re.escape(left_pred[1]) + r'\);')
    left_base = returned('cell', returns, [p['cell'][1], p['cell'][2]])
    right_base = returned('cell', returns, [reconstructed[1], p['cell'][2]])
    orderings.append((names['cell'], re.escape(zero[0]), re.escape(left_zero[0]),
                      r'if \(' + re.escape(left_zero[1]) + r' == 1\)'))
    orderings.append((names['cell'], re.escape(one[0]), re.escape(left_pred[0]), re.escape(right_zero[0]),
                      r'if \(' + re.escape(right_zero[1]) + r' == 1\)'))
    rule('cell', r'if \(' + re.escape(left_zero[1]) + r' == 1\)\s*\{\s*lean_object\* ' +
         re.escape(left_base[1]) + r';\s*' + re.escape(left_base[0]) + r'\s*return ' +
         re.escape(left_base[1]) + r';\s*\}\s*else\s*\{[^{}]*' + re.escape(one[0]) + r'\s*' +
         re.escape(left_pred[0]) + r'\s*' + re.escape(right_zero[0]))
    rule('cell', r'if \(' + re.escape(right_zero[1]) + r' == 1\)\s*\{[^{}]*lean_dec\(' +
         re.escape(p['cell'][1]) + r'\);\s*' + re.escape(reconstructed[0]) + r'\s*lean_dec\(' +
         re.escape(left_pred[1]) + r'\);\s*' + re.escape(right_base[0]) + r'\s*return ' +
         re.escape(right_base[1]) + r';\s*\}\s*else\s*\{[^{}]*' + re.escape(right_pred[0]))
    allocation_callback = closure('cell', names['push'], [p['cell'][2], left_pred[1], right_pred[1]])
    rule('cell', re.escape(right_pred[0]) + r'\s*lean_dec\(' + re.escape(p['cell'][1]) + r'\);\s*' +
         re.escape(allocation_callback) + r' = lean_alloc_closure\(\(void\*\)\(' +
         re.escape(names['push']) + r'\), 4, 3\);')
    allocation_tag = assignment('cell', '6')
    allocation = assignment('cell', r'lean_alloc_ctor\(2, 2, 1\)')
    rule('cell', r'lean_ctor_set\(' + re.escape(allocation[1]) + ', 0, ' + re.escape(allocation_callback) + r'\);')
    rule('cell', r'lean_ctor_set\(' + re.escape(allocation[1]) + ', 1, ' + re.escape(zero[1]) + r'\);')
    rule('cell', r'lean_ctor_set_uint8\(' + re.escape(allocation[1]) +
         r', sizeof\(void\*\)\*2, ' + re.escape(allocation_tag[1]) + r'\);')
    rule('cell', r'\breturn ' + re.escape(allocation[1]) + r';')
    orderings.append((names['cell'], closure_last_capture[allocation_callback], re.escape(allocation_tag[0]),
                      re.escape(allocation[0]),
                      r'lean_ctor_set\(' + re.escape(allocation[1]) + ', 0, ' + re.escape(allocation_callback) + r'\);',
                      r'lean_ctor_set\(' + re.escape(allocation[1]) + ', 1, ' + re.escape(zero[1]) + r'\);',
                      r'lean_ctor_set_uint8\(' + re.escape(allocation[1]) + r', sizeof\(void\*\)\*2, ' +
                      re.escape(allocation_tag[1]) + r'\);', r'\breturn ' + re.escape(allocation[1]) + r';'))
    unit = assignment('push', r'lean_box\(0\)')
    cons = assignment('push', r'lean_alloc_ctor\(1, 2, 0\)')
    rule('push', r'lean_ctor_set\(' + re.escape(cons[1]) + ', 0, ' + re.escape(unit[1]) + r'\);')
    tail_write = r'lean_ctor_set\(' + re.escape(cons[1]) + ', 1, ' + re.escape(p['push'][0]) + r'\);'
    rule('push', tail_write)
    child = returned('push', names['factory'], [p['push'][1], p['push'][2], cons[1]])
    ordered = (re.escape(unit[0]), re.escape(cons[0]),
               r'lean_ctor_set\(' + re.escape(cons[1]) + ', 0, ' + re.escape(unit[1]) + r'\);',
               tail_write, re.escape(child[0]))
    orderings.append((names['push'], *ordered))

    def check(current):
        for key, name in names.items():
            body = current[name]
            assignments = re.findall(r'\b(v_\w+)\s*=(?!=)', body)
            if any(parameter in assignments for parameter in p[key]):
                raise ValueError('Max rebinds a received parameter: ' + key)
            if len(assignments) != assignment_counts[key] or len(set(assignments)) != len(assignments):
                raise ValueError('Max adds/drops/rebinds a received local assignment: ' + key)
            if sensitive.search(body):
                raise ValueError('Unpaid composition/expected ceiling/witness/historical dependency: ' + key)
            if set(re.findall(r'\b(?:l|lp)_\w+\b', body)) != references[key]:
                raise ValueError('Changed max-stack call/closure graph: ' + key)
            all_calls = re.findall(r'\b([A-Za-z_]\w*)\s*\(', body)
            project_calls = [callee for callee in all_calls if callee.startswith(('l_', 'lp_'))]
            if sorted(project_calls) != sorted(calls[key]):
                raise ValueError('Max callback invoked outside its paid closure: ' + key)
            actual_counts = {callee: all_calls.count(callee) for callee in set(all_calls)
                             if callee not in project_calls and callee != 'if'}
            if actual_counts != primitive_counts[key]:
                raise ValueError('Max adds/drops a received fixed construction or primitive: ' + key)
        for name, pattern in required:
            if len(re.findall(pattern, current[name])) != 1:
                raise ValueError('Max substitutes its actual inputs/predecessors/tail/paid node: ' + name + '/' + pattern)
        for name, pattern, count in ownership:
            if len(re.findall(pattern, current[name])) != count:
                raise ValueError('Max substitutes an actual ownership argument: ' + name + '/' + pattern)
        for name, *patterns in orderings:
            positions = [re.search(pattern, current[name]).start() for pattern in patterns]
            if positions != sorted(positions) or len(set(positions)) != len(positions):
                raise ValueError('Max descends/releases before its actual construction/callback: ' + name)

    def mutations():
        result = []
        for name, pattern in required:
            changed = re.sub(pattern, 'substituted_max_stack_777;', functions[name], count=1)
            if changed == functions[name]:
                raise ValueError('Empty max-stack requirement mutation')
            result.append((name, changed))
        for name, pattern, _ in ownership:
            for statement in re.finditer(pattern, functions[name]):
                changed_statement = re.sub(r'\([^)]*\)', '(v_substituted_refcount_777)', statement[0], count=1)
                result.append((name, functions[name][:statement.start()] + changed_statement + functions[name][statement.end():]))
        for key, name in names.items():
            for parameter in p[key]:
                result.append((name, parameter + ' = v_substituted_received_777;\n' + functions[name]))
            variables = set(re.findall(r'\b(v_\w+)\s*=(?!=)', functions[name]))
            for variable in sorted(variables):
                result.append((name, functions[name] + '\n' + variable + ' = v_substituted_local_777;'))
            result.append((name, functions[name] + '\nv_new_alias_777 = v_substituted_local_777;'))
        comparison_site = re.search(re.escape(left_zero[0]), functions[names['cell']])
        result.append((names['cell'], functions[names['cell']][:comparison_site.start()] +
                       p['cell'][0] + ' = ' + p['cell'][1] + ';\n' + functions[names['cell']][comparison_site.start():]))
        capture_site = re.search(r'lean_closure_set\(' + re.escape(allocation_callback) + ', 0, ' +
                                 re.escape(p['cell'][2]) + r'\);', functions[names['cell']])
        result.append((names['cell'], functions[names['cell']][:capture_site.start()] +
                       p['cell'][2] + ' = ' + p['cell'][1] + ';\n' + functions[names['cell']][capture_site.start():]))
        for key in ('wrapper', 'factory'):
            for early in ('lean_nat_dec_eq(x, y);', 'lean_obj_tag(x);', 'lean_ctor_get(x, 1);'):
                result.append((names[key], functions[names[key]] + early))
        for key, callee in (('factory', names['boxed']), ('cell', names['push'])):
            result.append((names[key], functions[names[key]] + callee + '(x, y, z, u);'))
        result.append((names['cell'], functions[names['cell']] + 'lean_alloc_ctor(1, 2, 0);'))
        for key in names:
            for forbidden in (BASE + 'Control_Code_bind___redArg(x, y);',
                              BASE + 'Control_Code_bindForward___redArg(x, y);',
                              'l_List_lengthTR___redArg(x);', 'lean_nat_max(x, y);',
                              'lean_nat_min(x, y);', BASE + 'ControlReaderCeiling_max__trace(x, y);',
                              BASE + 'ControlNaturalStackAgreement_historicalMaxCode(x, y);'):
                result.append((names[key], functions[names[key]] + forbidden))
        for key, before, after in (('factory', ' = 17;', ' = 18;'), ('cell', ' = 6;', ' = 3;'),
                                   ('wrapper', 'lean_box(0)', 'lean_box(1)'),
                                   ('push', 'lean_box(0)', 'lean_box(1)'),
                                   ('cell', 'lean_unsigned_to_nat(1u)', 'lean_unsigned_to_nat(2u)')):
            changed = functions[names[key]].replace(before, after, 1)
            if changed == functions[names[key]]:
                raise ValueError('Empty max-stack payment/constructor inversion')
            result.append((names[key], changed))
        for key, before, after in (('wrapper', p['wrapper'][0], p['wrapper'][1]),
                                   ('push', p['push'][2], p['push'][1]),
                                   ('push', p['push'][0], p['push'][1]),
                                   ('cell', left_pred[1], p['cell'][0]),
                                   ('cell', p['cell'][2], zero[1])):
            result.append((names[key], functions[names[key]].replace(before, after)))
        result.append((names['push'], functions[names['push']].replace(names['factory'], returns)))
        for name, *patterns in orderings:
            first = re.search(patterns[0], functions[name])
            last = re.search(patterns[-1], functions[name])
            if last[0].startswith('if '):
                continue
            # Preserve all token requirements while moving the last actual
            # action ahead of the first actual cons/callback action.
            changed = (functions[name][:first.start()] + last[0] + '\n' +
                       functions[name][first.start():last.start()] + functions[name][last.end():])
            result.append((name, changed))
        return result

    return check, list(names.values()), mutations


def rules():
    result = []
    def add(suffix, *patterns):
        result.extend((BASE + suffix, pattern) for pattern in patterns)
    for direction, child, field in [('Forward', 'right', 3), ('Backward', 'left', 4)]:
        add('ControlFrontierCeilingApplication_trans' + direction + '___redArg___lam__2',
            r'v_application_\d+_ = lean_ctor_get\(v_first_\d+_, 0\);',
            rf'v_{direction.lower()}_\d+_ = lean_ctor_get\(v_{child}_\d+_, {field}\);',
            r'v_ceiling_\d+_ = lean_ctor_get\(v_first_\d+_, 1\);',
            r'v_continuation_\d+_ = lean_ctor_get\(v_application_\d+_, 0\);',
            r'v_reader_\d+_ = lean_ctor_get\(v_application_\d+_, 1\);',
            rf'lean_apply_4\(v_{direction.lower()}_\d+_, v_continuation_\d+_, v_ceiling_\d+_, v_reader_\d+_, lean_box\(0\)\);')
    for direction, child, field, callback in [('Forward', 'left', 3, 3), ('Backward', 'right', 4, 0)]:
        add(f'ControlFrontierCeilingApplication_trans{direction}___redArg___lam__{callback}',
            rf'v_{direction.lower()}_\d+_ = lean_ctor_get\(v_{child}_\d+_, {field}\);',
            rf'lean_apply_4\(v_{direction.lower()}_\d+_, v_input_\d+_, v_budget_\d+_, v_reader_\d+_, lean_box\(0\)\);')
        add(f'ControlFrontierCeilingApplication_trans{direction}___redArg',
            r'v___x_\d+_ = 114;',
            r'lean_alloc_ctor\(1, 2, 0\);',
            rf'lean_closure_set\({V}, 0, v_{child}_\d+_\);',
            rf'ControlFrontierCeilingApplication_trans{direction}___redArg___lam__{callback}')
    for direction, ceiling_field, executor_field in [('Forward', 1, 3), ('Backward', 2, 4)]:
        add(f'ControlFrontierCeilingApplication_prepend{direction}___redArg___lam__6',
            rf'v_{direction.lower()}Ceiling_\d+_ = lean_ctor_get\(v_child_\d+_, {ceiling_field}\);',
            rf'ControlReaderCeiling_code___redArg\(v_{direction.lower()}Ceiling_\d+_, v_budget_\d+_\);',
            rf'v_{direction.lower()}_\d+_ = lean_ctor_get\(v_child_\d+_, {executor_field}\);',
            rf'lean_apply_4\(v_{direction.lower()}_\d+_, v_a_\d+_, v_budget_\d+_, v_reader_\d+_, lean_box\(0\)\);')
    add('ControlStageCeilingExecution_code___redArg___lam__4',
        r'v_reduction_\d+_ = lean_ctor_get\(v_stage_\d+_, 4\);',
        r'v_code_\d+_ = lean_ctor_get\(v_reduction_\d+_, 1\);',
        rf'ControlFrontierCeilingEvaluation_code\({V}, {V}, v_frontier_\d+_, v_retained_\d+_, v_code_\d+_\);',
        rf'lean_closure_set\({V}, 4, v_opening_\d+_\);')
    add('ControlStageCeilingExecution_code___redArg___lam__3',
        rf'ControlFrontierCeilingApplication_transCode\({V}, {V}, {V}, v_frontier_\d+_, v_retained_\d+_, v_opening_\d+_, v_reduced_\d+_\);')
    add('ControlStageCeilingExecution_code___redArg___lam__1',
        r'v_original_\d+_ = lean_ctor_get\(v_composed_\d+_, 0\);',
        rf'lean_closure_set\({V}, 0, v_original_\d+_\);',
        rf'lean_closure_set\({V}, 1, v_composed_\d+_\);')
    add('ControlStageCeilingExecution_code___redArg___lam__0',
        rf'lean_ctor_set\({V}, 0, v_original_\d+_\);',
        rf'lean_ctor_set\({V}, 1, v_composed_\d+_\);')
    add('ControlCeilingCompletion_executedDecideCode___redArg___lam__4',
        r'v_execution_\d+_ = lean_ctor_get\(v_payload_\d+_, 1\);',
        r'v_forward_\d+_ = lean_ctor_get\(v_execution_\d+_, 3\);',
        rf'lean_apply_4\(v_forward_\d+_, v_input_\d+_, {V}, v_reader_\d+_, lean_box\(0\)\);')
    add('ControlCeilingCompletion_executedDecideCode___redArg___lam__2',
        r'v_application_\d+_ = lean_ctor_get\(v_paid_\d+_, 0\);',
        r'v_continuation_\d+_ = lean_ctor_get\(v_application_\d+_, 0\);',
        r'v_reader_\d+_ = lean_ctor_get\(v_application_\d+_, 1\);',
        rf'ControlCompletion_executedCompleteCode___redArg\([^;]+, v_continuation_\d+_, v_reader_\d+_\);')
    add('ControlMeasuredMaster_searchFromRootCode___lam__2',
        r'ControlStageCeilingExecution_code___redArg\(v_stage_\d+_, v_execution_\d+_\);')
    add('ControlMeasuredMaster_searchFromRootCode___lam__6',
        rf'ControlFrontierCeilingOpening_code\(v_formula_\d+_, {V}, {V}\);')
    add('ControlMeasuredMaster_runFromRootCode___lam__3',
        r'v_payload_\d+_ = lean_ctor_get\(v_produced_\d+_, 1\);',
        r'ControlCeilingCompletion_executedDecideCode___redArg\([^;]+, v_stage_\d+_, v_memory_\d+_, v_payload_\d+_\);')
    for suffix in ['ControlFrameExecution_formCode___redArg___lam__0',
                   'ControlFrameExecution_finishCode___redArg___lam__1']:
        add(suffix,
            rf'lean_ctor_set\({V}, 0, v_reader_\d+_\);',
            rf'lean_ctor_set\({V}, 1, v_knowledge_\d+_\);',
            rf'lean_ctor_set\({V}, 2, v_root_\d+_\);')
    add('ControlFrameExecution_finishCode___redArg___lam__1',
        rf'lean_ctor_set\({V}, 0, v_step_\d+_\);',
        rf'lean_ctor_set\({V}, 1, v_next_\d+_\);')
    for suffix in ['ControlDocumentaryExecution_execute___redArg',
                   'ControlDocumentaryExecution_initialExecute___redArg']:
        add(suffix,
            rf'ControlCompactExecution_execute___redArg\(v_sourceFuel_\d+_, v_finalBudget_\d+_, {V}\);')
    return result


def make_check(functions, select, parameters, stack_builder=None):
    # A pinned external client may pass the reviewed Arithmetic helper explicitly;
    # the normal repository entry point loads the adopted sibling guard.
    if stack_builder is None:
        arithmetic = runpy.run_path(str(ROOT / 'scripts/check-documentary-arithmetic-codegen.py'))
        stack_builder = arithmetic['make_stack_check']
    shared_check, shared_scope, _ = stack_builder(functions, select, parameters)
    max_check, max_scope, max_mutations = make_max_stack_check(functions, select, parameters)
    required = [(select(functions, suffix), pattern) for suffix, pattern in rules()]
    first_callbacks = [select(functions, BASE + suffix) for suffix in [
        'ControlFrontierCeilingApplication_transForward___redArg___lam__3',
        'ControlFrontierCeilingApplication_transBackward___redArg___lam__0',
        'ControlFrontierCeilingApplication_transForward___redArg___lam__2',
        'ControlFrontierCeilingApplication_transBackward___redArg___lam__2',
        'ControlCeilingCompletion_executedDecideCode___redArg___lam__4']]
    legacy_formation = [select(functions, BASE + suffix) for suffix in [
        'ControlReaderCeiling_recipeCode', 'ControlReaderCeiling_maxCode',
        'ControlFrontierCeilingApplication_transForward___redArg',
        'ControlFrontierCeilingApplication_transBackward___redArg']]
    legacy_scope = set(name for name, _ in required) | set(legacy_formation)
    formation = [name if name != select(functions, BASE + 'ControlReaderCeiling_maxCode')
                 else select(functions, BASE + 'ControlReaderCeiling_descendMax') for name in legacy_formation]
    scope = legacy_scope | set(formation) | set(max_scope) | set(shared_scope)
    forbidden = re.compile(r'\b\w*(?:ControlReaderCeiling_Recipe_denote|ControlFrontierApplication_transForward|ControlFrontierApplication_transBackward|ControlFrontierApplication_prependForward|ControlFrontierApplication_prependBackward|ControlCompletion_executedDecideCode|ControlFrontierExecutableOpening_code|ControlStageExecution_code|Control_execute|ControlHistorical_execute|Program_step)(?:___\w+)?\s*\(')
    def check(current):
        shared_check(current)
        max_check(current)
        for name, pattern in required:
            if len(re.findall(pattern, current[name])) != 1:
                raise ValueError('Ceiling consumer lost its actual received field/call: ' + name + ' / ' + pattern)
        for name in first_callbacks:
            if len(re.findall(r'\blean_apply_\d+\(', current[name])) != 1:
                raise ValueError('Received realized executor must be invoked exactly once: ' + name)
        for name in formation:
            if re.search(r'\blean_apply_\d+\(|\b\w*ControlReaderCeiling_(?:recipeCode|maxCode)\s*\(', current[name]):
                raise ValueError('Recursive descent or reader call before its paid transition: ' + name)
            if 'lean_alloc_ctor(1, 2, 0)' not in current[name]:
                raise ValueError('Formation lost its paid step: ' + name)
        for name in scope:
            if forbidden.search(current[name]):
                raise ValueError('Original executor/native ceiling/replay used in realized consumer: ' + name)
    # Keep the original consumer mutation scope, including the wrapper maxCode:
    # the 91 existing fixtures are retained before the new producer fixtures.
    check.max_mutations = max_mutations
    check.named_scope = sorted(scope)
    return check, required, sorted(legacy_scope), first_callbacks


def main():
    helper = runpy.run_path(str(ROOT / 'scripts/check-agent-codegen.py'))
    functions = {}; texts = []
    for p in sorted((ROOT / '.lake/build/ir').rglob('*.c')):
        source = p.read_text(encoding='utf-8'); texts.append(source)
        functions.update(helper['bodies_with_objects'](source))
    check, required, scope, callbacks = make_check(functions, helper['shared']['select'], helper['parameters'](texts))
    check(functions)
    mutations = []
    for name, pattern in required:
        body = re.sub(pattern, 'substituted_received_field_or_child_777;', functions[name], count=1)
        mutations.append((name, body))
    for name in callbacks:
        call = re.search(r'lean_apply_\d+\([^;]+\);', functions[name])[0]
        mutations.append((name, functions[name] + '\n' + call))
    for name in scope:
        mutations.append((name, functions[name] + '\n' + BASE + 'ControlReaderCeiling_Recipe_denote(v_unpaid_777, v_budget_777);'))
    if len(mutations) != 91:
        raise ValueError('Original ceiling consumer fixture inventory changed')
    mutations += check.max_mutations()
    for name, body in mutations:
        if body == functions[name]:
            raise ValueError('Mutation failed to change its input')
        current = dict(functions)
        current[name] = body
        try:
            check(current)
        except ValueError:
            continue
        raise ValueError('Changed actual ceiling consumer accepted: ' + name)
    print(f'DOCUMENTARY_CEILING_CONSUMERS_CODEGEN_OK: {len(check.named_scope)} named bodies; {len(required)} original actual-field/call requirements; {len(mutations)} textual mutations rejected (91 original consumer fixtures retained); paid max five-body graph with actual predecessors/cons/tails and qualified shared Arithmetic returns; whole original payload/received ceilings/readers and operative master/stage/completion coupling checked; complete runtime inventory and general proofs remain separate')


if __name__ == '__main__':
    main()
