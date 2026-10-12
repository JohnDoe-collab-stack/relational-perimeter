#!/usr/bin/env python3
"""Review the actual compact consumer independently of its Lean equality laws.

The complete closure inventory separately checks every reachable helper. Here
we check paid single child calls, metadata-only frames, positive path extension,
whole returned values, shared tape joins and the sole public execution route.
These textual C checks concern the declared abstract catalogue, not CPU or heap.
"""
from pathlib import Path
import re
import runpy
import sys

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parent.parent
FORBIDDEN = ('Control_execute', 'ControlHistorical_execute', 'ControlRunner_execute',
             'ControlAdministration_executeCode', 'ControlCompactExecution_specification',
             'ControlCompactData_sourceDescend', 'ControlCompactExecution_sourceExecute',
             'ControlRunner_Tape_cost', 'ControlRunner_Tape_labels', 'List_append', 'List_length')


def make_check(functions, select, block):
    suffixes = {
        'descend': 'ControlCompactExecution_descend___redArg',
        'finish': 'ControlCompactExecution_finish___redArg',
        'return': 'ControlCompactExecution_returnPaid___redArg',
        'source': 'ControlCompactData_returnSource___redArg',
        'business': 'ControlCompactData_businessOutput___redArg',
        'raw': 'ControlCompactExecution_executeRaw___redArg',
        'execute': 'ControlCompactExecution_execute___redArg',
        'public': 'ControlDocumentaryExecution_execute___redArg',
        'initial': 'ControlDocumentaryExecution_initialExecute___redArg',
        'charge': 'ControlCompactExecution_chargeFast',
        'suffix': 'ControlCompactExecution_suffixCost___redArg',
        'combine': 'ControlRunner_combine',
    }
    names = {key: select(functions, suffix) for key, suffix in suffixes.items()}
    scope = list(names.values())
    forbidden = re.compile(r'\b\w*(?:' + '|'.join(map(re.escape, FORBIDDEN)) + r')(?:___\w+)?\s*\(')

    def calls(body, name):
        return list(re.finditer(r'(v_\w+)\s*=\s*' + re.escape(name) + r'\(([^;]+)\);', body))

    def check(current):
        for name in scope:
            if forbidden.search(current[name]):
                raise ValueError('Replay or traversal in compact consumer: ' + name)
        body = current[names['descend']]
        callbacks = list(re.finditer(r'(v_\w+) = lean_apply_1\((v_next_\d+_), (v_\w+)\);', body))
        payments = calls(body, names['charge'])
        if len(callbacks) != 2 or len(re.findall(r'\blean_apply_\d+\(', body)) != 2:
            raise ValueError('Each received child must be invoked once')
        if len(payments) != 4:
            raise ValueError('Done/stop/business/admin entry catalogue changed')
        if len(re.findall(r'goto _start;', body)) != 2 or calls(body, names['descend']):
            raise ValueError('Compact descent must consume children in tail order')
        for index, callback in enumerate(callbacks):
            entered = [payment for payment in payments if payment.start() < callback.start()][-1]
            receipt, args = entered[1], [arg.strip() for arg in entered[2].split(',')]
            amount, budget = args
            prefix = body[:entered.start()]
            if index == 0:
                if not re.search(re.escape(amount) + r' = lean_unsigned_to_nat\(4u\);', prefix):
                    raise ValueError('Business child lacks its prepaid entry')
            else:
                addition = re.search(re.escape(amount) + r' = lean_nat_add\((v_\w+), (v_\w+)\);', prefix)
                if addition is None or not re.search(re.escape(addition[1]) + r' = lean_unsigned_to_nat\(4u\);', prefix):
                    raise ValueError('Administrative child lacks its fixed entry')
                product = re.search(re.escape(addition[2]) + r' = lean_nat_mul\((v_\w+), (v_forwards_\d+_)\);', prefix)
                if product is None or not re.search(re.escape(product[1]) + r' = lean_unsigned_to_nat\(3u\);', prefix):
                    raise ValueError('Received forwarding layers must be paid before invocation')
                if not re.search(re.escape(product[2]) + r' = lean_ctor_get\(v_code_\d+_, 1\);', prefix):
                    raise ValueError('Forwarding charge must use the received code')
            before = body[entered.end():callback.start()]
            failed = re.search(r'if \(lean_obj_tag\(' + re.escape(receipt) + r'\) == 0\)\s*\{', before)
            if failed is None:
                raise ValueError('Missing failed-entry guard')
            stopped = block(body, entered.end() + failed.end() - 1)
            if 'return ' not in stopped or 'lean_apply_' in stopped:
                raise ValueError('Failed payment must stop before invoking the child')
            residual = re.search(r'(v_\w+) = lean_ctor_get\(' + re.escape(receipt) + r', 0\);', before)
            after = body[callback.end():]
            if residual is None or not re.search(re.escape(budget) + r' = ' + re.escape(residual[1]) + r';', after):
                raise ValueError('Tail descent lost its actual paid residual')
            if not re.search(r'v_code_\d+_ = ' + re.escape(callback[1]) + r';', after):
                raise ValueError('Tail descent must consume the actual child code')
            if re.search(r'lean_ctor_set\([^;]+, ' + re.escape(callback[2]) + r'\);', body):
                raise ValueError('Administrative frame retained a callback')
        if len(re.findall(r'lean_alloc_ctor\(0, 0, 1\)', body)) != 1 or len(re.findall(r'lean_alloc_ctor\(1, 1, 1\)', body)) != 1:
            raise ValueError('Frames must contain business label or admin event/layers only')
        if 'lean_alloc_closure(' in body:
            raise ValueError('Compact consumer retained executable continuation frames')

        finished = current[names['finish']]
        if 'lean_apply_' in finished or len(calls(finished, names['return'])) != 1 or finished.count('goto _start;') != 1:
            raise ValueError('Return trail must consume actual children once without callbacks')
        restored = current[names['return']]
        charged = calls(restored, names['charge'])
        returned = calls(restored, names['source'])
        if 'lean_apply_' in restored or len(charged) != 1 or len(returned) != 1 or charged[0].end() >= returned[0].start():
            raise ValueError('Return must pay before extending the actual path/tape')
        failure = re.search(r'if \(lean_obj_tag\(' + re.escape(charged[0][1]) + r'\) == 0\)\s*\{', restored)
        if failure is None or 'return ' not in block(restored, failure.end() - 1):
            raise ValueError('Failed return payment must stop')
        received_child = returned[0][2].split(',')[-1].strip()
        remaining = re.search(r'(v_\w+) = lean_ctor_get\(' + re.escape(received_child) + r', 3\);', restored)
        if remaining is None or charged[0][2].split(',')[-1].strip() != remaining[1]:
            raise ValueError('Return payment must consume actual child remaining budget')

        positive = current[names['source']]
        if 'lean_apply_' in positive or 'lean_alloc_closure(' in positive:
            raise ValueError('Positive path construction invokes a producer')
        if len(calls(positive, names['combine'])) != 2:
            raise ValueError('Both path constructors must share their actual child tape')
        for joined in calls(positive, names['combine']):
            tape = joined[2].split(',')[1].strip()
            if not re.search(re.escape(tape) + r' = lean_ctor_get\(v_child_\d+_, 2\);', positive):
                raise ValueError('Join substituted the received child tape')
        if positive.count('lean_alloc_ctor(2, 1, 1)') != 1 or positive.count('lean_alloc_ctor(3, 2, 1)') != 1:
            raise ValueError('Executed business/admin events must extend a positive Type path')
        packet = current[names['business']]
        value = re.search(r'(v_value_\d+_) = lean_ctor_get\(v_val_\d+_, 0\);', packet)
        if value is None or not re.search(r'lean_ctor_set\(v_\w+, 0, ' + re.escape(value[1]) + r'\);', packet):
            raise ValueError('Business output reconstructed or replaced its whole received value')
        if 'lean_apply_' in packet or 'lean_alloc_closure(' in packet:
            raise ValueError('Business trace cons must preserve the actual whole child')
        joined = current[names['combine']]
        if joined.count('lean_alloc_ctor(1, 2, 0)') != 2 or 'lean_apply_' in joined:
            raise ValueError('Tape combine must construct exactly two fixed shared joins')
        for key in ('public', 'initial'):
            if len(calls(current[names[key]], names['execute'])) != 1:
                raise ValueError('Public entry bypasses the actual compact executor')
        if len(calls(current[names['execute']], names['raw'])) != 1 or len(calls(current[names['raw']], names['descend'])) != 1:
            raise ValueError('Actual executor must perform one descent')
        if [int(number) for number in re.findall(r'lean_unsigned_to_nat\((\d+)u\)', current[names['suffix']])] != [1, 4, 3]:
            raise ValueError('Return catalogue changed')
        charge = current[names['charge']]
        if 'lean_nat_dec_le(v_amount_' not in charge or not re.search(r'lean_nat_sub\(v_budget_\d+_, v_amount_\d+_\)', charge):
            raise ValueError('Fixed host-counter boundary changed')

    mutations = [(name, functions[name] + ' lp_forbidden_' + suffix + '();')
                 for name in scope for suffix in FORBIDDEN]
    for key in ('descend', 'finish', 'return', 'source', 'business', 'combine'):
        name = names[key]
        mutations.append((name, functions[name] + ' lean_apply_1(v_unpaid_777_, v_unit_777_);'))
    body = functions[names['descend']]
    callbacks = list(re.finditer(r'(v_\w+) = lean_apply_1\((v_next_\d+_), (v_\w+)\);', body))
    for callback in callbacks:
        mutations.append((names['descend'], body.replace(callback[0], 'dropped_actual_child;', 1)))
        mutations.append((names['descend'], body.replace('= ' + callback[1] + ';', '= v_substituted_child_777_;', 1)))
        mutations.append((names['descend'], body + ' lean_ctor_set(v_frame_777_, 0, ' + callback[2] + ');'))
    mutations.append((names['descend'], body.replace('lean_unsigned_to_nat(3u)', 'lean_unsigned_to_nat(0u)', 1)))
    mutations.append((names['descend'], body.replace('goto _start;', 'dropped_tail;', 1)))
    mutations.append((names['source'], functions[names['source']].replace('lean_alloc_ctor(3, 2, 1)', 'lean_alloc_ctor(0, 0, 0)', 1)))
    for key, target in (('public', 'execute'), ('initial', 'execute'), ('execute', 'raw'), ('raw', 'descend'), ('return', 'source')):
        name = names[key]
        mutations.append((name, functions[name].replace(names[target] + '(', 'lp_substituted_777_(', 1)))
    return check, mutations, scope


def main():
    helper = runpy.run_path(str(ROOT / 'scripts/check-agent-codegen.py'))
    runner = runpy.run_path(str(ROOT / 'scripts/check-documentary-runner-codegen.py'))
    functions = {}
    for path in sorted((ROOT / '.lake/build/ir').rglob('*.c')):
        functions.update(helper['bodies_with_objects'](path.read_text(encoding='utf-8')))
    check, mutations, scope = make_check(functions, helper['shared']['select'], runner['block'])
    check(functions)
    for name, body in mutations:
        current = dict(functions)
        current[name] = body
        try:
            check(current)
        except ValueError:
            continue
        raise ValueError('Mutation accepted: ' + name)
    print(f'DOCUMENTARY_COMPACT_CODEGEN_OK: {len(mutations)} textual mutants rejected; '
          f'{len(scope)} actual bodies; prepaid single children, metadata frames, positive paths, '
          'whole values and shared tape joins; public compact route')


if __name__ == '__main__':
    try:
        main()
    except (OSError, ValueError) as error:
        print('DOCUMENTARY_COMPACT_CODEGEN_ERROR: ' + str(error), file=sys.stderr)
        sys.exit(1)
