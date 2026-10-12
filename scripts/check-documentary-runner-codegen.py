#!/usr/bin/env python3
"""Check the terminal runner's paid callbacks and fixed administrative blocks.

Named C bodies are checked, with textual mutations. This is not a physical
heap/CPU theorem. Tape flattening is a reporting boundary, never an executor.
"""
from pathlib import Path
import re
import runpy
import sys

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parent.parent
FORBIDDEN = ('Control_execute', 'Control_runCtl', 'ControlHistorical_execute',
             'ControlCompatibility_erase', 'ControlRunner_Tape_cost',
             'ControlRunner_Tape_labels', 'List_append', 'List_length',
             'ControlAdministration_executeCode', 'ControlAdministration_bindCode')


def block(body, start):
    level = 0
    for index in range(start, len(body)):
        if body[index] == '{':
            level += 1
        elif body[index] == '}':
            level -= 1
            if level == 0:
                return body[start:index + 1]
    raise ValueError('Unclosed C branch')


def make_check(functions, select):
    execute = select(functions, 'ControlRunner_execute___redArg')
    combine = select(functions, 'ControlRunner_combine')
    bind = select(functions, 'Control_Code_bind___redArg')
    forward = select(functions, 'Control_Code_bindForward___redArg')
    charge = select(functions, 'ControlRunner_charge')
    scope = [name for name in functions if '_ControlRunner_' in name
             and not name.endswith('___boxed') and 'closed__' not in name
             and '_Tape_cost' not in name and '_Tape_labels' not in name]
    native = re.compile(r'\b\w*(?:' + '|'.join(map(re.escape, FORBIDDEN)) + r')(?:___\w+)?\s*\(')

    def check(current):
        for name in scope:
            if native.search(current[name]):
                raise ValueError('Replayed source or traversed audit tape: ' + name)
        body = current[execute]
        # The business and administration branches each invoke one callback
        # and consume its actual result in one recursive call.
        callbacks = list(re.finditer(r'(v_\w+) = lean_apply_1\((v_next_\d+_), (v_\w+)\);', body))
        calls = list(re.finditer(re.escape(execute) + r'\(([^;]+)\);', body))
        if len(callbacks) != 2 or len(calls) != 2:
            raise ValueError('Runner must call each received child exactly once')
        if len(re.findall(r'\blean_apply_\d+\(', body)) != 2:
            raise ValueError('Unexpected opaque invocation in terminal runner')
        charge_calls = list(re.finditer(re.escape(charge) + r'\((v_\w+), (v_\w+)\);', body))
        if len(charge_calls) != 8:
            raise ValueError('Fixed done/stop/entry/return charge catalogue changed')
        for index, (callback, recursive) in enumerate(zip(callbacks, calls)):
            entered = [call for call in charge_calls if call.start() < callback.start()][-1]
            amount = entered[1]
            prefix = body[:entered.start()]
            if index == 0:
                if not re.search(re.escape(amount) + r' = lean_unsigned_to_nat\(4u\);', prefix):
                    raise ValueError('Business callback does not prepay four steps')
            else:
                addition = re.search(re.escape(amount) + r' = lean_nat_add\((v_\w+), (v_\w+)\);', prefix)
                if addition is None or not re.search(re.escape(addition[1]) + r' = lean_unsigned_to_nat\(4u\);', prefix):
                    raise ValueError('Administrative callback lacks fixed entry block')
                product = re.search(re.escape(addition[2]) + r' = lean_nat_mul\((v_\w+), (v_forwards_\d+_)\);', prefix)
                if (product is None or not re.search(re.escape(product[1]) + r' = lean_unsigned_to_nat\(3u\);', prefix)
                        or not re.search(re.escape(product[2]) + r' = lean_ctor_get\(v_code_\d+_, 1\);', prefix)):
                    raise ValueError('Administrative callback does not prepay received forwarding count')
            assigned = re.search(r'(v_\w+) = $', body[:entered.start()])
            if assigned is None:
                raise ValueError('Entry charge result not retained')
            receipt = assigned[1]
            failure = re.search(r'if \(lean_obj_tag\(' + re.escape(receipt) + r'\) == 0\)\s*\{',
                                body[entered.end():callback.start()])
            if failure is None:
                raise ValueError('Entry failure guard missing')
            offset = entered.end() + failure.end() - 1
            stopped = block(body, offset)
            if 'return ' not in stopped or 'lean_apply_' in stopped:
                raise ValueError('Failed payment must return before callback')
            received = re.search(r'(v_\w+) = lean_ctor_get\(' + re.escape(receipt) + r', 0\);',
                                 body[entered.end():callback.start()])
            args = [arg.strip() for arg in recursive[1].split(',')]
            if (received is None or len(args) != 3 or args[1] != received[1]
                    or args[2] != callback[1] or callback.end() >= recursive.start()):
                raise ValueError('Recursive runner does not consume paid child and residual budget')
        joined = current[combine]
        if (len(re.findall(r'lean_alloc_ctor\(1, 2, 0\)', joined)) != 2
                or 'lean_apply_' in joined or re.search(r'\b\w*combine\s*\(', joined)
                or re.search(r'\b\w*List_\w+\s*\(', joined)):
            raise ValueError('Audit tree join must allocate two fixed nodes without traversal')
        if 'lean_apply_' in current[bind] or re.search(r'\b\w*Control_Code_bind\w*\s*\(', current[bind]):
            raise ValueError('Bind factory eagerly invokes or flattens its source')
        if 'lean_alloc_ctor(2, 2, 1)' not in current[bind]:
            raise ValueError('Bind must retain its intrinsic administration event')
        propagated = current[forward]
        if 'lean_apply_' in propagated:
            raise ValueError('Forward factory invokes an unpaid callback')
        tail = propagated.split('default:', 1)[-1]
        plus_one = re.search(r'(v_\w+) = lean_unsigned_to_nat\(1u\);', tail)
        if (plus_one is None or not re.search(r'lean_nat_add\(v_forwards_\d+_, ' + re.escape(plus_one[1]) + r'\)', tail)
                or len(re.findall(r'lean_alloc_closure\(', tail)) != 1):
            raise ValueError('Forward factory must conserve the event and add one actual layer')
        event = re.search(r'(v_event_\d+_) = lean_ctor_get_uint8\(v_code_\d+_, sizeof\(void\*\)\*2\);', tail)
        if event is None or not re.search(r'lean_ctor_set_uint8\([^;]+, ' + re.escape(event[1]) + r'\);', tail):
            raise ValueError('Forward factory changes the received event')

    mutations = [(name, functions[name] + ' lp_forbidden_' + suffix + '();')
                 for name in scope for suffix in FORBIDDEN]
    mutations += [(execute, functions[execute] + ' lean_apply_1(v_next_777_, v_unit_777_);'),
                  (combine, functions[combine] + ' lean_apply_1(v_child_777_, v_unit_777_);'),
                  (bind, functions[bind] + ' lean_apply_1(v_code_777_, v_unit_777_);')]
    mutations += [(forward, functions[forward] + ' lean_apply_1(v_code_777_, v_unit_777_);'),
                  (forward, functions[forward].replace('lean_unsigned_to_nat(1u)', 'lean_unsigned_to_nat(0u)', 1))]
    forwarded_event = re.search(r'lean_ctor_set_uint8\([^;]+, (v_event_\d+_)\);', functions[forward])
    if forwarded_event is None:
        raise ValueError('Missing retained event assignment')
    mutations.append((forward, functions[forward].replace(forwarded_event[0],
                      forwarded_event[0].replace(forwarded_event[1], '0'), 1)))
    # The administrative entry is the sole variable charge: removing its
    # multiplier must fail independently of complete packet equivalence.
    administrative = functions[execute].split('default:', 1)[-1]
    coefficient = re.search(r'(v_\w+) = lean_unsigned_to_nat\(3u\);', administrative)
    if coefficient is None:
        raise ValueError('Missing forwarding catalogue coefficient')
    mutations.append((execute, functions[execute].replace(coefficient[0],
                      coefficient[1] + ' = lean_unsigned_to_nat(0u);', 1)))
    callbacks = list(re.finditer(r'(v_\w+) = lean_apply_1\((v_next_\d+_), (v_\w+)\);', functions[execute]))
    for callback in callbacks:
        mutations.append((execute, functions[execute].replace(callback[0], 'dropped_callback;', 1)))
        mutations.append((execute, functions[execute].replace(callback[1] + ');', 'v_unreceived_777_);', 1)))
    return check, mutations, scope


def main():
    helper = runpy.run_path(str(ROOT / 'scripts/check-agent-codegen.py'))
    functions = {}
    for path in sorted((ROOT / '.lake/build/ir').rglob('*.c')):
        functions.update(helper['bodies_with_objects'](path.read_text(encoding='utf-8')))
    check, mutations, scope = make_check(functions, helper['shared']['select'])
    check(functions)
    for name, body in mutations:
        current = dict(functions)
        current[name] = body
        try:
            check(current)
        except ValueError:
            continue
        raise ValueError('Mutation accepted: ' + name)
    print(f'DOCUMENTARY_RUNNER_CODEGEN_OK: {len(mutations)} textual mutants rejected; '
          f'{len(scope)} named bodies; fixed paid entry, actual child/residual, shared tape joins, lazy bind')


if __name__ == '__main__':
    try:
        main()
    except (OSError, ValueError) as error:
        print('DOCUMENTARY_RUNNER_CODEGEN_ERROR: ' + str(error), file=sys.stderr)
        sys.exit(1)
