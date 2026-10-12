#!/usr/bin/env python3
"""Guard the fixed ownership boundary of the actual compact executor.

Frame formation was paid at descent entry. The helper transfers only the
immediate owned pointer; returnPaid succeeds before its paid-path invocation.
This checks generated C, not physical peak memory or time.
"""
from pathlib import Path
import re
import runpy
import sys
sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parent.parent

def make_check(functions, select, block, *, export_name='rp_documentary_owned_trail'):
    suffixes = {
        'paid_finish': 'ControlCompactExecution_finish___redArg',
        'paid_descend': 'ControlCompactExecution_descend___redArg',
        'source_finish': 'ControlCompactData_finishSource___redArg',
        'source_descend': 'ControlCompactData_sourceDescend___redArg',
        'paid_return': 'ControlCompactExecution_returnPaid___redArg',
        'source_return': 'ControlCompactData_returnSource___redArg',
    }
    names = {k: select(functions, s) for k, s in suffixes.items()}
    names['owned'] = export_name
    if export_name not in functions:
        raise ValueError('Missing reviewed monomorphic owned-pointer boundary')
    def calls(body, target):
        return list(re.finditer(r'(v_\w+)\s*=\s*' + re.escape(target) + r'\(([^;]+)\);', body))
    def check(current):
        helper = current[names['owned']]
        direct = r'return v_trail_\d+_;'
        # Both reviewed compiler shapes contain solely the input pointer return.
        plain = r'\{\s*' + direct + r'\s*\}'
        labeled = r'\{\s*_start:\s*\{\s*' + direct + r'\s*\}\s*\}'
        if not (re.fullmatch(plain, helper) or re.fullmatch(labeled, helper)):
            raise ValueError('Owned boundary traverses, allocates or substitutes a pointer')
        for kind in ('paid', 'source'):
            finish = current[names[kind + '_finish']]
            if re.search(r'\blean_apply_\d+\s*\(', finish):
                raise ValueError('Finish must not execute a callback')
            owned = calls(finish, names['owned'])
            returned = calls(finish, names[kind + '_return'])
            owned_count = len(re.findall(r'\b' + re.escape(names['owned']) + r'\s*\(', finish))
            return_count = len(re.findall(r'\b' + re.escape(names[kind + '_return']) + r'\s*\(', finish))
            if (len(owned) != 1 or len(returned) != 1 or
                    owned_count != 1 or return_count != 1 or
                    finish.count('goto _start;') != 1):
                raise ValueError('Finish must transfer and consume exactly one received frame')
            tail = re.search(r'(v_\w+) = lean_ctor_get\((v_trail_\w+), 1\);', finish)
            if tail is None or owned[0][2].strip() != tail[1]:
                raise ValueError('Owned boundary lost the actual received tail')
            consumed = re.search(r'lean_dec_ref_known\(' + re.escape(tail[2]) + r', 2\);', finish)
            if consumed is None or not tail.end() < consumed.start() < owned[0].start():
                raise ValueError('Current cons retained across the next iteration')
            if not re.search(re.escape(tail[2]) + r'\s*=\s*' + re.escape(owned[0][1]) + r';', finish[owned[0].end():]):
                raise ValueError('Loop must consume the actual transferred tail')
            if kind == 'paid':
                if returned[0].end() >= owned[0].start():
                    raise ValueError('Owned call precedes return payment')
                receipt = returned[0][1]
                guard = re.search(r'if \(lean_obj_tag\(' + re.escape(receipt) + r'\) == 0\)\s*\{',
                                  finish[returned[0].end():owned[0].start()])
                if guard is None:
                    raise ValueError('Missing return-payment failure guard')
                opening = returned[0].end() + guard.end() - 1
                failed = block(finish, opening)
                if calls(failed, names['owned']) or names['owned'] + '(' in failed:
                    raise ValueError('Failed terminal return invokes ownership boundary')
                if not re.search(r'return ' + re.escape(receipt) + r';', failed):
                    raise ValueError('Failed terminal return did not preserve its none')
                child = re.search(r'v_child_\w+\s*=\s*' + re.escape(receipt) + r';', finish[owned[0].end():])
                if child is None:
                    raise ValueError('Loop must consume the actual paid whole child')
            caller = current[names[kind + '_descend']]
            finishes = calls(caller, names[kind + '_finish'])
            if len(finishes) != 2:
                raise ValueError('Done and source stop must enter the same owned finish')
            for call in finishes:
                trail = call[2].split(',')[0].strip()
                after = caller[call.end():]
                immediate = re.match(r'\s*return ' + re.escape(call[1]) + r';', after)
                if immediate is None:
                    raise ValueError('Caller retains/replays the full trail after finish')
                if not trail.startswith('v_trail_'):
                    raise ValueError('Caller substituted its received trail')
    scope = list(names.values())
    mutations = []
    for kind in ('paid', 'source'):
        n = names[kind + '_finish']; body = functions[n]
        mutations += [
            (n, body + ' lean_apply_1(v_callback_999_, v_unit_999_);'),
            (n, body.replace(names['owned'] + '(', 'unreviewed_pointer_boundary(', 1)),
            (n, re.sub(r'lean_dec_ref_known\(v_trail_\w+, 2\);', '', body, count=1)),
            (n, body + ' ' + names[kind + '_return'] + '(v_frame_999_, v_child_999_);'),
            (n, body.replace('goto _start;', 'dropped_tail;', 1)),
        ]
        caller_n = names[kind + '_descend']; caller = functions[caller_n]
        first = calls(caller, names[kind + '_finish'])[0]
        mutations.append((caller_n, caller[:first.end()] +
                          ' lean_dec(v_retained_trail_999_);' + caller[first.end():]))
    mutations += [
        (names['owned'], '{ return lean_box(0); }'),
        (names['owned'], '{ lean_apply_1(v_unpaid_999_, v_unit_999_); return v_trail_999_; }'),
        (names['owned'], '{ return ' + names['owned'] + '(v_trail_999_); }'),
    ]
    paid_n = names['paid_finish']; body = functions[paid_n]
    returned = calls(body, names['paid_return'])[0]
    owned = calls(body, names['owned'])[0]
    mutations.append((paid_n, body[:returned.start()] + owned[0] +
                      body[returned.start():owned.start()] + body[owned.end():]))
    receipt = returned[1]
    guard = re.search(r'if \(lean_obj_tag\(' + re.escape(receipt) + r'\) == 0\)\s*\{', body)
    mutations.append((paid_n, body[:guard.end()] + '\n' + owned[0] + body[guard.end():]))
    return check, mutations, scope

def main():
    agent = runpy.run_path(str(ROOT/'scripts/check-agent-codegen.py'))
    runner = runpy.run_path(str(ROOT/'scripts/check-documentary-runner-codegen.py'))
    # The shared agent parser intentionally selects l_/lp_ symbols. The owned
    # export is explicitly named outside those prefixes, so inspect complete
    # balanced function bodies with the already qualified reader parser.
    complete = runpy.run_path(str(ROOT/'scripts/check-documentary-reader-payment-codegen.py'))
    functions = {}
    for module in ('DocumentaryControlCompactData', 'DocumentaryControlCompactExecution'):
        file = ROOT/'.lake/build/ir/Tests/LocalAlignment'/ (module + '.c')
        functions.update(complete['bodies'](file.read_text(encoding='utf-8')))
    check, mutations, scope = make_check(functions, agent['shared']['select'], runner['block'])
    check(functions)
    for name, body in mutations:
        current = dict(functions); current[name] = body
        try:
            check(current)
        except ValueError:
            continue
        raise ValueError('Ownership mutation accepted: ' + name)
    print('DOCUMENTARY_COMPACT_OWNERSHIP_CODEGEN_OK: ' + str(len(mutations)) +
          ' textual mutants rejected; immediate paid frame transfer, source stop distinct ' +
          'from terminal failure, single whole child consumed, owned trail released in order')

if __name__ == '__main__':
    try:
        main()
    except (OSError, ValueError, KeyError) as error:
        print('DOCUMENTARY_COMPACT_OWNERSHIP_CODEGEN_ERROR: ' + str(error), file=sys.stderr)
        sys.exit(1)
