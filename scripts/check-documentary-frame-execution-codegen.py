#!/usr/bin/env python3
"""Reject native producers and reads in the realized frame/assembly consumer.

The native table/function adapters retain original Frame.bindings as a datum.
Paid queries use tableReader, assembledReader and captureCode. Mutation cases
exercise this textual checker; they do not execute corrupt binaries.
The historical recipeReferenceReader for arbitrary producer extensions is a
conditional interface, outside this realized path. The whole-runtime inventory
must separately reject introducing it into the paid documentary consumer.
"""
from pathlib import Path
import re
import runpy
import sys

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parent.parent
PREFIXES = ('ControlFrameExecution_', 'ControlAssemblyExecution_', 'ControlBindingReader_',
            'ControlDeferred_quotationReader', 'ControlDeferred_derivedReader',
            'ControlDeferred_derivedAtReader', 'ControlDeferred_recipeReader')
FORBIDDEN = (
    'Program_step', 'Program_execute', 'Program_quotationStep', 'Program_deductionStep',
    'Snapshot_frame', 'Snapshot_FrameData_restore', 'Snapshot_Bindings_capture',
    'Snapshot_Bindings_read', 'Deduction_derivedKind', 'Resources_Ref_position',
    'Deduction_evaluate', 'Deduction_derive', 'Deduction_producer',
    'ControlMaster_runCode', 'ControlMaster_expandedRunCode', 'ControlStep_code',
    'ControlStep_expandedCode', 'AssignmentCapture_cursor', 'AssignmentCapture_retained',
    'PortableAssignment_interpret', 'TransportCode_eval',
    'MasterResources_Cursor_state',
    'Resources_Support_read', 'Resources_read',
    'ControlDeferred_referenceCode',
)
STORED_TABLE = 'ControlFrameExecution_code___redArg___lam__2'
STORED_BINDINGS = 'ControlFrameExecution_finishCode___redArg___lam__0'
STORED_TAIL = 'ControlBindingReader_captureCode___redArg___lam__2'
HISTORICAL_CONDITIONAL = 'ControlBindingReader_recipeReferenceReader'
TABLE_READ = re.compile(r'\b\w*Snapshot_Bindings_read(?:___\w+)?\s*\([^;]*?\)')


def make_check(functions, parameters):
    scope = [name for name in functions if any('_' + prefix in name for prefix in PREFIXES)
             and '_' + HISTORICAL_CONDITIONAL not in name
             and not name.endswith('___boxed') and 'closed__' not in name]
    for prefix in PREFIXES:
        if not any('_' + prefix in name for name in scope):
            raise ValueError('Missing compiled frame realization: ' + prefix)
    stored = [name for name in scope if name.endswith(STORED_TABLE)]
    if len(stored) != 1:
        raise ValueError('Original retained table adapter is absent or ambiguous')
    native = re.compile(r'\b\w*(?:' + '|'.join(map(re.escape, FORBIDDEN)) + r')(?:___\w+)?\s*\(')
    uninstrumented = re.compile(r'lean_apply_\d+\(v_(?:bindings|assignment|knowledge|readInput)_\d+_')

    def check(current):
        for name in scope:
            body = current[name]
            if name == stored[0]:
                if len(TABLE_READ.findall(body)) != 1:
                    raise ValueError('Original retained table adapter changed')
                body = TABLE_READ.sub('stored_original_table', body, count=1)
            if native.search(body):
                raise ValueError('Native producer/index/read in realized frame: ' + name)
            # These original-function adapters are stored as index data. The
            # capture receives the distinct third argument, the paid Reader.
            if name.endswith(STORED_BINDINGS):
                body = re.sub(r'lean_apply_2\(v_bindings_\d+_, v_spec_\d+_, v___y_\d+_\)',
                              'stored_original_binding_function', body, count=1)
            if uninstrumented.search(body):
                raise ValueError('Opaque original function invoked: ' + name)
            for adapter in (STORED_TABLE, STORED_BINDINGS, STORED_TAIL):
                if re.search(r'\b\w*' + re.escape(adapter) + r'\s*\(', body):
                    raise ValueError('Original adapter directly called by paid consumer: ' + name)
        capture_names = [name for name in current
                   if name.endswith('ControlFrameExecution_finishCode___redArg')]
        if len(capture_names) != 1:
            raise ValueError('Actual successor capture entry absent or ambiguous')
        capture = current[capture_names[0]]
        paid_reader = parameters[capture_names[0]][3]
        captures = re.findall(r'\b\w*ControlBindingReader_captureCode___redArg\(([^;]+)\)', capture)
        if len(captures) != 1 or captures[0].split(',')[-1].strip() != paid_reader:
            raise ValueError('Actual successor bindings are not paid-captured')
        # Whole original bindings remain stored. The paid capture consumes its
        # separate Reader argument, not this original function.
        wrapper = current[next(name for name in scope if name.endswith(
            'ControlFrameExecution_finishCode___redArg___lam__0'))]
        if len(re.findall(r'lean_apply_2\(v_bindings_\d+_, v_spec_\d+_, v___y_\d+_\)', wrapper)) != 1:
            raise ValueError('Original retained binding function wrapper changed')
        if re.search(r'lean_ctor_get\(v_step_\d+_, 0\)', capture) is None:
            raise ValueError('Successor does not consume actual returned Step')

    mutations = [(name, functions[name] + ' lp_forbidden_' + suffix + '();')
                 for name in scope for suffix in FORBIDDEN]
    # Reader substitution by an uninstrumented source at every consumer body.
    mutations += [(name, functions[name] + ' lean_apply_1(v_assignment_777_, v_query_777_);')
                  for name in scope]
    for name in scope:
        if name.endswith('ControlFrameExecution_finishCode___redArg'):
            actual = parameters[name][3]
            changed = re.sub(r'(ControlBindingReader_captureCode___redArg\([^;]+, )' +
                             re.escape(actual) + r'(\))', r'\1v_original_bindings_777_\2', functions[name])
            if changed == functions[name]:
                raise ValueError('Paid capture substitution mutation could not be formed')
            mutations.append((name, changed))
    return check, mutations, scope


def main():
    helper = runpy.run_path(str(ROOT / 'scripts/check-agent-codegen.py'))
    functions = {}
    texts = []
    for path in sorted((ROOT / '.lake/build/ir').rglob('*.c')):
        text = path.read_text(encoding='utf-8')
        texts.append(text)
        functions.update(helper['bodies_with_objects'](text))
    check, mutations, scope = make_check(functions, helper['parameters'](texts))
    check(functions)
    for name, body in mutations:
        current = dict(functions)
        current[name] = body
        try:
            check(current)
        except ValueError:
            pass
        else:
            raise ValueError('Native frame replay mutation accepted: ' + name)
    print('DOCUMENTARY_FRAME_EXECUTION_CODEGEN_OK: ' + str(len(mutations)) +
          ' textual mutations rejected in ' + str(len(scope)) +
          ' named bodies; actual paid binding capture; original table adapter retained separately; '
          'no native producer/position/index read in realized frame consumer')


if __name__ == '__main__':
    try:
        main()
    except (OSError, ValueError, KeyError, StopIteration) as error:
        print('DOCUMENTARY_FRAME_EXECUTION_CODEGEN_ERROR: ' + str(error), file=sys.stderr)
        sys.exit(1)
