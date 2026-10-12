#!/usr/bin/env python3
"""Reject native replays while forming and consuming measured readers.

This checks named C bodies and actual call syntax, not mere captured symbols.
Mutation fixtures exercise this checker, not corrupted runtime binaries.
The final documentary consumer and administration require separate checks.
"""
from pathlib import Path
import re
import runpy
import sys

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parent.parent
PREFIXES = (
    'ControlMeasuredAssignmentReader_', 'ControlMeasuredTransportReader_code',
    'ControlMeasuredTransportReader_applicationCode', 'ControlSequentialReader_',
    'ControlMasterApplicationReader_', 'ControlNextState_decisionWithReaderCode',
    'ControlNextState_withReaderCode',
    'ControlAssignmentCapture_', 'ControlMasterHeadReader_', 'ControlMeasuredMaster_',
    'ControlMasterRootBootstrap_',
)
FORBIDDEN = (
    'TransportCode_eval', 'PortableAssignment_interpret',
    'EndogenousDecomposition_constructStage', 'SAT_distinctGrowingDiscoveryFormula',
    'EndogenousDecomposition_causalStateOfThreadedState',
    'EndogenousDecomposition_causalStageOfThreadedStage',
    'EndogenousDecomposition_readTransportedAssignment',
    'EndogenousDecomposition_readFlippedAssignment',
    'EndogenousDecomposition_readAlternatingAssignment',
    'ControlNextState_decisionCode', 'ControlNextState_code',
    'ControlMasterApplication_code', 'ControlSequentialStage_code',
    'ControlMasterHead_code', 'ControlMaster_expandedSearchCode',
    'ControlMasterHead_prefixOperation', 'ControlMasterHead_continueCode',
    'ControlMaster_expandedRunCode', 'ControlMaster_runCode',
    'AssignmentCapture_retained', 'AssignmentCapture_cursor',
    'MasterResources_Cursor_state',
)
# These four reviewed adapters form or denote the ORIGINAL reader retained
# as data/index. They are not the paid queryCode. Adding another adapter needs
# a new review; a direct invocation from a controlled consumer fails below.
STORED_ORIGINAL = (
    'ControlMeasuredTransportReader_code___redArg___lam__19',
    'ControlSequentialReader_cachedReader___redArg',
    'ControlSequentialReader_cachedReader',
    'ControlSequentialReader_nextCached___redArg___lam__0',
)
ORIGINAL_READ = re.compile(
    r'\b\w*EndogenousDecomposition_readTransportedAssignment(?:___\w+)?\s*\([^;]*?\)')


def make_check(functions):
    scope = [name for name in functions
             if any('_' + prefix in name for prefix in PREFIXES)
             and not name.endswith('___boxed') and 'closed__' not in name]
    for prefix in PREFIXES:
        if not any('_' + prefix in name for name in scope):
            raise ValueError('Missing compiled reader consumer: ' + prefix)
    replay = re.compile(r'\b\w*(?:' + '|'.join(map(re.escape, FORBIDDEN)) +
                        r')(?:___\w+)?\s*\(')
    opaque = re.compile(r'lean_apply_\d+\(v_(?:assignment|readInput)_\d+_')

    def check(current):
        for name in scope:
            body = current[name]
            stored = any(name.endswith(suffix) for suffix in STORED_ORIGINAL)
            if stored:
                if len(ORIGINAL_READ.findall(body)) != 1:
                    raise ValueError('Original stored reader adapter changed: ' + name)
                body = ORIGINAL_READ.sub('stored_original_reader', body, count=1)
            if replay.search(body):
                raise ValueError('Unopened native replay in actual reader path: ' + name)
            if opaque.search(body):
                raise ValueError('Opaque original assignment/reader invoked: ' + name)
            if not stored:
                for suffix in STORED_ORIGINAL:
                    if re.search(r'\b\w*' + re.escape(suffix) + r'\s*\(', body):
                        raise ValueError('Stored original reader directly invoked by consumer: ' + name)

    mutations = [(name, functions[name] + ' lp_forbidden_' + suffix + '();')
                 for name in scope for suffix in FORBIDDEN]
    mutations += [(name, functions[name] +
                   ' lean_apply_1(v_assignment_777_, v_query_777_);') for name in scope]
    mutations += [(name, functions[name] +
                   ' lean_apply_1(v_readInput_777_, v_query_777_);') for name in scope]
    return check, mutations, scope


def main():
    agent = runpy.run_path(str(ROOT / 'scripts/check-agent-codegen.py'))
    functions = {}
    for path in sorted((ROOT / '.lake/build/ir').rglob('*.c')):
        functions.update(agent['bodies_with_objects'](path.read_text(encoding='utf-8')))
    check, mutations, scope = make_check(functions)
    check(functions)
    for name, body in mutations:
        current = dict(functions)
        current[name] = body
        try:
            check(current)
        except ValueError:
            pass
        else:
            raise ValueError('Native reader replay mutation accepted: ' + name)
    print('DOCUMENTARY_MEASURED_READER_CODEGEN_OK: ' + str(len(mutations)) +
          ' textual mutations rejected in ' + str(len(scope)) +
          ' named bodies; no native transport/index replay or opaque source read; '
          'whole-packet proofs and final consumer qualified separately')


if __name__ == '__main__':
    try:
        main()
    except (OSError, ValueError, KeyError) as error:
        print('DOCUMENTARY_MEASURED_READER_CODEGEN_ERROR: ' + str(error), file=sys.stderr)
        sys.exit(1)
