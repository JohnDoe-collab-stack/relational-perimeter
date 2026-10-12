#!/usr/bin/env python3
"""Reject causal history/formula reconstruction in actual measured production.

The projection is followed transitively, including captured C closures. Whole
packet equality remains a separate Lean obligation. Mutation fixtures exercise
this checker, not corrupted runtime binaries.
"""
from pathlib import Path
import re
import runpy
import sys

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parent.parent
PREFIXES = ('ControlCausalProjection_', 'ControlCausalDecomposition_',
            'ControlCausalContinuation_', 'ControlReceivedResources_',
            'ControlReceivedDiscovery_',
            'ControlMasterHeadReader_', 'ControlMeasuredMaster_')
FORBIDDEN = ('EndogenousDecomposition_causalStateOfThreadedState',
             'EndogenousDecomposition_causalStageOfThreadedStage',
             'EndogenousDecomposition_constructStage',
             'SAT_distinctGrowingDiscoveryFormula',
             'Resources_Support_read', 'Resources_Producer_arguments',
             'ControlMasterHead_prefixOperation', 'ControlMasterHead_continueCode')
ROOT_REPLAY = ('ControlMasterGeneration_rootCode',
               'EndogenousDecomposition_constructMeasuredOperationalRoot',
               'EndogenousDecomposition_measuredGeneratedExtractionFromSeed')


def make_check(functions, shared):
    scope = [name for name in functions
             if any('_' + prefix in name for prefix in PREFIXES)
             and not name.endswith('___boxed') and 'closed__' not in name]
    for prefix in PREFIXES:
        if not any('_' + prefix in name for name in scope):
            raise ValueError('Missing causal consumer: ' + prefix)
    projection = shared['select'](functions, 'ControlCausalProjection_code')
    received = shared['select'](functions, 'ControlReceivedDiscovery_code___redArg')
    forbidden = re.compile(r'\b\w*(?:' + '|'.join(map(re.escape, FORBIDDEN)) +
                           r')(?:___\w+)?\s*\(')

    def check(current):
        for name in scope:
            if forbidden.search(current[name]):
                raise ValueError('Native causal replay in actual consumer: ' + name)
            if '_ControlReceivedDiscovery_' in name and re.search(
                    r'\b\w*(?:ControlMasterGeneration_rootCode|'
                    r'EndogenousDecomposition_constructMeasuredOperationalRoot|'
                    r'EndogenousDecomposition_measuredGeneratedExtractionFromSeed)'
                    r'(?:___\w+)?\s*\(', current[name]):
                raise ValueError('Received root is reconstructed instead of consumed: ' + name)
        reached = shared['reachable'](current, projection)
        for name in reached:
            if any(part in name for part in FORBIDDEN):
                raise ValueError('Transitive causal projection replay: ' + name)
            if forbidden.search(current[name]):
                raise ValueError('Hidden causal replay in projection helper: ' + name)
        for name in shared['reachable'](current, received):
            if any(part in name for part in ROOT_REPLAY):
                raise ValueError('Transitive reconstruction of received measured root: ' + name)

    mutations = [(name, functions[name] + ' lp_forbidden_' + suffix + '();')
                 for name in scope for suffix in FORBIDDEN]
    mutations += [(name, functions[name] + ' lp_forbidden_' + suffix + '();')
                  for name in scope if '_ControlReceivedDiscovery_' in name
                  for suffix in ROOT_REPLAY]
    return check, mutations, scope, projection


def main():
    helper = runpy.run_path(str(ROOT / 'scripts/check-agent-codegen.py'))
    functions = {}
    for path in sorted((ROOT / '.lake/build/ir').rglob('*.c')):
        functions.update(helper['bodies_with_objects'](path.read_text(encoding='utf-8')))
    check, mutations, scope, projection = make_check(functions, helper['shared'])
    check(functions)
    for name, body in mutations:
        current = dict(functions)
        current[name] = body
        try:
            check(current)
        except ValueError:
            continue
        raise ValueError('Causal replay mutation accepted: ' + name)
    # A replay moved into a previously unnamed helper must also fail.
    extra = 0
    for suffix in FORBIDDEN:
        current = dict(functions)
        current['lp_hidden_causal_helper'] = '{ lp_forbidden_' + suffix + '(); }'
        current[projection] += ' lp_hidden_causal_helper();'
        try:
            check(current)
        except ValueError:
            extra += 1
            continue
        raise ValueError('Transitive helper replay mutation accepted: ' + suffix)
    print(f'DOCUMENTARY_CAUSAL_CODEGEN_OK: {len(mutations) + extra} textual mutants rejected; '
          f'{len(scope)} named consumer bodies; projection helpers followed transitively; '
          'received history/generation retained, no native canonical reconstruction')


if __name__ == '__main__':
    try:
        main()
    except (OSError, ValueError, KeyError) as error:
        print('DOCUMENTARY_CAUSAL_CODEGEN_ERROR: ' + str(error), file=sys.stderr)
        sys.exit(1)
