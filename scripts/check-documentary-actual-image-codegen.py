#!/usr/bin/env python3
"""Check that the actual image consumes occurrences returned by its licence.

Named C bodies and mutation inputs support the independent dataflow review.
They do not establish a physical allocation bound or execute mutant binaries.
"""
from pathlib import Path
import re
import runpy
import sys

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parent.parent
BASE = 'Agent_Local_Documentary_'
PREFIXES = (
    'ControlMasterDecomposition_carrierFrom',
    'ControlMasterDecomposition_imageFromLicenseCode',
    'ControlMasterDecomposition_actualDecompositionCode',
    'ControlMasterDecomposition_actualCode',
    'ControlProducedImage_codeFromFrontier',
    'ControlProducedImage_fromReceivedFrontier',
)
NATIVE = ('roleOpeningFiniteCarrier', 'roleConstitutedOccurrenceAt',
          'roleOpeningOccurrenceAt', 'relationallyConstitutedOccurrenceFrontier',
          'producedRoleOutputRegime', 'executedStageDecomposition')


def make_check(functions, select):
    scope = [name for name in functions if any(BASE + prefix in name for prefix in PREFIXES)
             and not name.endswith('___boxed') and 'closed__' not in name]
    for prefix in PREFIXES:
        if not any(BASE + prefix in name for name in scope):
            raise ValueError('Missing actual image body: ' + prefix)
    carrier = select(functions, BASE + 'ControlMasterDecomposition_carrierFromLicense___redArg')
    retained = select(functions, BASE + 'ControlMasterDecomposition_carrierFromFrontier___redArg')
    factory = select(functions, BASE + 'ControlMasterDecomposition_imageFromLicenseCode')
    consumer = next(name for name in scope if re.search(re.escape(carrier) + r'\s*\(', functions[name])
                    and 'imageFromLicenseCode' in name)
    native = re.compile(r'\b\w*(?:' + '|'.join(NATIVE) + r')(?:___\w+)?\s*\(')

    def check(current):
        for name in scope:
            if native.search(current[name]):
                raise ValueError('Original image/identity reconstructed: ' + name)
        body = current[carrier]
        projections = []
        for field in (0, 2):
            match = re.search(r'(v_\w+) = lean_ctor_get\((v_license_\d+_), ' + str(field) + r'\)', body)
            if not match or not re.search(r'lean_ctor_set\([^,]+, 0, ' + re.escape(match[1]) + r'\)', body):
                raise ValueError('Actual licence occurrence dropped: ' + str(field))
            projections.append(match[2])
        if projections[0] != projections[1]:
            raise ValueError('Occurrences came from different licences')
        if not re.search(r'lean_ctor_set\([^,]+, 1, v_frontier_\d+_\)', current[retained]):
            raise ValueError('Carrier drops its received frontier')
        if not re.search(r'= 25;', current[factory]):
            raise ValueError('Carrier formation has no paid resource label')
        body = current[consumer]
        actual_carrier = re.search(r'(v_\w+) = ' + re.escape(carrier) + r'\s*\(', body)
        if not actual_carrier:
            raise ValueError('Actual carrier formation missing')
        frontier = re.search(r'(v_\w+) = lean_ctor_get\(' + re.escape(actual_carrier[1]) + r', 1\)', body)
        if not frontier:
            raise ValueError('Actual carrier frontier not read')
        calls = re.findall(r'\b\w*ControlProducedImage_codeFromFrontier\w*\(([^;]+)\);', body)
        if len(calls) != 1 or not re.search(r'\b' + re.escape(frontier[1]) + r'\b', calls[0]):
            raise ValueError('Actual image does not consume exactly one received frontier')

    mutations = [(name, functions[name] + ' lp_native_' + symbol + '();')
                 for name in scope for symbol in NATIVE]
    for field in (0, 2):
        mutations.append((carrier, re.sub(r'(lean_ctor_get\(v_license_\d+_, )' + str(field) + r'(\))',
                                         r'\g<1>7\2', functions[carrier])))
    mutations += [(retained, re.sub(r'v_frontier_\d+_', 'v_substituted', functions[retained])),
                  (factory, functions[factory].replace('= 25;', '= 0;')),
                  (consumer, re.sub(r'(lean_ctor_get\(v_carrier_\d+_, )1(\))',
                                    r'\g<1>0\2', functions[consumer]))]
    return check, mutations, scope


def main():
    analysis = runpy.run_path(str(ROOT / 'scripts/check-agent-codegen.py'))
    functions = {}
    for path in sorted((ROOT / '.lake/build/ir').rglob('*.c')):
        functions.update(analysis['bodies_with_objects'](path.read_text(encoding='utf-8')))
    check, mutations, scope = make_check(functions, analysis['shared']['select'])
    check(functions)
    for name, body in mutations:
        mutated = dict(functions)
        mutated[name] = body
        try:
            check(mutated)
        except ValueError:
            pass
        else:
            raise ValueError('Actual image mutation accepted: ' + name)
    print('DOCUMENTARY_ACTUAL_IMAGE_CODEGEN_OK: ' + str(len(mutations)) +
          ' textual mutations rejected in ' + str(len(scope)) +
          ' named bodies; actual licence occurrences and frontier retained; '
          'whole-result proofs and final consumer qualified separately')


if __name__ == '__main__':
    try:
        main()
    except (OSError, ValueError, KeyError, StopIteration) as error:
        print('DOCUMENTARY_ACTUAL_IMAGE_CODEGEN_ERROR: ' + str(error), file=sys.stderr)
        sys.exit(1)
