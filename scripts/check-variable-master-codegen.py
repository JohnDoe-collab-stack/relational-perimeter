#!/usr/bin/env python3
"""Sharing checks for the named local producer chain, not a cost theorem.

The existing local symbolic C-IR analysis follows helpers and applied producer
closures. Each counted producer is an explicit boundary: its own internal
search/recursion is not a single elementary operation.
"""
from pathlib import Path
import copy
import re
import runpy
import sys

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parent.parent
agent = runpy.run_path(str(ROOT / 'scripts/check-agent-codegen.py'))
shared = agent['shared']


class LocalAnalysis(agent['AgentAnalysis']):
    """Keep producer-record identities even for unrelated operations.

    A support's formation can retain an earlier producer closure. A later
    extend still needs its own operation identity; skipping that producer's
    record construction would turn a known operation into an unknown callback.
    No operation is cut here: only record constructors are always interpreted.
    """
    def __init__(self, *args, constructors=(), **kwargs):
        self.constructors = set(constructors)
        self.shape_ids, self.run_cache = {}, {}
        super().__init__(*args, **kwargs)

    def relevant(self, name):
        return name in self.constructors or super().relevant(name)

    def run(self, name, arguments):
        # Exact structural memoization, including numbers, closures, captures
        # and every field. Cached results are copied because callers may set
        # constructor fields. This shares analysis work, not runtime work.
        seen = {}

        def shape(value):
            if id(value) in seen:
                return seen[id(value)]
            key = (value.tags, value.function, value.fixed, value.number,
                   tuple((slot, shape(child)) for slot, child in sorted(value.fields.items())))
            if key not in self.shape_ids:
                self.shape_ids[key] = len(self.shape_ids)
            seen[id(value)] = self.shape_ids[key]
            return seen[id(value)]

        key = (name, tuple(shape(value) for value in arguments))
        if key not in self.run_cache:
            self.run_cache[key] = copy.deepcopy(super().run(name, arguments))
        return copy.deepcopy(self.run_cache[key])


def erased_application_self_test():
    text = '''LEAN_EXPORT lean_object* l_target(lean_object* x){ return x; }
    LEAN_EXPORT lean_object* l_entry(lean_object* x){
      lean_object* produced; lean_object* erased;
      produced = l_target(x); erased = lean_box(0);
      return lean_apply_1(erased, produced);
    }
    LEAN_EXPORT lean_object* l_unknown(lean_object* f, lean_object* x){
      lean_object* produced; produced = l_target(x);
      return lean_apply_1(f, produced);
    }
    LEAN_EXPORT lean_object* l_twice(lean_object* x){
      lean_object* first; first = l_target(x); return l_target(x);
    }'''
    text = '\n'.join(line.lstrip() for line in text.splitlines())
    functions = shared['bodies'](text)
    params = agent['parameters']([text])
    analysis = LocalAnalysis(functions, params, shared['reachable'], target='l_target')
    result, low, high = analysis.run('l_entry', [agent['Value']()])
    if (low, high, result.number) != (1, 1, 0):
        raise ValueError(f'Erased application lost argument work: [{low},{high}], scalar={result.number}')
    _, low, high = analysis.run('l_twice', [agent['Value']()])
    if (low, high) != (2, 2):
        raise ValueError('Analysis memoization hid a repeated runtime call')
    try:
        analysis.run('l_unknown', [agent['Value'](), agent['Value']()])
    except ValueError as error:
        if 'Unresolved applied closure' not in str(error):
            raise
    else:
        raise ValueError('Unknown callback did not fail closed')
    print('VARIABLE_ERASED_APPLICATION_SELFTEST_OK')


def main():
    agent['self_test']()
    erased_application_self_test()
    functions, texts, owners = {}, [], {}
    for path in sorted((ROOT / '.lake/build/ir').rglob('*.c')):
        text = path.read_text(encoding='utf-8')
        texts.append(text)
        parsed = agent['bodies_with_objects'](text)
        functions.update(parsed)
        for name in parsed:
            owners.setdefault(name, set()).add(path.relative_to(ROOT / '.lake/build/ir').as_posix())
    compiled_parameters = agent['parameters'](texts)
    module = 'RelationalPerimeter/Computation/ConstitutiveSearch/EndogenousDecomposition/VariableMasterExecution.c'
    prefix = 'lp_relational_x2dperimeter_'

    def local(declaration, variant=''):
        return shared['owned_symbol'](functions, compiled_parameters, owners,
            prefix, 'ConstitutiveSearch.EndogenousDecomposition.VariableMaster.' + declaration,
            module, variant)

    step, head = local('step'), local('masterHead')
    opening = local('openFrontier', '___redArg')
    normalize = shared['select'](functions, 'normalizeGeneratedStructuralFrontierByFlip___redArg')
    discovery = shared['select'](functions, 'runThreadedNextDiscovery___redArg')
    extend = shared['select'](functions, 'Resources_Support_extend___redArg')
    for entry, expected in ((step, 5), (head, 4)):
        calls = re.findall(r'\b' + re.escape(extend) + r'\s*\(', functions[entry])
        if len(calls) != expected:
            raise ValueError(f'{entry}: expected {expected} local productions, found {len(calls)}')
        print(f'VARIABLE_PRODUCTIONS_OK {entry}: {expected}')

    normalized = {name: re.sub(r'\(\(lean_object\*\)\(((?:l|lp)_\w+)\)\)', r'\1', body)
                  for name, body in functions.items()}
    constructor_names = [
        'ConstitutiveSearch_EndogenousDecomposition_VariableMaster_' + name
        for name in ('produceHead', 'produceOpening', 'produceReduction', 'produceNextFrontier', 'produceNextCursor')]
    constructor_names += [
        'ConstitutiveSearch_EndogenousDecomposition_MasterResources_' + name
        for name in ('discover', 'applyStage', 'decompose', 'assemble', 'headNextPrefix', 'headNextSource', 'headNextFresh')]
    constructors = {prefix + name + variant for name in constructor_names
                    for variant in ('', '___redArg') if prefix + name + variant in functions}
    for entry, target in ((step, head), (head, discovery), (step, opening), (step, normalize)):
        analysis = LocalAnalysis(normalized, compiled_parameters, shared['reachable'],
            target=target, constructors=constructors)
        _, low, high = analysis.run(entry, [agent['Value']() for _ in compiled_parameters[entry]])
        if (low, high) != (1, 1):
            raise ValueError(f'{entry}: expected exactly one application of {target}, found [{low},{high}]')
        print(f'VARIABLE_APPLICATIONS_OK {entry}: {target}=[1,1]')
    shared['absent'](functions, step, [
        'VariableMaster_stepSupport', 'VariableMaster_nextCursor',
        'MasterResources_Cursor_headResources', 'MasterResources_Cursor_headSupport'])
    print('VARIABLE_MASTER_CODEGEN_OK: shared local head, opening and normalization; no reconstructed support')


if __name__ == '__main__':
    try:
        main()
    except (OSError, ValueError) as error:
        print(f'VARIABLE_MASTER_CODEGEN_FAILED: {error}', file=sys.stderr)
        sys.exit(1)
