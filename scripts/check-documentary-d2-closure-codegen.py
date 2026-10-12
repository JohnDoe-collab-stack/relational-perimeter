#!/usr/bin/env python3
"""Compare the complete reviewed documentary runtime graph with its inventory.

Stored original functions are explicit reviewed cuts, never automatic cuts by
module or name pattern. A direct invocation of such an adapter is rejected.
Static initializer bodies are followed as well as captured closures. The
inventory is a review record; this script has no refresh or acceptance mode.
It supplements whole-packet Lean proofs and dynamic producer/reader review.
"""
import hashlib
import json
from pathlib import Path
import re
import runpy
import sys

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parent.parent
INVENTORY = ROOT / 'scripts/documentary-d2-runtime-inventory.json'
NAMED_ABI = 'rp_documentary_owned_trail'
SYMBOL = re.compile(r'\b(?:(?:_init_)?(?:l|lp)_\w+|rp_documentary_owned_trail)\b')
PACKAGE = 'lp_relational_x2dperimeter_'
FORBIDDEN = (
    'EndogenousDecomposition_causalStateOfThreadedState',
    'EndogenousDecomposition_causalStageOfThreadedStage',
    'EndogenousDecomposition_constructStage', 'ConstitutiveGeneration_iteratedHistory',
    'SAT_distinctGrowingDiscoveryFormula', 'PortableAssignment_interpret',
    'TransportCode_eval', 'Deduction_evaluate', 'Program_step', 'Program_execute',
    'ControlMasterHead_continueCode', 'ControlMasterHead_prefixOperation',
    'Control_execute', 'ControlHistorical_execute', 'ControlAdministration_executeCode',
    'ControlRunner_execute', 'ControlCompactExecution_specification',
    'ControlRunner_Tape_labels', 'ControlRunner_Tape_cost',
    'Resources_Support_read', 'Resources_read',
    'ControlDeferred_referenceCode', 'ControlBindingReader_recipeReferenceReader',
    'l_List_append', 'l_List_length',
)


def short(name):
    return name.replace(PACKAGE, '')


def body_hash(body):
    return hashlib.sha256(body.replace('\r\n', '\n').encode()).hexdigest()


def check_fingerprints(current, expected):
    if current != expected:
        added = sorted(set(current) - set(expected))
        removed = sorted(set(expected) - set(current))
        changed = sorted(name for name in set(current) & set(expected)
                         if current[name] != expected[name])
        raise ValueError('Runtime review reopened: added=' + str(added[:8]) +
                         ', removed=' + str(removed[:8]) + ', changed=' + str(changed[:8]))


def walk(functions, roots, cuts, contextual):
    seen, external, stored, fixed = set(), set(), set(), set()
    stack = list(roots)
    while stack:
        name = stack.pop()
        if name in seen:
            continue
        if name not in functions:
            initializer = '_init_' + name
            if initializer in functions:
                stack.append(initializer)
            else:
                external.add(name)
            continue
        seen.add(name)
        if short(name) in cuts:
            stored.add(name)
            continue
        if short(name) in contextual:
            fixed.add(name)
            continue
        body = functions[name]
        for child in set(SYMBOL.findall(body)) - {name}:
            if short(child) in cuts and re.search(re.escape(child) + r'\s*\(', body):
                raise ValueError('Stored original function invoked directly: ' + name + ' -> ' + child)
            stack.append(child)
    return seen, external, stored, fixed


def validate_nil_quote_context(functions, seen, contextual, select):
    """The only native Ports.read use is quotationProducer's received nil ports.

    This is a site-specific fixed constructor boundary, not permission to
    invoke arbitrary producer arguments or native variable-length reads.
    Whole-body fingerprints also reopen review when any of these terms change.
    """
    ports = select(functions, 'Resources_Ports_read___redArg')
    if set(contextual) != {short(ports)}:
        raise ValueError('Unexpected contextual native boundary')
    arguments = select(functions, 'Resources_Producer_arguments___redArg')
    extension = select(functions, 'Resources_Support_Extension_produced___redArg')
    caller = select(functions, 'ControlAssemblyExecution_quotationCode___redArg___lam__3')
    producer = select(functions, 'Deduction_quotationProducer___redArg')

    def callers(child):
        return {name for name in seen if name != child and
                re.search(re.escape(child) + r'\s*\(', functions[name])}

    if callers(ports) != {arguments} or callers(arguments) != {extension}:
        raise ValueError('Native argument reader escaped the fixed quotation context')
    if callers(extension) != {caller}:
        raise ValueError('Native produced extension gained an unreviewed producer')
    body = functions[caller]
    produced = re.findall(r'(v_\w+)\s*=\s*' + re.escape(producer) + r'\([^;]+\);', body)
    calls = re.findall(re.escape(extension) + r'\(([^;]+)\);', body)
    if len(produced) != 1 or len(calls) != 1 or calls[0].split(',')[-1].strip() != produced[0]:
        raise ValueError('Produced extension does not receive the same quotation producer')
    factory = functions[producer]
    nils = re.findall(r'(v_\w+)\s*=\s*lean_box\(0\);', factory)
    if len(nils) != 2 or any(not re.search(
            r'lean_ctor_set\(v_\w+,\s*' + str(index) + r',\s*' + re.escape(value) + r'\);', factory)
            for index, value in enumerate(nils)):
        raise ValueError('Quotation producer no longer has fixed empty input kinds/ports')
    # The nil branch returns PUnit without inspecting resources; the other
    # branch remains in the frozen body, but is unreachable from this site.
    nil_branch = re.search(r'if \(lean_obj_tag\((v_\w+)\) == 0\)\s*\{([^{}]*)\}', functions[ports])
    if nil_branch is None or not re.search(r'(v_\w+)\s*=\s*lean_box\(0\);\s*return \1;', nil_branch[2]):
        raise ValueError('Native nil-ports terminal changed')
    if re.search(r'\b(?:l|lp)_\w+\s*\(|lean_apply_\d+\s*\(', nil_branch[2]):
        raise ValueError('Nil-ports branch gained an unclassified invocation')


def validate_named_abi(functions, seen, plan):
    boundaries = plan.get('named_abi_boundaries', {})
    if set(boundaries) != {NAMED_ABI}:
        raise ValueError('Named ABI boundary must be explicitly reviewed, exactly one known name')
    entry = boundaries[NAMED_ABI]
    if not entry.get('reason') or not entry.get('payment'):
        raise ValueError('Named ABI boundary lacks actual classification/payment')
    if NAMED_ABI not in seen or NAMED_ABI not in functions:
        raise ValueError('Actual public owned-pointer helper not followed by graph')
    body = functions[NAMED_ABI]
    # This monomorphic export is an executed immediate pointer transfer. It
    # may never acquire a callback, traversal, allocation or child operation.
    immediate = r'return v_trail_\d+_;'
    plain = r'\{\s*' + immediate + r'\s*\}'
    labeled = r'\{\s*_start:\s*\{\s*' + immediate + r'\s*\}\s*\}'
    if not (re.fullmatch(plain, body) or re.fullmatch(labeled, body)):
        raise ValueError('Reviewed owned-pointer ABI gained work or substituted data')
    sites = sorted(short(name) for name, source in functions.items()
                   if re.search(r'\brp_documentary_owned_trail\s*\(', source))
    actual_sites = sorted(short(name) for name in seen
                         if re.search(r'\brp_documentary_owned_trail\s*\(', functions[name]))
    if sites != entry['compiled_sites'] or actual_sites != entry['actual_public_sites']:
        raise ValueError('Named owned-pointer ABI gained or changed a compiled/public call site')


def inspect(functions, plan, select):
    if plan.get('schema') != 1 or plan.get('review_status') != 'reviewed':
        raise ValueError('Runtime inventory has no completed independent review')
    roots = [select(functions, suffix) for suffix in plan['roots']]
    cuts = plan['stored_original_functions']
    contextual = plan['contextual_fixed_functions']
    if any(not reason for reason in cuts.values()):
        raise ValueError('Stored boundary lacks its concrete producer/consumer reason')
    if any(not reason for reason in contextual.values()):
        raise ValueError('Contextual fixed boundary lacks its reviewed input invariant')
    seen, external, stored, fixed = walk(functions, roots, cuts, contextual)
    validate_nil_quote_context(functions, seen, contextual, select)
    validate_named_abi(functions, seen, plan)
    # Once cells are metadata, not functions. No other missing runtime symbol
    # may be silently promoted to a primitive.
    unexplained = {short(name) for name in external if not name.endswith('_once')}
    if unexplained != set(plan['external_terminals']):
        raise ValueError('Unclassified external symbol: ' + str(sorted(unexplained)))
    current = {}
    for name in seen:
        if name in stored:
            continue
        body = functions[name]
        if name not in fixed and any(re.search(r'\b\w*' + re.escape(part) + r'(?:___\w+)?\s*\(', body)
               for part in FORBIDDEN):
            raise ValueError('Uncontrolled producer/read/traversal in actual graph: ' + name)
        current[short(name)] = body_hash(body)
    expected = plan['reviewed_bodies']
    check_fingerprints(current, expected)
    check_fingerprints({short(name): body_hash(functions[name]) for name in stored},
                       plan['stored_body_fingerprints'])
    if {short(name) for name in fixed} != set(contextual):
        raise ValueError('Contextual fixed boundary changed')
    if {short(name) for name in stored} != set(plan['reached_stored_functions']):
        raise ValueError('Stored original boundaries changed')
    ffi = {}
    for name in sorted(seen - stored - fixed):
        for primitive in set(re.findall(r'\b(lean_\w+)\s*\(', functions[name])):
            ffi.setdefault(primitive, []).append(short(name))
    if any(not entry.get('reason') for entry in plan['ffi_boundaries'].values()):
        raise ValueError('FFI boundary has no explicit reviewed classification')
    expected_ffi = {name: entry['sites'] for name, entry in plan['ffi_boundaries'].items()}
    if ffi != expected_ffi:
        raise ValueError('Unclassified FFI primitive or changed primitive site')
    return seen, stored, roots


def main():
    plan = json.loads(INVENTORY.read_text(encoding='utf-8'))
    helper = runpy.run_path(str(ROOT / 'scripts/check-agent-codegen.py'))
    functions = {}
    for path in sorted((ROOT / '.lake/build/ir').rglob('*.c')):
        functions.update(helper['bodies_with_objects'](path.read_text(encoding='utf-8')))
    complete = runpy.run_path(str(ROOT / 'scripts/check-documentary-reader-payment-codegen.py'))
    data_C = ROOT / '.lake/build/ir/Tests/LocalAlignment/DocumentaryControlCompactData.c'
    named = complete['bodies'](data_C.read_text(encoding='utf-8'))
    if NAMED_ABI not in named:
        raise ValueError('Declared named ABI helper definition missing from actual C')
    functions[NAMED_ABI] = named[NAMED_ABI]
    seen, stored, roots = inspect(functions, plan, helper['shared']['select'])
    mutations = 0
    # Every reviewed body must reopen review when edited, including a body in
    # an unnamed helper reached only through another module or a static datum.
    for name in seen:
        expected = plan['stored_body_fingerprints'] if name in stored else plan['reviewed_bodies']
        current = dict(expected)
        current[short(name)] = body_hash(functions[name] + ' changed_reviewed_runtime_body;')
        try:
            check_fingerprints(current, expected)
        except ValueError:
            mutations += 1
            continue
        raise ValueError('Changed reviewed body accepted: ' + name)
    for name in roots:
        current = dict(functions)
        current['lp_unreviewed_helper'] = '{ return lean_box(0); }'
        current[name] += ' lp_unreviewed_helper();'
        try:
            inspect(current, plan, helper['shared']['select'])
        except ValueError:
            mutations += 1
            continue
        raise ValueError('New helper accepted: ' + name)
    select = helper['shared']['select']
    producer = select(functions, 'Deduction_quotationProducer___redArg')
    caller = select(functions, 'ControlAssemblyExecution_quotationCode___redArg___lam__3')
    arguments = select(functions, 'Resources_Producer_arguments___redArg')
    extension = select(functions, 'Resources_Support_Extension_produced___redArg')
    nils = re.findall(r'(v_\w+)\s*=\s*lean_box\(0\);', functions[producer])
    context_mutations = [
        (producer, functions[producer].replace(nils[1] + ' = lean_box(0);', nils[1] + ' = lean_box(1);', 1)),
        (caller, re.sub(r'(' + re.escape(extension) + r'\([^;]+, )v_\w+(\);)',
                        r'\1v_substituted_producer_777_\2', functions[caller])),
        (caller, functions[caller] + ' ' + arguments + '(v_unreviewed_777_, v_resources_777_);'),
    ]
    for name, body in context_mutations:
        if body == functions[name]:
            raise ValueError('Context mutation did not alter the reviewed body')
        current = dict(functions)
        current[name] = body
        try:
            validate_nil_quote_context(current, seen, plan['contextual_fixed_functions'], select)
        except ValueError:
            mutations += 1
            continue
        raise ValueError('Changed fixed quotation context accepted')
    for original in stored:
        current = dict(functions)
        current[roots[0]] += ' ' + original + '();'
        try:
            walk(current, roots, plan['stored_original_functions'], plan['contextual_fixed_functions'])
        except ValueError:
            mutations += 1
            continue
        raise ValueError('Direct invocation of stored original accepted: ' + original)
    for substitute in ['{ return lean_box(0); }',
                       '{ lean_apply_1(v_unpaid_777_, v_unit_777_); return v_trail_777_; }',
                       '{ return rp_documentary_owned_trail(v_trail_777_); }']:
        current = dict(functions)
        current[NAMED_ABI] = substitute
        try:
            inspect(current, plan, select)
        except ValueError:
            mutations += 1
            continue
        raise ValueError('Changed executed named ABI helper accepted')
    current = dict(functions)
    current[roots[0]] += ' rp_documentary_owned_trail(v_unpaid_777_);'
    try:
        inspect(current, plan, select)
    except ValueError:
        mutations += 1
    else:
        raise ValueError('Unclassified/unpaid named ABI helper site accepted')
    print(f'DOCUMENTARY_D2_CLOSURE_CODEGEN_OK: {len(seen) - len(stored)} reviewed bodies; '
          f'{len(stored)} explicit original-data boundaries; {mutations} textual mutations rejected; '
          f'{len(plan["ffi_boundaries"])} classified FFI symbols; '
          'static initializers/captured controlled closures followed; fixed quotation context tested; no refresh mode; '
          'one explicitly named monomorphic ABI followed and site-checked; '
          'dynamic sharing and whole-packet obligations reviewed separately')


if __name__ == '__main__':
    try:
        main()
    except (OSError, ValueError, KeyError) as error:
        print('DOCUMENTARY_D2_CLOSURE_CODEGEN_ERROR: ' + str(error), file=sys.stderr)
        sys.exit(1)
