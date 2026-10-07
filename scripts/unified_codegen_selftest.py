"""Regression cases for the bounded C analysis, not scientific benchmarks."""
from unified_codegen_analysis import Analysis, Value, parameters, add_static_objects


def self_test(bodies, reachable, owned_symbol):
    def model(source):
        source = '\n'.join(line.lstrip() for line in source.splitlines())
        functions = bodies(source)
        add_static_objects(functions, source)
        return functions, parameters([source])

    producer = 'LEAN_EXPORT lean_object* l_engine(lean_object* x){ return x; }\n'
    def count(source, expected):
        functions, params = model(producer + source)
        _, low, high = Analysis(functions, params, reachable, target='l_engine').run('l_entry', [Value()])
        if (low, high) != expected:
            raise ValueError(f'Application self-test expected {expected}, obtained {(low, high)}')

    count('''LEAN_EXPORT lean_object* l_entry(lean_object* x){
      lean_object* y; lean_object* pair;
      y = l_engine(x); pair = lean_alloc_ctor(0, 2, 0);
      lean_ctor_set(pair, 0, y); lean_ctor_set(pair, 1, y); return pair;
    }''', (1, 1))
    count('''LEAN_EXPORT lean_object* l_entry(lean_object* x){
      if (lean_obj_tag(x) == 0) { return l_engine(x); }
      else { return l_engine(x); }
    }''', (1, 1))
    count('''LEAN_EXPORT lean_object* l_helper(lean_object* f, lean_object* x){
      lean_object* a; lean_object* b;
      a = lean_apply_1(f, x); b = lean_apply_1(f, a); return b;
    }
    LEAN_EXPORT lean_object* l_entry(lean_object* x){
      lean_object* f; lean_object* alias;
      f = lean_alloc_closure((void*)l_engine, 1, 0); alias = f;
      return l_helper(alias, x);
    }''', (2, 2))
    count('''static const lean_closure_object l_operation_value = {
      .m_fun = (void*)l_engine, .m_num_fixed = 0};
    LEAN_EXPORT lean_object* l_entry(lean_object* x){ return lean_apply_1(l_operation, x); }''', (1, 1))
    count('''static const lean_closure_object l_operation_value = {
      .m_fun = (void*)l_engine, .m_num_fixed = 0};
    static const lean_ctor_object l_packet_value = {.m_objs = {&l_operation_value}};
    LEAN_EXPORT const lean_object* l_packet = (const lean_object*)&l_packet_value;
    LEAN_EXPORT lean_object* l_entry(lean_object* x){
      lean_object* f; f = lean_ctor_get(l_packet, 0); return lean_apply_1(f, x);
    }''', (1, 1))
    count('''LEAN_EXPORT lean_object* l_entry(lean_object* x){
      if (lean_obj_tag(x) == 0) { return x; } else { return l_engine(x); }
    }''', (0, 1))
    functions, params = model(producer + '''LEAN_EXPORT lean_object* l_entry(lean_object* x){
      lean_object* f; f = lean_ctor_get(x, 0); return lean_apply_1(f, x);
    }''')
    try:
        # A known sensitive function plus an unresolved applied callback.
        functions['l_entry'] = functions['l_entry'].replace('return lean_apply_1', 'l_engine(x); return lean_apply_1')
        Analysis(functions, params, reachable, target='l_engine').run('l_entry', [Value()])
    except ValueError as error:
        if 'Unresolved applied closure' not in str(error):
            raise
    else:
        raise ValueError('Unknown applied closure was incorrectly assigned zero effects')

    def capture(source, **configuration):
        functions, params = model(source)
        return Analysis(functions, params, reachable, capture=True, **configuration).run(
            'l_entry', [Value(frozenset({'archive'}))])[0].retained()

    transient = '''LEAN_EXPORT lean_object* l_entry(lean_object* archive){
      lean_object* ignored; lean_object* clean;
      ignored = lean_ctor_get(archive, 0); clean = lean_box(0); return clean;
    }'''
    if capture(transient):
        raise ValueError('Transient archive read mistaken for retention')
    retained = '''LEAN_EXPORT lean_object* l_reader(lean_object* archive, lean_object* query){ return query; }
    LEAN_EXPORT lean_object* l_entry(lean_object* archive){
      lean_object* reader; reader = lean_alloc_closure((void*)l_reader, 2, 1);
      lean_closure_set(reader, 0, archive); return reader;
    }'''
    if 'archive' not in capture(retained):
        raise ValueError('Nested reader environment lost its archive capture')
    loop = '''LEAN_EXPORT lean_object* l_reader(lean_object* archive, lean_object* query){ return query; }
    LEAN_EXPORT lean_object* l_entry(lean_object* archive){
      lean_object* items; lean_object* result;
      items = lean_box(0); result = lean_box(0);
      again: {
        if (lean_obj_tag(items) == 0) { return result; }
        else {
          lean_object* reader; lean_object* cell;
          reader = lean_alloc_closure((void*)l_reader, 2, 1);
          lean_closure_set(reader, 0, archive);
          cell = lean_alloc_ctor(1, 2, 0);
          lean_ctor_set(cell, 0, reader); lean_ctor_set(cell, 1, result);
          result = cell; items = lean_ctor_get(items, 1); goto again;
        }
      }
    }'''
    if 'archive' not in capture(loop):
        raise ValueError('Reader-list loop lost the accumulated environment capture')
    trusted = '''LEAN_EXPORT lean_object* l_Authoritative_target___redArg(lean_object* archive){ return lean_box(0); }
    LEAN_EXPORT lean_object* l_Authoritative_project(lean_object* archive){ return lean_box(0); }
    LEAN_EXPORT lean_object* l_Authoritative_result___redArg(lean_object* archive){ return archive; }
    '''
    boundaries = {'l_Authoritative_target___redArg': 'produced',
                  'l_Authoritative_project': 'live',
                  'l_Authoritative_result___redArg': 'archive'}
    for symbol, policy in boundaries.items():
        direct = trusted + f'''LEAN_EXPORT lean_object* l_entry(lean_object* archive){{
          return {symbol}(archive);
        }}'''
        indirect = trusted + f'''LEAN_EXPORT lean_object* l_entry(lean_object* archive){{
          lean_object* f; lean_object* alias;
          f = lean_alloc_closure((void*){symbol}, 1, 0); alias = f;
          return lean_apply_1(alias, archive);
        }}'''
        for case in (direct, indirect):
            observed = capture(case, capture_boundaries=boundaries)
            if ('archive' in observed) != (policy == 'archive'):
                raise ValueError('Exact boundary policy differs for direct/closure call: ' + symbol)
    # Names must never grant the privileges of a trusted production selector.
    # These match both the old substring rule and the old live suffix rule.
    for lookalike in ('l_ReviewExecutedChainNormalization_target___redArg',
                      'l_ReviewLiveContinuation_project'):
        source = trusted + f'''LEAN_EXPORT lean_object* {lookalike}(lean_object* archive){{ return archive; }}
        LEAN_EXPORT lean_object* l_entry(lean_object* archive){{ return {lookalike}(archive); }}'''
        if 'archive' not in capture(source, capture_boundaries=boundaries):
            raise ValueError('Lookalike helper erased archive tags: ' + lookalike)
        closure = trusted + f'''LEAN_EXPORT lean_object* {lookalike}(lean_object* archive){{ return archive; }}
        LEAN_EXPORT lean_object* l_entry(lean_object* archive){{
          lean_object* f; f = lean_alloc_closure((void*){lookalike}, 1, 0);
          return lean_apply_1(f, archive);
        }}'''
        if 'archive' not in capture(closure, capture_boundaries=boundaries):
            raise ValueError('Lookalike closure erased archive tags: ' + lookalike)
    functions, params = model(trusted)
    symbol = 'l_Authoritative_target___redArg'
    module = 'Authoritative.c'
    owners = {symbol: {module}}
    if owned_symbol(functions, params, owners, 'l_', 'Authoritative.target', module,
                    '___redArg') != symbol:
        raise ValueError('Exact owned-symbol resolution failed')
    for wrong in ({symbol: {'Foreign.c'}}, {symbol: {module, 'Foreign.c'}}, {}):
        try:
            owned_symbol(functions, params, wrong, 'l_', 'Authoritative.target', module, '___redArg')
        except ValueError:
            pass
        else:
            raise ValueError('Foreign or ambiguous boundary ownership was accepted')
    for configuration in ({'l_Missing': 'produced'}, {symbol: 'unknown'}):
        try:
            Analysis(functions, params, reachable, capture=True, capture_boundaries=configuration)
        except ValueError:
            pass
        else:
            raise ValueError('Missing or invalid capture boundary was accepted')
    try:
        Analysis(functions, params, reachable, capture=True,
                 capture_boundaries={symbol: 'produced'}).run(symbol, [])
    except ValueError:
        pass
    else:
        raise ValueError('Capture boundary with wrong arity was accepted')
    print('CODEGEN_ANALYSIS_SELFTEST_OK: sharing, branches, closures, retention, exact boundaries and artifact ownership')
