#!/usr/bin/env python3
"""Finite generated-C regressions for the agent bridge provenance checker."""
from __future__ import annotations

import contextlib
import io
import runpy
from pathlib import Path

from agent_codegen_provenance import ProvenanceError, bridge_provenance
from unified_codegen_analysis import add_static_objects, parameters


ROOT = Path(__file__).resolve().parent.parent


def program(event_body, *, next_body=None, static_helper=False):
    next_body = next_body or '''
lean_object* r; lean_object* result;
r = l_rich(a, b, source, request);
result = lean_ctor_get(r, 0);
return result;
'''
    static = '''
LEAN_EXPORT lean_object* l_identity(lean_object* value){ return value; }
static const lean_closure_object l_identity_closure_value = {
  .m_fun = (void*)l_identity, .m_arity = 1, .m_num_fixed = 0, .m_objs = {}
};
static const lean_object* l_identity_closure =
  (const lean_object*)&l_identity_closure_value;
''' if static_helper else ''
    return '''
LEAN_EXPORT lean_object* l_rich(lean_object* a, lean_object* b,
  lean_object* source, lean_object* request){ return lean_box(0); }
LEAN_EXPORT lean_object* l_foreign(lean_object* source, lean_object* request){ return source; }
''' + static + '''
LEAN_EXPORT lean_object* l_next(lean_object* a, lean_object* b,
  lean_object* source, lean_object* request){
''' + next_body + '''
}
LEAN_EXPORT lean_object* l_event(lean_object* a, lean_object* b,
  lean_object* source, lean_object* request){
''' + event_body + '''
}
LEAN_EXPORT lean_object* l_bridge(lean_object* a, lean_object* b){
  lean_object* next; lean_object* event; lean_object* out;
  next = lean_alloc_closure((void*)l_next, 4, 2);
  lean_closure_set(next, 0, a); lean_closure_set(next, 1, b);
  event = lean_alloc_closure((void*)l_event, 4, 2);
  lean_closure_set(event, 0, a); lean_closure_set(event, 1, b);
  out = lean_alloc_ctor(0, 9, 0);
  lean_ctor_set(out, 0, next); lean_ctor_set(out, 1, next);
  lean_ctor_set(out, 2, next); lean_ctor_set(out, 3, next);
  lean_ctor_set(out, 4, next); lean_ctor_set(out, 5, event);
  lean_ctor_set(out, 6, next); lean_ctor_set(out, 7, next);
  lean_ctor_set(out, 8, next); return out;
}
'''


DIRECT = '''
lean_object* r; lean_object* result;
r = l_rich(a, b, source, request);
result = lean_ctor_get(r, 1);
return result;
'''

REBUILT = '''
lean_object* r; lean_object* event; lean_object* productions; lean_object* message;
lean_object* alias; lean_object* out;
r = l_rich(a, b, source, request); event = lean_ctor_get(r, 1);
productions = lean_ctor_get(event, 0); message = lean_ctor_get(event, 1);
out = lean_alloc_ctor(0, 2, 0); alias = out;
lean_ctor_set(alias, 0, productions); lean_ctor_set(out, 1, message); return out;
'''

OWNERSHIP_REBUILT = '''
lean_object* r; lean_object* event;
r = l_rich(a, b, source, request); event = lean_ctor_get(r, 1);
if (lean_is_exclusive(event)) { return event; } else {
  lean_object* productions; lean_object* message; lean_object* out;
  productions = lean_ctor_get(event, 0); message = lean_ctor_get(event, 1);
  out = lean_alloc_ctor(0, 2, 0); lean_ctor_set(out, 0, productions);
  lean_ctor_set(out, 1, message); return out;
}
'''

MIXED = '''
lean_object* r; lean_object* event; lean_object* productions; lean_object* message;
lean_object* out;
r = l_rich(a, b, source, request); event = lean_ctor_get(r, 1);
productions = lean_ctor_get(event, 0); message = l_foreign(source, request);
out = lean_alloc_ctor(0, 2, 0); lean_ctor_set(out, 0, productions);
lean_ctor_set(out, 1, message); return out;
'''

BRANCH_MIXED = '''
lean_object* r; lean_object* event;
r = l_rich(a, b, source, request); event = lean_ctor_get(r, 1);
if (lean_obj_tag(request) == 0) { return event; } else {
  lean_object* productions; lean_object* message; lean_object* out;
  productions = lean_ctor_get(event, 0); message = l_foreign(source, request);
  out = lean_alloc_ctor(0, 2, 0); lean_ctor_set(out, 0, productions);
  lean_ctor_set(out, 1, message); return out;
}
'''

STATIC_HELPER = '''
lean_object* r; lean_object* event; lean_object* result;
r = l_rich(a, b, source, request); event = lean_ctor_get(r, 1);
result = lean_apply_1(l_identity_closure, event); return result;
'''

WRONG_ARGUMENT = '''
lean_object* r; lean_object* result;
r = l_rich(a, b, source, source); result = lean_ctor_get(r, 1); return result;
'''

WRONG_NEXT = '''
lean_object* r; lean_object* state; lean_object* rebuilt;
r = l_rich(a, b, source, request); state = lean_ctor_get(r, 0);
rebuilt = l_foreign(source, request); return rebuilt;
'''


def self_test(bodies, reachable):
    variants = (
        ('direct', DIRECT, None, False, True),
        ('rebuilt-event-with-alias', REBUILT, None, False, True),
        ('ownership-branch-exact-reconstruction', OWNERSHIP_REBUILT, None, False, True),
        ('static-transparent-helper', STATIC_HELPER, None, True, True),
        ('projected-message', MIXED, None, False, False),
        ('one-bad-branch', BRANCH_MIXED, None, False, False),
        ('wrong-rich-argument', WRONG_ARGUMENT, None, False, False),
        ('independent-source-next', DIRECT, WRONG_NEXT, False, False),
    )
    for name, event_body, next_body, static_helper, permitted in variants:
        text = '\n'.join(line.lstrip() for line in
                         program(event_body, next_body=next_body,
                                 static_helper=static_helper).splitlines())
        functions = bodies(text)
        add_static_objects(functions, text)
        params = parameters([text])
        try:
            bridge_provenance(functions, params, reachable, 'l_bridge', 'l_rich')
        except ProvenanceError:
            if permitted:
                raise
        else:
            if not permitted:
                raise ProvenanceError('invalid provenance accepted: ' + name)
    print('AGENT_PROVENANCE_SELFTEST_OK: exact returns, reconstruction, aliases, '
          'branches, captures and both rich fields')


def main():
    shared = runpy.run_path(str(ROOT / 'scripts/check-unified-codegen.py'))
    with contextlib.redirect_stdout(io.StringIO()):
        self_test(shared['bodies'], shared['reachable'])
    print('AGENT_PROVENANCE_SELFTEST_OK')


if __name__ == '__main__':
    main()
