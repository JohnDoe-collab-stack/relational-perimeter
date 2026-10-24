#!/usr/bin/env python3
"""Compiled-agent dependency and sharing checks, not a cost/heap theorem.

Reuse the existing local C-IR parser. No runtime scientific dependency is added.
"""
from pathlib import Path
import re
import runpy
import sys
from unified_codegen_analysis import Analysis, Value, parameters, split_arguments

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parent.parent
shared = runpy.run_path(str(ROOT / "scripts/check-unified-codegen.py"))


class AgentAnalysis(Analysis):
    """One structural unfolding, with explicitly named recursive tails cut.

    This does not bound a whole advance/executeAll. The Lean recursion and
    iteration-count laws are checked separately. New helper cycles fail closed.
    """
    def __init__(self, *args, unfolds=(), boundaries=(), **kwargs):
        super().__init__(*args, **kwargs)
        self.unfolds, self.boundaries = set(unfolds), set(boundaries)

    def run(self, name, arguments):
        if name in self.boundaries:
            return Value(), 0, 0
        if name in self.unfolds and any(frame[0] == name for frame in self.stack):
            return Value(), 0, 0
        return super().run(name, arguments)

    def global_value(self, name):
        body = self.functions.get(name, '')
        fields = re.search(r'\.m_objs\s*=\s*\{(.*?)\}', body, re.S)
        if fields and '.m_fun' not in body:
            result = {}
            for index, item in enumerate(split_arguments(fields[1])):
                symbols = re.findall(r'\b(?:l|lp)_\w+\b', item)
                if len(symbols) == 1 and symbols[0] in self.functions:
                    result[index] = self.global_value(symbols[0])
                elif not symbols and re.fullmatch(r'[()\s\d<>|*a-z_]+', item):
                    # A statically boxed immediate has no closure or callee.
                    if 'lean_object' not in item or 'size_t' not in item or '<< 1' not in item:
                        raise ValueError('Unresolved static immediate: ' + item)
                    result[index] = Value()
                else:
                    raise ValueError('Unresolved static producer field: ' + item)
            return Value(fields=result)
        return super().global_value(name)


def applications(functions, compiled_parameters, entry, target, maximum, *, unfolds=(), boundaries=()):
    # Remove only generated casts around a named static object, preserving its
    # identity and all applications. This is not a producer boundary.
    normalized = {name: re.sub(r'\(\(lean_object\*\)\(((?:l|lp)_\w+)\)\)', r'\1', body)
                  for name, body in functions.items()}
    analysis = AgentAnalysis(normalized, compiled_parameters, shared['reachable'], target=target,
                             unfolds=unfolds, boundaries=boundaries)
    _, low, high = analysis.run(entry, [Value() for _ in compiled_parameters[entry]])
    if high != maximum:
        raise ValueError(f'{entry}: expected maximum {maximum} applications of {target}, found [{low},{high}]')
    print(f'AGENT_APPLICATIONS_OK {entry}: {target}=[{low},{high}]; explicit unfolding scope')


def recursive_tail_applications(functions, compiled_parameters, entry):
    # Unfold the current node under a fresh analysis-only name, then count
    # applications of the real recursive tail, including through helpers.
    alias = entry + '__one_unfolding_check'
    if alias in functions:
        raise ValueError('Analysis entry alias already exists')
    augmented, params = dict(functions), dict(compiled_parameters)
    augmented[alias], params[alias] = functions[entry], compiled_parameters[entry]
    applications(augmented, params, alias, entry, 1)


def forwarded_result(functions, entry, producer, consumer, argument_index):
    """Require the exact object returned by `producer` to reach `consumer`.

    A mere call to the producer is insufficient: a wrapper could call it,
    discard its target field, rebuild an equal canonical object and pass that
    replacement onward.  Generated Lean C names every intermediate object, so
    this check follows the produced occurrence to the selected consumer slot.
    """
    body = functions.get(entry, '')
    produced = re.findall(
        rf'\b((?:v|l|lp)_\w+)\s*=\s*{re.escape(producer)}\s*\(', body)
    if len(produced) != 1:
        raise ValueError(
            f'{entry}: expected one assigned result from {producer}, found {len(produced)}')
    consumer_calls = re.findall(
        rf'{re.escape(consumer)}\s*\((.*?)\)\s*;', body, re.S)
    if len(consumer_calls) != 1:
        raise ValueError(
            f'{entry}: expected one call to {consumer}, found {len(consumer_calls)}')
    arguments = split_arguments(consumer_calls[0])
    if argument_index >= len(arguments):
        raise ValueError(
            f'{entry}: consumer argument {argument_index} is absent')
    normalized = re.sub(r'\(\(lean_object\*\)\(([^()]+)\)\)', r'\1',
                        arguments[argument_index]).strip()
    if normalized != produced[0]:
        raise ValueError(
            f'{entry}: {producer} result {produced[0]} is not consumer '
            f'argument {argument_index}; found {normalized}')
    print(f'AGENT_FORWARDING_OK {entry}: exact {producer} result -> '
          f'{consumer}[{argument_index}]')


def returned_except_payload(functions, entry, producer):
    """Require `entry` to return the payload of the exact `Except` produced.

    This detects the runtime-level bypass where the checker is executed but a
    separately prepared, propositionally equal successor is returned instead
    of the successful payload obtained from that execution.
    """
    body = functions.get(entry, '')
    produced = re.findall(
        rf'\b((?:v|l|lp)_\w+)\s*=\s*{re.escape(producer)}\s*\(', body)
    if len(produced) != 1:
        raise ValueError(
            f'{entry}: expected one assigned Except from {producer}, found {len(produced)}')
    payload = re.findall(
        rf'\b((?:v|l|lp)_\w+)\s*=\s*lean_ctor_get\s*\(\s*'
        rf'{re.escape(produced[0])}\s*,\s*0\s*\)', body)
    if len(payload) != 1:
        raise ValueError(
            f'{entry}: expected the payload of {produced[0]} to be extracted once; '
            f'found {len(payload)}')
    returned = re.findall(r'\breturn\s+((?:v|l|lp)_\w+)\s*;', body)
    if returned != [payload[0]]:
        raise ValueError(
            f'{entry}: expected exact produced payload {payload[0]} to be returned; '
            f'found {returned}')
    print(f'AGENT_EXCEPT_PAYLOAD_OK {entry}: exact {producer} payload returned')


def forwarded_parameter(functions, compiled_parameters, entry, parameter_index,
                        consumer, argument_index):
    """Require one runtime parameter occurrence to reach a consumer slot."""
    params = compiled_parameters.get(entry, ())
    if parameter_index >= len(params):
        raise ValueError(f'{entry}: parameter {parameter_index} is absent')
    body = functions.get(entry, '')
    calls = re.findall(rf'{re.escape(consumer)}\s*\((.*?)\)\s*;', body, re.S)
    if len(calls) != 1:
        raise ValueError(
            f'{entry}: expected one call to {consumer}, found {len(calls)}')
    args = split_arguments(calls[0])
    if argument_index >= len(args):
        raise ValueError(f'{entry}: consumer argument {argument_index} is absent')
    if args[argument_index].strip() != params[parameter_index]:
        raise ValueError(
            f'{entry}: parameter {params[parameter_index]} is not {consumer}'
            f'[{argument_index}]; found {args[argument_index].strip()}')
    print(f'AGENT_PARAMETER_FORWARDING_OK {entry}: parameter '
          f'{parameter_index} -> {consumer}[{argument_index}]')


def forwarded_ctor_field(functions, compiled_parameters, entry, parameter_index,
                         field_index, consumer, argument_index):
    """Require a field read from the received value to reach a consumer slot."""
    params = compiled_parameters.get(entry, ())
    if parameter_index >= len(params):
        raise ValueError(f'{entry}: parameter {parameter_index} is absent')
    body = functions.get(entry, '')
    extracted = re.findall(
        rf'\b([A-Za-z_]\w*)\s*=\s*lean_ctor_get\s*\(\s*'
        rf'{re.escape(params[parameter_index])}\s*,\s*{field_index}\s*\)', body)
    if not extracted:
        raise ValueError(
            f'{entry}: expected an extraction of received field {field_index}, '
            'found none')
    calls = re.findall(rf'{re.escape(consumer)}\s*\((.*?)\)\s*;', body, re.S)
    if len(calls) != 1:
        raise ValueError(
            f'{entry}: expected one call to {consumer}, found {len(calls)}')
    args = split_arguments(calls[0])
    if argument_index >= len(args):
        raise ValueError(f'{entry}: consumer argument {argument_index} is absent')
    forwarded = args[argument_index].strip()
    if forwarded not in extracted:
        raise ValueError(
            f'{entry}: no received field {field_index} in {extracted} is '
            f'{consumer}[{argument_index}]; found {args[argument_index].strip()}')
    print(f'AGENT_FIELD_FORWARDING_OK {entry}: received field {field_index} -> '
          f'{consumer}[{argument_index}]')


def global_field_to_constructor(functions, entry, source, field_index,
                                constructor_fields):
    """Require fields of one returned constructor to share a field of `source`.

    This is the generated-code guard for a named dependent request: the
    predecessor stored in that request must be projected from the preceding
    executed submission, not reconstructed from an equal global agent.
    """
    body = functions.get(entry, '')
    source_values = re.findall(
        rf'\b([A-Za-z_]\w*)\s*=\s*{re.escape(source)}\s*;', body)
    if len(source_values) != 1:
        raise ValueError(
            f'{entry}: expected one material read of {source}, found '
            f'{len(source_values)}')
    extracted = re.findall(
        rf'\b([A-Za-z_]\w*)\s*=\s*lean_ctor_get\s*\(\s*'
        rf'{re.escape(source_values[0])}\s*,\s*{field_index}\s*\)', body)
    if len(extracted) != 1:
        raise ValueError(
            f'{entry}: expected source field {field_index} once, found '
            f'{len(extracted)}')
    returned = re.findall(r'\breturn\s+([A-Za-z_]\w*)\s*;', body)
    if len(returned) != 1:
        raise ValueError(f'{entry}: expected one returned constructor')
    for output_field in constructor_fields:
        assignments = re.findall(
            rf'lean_ctor_set\s*\(\s*{re.escape(returned[0])}\s*,\s*'
            rf'{output_field}\s*,\s*([A-Za-z_]\w*)\s*\)', body)
        if assignments != [extracted[0]]:
            raise ValueError(
                f'{entry}: constructor field {output_field} does not receive '
                f'exact {source} field {field_index}; found {assignments}')
    print(f'AGENT_GLOBAL_FIELD_SHARING_OK {entry}: {source}[{field_index}] '
          f'-> constructor fields {list(constructor_fields)}')


def global_to_constructor(functions, entry, source, constructor_field):
    """Require a constructor field to contain the exact named global value."""
    body = functions.get(entry, '')
    received = re.findall(
        rf'\b([A-Za-z_]\w*)\s*=\s*{re.escape(source)}\s*;', body)
    if len(received) != 1:
        raise ValueError(
            f'{entry}: expected one material read of {source}, found '
            f'{len(received)}')
    returned = re.findall(r'\breturn\s+([A-Za-z_]\w*)\s*;', body)
    if len(returned) != 1:
        raise ValueError(f'{entry}: expected one returned constructor')
    assignments = re.findall(
        rf'lean_ctor_set\s*\(\s*{re.escape(returned[0])}\s*,\s*'
        rf'{constructor_field}\s*,\s*([A-Za-z_]\w*)\s*\)', body)
    if assignments != [received[0]]:
        raise ValueError(
            f'{entry}: constructor field {constructor_field} does not receive '
            f'exact {source}; found {assignments}')
    print(f'AGENT_GLOBAL_CONSTRUCTOR_OK {entry}: exact {source} occurrence '
          f'-> constructor field {constructor_field}')


def result_to_constructor(functions, entry, producer, constructor_field):
    """Require the exact producer result in one returned constructor field."""
    body = functions.get(entry, '')
    produced = re.findall(
        rf'\b([A-Za-z_]\w*)\s*=\s*{re.escape(producer)}\s*\(', body)
    if len(produced) != 1:
        raise ValueError(
            f'{entry}: expected one assigned result from {producer}, found '
            f'{len(produced)}')
    returned = re.findall(r'\breturn\s+([A-Za-z_]\w*)\s*;', body)
    if len(returned) != 1:
        raise ValueError(f'{entry}: expected one returned constructor')
    assignments = re.findall(
        rf'lean_ctor_set\s*\(\s*{re.escape(returned[0])}\s*,\s*'
        rf'{constructor_field}\s*,\s*([A-Za-z_]\w*)\s*\)', body)
    if assignments != [produced[0]]:
        raise ValueError(
            f'{entry}: constructor field {constructor_field} does not receive '
            f'exact {producer} result {produced[0]}; found {assignments}')
    print(f'AGENT_RESULT_CONSTRUCTOR_OK {entry}: exact {producer} result '
          f'-> constructor field {constructor_field}')


def result_field_to_constructor(functions, entry, producer, source_field,
                                constructor_field):
    """Require a field of the exact producer result in the returned value."""
    body = functions.get(entry, '')
    produced = re.findall(
        rf'\b([A-Za-z_]\w*)\s*=\s*{re.escape(producer)}\s*\(', body)
    if len(produced) != 1:
        raise ValueError(
            f'{entry}: expected one assigned result from {producer}, found '
            f'{len(produced)}')
    extracted = re.findall(
        rf'\b([A-Za-z_]\w*)\s*=\s*lean_ctor_get\s*\(\s*'
        rf'{re.escape(produced[0])}\s*,\s*{source_field}\s*\)', body)
    if len(extracted) != 1:
        raise ValueError(
            f'{entry}: expected field {source_field} of {producer} result once, '
            f'found {len(extracted)}')
    returned = re.findall(r'\breturn\s+([A-Za-z_]\w*)\s*;', body)
    if len(returned) != 1:
        raise ValueError(f'{entry}: expected one returned constructor')
    assignments = re.findall(
        rf'lean_ctor_set\s*\(\s*{re.escape(returned[0])}\s*,\s*'
        rf'{constructor_field}\s*,\s*([A-Za-z_]\w*)\s*\)', body)
    if assignments != [extracted[0]]:
        raise ValueError(
            f'{entry}: constructor field {constructor_field} does not receive '
            f'{producer} result field {source_field}; found {assignments}')
    print(f'AGENT_RESULT_FIELD_CONSTRUCTOR_OK {entry}: exact {producer}'
          f'[{source_field}] -> constructor field {constructor_field}')


def parameter_field_to_constructor(functions, compiled_parameters, entry,
                                   parameter_index, source_field,
                                   constructor_field):
    """Require a received parameter field in the returned constructor."""
    params = compiled_parameters.get(entry, ())
    if parameter_index >= len(params):
        raise ValueError(f'{entry}: parameter {parameter_index} is absent')
    body = functions.get(entry, '')
    extracted = re.findall(
        rf'\b([A-Za-z_]\w*)\s*=\s*lean_ctor_get\s*\(\s*'
        rf'{re.escape(params[parameter_index])}\s*,\s*{source_field}\s*\)', body)
    if len(extracted) != 1:
        raise ValueError(
            f'{entry}: expected parameter field {source_field} once, found '
            f'{len(extracted)}')
    returned = re.findall(r'\breturn\s+([A-Za-z_]\w*)\s*;', body)
    if len(returned) != 1:
        raise ValueError(f'{entry}: expected one returned constructor')
    assignments = re.findall(
        rf'lean_ctor_set\s*\(\s*{re.escape(returned[0])}\s*,\s*'
        rf'{constructor_field}\s*,\s*([A-Za-z_]\w*)\s*\)', body)
    if assignments != [extracted[0]]:
        raise ValueError(
            f'{entry}: constructor field {constructor_field} does not receive '
            f'parameter {parameter_index} field {source_field}; found '
            f'{assignments}')
    print(f'AGENT_PARAMETER_FIELD_CONSTRUCTOR_OK {entry}: parameter '
          f'{parameter_index}[{source_field}] -> constructor field '
          f'{constructor_field}')


def forwarded_global(functions, entry, source, consumer, argument_index):
    """Require the exact named global occurrence to reach a consumer slot."""
    body = functions.get(entry, '')
    received = re.findall(
        rf'\b([A-Za-z_]\w*)\s*=\s*{re.escape(source)}\s*;', body)
    if len(received) != 1:
        raise ValueError(
            f'{entry}: expected one material read of {source}, found '
            f'{len(received)}')
    calls = re.findall(rf'{re.escape(consumer)}\s*\((.*?)\)\s*;', body, re.S)
    if len(calls) != 1:
        raise ValueError(
            f'{entry}: expected one call to {consumer}, found {len(calls)}')
    arguments = split_arguments(calls[0])
    if argument_index >= len(arguments):
        raise ValueError(
            f'{entry}: consumer argument {argument_index} is absent')
    normalized = re.sub(r'\(\(lean_object\*\)\(([^()]+)\)\)', r'\1',
                        arguments[argument_index]).strip()
    if normalized != received[0]:
        raise ValueError(
            f'{entry}: exact global {source} occurrence {received[0]} is not '
            f'{consumer}[{argument_index}]; found {normalized}')
    print(f'AGENT_GLOBAL_FORWARDING_OK {entry}: exact {source} occurrence -> '
          f'{consumer}[{argument_index}]')


def select_initializer(functions, suffix):
    """Select one generated initializer, including opaque closed values."""
    matches = [name for name in functions
               if name.startswith('_init_') and name.endswith(suffix)]
    if len(matches) != 1:
        raise ValueError(
            f'Expected one generated initializer for {suffix}; found {matches}')
    return matches[0]


def bodies_with_objects(text):
    result = shared["bodies"](text)
    clean = shared["LITERALS"].sub(lambda match: " " * len(match.group()), text)
    # Producers can be static constructor objects containing operation
    # closures. Following only closure objects misses this intervening record.
    for match in re.finditer(
            r"(?:static|LEAN_EXPORT) const lean_(?:closure|ctor)_object "
            r"((?:l|lp)_\w+)_value\s*=\s*(\{.*?\});", clean, re.S):
        result[match[1] + "_value"] = match[2]
        result[match[1]] = match[2]
    for match in re.finditer(
            r"(?:static|LEAN_EXPORT) const lean_object\* ((?:l|lp)_\w+)\s*=\s*([^;]+);", clean):
        result[match[1]] = match[2]
    return result


def self_test():
    """Finite C-IR regressions of this checker, not runtime experiments."""
    base = 'LEAN_EXPORT lean_object* l_target(lean_object* x){ return x; }\n'
    variants = (
        ('shared-result', '''LEAN_EXPORT lean_object* l_entry(lean_object* x){
          lean_object* y; lean_object* pair;
          y = l_target(x); pair = lean_alloc_ctor(0, 2, 0);
          lean_ctor_set(pair, 0, y); lean_ctor_set(pair, 1, y); return pair;
        }''', (1, 1)),
        ('hidden-double-call', '''LEAN_EXPORT lean_object* l_helper(lean_object* x){
          lean_object* first; first = l_target(x); return l_target(first);
        }
        LEAN_EXPORT lean_object* l_entry(lean_object* x){ return l_helper(x); }''', (2, 2)),
        ('same-closure-twice', '''LEAN_EXPORT lean_object* l_helper(lean_object* f, lean_object* x){
          lean_object* first; first = lean_apply_1(f, x); return lean_apply_1(f, first);
        }
        LEAN_EXPORT lean_object* l_entry(lean_object* x){
          lean_object* f; f = lean_alloc_closure((void*)l_target, 1, 0); return l_helper(f, x);
        }''', (2, 2)),
    )
    for name, body, expected in variants:
        text = '\n'.join(line.lstrip() for line in (base + body).splitlines())
        functions, params = bodies_with_objects(text), parameters([text])
        _, low, high = AgentAnalysis(functions, params, shared['reachable'], target='l_target').run(
            'l_entry', [Value()])
        if (low, high) != expected:
            raise ValueError(f'{name}: expected {expected}, found {(low, high)}')
    forwarded = bodies_with_objects('''
LEAN_EXPORT lean_object* l_producer(lean_object* x){ return x; }
LEAN_EXPORT lean_object* l_consumer(lean_object* x){ return x; }
LEAN_EXPORT lean_object* l_entry(lean_object* x){
  lean_object* v_produced; lean_object* v_result;
  v_produced = l_producer(x); v_result = l_consumer(v_produced); return v_result;
}''')
    forwarded_result(forwarded, 'l_entry', 'l_producer', 'l_consumer', 0)
    substituted = bodies_with_objects('''
LEAN_EXPORT lean_object* l_producer(lean_object* x){ return x; }
LEAN_EXPORT lean_object* l_consumer(lean_object* x){ return x; }
LEAN_EXPORT lean_object* l_canonical(lean_object* x){ return x; }
LEAN_EXPORT lean_object* l_entry(lean_object* x){
  lean_object* v_produced; lean_object* v_replacement; lean_object* v_result;
  v_produced = l_producer(x); v_replacement = l_canonical(x);
  v_result = l_consumer(v_replacement); return v_result;
}''')
    try:
        forwarded_result(substituted, 'l_entry', 'l_producer', 'l_consumer', 0)
    except ValueError:
        pass
    else:
        raise ValueError('Produced-field substitution self-check failed')
    except_payload = bodies_with_objects('''
LEAN_EXPORT lean_object* l_producer(lean_object* x){ return x; }
LEAN_EXPORT lean_object* l_entry(lean_object* x){
  lean_object* v_produced; lean_object* v_payload;
  v_produced = l_producer(x); v_payload = lean_ctor_get(v_produced, 0);
  return v_payload;
}''')
    returned_except_payload(except_payload, 'l_entry', 'l_producer')
    replaced_payload = bodies_with_objects('''
LEAN_EXPORT lean_object* l_producer(lean_object* x){ return x; }
LEAN_EXPORT lean_object* l_replacement(lean_object* x){ return x; }
LEAN_EXPORT lean_object* l_entry(lean_object* x){
  lean_object* v_produced; lean_object* v_payload; lean_object* v_rebuilt;
  v_produced = l_producer(x); v_payload = lean_ctor_get(v_produced, 0);
  v_rebuilt = l_replacement(x); return v_rebuilt;
}''')
    try:
        returned_except_payload(replaced_payload, 'l_entry', 'l_producer')
    except ValueError:
        pass
    else:
        raise ValueError('Except-payload substitution self-check failed')
    received_field = bodies_with_objects('''
LEAN_EXPORT lean_object* l_consumer(lean_object* x){ return x; }
LEAN_EXPORT lean_object* l_entry(lean_object* update){
  lean_object* current; current = lean_ctor_get(update, 0);
  return l_consumer(current);
}''')
    received_params = parameters(['''
LEAN_EXPORT lean_object* l_consumer(lean_object* x){ return x; }
LEAN_EXPORT lean_object* l_entry(lean_object* update){
  lean_object* current; current = lean_ctor_get(update, 0);
  return l_consumer(current);
}'''])
    forwarded_ctor_field(received_field, received_params, 'l_entry', 0, 0,
                         'l_consumer', 0)
    substituted_field = bodies_with_objects('''
LEAN_EXPORT lean_object* l_consumer(lean_object* x){ return x; }
LEAN_EXPORT lean_object* l_global(){ return lean_box(0); }
LEAN_EXPORT lean_object* l_entry(lean_object* update){
  lean_object* current; lean_object* replacement;
  current = lean_ctor_get(update, 0); replacement = l_global();
  return l_consumer(replacement);
}''')
    substituted_params = parameters(['''
LEAN_EXPORT lean_object* l_consumer(lean_object* x){ return x; }
LEAN_EXPORT lean_object* l_global(){ return lean_box(0); }
LEAN_EXPORT lean_object* l_entry(lean_object* update){
  lean_object* current; lean_object* replacement;
  current = lean_ctor_get(update, 0); replacement = l_global();
  return l_consumer(replacement);
}'''])
    try:
        forwarded_ctor_field(substituted_field, substituted_params, 'l_entry',
                             0, 0, 'l_consumer', 0)
    except ValueError:
        pass
    else:
        raise ValueError('Received-predecessor substitution self-check failed')
    received_parameter_text = '''
LEAN_EXPORT lean_object* l_consumer(lean_object* x){ return x; }
LEAN_EXPORT lean_object* l_entry(lean_object* current){
  return l_consumer(current);
}'''
    received_parameter = bodies_with_objects(received_parameter_text)
    received_parameter_params = parameters([received_parameter_text])
    forwarded_parameter(received_parameter, received_parameter_params, 'l_entry',
                        0, 'l_consumer', 0)
    substituted_parameter_text = '''
LEAN_EXPORT lean_object* l_consumer(lean_object* x){ return x; }
LEAN_EXPORT lean_object* l_global(){ return lean_box(0); }
LEAN_EXPORT lean_object* l_entry(lean_object* current){
  lean_object* replacement; replacement = l_global();
  return l_consumer(replacement);
}'''
    substituted_parameter = bodies_with_objects(substituted_parameter_text)
    substituted_parameter_params = parameters([substituted_parameter_text])
    try:
        forwarded_parameter(substituted_parameter, substituted_parameter_params,
                            'l_entry', 0, 'l_consumer', 0)
    except ValueError:
        pass
    else:
        raise ValueError('Received-parameter substitution self-check failed')
    shared_global_field = bodies_with_objects('''
LEAN_EXPORT lean_object* l_submission;
LEAN_EXPORT lean_object* l_entry(){
  lean_object* runtime; lean_object* current; lean_object* request;
  runtime = l_submission; current = lean_ctor_get(runtime, 1);
  request = lean_alloc_ctor(1, 2, 0);
  lean_ctor_set(request, 0, current); lean_ctor_set(request, 1, current);
  return request;
}''')
    global_field_to_constructor(shared_global_field, 'l_entry', 'l_submission',
                                1, (0, 1))
    global_constructed = bodies_with_objects('''
LEAN_EXPORT lean_object* l_source;
LEAN_EXPORT lean_object* l_entry;
static lean_object* _init_l_entry(void){
  lean_object* source; lean_object* result;
  source = l_source; result = lean_alloc_ctor(0, 1, 0);
  lean_ctor_set(result, 0, source); return result;
}''')
    global_to_constructor(global_constructed, '_init_l_entry', 'l_source', 0)
    produced_constructor_text = '''
LEAN_EXPORT lean_object* l_producer(lean_object* x){ return x; }
LEAN_EXPORT lean_object* l_entry(lean_object* received){
  lean_object* produced; lean_object* projectedResult;
  lean_object* projectedParameter; lean_object* result;
  produced = l_producer(received);
  projectedResult = lean_ctor_get(produced, 0);
  projectedParameter = lean_ctor_get(received, 1);
  result = lean_alloc_ctor(0, 3, 0);
  lean_ctor_set(result, 0, produced);
  lean_ctor_set(result, 1, projectedResult);
  lean_ctor_set(result, 2, projectedParameter);
  return result;
}'''
    produced_constructor = bodies_with_objects(produced_constructor_text)
    produced_constructor_params = parameters([produced_constructor_text])
    result_to_constructor(produced_constructor, 'l_entry', 'l_producer', 0)
    result_field_to_constructor(produced_constructor, 'l_entry', 'l_producer',
                                0, 1)
    parameter_field_to_constructor(produced_constructor,
                                   produced_constructor_params, 'l_entry',
                                   0, 1, 2)
    replaced_global_field = bodies_with_objects('''
LEAN_EXPORT lean_object* l_submission;
LEAN_EXPORT lean_object* l_canonical;
LEAN_EXPORT lean_object* l_entry(){
  lean_object* runtime; lean_object* current; lean_object* request;
  runtime = l_submission; current = lean_ctor_get(runtime, 1);
  request = lean_alloc_ctor(1, 2, 0);
  lean_ctor_set(request, 0, l_canonical); lean_ctor_set(request, 1, l_canonical);
  return request;
}''')
    try:
        global_field_to_constructor(replaced_global_field, 'l_entry',
                                    'l_submission', 1, (0, 1))
    except ValueError:
        pass
    else:
        raise ValueError('Submitted-predecessor substitution self-check failed')
    forwarded_global_source = bodies_with_objects('''
LEAN_EXPORT lean_object* l_source;
LEAN_EXPORT lean_object* l_consumer(lean_object* x, lean_object* y){ return y; }
LEAN_EXPORT lean_object* l_entry(){
  lean_object* received; lean_object* result;
  received = l_source; result = l_consumer(lean_box(0), received); return result;
}''')
    forwarded_global(forwarded_global_source, 'l_entry', 'l_source',
                     'l_consumer', 1)
    replaced_global_source = bodies_with_objects('''
LEAN_EXPORT lean_object* l_source;
LEAN_EXPORT lean_object* l_replacement;
LEAN_EXPORT lean_object* l_consumer(lean_object* x, lean_object* y){ return y; }
LEAN_EXPORT lean_object* l_entry(){
  lean_object* received; lean_object* result;
  received = l_source; result = l_consumer(lean_box(0), l_replacement); return result;
}''')
    try:
        forwarded_global(replaced_global_source, 'l_entry', 'l_source',
                         'l_consumer', 1)
    except ValueError:
        pass
    else:
        raise ValueError('Submitted-global forwarding self-check failed')
    print('AGENT_ANALYSIS_SELFTEST_OK: sharing, hidden helper and repeated closure application')


def main():
    self_test()
    probe = bodies_with_objects("""
static const lean_closure_object l_operation_value = {.m_fun = (void*)l_bad};
static const lean_ctor_object l_packet_value = {.m_objs = {&l_operation_value}};
LEAN_EXPORT const lean_object* l_producer = (const lean_object*)&l_packet_value;
LEAN_EXPORT lean_object* l_entry(){ return l_producer; }
LEAN_EXPORT lean_object* l_bad(){ return 0; }
""")
    if "l_bad" not in shared["reachable"](probe, "l_entry"):
        raise ValueError("Static producer/constructor/closure reachability self-test failed")
    functions = {}
    texts = []
    for path in sorted((ROOT / ".lake/build/ir").rglob("*.c")):
        text = path.read_text(encoding="utf-8")
        texts.append(text)
        functions.update(bodies_with_objects(text))
    compiled_parameters = parameters(texts)
    select, absent, calls = (shared[name] for name in ("select", "absent", "calls"))
    executor = select(functions, "Agent_executeRequests")
    request = select(functions, "Agent_executeInput")
    produced = select(functions, "Agent_executeProducedInput")
    step = select(functions, "Agent_step")
    worker = select(functions, "Agent_runSteps")
    decision = select(functions, "Agent_decideReply")
    session = select(functions, "Agent_Session_execute")
    session_produce = select(functions, "Agent_Session_produce")
    session_all = select(functions, "Agent_Session_executeAll")
    of_master = select(functions, "Agent_Session_ofMaster")
    initialize = select(functions, "Agent_initializeAgent")
    public_agent = select(functions, "Agent_publicAgent")
    prepared_memory = select(functions, "Agent_Prepared_memory")
    forbidden = ["Agent_source", "Agent_History_", "MasterResources_", "UnifiedMaster_",
                 "Agent_normalizedRegister", "Agent_start", "Agent_prepare", "Agent_encodeSelection",
                 "Agent_decodeSelection", "ProducedContinuation_Source_", "profileFrontier",
                 "roleProfileFrontier", "roleOccurrenceProfileFrontier",
                 "roleProfileFiniteCarrier", "enumerateRoleOccurrenceProfiles"]
    # The unchanged live engine builds a two-source local output-image
    # readout *after* executing the action. It is not the global role-profile
    # frontier and does not select discovery. Check the discovery entry
    # separately, with the stricter image/readout exclusion.
    for entry in (session, session_produce, session_all, executor, request, produced, worker, step, decision):
        absent(functions, entry, forbidden)
    # Scientific interpretation must read the rich support; it may not call
    # the projected responder. This graph check complements formation types,
    # and is not an observational non-equivalence theorem.
    for entry in (select(functions, 'Agent_sourceProduced'), select(functions, 'Agent_sourcePerform')):
        absent(functions, entry, ['Agent_project', 'Agent_executeInput', 'Agent_executeProducedInput',
                                  'Agent_performCertified'])
    support_read = select(functions, 'Resources_Support_read___redArg')
    for entry in (select(functions, 'Agent_MaterialReading_values___redArg'),
                  select(functions, 'Agent_RegisterRealization_materialRegister___redArg')):
        if support_read not in shared['reachable'](functions, entry):
            raise ValueError('Rich reading no longer reaches the actual support read: ' + entry)
        print('AGENT_RICH_READ_OK ' + entry + ': typed support read, not a projected value list')
    calls(functions, executor, "Agent_executeInput", 1)
    calls(functions, request, "Agent_executeProducedInput", 1)
    calls(functions, worker, "Agent_step", 1)
    calls(functions, step, "LiveContinuation_produce", 1)
    calls(functions, worker, "Agent_runSteps", 1)
    discovery = select(functions, "runThreadedNextDiscovery")
    absent(functions, discovery, forbidden + ["_imageRegime", "_outputRegime", "_frontier"])
    operation = select(functions, "Agent_interactionProducer___lam__1")
    calls(functions, operation, "Agent_performCertified", 1)
    shared["producer_routes"](functions, produced,
        select(functions, "Agent_performCertified"), 1)
    # Initialization may construct its master exactly once; resumption above
    # must never call it. Count the route to the established public factory.
    prepare = select(functions, "Agent_prepare")
    master = select(functions, "UnifiedMaster_publicInstance")
    live = select(functions, "LiveContinuation_produce")
    for entry in (prepare, initialize, public_agent):
        applications(functions, compiled_parameters, entry, master, 1)
    for entry in (of_master, prepared_memory):
        absent(functions, entry, [], exact=(master, prepare))
    for entry, target in ((session, request), (session_produce, produced),
                          (session_all, executor), (request, produced),
                          (produced, select(functions, 'Agent_performCertified')), (step, live)):
        applications(functions, compiled_parameters, entry, target, 1)
    for entry, target in ((executor, request), (worker, step)):
        applications(functions, compiled_parameters, entry, target, 1, unfolds=(entry,))
        recursive_tail_applications(functions, compiled_parameters, entry)
    # The one authorized request route is checked above. No live production
    # may be added beside it by a wrapper or a non-inlined helper.
    for entry, boundary in ((session, request), (session_produce, produced), (session_all, executor)):
        applications(functions, compiled_parameters, entry, live, 0, boundaries=(boundary,))
    # L3/F1: each material branch consumes the exact current checked state and
    # its certificate witnesses in one state-indexed reconfiguration/action
    # producer.  That producer executes one ReconfiguredActionEffect, which
    # stores the action result and therefore cannot reconstruct a detached
    # effect.  The raw reconfiguration must itself call `reconfigure`, so the
    # current system and its exact run reach the compiled installation path.
    learned_producer = select(functions, "NeuralAgent_produceLearnedTransitionData___redArg")
    learned_aligned_action = select(functions,
        "NeuralAgent_executeLearnedAlignedReconfigurationFromState")
    learned_extended_action = select(functions,
        "NeuralAgent_executeLearnedExtendedReconfigurationFromState")
    learned_aligned_raw = select(functions,
        "NeuralAgent_learnedAlignedRawReconfigurationForState")
    learned_extended_raw = select(functions,
        "NeuralAgent_learnedExtendedRawReconfigurationForState")
    learned_aligned_certificate = select(functions,
        "NeuralAgent_learnedAlignedCertifiedReconfigurationForState")
    learned_extended_certificate = select(functions,
        "NeuralAgent_learnedExtendedCertifiedReconfigurationForState")
    produced_certificate = select(functions,
        "NeuralAgent_certifyProducedReconfiguration___redArg")
    reconfigured_action = select(functions,
        "NeuralAgent_executeReconfiguredAction___redArg")
    learned_target = select(functions,
        "NeuralAgent_learnedProducedTransitionTarget___redArg")
    calls(functions, learned_producer,
        "NeuralAgent_executeLearnedAlignedReconfigurationFromState", 1)
    calls(functions, learned_producer,
        "NeuralAgent_executeLearnedExtendedReconfigurationFromState", 1)
    calls(functions, learned_aligned_action,
        "NeuralAgent_executeReconfiguredAction___redArg", 1)
    calls(functions, learned_extended_action,
        "NeuralAgent_executeReconfiguredAction___redArg", 1)
    calls(functions, learned_aligned_raw, "NeuralAgent_reconfigure___redArg", 1)
    calls(functions, learned_extended_raw, "NeuralAgent_reconfigure___redArg", 1)
    forwarded_result(functions, learned_aligned_certificate,
        learned_aligned_raw, produced_certificate, 0)
    forwarded_result(functions, learned_extended_certificate,
        learned_extended_raw, produced_certificate, 0)
    forwarded_result(functions, learned_aligned_action,
        learned_aligned_certificate, reconfigured_action, 3)
    forwarded_result(functions, learned_extended_action,
        learned_extended_certificate, reconfigured_action, 3)
    calls(functions, reconfigured_action, "Agent_executeProducedInput", 1)
    absent(functions, learned_target,
        ["executeLearnedAlignedReconfigurationFromState",
         "executeLearnedExtendedReconfigurationFromState",
         "executeReconfiguredAction", "Agent_executeProducedInput"])
    print("AGENT_LEARNED_SHARING_OK: each material branch consumes its current state in one reconfiguration/action/effect occurrence; the successor only projects that shared occurrence")
    # F2: the successive runtime route must execute the decoder-produced
    # analysis and build the installed checked update from that analysis.  A
    # return of the separately named canonical checked update would recreate
    # the bypass found by the audit even if extensional equality tests passed.
    successive_analysis = select(functions,
        "NeuralAgent_analyzeDecodedLearnedSuccessiveUpdateAtCurrent___redArg")
    successive_decoded = select(functions,
        "NeuralAgent_checkDecodedLearnedExtendedSerializedUpdateAtCurrent___redArg")
    successive_runtime = select(functions,
        "NeuralAgent_checkLearnedRuntimeUpdateAtCurrent___redArg")
    calls(functions, successive_decoded,
        "NeuralAgent_analyzeDecodedLearnedSuccessiveUpdateAtCurrent___redArg", 1)
    calls(functions, successive_decoded,
        "NeuralAgent_buildIncrementalCheckedUpdate___redArg", 1)
    forwarded_parameter(functions, compiled_parameters, successive_decoded,
        0, successive_analysis, 0)
    calls(functions, successive_runtime,
        "NeuralAgent_checkDecodedLearnedExtendedSerializedUpdateAtCurrent___redArg", 1)
    forwarded_parameter(functions, compiled_parameters, successive_runtime,
        0, successive_decoded, 0)
    transition_producer = select(functions,
        "NeuralAgent_produceTransition___redArg")
    structural_graph = select(functions,
        "NeuralAgent_calculatePreCertificateConstitutiveGraph___redArg")
    structural_transports = select(functions,
        "NeuralAgent_calculateLicensedStructuralTransports")
    structural_recomputation = select(functions,
        "NeuralAgent_recomputeAffectedStructuralObservations")
    structural_calculation = select(functions,
        "NeuralAgent_calculateIncrementalStructuralAssembly")
    forwarded_parameter(functions, compiled_parameters, successive_analysis,
        0, transition_producer, 3)
    forwarded_ctor_field(functions, compiled_parameters, successive_analysis,
        0, 1, structural_graph, 1)
    for consumer, artifact_slot, state_slot, certificate_slot in (
            (structural_transports, 2, 4, 5),
            (structural_recomputation, 2, 4, 5),
            (structural_calculation, 2, 4, 5)):
        forwarded_ctor_field(functions, compiled_parameters, successive_analysis,
            0, 1, consumer, artifact_slot)
        forwarded_ctor_field(functions, compiled_parameters, successive_analysis,
            0, 2, consumer, state_slot)
        forwarded_ctor_field(functions, compiled_parameters, successive_analysis,
            0, 3, consumer, certificate_slot)
    absent(functions, successive_decoded, ["learnedExtendedCheckedUpdate"])
    absent(functions, successive_analysis,
        ["LearnedAlignedCheckedAgent", "learnedExtendedCheckedUpdate"])
    # The two named material runtimes must consume the successful payload of
    # `submitUpdate`; equality with a prepared result is not a data route.
    submission_consumer = select(functions,
        "NeuralAgent_acceptedRuntimeSubmissionOfCheck___redArg")
    submit_update = select(functions, "NeuralAgent_submitUpdate___redArg")
    aligned_submission = select_initializer(functions,
        "NeuralAgent_learnedAlignedRuntimeSubmission___closed__0")
    extended_submission = select_initializer(functions,
        "NeuralAgent_learnedExtendedRuntimeSubmission___closed__0")
    aligned_runtime = select_initializer(functions,
        "NeuralAgent_learnedAlignedCertifiedRuntime")
    extended_runtime = select_initializer(functions,
        "NeuralAgent_learnedExtendedCertifiedRuntime")
    submitted_update = select_initializer(functions,
        "NeuralAgent_learnedExtendedSubmittedRuntimeUpdate")
    aligned_submission_values = sorted(set(re.findall(
        r'\b(?:l|lp)_\w*NeuralAgent_learnedAlignedRuntimeSubmission\b',
        functions[submitted_update])))
    if len(aligned_submission_values) != 1:
        raise ValueError(
            f'{submitted_update}: expected one aligned submission value, found '
            f'{aligned_submission_values}')
    aligned_submission_value = aligned_submission_values[0]
    global_field_to_constructor(functions, submitted_update,
        aligned_submission_value, 1, (0, 1))
    returned_except_payload(functions, submission_consumer, submit_update)
    aligned_update_values = sorted(set(re.findall(
        r'\b(?:l|lp)_\w*NeuralAgent_learnedAlignedRuntimeUpdate\b',
        functions[aligned_submission])))
    initial_runtime_values = sorted(set(re.findall(
        r'\b(?:l|lp)_\w*NeuralAgent_learnedInitialCertifiedRuntime\b',
        functions[aligned_submission])))
    submitted_update_values = sorted(set(re.findall(
        r'\b(?:l|lp)_\w*NeuralAgent_learnedExtendedSubmittedRuntimeUpdate\b',
        functions[extended_submission])))
    extended_source_values = sorted(set(re.findall(
        r'\b(?:l|lp)_\w*NeuralAgent_learnedAlignedRuntimeSubmission\b',
        functions[extended_submission])))
    for label, values in (
            ('initial runtime', initial_runtime_values),
            ('aligned update', aligned_update_values),
            ('extended source', extended_source_values),
            ('submitted successive update', submitted_update_values)):
        if len(values) != 1:
            raise ValueError(
                f'named runtime submission: expected one {label}, found {values}')
    forwarded_global(functions, aligned_submission, initial_runtime_values[0],
        submission_consumer, 1)
    forwarded_global(functions, aligned_submission, aligned_update_values[0],
        submission_consumer, 2)
    forwarded_global(functions, extended_submission, extended_source_values[0],
        submission_consumer, 1)
    forwarded_global(functions, extended_submission, submitted_update_values[0],
        submission_consumer, 2)
    for submission in (aligned_submission, extended_submission):
        calls(functions, submission,
            "NeuralAgent_acceptedRuntimeSubmissionOfCheck___redArg", 1)
        absent(functions, submission, ["installAcceptedUpdate"])
    for runtime, submission in ((aligned_runtime, aligned_submission),
                                (extended_runtime, extended_submission)):
        graph = shared["reachable"](functions, runtime)
        if submission not in graph:
            raise ValueError(
                f'{runtime}: named runtime does not consume its executed submission')
        absent(functions, runtime, ["installAcceptedUpdate"])
    print("AGENT_SUCCESSIVE_RUNTIME_OK: decoded update -> executed successive analysis -> transported/recomputed target -> submitUpdate result -> named installed runtime; no canonical-update or prepared-result bypass")
    # F3: an admitted ordinary continuation must execute the reduced future
    # contract, while a contract change must pass through the post-forgetting
    # analyzer and build the checked successor from that returned analysis.
    # These are distinct compiled routes; neither may substitute a named
    # canonical successor or treat the continuation as a contract update.
    post_continuation = select(functions,
        "NeuralAgent_submitLearnedPostForgettingContinuation")
    post_runtime = select(functions,
        "NeuralAgent_checkLearnedPostForgettingRuntimeUpdate___redArg")
    post_received = select(functions,
        "NeuralAgent_closeReceivedLearnedPostForgettingAnalysis")
    post_closed_change = select(functions,
        "NeuralAgent_closeLearnedPostForgettingContractChange")
    post_resources = select(functions,
        "NeuralAgent_executeLearnedPostForgettingContractResources___redArg")
    post_target_analysis = select(functions,
        "NeuralAgent_LearnedPostForgettingContractResources_targetAnalysis___redArg")
    post_action = select(functions,
        "NeuralAgent_LearnedPostForgettingContractResources_action___redArg")
    post_action_effect = select(functions,
        "NeuralAgent_LearnedPostForgettingContractResources_actionEffect___redArg")
    post_recomputed = select(functions,
        "NeuralAgent_LearnedPostForgettingContractResources_recomputedFragments___redArg")
    post_produced_proposal = select(functions,
        "NeuralAgent_LearnedPostForgettingExecutionReceipt_producedProposal")
    post_execute_action = select(functions,
        "NeuralAgent_executeLearnedActionFromProducedProposal___redArg")
    post_produce_effect = select(functions,
        "NeuralAgent_produceLearnedEffect___redArg")
    post_justification = select(functions,
        "NeuralAgent_learnedPostForgettingJustificationFromLocalConditions___redArg")
    post_builder = select(functions,
        "NeuralAgent_buildIncrementalCheckedUpdate___redArg")
    post_receipt_init = select_initializer(functions,
        "NeuralAgent_learnedPostForgettingExecutionReceipt___closed__0")
    post_update_init = select_initializer(functions,
        "NeuralAgent_learnedPostForgettingExtendedRuntimeUpdate___closed__0")
    post_submission_init = select_initializer(functions,
        "NeuralAgent_learnedPostForgettingExtendedRuntimeSubmission___closed__0")
    post_runtime_init = select_initializer(functions,
        "NeuralAgent_learnedPostForgettingExtendedRuntime")
    post_receipt_producer = select(functions,
        "NeuralAgent_executionReceiptOfInstalledPostForgettingContinuation")
    post_submission_consumer = select(functions,
        "NeuralAgent_acceptedRuntimeSubmissionOfCheck___redArg")
    calls(functions, post_continuation,
        "NeuralAgent_checkLearnedPostForgettingIncremental", 1)
    calls(functions, post_continuation,
        "NeuralAgent_executePostForgettingContinuation___redArg", 1)
    calls(functions, post_runtime,
        "NeuralAgent_analyzeLearnedPostForgettingIncrementally", 1)
    calls(functions, post_runtime,
        "NeuralAgent_closeReceivedLearnedPostForgettingAnalysis", 1)
    calls(functions, post_received,
        "NeuralAgent_learnedPostForgettingJustificationFromLocalConditions___redArg", 1)
    calls(functions, post_received,
        "NeuralAgent_closeLearnedPostForgettingContractChange", 1)
    forwarded_result(functions, post_received, post_justification,
        post_closed_change, 3)
    forwarded_ctor_field(functions, compiled_parameters, post_runtime, 0, 0,
        post_received, 0)
    forwarded_parameter(functions, compiled_parameters, post_received, 0,
        post_closed_change, 2)
    forwarded_parameter(functions, compiled_parameters, post_closed_change, 2,
        post_resources, 1)
    forwarded_parameter(functions, compiled_parameters, post_closed_change, 3,
        post_resources, 0)
    calls(functions, post_closed_change,
        "NeuralAgent_executeLearnedPostForgettingContractResources___redArg", 1)
    calls(functions, post_resources,
        "NeuralAgent_JustifiedPostForgettingTransition_transportedPersistent___redArg", 1)
    calls(functions, post_resources,
        "NeuralAgent_JustifiedPostForgettingTransition_rechecked___redArg", 1)
    calls(functions, post_closed_change,
        "NeuralAgent_LearnedPostForgettingContractResources_targetAnalysis___redArg", 1)
    calls(functions, post_target_analysis,
        "NeuralAgent_LearnedPostForgettingContractResources_recomputedFragments___redArg", 1)
    calls(functions, post_action,
        "NeuralAgent_LearnedPostForgettingExecutionReceipt_producedProposal", 1)
    forwarded_ctor_field(functions, compiled_parameters, post_action, 2, 0,
        post_produced_proposal, 0)
    calls(functions, post_action,
        "NeuralAgent_executeLearnedActionFromProducedProposal___redArg", 1)
    forwarded_result(functions, post_action, post_produced_proposal,
        post_execute_action, 1)
    forwarded_ctor_field(functions, compiled_parameters, post_action, 2, 2,
        post_execute_action, 2)
    forwarded_ctor_field(functions, compiled_parameters, post_action, 2, 3,
        post_execute_action, 4)
    calls(functions, post_action_effect,
        "NeuralAgent_LearnedPostForgettingContractResources_action___redArg", 1)
    calls(functions, post_action_effect,
        "NeuralAgent_produceLearnedEffect___redArg", 1)
    forwarded_result(functions, post_action_effect, post_action,
        post_produce_effect, 0)
    result_to_constructor(functions, post_action_effect, post_action, 0)
    result_to_constructor(functions, post_action_effect, post_produce_effect, 1)
    calls(functions, post_recomputed,
        "NeuralAgent_LearnedPostForgettingContractResources_actionEffect___redArg", 1)
    result_to_constructor(functions, post_recomputed, post_action_effect, 4)
    result_field_to_constructor(functions, post_recomputed, post_action_effect,
        0, 2)
    parameter_field_to_constructor(functions, compiled_parameters,
        post_recomputed, 2, 3, 3)
    calls(functions, post_closed_change,
        "NeuralAgent_buildIncrementalCheckedUpdate___redArg", 1)
    forwarded_result(functions, post_closed_change, post_resources,
        post_target_analysis, 2)
    forwarded_result(functions, post_closed_change, post_target_analysis,
        post_builder, 0)
    installed_continuation_values = sorted(set(re.findall(
        r'\b(?:l|lp)_\w*NeuralAgent_learnedInstalledPostForgettingContinuation\b',
        functions[post_receipt_init])))
    receipt_values = sorted(set(re.findall(
        r'\b(?:l|lp)_\w*NeuralAgent_learnedPostForgettingExecutionReceipt\b',
        functions[post_update_init])))
    initial_runtime_values = sorted(set(re.findall(
        r'\b(?:l|lp)_\w*NeuralAgent_learnedPostForgettingInitialRuntime\b',
        functions[post_submission_init])))
    update_values = sorted(set(re.findall(
        r'\b(?:l|lp)_\w*NeuralAgent_learnedPostForgettingExtendedRuntimeUpdate\b',
        functions[post_submission_init])))
    submission_values = sorted(set(re.findall(
        r'\b(?:l|lp)_\w*NeuralAgent_learnedPostForgettingExtendedRuntimeSubmission\b',
        functions[post_runtime_init])))
    for label, values in (
            ('installed continuation', installed_continuation_values),
            ('execution receipt', receipt_values),
            ('initial post-forgetting runtime', initial_runtime_values),
            ('post-forgetting runtime update', update_values),
            ('post-forgetting runtime submission', submission_values)):
        if len(values) != 1:
            raise ValueError(
                f'post-forgetting route: expected one {label}, found {values}')
    forwarded_global(functions, post_receipt_init,
        installed_continuation_values[0], post_receipt_producer, 0)
    global_to_constructor(functions, post_update_init, receipt_values[0], 0)
    calls(functions, post_submission_init,
        "NeuralAgent_acceptedRuntimeSubmissionOfCheck___redArg", 1)
    forwarded_global(functions, post_submission_init, initial_runtime_values[0],
        post_submission_consumer, 1)
    forwarded_global(functions, post_submission_init, update_values[0],
        post_submission_consumer, 2)
    if post_submission_init not in shared["reachable"](
            functions, post_runtime_init):
        raise ValueError(
            f'{post_runtime_init}: named runtime does not consume its executed submission')
    if submission_values[0] not in functions[post_runtime_init]:
        raise ValueError(
            f'{post_runtime_init}: exact post-forgetting submission is absent')
    absent(functions, post_runtime,
        ["learnedExtendedCheckedUpdate", "learnedPostForgettingExtendedRuntime"])
    absent(functions, post_target_analysis,
        ["learnedExtendedCheckedUpdate", "learnedPostForgettingExtendedRuntime"])
    absent(functions, post_submission_init, ["installAcceptedUpdate"])
    absent(functions, post_runtime_init, ["installAcceptedUpdate"])
    print("AGENT_POST_FORGETTING_RUNTIME_OK: the installed reduced-memory continuation emits the exact receipt carried by the runtime update; its outcome and next memory compute the proposal passed to the action, transport and recheck feed the installed certificate, and the named runtime consumes the actual submitUpdate result; no canonical-successor or receipt-erasure bypass")
    # L6: the installed incremental successor must be assembled through the
    # unique fragment constructor whose structural field is the calculated
    # transport/recompute assembly.  Neither that constructor nor the scaling
    # incremental analyzer may call a complete checker as an oracle.
    incremental_builder = select(functions,
        "NeuralAgent_buildIncrementalCheckedUpdate___redArg")
    fragment_assembly = select(functions,
        "NeuralAgent_IncrementalTargetAnalysis_fragments___redArg")
    calls(functions, incremental_builder,
        "NeuralAgent_IncrementalTargetAnalysis_fragments___redArg", 1)
    absent(functions, fragment_assembly,
        ["checkInitial", "checkFullUpdate", "FullRecheck", "certifyFragments"])
    structural_assembly = select(functions,
        "NeuralAgent_calculateIncrementalStructuralAssembly")
    direct_recomputation = select(functions,
        "NeuralAgent_recomputeAffectedStructuralObservations")
    absent(functions, structural_assembly,
        ["stableStructuralObservationSnapshot", "PreCertificateConstitutiveGraph_targetObservations"])
    absent(functions, direct_recomputation,
        ["stableStructuralObservationSnapshot"])
    scaling_incremental = select(functions,
        "NeuralAgent_analyzeScalingIncrementalUpdate")
    absent(functions, scaling_incremental,
        ["checkInitial", "checkFullUpdate", "FullRecheck", "certifyFragments"])
    print("AGENT_INCREMENTAL_ASSEMBLY_OK: installed certificate consumes direct transport/recomputation; no regenerated target snapshot or complete-check oracle")
    # F4: the successor campaign must produce one action from the exact source,
    # pass that same produced object to the effect constructor, and build the
    # successor from that effect.  Re-executing an extensionally equal action
    # here would hide an occurrence substitution behind value equality.
    causal_producer = select(functions,
        "NeuralAgent_produceCausalScalingTransition")
    causal_action = select(functions,
        "NeuralAgent_causalScalingAction")
    causal_target_analysis = select(functions,
        "NeuralAgent_causalScalingIncrementalTargetAnalysis")
    calls(functions, causal_producer, "NeuralAgent_causalScalingAction", 1)
    calls(functions, causal_action,
        "NeuralAgent_causalScalingTransitionRequest___redArg", 1)
    calls(functions, causal_action,
        "Agent_executeProducedInput", 1)
    calls(functions, causal_producer,
        "NeuralAgent_causalScalingEffectOfAction___redArg", 1)
    absent(functions, causal_producer, [], exact=(
        select(functions, "NeuralAgent_causalScalingEffect"),
        select(functions, "NeuralAgent_produceScalingEffect"),
    ))
    calls(functions, causal_target_analysis,
        "NeuralAgent_ExecutedTransitionProduction_targetState___redArg", 1)
    causal_trace = select(functions,
        "NeuralAgent_CompiledCausalCompletePropertyScaling_runTrace")
    calls(functions, causal_trace,
        "NeuralAgent_checkGenericIncrementalUpdate___redArg", 1)
    calls(functions, causal_trace,
        "NeuralAgent_checkFullUpdate___redArg", 1)
    print("AGENT_CAUSAL_SCALING_OK: one source-indexed action occurrence is consumed by one effect occurrence and the produced successor")
    print("AGENT_CAUSAL_SCALING_PAIRED_OK: the compiled runner executes one incremental check and one independent full recheck on each current state before continuing from the checked successor")
    print("AGENT_CODEGEN_OK: actual live step, one request head, learned sharing and incremental assembly, no rich archive or extensive enumeration")


if __name__ == "__main__":
    try:
        main()
    except (OSError, ValueError) as error:
        print(f"AGENT_CODEGEN_FAILED: {error}", file=sys.stderr)
        sys.exit(1)
