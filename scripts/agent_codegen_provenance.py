#!/usr/bin/env python3
"""Exact return-origin analysis for the two rich fields of the agent bridge.

This is a bounded analysis of the generated C emitted by the pinned Lean
toolchain.  It establishes dataflow from one owned ``sourcePerform`` call to
the selected return.  It is not an equivalence checker for arbitrary C.
Unsupported sensitive forms fail closed.
"""
from __future__ import annotations

from dataclasses import dataclass, field
import copy
import re

from unified_codegen_analysis import split_arguments, statements


class ProvenanceError(ValueError):
    pass


@dataclass(frozen=True)
class Symbol:
    name: str


@dataclass(frozen=True)
class Number:
    value: int


@dataclass(frozen=True)
class Foreign:
    label: str


@dataclass(frozen=True)
class ScalarFlag:
    key: str


@dataclass(frozen=True)
class Unknown:
    label: str


@dataclass(frozen=True)
class RichResult:
    call: int
    arguments: tuple


@dataclass(frozen=True)
class Projection:
    base: object
    path: tuple[int, ...]


@dataclass(frozen=True)
class Reference:
    identity: int


@dataclass(frozen=True)
class ClosureValue:
    function: str
    fixed: tuple


@dataclass(frozen=True)
class ConstructorValue:
    tag: int
    pointer_fields: int
    scalar_fields: int
    fields: tuple


@dataclass
class HeapObject:
    kind: str
    tag: int | None = None
    pointer_fields: int = 0
    scalar_fields: int = 0
    function: str | None = None
    fixed_count: int = 0
    fields: dict[int, object] = field(default_factory=dict)


@dataclass
class State:
    environment: dict[str, object]
    heap: dict[int, HeapObject] = field(default_factory=dict)
    constraints: dict[str, bool] = field(default_factory=dict)
    next_identity: int = 0
    rich_calls: int = 0

    def allocate(self, obj: HeapObject) -> Reference:
        identity = self.next_identity
        self.next_identity += 1
        self.heap[identity] = obj
        return Reference(identity)


@dataclass(frozen=True)
class Return:
    value: object
    state: State


def project(value, slot: int):
    if isinstance(value, Projection):
        return Projection(value.base, value.path + (slot,))
    return Projection(value, (slot,))


def contains_rich(value, heap, seen=None):
    seen = set() if seen is None else seen
    if isinstance(value, (RichResult, Projection)):
        return isinstance(value, RichResult) or contains_rich(value.base, heap, seen)
    if isinstance(value, ClosureValue):
        return any(contains_rich(item, heap, seen) for item in value.fixed)
    if isinstance(value, ConstructorValue):
        return any(contains_rich(item, heap, seen) for item in value.fields)
    if isinstance(value, Reference):
        if value.identity in seen:
            return False
        seen.add(value.identity)
        obj = heap.get(value.identity)
        return obj is not None and any(contains_rich(item, heap, seen) for item in obj.fields.values())
    return False


def collapse_exact_reconstruction(value):
    """Identify only an exact, ordered reconstruction of one projected object."""
    if not isinstance(value, ConstructorValue) or value.scalar_fields != 0 or \
            value.pointer_fields != len(value.fields) or not value.fields:
        return value
    if not all(isinstance(item, Projection) for item in value.fields):
        return value
    first = value.fields[0]
    if not first.path or first.path[-1] != 0:
        return value
    prefix = first.path[:-1]
    if all(item.base == first.base and item.path == prefix + (index,)
           for index, item in enumerate(value.fields)):
        return Projection(first.base, prefix)
    return value


class ProvenanceAnalysis:
    """Path-sensitive interpreter for the generated-C fragment used here."""

    def __init__(self, functions, parameters, reachable, *, rich, expected_arguments):
        self.functions = functions
        self.parameters = parameters
        self.reachable = reachable
        self.rich = rich
        self.expected_arguments = tuple(expected_arguments)
        self.stack = []
        self._compiled = {}
        self._globals = {}

    def _compile(self, name):
        if name in self._compiled:
            return self._compiled[name]
        if name not in self.functions:
            raise ProvenanceError('unknown generated-C function: ' + name)
        nodes, labels = [], {}

        def compile_block(items, after):
            node = after
            for item in reversed(items):
                if item[0] == 'label':
                    labels[item[1]] = node
                elif item[0] == 'if':
                    yes = compile_block(item[2], node)
                    no = compile_block(item[3], node)
                    nodes.append(('branch', item[1], yes, no))
                    node = len(nodes) - 1
                elif item[0] == 'switch':
                    nodes.append(('fallthrough',))
                    stop = len(nodes) - 1
                    successors = [compile_block(case, stop) for case in item[2]]
                    nodes.append(('branch', None, *successors))
                    node = len(nodes) - 1
                else:
                    nodes.append(('statement', item[1], node))
                    node = len(nodes) - 1
            return node

        entry = compile_block(statements(self.functions[name]), None)
        self._compiled[name] = (entry, nodes, labels)
        return self._compiled[name]

    def global_value(self, name, state):
        if name in self._globals:
            return self._globals[name]
        body = self.functions.get(name, '')
        fun = re.search(r'\.m_fun\s*=\s*\(void\*\)\s*((?:l|lp)_\w+)', body)
        if fun:
            fixed = re.search(r'\.m_num_fixed\s*=\s*(\d+)', body)
            count = int(fixed[1]) if fixed else 0
            raw_fields = re.search(r'\.m_objs\s*=\s*\{(.*?)\}', body, re.S)
            fields = []
            if raw_fields and raw_fields[1].strip():
                for item in split_arguments(raw_fields[1]):
                    symbols = re.findall(r'\b(?:l|lp)_\w+\b', item)
                    if len(symbols) != 1:
                        raise ProvenanceError('unresolved static closure field: ' + item)
                    fields.append(self.global_value(symbols[0], state))
            if len(fields) < count:
                raise ProvenanceError('incomplete static closure captures: ' + name)
            value = ClosureValue(fun[1], tuple(fields[:count]))
            self._globals[name] = value
            return value
        alias = re.findall(r'\b(?:l|lp)_\w+\b', body)
        alias = [item for item in alias if item != name]
        if len(alias) == 1 and alias[0] in self.functions:
            value = self.global_value(alias[0], state)
            self._globals[name] = value
            return value
        raise ProvenanceError('unresolved static value in sensitive path: ' + name)

    def normalize(self, value, state, seen=None):
        seen = set() if seen is None else seen
        if not isinstance(value, Reference):
            return value
        if value.identity in seen:
            raise ProvenanceError('cyclic heap object in sensitive return')
        obj = state.heap.get(value.identity)
        if obj is None:
            raise ProvenanceError('dangling heap reference in sensitive return')
        seen = seen | {value.identity}
        if obj.kind == 'closure':
            fixed = tuple(self.normalize(obj.fields.get(i, Unknown(f'closure-field-{i}')), state, seen)
                          for i in range(obj.fixed_count))
            return ClosureValue(obj.function, fixed)
        if obj.kind == 'ctor':
            fields = tuple(self.normalize(obj.fields.get(i, Unknown(f'ctor-field-{i}')), state, seen)
                           for i in range(obj.pointer_fields))
            return ConstructorValue(obj.tag, obj.pointer_fields, obj.scalar_fields, fields)
        raise ProvenanceError('unknown heap-object kind')

    def run(self, name, arguments, state=None):
        if name in self.stack:
            raise ProvenanceError('recursive sensitive helper: ' + name)
        params = self.parameters.get(name)
        if params is None or len(params) != len(arguments):
            raise ProvenanceError(f'unresolved generated-C arity: {name}')
        state = State(dict(zip(params, arguments))) if state is None else state
        state.environment = dict(zip(params, arguments))
        entry, nodes, labels = self._compile(name)
        self.stack.append(name)
        try:
            return self._walk(name, entry, nodes, labels, state, set())
        finally:
            self.stack.pop()

    def _walk(self, name, pc, nodes, labels, state, path):
        if pc is None:
            raise ProvenanceError('sensitive C path lacks return: ' + name)
        if pc in path:
            raise ProvenanceError('unresolved sensitive C loop: ' + name)
        node = nodes[pc]
        path = path | {pc}
        if node[0] == 'fallthrough':
            raise ProvenanceError('unsupported C switch fall-through: ' + name)
        if node[0] == 'branch':
            outcomes = []
            condition, successors = node[1], node[2:]
            choices = self.branch_choices(condition, successors, state)
            for successor, branch_state in choices:
                outcomes.extend(self._walk(name, successor, nodes, labels, branch_state, path))
            return outcomes
        text, successor = node[1:]
        if text.startswith('goto '):
            label = text[5:].strip()
            if label not in labels:
                raise ProvenanceError('unknown C jump: ' + label)
            return self._walk(name, labels[label], nodes, labels, state, path)
        if text.startswith('return '):
            value = self.evaluate(text[7:], state)
            return [Return(self.normalize(value, state), state)]
        assignment = re.match(r'^(\w+)\s*=\s*(.*)$', text, re.S)
        if assignment:
            state.environment[assignment[1]] = self.evaluate(assignment[2], state)
        elif re.match(r'^(lean_object\*|uint\d+_t|size_t|double|void\*)\s+\w+$', text):
            pass
        else:
            self.evaluate(text, state)
        return self._walk(name, successor, nodes, labels, state, path)

    def branch_choices(self, condition, successors, state):
        if condition is None or len(successors) != 2:
            return [(successor, copy.deepcopy(state)) for successor in successors]
        raw = condition[condition.find('(') + 1:condition.rfind(')')].strip()
        comparison = re.fullmatch(r'(\w+)\s*(==|!=)\s*([01])', raw)
        if not comparison:
            return [(successor, copy.deepcopy(state)) for successor in successors]
        value = state.environment.get(comparison[1])
        if not isinstance(value, ScalarFlag):
            return [(successor, copy.deepcopy(state)) for successor in successors]
        expected = comparison[3] == '1'
        if comparison[2] == '!=':
            expected = not expected
        choices = []
        for successor, required in zip(successors, (expected, not expected)):
            previous = state.constraints.get(value.key)
            if previous is not None and previous != required:
                continue
            branch_state = copy.deepcopy(state)
            branch_state.constraints[value.key] = required
            choices.append((successor, branch_state))
        return choices

    def evaluate(self, expression, state):
        expression = expression.strip()
        if expression in state.environment:
            return state.environment[expression]
        if re.fullmatch(r'\d+', expression):
            return Number(int(expression))
        # Generated casts around globals and function pointers are transparent.
        casted = re.fullmatch(r'\(\(lean_object\*\)\(((?:l|lp)_\w+)\)\)', expression)
        if casted:
            return self.global_value(casted[1], state)
        if expression in self.functions:
            if expression in self.parameters:
                return ClosureValue(expression, ())
            return self.global_value(expression, state)
        ownership = re.fullmatch(r'!?lean_is_exclusive\((.*)\)', expression, re.S)
        if ownership:
            # This controls only the generated runtime's in-place-reuse branch.
            # Both paths are explored; the ownership bit is never accepted as
            # an origin for a returned value.
            target = self.evaluate(ownership[1], state)
            return ScalarFlag('runtime-ownership:' + repr(target))
        direct = re.fullmatch(r'(\w+)\((.*)\)', expression, re.S)
        if not direct:
            if re.search(r'\b\w+\s*\(', expression):
                raise ProvenanceError('unsupported sensitive C expression: ' + expression)
            tokens = [state.environment[token] for token in re.findall(r'\b\w+\b', expression)
                      if token in state.environment]
            if any(contains_rich(value, state.heap) for value in tokens):
                raise ProvenanceError('rich origin hidden by unsupported expression: ' + expression)
            return Foreign('scalar-expression')
        callee, raw = direct.groups()
        args = [self.evaluate(item, state) for item in split_arguments(raw)]
        if callee.startswith(('lean_inc', 'lean_dec')):
            return Foreign('reference-count')
        if callee == 'lean_box':
            return args[0] if args else Foreign('boxed-unit')
        if callee == 'lean_alloc_ctor':
            if len(args) != 3 or not all(isinstance(item, Number) for item in args):
                raise ProvenanceError('unresolved constructor allocation: ' + expression)
            return state.allocate(HeapObject('ctor', tag=args[0].value,
                pointer_fields=args[1].value, scalar_fields=args[2].value))
        if callee == 'lean_alloc_closure':
            target = re.findall(r'\b(?:l|lp)_\w+\b', split_arguments(raw)[0])
            if len(target) != 1 or len(args) != 3 or not isinstance(args[2], Number):
                raise ProvenanceError('unresolved closure allocation: ' + expression)
            return state.allocate(HeapObject('closure', function=target[0], fixed_count=args[2].value))
        if callee in ('lean_ctor_set', 'lean_closure_set'):
            if len(args) != 3 or not isinstance(args[1], Number):
                raise ProvenanceError('unresolved heap update: ' + expression)
            if isinstance(args[0], Projection):
                raise ProvenanceError('generated code mutates a projected rich-result object')
            if not isinstance(args[0], Reference):
                raise ProvenanceError('unresolved heap update: ' + expression)
            obj = state.heap.get(args[0].identity)
            if obj is None:
                raise ProvenanceError('heap update through unknown reference')
            obj.fields[args[1].value] = args[2]
            return Foreign('heap-update')
        if callee.startswith('lean_ctor_set_'):
            if len(args) < 3 or not isinstance(args[0], Reference):
                raise ProvenanceError('unresolved scalar-field update: ' + expression)
            obj = state.heap.get(args[0].identity)
            if obj is None:
                raise ProvenanceError('scalar update through unknown reference')
            # Scalar payload is retained in the constructor shape but is not a
            # pointer origin. Its presence is pinned by scalar_fields.
            return Foreign('scalar-field-update')
        if callee == 'lean_ctor_get':
            if len(args) != 2 or not isinstance(args[1], Number):
                raise ProvenanceError('unresolved field projection: ' + expression)
            slot = args[1].value
            if isinstance(args[0], Reference):
                obj = state.heap.get(args[0].identity)
                if obj is None:
                    raise ProvenanceError('field projection through unknown reference')
                return obj.fields.get(slot, Unknown(f'unset-field-{slot}'))
            return project(args[0], slot)
        if callee.startswith('lean_apply_'):
            if not args:
                raise ProvenanceError('empty closure application')
            closure = self.normalize(args[0], state)
            if not isinstance(closure, ClosureValue):
                raise ProvenanceError('unresolved applied closure: ' + self.stack[-1])
            outcomes = self.run(closure.function, list(closure.fixed) + args[1:], copy.deepcopy(state))
            return self._single_value(callee, outcomes, state)
        if callee == self.rich:
            state.rich_calls += 1
            if tuple(args) != self.expected_arguments:
                raise ProvenanceError('sourcePerform called with wrong captured or invocation arguments')
            return RichResult(state.rich_calls, tuple(args))
        if callee.startswith('lean_'):
            if any(contains_rich(item, state.heap) for item in args):
                raise ProvenanceError('unsupported Lean runtime operation on rich origin: ' + callee)
            return Foreign(callee)
        if callee in self.functions and (self.rich in self.reachable(self.functions, callee)
                                         or any(contains_rich(item, state.heap) for item in args)):
            outcomes = self.run(callee, args, copy.deepcopy(state))
            return self._single_value(callee, outcomes, state)
        if any(contains_rich(item, state.heap) for item in args):
            raise ProvenanceError('unresolved foreign operation on rich origin: ' + callee)
        return Foreign(callee)

    def _single_value(self, callee, outcomes, caller_state):
        if not outcomes:
            raise ProvenanceError('callee has no sensitive return: ' + callee)
        values = [collapse_exact_reconstruction(outcome.value) for outcome in outcomes]
        counts = {outcome.state.rich_calls for outcome in outcomes}
        if len(set(values)) != 1 or len(counts) != 1:
            raise ProvenanceError('path-dependent sensitive helper result: ' + callee +
                                  ': ' + repr(values))
        first = outcomes[0].state
        caller_objects = set(caller_state.heap)
        observed = {key: first.heap[key] for key in caller_objects}
        if any({key: outcome.state.heap[key] for key in caller_objects} != observed
               for outcome in outcomes[1:]):
            raise ProvenanceError('path-dependent sensitive helper heap: ' + callee)
        # Propagate effects on caller-owned aliases. Callee-local allocations
        # have already been normalized into the returned value and do not
        # become part of the caller's abstract heap.
        for key, value in observed.items():
            caller_state.heap[key] = copy.deepcopy(value)
        caller_state.rich_calls = counts.pop()
        return values[0]


def exact_projection(value, expected_path, expected_arguments):
    return isinstance(value, Projection) and isinstance(value.base, RichResult) and \
        value.base.call == 1 and value.base.arguments == tuple(expected_arguments) and \
        value.path == tuple(expected_path)


def exact_event(value, expected_arguments):
    if exact_projection(value, (1,), expected_arguments):
        return True
    return isinstance(value, ConstructorValue) and value.tag == 0 and \
        value.pointer_fields == 2 and value.scalar_fields == 0 and \
        len(value.fields) == 2 and \
        exact_projection(value.fields[0], (1, 0), expected_arguments) and \
        exact_projection(value.fields[1], (1, 1), expected_arguments)


def bridge_provenance(functions, parameters, reachable, entry, rich,
                      *, source_next_slot=1, source_event_slot=5, runtime_fields=9):
    """Verify exact rich-result provenance for the actual returned bridge."""
    factory_input, factory_master = Symbol('factory.input'), Symbol('factory.master')
    source, request = Symbol('invocation.source'), Symbol('invocation.request')
    expected = (factory_input, factory_master, source, request)
    analysis = ProvenanceAnalysis(functions, parameters, reachable, rich=rich,
                                  expected_arguments=expected)
    factory_returns = analysis.run(entry, [factory_input, factory_master])
    if len(factory_returns) != 1:
        raise ProvenanceError('bridge factory has unresolved alternative returns')
    record = factory_returns[0].value
    if not isinstance(record, ConstructorValue) or record.pointer_fields != runtime_fields or \
            record.scalar_fields != 0 or len(record.fields) != runtime_fields:
        raise ProvenanceError('unresolved or changed Exact runtime record')
    results = {}
    for label, slot, predicate in (
            ('sourceNext', source_next_slot,
             lambda value: exact_projection(value, (0,), expected)),
            ('sourceEvent', source_event_slot,
             lambda value: exact_event(value, expected))):
        closure = record.fields[slot]
        if not isinstance(closure, ClosureValue):
            raise ProvenanceError('unresolved selected ' + label + ' closure')
        checker = ProvenanceAnalysis(functions, parameters, reachable, rich=rich,
                                     expected_arguments=expected)
        try:
            returns = checker.run(closure.function, list(closure.fixed) + [source, request])
        except ProvenanceError as error:
            raise ProvenanceError(label + ': ' + str(error)) from error
        if not returns:
            raise ProvenanceError(label + ': no return')
        for index, outcome in enumerate(returns):
            if outcome.state.rich_calls != 1:
                raise ProvenanceError(f'{label}: path {index}: expected one sourcePerform call, '
                                      f'found {outcome.state.rich_calls}')
            if not predicate(outcome.value):
                raise ProvenanceError(f'{label}: path {index}: returned origin {outcome.value!r}')
        results[label] = (closure.function, len(returns))
    return results
