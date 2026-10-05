"""Bounded symbolic analysis of Lean 4.33 generated C entry points.

Not a C verifier or a cost/heap theorem. Unsupported control flow on an
analysed sensitive path fails closed. The shared static-route API is unchanged.
"""
from dataclasses import dataclass, field
import copy
import re


@dataclass
class Value:
    tags: frozenset = frozenset()
    fields: dict = field(default_factory=dict)
    function: str | None = None
    fixed: int = 0
    number: int | None = None

    def retained(self):
        return self.tags | frozenset().union(*(v.retained() for v in self.fields.values()))


def join(values):
    if not values:
        raise ValueError("C analysis has no reachable return")
    if len(values) == 1:
        return values[0]
    result = Value(frozenset().union(*(v.tags for v in values)))
    keys = set().union(*(v.fields for v in values))
    for key in keys:
        result.fields[key] = join([v.fields.get(key, Value(v.tags)) for v in values])
    functions = {v.function for v in values}
    if len(functions) == 1:
        result.function = values[0].function
        result.fixed = values[0].fixed
    return result


def split_arguments(text):
    parts, start, depth = [], 0, 0
    for index, char in enumerate(text):
        depth += (char == '(') - (char == ')')
        if char == ',' and depth == 0:
            parts.append(text[start:index].strip())
            start = index + 1
    parts.append(text[start:].strip())
    return parts if text.strip() else []


def statements(body):
    tokens, start, depth = [], 0, 0
    for index, char in enumerate(body):
        depth += (char == '(') - (char == ')')
        if char in '{};' and depth == 0:
            prefix = body[start:index].strip()
            if prefix:
                # Generated labels precede either a block or a declaration.
                label = re.match(r'^(\w+):\s*(.*)$', prefix, re.S)
                if label:
                    tokens.append(('label', label[1]))
                    prefix = label[2].strip()
                if prefix:
                    tokens.append(('text', prefix))
            tokens.append((char, char))
            start = index + 1
    if body[start:].strip():
        raise ValueError("Unparsed generated-C suffix")
    cursor = 0

    def block():
        nonlocal cursor
        nodes = []
        while cursor < len(tokens):
            kind, text = tokens[cursor]
            cursor += 1
            if kind == '}':
                return nodes
            if kind == ';':
                continue
            if kind == 'label':
                nodes.append(('label', text))
            elif kind == '{':
                nodes.extend(block())
            elif text.startswith('if ' ) or text.startswith('if('):
                if cursor >= len(tokens) or tokens[cursor][0] != '{':
                    raise ValueError("Unsupported unbraced C branch")
                cursor += 1
                yes = block()
                no = []
                if cursor < len(tokens) and tokens[cursor] == ('text', 'else'):
                    cursor += 1
                    if tokens[cursor][0] != '{':
                        raise ValueError("Unsupported C else")
                    cursor += 1
                    no = block()
                nodes.append(('if', text, yes, no))
            elif re.match(r'^switch\s*\(', text):
                # Generated tag dispatch: every alternative is a braced block
                # which must end by return/goto (no fall-through, checked on
                # every path). All alternatives are explored, like a branch.
                if cursor >= len(tokens) or tokens[cursor][0] != '{':
                    raise ValueError("Unsupported unbraced C switch")
                cursor += 1
                alternatives = []
                while True:
                    if cursor >= len(tokens):
                        raise ValueError("Unterminated C switch")
                    item_kind, item = tokens[cursor]
                    if item_kind == '}':
                        cursor += 1
                        break
                    if not ((item_kind == 'text' and re.fullmatch(r'case\s+\d+\s*:', item)) or
                            (item_kind == 'label' and item == 'default')):
                        raise ValueError("Unsupported C switch alternative: " + item)
                    cursor += 1
                    if cursor >= len(tokens) or tokens[cursor][0] != '{':
                        raise ValueError("Unsupported unbraced C switch alternative")
                    cursor += 1
                    alternatives.append(block())
                if not alternatives:
                    raise ValueError("Empty C switch")
                nodes.append(('switch', text, alternatives))
            elif re.match(r'^(switch|for|while|do)\b', text):
                raise ValueError("Unsupported sensitive C control flow: " + text)
            else:
                nodes.append(('statement', text))
        return nodes

    return block()


class Analysis:
    def __init__(self, functions, parameters, reachable, target=None, capture=False,
                 archive_getters=(), capture_boundaries=None):
        self.functions, self.parameters = functions, parameters
        self.reachable, self.target, self.capture = reachable, target, capture
        self.stack = []
        self.memo = {}
        self.initializing = set()
        # Only exact, caller-resolved symbols may be trusted boundaries. A
        # helper whose name resembles a production selector is still analysed.
        self.capture_boundaries = dict(capture_boundaries or {})
        for symbol in archive_getters:
            if symbol in self.capture_boundaries and self.capture_boundaries[symbol] != 'archive':
                raise ValueError('Conflicting capture boundary: ' + symbol)
            self.capture_boundaries[symbol] = 'archive'
        for symbol, kind in self.capture_boundaries.items():
            if symbol not in functions or symbol not in parameters:
                raise ValueError('Missing exact capture boundary definition: ' + symbol)
            if kind not in ('archive', 'produced', 'live'):
                raise ValueError('Unknown capture boundary policy: ' + kind)
        if self.capture_boundaries and not capture:
            raise ValueError('Capture boundaries require capture analysis')

    def relevant(self, name):
        return self.target is not None and self.target in self.reachable(self.functions, name)

    def closure_relevant(self, value):
        return ((value.function in self.functions and self.relevant(value.function)) or
                any(self.closure_relevant(v) for v in value.fields.values()))

    def global_value(self, name):
        body = self.functions.get(name, '')
        target = re.search(r'\.m_fun\s*=\s*\(void\*\)\s*((?:l|lp)_\w+)', body)
        if target:
            fixed = re.search(r'\.m_num_fixed\s*=\s*(\d+)', body)
            if fixed and int(fixed[1]):
                raise ValueError("Unsupported statically captured closure: " + name)
            return Value(function=target[1])
        objects = re.search(r'\.m_objs\s*=\s*\{(.*?)\}', body, re.S)
        if objects:
            fields = {}
            for index, item in enumerate(split_arguments(objects[1])):
                symbols = re.findall(r'\b(?:l|lp)_\w+\b', item)
                if len(symbols) != 1 or symbols[0] not in self.functions:
                    raise ValueError('Unresolved static constructor field: ' + item)
                fields[index] = self.global_value(symbols[0])
            return Value(fields=fields)
        if not body.startswith('{'):
            symbols = re.findall(r'\b(?:l|lp)_\w+\b', body)
            if len(symbols) == 1 and symbols[0] in self.functions:
                return self.global_value(symbols[0])
        initializer = '_init_' + name
        if initializer in self.functions:
            if initializer in self.initializing:
                raise ValueError("C initializer cycle: " + initializer)
            self.initializing.add(initializer)
            value, lo, hi = self.run(initializer, [])
            self.initializing.remove(initializer)
            if hi:
                raise ValueError("Producer in module initialization, not per-entry: " + initializer)
            return value
        return Value()

    def run(self, name, arguments):
        if self.capture and name in self.capture_boundaries:
            if len(self.parameters[name]) != len(arguments):
                raise ValueError('Exact capture boundary arity mismatch: ' + name)
            # These are explicit analysis scope boundaries, not claims about
            # arbitrary callbacks within a produced value or live state.
            tags = frozenset({'archive'}) if self.capture_boundaries[name] == 'archive' else frozenset()
            return Value(tags), 0, 0
        if name == self.target:
            return Value(), 1, 1  # Do not unfold the recursive producer.
        if name not in self.functions:
            if any(self.closure_relevant(v) for v in arguments):
                raise ValueError("Unknown helper receives a producer closure: " + name)
            return Value(frozenset().union(*(v.retained() for v in arguments))), 0, 0
        if not self.capture and not self.relevant(name) and not any(self.closure_relevant(v) for v in arguments):
            return Value(), 0, 0
        # Capture analysis is rooted at the source factory; other recursive
        # consumers use a monotone least approximation, checked to a fixed point.
        signature = (name, tuple(v.retained() for v in arguments))
        if signature in self.stack:
            if not self.capture:
                raise ValueError("Unresolved producer multiplicity through an upstream cycle: " + name)
            return self.memo.get(signature, Value()), 0, 0
        params = self.parameters.get(name)
        if params is None or len(params) != len(arguments):
            raise ValueError("Unresolved generated-C arity: " + name)
        self.stack.append(signature)
        try:
            nodes, labels = [], {}

            def compile_block(items, after):
                node = after
                for item in reversed(items):
                    if item[0] == 'label':
                        labels[item[1]] = node
                    elif item[0] == 'if':
                        yes = compile_block(item[2], node)
                        no = compile_block(item[3], node)
                        nodes.append(('if', item[1], yes, no))
                        node = len(nodes) - 1
                    elif item[0] == 'switch':
                        nodes.append(('fallthrough',))
                        stop = len(nodes) - 1
                        successors = [compile_block(alternative, stop) for alternative in item[2]]
                        nodes.append(('if', item[1], *successors))
                        node = len(nodes) - 1
                    else:
                        nodes.append(('statement', item[1], node))
                        node = len(nodes) - 1
                return node

            entry = compile_block(statements(self.functions[name]), None)
            loop_summaries = set()

            def walk(pc, environment, path, low=0, high=0):
                if pc is None:
                    raise ValueError("Sensitive C path lacks return: " + name)
                if pc in path:
                    if not self.capture:
                        raise ValueError("Unresolved sensitive C loop: " + name)
                    # Tail-recursive list helpers compile to backward gotos.
                    # Widen loop-carried fields to their union of capture tags;
                    # this loses precision conservatively, never archive tags.
                    widened = {key: Value(value.retained(), function=value.function,
                                          fixed=value.fixed, number=value.number)
                               for key, value in environment.items()}
                    signature = (pc, tuple(sorted((key, value.tags, value.function, value.fixed, value.number)
                                                  for key, value in widened.items())))
                    if signature in loop_summaries:
                        return []  # Stable widened state; exits already explored.
                    if len(loop_summaries) >= 32:
                        raise ValueError('Unresolved capture loop summary: ' + name)
                    loop_summaries.add(signature)
                    return walk(pc, widened, set(), low, high)
                node = nodes[pc]
                path = path | {pc}
                if node[0] == 'fallthrough':
                    raise ValueError("Unsupported C switch fall-through: " + name)
                if node[0] == 'if':
                    condition = node[1][node[1].index('(') + 1:-1]
                    _, lo, hi = evaluate(condition, environment)
                    returns = []
                    for successor in node[2:]:
                        returns.extend(walk(successor, copy.deepcopy(environment), path,
                                            low + lo, high + hi))
                    return returns
                text, successor = node[1:]
                if text.startswith('goto '):
                    label = text[5:].strip()
                    if label not in labels:
                        raise ValueError("Unknown C jump: " + label)
                    return walk(labels[label], environment, path, low, high)
                if text.startswith('return '):
                    value, lo, hi = evaluate(text[7:], environment)
                    return [(value, low + lo, high + hi)]
                assignment = re.match(r'^(\w+)\s*=\s*(.*)$', text, re.S)
                if assignment:
                    value, lo, hi = evaluate(assignment[2], environment)
                    environment[assignment[1]] = value
                elif re.match(r'^(lean_object\*|uint\d+_t|size_t|double|void\*)\s+\w+$', text):
                    lo = hi = 0
                else:
                    _, lo, hi = evaluate(text, environment)
                return walk(successor, environment, path, low + lo, high + hi)

            def evaluate(expression, environment):
                expression = expression.strip()
                if expression in environment:
                    return environment[expression], 0, 0
                if re.fullmatch(r'\d+', expression):
                    return Value(number=int(expression)), 0, 0
                direct = re.fullmatch(r'(\w+)\((.*)\)', expression, re.S)
                if not direct:
                    # Casts and scalar conditions may mention values but cannot
                    # hide an unanalysed function application.
                    if re.search(r'\b\w+\s*\(', expression):
                        calls = re.findall(r'((?:l|lp)_\w+)\s*\(', expression)
                        if calls or 'lean_apply_' in expression:
                            raise ValueError("Unsupported sensitive C expression: " + expression)
                    if expression in self.functions:
                        if expression in self.parameters:
                            return Value(function=expression), 0, 0
                        return self.global_value(expression), 0, 0
                    tokens = re.findall(r'\b\w+\b', expression)
                    return Value(frozenset().union(*(environment[t].retained()
                        for t in tokens if t in environment))), 0, 0
                callee, raw = direct.groups()
                raw_args = split_arguments(raw)
                parsed = [evaluate(arg, environment) for arg in raw_args]
                values = [value for value, _, _ in parsed]
                low, high = sum(lo for _, lo, _ in parsed), sum(hi for _, _, hi in parsed)
                if callee.startswith(('lean_inc', 'lean_dec')):
                    return Value(), low, high
                if callee == 'lean_alloc_ctor':
                    return Value(), low, high
                if callee == 'lean_box':
                    return values[0] if values else Value(), low, high
                if callee == 'lean_alloc_closure':
                    target = re.findall(r'\b(?:l|lp)_\w+\b', raw_args[0])
                    if len(target) != 1 or values[2].number is None:
                        raise ValueError("Unresolved closure allocation: " + expression)
                    return Value(function=target[0], fixed=values[2].number), low, high
                if callee in ('lean_ctor_set', 'lean_closure_set'):
                    slot = values[1].number
                    if slot is None:
                        raise ValueError("Unresolved retained-field index")
                    values[0].fields[slot] = values[2]
                    return Value(), low, high
                if callee == 'lean_ctor_get':
                    slot = values[1].number
                    if slot is None:
                        raise ValueError("Unresolved projected-field index")
                    return values[0].fields.get(slot, Value(values[0].tags)), low, high
                if callee.startswith('lean_apply_'):
                    closure = values[0]
                    if closure.function is None:
                        raise ValueError("Unresolved applied closure: " + name)
                    bound = [closure.fields.get(i, Value(closure.tags)) for i in range(closure.fixed)]
                    value, lo, hi = self.run(closure.function, bound + values[1:])
                    return value, low + lo, high + hi
                if callee.startswith('lean_'):
                    return Value(frozenset().union(*(v.retained() for v in values))), low, high
                value, lo, hi = self.run(callee, values)
                return value, low + lo, high + hi

            # Recursion in reader-list extraction is analysed monotonically.
            previous = self.memo.get(signature, Value())
            for _ in range(4 if self.capture else 1):
                loop_summaries.clear()
                returns = walk(entry, dict(zip(params, copy.deepcopy(arguments))), set())
                result = join([v for v, _, _ in returns])
                self.memo[signature] = result
                if result.retained() == previous.retained():
                    break
                previous = result
            else:
                raise ValueError("Capture summary did not converge: " + name)
            return result, min(lo for _, lo, _ in returns), max(hi for _, _, hi in returns)
        finally:
            self.stack.pop()


def parameters(texts):
    found = {}
    header = re.compile(r'(?m)^(?:LEAN_EXPORT |static )?(?:lean_object\*|uint\d+_t|double|void|size_t) '
                        r'((?:_init_)?(?:l|lp)_\w+)\(([^;]*?)\)\{')
    for text in texts:
        for match in header.finditer(text):
            found[match[1]] = [re.search(r'(\w+)\s*$', arg)[1]
                              for arg in split_arguments(match[2])]
    return found


def add_static_objects(functions, text):
    """Augment the local graph without changing the shared static-route parser."""
    for match in re.finditer(r'(?:static|LEAN_EXPORT) const lean_(?:closure|ctor)_object '
                            r'((?:l|lp)_\w+)_value\s*=\s*(\{.*?\});', text, re.S):
        functions[match[1] + '_value'] = match[2]
        functions[match[1]] = match[2]
    for match in re.finditer(r'(?:static|LEAN_EXPORT) const lean_object\* '
                            r'((?:l|lp)_\w+)\s*=\s*([^;]+);', text):
        functions[match[1]] = match[2]
