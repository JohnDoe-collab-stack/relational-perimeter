"""Field/path-sensitive analysis of the pinned Lean-generated local C chain.

Calls have distinct identities. Branch results are never unioned into taint
sets. Summaries are scope boundaries, and the gate validates the actual bodies
of every summarized producer/getter before using them. Search kernels and
finite list kernels are not unfolded: this is not a C verifier or a cost bound.
Unfolded helpers may build fresh objects, but writes through their received
objects/aliases are rejected: their post-call heap is not summarized. This
boundary is checked at the write, not inferred from an object's original kind.
"""
from dataclasses import dataclass, field
import copy
import re
from unified_codegen_analysis import statements, split_arguments


class FlowError(ValueError):
    pass


@dataclass
class Datum:
    origin: tuple = ("unknown",)
    fields: dict = field(default_factory=dict)
    scalars: dict = field(default_factory=dict)
    tag: int | None = None
    function: str | None = None
    fixed: int = 0
    borrowed: frozenset = frozenset()

    def get(self, slot):
        if slot not in self.fields:
            return Datum(("field", self.origin, slot), borrowed=self.borrowed)
        return self.fields[slot]


def parameter(index):
    return Datum(("parameter", index))


def path(value, *slots):
    for slot in slots:
        value = value.get(slot)
    return value


def frozen(value):
    if value.fields or value.scalars:
        return ("record", value.tag, value.function, value.fixed,
                tuple(sorted((i, frozen(v)) for i, v in value.fields.items())),
                tuple(sorted((i, frozen(v)) for i, v in value.scalars.items())))
    if value.function is not None or value.tag is not None:
        return ("object", value.origin, value.tag, value.function, value.fixed)
    return value.origin


def same(one, two):
    return frozen(one) == frozen(two)


def require(condition, message):
    if not condition:
        raise FlowError("PROVENANCE_INCORRECT: " + message)


@dataclass
class Call:
    name: str
    arguments: list
    result: Datum


def unique(calls, name):
    selected = [c for c in calls if c.name == name]
    require(len(selected) == 1, f"{name}: expected one call, got {len(selected)}")
    return selected[0]


class Flow:
    def __init__(self, functions, parameters, reachable, *, unfold=(), terminals=(), cut_backedges=(), owners=None,
                 expand_unknown_writes=True):
        self.functions, self.parameters, self.reachable = functions, parameters, reachable
        self.unfold, self.terminals = set(unfold), set(terminals)
        self.serial, self.stack = 0, []
        self.borrow_frames = []
        self.graphs = {}
        self.cut_backedges = set(cut_backedges)
        self.initializing = set()
        self.owners = owners
        self.expand_unknown_writes = expand_unknown_writes

    def definition_check(self, name):
        if self.owners is not None and name in self.functions and len(self.owners.get(name, set())) != 1:
            raise FlowError("FORM_UNSUPPORTED: ambiguous helper/object owner " + name)

    def global_value(self, name):
        self.definition_check(name)
        if name in self.initializing:
            raise FlowError("FORM_UNSUPPORTED: static object cycle " + name)
        self.initializing.add(name)
        try:
            body = self.functions[name]
            closure = re.search(r"\.m_fun\s*=\s*\(void\*\)\s*((?:l|lp)_\w+)", body)
            if closure:
                fixed = re.search(r"\.m_num_fixed\s*=\s*(\d+)", body)
                if fixed and int(fixed[1]):
                    raise FlowError("FORM_UNSUPPORTED: static captures " + name)
                return Datum(function=closure[1])
            members = re.search(r"\.m_objs\s*=\s*\{(.*?)\}", body, re.S)
            if members:
                count = re.search(r"\.m_other\s*=\s*(\d+)", body)
                tag = re.search(r"\.m_tag\s*=\s*(\d+)", body)
                value = Datum(("global", name), tag=int(tag[1]) if tag else None)
                items = split_arguments(members[1])
                for i, item in enumerate(items[:int(count[1]) if count else len(items)]):
                    names = re.findall(r"\b(?:l|lp)_\w+\b", item)
                    immediate = re.search(r"\(size_t\)\((\d+)\)\s*<<\s*1", item)
                    if len(names) == 1 and names[0] in self.functions:
                        value.fields[i] = self.global_value(names[0])
                    elif immediate:
                        value.fields[i] = Datum(("literal", int(immediate[1])))
                    else:
                        raise FlowError("FORM_UNSUPPORTED: static field " + item)
                return value
            names = re.findall(r"\b(?:l|lp)_\w+\b", body)
            if len(names) == 1 and names[0] in self.functions:
                return self.global_value(names[0])
            raise FlowError("FORM_UNSUPPORTED: static object " + name)
        finally:
            self.initializing.remove(name)

    def fresh(self, kind, *parts):
        self.serial += 1
        return Datum((kind, self.serial, *parts))

    def should_unfold(self, name):
        if name in self.terminals:
            return False
        if name in self.unfold:
            return True
        if name not in self.parameters:
            return False
        # Follow adapters/helpers/closures leading to the sensitive entries.
        if (self.unfold | self.terminals).intersection(self.reachable(self.functions, name)):
            return True
        # A helper with writes cannot be an opaque, apparently pure call just
        # because it is large or has an extra wrapper. Stop at checked summaries.
        pending, visited = ([name] if self.expand_unknown_writes else []), set()
        while pending:
            current = pending.pop()
            if current in visited or current in self.terminals:
                continue
            visited.add(current)
            body = self.functions.get(current, "")
            # Writes to provably fresh local allocations do not affect the
            # caller's heap. Every assignment to an eligible receiver must be
            # an allocation or an alias of such a receiver; an unknown call,
            # projection or reassignment makes it ineligible. This only decides
            # whether a helper needs unfolding, not provenance of its result.
            assignments = {}
            for target, expression in re.findall(r"\b(\w+)\s*=\s*([^;]+);", body):
                assignments.setdefault(target, []).append(expression.strip())

            def allocation(expression):
                match = re.match(r"lean_alloc_(?:ctor|closure)\s*\(", expression)
                if not match:
                    return False
                depth = 1
                for index in range(match.end(), len(expression)):
                    depth += (expression[index] == "(") - (expression[index] == ")")
                    if depth == 0:
                        return index == len(expression) - 1
                return False

            fresh = set()
            while True:
                added = {target for target, expressions in assignments.items()
                         if target not in fresh and target not in self.parameters.get(current, [])
                         and all(expression in fresh or allocation(expression)
                                 for expression in expressions)}
                if not added:
                    break
                fresh.update(added)
            receivers = re.findall(r"\b(?:lean_ctor_set\w*|lean_closure_set)\s*\(\s*([^,]+),", body)
            if any(receiver.strip() not in fresh for receiver in receivers):
                return True
            # Also follow closure targets and their static-object references.
            pending.extend(c for c in re.findall(r"\b\w+\b", body) if c in self.functions)
        body = self.functions[name]
        callees = re.findall(r"\b(\w+)\s*\(", body)
        # Transparent projection/record adapters. No arithmetic or unrecognized
        # call is certified as a transparent source of data.
        return len(body) < 1800 and all(c.startswith(("lean_ctor_", "lean_inc", "lean_dec"))
            or c in ("lean_alloc_ctor", "lean_box", "lean_is_exclusive", "if") for c in callees)

    def call(self, name, arguments):
        self.definition_check(name)
        if name not in self.parameters or len(arguments) != len(self.parameters[name]):
            raise FlowError("FORM_UNSUPPORTED: missing definition/arity for " + name)
        before = copy.deepcopy(arguments)
        if not self.should_unfold(name):
            result = self.fresh("result", name)
            return [(result, [Call(name, before, copy.deepcopy(result))])]
        if name in self.stack:
            raise FlowError("FORM_UNSUPPORTED: sensitive helper cycle " + name)
        self.stack.append(name)
        self.serial += 1
        frame = self.serial
        self.borrow_frames.append(frame)
        try:
            borrowed = copy.deepcopy(arguments)
            seen = set()

            def mark(value):
                if id(value) in seen:
                    return
                seen.add(id(value))
                value.borrowed = value.borrowed | {frame}
                for child in (*value.fields.values(), *value.scalars.values()):
                    mark(child)

            for value in borrowed:
                mark(value)
            results = self.body(name, borrowed)
            return [(value, calls + [Call(name, before, copy.deepcopy(value))]) for value, calls in results]
        finally:
            self.borrow_frames.pop()
            self.stack.pop()

    def write_check(self, value, callee):
        if value.borrowed:
            reason = ("helper mutates borrowed input " if value.borrowed.intersection(self.borrow_frames)
                      else "write through returned helper alias ")
            raise FlowError("FORM_UNSUPPORTED: " + reason + callee)

    def graph(self, name):
        if name in self.graphs:
            return self.graphs[name]
        nodes, labels = [], {}

        def block(items, after):
            node = after
            for item in reversed(items):
                if item[0] == "label":
                    labels[item[1]] = node
                elif item[0] == "if":
                    yes, no = block(item[2], node), block(item[3], node)
                    nodes.append(("if", item[1], yes, no)); node = len(nodes) - 1
                else:
                    nodes.append(("statement", item[1], node)); node = len(nodes) - 1
            return node

        try:
            entry = block(statements(self.functions[name]), None)
        except ValueError as error:
            raise FlowError("FORM_UNSUPPORTED: " + name + ": " + str(error)) from error
        self.graphs[name] = entry, nodes, labels
        return entry, nodes, labels

    def evaluate(self, expression, environment):
        expression = expression.strip()
        if expression in environment:
            return [(environment[expression], [])]
        if re.fullmatch(r"\d+[uUlL]*", expression):
            return [(Datum(("literal", int(re.sub(r"[uUlL]+$", "", expression)))), [])]
        direct = re.fullmatch(r"(\w+)\((.*)\)", expression, re.S)
        if not direct:
            if re.fullmatch(r"sizeof\(void\*\)\*\d+", expression):
                return [(Datum(("offset", expression)), [])]
            if expression in self.functions:
                if expression in self.parameters:
                    return [(Datum(function=expression), [])]
                return [(self.global_value(expression), [])]
            if expression.startswith("(void*)"):
                return self.evaluate(expression[7:], environment)
            # Conditions are not sources of selected variables or successors.
            # Evaluate embedded calls, preserving their work and call identity.
            match = re.fullmatch(r"(!?\w+(?:\([^;]*\))?)\s*(==|!=)\s*(\d+)", expression)
            if match:
                return [(Datum(("condition", frozen(v), match[2], match[3])), cs)
                        for v, cs in self.evaluate(match[1], environment)]
            if expression.startswith("!"):
                return [(Datum(("not", frozen(v))), cs)
                        for v, cs in self.evaluate(expression[1:], environment)]
            if re.search(r"\b\w+\s*\(", expression):
                raise FlowError("FORM_UNSUPPORTED: expression " + expression)
            if re.fullmatch(r"sizeof\(void\*\)\*\d+", expression):
                return [(Datum(("offset", expression)), [])]
            raise FlowError("FORM_UNSUPPORTED: expression " + expression)
        callee, raw = direct.groups()
        variants = [([], [], environment)]
        for argument in split_arguments(raw):
            expanded = []
            for values, calls, env in variants:
                # Copy the whole tuple to preserve aliases on each branch.
                for value, extra in self.evaluate(argument, env):
                    expanded.append((values + [value], calls + extra, env))
            variants = expanded
        outputs = []
        for values, calls, env in variants:
            def literal(index):
                value = values[index].origin
                if len(value) != 2 or value[0] != "literal":
                    raise FlowError("FORM_UNSUPPORTED: nonliteral field/arity " + expression)
                return value[1]
            if callee.startswith(("lean_inc", "lean_dec")):
                result = Datum(("erased",))
            elif callee == "lean_alloc_ctor":
                result = self.fresh("allocation"); result.tag = literal(0)
            elif callee == "lean_box":
                result = values[0]
            elif callee in ("lean_ctor_get", "lean_closure_get"):
                result = values[0].get(literal(1))
            elif callee in ("lean_ctor_set", "lean_closure_set"):
                self.write_check(values[0], callee)
                values[0].fields[literal(1)] = values[2]; result = Datum(("erased",))
            elif callee == "lean_ctor_set_tag":
                self.write_check(values[0], callee)
                values[0].tag = literal(1); result = Datum(("erased",))
            elif callee.startswith("lean_ctor_set_"):
                self.write_check(values[0], callee)
                values[0].scalars[frozen(values[1])] = values[2]; result = Datum(("erased",))
            elif callee.startswith("lean_ctor_get_"):
                result = values[0].scalars.get(frozen(values[1]),
                    Datum(("scalar", values[0].origin, frozen(values[1]))))
            elif callee == "lean_alloc_closure":
                result = Datum(function=values[0].function, fixed=literal(2))
                if result.function is None:
                    raise FlowError("FORM_UNSUPPORTED: unresolved allocated closure")
            elif callee.startswith("lean_apply_"):
                closure = values[0]
                if closure.function is None:
                    if closure.origin[0] == "literal":
                        outputs.append((closure, calls)); continue
                    raise FlowError("FORM_UNSUPPORTED: unresolved applied closure")
                bound = [closure.get(i) for i in range(closure.fixed)]
                outputs.extend((v, calls + cs) for v, cs in self.call(closure.function, bound + values[1:]))
                continue
            elif callee in ("lean_is_exclusive", "lean_obj_tag", "lean_is_scalar"):
                result = Datum(("condition-read", callee, frozen(values[0])))
            elif callee.startswith("lean_"):
                # Arithmetic/runtime operations are explicit computed sources,
                # never exact aliases for one of their input fields.
                result = self.fresh("primitive", callee, tuple(frozen(v) for v in values))
            else:
                outputs.extend((v, calls + cs) for v, cs in self.call(callee, values)); continue
            outputs.append((result, calls))
        return outputs

    def body(self, name, arguments):
        self.definition_check(name)
        entry, nodes, labels = self.graph(name)

        def walk(pc, env, visited, calls, facts):
            if pc in visited and name in self.cut_backedges:
                # One finite-list iteration, with its actual next arguments.
                # This explicit kernel boundary does not unfold the entire list.
                return [(Datum(("loop", name), fields={i: copy.deepcopy(env[p])
                    for i, p in enumerate(self.parameters[name])}), calls)]
            if pc is None or pc in visited:
                raise FlowError("FORM_UNSUPPORTED: path without return/cycle in " + name)
            node, visited = nodes[pc], visited | {pc}
            if node[0] == "if":
                condition = node[1][node[1].index("(") + 1:-1]
                results = []
                for tested, extra in self.evaluate(condition, env):
                    key = frozen(tested)
                    choices = [facts[key]] if key in facts else [0, 1]
                    for choice in choices:
                        successor = node[2 + choice]
                        envCopy, callsCopy = copy.deepcopy((env, calls + extra))
                        branchFacts = dict(facts); branchFacts[key] = choice
                        results.extend(walk(successor, envCopy, visited, callsCopy, branchFacts))
                return results
            text, successor = node[1:]
            if text.startswith("goto "):
                label = text[5:].strip()
                if label not in labels:
                    raise FlowError("FORM_UNSUPPORTED: jump " + label)
                return walk(labels[label], env, visited, calls, facts)
            if text.startswith("return "):
                return [(v, calls + cs) for v, cs in self.evaluate(text[7:], env)]
            if re.fullmatch(r"(?:lean_object\*|uint\d+_t|size_t|double|void\*)\s+\w+", text):
                return walk(successor, env, visited, calls, facts)
            match = re.match(r"^(\w+)\s*=\s*(.*)$", text, re.S)
            results = []
            for value, extra in self.evaluate(match[2] if match else text, env):
                if match:
                    env[match[1]] = value
                envCopy, callsCopy = copy.deepcopy((env, calls + extra))
                results.extend(walk(successor, envCopy, visited, callsCopy, facts))
            return results

        return walk(entry, dict(zip(self.parameters[name], copy.deepcopy(arguments))), set(), [], {})

    def inspect(self, name):
        self.unfold.add(name)
        return self.body(name, [parameter(i) for i in range(len(self.parameters[name]))])


def self_test(parser, parameters, reachable):
    """Fixed checker regressions, not confirmatory performance experiments."""
    text = '''LEAN_EXPORT lean_object* l_produce(lean_object* x){ return x; }
LEAN_EXPORT lean_object* l_get(lean_object* x){ return lean_ctor_get(x, 0); }
LEAN_EXPORT lean_object* l_good(lean_object* x){
 lean_object* p; lean_object* pair; p = l_produce(x);
 pair = lean_alloc_ctor(0, 2, 0); lean_ctor_set(pair, 0, p);
 lean_ctor_set(pair, 1, p); return pair;
}
LEAN_EXPORT lean_object* l_bad(lean_object* x){
 lean_object* p; lean_object* q; lean_object* pair;
 p = l_produce(x); q = l_produce(x); pair = lean_alloc_ctor(0, 2, 0);
 lean_ctor_set(pair, 0, p); lean_ctor_set(pair, 1, q); return pair;
}
LEAN_EXPORT lean_object* l_fields(lean_object* x){
 lean_object* p; lean_object* alias; lean_object* pair; p = l_produce(x); alias = p;
 pair = lean_alloc_ctor(0, 2, 0); lean_ctor_set(pair, 0, l_get(alias));
 lean_ctor_set(pair, 1, lean_ctor_get(p, 0)); return pair;
}
LEAN_EXPORT lean_object* l_wrong_field(lean_object* x){
 lean_object* p; lean_object* pair; p = l_produce(x); pair = lean_alloc_ctor(0, 2, 0);
 lean_ctor_set(pair, 0, lean_ctor_get(p, 1));
 lean_ctor_set(pair, 1, lean_ctor_get(p, 0)); return pair;
}
LEAN_EXPORT lean_object* l_closure(lean_object* x){
 lean_object* f; lean_object* p; lean_object* pair;
 f = lean_alloc_closure((void*)l_produce, 1, 0); p = lean_apply_1(f, x);
 pair = lean_alloc_ctor(0, 2, 0); lean_ctor_set(pair, 0, p);
 lean_ctor_set(pair, 1, p); return pair;
}
LEAN_EXPORT lean_object* l_branch(lean_object* x){
 lean_object* p; lean_object* pair; p = l_produce(x); pair = lean_alloc_ctor(0, 2, 0);
 lean_ctor_set(pair, 0, p);
 if (lean_is_exclusive(x)) { lean_ctor_set(pair, 1, p); }
 else { lean_ctor_set(pair, 1, x); } return pair;
}'''
    functions, params = parser(text), parameters([text])
    for entry in ("l_good", "l_fields", "l_closure"):
        analysis = Flow(functions, params, reachable, terminals=("l_produce",))
        for value, calls in analysis.inspect(entry):
            require(same(value.get(0), value.get(1)), entry + ": lost alias")
            unique(calls, "l_produce")
    for entry in ("l_bad", "l_wrong_field", "l_branch"):
        analysis = Flow(functions, params, reachable, terminals=("l_produce",))
        try:
            for value, _ in analysis.inspect(entry):
                require(same(value.get(0), value.get(1)), "self-test incorrect origin")
        except FlowError as error:
            if not str(error).startswith("PROVENANCE_INCORRECT:"):
                raise
        else:
            raise FlowError("Self-test accepted " + entry)
    require(not same(Datum(fields={0: parameter(0)}, tag=0),
                     Datum(fields={0: parameter(0)}, tag=1)), "constructor tag erased")
    require(not same(Datum(fields={0: parameter(0)}, function="l_good", fixed=1),
                     Datum(fields={0: parameter(0)}, function="l_bad", fixed=1)),
            "captured closure target erased")
    # All these objects are borrowed by the helper, regardless of where the
    # caller obtained them. Copies/aliases and nested calls must retain that
    # ownership boundary. Literal event 3 is the .refused constructor.
    writes = (
        ("event", "lean_ctor_set(x, 1, lean_box(3))"),
        ("nested", "lean_ctor_set(lean_ctor_get(x, 0), 1, lean_box(3))"),
        ("scalar", "lean_ctor_set_uint8(x, sizeof(void*)*2, 3)"),
        ("tag", "lean_ctor_set_tag(x, 3)"),
        ("capture", "lean_closure_set(x, 0, lean_box(3))"),
    )
    origins = ("x", "l_produce(x)", "lean_alloc_ctor(0, 2, 0)")
    checked = 0
    for label, write in writes:
        for index, origin in enumerate(origins):
            source = text + '''
LEAN_EXPORT lean_object* l_write(lean_object* x){ WRITE; return x; }
LEAN_EXPORT lean_object* l_wrap(lean_object* x){ return l_write(x); }
LEAN_EXPORT lean_object* l_probe(lean_object* x){
 lean_object* pair; pair = ORIGIN; l_wrap(pair); return pair;
}'''.replace("WRITE", write).replace("ORIGIN", origin)
            analysis = Flow(parser(source), parameters([source]), reachable, terminals=("l_produce",))
            try:
                analysis.inspect("l_probe")
            except FlowError as error:
                if not str(error).startswith("FORM_UNSUPPORTED: helper mutates borrowed input "):
                    raise FlowError(f"Wrong borrowed-write rejection: {label}/{index}: {error}") from error
            else:
                raise FlowError(f"Self-test accepted borrowed write: {label}/{index}")
            checked += 1
    # Exceed the old transparent-helper size threshold deliberately: a large
    # writer must not become an opaque call with its effects silently dropped.
    source = text + '''
LEAN_EXPORT lean_object* l_large(lean_object* x){ PADDING lean_ctor_set(x,1,lean_box(3)); return x; }
LEAN_EXPORT lean_object* l_large_probe(lean_object* x){
 lean_object* p; p=l_produce(x); l_large(p); return p;
}'''.replace("PADDING", "lean_inc(x); lean_dec(x); " * 100)
    analysis = Flow(parser(source), parameters([source]), reachable, terminals=("l_produce",))
    try:
        analysis.inspect("l_large_probe")
    except FlowError as error:
        require(str(error).startswith("FORM_UNSUPPORTED: helper mutates borrowed input "),
                "large writer rejected for the wrong reason")
    else:
        raise FlowError("Self-test accepted large borrowed writer")
    for projection in ("x", "lean_ctor_get(x,0)"):
        source = text + '''
LEAN_EXPORT lean_object* l_alias(lean_object* x){ return PROJECTION; }
LEAN_EXPORT lean_object* l_alias_probe(lean_object* x){
 lean_object* p; lean_object* alias; p=l_produce(x); alias=l_alias(p);
 lean_ctor_set(alias,1,lean_box(3)); return p;
}'''.replace("PROJECTION", projection)
        analysis = Flow(parser(source), parameters([source]), reachable, terminals=("l_produce",))
        try:
            analysis.inspect("l_alias_probe")
        except FlowError as error:
            require(str(error) == "FORM_UNSUPPORTED: write through returned helper alias lean_ctor_set",
                    "returned-alias write rejected for the wrong reason")
        else:
            raise FlowError("Self-test accepted write through returned helper alias")
    print(f"MACHINE_FLOW_SELFTEST_OK: aliases, helpers, closures, tags, fields and paths; {checked + 1} borrowed writes and 2 returned-alias writes rejected")
