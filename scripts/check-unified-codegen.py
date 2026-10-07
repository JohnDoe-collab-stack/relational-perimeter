#!/usr/bin/env python3
"""Structural C-IR checks for the public producer and restricted restart API.

Includes transitive callees and statically named closure functions/initializers.
It does not establish total cost, physical memory bounds, or properties of
arbitrary client-provided callbacks. Those are not claims of this contract.
"""
from pathlib import Path
import re
import sys
import subprocess
sys.dont_write_bytecode = True
from unified_codegen_analysis import Analysis, Value, parameters, add_static_objects
from unified_codegen_selftest import self_test

ROOT = Path(__file__).resolve().parent.parent
HEADER = re.compile(r"(?m)^(?:LEAN_EXPORT |static )?(?:lean_object\*|uint\d+_t|double|void|size_t) "
                    r"((?:_init_)?(?:l|lp)_[A-Za-z0-9_]+)\([^;]*?\)\{")
TOKEN = re.compile(r"\b(?:_init_)?(?:l|lp)_[A-Za-z0-9_]+\b")
LITERALS = re.compile(r'"(?:\\.|[^"\\])*"|\'(?:\\.|[^\'\\])*\'|/\*.*?\*/|//[^\n]*', re.S)


def bodies(text):
    clean = LITERALS.sub(lambda m: " " * len(m.group()), text)
    result = {}
    for match in HEADER.finditer(clean):
        start = match.end() - 1
        depth = 1
        end = start + 1
        while depth and end < len(clean):
            depth += (clean[end] == "{") - (clean[end] == "}")
            end += 1
        if depth:
            raise ValueError(f"Unbalanced C function {match[1]}")
        result[match[1]] = clean[start:end]
    # Lean 4.33 may emit a static closure object rather than an _init function.
    for match in re.finditer(r"static const lean_closure_object ((?:l|lp)_\w+)_value\s*=\s*(\{.*?\});", clean, re.S):
        result[match[1]] = match[2]
    return result


def reachable(functions, start):
    seen, pending = set(), [start]
    while pending:
        name = pending.pop()
        if name in seen:
            continue
        seen.add(name)
        for token in TOKEN.findall(functions[name]):
            if token in functions and token not in seen:
                pending.append(token)
            initializer = "_init_" + token
            if initializer in functions and initializer not in seen:
                pending.append(initializer)
    return seen


def select(functions, suffix):
    matches = [name for name in functions if not name.startswith("_init_") and name.endswith(suffix)]
    if len(matches) != 1:
        raise ValueError(f"Expected one generated function for {suffix}; found {matches}")
    return matches[0]


def absent(functions, start, forbidden, exact=()):
    graph = reachable(functions, start)
    bad = sorted(name for name in graph if name in exact or any(fragment in name for fragment in forbidden))
    if bad:
        raise ValueError(f"Forbidden transitive dependency from {start}: {bad}")
    print(f"CODEGEN_GRAPH_OK {start}: {len(graph)} functions, static closure targets included")


def calls(functions, name, suffix, expected):
    actual = sum(1 for token in re.findall(r"\b((?:l|lp)_\w+)\s*\(", functions[name])
                 if token.endswith(suffix))
    if actual != expected:
        raise ValueError(f"{name}: {suffix}: expected {expected} calls, found {actual}")
    print(f"CODEGEN_CALL_OK {name}: {suffix}={actual}")


def owned_symbol(functions, compiled_parameters, owners, prefix, declaration, module, variant=''):
    """Resolve a fully qualified declaration and its defining C artifact.

    Imported prototypes do not establish ownership. Missing, duplicate or
    foreign definitions fail closed; substring/suffix lookalikes cannot match.
    """
    symbol = prefix + declaration.replace('.', '_') + variant
    if symbol not in functions or symbol not in compiled_parameters:
        raise ValueError('Missing exact generated definition: ' + symbol)
    if owners.get(symbol) != {module}:
        raise ValueError(f'{symbol}: expected defining artifact {module}; found {owners.get(symbol)}')
    return symbol


def producer_routes(functions, start, target, expected, boundaries=()):
    """Count static call/reference routes up to the producer boundary.

    The producer's recursion is intentionally not unfolded. This shared API
    counts references, NOT applications of a closure. Application multiplicity
    is checked separately by the local symbolic analysis below.
    """
    memo = {}
    def count(name, stack):
        if name == target:
            return 1
        if name in boundaries:
            return 0
        if name in memo:
            return memo[name]
        if target not in reachable(functions, name):
            memo[name] = 0
            return 0
        if name in stack:
            # Pure recursive dependencies without this producer are irrelevant.
            if target in reachable(functions, name):
                raise ValueError(f"Producer reachable through upstream cycle: {name}")
            return 0
        total = 0
        for token in TOKEN.findall(functions[name]):
            if token in functions:
                total += count(token, stack | {name})
            elif "_init_" + token in functions:
                total += count("_init_" + token, stack | {name})
            if total > expected:
                break
        memo[name] = total
        return total
    actual = count(start, set())
    if actual != expected:
        raise ValueError(f"{start}: expected {expected} static producer routes to {target}, found {actual}")
    print(f"CODEGEN_PRODUCER_OK {start}: transitive routes={actual}")


def main():
    self_test(bodies, reachable, owned_symbol)
    # The negative self-check must follow a closure target, not merely a call.
    probe = {"l_start": "{ lean_alloc_closure(l_bad, 1, 0); }", "l_bad": "{}"}
    if "l_bad" not in reachable(probe, "l_start"):
        raise ValueError("Closure-reachability self-check failed")
    initializers = bodies("static lean_object* _init_l_cache(){ return l_bad(); }\n"
                          "LEAN_EXPORT lean_object* l_start(){ return l_cache; }\n"
                          "LEAN_EXPORT lean_object* l_bad(){ return 0; }")
    if "l_bad" not in reachable(initializers, "l_start"):
        raise ValueError("Initializer-reachability self-check failed")
    # A hidden second execution must be rejected, even in a named helper.
    doubled = {"l_entry": "{ l_engine(); l_helper(); }", "l_helper": "{ l_engine(); }", "l_engine": "{}"}
    try:
        producer_routes(doubled, "l_entry", "l_engine", 1)
    except ValueError:
        pass
    else:
        raise ValueError("Hidden second producer self-check failed")
    inventory = subprocess.run(
        ["git", "ls-files", "--cached", "--others", "--exclude-standard", "--", "*.lean"],
        cwd=ROOT, capture_output=True, text=True, check=False)
    if inventory.returncode:
        raise ValueError("Cannot obtain the compiled-source inventory")
    sources = [ROOT / line for line in inventory.stdout.splitlines() if (ROOT / line).is_file()]
    compiled = [ROOT / ".lake/build/ir" / path.relative_to(ROOT).with_suffix(".c") for path in sources]
    missing = [str(path.relative_to(ROOT)) for path in compiled if not path.is_file()]
    if missing:
        raise ValueError(f"Incomplete C dependency graph; rebuild these artifacts: {missing}")
    functions = {}
    owners = {}
    compiled_texts = []
    for path in compiled:
        source = path.read_text(encoding="utf-8")
        compiled_texts.append(source)
        module = path.relative_to(ROOT / '.lake/build/ir').as_posix()
        for symbol in parameters([source]):
            owners.setdefault(symbol, set()).add(module)
        functions.update(bodies(source))
        add_static_objects(functions, LITERALS.sub(lambda m: ' ' * len(m.group()), source))
    if not functions:
        raise ValueError("Missing generated C; run lake build first")
    entry = select(functions, "UnifiedMaster_publicInstance")
    producer = select(functions, "MasterResources_executeWithReferences")
    compiled_parameters = parameters(compiled_texts)
    def applications(suffix, expected):
        start = select(functions, suffix)
        analysis = Analysis(functions, compiled_parameters, reachable, target=producer)
        _, low, high = analysis.run(start, [Value() for _ in compiled_parameters[start]])
        if (low, high) != (expected, expected):
            raise ValueError(f"{start}: expected {expected} entry applications, obtained [{low}, {high}]")
        print(f"CODEGEN_APPLICATIONS_OK {start}: [{low}, {high}], recursive producer boundary")
    for suffix, expected in [
            ("UnifiedMaster_publicInstance", 1),
            ("UnifiedMaster_resource__history__extension___redArg", 1),
            ("UnifiedMaster_Instance_grow___redArg", 1),
            ("UnifiedMaster_Growth_resume___redArg", 1),
            ("UnifiedMaster_publicContinuation", 2),
            ("UnifiedMaster_publicGrowthTwice", 3)]:
        applications(suffix, expected)
    projection_executor = select(functions, "MasterResources_execute")
    producer_routes(functions, entry, producer, 1)
    old_executor = ["executeCausalOperationalExecutionHistory", "executeCausalOperationalHead"]
    # Full exported wrappers survive when a mutation makes an erased argument
    # computationally relevant; a missing redArg helper is not a causal rejection.
    for suffix in ["UnifiedMaster_Instance_stagewise",
                   "UnifiedMaster_Instance_normalization",
                   "UnifiedMaster_Instance_checkpoint"]:
        consumer = select(functions, suffix)
        absent(functions, consumer, old_executor + ["MasterResources_execute"], [projection_executor])
        applications(suffix, 0)
    absent(functions, entry, old_executor + ["MasterResources_execute___"], [projection_executor])
    absent(functions, producer, old_executor, [projection_executor])
    growth = select(functions, "UnifiedMaster_resource__history__extension___redArg")
    producer_routes(functions, growth, producer, 1)
    growth_forbidden = old_executor + ["UnifiedMaster_publicInstance", "ProducedContinuation_publicOrigin",
        "MasterResources_execute___"]
    absent(functions, growth, growth_forbidden, [projection_executor])
    for suffix in ["UnifiedMaster_Instance_grow___redArg", "UnifiedMaster_Growth_resume___redArg"]:
        extension = select(functions, suffix)
        producer_routes(functions, extension, producer, 1)
        absent(functions, extension, growth_forbidden, [projection_executor])
    # One initial execution plus one or two new suffix executions, respectively.
    for suffix, expected in [("UnifiedMaster_publicContinuation", 2), ("UnifiedMaster_publicGrowthTwice", 3)]:
        combined = select(functions, suffix)
        producer_routes(functions, combined, producer, expected)
        absent(functions, combined, old_executor + ["MasterResources_execute___"], [projection_executor])
    head = select(functions, "MasterResources_Cursor_headResources")
    absent(functions, head, old_executor + ["MasterResources_executeWithReferences", "UnifiedMaster_"], [projection_executor])
    # Check one recursive suffix and one produced head in the producer body.
    # The recursive suffix is a boundary when counting the current head.
    body_check = "l_codegen_producer_body"
    functions[body_check] = functions[producer]
    producer_routes(functions, body_check, producer, 1)
    producer_routes(functions, body_check, head, 1, boundaries=[producer])
    del functions[body_check]
    stored = select(functions, "CertifiedRoleGrouping_growStored___redArg")
    absent(functions, stored, ["MasterResources_execute", "MasterResources_Cursor_next",
        "runThreadedNextDiscovery", "buildFromExecutedDiscovery", "executeCausalOperationalHead"])
    restart = select(functions, "ProducedContinuation_executeRequests___redArg")
    absent(functions, restart, ["MasterResources_", "UnifiedMaster_", "Resources_Support_",
        "ConstitutedOperationalPrefix_", "ProducedContinuation_Source_"])
    calls(functions, restart, "ProducedContinuation_executeInput___redArg", 1)
    request = select(functions, "ProducedContinuation_executeInput___redArg")
    calls(functions, request, "LiveContinuation_execute", 1)
    live = select(functions, "LiveContinuation_execute")
    calls(functions, live, "LiveContinuation_produce", 1)
    project = select(functions, "ProducedContinuation_project___redArg")
    if "lean_alloc_closure" in functions[project]:
        raise ValueError("Restart projection allocates a closure over its historical source")
    if not re.search(r"lean_alloc_ctor\(0,\s*3,\s*0\)", functions[project]):
        raise ValueError("Restart-memory layout is not live state / output / readers")
    print("CODEGEN_MEMORY_OK: three top-level fields, no source closure; nested schema checked by AllConstantsAudit")
    # Follow field values from production to retention, rather than checking
    # project alone. Whole source profiles/results are tagged archives; the
    # executed-target selector and restricted live projection are named scope
    # boundaries, not a general claim about arbitrary client assignments.
    public_declaration = 'ConstitutiveSearch_EndogenousDecomposition_UnifiedMaster_publicInstance'
    if not entry.endswith(public_declaration):
        raise ValueError('Cannot resolve the public declaration namespace: ' + entry)
    prefix = entry[:-len(public_declaration)]
    module_root = 'RelationalPerimeter/Computation/ConstitutiveSearch/EndogenousDecomposition/'
    namespace = 'ConstitutiveSearch.EndogenousDecomposition.'
    def authority(declaration, module, variant=''):
        return owned_symbol(functions, compiled_parameters, owners, prefix,
                            namespace + declaration, module_root + module + '.c', variant)
    if authority('UnifiedMaster.publicInstance', 'UnifiedPublicCertificate') != entry:
        raise ValueError('Public declaration is not defined by its authoritative artifact')
    capture_boundaries = {
        authority('ExecutedCausalNormalization.result', 'ExecutedCausalNormalization', '___redArg'): 'archive',
        authority('ExecutedChainNormalization.target', 'ExecutedRoleIndexedReduction', '___redArg'): 'produced',
        authority('LiveContinuation.project', 'LiveResourceContinuation'): 'live',
    }
    getters = (
        authority('UnifiedMaster.Instance.reduction', 'UnifiedPublicCertificate', '___redArg'),
        authority('UnifiedMaster.Instance.normalization', 'UnifiedPublicCertificate', '___redArg'),
        authority('MasterResources.Cursor.state', 'MasterResourceExecution'),
        authority('causalStateOfThreadedState', 'InstrumentedExecutionRealization'),
    )
    print('CODEGEN_BOUNDARIES_OK: exact qualified symbols and unique defining artifacts')
    factory = select(functions, "ProducedContinuation_produce___redArg")
    capture = Analysis(functions, compiled_parameters, reachable, capture=True,
                       capture_boundaries=capture_boundaries)
    args = [Value(frozenset({'archive'})) for _ in compiled_parameters[factory]]
    source, _, _ = capture.run(factory, args)
    memory, _, _ = capture.run(project, [source])
    if 'archive' in memory.retained():
        raise ValueError("Historical value remains accessible in a retained output/reader closure")
    print("CODEGEN_CAPTURE_OK: source factory -> projected memory; produced target/live boundaries explicit")
    for suffix in ('UnifiedMaster_Instance_source', 'UnifiedMaster_Instance_checkpoint'):
        start = select(functions, suffix)
        flow = Analysis(functions, compiled_parameters, reachable, capture=True,
                        archive_getters=getters, capture_boundaries=capture_boundaries)
        value, _, _ = flow.run(start, [Value(frozenset({'archive'})) for _ in compiled_parameters[start]])
        if suffix.endswith('source'):
            value, _, _ = flow.run(project, [value])
        for field, label in ((0, 'live state'), (1, 'produced output'), (2, 'readers')):
            if field not in value.fields or 'archive' in value.fields[field].retained():
                raise ValueError(f'{start}: unresolved or archived retained {label}')
        print(f'CODEGEN_CAPTURE_OK {start}: live / output / readers; rich getters conservatively tainted')
    print("CODEGEN_OK: structural producer, extension and restart checks; no cost or physical-memory claim")


if __name__ == "__main__":
    try:
        main()
    except (OSError, ValueError) as error:
        print(f"CODEGEN_FAILED: {error}", file=sys.stderr)
        sys.exit(1)
