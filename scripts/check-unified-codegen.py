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


def producer_routes(functions, start, target, expected, boundaries=()):
    """Count static call/reference routes up to the producer boundary.

    The producer's own recursion is intentionally not unfolded. A helper or
    closure cannot conceal another route; an upstream recursive cycle fails
    closed. This is a check of these compiled entry points, not a time bound.
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
    for path in compiled:
        functions.update(bodies(path.read_text(encoding="utf-8")))
    if not functions:
        raise ValueError("Missing generated C; run lake build first")
    entry = select(functions, "UnifiedMaster_publicInstance")
    producer = select(functions, "MasterResources_executeWithReferences")
    projection_executor = select(functions, "MasterResources_execute")
    producer_routes(functions, entry, producer, 1)
    old_executor = ["executeCausalOperationalExecutionHistory", "executeCausalOperationalHead"]
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
    print("CODEGEN_OK: structural producer, extension and restart checks; no cost or physical-memory claim")


if __name__ == "__main__":
    try:
        main()
    except (OSError, ValueError) as error:
        print(f"CODEGEN_FAILED: {error}", file=sys.stderr)
        sys.exit(1)
