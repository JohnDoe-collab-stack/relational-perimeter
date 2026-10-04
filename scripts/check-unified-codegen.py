#!/usr/bin/env python3
"""Structural C-IR checks for the public producer and restricted restart API.

Includes transitive callees and statically named closure functions/initializers.
It does not establish total cost, physical memory bounds, or properties of
arbitrary client-provided callbacks. Those are not claims of this contract.
"""
from pathlib import Path
import re
import sys

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


def absent(functions, start, forbidden):
    graph = reachable(functions, start)
    bad = sorted(name for name in graph if any(fragment in name for fragment in forbidden))
    if bad:
        raise ValueError(f"Forbidden transitive dependency from {start}: {bad}")
    print(f"CODEGEN_GRAPH_OK {start}: {len(graph)} functions, static closure targets included")


def calls(functions, name, suffix, expected):
    actual = sum(1 for token in re.findall(r"\b((?:l|lp)_\w+)\s*\(", functions[name])
                 if token.endswith(suffix))
    if actual != expected:
        raise ValueError(f"{name}: {suffix}: expected {expected} calls, found {actual}")
    print(f"CODEGEN_CALL_OK {name}: {suffix}={actual}")


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
    functions = {}
    for path in (ROOT / ".lake/build/ir").rglob("*.c"):
        functions.update(bodies(path.read_text(encoding="utf-8")))
    if not functions:
        raise ValueError("Missing generated C; run lake build first")
    entry = select(functions, "UnifiedMaster_publicInstance")
    calls(functions, entry, "MasterResources_executeWithReferences", 1)
    calls(functions, entry, "MasterResources_execute", 0)
    growth = select(functions, "UnifiedMaster_resource__history__extension___redArg")
    calls(functions, growth, "MasterResources_executeWithReferences", 1)
    absent(functions, growth, ["UnifiedMaster_publicInstance", "ProducedContinuation_publicOrigin"])
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
    print("CODEGEN_MEMORY_OK: three live fields, no closure over the historical source")
    print("CODEGEN_OK: structural producer, extension and restart checks; no cost or physical-memory claim")


if __name__ == "__main__":
    try:
        main()
    except (OSError, ValueError) as error:
        print(f"CODEGEN_FAILED: {error}", file=sys.stderr)
        sys.exit(1)
