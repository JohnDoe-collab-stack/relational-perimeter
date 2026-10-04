#!/usr/bin/env python3
"""Compiled-agent dependency and sharing checks, not a cost/heap theorem.

Reuse the existing local C-IR parser. No runtime scientific dependency is added.
"""
from pathlib import Path
import re
import runpy
import sys

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parent.parent
shared = runpy.run_path(str(ROOT / "scripts/check-unified-codegen.py"))


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


def main():
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
    for path in sorted((ROOT / ".lake/build/ir").rglob("*.c")):
        functions.update(bodies_with_objects(path.read_text(encoding="utf-8")))
    select, absent, calls = (shared[name] for name in ("select", "absent", "calls"))
    executor = select(functions, "Agent_executeRequests")
    request = select(functions, "Agent_executeInput")
    produced = select(functions, "Agent_executeProducedInput")
    step = select(functions, "Agent_step")
    worker = select(functions, "Agent_runSteps")
    decision = select(functions, "Agent_decideReply")
    forbidden = ["Agent_source", "Agent_History_", "MasterResources_", "UnifiedMaster_",
                 "Agent_normalizedRegister", "Agent_start", "Agent_prepare", "Agent_encodeSelection",
                 "Agent_decodeSelection", "ProducedContinuation_Source_", "profileFrontier",
                 "roleProfileFrontier", "roleOccurrenceProfileFrontier",
                 "roleProfileFiniteCarrier", "enumerateRoleOccurrenceProfiles"]
    # The unchanged live engine builds a two-source local output-image
    # readout *after* executing the action. It is not the global role-profile
    # frontier and does not select discovery. Check the discovery entry
    # separately, with the stricter image/readout exclusion.
    for entry in (executor, request, produced, worker, decision):
        absent(functions, entry, forbidden)
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
    shared["producer_routes"](functions, prepare, master, 1)
    print("AGENT_CODEGEN_OK: actual live step, one request head, no rich archive or extensive enumeration")


if __name__ == "__main__":
    try:
        main()
    except (OSError, ValueError) as error:
        print(f"AGENT_CODEGEN_FAILED: {error}", file=sys.stderr)
        sys.exit(1)
