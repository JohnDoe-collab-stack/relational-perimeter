#!/usr/bin/env python3
"""Read-only named-sharing checks for the declared finite coupling assembly.

Only named calls and transitively known C/closure targets are covered.
No physical-location, total-cost or dynamic-callback claim follows.
"""
from contextlib import redirect_stdout
import io
from pathlib import Path
import runpy
import re
import sys

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parent.parent
shared = runpy.run_path(str(ROOT / "scripts/check-unified-codegen.py"))


def must_reject(action):
    try:
        with redirect_stdout(io.StringIO()):
            action()
    except ValueError:
        return
    raise ValueError("NETWORK_SELFTEST: invalid sharing accepted")


def tail_loop(body):
    if body.count("goto _start;") != 1 or not re.search(
        r"\bv_course_\d+_\s*=\s*v___x_\d+_;\s*v_x_\d+_\s*=\s*v_tail_\d+_;\s*goto _start;", body
    ):
        raise ValueError("NETWORK_TAIL: missing actual produced-course and received-tail resumption")


def main():
    must_reject(lambda: tail_loop("{ goto _start; }"))
    must_reject(lambda: shared["calls"]({"l_root": "{ l_head(); l_head(); }"}, "l_root", "l_head", 1))
    must_reject(lambda: shared["calls"]({"l_root": "{}"}, "l_root", "l_head", 1))
    must_reject(lambda: shared["absent"]({"l_root": "{ l_helper(); }",
        "l_helper": "{ lean_alloc_closure(l_perform, 1, 0); }", "l_perform": "{}"}, "l_root", ["_perform"]))
    must_reject(lambda: shared["owned_symbol"]({}, {}, {}, "l_", "head", "missing.c"))
    functions, owners, texts = {}, {}, []
    for path in sorted((ROOT / ".lake/build/ir").rglob("*.c")):
        text = path.read_text(encoding="utf-8")
        texts.append(text)
        parsed = shared["bodies"](text)
        functions.update(parsed)
        for name in parsed:
            owners.setdefault(name, set()).add(path.relative_to(ROOT / ".lake/build/ir").as_posix())
    params = shared["parameters"](texts)

    def symbol(name, module, layer="Production", variant="___redArg"):
        declaration = "RelationalPerimeter.Relativity." + layer + "." + name
        return shared["owned_symbol"](functions, params, owners, "lp_relational_x2dperimeter_", declaration,
            "RelationalPerimeter/Relativity/" + layer + "/" + module + ".c", variant)

    core, passages = "CouplingNetworks", "NetworkEncounterPassages"
    signal = symbol("Network.performSignal", core)
    delivery = symbol("Network.performDelivery", core)
    encounter = symbol("Network.performEncounter", core)
    fill = symbol("Network.performFill", passages)
    heads = symbol("Network.producePassageHeads", passages)
    continued = symbol("Network.runContinuedPassage", passages)
    advance = symbol("Network.Course.advance", passages)
    extend = symbol("Network.Course.extend", passages)
    recurring = shared["owned_symbol"](functions, params, owners, "lp_relational_x2dperimeter_",
        "RelationalPerimeter.Relativity.Production.performRecurring",
        "RelationalPerimeter/Relativity/Production/RecurringInteractions.c", "")
    for entry in (signal, delivery, encounter):
        shared["calls"](functions, entry, recurring, 1)
    shared["calls"](functions, fill, delivery, 2)
    for entry in (signal, fill, encounter):
        shared["calls"](functions, heads, entry, 1)
    shared["calls"](functions, continued, heads, 1)
    shared["calls"](functions, continued, signal, 1)
    shared["calls"](functions, advance, heads, 1)
    shared["calls"](functions, extend, advance, 1)
    shared["calls"](functions, extend, extend, 0)
    tail_loop(functions[extend])
    for name, module, layer in (
        ("Network.PassageHeads.history", passages, "Production"),
        ("Network.PassageHeads.used", passages, "Production"),
        ("networkFirst", "NetworkEncounterDescriptions", "Reconstruction"),
        ("networkSecond", "NetworkEncounterDescriptions", "Reconstruction"),
        ("networkEncounterAgreement", "NetworkEncounterDescriptions", "Reconstruction"),
        ("networkAnchorConstraints", "NetworkEncounterDescriptions", "Reconstruction"),
    ):
        shared["absent"](functions, symbol(name, module, layer), ["_perform", "_execute", "FutureContract_outcome"])
    print("NETWORK_ENCOUNTERS_CODEGEN_OK: shared four-production passages and producer-free descriptions")


if __name__ == "__main__":
    try:
        main()
    except (ValueError, OSError) as error:
        print(error, file=sys.stderr)
        sys.exit(1)
