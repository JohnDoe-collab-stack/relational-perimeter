#!/usr/bin/env python3
"""Read-only static C checks for cached encounter descriptions.

The scope is named calls and transitive, statically known closure targets.
No total-cost, dynamic-callback, physical-topology or memory claim is made.
The existing encounter-production protocol is not rewritten by this check.
"""
from contextlib import redirect_stdout
import io
from pathlib import Path
import runpy
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
    raise ValueError("ENCOUNTER_DESCRIPTION_SELFTEST: invalid graph accepted")


def self_test():
    # A copied helper and a static closure remain within the checked graph.
    must_reject(lambda: shared["absent"]({
        "l_start": "{ l_helper(); }",
        "l_helper": "{ lean_alloc_closure(l_perform, 1, 0); }",
        "l_perform": "{}",
    }, "l_start", ["_perform"]))
    must_reject(lambda: shared["calls"]({"l_start": "{ l_head(); l_head(); }"}, "l_start", "l_head", 1))
    must_reject(lambda: shared["calls"]({"l_start": "{}"}, "l_start", "l_head", 1))
    must_reject(lambda: shared["owned_symbol"]({}, {}, {}, "l_", "head", "module.c"))


def main():
    self_test()
    functions, owners, texts = {}, {}, []
    for path in sorted((ROOT / ".lake/build/ir").rglob("*.c")):
        text = path.read_text(encoding="utf-8")
        texts.append(text)
        parsed = shared["bodies"](text)
        functions.update(parsed)
        for name in parsed:
            owners.setdefault(name, set()).add(path.relative_to(ROOT / ".lake/build/ir").as_posix())
    params = shared["parameters"](texts)

    def symbol(declaration, module, variant=""):
        return shared["owned_symbol"](functions, params, owners, "lp_relational_x2dperimeter_",
            "RelationalPerimeter.Relativity.Reconstruction." + declaration,
            "RelationalPerimeter/Relativity/Reconstruction/" + module + ".c", variant)

    precision_module = "EncounterPrecisionDescriptions"
    basis_module = "EncounterReadoutBasis"
    runner = symbol("runEncounterPrecisions", precision_module, "___redArg")
    head = symbol("refineEncounterPrecision", precision_module, "___redArg")
    compose = symbol("EncounterPrecisionDescription.compose", precision_module, "___redArg")
    shared["calls"](functions, runner, head, 1)
    shared["calls"](functions, runner, runner, 1)
    shared["calls"](functions, runner, compose, 1)
    for declaration, module in (
        ("refineEncounterPrecision", precision_module),
        ("runEncounterPrecisions", precision_module),
        ("EncounterPrecisionDescription.resume", precision_module),
        ("LocationAgreement.transportPrecision", precision_module),
        ("commonEncounterPrecisions", precision_module),
        ("meetEncounterReadouts", basis_module),
        ("LocalizedPresentation.realizeReadoutNeighborhood", basis_module),
        ("selectEncounterReadoutCover", basis_module),
        ("LocationAgreement.transportNeighborhood", basis_module),
    ):
        entry = symbol(declaration, module)
        shared["absent"](functions, entry, ["_perform", "_execute", "FutureContract_outcome"])
    print("ENCOUNTER_DESCRIPTIONS_CODEGEN_OK: one named head and suffix; no statically reachable producer")


if __name__ == "__main__":
    try:
        main()
    except (ValueError, OSError) as error:
        print(error, file=sys.stderr)
        sys.exit(1)
