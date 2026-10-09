#!/usr/bin/env python3
"""Read-only checks of named sites in the measured-path/encounter bridge.

Like the finite-network checker, this checks named C call sites and static
helper/closure reachability, not multiplicity through arbitrary callbacks.
The relay recursion is checked per node, never counted as one elementary
operation. No time, heap, physical-law or geometric conclusion follows.
"""
from contextlib import redirect_stdout
import io
from pathlib import Path
import re
import runpy
import sys

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parent.parent
shared = runpy.run_path(str(ROOT / "scripts/check-unified-codegen.py"))


def reject(action):
    try:
        with redirect_stdout(io.StringIO()):
            action()
    except ValueError:
        return
    raise ValueError("MEASURED_SELFTEST: accepted invalid named sharing")


def tail_loop(body):
    if body.count("goto _start;") != 1 or not re.search(
        r"\bv_prior_\d+_\s*=\s*v_(?:next|head)_\d+_;\s*v_x_\d+_\s*=\s*v_tail_\d+_;\s*goto _start;", body
    ):
        raise ValueError("MEASURED_TAIL: missing produced-state/received-tail resumption")


def main():
    reject(lambda: tail_loop("{ goto _start; }"))
    reject(lambda: shared["calls"]({"l_root": "{ l_head(); l_head(); }"}, "l_root", "l_head", 1))
    reject(lambda: shared["calls"]({"l_root": "{}"}, "l_root", "l_head", 1))
    reject(lambda: shared["absent"]({"l_root": "{ l_helper(); }",
        "l_helper": "{ lean_alloc_closure(l_perform, 1, 0); }", "l_perform": "{}"}, "l_root", ["_perform"]))
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
            "RelationalPerimeter.Relativity." + declaration,
            "RelationalPerimeter/Relativity/" + module + ".c", variant)

    module = "Production/EncounterRelativePaths"
    measure = symbol("Production.Encounter.measure", module)
    refine = symbol("Production.Encounter.refine", module)
    relay = symbol("Production.Encounter.runRelays", module, "___redArg")
    resume = symbol("Production.Encounter.MeasurementRun.resume", module, "___redArg")
    runner = symbol("Production.Encounter.MeasurementRun.runMore", module, "___redArg")
    head = symbol("Production.Encounter.measureThen", module)
    delivery = symbol("Production.Encounter.performDelivery", "Production/ConstitutedEncounters", "___redArg")
    encounter = symbol("Production.Encounter.performEncounter", "Production/ConstitutedEncounters")
    signal = symbol("Production.Encounter.performSignal", "Production/ConstitutedEncounters")
    for entry, target, expected in (
        (measure, delivery, 2), (measure, encounter, 1),
        (refine, relay, 2), (refine, measure, 1), (resume, refine, 1),
        (head, measure, 1), (relay, signal, 1), (relay, relay, 1),
        (runner, resume, 1), (runner, runner, 0),
    ):
        shared["calls"](functions, entry, target, expected)
    tail_loop(functions[runner])
    constraints = "Reconstruction/MeasuredPathConstraints"
    advance = symbol("Reconstruction.MeasuredDescriptionRun.advance", constraints, "___redArg")
    describe = symbol("Reconstruction.describeMeasuredRefinement", constraints, "___redArg")
    corrected = symbol("Reconstruction.correctedRefinementValue", constraints, "___redArg")
    descriptions = symbol("Reconstruction.MeasuredDescriptionRun.runMore", constraints, "___redArg")
    consumed = symbol("Reconstruction.measuredRelativeValue", "Reconstruction/MeasuredEncounterDescriptions")
    for entry, target, expected in (
        (advance, refine, 1), (advance, describe, 1), (describe, corrected, 1),
        (corrected, consumed, 1), (descriptions, advance, 1), (descriptions, descriptions, 0),
    ):
        shared["calls"](functions, entry, target, expected)
    tail_loop(functions[descriptions])
    grouping = "Reconstruction/MeasuredLocationGrouping"
    check_group = symbol("Reconstruction.checkAndGroupMeasuredLocations", grouping)
    recognize = symbol("Reconstruction.searchMeasuredLocationRaccord", grouping)
    common = symbol("Reconstruction.groupMeasuredLocations", grouping, "___redArg")
    grouped = symbol("Reconstruction.groupedMeasuredDescription", grouping, "___redArg")
    for entry, target in ((check_group, recognize), (check_group, common), (grouped, check_group)):
        shared["calls"](functions, entry, target, 1)
    for declaration, owner, variant in (
        ("Production.Encounter.Measurement.next", module, ""),
        ("Production.Encounter.Measurement.history", module, "___redArg"),
        ("Reconstruction.measuredFirst", "Reconstruction/MeasuredEncounterDescriptions", "___redArg"),
        ("Reconstruction.measuredSecond", "Reconstruction/MeasuredEncounterDescriptions", "___redArg"),
        ("Reconstruction.measuredRelativeValue", "Reconstruction/MeasuredEncounterDescriptions", ""),
        ("Reconstruction.measuredPathValue", constraints, ""),
        ("Reconstruction.describeMeasuredRefinement", constraints, "___redArg"),
        ("Reconstruction.correctedRefinementValue", constraints, "___redArg"),
        ("Reconstruction.commonMeasuredDescriptions", constraints, "___redArg"),
        ("Production.Encounter.MeasurementChain.drift", "Production/EncounterMeasurementLaws", "___redArg"),
        ("Reconstruction.searchMeasuredLocationRaccord", grouping, ""),
        ("Reconstruction.checkAndGroupMeasuredLocations", grouping, ""),
        ("Reconstruction.groupedMeasuredDescription", grouping, "___redArg"),
        ("Reconstruction.ConstrainedMeasuredLocation.prolong", grouping, "___redArg"),
    ):
        shared["absent"](functions, symbol(declaration, owner, variant),
                         ["_perform", "_execute", "_Encounter_refine", "FutureContract_outcome"])
    print("MEASURED_ENCOUNTER_CODEGEN_OK: named shared measurement/constraint sites, checked grouping, actual successors and static producer-free consumers")


if __name__ == "__main__":
    try:
        main()
    except (ValueError, OSError) as error:
        print(error, file=sys.stderr)
        sys.exit(1)
