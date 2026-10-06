#!/usr/bin/env python3
"""Named compiled dependency check for the role-signature consumer.

This checks named C functions and static closure targets, not arbitrary client
callbacks, heap liveness, a wall-clock bound, or total computation cost.
"""
from pathlib import Path
import importlib.util
import subprocess
import sys

sys.dont_write_bytecode = True

ROOT = Path(__file__).resolve().parent.parent


def main():
    spec = importlib.util.spec_from_file_location(
        "signature_codegen_helpers", ROOT / "scripts/check-unified-codegen.py")
    helpers = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(helpers)
    inventory = subprocess.run(
        ["git", "ls-files", "--cached", "--others", "--exclude-standard", "--", "*.lean"],
        cwd=ROOT, capture_output=True, text=True, check=True)
    functions = {}
    for relative in inventory.stdout.splitlines():
        # Production cannot import Tests under the enforced module strata.
        # Test-only artifacts are not callees of the measured public consumer.
        if relative.replace("\\", "/").startswith("Tests/"):
            continue
        if not (ROOT / relative).is_file():
            continue
        compiled = ROOT / ".lake/build/ir" / Path(relative).with_suffix(".c")
        if not compiled.is_file():
            raise ValueError(f"Missing compiled dependency artifact: {compiled}")
        source = compiled.read_text(encoding="utf-8")
        functions.update(helpers.bodies(source))
        helpers.add_static_objects(functions, helpers.LITERALS.sub(
            lambda match: " " * len(match.group()), source))
    forbidden = ["roleProfileFiniteCarrier", "roleOccurrenceProfileFrontier",
                 "roleProfileFrontier", "Adaptive_outputRegime",
                 "binaryProfiles", "enumerateProfiles"]
    for suffix in ["ContinuationSignatures_produceRoleSignature",
                   "ContinuationSignatures_executeReadings",
                   "ContinuationSignatures_publicSignatureMemory",
                   "ContinuationSignatures_ReachableAgent_executeSignedInput",
                   "ContinuationSignatures_ReachableAgent_canonicalMemory"]:
        entry = helpers.select(functions, suffix)
        helpers.absent(functions, entry, forbidden)
        if suffix == "ContinuationSignatures_produceRoleSignature":
            helpers.absent(functions, entry, ["imageRegime", "frontier"])
        if "ReachableAgent" in suffix:
            helpers.absent(functions, entry,
                           ["Agent_History_", "Agent_sourcePerform", "Agent_sourceRunSteps",
                            "ReachableAgent_historyAt", "ReachableAgent_coveredSource"])
    runtime = helpers.select(functions, "ContinuationSignatures_executeReadings")
    helpers.absent(functions, runtime,
                   ["ContinuationSignatures_executeSigned", "MasterResources_execute",
                    "executeCausalOperationalExecutionHistory"])
    signature = helpers.select(functions, "ContinuationSignatures_produceRoleSignature")
    helpers.calls(functions, runtime, "ContinuationSignatures_produceRoleSignature", 1)
    helpers.calls(functions, runtime, "ContinuationSignatures_executeReadings", 1)
    graph = helpers.reachable(functions, signature)
    if not any("ContinuationSignatures_producedOutput" in name for name in graph):
        raise ValueError("Signature consumer no longer reads the produced action output")
    # The reused master does form its two-occurrence local image. This is not
    # an absence-of-all-image-construction claim. The public Lean client test
    # local_image_domain_has_two_occurrences protects that typed local scope.
    runtime_graph = helpers.reachable(functions, runtime)
    local_images = sorted(name for name in runtime_graph
                          if "imageRegime" in name and "producedRoleOutputRegime" in name)
    print(f"SIGNATURE_LOCAL_IMAGES: {len(local_images)} named local-image helpers; domain size 2 in Lean")
    print("SIGNATURE_CODEGEN_OK: named action-output chain; no global profile enumeration")
    print("REACHABLE_SIGNATURE_CODEGEN_OK: actual runtime result and replay engine; no rich source archive")


if __name__ == "__main__":
    try:
        main()
    except (OSError, ValueError, subprocess.CalledProcessError) as error:
        print(f"SIGNATURE_CODEGEN_FAILED: {error}", file=sys.stderr)
        sys.exit(1)
