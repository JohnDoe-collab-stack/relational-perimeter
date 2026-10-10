#!/usr/bin/env python3
"""Fresh-process file restart and independently specified binary fixture oracle."""
import copy
import json
from pathlib import Path
import runpy
import sys
import tempfile

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parent.parent
BASE = {"version": 1, "schema": 1, "round": 4, "depth": 3, "task": 1,
        "nodes": [[0, 1, 42], [1, 0, 1, 0, 1], [0, 2, 43], [0, 1, 42]],
        "bindings": [0, 1, 2, 3]}
FINAL = {**BASE, "round": 5, "task": 0,
         "nodes": [[1, 1, 1, 1, 2], *BASE["nodes"]], "bindings": [0, 1, 2, 3, 4]}
DOCUMENT = ("Dossier documentaire\nConclusion : 2\nOccurrence : 0\nOrigines : 1,2,1,2\nRegles : 1,0,0\nSources :\n"
            "[document=1 version=1 excerpt=0 position=1] La mesure certifiee est 42.\n"
            "[document=1 version=2 excerpt=0 position=2] La mesure revisee est 43.\n"
            "[document=1 version=1 excerpt=0 position=1] La mesure certifiee est 42.\n"
            "[document=1 version=2 excerpt=0 position=2] La mesure revisee est 43.\n").encode("utf-8")


def wire(state):
    words = [state[key] for key in ("version", "schema", "round", "depth", "task")]
    words += [len(state["nodes"]), len(state["bindings"])]
    words += [word for node in state["nodes"] for word in node] + state["bindings"]
    def word(value):
        return bytes([0 if value >= 0 else 1]) + bytes([1]) * (value if value >= 0 else -value - 1) + bytes([2])
    return word(len(words)) + b"".join(word(value) for value in words)


def main():
    adapter = runpy.run_path(str(ROOT / "apps/local-alignment/documentary-checkpoint.py"))
    invoke = adapter["invoke"]
    receipts = []
    with tempfile.TemporaryDirectory(prefix="rp-documentary-restart-") as temporary:
        directory = Path(temporary)
        split = directory / "split"
        continuous = directory / "continuous"
        receipts.append(invoke("start", split))
        assert (split / "checkpoint.bin").read_bytes() == wire(BASE), "Actual prefix bytes changed"
        assert not (split / "dossier.md").exists(), "Start unexpectedly published the final dossier"
        receipts.append(invoke("resume", split))
        receipts.append(invoke("continuous", continuous))
        assert receipts[0]["process_id"] != receipts[1]["process_id"], "Restart used the same process"
        assert "PortableStart" not in receipts[1]["client_import"], "Resume imported the start execution"
        for workspace in (split, continuous):
            assert (workspace / "dossier.md").read_bytes() == DOCUMENT, "Actual rendered proof dossier differs"
            assert (workspace / "result.bin").read_bytes() == wire(FINAL), "Actual final resource/port bytes differ"
        original_document = (split / "dossier.md").read_bytes()
        receipts.append(invoke("resume", split))
        assert (split / "dossier.md").read_bytes() == original_document, "Repeated fresh load changed output"
        assert (split / "checkpoint.bin").read_bytes() == wire(BASE), "Resume changed the received checkpoint"

        mutations = []
        for key, value in (("version", 2), ("schema", 2), ("round", 3), ("depth", 4), ("task", 2)):
            state = copy.deepcopy(BASE); state[key] = value
            mutations.append((key, wire(state)))
        for label, index, field, value in (
                ("changed-value", 1, 4, 2), ("private-source", 3, 1, 0), ("missing-source", 3, 1, 99),
                ("duplicate-forbidden-rule", 1, 1, 2), ("missing-rule", 1, 1, 99),
                ("missing-premise", 1, 2, 99), ("reversed-premises", 1, 2, 0),
                ("negative-position", 3, 1, -1)):
            state = copy.deepcopy(BASE); state["nodes"][index][field] = value
            mutations.append((label, wire(state)))
        for label, positions in (("wrong-binding", [0, 0, 2, 3]), ("missing-binding", [0, 1, 2]),
                                  ("extra-binding", [0, 1, 2, 3, 0]), ("missing-bound-occurrence", [0, 1, 2, 99])):
            state = copy.deepcopy(BASE); state["bindings"] = positions
            mutations.append((label, wire(state)))
        mutations += [("truncated", wire(BASE)[:-1]), ("trailing", wire(BASE) + b"\x02"),
                      ("invalid-byte", b"\xff" + wire(BASE)[1:])]
        for label, bytes_ in mutations:
            bad = directory / label; bad.mkdir()
            (bad / "checkpoint.bin").write_bytes(bytes_)
            receipts.append(invoke("resume", bad, expect_success=False))
            assert not (bad / "dossier.md").exists(), "Rejected checkpoint published a document: " + label
            assert not (bad / "result.bin").exists(), "Rejected checkpoint published a result: " + label

        # Equal baseline values retain their distinct local occurrences. This is
        # a coherent alternative binding payload, not claimed to be the original
        # saved history; loader validity is separate from file authenticity.
        alternate = copy.deepcopy(BASE); alternate["bindings"] = [3, 1, 2, 0]
        other = directory / "distinct-equal-occurrences"; other.mkdir()
        (other / "checkpoint.bin").write_bytes(wire(alternate))
        receipts.append(invoke("resume", other))
        alternate_final = {**FINAL, "bindings": [0, 4, 2, 3, 1]}
        assert (other / "result.bin").read_bytes() == wire(alternate_final), "Equal-valued occurrences were merged"
        assert (other / "dossier.md").read_bytes() == DOCUMENT
        assert adapter["RESUME"].count("let finished := resume loaded") == 1
        assert "PortableStart" not in adapter["RESUME"] and "PortableCases" not in adapter["RESUME"]
        assert "PortableStart.remaining" not in adapter["START"]
    summary = {"status": "passed", "physical_processes": len(receipts), "rejections": len(mutations),
               "normal_and_alternative_runs": 5, "runtime_audits_per_process": 5,
               "checkpoint_bytes": len(wire(BASE)), "document_bytes": len(DOCUMENT),
               "same_uninterrupted_document_and_resources": True, "receipts": receipts}
    print("DOCUMENTARY_CHECKPOINT_SMOKE_OK " + json.dumps(summary, separators=(",", ":")))


if __name__ == "__main__":
    try:
        main()
    except (AssertionError, OSError, ValueError, RuntimeError) as error:
        print("DOCUMENTARY_CHECKPOINT_SMOKE_ERROR: " + str(error), file=sys.stderr)
        sys.exit(1)
