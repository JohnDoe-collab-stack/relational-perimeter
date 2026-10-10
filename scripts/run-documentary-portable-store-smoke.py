#!/usr/bin/env python3
"""Store-only byte restart: literal graph oracle, new deduction and rejections.

This does not reload a complete present or execute new master quotations.
Raw clients and files stay in a temporary directory outside the repository.
"""
import copy
import json
from pathlib import Path
import runpy
import subprocess
import sys
import tempfile

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parent.parent
NORMAL = [[1, 1, 1, 1, 2], [0, 1, 42], [1, 0, 1, 0, 1], [0, 2, 43], [0, 1, 42]]
HOSTILE = [[1, 1, 2, 2, 2], [1, 0, 1, 1, 0], *NORMAL[1:]]
WRONG_ORDER = [[1, 1, 1, 1, 2], [0, 1, 42], [1, 0, 2, 1, 1],
               [1, 0, 0, 1, -1], [0, 2, 43], [0, 1, 42]]

COMMON = r"""
set_option genInjectivity false
set_option maxRecDepth 8192
set_option maxHeartbeats 30000000
namespace PortableStoreSmoke
open ConstitutiveSearch.Resources
open ConstitutiveSearch.Agent.Local.Documentary

def write (path : String) (bytes : List UInt8) : IO Unit :=
  IO.FS.writeBinFile path ⟨bytes.toArray⟩

def say (message : String) : IO Unit := do
  let output ← IO.getStdout
  output.write message.toUTF8
"""
ENTRY = r"""
end PortableStoreSmoke
def main (args : List String) : IO Unit := match args with
  | [checkpoint, restored, continued] => PortableStoreSmoke.run checkpoint restored continued
  | [] => throw (IO.userError "Expected three paths")
  | [_] => throw (IO.userError "Expected three paths")
  | [_, _] => throw (IO.userError "Expected three paths")
  | _ :: _ :: _ :: _ :: _ => throw (IO.userError "Expected three paths")
"""
START = ("import Tests.LocalAlignment.DocumentaryPortableStore\n"
         "import Tests.LocalAlignment.DocumentaryPortableStart\n" + COMMON + r"""
def proposal (mode : Nat) (view : Adaptive.Observation) : Option Adaptive.Proposal :=
  if mode == 0 then none
  else if mode == 1 then some .current
  else if mode == 2 then some (.inspect 0)
  else if mode == 3 then some (.quote 99 99)
  else if mode == 4 then match view.goal with
    | .quotation _ => some (.quote 0 0)
    | .conclusion _ => if view.round == 2 then some (.deduce 2 1 0) else some (.deduce 0 1 1)
  else if mode == 5 then match view.goal with
    | .quotation _ => some .reverseSources
    | .conclusion _ => some .current
  else if mode == 6 then match view.goal with
    | .quotation _ => some .current
    | .conclusion _ => if view.round == 2 then some (.deduce 0 0 1) else some .current
  else if view.round == 0 then some (.quote 0 1)
  else if view.round == 1 then some (.quote 1 2)
  else if view.round == 2 then some (.deduce 0 1 0)
  else if view.round == 3 then some (.quote 0 1)
  else some (.deduce 1 1 1)

def policy : Adaptive.Policy Nat :=
  ⟨fun context _ view => ⟨context + 1, proposal __MODE__ view⟩, fun _ => 0⟩

def run (checkpoint _restored _continued : String) : IO Unit := do
  let initial := PortableStart.initial ConstitutiveSearch.EndogenousDecomposition.VariableMaster.Example.origin
  let session : Adaptive.Session PortableCheckpoint.sources PortableCheckpoint.contract PortableCheckpoint.policy Nat [] :=
    ⟨initial, 0, 0, none⟩
  let actual := Adaptive.run policy (fun _ => ⟨"received task", __FORGET__⟩) session
    (PortableStart.script.append PortableStart.remaining)
  write checkpoint (PortableStore.save actual.1.frame.store)
  say "STORE_SAVED\n"
""" + ENTRY)
RESUME = "import Tests.LocalAlignment.DocumentaryPortableStore\n" + COMMON + r"""
def run (checkpoint restored continued : String) : IO Unit := do
  let bytes ← IO.FS.readBinFile checkpoint
  match PortableStore.load PortableCheckpoint.sources PortableCheckpoint.contract PortableCheckpoint.policy bytes.data.toList with
  | .error _ => throw (IO.userError "Store checkpoint rejected")
  | .ok store =>
      match Adaptive.locate store.1 0 with
      | none => throw (IO.userError "No premise for smoke continuation")
      | some top =>
          let actual := Deduction.execute store.2 PortableCheckpoint.sum top.2 top.2
          match actual with
          | .refused _ => throw (IO.userError "Continuation rule refused")
          | .accepted action permission =>
              let next : Deduction.Store PortableCheckpoint.sources PortableCheckpoint.contract PortableCheckpoint.policy :=
                ⟨_, Deduction.incorporateDerived action permission⟩
              write restored (PortableStore.save store)
              write continued (PortableStore.save next)
              say "STORE_RESTORED_AND_CONTINUED\n"
""" + ENTRY


def audited(source, names):
    return source + "\n/- AXIOM_AUDIT_BEGIN -/\n" + "".join(
        "#print axioms " + name + "\n" for name in names) + "/- AXIOM_AUDIT_END -/\n"


def invoke(source, client, paths, names, marker, success=True):
    client.write_text(audited(source, names), encoding="utf-8", newline="\n")
    process = subprocess.Popen(["lake", "env", "lean", "--run", str(client), *map(str, paths)],
                               cwd=ROOT, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    try:
        stdout, stderr = process.communicate(timeout=120)
    except subprocess.TimeoutExpired:
        process.kill()
        process.communicate()
        raise ValueError("Store smoke client timed out") from None
    lines = stdout.decode("utf-8", "strict").splitlines()
    expected = ["'" + name + "' does not depend on any axioms" for name in names]
    if success:
        if process.returncode or stderr or lines != expected + [marker]:
            raise ValueError("Store client failed: " + stdout.decode("utf-8", "replace") + stderr.decode("utf-8", "replace"))
    elif not process.returncode or lines != expected or b"Store checkpoint rejected" not in stderr:
        raise ValueError("Rejection did not reach the audited store loader")
    return process.pid


def main():
    wire = runpy.run_path(str(ROOT / "scripts/run-documentary-checkpoint-smoke.py"))["wire"]
    base = {"version": 1, "schema": 2, "round": 0, "depth": 0, "task": 0,
            "nodes": NORMAL, "bindings": []}
    processes = []
    names = ["PortableStoreSmoke.write", "PortableStoreSmoke.say", "PortableStoreSmoke.run", "main"]
    with tempfile.TemporaryDirectory(prefix="rp-portable-store-") as temporary:
        directory = Path(temporary)
        for mode in range(8):
            for forget in (False, True):
                paths = [directory / f"{mode}-{forget}-{name}.bin" for name in ("checkpoint", "restored", "continued")]
                source = START.replace("__MODE__", str(mode)).replace("__FORGET__", "true" if forget else "false")
                start_names = names[:2] + ["PortableStoreSmoke.proposal", "PortableStoreSmoke.policy"] + names[2:]
                start_pid = invoke(source, directory / "Start.lean", paths, start_names, "STORE_SAVED")
                nodes = HOSTILE if mode == 4 else WRONG_ORDER if mode == 6 else NORMAL
                state = {**base, "nodes": nodes}
                assert paths[0].read_bytes() == wire(state), "Actual graph differs from literal oracle"
                assert not paths[1].exists() and not paths[2].exists(), "Start executed a future"
                resume_pid = invoke(RESUME, directory / "Resume.lean", paths, names, "STORE_RESTORED_AND_CONTINUED")
                assert start_pid != resume_pid, "Store restart reused the same process"
                assert paths[1].read_bytes() == paths[0].read_bytes(), "Restored canonical graph changed"
                assert paths[2].read_bytes() == wire({**state, "nodes": [[1, 1, 0, 0, 4], *nodes]}), "New actual deduction changed"
                processes += [start_pid, resume_pid]
        mutations = []
        for key, value in (("version", 2), ("schema", 1), ("round", 1), ("depth", 1), ("task", 1), ("bindings", [0])):
            changed = copy.deepcopy(base); changed[key] = value
            mutations.append((key, wire(changed)))
        for label, nodes in (("source", [[0, 0, 42]]), ("value", [[0, 1, 43]]),
                             ("rule", [[1, 2, 0, 0, 0], [0, 1, 42]]),
                             ("premise", [[1, 0, 0, 1, 0], [0, 1, 42]])):
            mutations.append((label, wire({**base, "nodes": nodes})))
        mutations += [("truncated", wire(base)[:-1]), ("trailing", wire(base) + b"\x02"),
                      ("alphabet", b"\xff" + wire(base)[1:])]
        for label, payload in mutations:
            paths = [directory / f"bad-{label}-{name}.bin" for name in ("checkpoint", "restored", "continued")]
            paths[0].write_bytes(payload)
            processes.append(invoke(RESUME, directory / "Resume.lean", paths, names, "", False))
            assert not paths[1].exists() and not paths[2].exists(), "Rejected bytes executed or published a future"
    assert "PortableStart" not in RESUME and "Cases" not in RESUME
    assert RESUME.count("let actual := Deduction.execute") == 1
    print("DOCUMENTARY_PORTABLE_STORE_SMOKE_OK " + json.dumps({
        "adaptive_cases": 16, "physical_processes": len(processes), "rejections": len(mutations),
        "literal_graphs": 3, "new_deduction_value": 4,
        "start_runtime_audits": 6, "resume_runtime_audits": 4,
        "scope": "canonical store only; received configuration; no complete-present or master restart"
    }, separators=(",", ":")))


if __name__ == "__main__":
    try:
        main()
    except (AssertionError, OSError, ValueError) as error:
        print("DOCUMENTARY_PORTABLE_STORE_SMOKE_ERROR: " + str(error), file=sys.stderr)
        sys.exit(1)
