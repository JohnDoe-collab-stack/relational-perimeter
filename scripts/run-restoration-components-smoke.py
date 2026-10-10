#!/usr/bin/env python3
"""Dossier bytes across processes; typed master/present restoration in process.

The byte restart resumes the dossier component only. It performs a new certified
extraction; it does not load a master cursor or claim a full adaptive restart.
"""
import copy
from pathlib import Path
import runpy
import subprocess
import sys
import tempfile

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parent.parent
BASE = {"version": 1, "schema": 3, "round": 0, "depth": 0, "task": 0,
        "nodes": [], "bindings": [1, 2, 1]}
SOURCE_TEXT = ("[document=1 version=1 excerpt=0 position=1] La mesure certifiee est 42.\n"
               "[document=1 version=2 excerpt=0 position=2] La mesure revisee est 43.\n"
               "[document=1 version=1 excerpt=0 position=1] La mesure certifiee est 42.\n").encode("utf-8")

COMMON = r"""
set_option genInjectivity false
set_option maxRecDepth 8192
set_option maxHeartbeats 30000000
namespace RestorationComponentsSmoke
open ConstitutiveSearch.Resources
open ConstitutiveSearch.Agent.Local.Documentary

def write (path : String) (bytes : List UInt8) : IO Unit := IO.FS.writeBinFile path ⟨bytes.toArray⟩
def say (message : String) : IO Unit := do
  let output ← IO.getStdout
  output.write message.toUTF8
"""
ENTRY = r"""
end RestorationComponentsSmoke
def main (args : List String) : IO Unit := match args with
  | [checkpoint, restored, continued, document] => RestorationComponentsSmoke.run checkpoint restored continued document
  | [] => throw (IO.userError "Expected four paths")
  | [_] => throw (IO.userError "Expected four paths")
  | [_, _] => throw (IO.userError "Expected four paths")
  | [_, _, _] => throw (IO.userError "Expected four paths")
  | _ :: _ :: _ :: _ :: _ :: _ => throw (IO.userError "Expected four paths")
"""
RESUME = "import Tests.LocalAlignment.DocumentaryPortableMemory\n" + COMMON + r"""
def outputs {items : List Citation} :
    ({item : Citation} → Ref items item → Conforms PortableCheckpoint.sources PortableCheckpoint.contract item) →
    List (Output PortableCheckpoint.sources PortableCheckpoint.contract) :=
  match items with
  | [] => fun _ => []
  | item :: rest => fun valid => ⟨item, valid .here⟩ :: outputs (items := rest) (fun ref => valid (.prior ref))

def run (checkpoint restored continued document : String) : IO Unit := do
  let bytes ← IO.FS.readBinFile checkpoint
  match PortableMemory.load PortableCheckpoint.sources PortableCheckpoint.contract bytes.data.toList with
  | .error _ => throw (IO.userError "Dossier checkpoint rejected")
  | .ok memory =>
      write restored (PortableMemory.save memory)
      write document (PortableCheckpoint.renderBytes (PortableCheckpoint.sourceParts (outputs memory.valid)))
      let next := ConstitutiveSearch.Agent.Local.Documentary.executeCertified memory ⟨⟨1, 1, 0⟩, .prior .here⟩
      match next.1.2 with
      | none => throw (IO.userError "New certified extraction was refused")
      | some _ =>
          write continued (PortableMemory.save next.1.1)
          say "DOSSIER_RESTORED_AND_NEW_EXTRACTION\n"
""" + ENTRY

TYPED = """import Tests.LocalAlignment.DocumentaryMaterializedPresent
import Tests.LocalAlignment.DocumentaryMemoryCases
""" + COMMON + r"""
def run (_checkpoint _restored _continued _document : String) : IO Unit := do
  let restored := (MaterializedPresent.present MemoryCases.retainedPrefix).restore
  let actual := Memory.run restored MemoryCases.futures
  if actual.1.remaining.length != 0 || actual.1.session.round != 5 then
    throw (IO.userError "Materialized present did not finish")
  match Memory.read actual.1 0 with
  | none => throw (IO.userError "Missing final materialized output")
  | some output =>
      if output.value != 2 || output.origins != [1, 2, 1, 2] then
        throw (IO.userError "Materialized future result changed")
      say "TYPED_MASTER_AND_PRESENT_CONTINUED\n"
""" + ENTRY


def invoke(source, client, paths, names, marker, success=True):
    client.write_text(source + "\n/- AXIOM_AUDIT_BEGIN -/\n" + "".join(
        "#print axioms " + name + "\n" for name in names) + "/- AXIOM_AUDIT_END -/\n",
        encoding="utf-8", newline="\n")
    process = subprocess.Popen(["lake", "env", "lean", "--run", str(client), *map(str, paths)],
                               cwd=ROOT, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    try:
        stdout, stderr = process.communicate(timeout=120)
    except subprocess.TimeoutExpired:
        process.kill()
        process.communicate()
        raise ValueError("Restoration components client timed out") from None
    lines = stdout.decode("utf-8", "strict").splitlines()
    audit = ["'" + name + "' does not depend on any axioms" for name in names]
    if success:
        if process.returncode or stderr or lines != audit + [marker]:
            raise ValueError("Components client failed: " + stdout.decode("utf-8", "replace") + stderr.decode("utf-8", "replace"))
    elif not process.returncode or lines != audit or b"Dossier checkpoint rejected" not in stderr:
        raise ValueError("Invalid dossier did not reach the audited loader")
    return process.pid


def main():
    store = runpy.run_path(str(ROOT / "scripts/run-documentary-portable-store-smoke.py"))
    wire = runpy.run_path(str(ROOT / "scripts/run-documentary-checkpoint-smoke.py"))["wire"]
    # Reuse the frozen eight proposal regimes, but save the actual dossier field.
    start = store["START"].replace("PortableStoreSmoke", "RestorationComponentsSmoke")
    start = start.replace("PortableStore\n", "PortableMemory\n")
    start = start.replace("checkpoint _restored _continued : String", "checkpoint _restored _continued _document : String")
    start = start[:start.index("end RestorationComponentsSmoke")] + ENTRY
    start = start.replace("PortableStore.save actual.1.frame.store", "PortableMemory.save actual.1.frame.dossier.memory")
    start = start.replace("STORE_SAVED", "DOSSIER_SAVED")
    base_names = ["RestorationComponentsSmoke.write", "RestorationComponentsSmoke.say",
                  "RestorationComponentsSmoke.run", "main"]
    pids = []
    with tempfile.TemporaryDirectory(prefix="rp-restoration-components-") as temporary:
        directory = Path(temporary)
        for mode in range(8):
            for forget in (False, True):
                paths = [directory / f"{mode}-{forget}-{name}" for name in ("checkpoint.bin", "restored.bin", "continued.bin", "dossier.md")]
                source = start.replace("__MODE__", str(mode)).replace("__FORGET__", "true" if forget else "false")
                names = base_names[:2] + ["RestorationComponentsSmoke.proposal", "RestorationComponentsSmoke.policy"] + base_names[2:]
                first = invoke(source, directory / "Start.lean", paths, names, "DOSSIER_SAVED")
                if paths[0].read_bytes() != wire(BASE):
                    raise ValueError("Actual adaptive dossier differs from the independent source-position oracle")
                second = invoke(RESUME, directory / "Resume.lean", paths,
                                base_names[:2] + ["RestorationComponentsSmoke.outputs"] + base_names[2:],
                                "DOSSIER_RESTORED_AND_NEW_EXTRACTION")
                if first == second or paths[1].read_bytes() != wire(BASE) or paths[2].read_bytes() != wire({**BASE, "bindings": [1, 1, 2, 1]}):
                    raise ValueError("Dossier byte restart or new extraction differs from the independent oracle")
                if paths[3].read_bytes() != SOURCE_TEXT:
                    raise ValueError("Restored source occurrences or content changed")
                pids.extend((first, second))
        mutations = []
        for key, value in (("version", 2), ("schema", 2), ("round", 1), ("depth", 1), ("task", 1),
                           ("nodes", [[0, 1, 42]]), ("bindings", [99]), ("bindings", [0]), ("bindings", [-1])):
            state = copy.deepcopy(BASE)
            state[key] = value
            mutations.append((key, wire(state)))
        original = wire(BASE)
        mutations.extend((("truncated", original[:-1]), ("trailing", original + bytes([0])), ("alphabet", bytes([7]) + original[1:])))
        for index, (label, corrupted) in enumerate(mutations):
            paths = [directory / f"invalid-{index}-{name}" for name in ("checkpoint.bin", "restored.bin", "continued.bin", "dossier.md")]
            paths[0].write_bytes(corrupted)
            pids.append(invoke(RESUME, directory / "Resume.lean", paths,
                               base_names[:2] + ["RestorationComponentsSmoke.outputs"] + base_names[2:], "", False))
            if any(path.exists() for path in paths[1:]):
                raise ValueError("Rejected dossier wrote an output: " + label)
        paths = [directory / "unused" for _ in range(4)]
        pids.append(invoke(TYPED, directory / "Typed.lean", paths, base_names,
                           "TYPED_MASTER_AND_PRESENT_CONTINUED"))
    print(f"RESTORATION_COMPONENTS_SMOKE_OK: {len(pids)} processes; 16 dossier byte restarts; "
          f"{len(mutations)} invalid files rejected; new certified extractions; "
          "typed full-present future with new master quotation and sum; full-present bytes still open")


if __name__ == "__main__":
    try:
        main()
    except (OSError, ValueError, KeyError, UnicodeError) as error:
        print("RESTORATION_COMPONENTS_SMOKE_ERROR: " + str(error), file=sys.stderr)
        sys.exit(1)
