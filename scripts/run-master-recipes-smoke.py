#!/usr/bin/env python3
"""Audited runtime reads of actual master ports and first-order recipe records.

One process executes existing documentary tasks and reads retained formation
ports. Record bytes have independent literal oracles and invalid-format probes.
No complete master/present serialization or physical master restart is claimed.
"""
from pathlib import Path
import subprocess
import sys
import tempfile

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parent.parent
CLIENT = r"""
import Tests.LocalAlignment.DocumentaryMasterObservation
import Tests.LocalAlignment.DocumentaryProgramCases
set_option genInjectivity false
set_option maxHeartbeats 3000000
namespace RecipeSmoke
open ConstitutiveSearch.Resources
open ConstitutiveSearch.EndogenousDecomposition
open ConstitutiveSearch.Agent.Local.Documentary

def say : IO Unit := do
  let output ← IO.getStdout
  output.write "MASTER_RECIPES_RUNTIME_OK\n".toUTF8

def emit (path : String) (cursor : MasterResources.Cursor) : IO Unit :=
  let words := (ControlCodec.Codec.list (ControlCodec.Codec.list ControlCodec.natural)).words
    (MasterObservation.observedPorts cursor.support.formation)
  IO.FS.writeBinFile path ⟨(ControlCodec.bytes words).toArray⟩

def records : List MasterOperations.Record :=
  [.discover 2, .applyStage 0 1, .decompose 3 0, .assemble 0,
   .nextPrefix 0, .nextSource 1, .nextFresh 2 6, .nextFresh 2 2]

def invalid : List (List UInt8) := __INVALID__

def writeRecords (paths : List String) (records : List MasterOperations.Record) : IO Unit :=
  match paths with
  | [] => match records with
    | [] => pure ()
    | _ :: _ => throw (IO.userError "Missing record path")
  | path :: rest => match records with
    | [] => throw (IO.userError "Extra record path")
    | record :: records => do
        match MasterOperations.loadRecord (MasterOperations.saveRecord record) with
        | none => throw (IO.userError "Recipe record rejected")
        | some loaded =>
            if loaded.fields != record.fields then throw (IO.userError "Recipe record changed")
            IO.FS.writeBinFile path ⟨(MasterOperations.saveRecord record).toArray⟩
            writeRecords rest records

def checkInvalid : List (List UInt8) → IO Unit
  | [] => pure ()
  | bytes :: rest => do
      if !(MasterOperations.loadRecord bytes).isNone then throw (IO.userError "Invalid recipe accepted")
      checkInvalid rest

def run (programPath unsuitablePath blockedPath initialPath : String) (recordPaths : List String)
    (frame : Program.Frame Cases.sources Cases.contract DeductionCases.policy []) : IO Unit := do
  let actual := Program.execute frame ProgramCases.script
  let wrong := Program.execute frame ProgramCases.wrongScript
  let blocked := Program.execute frame ProgramCases.sourceBlockedScript
  emit programPath actual.1.dossier.cursor
  emit unsuitablePath wrong.1.dossier.cursor
  emit blockedPath blocked.1.dossier.cursor
  emit initialPath frame.dossier.cursor
  writeRecords recordPaths records
  checkInvalid invalid
  say
end RecipeSmoke
def main (args : List String) : IO Unit := match args with
  | programPath :: unsuitablePath :: blockedPath :: initialPath :: recordPaths =>
      RecipeSmoke.run programPath unsuitablePath blockedPath initialPath recordPaths
        ConstitutiveSearch.Agent.Local.Documentary.ProgramCases.start
  | [] => throw (IO.userError "Expected paths")
  | [_] => throw (IO.userError "Expected paths")
  | [_, _] => throw (IO.userError "Expected paths")
  | [_, _, _] => throw (IO.userError "Expected paths")
"""


def wire(words):
    def word(value):
        return bytes([0 if value >= 0 else 1] + [1] * (value if value >= 0 else -value - 1) + [2])
    return word(len(words)) + b"".join(word(value) for value in words)


def main():
    fields = [(0, [2]), (1, [0, 1]), (2, [3, 0]), (3, [0]),
              (4, [0]), (5, [1]), (6, [2, 6]), (6, [2, 2])]
    invalid = [wire(words) for words in (
        [7, 1, 0], [-1, 1, 0], [0, 0], [0, 2, 2, 2],
        [1, 1, 0], [1, 3, 0, 1, 2], [0, 1, -1],
        [6, -1, 2, 6], [0, 1, 2, 0],
    )]
    valid = wire([0, 1, 2])
    invalid += [valid[:-1], valid + b"\x00", b"\x07" + valid[1:]]
    names = ["RecipeSmoke.say", "RecipeSmoke.emit", "RecipeSmoke.records", "RecipeSmoke.invalid", "RecipeSmoke.writeRecords",
             "RecipeSmoke.checkInvalid", "RecipeSmoke.run", "main"]
    audit = "\n/- AXIOM_AUDIT_BEGIN -/\n" + "".join("#print axioms " + name + "\n" for name in names) + "/- AXIOM_AUDIT_END -/\n"
    source = CLIENT.replace("__INVALID__", str([list(data) for data in invalid])) + audit
    with tempfile.TemporaryDirectory(prefix="rp-master-recipes-") as temporary:
        directory = Path(temporary)
        client = directory / "RecipeSmoke.lean"
        client.write_text(source, encoding="utf-8", newline="\n")
        paths = [directory / (label + ".bin") for label in ("program", "unsuitable", "blocked", "initial")]
        paths += [directory / f"record-{index}.bin" for index in range(8)]
        result = subprocess.run(["lake", "env", "lean", "--run", str(client), *map(str, paths)], cwd=ROOT,
                                capture_output=True, timeout=60)
        output = result.stdout.decode("utf-8", "strict").splitlines()
        expected_audit = ["'" + name + "' does not depend on any axioms" for name in names]
        if result.returncode or result.stderr or output != expected_audit + ["MASTER_RECIPES_RUNTIME_OK"]:
            raise ValueError("Audited recipe runtime failed: " + (result.stdout + result.stderr).decode("utf-8", "replace"))
        first = [[2], [0, 1], [3, 0], [0], [0], [1], [2, 6]]
        later = [[1], [0, 1], [4, 0], [0], [0], [1], [2, 6]]
        expected_ports = {"program": first + later * 2, "unsuitable": first + later,
                          "blocked": first + later, "initial": []}
        for label, ports in expected_ports.items():
            words = [len(ports)] + [value for group in ports for value in [len(group), *group]]
            if (directory / (label + ".bin")).read_bytes() != wire(words):
                raise ValueError("Actual master input ports differ from literal oracle: " + label)
        for index, (tag, ports) in enumerate(fields):
            if (directory / f"record-{index}.bin").read_bytes() != wire([tag, len(ports), *ports]):
                raise ValueError("Recipe record wire differs from literal oracle")
    print("MASTER_RECIPES_SMOKE_OK: one audited process; three actual documentary traces and initial ports; "
          "eight literal record wires; twelve invalid records rejected; master byte restart still open")


if __name__ == "__main__":
    try:
        main()
    except (AssertionError, OSError, ValueError, subprocess.TimeoutExpired) as error:
        print("MASTER_RECIPES_SMOKE_ERROR: " + str(error), file=sys.stderr)
        sys.exit(1)
