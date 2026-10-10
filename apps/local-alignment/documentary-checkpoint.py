#!/usr/bin/env python3
"""Physical realization of the restricted final-deduction checkpoint.

Two separate Lean clients: the resume client imports neither the start module
nor closed execution cases. Files are read back and receipts hash actual bytes.
No model inference, full master-cursor persistence or generic adaptive restart.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import tempfile

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
COMMON = r"""
set_option genInjectivity false
set_option maxRecDepth 8192
set_option maxHeartbeats 30000000
namespace DocumentaryCheckpointClient
open ConstitutiveSearch.Resources
open ConstitutiveSearch.Agent.Local.Documentary
open Program Portable PortableCheckpoint

def writeBytes (path : String) (bytes : List Nat) : IO Unit :=
  IO.FS.writeBinFile path ⟨(toBytes bytes).toArray⟩

def writeDocument (path : String) (store : Deduction.Store sources contract policy)
    (output : Bound store (.conclusion demand)) : IO Unit :=
  IO.FS.writeBinFile path (render store output)

def say (message : String) : IO Unit := do
  let output ← IO.getStdout
  output.write message.toUTF8
"""
ENTRY = r"""
end DocumentaryCheckpointClient

def main (args : List String) : IO Unit := match args with
  | [checkpoint, document, result] => DocumentaryCheckpointClient.run checkpoint document result
  | [] => throw (IO.userError "Expected three path arguments")
  | [_] => throw (IO.userError "Expected three path arguments")
  | [_, _] => throw (IO.userError "Expected three path arguments")
  | _ :: _ :: _ :: _ :: _ => throw (IO.userError "Expected three path arguments")
"""
START = "import Tests.LocalAlignment.DocumentaryPortableStart\n" + COMMON + r"""
def run (checkpoint _document _result : String) : IO Unit := do
  let executed := PortableStart.executePrefix
    (PortableStart.initial ConstitutiveSearch.EndogenousDecomposition.VariableMaster.Example.origin)
  match save executed.1 4 with
  | none => throw (IO.userError "Checkpoint binding missing")
  | some saved =>
      writeBytes checkpoint (encode saved)
      say "START_SAVED\n"
""" + ENTRY
CONTINUOUS = "import Tests.LocalAlignment.DocumentaryPortableStart\n" + COMMON + r"""
def run (checkpoint document result : String) : IO Unit := do
  let executed := PortableStart.executePrefix
    (PortableStart.initial ConstitutiveSearch.EndogenousDecomposition.VariableMaster.Example.origin)
  match save executed.1 4 with
  | none => throw (IO.userError "Checkpoint binding missing")
  | some saved =>
      writeBytes checkpoint (encode saved)
      let continued := Program.execute executed.1 PortableStart.remaining
      match loadBound continued.1.store (.conclusion demand) 0 with
      | none => throw (IO.userError "Actual conclusion criterion failed")
      | some output =>
          match captureBindings (.conclusion demand :: slots) continued.1.bindings with
          | none => throw (IO.userError "Actual final binding missing")
          | some bindings =>
              writeDocument document continued.1.store output
              writeBytes result (encode ⟨1, 1, 5, continued.1.dossier.cursor.depth,
                record continued.1.store, bindings, 0⟩)
              say "UNINTERRUPTED_PUBLISHED\n"
""" + ENTRY
RESUME = "import Tests.LocalAlignment.DocumentaryPortableCheckpoint\n" + COMMON + r"""
def run (checkpoint document result : String) : IO Unit := do
  let actualBytes ← IO.FS.readBinFile checkpoint
  match decode (fromBytes actualBytes.data.toList) with
  | none => throw (IO.userError "Checkpoint bytes rejected")
  | some saved => match load saved with
    | .error _ => throw (IO.userError "Checkpoint contract rejected")
    | .ok loaded =>
        let finished := resume loaded
        writeDocument document finished.store finished.output
        writeBytes result (encode ⟨1, 1, loaded.round + 1, loaded.depth,
          record finished.store, 0 :: loaded.table.positions.map (fun position => position + 1), 0⟩)
        say "RESUME_PUBLISHED\n"
end DocumentaryCheckpointClient

def main (args : List String) : IO Unit := match args with
  | [checkpoint, document, result] => DocumentaryCheckpointClient.run checkpoint document result
  | [] => throw (IO.userError "Expected three path arguments")
  | [_] => throw (IO.userError "Expected three path arguments")
  | [_, _] => throw (IO.userError "Expected three path arguments")
  | _ :: _ :: _ :: _ :: _ => throw (IO.userError "Expected three path arguments")
"""


def client_source(mode: str) -> str:
    source = {"start": START, "resume": RESUME, "continuous": CONTINUOUS}[mode]
    return source + "\n/- AXIOM_AUDIT_BEGIN -/\n" + "".join(
        "#print axioms " + name + "\n" for name in (
            "DocumentaryCheckpointClient.writeBytes", "DocumentaryCheckpointClient.writeDocument",
            "DocumentaryCheckpointClient.say", "DocumentaryCheckpointClient.run", "main")) + "/- AXIOM_AUDIT_END -/\n"


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def invoke(mode: str, workspace: Path, *, expect_success: bool = True) -> dict:
    workspace = workspace.resolve()
    workspace.mkdir(parents=True, exist_ok=True)
    checkpoint = workspace / "checkpoint.bin"
    document = workspace / "dossier.md"
    result = workspace / "result.bin"
    arguments = [str(checkpoint), str(document), str(result)]
    if mode == "resume" and checkpoint.exists() and checkpoint.stat().st_size > 1048576:
        raise ValueError("Checkpoint exceeds the adapter's received file limit")
    with tempfile.TemporaryDirectory(prefix="rp-documentary-checkpoint-client-") as temporary:
        client = Path(temporary) / "Client.lean"
        source = client_source(mode)
        client.write_text(source, encoding="utf-8", newline="\n")
        process = subprocess.Popen(["lake", "env", "lean", "--run", str(client), *arguments],
                                   cwd=ROOT, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        try:
            stdout, stderr = process.communicate(timeout=120)
        except subprocess.TimeoutExpired:
            process.kill()
            process.communicate()
            raise RuntimeError("Checkpoint client timed out") from None
    output = stdout.decode("utf-8", errors="strict")
    diagnostics = stderr.decode("utf-8", errors="replace")
    receipt = {"mode": mode, "process_id": process.pid, "returncode": process.returncode,
               "client_sha256": hashlib.sha256(source.encode()).hexdigest(),
               "client_import": source.splitlines()[0], "runtime_audits": 5,
               "compiler_runtime_system_boundary": "Lean IO, runtime, filesystem and operating system",
               "mathematical_scope": "fixed quotation/binary-rule formation; one final sum; no master cursor reload"}
    if expect_success:
        if process.returncode or diagnostics or "depends on axioms:" in output or "warning:" in output:
            raise RuntimeError("Checkpoint client failed:\n" + output + diagnostics)
        marker = {"start": "START_SAVED", "resume": "RESUME_PUBLISHED", "continuous": "UNINTERRUPTED_PUBLISHED"}[mode]
        if not output.endswith(marker + "\n") or output.count("does not depend on any axioms") != 5:
            raise RuntimeError("Checkpoint client audit/marker changed:\n" + output)
        for name, path in (("checkpoint", checkpoint), ("document", document), ("result", result)):
            if mode == "start" and name != "checkpoint":
                continue
            receipt[name] = {"bytes": path.stat().st_size, "sha256": sha(path), "read_back": True}
        (workspace / (mode + "-receipt.json")).write_text(json.dumps(receipt, indent=2) + "\n", encoding="utf-8")
    elif process.returncode == 0:
        raise RuntimeError("Altered checkpoint was accepted")
    elif output.count("does not depend on any axioms") != 5 or "depends on axioms:" in output or "error:" in output:
        raise RuntimeError("Rejection test did not reach the audited client:\n" + output + diagnostics)
    if not expect_success:
        receipt["rejected"] = True
        receipt["diagnostic_sha256"] = hashlib.sha256(stderr).hexdigest()
    return receipt


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("mode", choices=("start", "resume", "continuous"))
    parser.add_argument("workspace", type=Path)
    args = parser.parse_args()
    receipt = invoke(args.mode, args.workspace)
    print(json.dumps(receipt, indent=2))


if __name__ == "__main__":
    try:
        main()
    except (OSError, ValueError, RuntimeError) as error:
        print("DOCUMENTARY_CHECKPOINT_ERROR: " + str(error), file=sys.stderr)
        sys.exit(1)
