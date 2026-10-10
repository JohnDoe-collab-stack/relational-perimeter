#!/usr/bin/env python3
"""Cold dependent-assignment restart, followed by a NEW operational stage.
One start consumes the existing public master and its three actual scripts.
The cold client imports the component loader, receives bytes only, and executes
a fresh stage from the restored SequentialAssignment. Other master fields are
not loaded. Binary words and bit/work outcomes have independent literal oracles.
"""
from pathlib import Path
import hashlib
import json
import runpy
import subprocess
import sys
import tempfile

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parent.parent
QUERIES = [0, 1, 2, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]
COMMON = r"""
set_option genInjectivity false
set_option maxHeartbeats 5000000
namespace __NS__
open ConstitutiveSearch.Resources
open ConstitutiveSearch.EndogenousDecomposition
open ConstitutiveSearch.Agent.Local.Documentary
open PortableAssignment

def queries : List Nat := [0, 1, 2, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]

def resultBytes (data : Bundle) : List UInt8 :=
  let output := readQueries data queries
  let bits := output.1.map (fun value => match value with | false => 0 | true => 1)
  let words := (ControlCodec.natural.list.product (ControlCodec.natural.product ControlCodec.natural)).words
    (bits, output.2.nodes, output.2.labelSteps)
  ControlCodec.bytes words

def writeResult (path : String) (data : Bundle) : IO Unit :=
  IO.FS.writeBinFile path ⟨(resultBytes data).toArray⟩

def say : IO Unit := do
  let output ← IO.getStdout
  output.write "SEQUENTIAL_RUNTIME_OK\n".toUTF8
"""
START = r"""
import Tests.LocalAlignment.DocumentarySequentialCapture
import Tests.LocalAlignment.DocumentarySequentialCases
__COMMON__

def save (codePath beforePath afterPath : String) (cursor : MasterResources.Cursor)
    (ready : SequentialCapture.Ready cursor) : IO Unit := do
  let bytes := SequentialPortable.save cursor.depth (AssignmentCapture.cursor cursor)
  IO.FS.writeBinFile codePath ⟨bytes.toArray⟩
  writeResult beforePath (sequential cursor.assignment)
  match SequentialCapture.restoreState cursor ready bytes rfl with
  | none => throw (IO.userError "Valid state coupling failed")
  | some loaded =>
      let next := executeSequentialStage cursor.depth loaded.2.threadedAssignment
      writeResult afterPath (sequential next.next)

def run (a b c d e f g h i : String)
    (frame : Program.Frame Cases.sources Cases.contract DeductionCases.policy [])
    (initial : SequentialCapture.Ready frame.dossier.cursor) : IO Unit := do
  let actual := Program.execute frame ProgramCases.script
  let wrong := Program.execute frame ProgramCases.wrongScript
  let blocked := Program.execute frame ProgramCases.sourceBlockedScript
  save a b c actual.1.dossier.cursor (SequentialCapture.program_ready actual.2 initial)
  save d e f wrong.1.dossier.cursor (SequentialCapture.program_ready wrong.2 initial)
  save g h i blocked.1.dossier.cursor (SequentialCapture.program_ready blocked.2 initial)
  say
end SequentialStart

def main (args : List String) : IO Unit := match args with
  | a :: b :: c :: d :: e :: f :: g :: h :: i :: rest => match rest with
    | [] => SequentialStart.run a b c d e f g h i
        ConstitutiveSearch.Agent.Local.Documentary.ProgramCases.start
        ConstitutiveSearch.Agent.Local.Documentary.SequentialCases.initial
    | _ :: _ => throw (IO.userError "Expected nine paths")
  | [] => throw (IO.userError "Expected nine paths")
  | [_] => throw (IO.userError "Expected nine paths")
  | [_, _] => throw (IO.userError "Expected nine paths")
  | [_, _, _] => throw (IO.userError "Expected nine paths")
  | [_, _, _, _] => throw (IO.userError "Expected nine paths")
  | [_, _, _, _, _] => throw (IO.userError "Expected nine paths")
  | [_, _, _, _, _, _] => throw (IO.userError "Expected nine paths")
  | [_, _, _, _, _, _, _] => throw (IO.userError "Expected nine paths")
  | [_, _, _, _, _, _, _, _] => throw (IO.userError "Expected nine paths")
"""
RESUME = r"""
import Tests.LocalAlignment.DocumentarySequentialPortable
__COMMON__

def resume (inputPath beforePath afterPath : String) : IO Unit := do
  let bytes ← IO.FS.readBinFile inputPath
  match SequentialPortable.restore bytes.data.toList with
  | none => throw (IO.userError "Invalid dependent assignment")
  | some data =>
      writeResult beforePath (sequential data.2)
      let next := executeSequentialStage data.1 data.2
      writeResult afterPath (sequential next.next)
  say
end SequentialRestart

def main (args : List String) : IO Unit := match args with
  | inputPath :: beforePath :: afterPath :: rest => match rest with
    | [] => SequentialRestart.resume inputPath beforePath afterPath
    | _ :: _ => throw (IO.userError "Expected three paths")
  | [] => throw (IO.userError "Expected three paths")
  | [_] => throw (IO.userError "Expected three paths")
  | [_, _] => throw (IO.userError "Expected three paths")
"""
INVALID = r"""
import Tests.LocalAlignment.DocumentarySequentialPortable
set_option genInjectivity false
namespace SequentialInvalid
open ConstitutiveSearch.Agent.Local.Documentary

def checkFiles : List String → IO Unit
  | [] => pure ()
  | path :: rest => do
      let bytes ← IO.FS.readBinFile path
      if !(SequentialPortable.restore bytes.data.toList).isNone then
        throw (IO.userError "Invalid dependent assignment accepted")
      checkFiles rest

def say : IO Unit := do
  let output ← IO.getStdout
  output.write "SEQUENTIAL_RUNTIME_OK\n".toUTF8
end SequentialInvalid

def main (args : List String) : IO Unit := do
  SequentialInvalid.checkFiles args
  SequentialInvalid.say
"""


def code_words(depth, program):
    words = [89, 1, depth, len(program)]
    for command in program:
        words.extend([0, 0] if command is None else [1, 1, command])
    return words


def oracle(program, wire):
    bits, nodes, labels = [], 1, 0
    for query in QUERIES:
        bit = query < 2 or query % 2 == 1
        query_nodes, query_labels = max(1, query), 0
        for command in reversed(program):
            query_nodes += 1
            if command is not None:
                query_labels += min(query, command) + 1
                if query == command:
                    bit = not bit
        bits.append(int(bit))
        nodes += query_nodes + 1
        labels += query_labels
    return wire([len(bits), *bits, nodes, labels])


def client(directory, label, template, names):
    template = template.replace("__COMMON__", COMMON.replace("__NS__", label))
    audit = "\n/- AXIOM_AUDIT_BEGIN -/\n" + "".join("#print axioms " + n + "\n" for n in names) + "/- AXIOM_AUDIT_END -/\n"
    path = directory / (label + ".lean")
    path.write_text(template + audit, encoding="utf-8", newline="\n")
    return path


def run(path, args, names):
    process = subprocess.Popen(["lake", "env", "lean", "--run", str(path), *map(str, args)],
                               cwd=ROOT, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    try:
        stdout, stderr = process.communicate(timeout=60)
    except subprocess.TimeoutExpired:
        process.kill()
        process.communicate()
        raise
    lines = stdout.decode("utf-8", "strict").splitlines()
    expected = ["'" + name + "' does not depend on any axioms" for name in names] + ["SEQUENTIAL_RUNTIME_OK"]
    if process.returncode or stderr or lines != expected:
        raise ValueError("Audited dependent-assignment client failed: " + (stdout + stderr).decode("utf-8", "replace"))
    return {"client": path.name, "process_id": process.pid, "runtime_audits": len(names),
            "client_sha256": hashlib.sha256(path.read_bytes()).hexdigest(), "returncode": process.returncode}


def main():
    previous = runpy.run_path(str(ROOT / "scripts/run-assignment-restart-smoke.py"))
    wire = previous["wire"]
    with tempfile.TemporaryDirectory(prefix="rp-sequential-restart-") as temporary:
        directory = Path(temporary)
        start_names = ["SequentialStart." + n for n in ("queries", "resultBytes", "writeResult", "say", "save", "run")] + ["main"]
        resume_names = ["SequentialRestart." + n for n in ("queries", "resultBytes", "writeResult", "say", "resume")] + ["main"]
        invalid_names = ["SequentialInvalid.checkFiles", "SequentialInvalid.say", "main"]
        start = client(directory, "SequentialStart", START, start_names)
        resume = client(directory, "SequentialRestart", RESUME, resume_names)
        invalid = client(directory, "SequentialInvalid", INVALID, invalid_names)
        actual = {"complete": (3, [14, 12, 10]), "unsuitable": (2, [12, 10]), "blocked": (2, [12, 10])}
        paths = []
        for label in actual:
            paths += [directory / (label + ".bin"), directory / (label + "-before.bin"), directory / (label + "-after.bin")]
        receipts = [run(start, paths, start_names)]
        comparisons = []
        for label, (depth, program) in actual.items():
            saved = directory / (label + ".bin")
            if saved.read_bytes() != wire(code_words(depth, program)):
                raise ValueError("Actual depth/code differs from literal retained-code oracle: " + label)
            before, after = oracle(program, wire), oracle([2 * depth + 10, *program], wire)
            if (directory / (label + "-before.bin")).read_bytes() != before:
                raise ValueError("Actual reader differs from independent oracle: " + label)
            if (directory / (label + "-after.bin")).read_bytes() != after:
                raise ValueError("Actual new stage differs from independent oracle: " + label)
            resumed_before, resumed_after = directory / (label + "-resumed-before.bin"), directory / (label + "-resumed-after.bin")
            receipts.append(run(resume, [saved, resumed_before, resumed_after], resume_names))
            if resumed_before.read_bytes() != before or resumed_after.read_bytes() != after:
                raise ValueError("Cold restart or NEW stage differs: " + label)
            comparisons.append({"case": label, "depth": depth, "code": program, "next_selected": 2 * depth + 10,
                                "before_sha256": hashlib.sha256(before).hexdigest(),
                                "after_sha256": hashlib.sha256(after).hexdigest()})
        synthetic = {"seed": (0, []), "visits": (0, [None, None]),
                     "double-flip": (0, [2, 2]), "composition": (1, [None, 10, None])}
        for label, (depth, program) in synthetic.items():
            saved = directory / (label + ".bin")
            saved.write_bytes(wire(code_words(depth, program)))
            resumed_before, resumed_after = directory / (label + "-resumed-before.bin"), directory / (label + "-resumed-after.bin")
            receipts.append(run(resume, [saved, resumed_before, resumed_after], resume_names))
            if resumed_before.read_bytes() != oracle(program, wire) or resumed_after.read_bytes() != oracle([2 * depth + 10, *program], wire):
                raise ValueError("Synthetic reader or NEW stage oracle differs: " + label)
        malformed_words = [
            [90, 1, 0, 0], [89, 2, 0, 0], [-1, 1, 0, 0], [89, -1, 0, 0], [89, 1, -1, 0], [89, 1, 0, -1],
            [89, 1, 0, 1, 2, 0], [89, 1, 0, 1, 0, 1, 2], [89, 1, 0, 1, 1, 0],
            [89, 1, 0, 1, 1, 1, -1], [89, 1, 0, 2, 1, 1, 2], [89, 1, 0, 0, 0],
            code_words(0, [0]), code_words(0, [0, 0]), code_words(0, [10]),
            code_words(0, [11]), code_words(1, [12]), code_words(1, [13]),
        ]
        valid = wire(code_words(1, [10]))
        malformed = [wire(words) for words in malformed_words] + [valid[:-1], valid + b"\x00", b"\x07" + valid[1:]]
        invalid_paths = []
        for index, content in enumerate(malformed):
            path = directory / f"invalid-{index}.bin"
            path.write_bytes(content)
            invalid_paths.append(path)
        receipts.append(run(invalid, invalid_paths, invalid_names))
        print("SEQUENTIAL_RESTART_RECEIPTS " + json.dumps({
            "kind": "development_smoke", "processes": receipts,
            "actual_comparisons": comparisons, "new_cold_stages_executed": 7,
            "retained_state_couplings_executed": 3, "new_coupled_stages_executed": 3,
            "actual_reader_restarts": 3, "synthetic_restarts": 4, "invalid_inputs_rejected": len(malformed),
            "queries": QUERIES, "component": "complete_dependent_SequentialAssignment",
            "retained_master_environment_reloaded": False, "full_present_reloaded": False,
            "qwen_calls": 0}, sort_keys=True))
        print(f"SEQUENTIAL_RESTART_SMOKE_OK: three actual and four synthetic cold restarts; seven NEW stages; {len(malformed)} invalid inputs; component scope")


if __name__ == "__main__":
    try:
        main()
    except (OSError, ValueError, KeyError, subprocess.TimeoutExpired) as error:
        print("SEQUENTIAL_RESTART_SMOKE_ERROR: " + str(error), file=sys.stderr)
        sys.exit(1)
