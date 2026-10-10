#!/usr/bin/env python3
"""Physical reader-component restart from actual retained master values.

One start client executes the three existing documentary scripts. Cold clients
receive only assignment-program bytes, read new queries and preserve measured
work. Independent literal programs and arithmetic oracles check exact files.
These clients do not restore the master cursor, its proofs or the full present.
"""
from pathlib import Path
import hashlib
import json
import subprocess
import sys
import tempfile

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parent.parent
QUERIES = [0, 1, 2, 9, 10, 11, 12, 13, 14, 15]
COMMON = r"""
set_option genInjectivity false
set_option maxHeartbeats 4000000
namespace __NS__
open ConstitutiveSearch.Resources
open ConstitutiveSearch.EndogenousDecomposition
open ConstitutiveSearch.Agent.Local.Documentary
open PortableAssignment
def queries : List Nat := [0, 1, 2, 9, 10, 11, 12, 13, 14, 15]
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
  output.write "ASSIGNMENT_RUNTIME_OK\n".toUTF8
"""
START = r"""
import Tests.LocalAlignment.DocumentaryAssignmentCapture
import Tests.LocalAlignment.DocumentaryProgramCases
__COMMON__
def save (codePath resultPath : String) (cursor : MasterResources.Cursor) : IO Unit := do
  IO.FS.writeBinFile codePath ⟨(AssignmentCodec.save (AssignmentCapture.cursor cursor)).toArray⟩
  writeResult resultPath (sequential cursor.assignment)
def run (firstCode firstResult secondCode secondResult thirdCode thirdResult : String)
    (frame : Program.Frame Cases.sources Cases.contract DeductionCases.policy []) : IO Unit := do
  let actual := Program.execute frame ProgramCases.script
  let wrong := Program.execute frame ProgramCases.wrongScript
  let blocked := Program.execute frame ProgramCases.sourceBlockedScript
  save firstCode firstResult actual.1.dossier.cursor
  save secondCode secondResult wrong.1.dossier.cursor
  save thirdCode thirdResult blocked.1.dossier.cursor
  say
end AssignmentStart
def main (args : List String) : IO Unit := match args with
  | firstCode :: firstResult :: secondCode :: secondResult :: thirdCode :: thirdResult :: rest =>
      match rest with
      | [] => AssignmentStart.run firstCode firstResult secondCode secondResult thirdCode thirdResult
          ConstitutiveSearch.Agent.Local.Documentary.ProgramCases.start
      | _ :: _ => throw (IO.userError "Expected six paths")
  | [] => throw (IO.userError "Expected six paths")
  | [_] => throw (IO.userError "Expected six paths")
  | [_, _] => throw (IO.userError "Expected six paths")
  | [_, _, _] => throw (IO.userError "Expected six paths")
  | [_, _, _, _] => throw (IO.userError "Expected six paths")
  | [_, _, _, _, _] => throw (IO.userError "Expected six paths")
"""
RESUME = r"""
import Tests.LocalAlignment.DocumentaryAssignmentCodec
__COMMON__
def resume (inputPath outputPath : String) : IO Unit := do
  let bytes ← IO.FS.readBinFile inputPath
  match AssignmentCodec.restore bytes.data.toList with
  | none => throw (IO.userError "Invalid assignment program")
  | some data => writeResult outputPath data
  say
end AssignmentRestart
def main (args : List String) : IO Unit := match args with
  | inputPath :: outputPath :: rest => match rest with
    | [] => AssignmentRestart.resume inputPath outputPath
    | _ :: _ => throw (IO.userError "Expected two paths")
  | [] => throw (IO.userError "Expected two paths")
  | [_] => throw (IO.userError "Expected two paths")
"""
INVALID = r"""
import Tests.LocalAlignment.DocumentaryAssignmentCodec
set_option genInjectivity false
namespace AssignmentInvalid
open ConstitutiveSearch.Agent.Local.Documentary
def checkFiles : List String → IO Unit
  | [] => pure ()
  | path :: rest => do
      let bytes ← IO.FS.readBinFile path
      if !(AssignmentCodec.load bytes.data.toList).isNone then
        throw (IO.userError "Invalid assignment program accepted")
      checkFiles rest
def say : IO Unit := do
  let output ← IO.getStdout
  output.write "ASSIGNMENT_RUNTIME_OK\n".toUTF8
end AssignmentInvalid
def main (args : List String) : IO Unit := do
  AssignmentInvalid.checkFiles args
  AssignmentInvalid.say
"""


def wire(words):
    def word(value):
        return bytes([0 if value >= 0 else 1] + [1] * (value if value >= 0 else -value - 1) + [2])
    return word(len(words)) + b"".join(word(value) for value in words)


def code_words(program):
    words = [88, 1, len(program)]
    for command in program:
        words.extend([0, 0] if command is None else [1, 1, command])
    return words


def query_oracle(program):
    bits, nodes, labels = [], 1, 0
    for query in QUERIES:
        bit = query < 2 or query % 2 == 1
        work_nodes, work_labels = max(1, query), 0
        for command in reversed(program):
            work_nodes += 1
            if command is not None:
                work_labels += min(query, command) + 1
                if query == command:
                    bit = not bit
        bits.append(int(bit))
        nodes += work_nodes + 1
        labels += work_labels
    return wire([len(bits), *bits, nodes, labels])


def client(directory, label, template, namespace, names):
    if "__COMMON__" in template:
        template = template.replace("__COMMON__", COMMON.replace("__NS__", namespace))
    audit = "\n/- AXIOM_AUDIT_BEGIN -/\n" + "".join("#print axioms " + name + "\n" for name in names) + "/- AXIOM_AUDIT_END -/\n"
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
    expected = ["'" + name + "' does not depend on any axioms" for name in names] + ["ASSIGNMENT_RUNTIME_OK"]
    if process.returncode or stderr or lines != expected:
        raise ValueError("Audited assignment client failed: " + (stdout + stderr).decode("utf-8", "replace"))
    return {"client": path.name, "process_id": process.pid, "runtime_audits": len(names),
            "client_sha256": hashlib.sha256(path.read_bytes()).hexdigest(), "returncode": process.returncode}


def main():
    with tempfile.TemporaryDirectory(prefix="rp-assignment-restart-") as temporary:
        directory = Path(temporary)
        names_start = ["AssignmentStart." + name for name in ("queries", "resultBytes", "writeResult", "say", "save", "run")] + ["main"]
        names_resume = ["AssignmentRestart." + name for name in ("queries", "resultBytes", "writeResult", "say", "resume")] + ["main"]
        names_invalid = ["AssignmentInvalid.checkFiles", "AssignmentInvalid.say", "main"]
        start = client(directory, "AssignmentStart", START, "AssignmentStart", names_start)
        resume = client(directory, "AssignmentRestart", RESUME, "AssignmentRestart", names_resume)
        invalid_client = client(directory, "AssignmentInvalid", INVALID, "", names_invalid)
        actual = {"complete": [14, 12, 10], "unsuitable": [12, 10], "blocked": [12, 10]}
        paths = []
        for label in actual:
            paths += [directory / (label + ".bin"), directory / (label + "-actual.bin")]
        receipts = [run(start, paths, names_start)]
        for label, program in actual.items():
            saved = directory / (label + ".bin")
            expected = query_oracle(program)
            if saved.read_bytes() != wire(code_words(program)):
                raise ValueError("Actual retained recipe differs from literal code oracle: " + label)
            if (directory / (label + "-actual.bin")).read_bytes() != expected:
                raise ValueError("Actual assignment/reader differs from independent query/work oracle: " + label)
            output = directory / (label + "-resumed.bin")
            receipts.append(run(resume, [saved, output], names_resume))
            if output.read_bytes() != expected:
                raise ValueError("Cold reader restart changed bits or measured work: " + label)
        synthetic = {"seed": [], "visit": [None], "double-flip": [2, 2], "composition": [None, 10, None]}
        for label, program in synthetic.items():
            saved, output = directory / (label + ".bin"), directory / (label + "-resumed.bin")
            saved.write_bytes(wire(code_words(program)))
            receipts.append(run(resume, [saved, output], names_resume))
            if output.read_bytes() != query_oracle(program):
                raise ValueError("Cold reader shape/visit oracle differs: " + label)
        malformed_words = [
            [89, 1, 0], [88, 2, 0], [-1, 1, 0], [88, -1, 0], [88, 1, -1],
            [88, 1, 1, 2, 0], [88, 1, 1, 0, 1, 10], [88, 1, 1, 1, 0],
            [88, 1, 1, 1, 1, -1], [88, 1, 2, 1, 1, 10],
            [88, 1, 0, 0], [88, 1, 1, 0, 0, 0],
        ]
        valid = wire(code_words([10]))
        malformed = [wire(words) for words in malformed_words] + [valid[:-1], valid + b"\x00", b"\x07" + valid[1:]]
        invalid_paths = []
        for index, content in enumerate(malformed):
            path = directory / f"invalid-{index}.bin"
            path.write_bytes(content)
            invalid_paths.append(path)
        receipts.append(run(invalid_client, invalid_paths, names_invalid))
        # Identity and double flips preserve bits but retain their reader work.
        if query_oracle([]) == query_oracle([None]) or query_oracle([]) == query_oracle([2, 2]):
            raise ValueError("Reader work separators were collapsed")
    print("ASSIGNMENT_RESTART_SMOKE_OK " + json.dumps({
        "physical_processes": len(receipts), "actual_master_reader_restarts": len(actual),
        "synthetic_reader_restarts": len(synthetic), "invalid_programs_rejected": len(malformed),
        "queries_per_reader": len(QUERIES), "start_runtime_audits": len(names_start),
        "resume_runtime_audits": len(names_resume), "invalid_runtime_audits": len(names_invalid),
        "same_actual_bits_and_measured_work": True, "master_cursor_reloaded": False,
        "full_present_reloaded": False, "qwen_calls": 0, "receipts": receipts,
    }, separators=(",", ":")))


if __name__ == "__main__":
    try:
        main()
    except (AssertionError, OSError, ValueError, subprocess.TimeoutExpired) as error:
        print("ASSIGNMENT_RESTART_SMOKE_ERROR: " + str(error), file=sys.stderr)
        sys.exit(1)
