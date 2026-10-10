#!/usr/bin/env python3
"""Cold complete-threaded-state/history/generation/constitution restarts.

The assembled present test reads its byte sections in the same process with
the captured typed master payload retained. It is explicitly not a cold
full-master or full-present restart. All fixtures consume the existing public
master. Independent Python oracles freeze fields, bits, reader work and wires.
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
set_option maxHeartbeats 8000000
namespace __NS__
open ConstitutiveSearch.Resources
open ConstitutiveSearch.EndogenousDecomposition
open ConstitutiveSearch.Agent.Local.Documentary
open PortableAssignment
open StrongPerimetralTurning
open StrongPerimetralTurning.Example

def write (path : String) (value : List UInt8) : IO Unit :=
  IO.FS.writeBinFile path ⟨value.toArray⟩

def pathAt : Nat → List String → String
  | 0, value :: _ => value
  | index + 1, _ :: rest => pathAt index rest
  | _, [] => "missing-path"

def stateWords {depth assignment} (state : ThreadedConstitutiveState depth assignment) : ControlCodec.Words :=
  let read := readQueries (sequential state.threadedAssignment) [0, 1, 2, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]
  let bits := read.1.map (fun value => match value with | false => 0 | true => 1)
  [Int.ofNat depth] ++ FoundationPortable.treeWords (FoundationPortable.capture state.generation.target) ++
    [Int.ofNat state.generation.generateCalls, Int.ofNat state.generation.generatedSteps,
      Int.ofNat state.generation.provenanceUnits, Int.ofNat state.generation.certificatesProduced,
      Int.ofNat state.searchSeed] ++ StatePortable.decision.list.words state.decisions ++
    ControlCodec.natural.list.words state.provenance ++ ControlCodec.natural.list.words bits ++
    [Int.ofNat read.2.nodes, Int.ofNat read.2.labelSteps]

def stateResult {depth assignment} (state : ThreadedConstitutiveState depth assignment) : List UInt8 :=
  ControlCodec.bytes (stateWords state)

def say : IO Unit := do
  let output ← IO.getStdout
  output.write "STATE_ASSEMBLY_RUNTIME_OK\n".toUTF8
"""
START = r"""
import Tests.LocalAlignment.DocumentaryAssembledCases
import Tests.LocalAlignment.DocumentaryCanonicalAdaptiveRestoration
__COMMON__

def saveCursor (files : List String) (base : Nat) (cursor : MasterResources.Cursor)
    (ready : SequentialCapture.Ready cursor) : IO Unit := do
  write (pathAt base files) (StateCapture.save cursor ready)
  write (pathAt (base + 1) files) (GenerationPortable.save cursor.state.generation)
  write (pathAt (base + 2) files) (FoundationPortable.save cursor.state.generation.target)
  match StateCapture.history cursor with
  | none => throw (IO.userError "Executed prefix lost retained history")
  | some history => write (pathAt (base + 3) files) (HistoryPortable.save history)
  write (pathAt (base + 4) files) (stateResult cursor.state)
  let discovery := runThreadedNextDiscovery cursor.state
  let next := buildFromExecutedDiscovery cursor.state cursor.freshness discovery rfl
  write (pathAt (base + 5) files) (stateResult next.run.nextRun.next)

def hybrid (files : List String) (before : Snapshot.PresentData Cases.sources Cases.contract DeductionCases.policy Nat
    [ProgramCases.sumSpec, ProgramCases.baselineSpec, ProgramCases.deltaSpec, ProgramCases.revisedSpec, ProgramCases.baselineSpec])
    (ready : SequentialCapture.Ready before.session.frame.dossier.cursor) : IO Unit := do
  let packet := AssembledCheckpoint.capture ControlCodec.natural before ready
  let path := pathAt 18 files
  write path packet.wire
  let saved ← IO.FS.readBinFile path
  if same : saved.data.toList = packet.wire then
    let filePacket : AssembledCheckpoint.Packet :=
      { packet with
        wire := saved.data.toList
        sourceExact := by intro parts found; rw [same] at found; exact packet.sourceExact parts found }
    match AssembledCheckpoint.restore Cases.sources Cases.contract DeductionCases.policy
      ControlCodec.natural
      [ProgramCases.sumSpec, ProgramCases.baselineSpec, ProgramCases.deltaSpec, ProgramCases.revisedSpec, ProgramCases.baselineSpec]
      filePacket with
    | none => throw (IO.userError "Assembled checkpoint rejected")
    | some loaded =>
        let requests : List (Memory.Request Nat) :=
          [.reset (AdaptiveCases.policy 4), .progress (AdaptiveCases.policy 4) (AdaptiveCases.feed true 3),
            .progress (AdaptiveCases.policy 4) (AdaptiveCases.feed true 4)]
        let original := Memory.run before requests
        let resumed := Memory.run loaded requests
        write (pathAt 19 files)
          (PortableControl.save ControlCodec.natural (PortableControl.capture original.1))
        write (pathAt 20 files)
          (PortableControl.save ControlCodec.natural (PortableControl.capture resumed.1))
        write (pathAt 21 files) (PortableStore.save original.1.session.frame.store)
        write (pathAt 22 files) (PortableStore.save resumed.1.session.frame.store)
        write (pathAt 23 files) (stateResult original.1.session.frame.dossier.cursor.state)
        write (pathAt 24 files) (stateResult resumed.1.session.frame.dossier.cursor.state)
        if original.1.session.round != 5 || resumed.1.session.round != 5 ||
            original.1.remaining.length != 0 || resumed.1.remaining.length != 0 then
          throw (IO.userError "Restored control failed to complete remaining task")
  else throw (IO.userError "File sections differ from captured sections")

def run (files : List String) (frame : Program.Frame Cases.sources Cases.contract DeductionCases.policy [])
    (initial : SequentialCapture.Ready frame.dossier.cursor)
    (boot : Snapshot.PresentData Cases.sources Cases.contract DeductionCases.policy Nat
      [ProgramCases.sumSpec, ProgramCases.baselineSpec, ProgramCases.deltaSpec, ProgramCases.revisedSpec, ProgramCases.baselineSpec])
    (bootReady : SequentialCapture.Ready boot.session.frame.dossier.cursor) : IO Unit := do
  let actual := Program.execute frame ProgramCases.script
  let wrong := Program.execute frame ProgramCases.wrongScript
  let blocked := Program.execute frame ProgramCases.sourceBlockedScript
  saveCursor files 0 actual.1.dossier.cursor (SequentialCapture.program_ready actual.2 initial)
  saveCursor files 6 wrong.1.dossier.cursor (SequentialCapture.program_ready wrong.2 initial)
  saveCursor files 12 blocked.1.dossier.cursor (SequentialCapture.program_ready blocked.2 initial)
  let producedPrefix := Memory.run boot
    [.progress (AdaptiveCases.policy 4) (AdaptiveCases.feed true 0),
      .progress (AdaptiveCases.policy 4) (AdaptiveCases.feed true 1),
      .progress (AdaptiveCases.policy 4) (AdaptiveCases.feed true 2)]
  hybrid files producedPrefix.1 (SequentialCapture.memory_ready producedPrefix.2 bootReady)
  say
end StateAssemblyStart

def main (args : List String) : IO Unit :=
  if args.length == 25 then StateAssemblyStart.run args
        ConstitutiveSearch.Agent.Local.Documentary.ProgramCases.start
        ConstitutiveSearch.Agent.Local.Documentary.SequentialCases.initial
        ConstitutiveSearch.Agent.Local.Documentary.MemoryCases.boot
        ConstitutiveSearch.Agent.Local.Documentary.SequentialCases.initial
  else throw (IO.userError "Expected twenty-five paths")
"""
COLD = r"""
import Tests.LocalAlignment.DocumentaryStatePortable
import RelationalPerimeter.Computation.ConstitutiveSearch.EndogenousDecomposition.CausalOperationalExecution
__COMMON__

def run (files : List String) : IO Unit := do
  let bytes ← IO.FS.readBinFile (pathAt 0 files)
  match StatePortable.load bytes.data.toList with
  | none => throw (IO.userError "Threaded source record rejected")
  | some value => write (pathAt 11 files) (ControlCodec.bytes (StatePortable.envelope.words value))
  match StatePortable.restoreForNext bytes.data.toList with
  | none => throw (IO.userError "Complete threaded source rejected")
  | some ⟨_, _, ⟨state, fresh⟩⟩ =>
      write (pathAt 4 files) (stateResult state)
      let discovery := runThreadedNextDiscovery state
      let next := buildFromExecutedDiscovery state fresh discovery rfl
      write (pathAt 5 files) (stateResult next.run.nextRun.next)
  let generation ← IO.FS.readBinFile (pathAt 1 files)
  match GenerationPortable.restore generation.data.toList with
  | none => throw (IO.userError "Generation rejected")
  | some ⟨_, value⟩ => write (pathAt 6 files) (GenerationPortable.save value)
  let positive ← IO.FS.readBinFile (pathAt 2 files)
  match FoundationPortable.restore examplePresentation positive.data.toList with
  | none => throw (IO.userError "Positive constitution rejected")
  | some value =>
      write (pathAt 7 files) (FoundationPortable.save value)
      let future := generate value
      write (pathAt 8 files) (FoundationPortable.save future.1)
  let history ← IO.FS.readBinFile (pathAt 3 files)
  match HistoryPortable.restore examplePresentation history.data.toList with
  | none => throw (IO.userError "Rooted history rejected")
  | some value =>
      write (pathAt 9 files) (HistoryPortable.save value)
      let future := appendGenerated value (generate value.endpoint)
      write (pathAt 10 files) (HistoryPortable.save future)
  say
end StateAssemblyCold

def main (args : List String) : IO Unit :=
  if args.length == 12 then StateAssemblyCold.run args else throw (IO.userError "Expected twelve paths")
"""
SYNTHETIC = r"""
import Tests.LocalAlignment.DocumentaryStatePortable
__COMMON__

def run (input output : String) : IO Unit := do
  let bytes ← IO.FS.readBinFile input
  match StatePortable.restore bytes.data.toList with
  | none => throw (IO.userError "Valid synthetic source rejected")
  | some ⟨_, _, state⟩ => write output (stateResult state)
  say
end StateAssemblySynthetic
def main (args : List String) : IO Unit := match args with
  | input :: output :: rest => match rest with
    | [] => StateAssemblySynthetic.run input output
    | _ :: _ => throw (IO.userError "Expected input and output")
  | [] => throw (IO.userError "Expected input and output")
  | [_] => throw (IO.userError "Expected input and output")
"""
INVALID = r"""
import Tests.LocalAlignment.DocumentaryStatePortable
__COMMON__
def run : List String → IO Unit
  | [] => say
  | path :: rest => do
      let bytes ← IO.FS.readBinFile path
      if (StatePortable.restore bytes.data.toList).isSome then
        throw (IO.userError "Malformed source accepted")
      run rest
end StateAssemblyInvalid
def main (args : List String) : IO Unit := StateAssemblyInvalid.run args
"""


def client(directory, name, template, definitions):
    source = template.replace("__COMMON__", COMMON.replace("__NS__", name))
    names = [name + "." + n for n in ("write", "pathAt", "stateWords", "stateResult", "say", *definitions)] + ["main"]
    source += "\n/- AXIOM_AUDIT_BEGIN -/\n" + "".join("#print axioms " + n + "\n" for n in names) + "/- AXIOM_AUDIT_END -/\n"
    path = directory / (name + ".lean")
    path.write_text(source, encoding="utf-8", newline="\n")
    return path, names


def run_client(client_spec, arguments):
    path, names = client_spec
    process = subprocess.Popen(["lake", "env", "lean", "--run", str(path), *map(str, arguments)],
                               cwd=ROOT, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    try:
        out, err = process.communicate(timeout=60)
    except subprocess.TimeoutExpired:
        process.kill()
        process.communicate()
        raise
    expected = ["'" + name + "' does not depend on any axioms" for name in names] + ["STATE_ASSEMBLY_RUNTIME_OK"]
    if process.returncode or err or out.decode("utf-8", "strict").splitlines() != expected:
        raise ValueError("Audited state client failed: " + (out + err).decode("utf-8", "replace"))
    return {"client": path.name, "process_id": process.pid, "client_sha256": hashlib.sha256(path.read_bytes()).hexdigest(),
            "runtime_audits": len(names), "returncode": process.returncode}


def commands(program):
    return [len(program), *[word for value in program for word in ([0, 0] if value is None else [1, 1, value])]]


def tree(level):
    return [1] * level + [0]


def generation_words(depth, counts=(1, 1, 1, 1)):
    return [92, 1, depth, *tree(depth + 4), *counts]


def history_words(level):
    return [91, 1, *([1] * level), 0, *[word for end in range(1, level + 1) for word in tree(end)]]


def state_words(depth, program, decisions, provenance, counts=(1, 1, 1, 1), seed=None):
    return [93, 1, depth, *commands(program), *tree(depth + 4), *counts,
            2 * (depth + 4) if seed is None else seed,
            len(decisions), *[word for label, bit in decisions for word in (label, bit)],
            len(provenance), *provenance]


def state_oracle(depth, program, decisions, provenance, wire, counts=(1, 1, 1, 1)):
    # Include the terminal node of the received query-list traversal.
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
    words = [depth, *tree(depth + 4), *counts, 2 * (depth + 4),
             len(decisions), *[word for label, bit in decisions for word in (label, bit)],
             len(provenance), *provenance, len(bits), *bits, nodes, labels]
    return wire(words)


def main():
    shared = runpy.run_path(str(ROOT / "scripts/run-assignment-restart-smoke.py"))
    wire = shared["wire"]
    with tempfile.TemporaryDirectory(prefix="rp-state-assembly-") as temporary:
        directory = Path(temporary)
        # Clients/logs/binary files are development evidence outside the repository.
        start = client(directory, "StateAssemblyStart", START, ("saveCursor", "hybrid", "run"))
        cold = client(directory, "StateAssemblyCold", COLD, ("run",))
        synthetic = client(directory, "StateAssemblySynthetic", SYNTHETIC, ("run",))
        invalid = client(directory, "StateAssemblyInvalid", INVALID, ("run",))
        actual = {"complete": (3, [14, 12, 10]), "unsuitable": (2, [12, 10]), "blocked": (2, [12, 10])}
        start_paths = [directory / f"{key}-{suffix}.bin" for key in actual
                       for suffix in ("state", "generation", "positive", "history", "before", "after")]
        start_paths += [directory / "assembled.bin"] + [directory / f"assembled-{key}.bin" for key in
                       ("original", "resumed", "original-store", "resumed-store", "original-source", "resumed-source")]
        receipts = [run_client(start, start_paths)]
        comparisons = []
        for key, (depth, program) in actual.items():
            decisions = [(label, 1) for label in program]
            expected = {
                "state": state_words(depth, program, decisions, program),
                "generation": generation_words(depth),
                "positive": [90, 1, *tree(depth + 4)],
                "history": history_words(depth + 3),
            }
            for component, words in expected.items():
                if (directory / f"{key}-{component}.bin").read_bytes() != wire(words):
                    raise ValueError("Literal wire mismatch: " + key + " " + component)
            before = state_oracle(depth, program, decisions, program, wire)
            selected = 2 * depth + 10
            after = state_oracle(depth + 1, [selected, *program], [(selected, 1), *decisions], [selected, *program], wire)
            if (directory / f"{key}-before.bin").read_bytes() != before or (directory / f"{key}-after.bin").read_bytes() != after:
                raise ValueError("Original complete state or NEW threaded stage mismatch: " + key)
            cold_paths = [directory / f"{key}-{suffix}.bin" for suffix in
                          ("state", "generation", "positive", "history", "cold-before", "cold-after", "cold-generation",
                           "cold-positive", "future-positive", "cold-history", "future-history", "cold-state")]
            receipts.append(run_client(cold, cold_paths))
            for component in expected:
                if (directory / f"{key}-cold-{component}.bin").read_bytes() != (directory / f"{key}-{component}.bin").read_bytes():
                    raise ValueError("Cold component differs: " + key + " " + component)
            if (directory / f"{key}-cold-before.bin").read_bytes() != before or (directory / f"{key}-cold-after.bin").read_bytes() != after:
                raise ValueError("Cold complete state or NEW threaded stage mismatch: " + key)
            if (directory / f"{key}-future-positive.bin").read_bytes() != wire([90, 1, *tree(depth + 5)]):
                raise ValueError("NEW free generation mismatch: " + key)
            if (directory / f"{key}-future-history.bin").read_bytes() != wire(history_words(depth + 4)):
                raise ValueError("NEW generated history mismatch: " + key)
            comparisons.append({"case": key, "depth": depth, "decisions": decisions, "next_selected": selected,
                                "before_sha256": hashlib.sha256(before).hexdigest(), "after_sha256": hashlib.sha256(after).hexdigest()})
        for suffix in ("", "-store", "-source"):
            if (directory / ("assembled-original" + suffix + ".bin")).read_bytes() != (directory / ("assembled-resumed" + suffix + ".bin")).read_bytes():
                raise ValueError("Assembled continuation differs: " + suffix)
        synthetic_cases = {
            "seed-counts": (0, [], [], [], (7, 8, 9, 10)),
            "duplicate-decisions": (0, [], [(2, 0), (2, 0)], [2, 2], (1, 1, 1, 1)),
            "composition": (1, [None, 10, None], [(10, 1)], [10], (1, 1, 1, 1)),
        }
        for key, (depth, program, decisions, provenance, counts) in synthetic_cases.items():
            source, result = directory / (key + ".bin"), directory / (key + "-result.bin")
            source.write_bytes(wire(state_words(depth, program, decisions, provenance, counts)))
            receipts.append(run_client(synthetic, [source, result]))
            if result.read_bytes() != state_oracle(depth, program, decisions, provenance, wire, counts):
                raise ValueError("Synthetic full-field source mismatch: " + key)
        valid_words = state_words(0, [], [], [])
        invalid_words = [
            [94, 1], [93, 2], [-1, 1], [93, -1], [93, 1, -1],
            [*valid_words, 0],
            state_words(0, [0], [], []),
            state_words(0, [10], [], []),
            state_words(0, [], [], [], seed=9),
            state_words(0, [], [(2, 1)], [2]),
            state_words(0, [], [(2, 0)], [1]),
            state_words(0, [], [(2, 2)], [2]),
            [93, 1, 0, 0, 0, 1, 1, 1, 1, 8, 0, 0],
            [93, 1, 0, 0, *tree(5), 1, 1, 1, 1, 8, 0, 0],
        ]
        malformed = [wire(words) for words in invalid_words] + [b"", wire(valid_words)[:-1], wire(valid_words) + b"\x00",
                                                                  b"\x07" + wire(valid_words)[1:]]
        paths = []
        for index, value in enumerate(malformed):
            path = directory / f"invalid-{index}.bin"
            path.write_bytes(value)
            paths.append(path)
        receipts.append(run_client(invalid, paths))
        print("STATE_ASSEMBLY_RECEIPTS " + json.dumps({
            "kind": "development_smoke", "processes": receipts, "actual_comparisons": comparisons,
            "cold_source_restarts": 3, "cold_history_restarts": 3, "cold_generation_restarts": 3,
            "cold_constitution_restarts": 3, "new_cold_threaded_stages": 3, "new_cold_free_generations": 6,
            "synthetic_sources": len(synthetic_cases), "invalid_sources_rejected": len(malformed),
            "assembled_checkpoint_file_read": True, "assembled_continuation_round": 5,
            "assembled_continuation_remaining": 0, "assembled_master_representation": "captured_typed_payload",
            "full_master_cold_restart": False, "full_present_cold_restart": False, "qwen_calls": 0,
        }, sort_keys=True))
        print("STATE_ASSEMBLY_SMOKE_OK: complete source/history/generation/constitution cold restarts; "
              "NEW threaded stages; assembled typed-master file continuation; component scope")


if __name__ == "__main__":
    try:
        main()
    except (OSError, ValueError, KeyError, subprocess.TimeoutExpired) as error:
        print("STATE_ASSEMBLY_SMOKE_ERROR: " + str(error), file=sys.stderr)
        sys.exit(1)
