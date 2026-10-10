#!/usr/bin/env python3
"""Control/store component restart with independent literal wire and graph oracles.

No physical master restoration is claimed. The fresh loader never executes a
master quotation; a separate in-process case supplies the same actual dossier
and store and tests future execution after control-byte restoration.
"""
import copy
from pathlib import Path
import runpy
import subprocess
import sys
import tempfile

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parent.parent
BASELINE = [0, 7, 42, 1, 1]
REVISION = [0, 7, 43, 1, 2]
DELTA = [1, 1, 1, 0, 1, 2, 1, 2]
SUM = [1, 2, 1, 1, 1, 4, 1, 2, 1, 2]
QUOTE = [0, 7, 42, 1, 1, 0, 1]
CONCLUDE = [1, 1, 1, 1, *SUM[1:]]
NORMAL = [[1, 0, 1, 0, 1], [0, 2, 43], [0, 1, 42]]
WRONG_ORDER = [[1, 0, 2, 1, 1], [1, 0, 0, 1, -1], [0, 2, 43], [0, 1, 42]]
COMMON = r"""
set_option genInjectivity false
set_option maxRecDepth 8192
set_option maxHeartbeats 30000000
namespace ControlSmoke
open ConstitutiveSearch.Resources
open ConstitutiveSearch.Agent.Local.Documentary
open ConstitutiveSearch.Agent.Local.Documentary.Program

def write (path : String) (bytes : List UInt8) : IO Unit :=
  IO.FS.writeBinFile path ⟨bytes.toArray⟩
def say (message : String) : IO Unit := do
  let output ← IO.getStdout
  output.write message.toUTF8
def final : List Specification :=
  [.conclusion PortableCheckpoint.demand, PortableCheckpoint.baseline,
   PortableCheckpoint.delta, PortableCheckpoint.revision, PortableCheckpoint.baseline]
"""
ENTRY = r"""
end ControlSmoke
def main (args : List String) : IO Unit := match args with
  | [store, control, restoredControl, restoredStore] => ControlSmoke.run store control restoredControl restoredStore
  | [] => throw (IO.userError "Expected four paths")
  | [_] => throw (IO.userError "Expected four paths")
  | [_, _] => throw (IO.userError "Expected four paths")
  | [_, _, _] => throw (IO.userError "Expected four paths")
  | _ :: _ :: _ :: _ :: _ :: _ => throw (IO.userError "Expected four paths")
"""
START_HEAD = r"""
def prefixTasks : Script PortableCheckpoint.context PortableCheckpoint.policy []
    [PortableCheckpoint.delta, PortableCheckpoint.revision, PortableCheckpoint.baseline] :=
  .cons (.quotation PortableStart.baselineTask) (.cons (.quotation PortableStart.revisionTask)
    (.cons (.conclusion PortableCheckpoint.difference (.prior .here) .here
      ⟨1, some 0, some [1, 2]⟩) .done))
def remaining : Script PortableCheckpoint.context PortableCheckpoint.policy
    [PortableCheckpoint.delta, PortableCheckpoint.revision, PortableCheckpoint.baseline] final :=
  .cons (.quotation PortableStart.baselineTask)
    (.cons (.conclusion PortableCheckpoint.sum (.prior .here) (.prior .here) PortableCheckpoint.demand) .done)
"""
START_RUN = r"""
def run (store control _restoredControl _restoredStore : String) : IO Unit := do
  let frame := PortableStart.initial ConstitutiveSearch.EndogenousDecomposition.VariableMaster.Example.origin
  let initial : Adaptive.Session PortableCheckpoint.sources PortableCheckpoint.contract PortableCheckpoint.policy Nat [] :=
    ⟨frame, 0, 0, none⟩
  let actual := Adaptive.run policy (fun _ => ⟨"received task", __FORGET__⟩) initial prefixTasks
  let data := Snapshot.present (Adaptive.Present.mk _ actual.1 remaining)
  let kept := if __RESET__ then data.reset policy else data
  write store (PortableStore.save kept.session.frame.store)
  write control (PortableControl.save ControlCodec.natural (PortableControl.capture kept))
  say "CONTROL_COMPONENT_SAVED\n"
"""
RESUME = ("import Tests.LocalAlignment.DocumentaryPortableControl\n"
          "import Tests.LocalAlignment.DocumentaryPortableStore\n" + COMMON + r"""
def run (storePath controlPath restoredControl restoredStore : String) : IO Unit := do
  let stored ← IO.FS.readBinFile storePath
  let control ← IO.FS.readBinFile controlPath
  match PortableStore.load PortableCheckpoint.sources PortableCheckpoint.contract PortableCheckpoint.policy stored.data.toList with
  | .error _ => throw (IO.userError "Store component rejected")
  | .ok store => match PortableControl.load ControlCodec.natural store final control.data.toList with
    | none => throw (IO.userError "Control component rejected")
    | some loaded =>
        write restoredControl (PortableControl.save ControlCodec.natural loaded)
        write restoredStore (PortableStore.save store)
        say "CONTROL_COMPONENT_RESTORED\n"
""" + ENTRY)
TYPED = ("import Tests.LocalAlignment.DocumentaryPortableControl\n"
         "import Tests.LocalAlignment.DocumentaryMemoryCases\n" + COMMON + r"""
def reload {context sources contract rules final}
    (before : @Snapshot.PresentData context sources contract rules Nat final) :=
  PortableControl.loadPresent ControlCodec.natural before.session.frame.dossier before.session.frame.store final
    (PortableControl.save ControlCodec.natural (PortableControl.capture before))

def run (_store _control _restoredControl _restoredStore : String) : IO Unit := do
  let before := MemoryCases.retainedPrefix
  match reload before with
  | none => throw (IO.userError "Actual prefix control rejected")
  | some loaded =>
      let actual := Memory.run loaded MemoryCases.futures
      if actual.1.remaining.length != 0 || actual.1.session.round != 5 then
        throw (IO.userError "Loaded control failed to finish")
      match Memory.read actual.1 0 with
      | none => throw (IO.userError "Loaded control has no conclusion")
      | some result => if result.value != 2 || result.origins != [1, 2, 1, 2] then
          throw (IO.userError "Loaded control altered the actual future")
  let blocked := MemoryCases.blockedRetained
  match reload blocked with
  | none => throw (IO.userError "Blocked control incorrectly rejected")
  | some loaded =>
      if succeeded loaded.session.frame.restore ||
          (PortableControl.record (PortableControl.capture loaded)).bindings != [some 0, none, none, some 1, some 2] then
        throw (IO.userError "Missing bindings or failed goal were repaired")
  let unsuitable := Adaptive.run (AdaptiveCases.policy 0) (AdaptiveCases.feed false)
    AdaptiveCases.start ProgramCases.wrongScript
  let wrong := Snapshot.present (Adaptive.Present.mk _ unsuitable.1 .done)
  match reload wrong with
  | none => throw (IO.userError "Permitted unsuitable output incorrectly rejected")
  | some loaded =>
      if succeeded loaded.session.frame.restore ||
          (PortableControl.record (PortableControl.capture loaded)).bindings != [some 0, some 1, some 2, some 3] then
        throw (IO.userError "Unsuitable output was repaired or dropped")
  let completed := MemoryCases.finalData
  match reload completed with
  | none => throw (IO.userError "Completed control rejected")
  | some loaded =>
      if (PortableControl.record (PortableControl.capture loaded)).bindings !=
          [some 0, some 2, some 3, some 4, some 5] then
        throw (IO.userError "Equal-valued occurrence ports were merged")
  say "CONTROL_BYTES_WITH_SUPPLIED_MASTER_CONTINUED\n"
""" + ENTRY)


def opt_nat(value):
    return [0] if value is None else [1, value]


def summary_words(summary):
    if summary is None:
        return [0]
    route, events, inspection = summary
    result = [1, route, len(events), *events]
    if inspection is None:
        return result + [0]
    position, value, origins = inspection
    return result + [1, position, value, len(origins), *origins]


def words(raw):
    result = [raw["version"], raw["schema"], len(raw["slots"])]
    for spec in raw["slots"]:
        result.extend(spec)
    result.append(len(raw["bindings"]))
    for binding in raw["bindings"]:
        result.extend(opt_nat(binding))
    result.append(len(raw["remaining"]))
    for command in raw["remaining"]:
        result.extend(command)
    return result + [raw["context"], raw["round"], *summary_words(raw["last"])]


def wire(values):
    def word(value):
        return bytes([0 if value >= 0 else 1] + [1] * (value if value >= 0 else -value - 1) + [2])
    return word(len(values)) + b"".join(word(value) for value in values)


def oracle(mode, forget, reset=False):
    raw = dict(version=1, schema=4, slots=[DELTA, REVISION, BASELINE],
               bindings=[0, 2, 3] if mode == 6 else [0, 1, 2],
               remaining=[QUOTE, CONCLUDE], context=0 if reset else 1 if forget else 3, round=3)
    route = {0: 2, 1: 0, 2: 4, 3: 3, 4: 5, 5: 0, 6: 5, 7: 0}[mode]
    events = [2, 1] if mode == 4 else [1, 1] if mode == 6 else [1]
    raw["last"] = (route, events, (0, 43, [2]) if mode == 2 else None)
    return raw


def invoke(source, client, paths, names, marker, success=True):
    client.write_text(source + "\n/- AXIOM_AUDIT_BEGIN -/\n" + "".join(
        "#print axioms " + name + "\n" for name in names) + "/- AXIOM_AUDIT_END -/\n", encoding="utf-8", newline="\n")
    process = subprocess.Popen(["lake", "env", "lean", "--run", str(client), *map(str, paths)],
                               cwd=ROOT, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    try:
        stdout, stderr = process.communicate(timeout=120)
    except subprocess.TimeoutExpired:
        process.kill()
        process.communicate()
        raise ValueError("Control client timed out") from None
    lines = stdout.decode("utf-8", "strict").splitlines()
    audit = ["'" + name + "' does not depend on any axioms" for name in names]
    if success:
        if process.returncode or stderr or lines != audit + [marker]:
            raise ValueError("Control client failed: " + (stdout + stderr).decode("utf-8", "replace"))
    elif not process.returncode or lines != audit or b"Control component rejected" not in stderr:
        raise ValueError("Bad control did not reach the audited loader: " + (stdout + stderr).decode("utf-8", "replace"))
    return process.pid


def main():
    old = runpy.run_path(str(ROOT / "scripts/run-documentary-portable-store-smoke.py"))
    old_wire = runpy.run_path(str(ROOT / "scripts/run-documentary-checkpoint-smoke.py"))["wire"]
    start_policy = old["START"][old["START"].index("def proposal"):old["START"].index("def run")]
    start = ("import Tests.LocalAlignment.DocumentaryPortableControl\n"
             "import Tests.LocalAlignment.DocumentaryPortableStore\n"
             "import Tests.LocalAlignment.DocumentaryPortableStart\n" + COMMON + START_HEAD + start_policy + START_RUN + ENTRY)
    base_names = ["ControlSmoke.write", "ControlSmoke.say", "ControlSmoke.final", "ControlSmoke.run", "main"]
    start_names = base_names[:3] + ["ControlSmoke.prefixTasks", "ControlSmoke.remaining", "ControlSmoke.proposal", "ControlSmoke.policy"] + base_names[3:]
    pids, restarts = [], 0
    with tempfile.TemporaryDirectory(prefix="rp-portable-control-") as temporary:
        directory = Path(temporary)
        regimes = [(mode, forget, False) for mode in range(8) for forget in (False, True)]
        regimes += [(4, False, True), (6, False, True)]
        for index, (mode, forget, reset) in enumerate(regimes):
            paths = [directory / f"{index}-{name}" for name in ("store.bin", "control.bin", "loaded-control.bin", "loaded-store.bin")]
            source = start.replace("__MODE__", str(mode)).replace("__FORGET__", str(forget).lower()).replace("__RESET__", str(reset).lower())
            first = invoke(source, directory / "Start.lean", paths, start_names, "CONTROL_COMPONENT_SAVED")
            expected = wire(words(oracle(mode, forget, reset)))
            expected_store = old_wire(dict(version=1, schema=2, round=0, depth=0, task=0,
                                           nodes=WRONG_ORDER if mode == 6 else NORMAL, bindings=[]))
            if paths[0].read_bytes() != expected_store or paths[1].read_bytes() != expected:
                raise ValueError(f"Actual control/store differs from literal oracle: mode={mode} forget={forget} reset={reset}")
            second = invoke(RESUME, directory / "Resume.lean", paths, base_names, "CONTROL_COMPONENT_RESTORED")
            if first == second or paths[2].read_bytes() != expected or paths[3].read_bytes() != expected_store:
                raise ValueError("Fresh-process control/store restoration changed actual data")
            pids.extend((first, second))
            restarts += 1
        base = oracle(4, True)
        mutations = []
        for key, value in (("version", 2), ("schema", 3), ("bindings", [0, 1]),
                           ("bindings", [0, 1, 2, None]), ("bindings", [99, 1, 2]),
                           ("bindings", [-1, 1, 2]), ("context", -1), ("round", -1),
                           ("remaining", []), ("slots", [DELTA, BASELINE, BASELINE]),
                           ("last", (6, [1], None)), ("last", (5, [4], None))):
            changed = copy.deepcopy(base)
            changed[key] = value
            mutations.append((key, wire(words(changed))))
        for command_index, field_index in ((0, 5), (1, 1), (1, 2), (1, 3)):
            changed = copy.deepcopy(base)
            changed["remaining"][command_index][field_index] = 99
            mutations.append(("missing-port", wire(words(changed))))
        original = wire(words(base))
        mutations += [("truncated", original[:-1]), ("trailing-byte", original + bytes([0])),
                      ("alphabet", bytes([7]) + original[1:]), ("trailing-word", wire(words(base) + [0]))]
        valid_store = old_wire(dict(version=1, schema=2, round=0, depth=0, task=0, nodes=NORMAL, bindings=[]))
        for index, (label, invalid) in enumerate(mutations):
            paths = [directory / f"bad-{index}-{name}" for name in ("store.bin", "control.bin", "loaded-control.bin", "loaded-store.bin")]
            paths[0].write_bytes(valid_store)
            paths[1].write_bytes(invalid)
            pids.append(invoke(RESUME, directory / "Resume.lean", paths, base_names, "", False))
            if paths[2].exists() or paths[3].exists():
                raise ValueError("Rejected control produced an output: " + label)
        pids.append(invoke(TYPED, directory / "Typed.lean", [directory / "unused"] * 4,
                           base_names[:3] + ["ControlSmoke.reload"] + base_names[3:],
                           "CONTROL_BYTES_WITH_SUPPLIED_MASTER_CONTINUED"))
    print(f"PORTABLE_CONTROL_SMOKE_OK: {len(pids)} processes; {restarts} control/store component restarts; "
          f"{len(mutations)} invalid controls rejected; pending quotation and sum restored; "
          "future quotation/sum with supplied actual master; full-present byte restart still open")


if __name__ == "__main__":
    try:
        main()
    except (OSError, ValueError, KeyError, UnicodeError) as error:
        print("PORTABLE_CONTROL_SMOKE_ERROR: " + str(error), file=sys.stderr)
        sys.exit(1)
