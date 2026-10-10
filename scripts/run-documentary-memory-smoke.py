#!/usr/bin/env python3
"""Constructed memory/checkpoint smoke with an independent literal-state oracle.

Typed payloads only: no disk checkpoint, physical restart or model inference.
The protocol varies policy, reset, checkpoint cut and task incompatibility.
"""
import itertools
from pathlib import Path
import runpy
import subprocess
import sys
import tempfile

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parent.parent
CLIENT = r"""
import Tests.LocalAlignment.DocumentaryMemoryCases
set_option genInjectivity false
set_option maxRecDepth 8192
set_option maxHeartbeats 30000000
namespace DocumentaryMemorySmoke
open ConstitutiveSearch.Resources
open ConstitutiveSearch.Agent.Local.Documentary
open Program Adaptive Snapshot Memory

def verify (index : Nat) : List Bool → IO Unit
  | [] => pure ()
  | passed :: rest => if passed then verify (index + 1) rest else do
      let stderr ← IO.getStderr
      stderr.write ⟨(Cases.utf8 (Nat.repr index)).toArray⟩
      throw (IO.userError "Documentary memory verdict changed")

def route : Adaptive.Route → Nat
  | .matched => 0 | .reversed => 1 | .absent => 2
  | .invalid => 3 | .inspected => 4 | .diverted => 5

def production : Program.Event → Nat
  | .quoted => 0 | .derived => 1 | .refused => 2 | .missing => 3

def event : Memory.Event → List Int
  | .produced summary => [0, Int.ofNat (route summary.route)] ++ summary.events.map (fun e => Int.ofNat (production e))
  | .inspected none => [1, -1]
  | .inspected (some found) => [1, Int.ofNat found.position, found.value] ++ found.origins.map Int.ofNat
  | .observed clock depth available slots remaining complete =>
      [2, Int.ofNat clock, Int.ofNat depth, Int.ofNat available, Int.ofNat slots, Int.ofNat remaining, if complete then 1 else 0]
  | .reset => [3]
  | .finished => [4]

def commands (mode : Nat) (forget : Bool) (resetAt : Nat) : List (Memory.Request Nat) :=
  (List.range 5).flatMap (fun clock =>
    (if clock == resetAt then [.reset (AdaptiveCases.policy mode)] else []) ++
      [.inspect 0, .status, .progress (AdaptiveCases.policy mode) (AdaptiveCases.feed forget clock)]) ++
    (if resetAt == 5 then [.reset (AdaptiveCases.policy mode)] else []) ++ [.inspect 0, .inspect 99, .status]

def inventory {context sources contract rules Context final}
    (data : @PresentData context sources contract rules Context final) : List (Option Int) :=
  (List.range data.session.frame.store.1.length).map (fun index =>
    (Adaptive.locate data.session.frame.store.1 index).map (fun found => data.session.frame.store.2.resources.read found.2))

def matrix {final} (boot : PresentData Cases.sources Cases.contract DeductionCases.policy Nat final) (mode : Nat) (forget : Bool) (resetAt cut : Nat)
    (values items : List (Option Int)) (positions : List (Option Nat)) (productions routes : List Nat)
    (heads : Nat) (completed : Bool) : Bool :=
  let requests := commands mode forget resetAt
  let prefixSize := cut * 3 + (if resetAt < cut then 1 else 0)
  let executedPrefix := Memory.sourceRun ⟨boot, []⟩ (requests.take prefixSize)
  let tail := requests.drop prefixSize
  match Snapshot.load (Snapshot.save (project executedPrefix.1)) with
  | none => false
  | some loaded =>
      let reduced := Memory.run loaded tail
      let rich := Memory.sourceRun executedPrefix.1 tail
      let retained := reduced.1
      let reads := (List.range 5).map (Memory.read retained)
      let summaries := rich.1.archive.reverse.map (fun received => received.summary)
      (reduced.2.events.map event == rich.2.map event) &&
      (reads.map (fun found => found.map (fun result => result.value)) == values) &&
      (reads.map (fun found => found.map (fun result => result.position)) == positions) &&
      (inventory retained == items) &&
      (summaries.flatMap (fun summary => summary.events.map production) == productions) &&
      (summaries.map (fun summary => route summary.route) == routes) &&
      (rich.1.archive.length == 5) && (retained.remaining.length == 0) &&
      (retained.session.round == 5) && (retained.session.frame.dossier.cursor.depth == heads) &&
      (Program.succeeded retained.session.frame.restore == completed) &&
      (retained.session.context == if resetAt == 5 then 0 else if forget then 1 else 5 - resetAt) &&
      ((Memory.accepted retained (.inspect 99)).isSome == false) &&
      ((Memory.accepted retained (.inspect 0)).isSome == (Memory.read retained 0).isSome) &&
      (Snapshot.load { Snapshot.save retained with version := 2 }).isNone

def run : IO Unit := do
  let loaded := MemoryCases.loaded
  let resumed := MemoryCases.resumed
  let terminal := MemoryCases.terminal
  verify 0 [loaded.session.round == 3, loaded.remaining.length == 2,
    (Memory.read loaded 0).map (fun found => found.value) == some 1,
    (Memory.read loaded 0).map (fun found => found.origins) == some [1, 2],
    Program.succeeded resumed.1.frame, resumed.1.round == 5,
    resumed.1.frame.store.2.resources.read terminal.occurrence.2 == 2,
    terminal.occurrence.1.origins == [1, 2, 1, 2],
    MemoryCases.continued.1.remaining.length == 0,
    (Memory.read MemoryCases.continued.1 0).map (fun found => found.value) == some 2,
    (Memory.read MemoryCases.versionOne 0).map (fun found => found.value) == some 42,
    (Memory.read MemoryCases.versionTwo 0).map (fun found => found.value) == some 42,
    (Memory.read MemoryCases.versionOne 0).map (fun found => found.origins) == some [1],
    (Memory.read MemoryCases.versionTwo 0).map (fun found => found.origins) == some [2],
    MemoryCases.leftProduced.1.archive.length == 1, MemoryCases.rightProduced.1.archive.length == 1,
    loaded.session.context == 1, (loaded.reset MemoryCases.contextPolicy).session.context == 0,
    (Memory.read (loaded.reset MemoryCases.contextPolicy) 0).map (fun found => found.value) == some 1]
__MATRIX__
  let stdout ← IO.getStdout
  stdout.write ⟨(Cases.utf8 "DOCUMENTARY_MEMORY_SMOKE_DONE\n").toArray⟩
end DocumentaryMemorySmoke
def main : IO Unit := DocumentaryMemorySmoke.run
/- AXIOM_AUDIT_BEGIN -/
#print axioms DocumentaryMemorySmoke.verify
#print axioms DocumentaryMemorySmoke.route
#print axioms DocumentaryMemorySmoke.production
#print axioms DocumentaryMemorySmoke.event
#print axioms DocumentaryMemorySmoke.commands
#print axioms DocumentaryMemorySmoke.inventory
#print axioms DocumentaryMemorySmoke.matrix
#print axioms DocumentaryMemorySmoke.run
#print axioms main
/- AXIOM_AUDIT_END -/
"""


def main():
    oracle = runpy.run_path(str(ROOT / "scripts/run-documentary-adaptive-smoke.py"))["oracle"]
    checks = []
    options = lambda xs: "[" + ", ".join("none" if x is None else f"some ({x})" for x in xs) + "]"
    boolean = lambda x: "true" if x else "false"
    for mode, forget, reset, cut in itertools.product(range(8), [False, True], range(6), range(6)):
        values, items, positions, events, routes, _, heads, complete = oracle(
            42, 43, [0, 1], False, False, mode)
        checks.append(f"matrix (Snapshot.present (Adaptive.Present.mk [] AdaptiveCases.start ProgramCases.script)) {mode} {boolean(forget)} {reset} {cut} {options(values)} {options(items)} "
                      f"{options(positions)} {events} {routes} {heads} {boolean(complete)}")
    for forget, reset, cut in itertools.product([False, True], range(6), range(6)):
        checks.append(f"matrix (Snapshot.present (Adaptive.Present.mk [] AdaptiveCases.start ProgramCases.blockedScript)) "
                      f"0 {boolean(forget)} {reset} {cut} [some 42, none, none, some 43, some 42] "
                      "[some 42, some 43, some 42] [some 0, none, none, some 1, some 2] "
                      "[0, 0, 2, 3, 0] [2, 2, 2, 2, 2] 3 false")
    groups = ["  verify " + str(19 + i) + " [\n    " + ",\n    ".join("(" + c + ")" for c in checks[i:i + 40]) + "]"
              for i in range(0, len(checks), 40)]
    with tempfile.TemporaryDirectory(prefix="rp-documentary-memory-smoke-") as directory:
        client = Path(directory) / "Smoke.lean"
        client.write_text(CLIENT.replace("__MATRIX__", "\n".join(groups)), encoding="utf-8", newline="\n")
        result = subprocess.run(["lake", "env", "lean", "--run", str(client)], cwd=ROOT,
                                capture_output=True, timeout=300, check=False)
    if result.returncode or result.stderr:
        raise ValueError("Lean memory smoke failed: " + (result.stdout + result.stderr).decode("utf-8", "replace"))
    names = ["verify", "route", "production", "event", "commands", "inventory", "matrix", "run"]
    expected = {("'DocumentaryMemorySmoke." + name + "' does not depend on any axioms").encode() for name in names}
    expected.add(b"'main' does not depend on any axioms")
    expected.add(b"DOCUMENTARY_MEMORY_SMOKE_DONE")
    if set(result.stdout.splitlines()) != expected or len(result.stdout.splitlines()) != len(expected):
        raise ValueError("Missing runtime audit or unexpected output: " + result.stdout.decode("utf-8", "replace"))
    print(f"DOCUMENTARY_MEMORY_SMOKE_OK: 19 fixed checks, {len(checks)} literal-oracle checkpoint/reset cases, nine clean runtime audits; typed payloads only")


if __name__ == "__main__":
    try:
        main()
    except (OSError, ValueError, subprocess.TimeoutExpired) as error:
        print("DOCUMENTARY_MEMORY_SMOKE_ERROR: " + str(error), file=sys.stderr)
        sys.exit(1)
