#!/usr/bin/env python3
"""Run actual recovery from initial, forgotten and loaded documentary presents.

Literal expected results are independent of the adapter's validity certificates.
Control byte loading still receives the same dossier/store. The assembled load
still retains its typed master. This is not a whole-state cold restart.
"""
import hashlib
from pathlib import Path
import subprocess
import sys
import tempfile

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parent.parent
CLIENT = r"""
import Tests.LocalAlignment.DocumentaryRecoveryDataCases
set_option genInjectivity false
set_option maxRecDepth 8192
set_option maxHeartbeats 30000000
namespace DocumentaryRecoverySmoke
open ConstitutiveSearch.Resources
open ConstitutiveSearch.Agent.Local.Documentary
open Program Adaptive Snapshot

def verify (index : Nat) : List Bool → IO Unit
  | [] => pure ()
  | passed :: rest => if passed then verify (index + 1) rest else do
      let stderr ← IO.getStderr
      stderr.write ⟨(Cases.utf8 (Nat.repr index)).toArray⟩
      throw (IO.userError "Documentary recovery verdict changed")

def resume (before : PresentData Cases.sources Cases.contract DeductionCases.policy Nat
    [ProgramCases.sumSpec, ProgramCases.baselineSpec, ProgramCases.deltaSpec,
     ProgramCases.revisedSpec, ProgramCases.baselineSpec]) (attempts : Nat) : Bool :=
  let actual := RecoveryData.recover before
  let retained := Snapshot.present
    ⟨[ProgramCases.sumSpec, ProgramCases.baselineSpec, ProgramCases.deltaSpec,
      ProgramCases.revisedSpec, ProgramCases.baselineSpec], actual.1, .done⟩
  (actual.2.attempts == attempts) && (actual.1.round == 5) &&
    Program.succeeded actual.1.frame && (retained.remaining.length == 0) &&
    ((Memory.read retained 0).map (fun found => found.value) == some 2) &&
    ((Memory.read retained 0).map (fun found => found.origins) == some [1, 2, 1, 2])

def controlLoaded : Bool :=
  let before := MemoryCases.retainedPrefix
  match PortableControl.loadPresent ControlCodec.natural
    before.session.frame.dossier before.session.frame.store _
    (PortableControl.save ControlCodec.natural (PortableControl.capture before)) with
  | none => false
  | some loaded => resume loaded 2

def assembledLoaded : Bool :=
  match AssembledCheckpoint.restore Cases.sources Cases.contract DeductionCases.policy
    ControlCodec.natural _ AssembledCases.boot with
  | none => false
  | some loaded => resume loaded 5

def run : IO Unit := do
  let report := RecoveryDataCases.report
  let packet := RecoveryData.prepare MemoryCases.retainedPrefix
  let resetPacket := RecoveryData.prepare (MemoryCases.retainedPrefix.reset (AdaptiveCases.policy 4))
  let blocked := RecoveryDataCases.blockedRecovery
  verify 0 [report.1 == 5, report.2.1 == 2, report.2.2.1 == 5,
    report.2.2.2.1 == 2, report.2.2.2.2.1 == [1, 2, 1, 2],
    report.2.2.2.2.2.1 == false, report.2.2.2.2.2.2 == 5,
    resume MemoryCases.boot 5, resume MemoryCases.retainedPrefix 2,
    resume (MemoryCases.retainedPrefix.reset (AdaptiveCases.policy 4)) 2,
    resume (Memory.project MemoryCases.leftProduced.1) 4,
    resume (Memory.project MemoryCases.rightProduced.1) 4,
    controlLoaded, assembledLoaded,
    packet.transition.next.remaining.length == 1,
    packet.transition.next.session.round == 4,
    resetPacket.transition.next.session.context == 0,
    resetPacket.transition.next.remaining.length == 1,
    (Memory.read packet.transition.next 0).map (fun found => found.value) == some 42,
    (Memory.read packet.transition.next 1).map (fun found => found.value) == some 1,
    blocked.1.round == 5, Program.succeeded blocked.1.frame == false,
    blocked.2.attempts == 5]
  let stdout ← IO.getStdout
  stdout.write ⟨(Cases.utf8 "DOCUMENTARY_RECOVERY_SMOKE_DONE\n").toArray⟩
end DocumentaryRecoverySmoke

def main : IO Unit := DocumentaryRecoverySmoke.run
/- AXIOM_AUDIT_BEGIN -/
#print axioms DocumentaryRecoverySmoke.verify
#print axioms DocumentaryRecoverySmoke.resume
#print axioms DocumentaryRecoverySmoke.controlLoaded
#print axioms DocumentaryRecoverySmoke.assembledLoaded
#print axioms DocumentaryRecoverySmoke.run
#print axioms main
/- AXIOM_AUDIT_END -/
"""


def main():
    source = CLIENT.encode("utf-8")
    with tempfile.TemporaryDirectory(prefix="rp-documentary-recovery-smoke-") as directory:
        client = Path(directory) / "Smoke.lean"
        client.write_bytes(source)
        result = subprocess.run(["lake", "env", "lean", "--run", str(client)], cwd=ROOT,
                                capture_output=True, timeout=300, check=False)
    if result.returncode or result.stderr:
        raise ValueError("Lean recovery smoke failed: " + (result.stdout + result.stderr).decode("utf-8", "replace"))
    expected = {("'DocumentaryRecoverySmoke." + name + "' does not depend on any axioms").encode()
                for name in ("verify", "resume", "controlLoaded", "assembledLoaded", "run")}
    expected.update((b"'main' does not depend on any axioms", b"DOCUMENTARY_RECOVERY_SMOKE_DONE"))
    if set(result.stdout.splitlines()) != expected or len(result.stdout.splitlines()) != len(expected):
        raise ValueError("Missing runtime audit or unexpected output: " + result.stdout.decode("utf-8", "replace"))
    print("DOCUMENTARY_RECOVERY_SMOKE_OK: 23 literal checks, six clean runtime audits; "
          "component loading with supplied master; client_sha256=" + hashlib.sha256(source).hexdigest())


if __name__ == "__main__":
    try:
        main()
    except (OSError, ValueError, subprocess.TimeoutExpired) as error:
        print("DOCUMENTARY_RECOVERY_SMOKE_ERROR: " + str(error), file=sys.stderr)
        sys.exit(1)
