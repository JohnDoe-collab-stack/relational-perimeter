#!/usr/bin/env python3
"""Fuel matrices over actual documentary packets, with literal expectations.

Producer entry counts are abstract labels, not their internal resource bounds.
Control loading receives the existing dossier/store, as in the component codec.
"""
import hashlib
from pathlib import Path
import subprocess
import sys
import tempfile

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parent.parent
CLIENT = r"""
import Tests.LocalAlignment.DocumentaryControlInterpreterCases
set_option genInjectivity false
set_option maxRecDepth 8192
set_option maxHeartbeats 30000000
namespace DocumentaryInterpreterSmoke
open ConstitutiveSearch.Resources
open ConstitutiveSearch.Agent.Local.Documentary
open Program Snapshot Control ControlBindings ControlInterpreterCases

def tag : Label → Nat
  | .instruction => 0
  | .binding => 1
  | .quotationProducer => 2
  | .deductionProducer => 3
  | .missingAssembly => 4
  | .naturalComparison => 5
  | .permissionCell => 6
  | .permissionReturn => 7
  | .deductionDecision => 8
  | .deductionAssembly => 9
  | .referencePosition => 10
  | .referenceReturn => 11

def traceTag {Value : Type u} {code : Code Label Value} {labels value} :
    Eval code labels value → Nat
  | .done => 0
  | .step _ => 1

def eventTag : Event → Nat
  | .quoted => 0
  | .derived => 1
  | .refused => 2
  | .missing => 3

def stepCheck {slots spec}
    (before : FrameData Cases.sources Cases.contract DeductionCases.policy slots)
    (instruction : Instruction Cases.context DeductionCases.policy slots spec)
    (bound : Nat) (labels : List Nat) (event : Event) (value : Option Int)
    (origins : Option (List Nat)) (successful : Bool) (fuel : Nat) : Bool :=
  match Control.execute fuel (ControlStep.code before instruction) with
  | none => fuel < bound
  | some actual =>
      let packet := actual.value.1
      let found := packet.next.bindings .here
      let readValue := ProgramCases.bindingValue packet.next.store found
      let readOrigins := found.map (fun occurrence => occurrence.1.origins)
      (bound ≤ fuel) && (actual.labels.map tag == labels) &&
        (eventTag packet.event == eventTag event) && (readValue == value) && (readOrigins == origins) &&
        (Program.succeeded packet.next == successful)

def readCheck {spec}
    (slot : Ref [ProgramCases.sumSpec, ProgramCases.baselineSpec, ProgramCases.deltaSpec,
      ProgramCases.revisedSpec, ProgramCases.baselineSpec] spec)
    (bound position : Nat) (fuel : Nat) : Bool :=
  match Control.execute fuel (readCode finalTable slot) with
  | none => fuel < bound
  | some actual => (bound ≤ fuel) && (actual.labels.map tag == List.replicate bound 1) &&
      (ProgramCases.bindingPosition ProgramCases.actual.1.store actual.value.1 == some position) &&
      (ProgramCases.bindingValue ProgramCases.actual.1.store actual.value.1 == some 42)

def matrices : List Bool :=
  let fuels := List.range 24
  (fuels.map (stepCheck quoteFrame quoteInstruction 2 [0, 2] .quoted (some 42) (some [1]) true)) ++
  (fuels.map (stepCheck twoFrame differenceInstruction 10 [0, 1, 1, 1, 10, 6, 5, 7, 3, 9]
    .derived (some 1) (some [1, 2]) true)) ++
  (fuels.map (stepCheck sumFrame sumInstruction 17 [0, 1, 1, 1, 1, 10, 10, 11, 6, 5, 6, 5, 5, 7, 7, 3, 9]
    .derived (some 2) (some [1, 2, 1, 2]) true)) ++
  (fuels.map (stepCheck twoFrame forbiddenInstruction 19 [0, 1, 1, 1, 10, 10, 10, 11, 11, 6, 5, 6, 5, 5, 6, 7, 7, 8, 9]
    .refused none none false)) ++
  (fuels.map (stepCheck refusedFrame leftMissing 3 [0, 1, 4] .missing none none false)) ++
  (fuels.map (stepCheck refusedFrame rightMissing 5 [0, 1, 1, 1, 4] .missing none none false)) ++
  (fuels.map (stepCheck quoteFrame (.quotation ⟨Cases.pinnedDemand, Cases.privateOrigin, Cases.publicOrigin⟩)
    2 [0, 2] .refused none none false)) ++
  (fuels.map (stepCheck twoFrame
    (.conclusion DeductionCases.differenceRequest (.prior .here) .here ProgramCases.wrongDemand)
    10 [0, 1, 1, 1, 10, 6, 5, 7, 3, 9] .derived (some 1) (some [1, 2]) false)) ++
  (fuels.map (readCheck oldest 5 4)) ++ (fuels.map (readCheck repeated 2 1))

def permissionCheck (scope : List Nat) (position cost : Nat) (found : Option Nat)
    (labels : List Nat) (fuel : Nat) : Bool :=
  match Control.execute fuel (ControlPermission.lookupCode scope position) with
  | none => fuel < cost
  | some actual => (cost ≤ fuel) &&
      (actual.value.1.map Ref.position == found) && (actual.labels.map tag == labels)

def permissionMatrices : List Bool :=
  let fuels := List.range 39
  (fuels.map (permissionCheck [] 7 1 none [6])) ++
  (fuels.map (permissionCheck [1, 1] 1 4 (some 0) [6, 5, 5, 7])) ++
  (fuels.map (permissionCheck [3, 5, 5] 5 14 (some 1)
    [6, 5, 5, 5, 5, 6, 5, 5, 5, 5, 5, 5, 7, 7])) ++
  (fuels.map (permissionCheck [0, 1] 2 8 none [6, 5, 6, 5, 5, 6, 7, 7])) ++
  (fuels.map (permissionCheck [32] 32 35 (some 0) (6 :: (List.replicate 33 5 ++ [7])))) ++
  (fuels.map (permissionCheck [32] 31 35 none (6 :: (List.replicate 32 5 ++ [6, 7]))))

def positionCheck {Kind : Type u} {scope : List Kind} {kind : Kind} (ref : Ref scope kind)
    (position cost : Nat) (labels : List Nat) (fuel : Nat) : Bool :=
  match Control.execute fuel (ControlReference.positionCode ref) with
  | none => fuel < cost
  | some actual => (cost ≤ fuel) && (actual.value.1 == position) && (actual.labels.map tag == labels)

def positionMatrices : List Bool :=
  let fuels := List.range 24
  (fuels.map (positionCheck DeductionCases.differenceRequest.2 0 1 [10])) ++
  (fuels.map (positionCheck DeductionCases.sumRequest.2 1 3 [10, 10, 11])) ++
  (fuels.map (positionCheck DeductionCases.duplicateRequest.2 2 5 [10, 10, 10, 11, 11]))

def fromScript {slots}
    (frame : FrameData Cases.sources Cases.contract DeductionCases.policy slots)
    (script : Script Cases.context DeductionCases.policy slots
      [ProgramCases.sumSpec, ProgramCases.baselineSpec, ProgramCases.deltaSpec,
        ProgramCases.revisedSpec, ProgramCases.baselineSpec]) : Bool :=
  match script with
  | .done => false
  | .cons instruction _ =>
      stepCheck frame instruction 2 [0, 2] .quoted (some 42) (some [1]) true 2

def fromPresent (before : PresentData Cases.sources Cases.contract DeductionCases.policy Nat
    [ProgramCases.sumSpec, ProgramCases.baselineSpec, ProgramCases.deltaSpec,
      ProgramCases.revisedSpec, ProgramCases.baselineSpec]) : Bool :=
  fromScript before.session.frame before.remaining

def loaded : Bool :=
  let before := MemoryCases.retainedPrefix
  match PortableControl.loadPresent ControlCodec.natural
    before.session.frame.dossier before.session.frame.store _
    (PortableControl.save ControlCodec.natural (PortableControl.capture before)) with
  | none => false
  | some restored => fromPresent restored

def verify (index : Nat) : List Bool → IO Unit
  | [] => pure ()
  | passed :: rest => if passed then verify (index + 1) rest else do
      let stderr ← IO.getStderr
      stderr.write ⟨(Cases.utf8 (Nat.repr index)).toArray⟩
      throw (IO.userError "Documentary interpreter verdict changed")

def run : IO Unit := do
  let certified := sumActual.sound
  verify 0 (matrices ++ permissionMatrices ++ positionMatrices ++ [fromPresent MemoryCases.retainedPrefix,
    fromPresent (MemoryCases.retainedPrefix.reset (AdaptiveCases.policy 4)), loaded,
    stepCheck (Memory.project MemoryCases.leftProduced.1).session.frame
      (.quotation ProgramCases.revisedTask) 2 [0, 2] .quoted (some 43) (some [2]) true 2,
    stepCheck (Memory.project MemoryCases.rightProduced.1).session.frame
      (.quotation ProgramCases.revisedTask) 2 [0, 2] .quoted (some 43) (some [2]) true 2,
    sumActual.labels.length == 17,
    sumActual.value.1.next.store.2.resources.read terminal.occurrence.2 == 2,
    terminal.occurrence.1.origins == [1, 2, 1, 2],
    traceTag certified.1 == 1])
  let stdout ← IO.getStdout
  stdout.write ⟨(Cases.utf8 "DOCUMENTARY_INTERPRETER_SMOKE_DONE\n").toArray⟩
end DocumentaryInterpreterSmoke
def main : IO Unit := DocumentaryInterpreterSmoke.run
/- AXIOM_AUDIT_BEGIN -/
#print axioms DocumentaryInterpreterSmoke.tag
#print axioms DocumentaryInterpreterSmoke.traceTag
#print axioms DocumentaryInterpreterSmoke.eventTag
#print axioms DocumentaryInterpreterSmoke.stepCheck
#print axioms DocumentaryInterpreterSmoke.readCheck
#print axioms DocumentaryInterpreterSmoke.matrices
#print axioms DocumentaryInterpreterSmoke.permissionCheck
#print axioms DocumentaryInterpreterSmoke.permissionMatrices
#print axioms DocumentaryInterpreterSmoke.positionCheck
#print axioms DocumentaryInterpreterSmoke.positionMatrices
#print axioms DocumentaryInterpreterSmoke.fromScript
#print axioms DocumentaryInterpreterSmoke.fromPresent
#print axioms DocumentaryInterpreterSmoke.loaded
#print axioms DocumentaryInterpreterSmoke.verify
#print axioms DocumentaryInterpreterSmoke.run
#print axioms main
/- AXIOM_AUDIT_END -/
"""


def main():
    source = CLIENT.encode("utf-8")
    with tempfile.TemporaryDirectory(prefix="rp-documentary-interpreter-smoke-") as directory:
        client = Path(directory) / "Smoke.lean"
        client.write_bytes(source)
        result = subprocess.run(["lake", "env", "lean", "--run", str(client)], cwd=ROOT,
                                capture_output=True, timeout=300, check=False)
    if result.returncode or result.stderr:
        raise ValueError("Lean interpreter smoke failed: " +
                         (result.stdout + result.stderr).decode("utf-8", "replace"))
    expected = {("'DocumentaryInterpreterSmoke." + name + "' does not depend on any axioms").encode()
                for name in ("tag", "traceTag", "eventTag", "stepCheck", "readCheck", "matrices", "permissionCheck", "permissionMatrices", "positionCheck", "positionMatrices", "fromScript", "fromPresent",
                             "loaded", "verify", "run")}
    expected.update((b"'main' does not depend on any axioms", b"DOCUMENTARY_INTERPRETER_SMOKE_DONE"))
    if set(result.stdout.splitlines()) != expected or len(result.stdout.splitlines()) != len(expected):
        raise ValueError("Missing runtime audit or unexpected output: " + result.stdout.decode("utf-8", "replace"))
    print("DOCUMENTARY_INTERPRETER_SMOKE_OK: 240 documentary, 234 permission and 72 position fuel checks, nine integration checks, "
          "16 clean runtime audits; client_sha256=" + hashlib.sha256(source).hexdigest())


if __name__ == "__main__":
    try:
        main()
    except (OSError, ValueError, subprocess.TimeoutExpired) as error:
        print("DOCUMENTARY_INTERPRETER_SMOKE_ERROR: " + str(error), file=sys.stderr)
        sys.exit(1)
