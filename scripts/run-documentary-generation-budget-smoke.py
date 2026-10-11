#!/usr/bin/env python3
"""Frozen component probes; source allowances precede generator execution.

Fixture histories use the original constructor. Production uses the opened
generator and the separately controlled allowance. No physical bound claim.
"""
import hashlib
from pathlib import Path
import subprocess
import sys
import tempfile

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parent.parent
CLIENT = r"""
import Tests.LocalAlignment.DocumentaryGenerationBudgetCases
set_option genInjectivity false
set_option backward.match.sparseCases false
set_option maxRecDepth 16384
set_option maxHeartbeats 30000000
namespace GenerationBudgetSmoke
open StrongPerimetralTurning ConstitutiveSearch ConstitutiveSearch.EndogenousDecomposition
open ConstitutiveSearch.Agent.Local.Documentary
open Control ControlBindings GenerationBudgetCases

def generationLabel : Label → Bool
  | .masterNextStateGeneration => true
  | _ => false

def probe (depth : Nat) : Bool :=
  let received := source depth
  let bootstrap := ControlGenerationBudget.canonicalBoundCode received
  let bootstrapFuel := ControlGenerationBudget.canonicalBootstrapBound received
  match Control.execute bootstrapFuel bootstrap with
  | none => false
  | some allowance =>
    let code := ControlConstitutiveGeneration.canonicalCode received rfl
    match Control.execute allowance.value.1 code with
    | none => false
    | some actual =>
      let length := actual.labels.length
      let exact := Control.execute length code
      let short := Control.execute (length - 1) code
      let surplus := Control.execute (allowance.value.1 + 5) code
      let bootstrapShort := Control.execute (allowance.labels.length - 1) bootstrap
      let bootstrapHasNoGeneration := !(allowance.labels.any generationLabel)
      let oneGeneration := (actual.labels.filter generationLabel).length == 1
      let counters := actual.value.1.generateCalls == 1 && actual.value.1.generatedSteps == 1 &&
        actual.value.1.provenanceUnits == 1 && actual.value.1.certificatesProduced == 1
      let stable := match exact, surplus with
        | some first, some second => first.labels.length == second.labels.length
        | _, _ => false
      bootstrapHasNoGeneration && oneGeneration && counters && stable && exact.isSome &&
        !short.isSome && !bootstrapShort.isSome && !(Control.execute 0 code).isSome &&
        allowance.value.1 == ControlConstitutiveGeneration.bound received + 1 &&
        length <= allowance.value.1 && allowance.labels.length <= bootstrapFuel

def run : IO Unit := do
  if !(probe 0 && probe 1 && probe 2 && probe 5) then
    throw (IO.userError "Generation allowance mismatch")
  let stdout ← IO.getStdout
  stdout.write "DOCUMENTARY_GENERATION_BUDGET_SMOKE_DONE\n".toUTF8
end GenerationBudgetSmoke
def main : IO Unit := GenerationBudgetSmoke.run
/- AXIOM_AUDIT_BEGIN -/
#print axioms GenerationBudgetSmoke.generationLabel
#print axioms GenerationBudgetSmoke.probe
#print axioms GenerationBudgetSmoke.run
#print axioms main
/- AXIOM_AUDIT_END -/
"""

def main():
    source = CLIENT.encode("utf-8")
    with tempfile.TemporaryDirectory(prefix="rp-generation-budget-") as directory:
        client = Path(directory) / "Smoke.lean"
        client.write_bytes(source)
        result = subprocess.run(["lake", "env", "lean", "--run", str(client)], cwd=ROOT,
                                capture_output=True, timeout=300, check=False)
    if result.returncode or result.stderr:
        raise ValueError((result.stdout + result.stderr).decode("utf-8", "replace"))
    expected = {("'GenerationBudgetSmoke." + name + "' does not depend on any axioms").encode()
                for name in ("generationLabel", "probe", "run")}
    expected.update((b"'main' does not depend on any axioms", b"DOCUMENTARY_GENERATION_BUDGET_SMOKE_DONE"))
    if set(result.stdout.splitlines()) != expected or len(result.stdout.splitlines()) != len(expected):
        raise ValueError("Unexpected runtime output: " + result.stdout.decode("utf-8", "replace"))
    print("DOCUMENTARY_GENERATION_BUDGET_SMOKE_OK: four histories; source bootstrap, exact/short/surplus fuel; "
          "four clean runtime audits; client_sha256=" + hashlib.sha256(source).hexdigest())

if __name__ == "__main__":
    try:
        main()
    except (OSError, ValueError, subprocess.TimeoutExpired) as error:
        print("DOCUMENTARY_GENERATION_BUDGET_SMOKE_ERROR: " + str(error), file=sys.stderr)
        sys.exit(1)
