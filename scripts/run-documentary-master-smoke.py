#!/usr/bin/env python3
"""Development execution of the two-source documentary master bridge.

Run independent goal checks, actual source-origin readouts, changing retained
frontiers and continuation from the produced successor. Copy the actual rendered
bytes unchanged. No model inference or reduced-state checkpoint is claimed.
"""
import argparse
from pathlib import Path
import subprocess
import sys
import tempfile

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parent.parent
CLIENT = r"""
import Tests.LocalAlignment.DocumentaryMasterCases
namespace DocumentaryMasterSmoke
open ConstitutiveSearch.Agent.Local.Documentary
open ConstitutiveSearch.Agent.Local.Documentary.Cases
open ConstitutiveSearch.Agent.Local.Documentary.MasterCases

def verify : List (Bool × Bool) → IO Unit
  | [] => pure ()
  | check :: rest =>
      if check.1 == check.2 then verify rest
      else throw (IO.userError "master documentary verdict or readout changed")

def run : IO Unit := do
  let checks := [
    (factRun.1.reduction.retained.length == 2, true),
    (bothRun.1.reduction.retained.length == 1, true),
    (goalSucceeded [factDemand] factRun.2.result.1.items, true),
    (factRun.2.result.2.map Citation.position == some 1, true),
    (bothRun.2.result.2.map Citation.position == some 1, true),
    (goalSucceeded [pinnedDemand] pinnedRun.2.result.1.items, false),
    (pinnedRun.2.result.2.isNone, true),
    (goalSucceeded [revisedDemand] revisedRun.2.result.1.items, true),
    (revisedRun.2.result.2.map Citation.position == some 2, true),
    (revisedRun.2.result.2.map (fun item => item.passage.value) == some 43, true),
    (goalSucceeded [factDemand] revisedRun.2.result.1.items, false),
    (goalSucceeded [factDemand] contextErasedRun.2.result.1.items, true),
    (goalSucceeded [pinnedDemand] pinnedContextErasedRun.2.result.1.items, false),
    (pinnedContextErasedRun.2.result.2.isNone, true),
    (goalSucceeded [factDemand] continuedRun.2.result.1.items, true),
    (continuedRun.2.result.1.items.length == 2, true),
    (continuedRun.1.head.next.depth == factRun.1.head.next.depth + 1, true)]
  verify checks
  let stdout ← IO.getStdout
  stdout.write ⟨(utf8 "DOCUMENTARY_MASTER_DOCUMENT_BEGIN\n").toArray⟩
  stdout.write ⟨ConstitutiveSearch.Agent.Local.Documentary.MasterCases.actualDocument.toArray⟩
  stdout.write ⟨(utf8 "DOCUMENTARY_MASTER_DOCUMENT_END\n").toArray⟩
end DocumentaryMasterSmoke
def main : IO Unit := DocumentaryMasterSmoke.run
/- AXIOM_AUDIT_BEGIN -/
#print axioms DocumentaryMasterSmoke.verify
#print axioms DocumentaryMasterSmoke.run
#print axioms main
/- AXIOM_AUDIT_END -/
"""
EXPECTED = (
    b"> La mesure certifiee est 42.\n\n"
    b"Source 1, version 1, extrait 0, occurrence recue 1.\n"
    b"Fait 7 = 42.\n"
)
HEADER = (
    "# Élément documentaire produit par le raccord au maître\n\n"
    "Cas construit de développement, sans inférence du modèle. "
    "Le maître produit une découverte ; les sources, la demande et les permissions "
    "déterminent le problème reçu. L'ouverture et le regroupement exécutés "
    "déterminent l'occurrence finalement extraite. Le corps ci-dessous est copié "
    "depuis cette production Lean.\n\n"
).encode("utf-8")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, help="Create a new Markdown artifact; never overwrite.")
    args = parser.parse_args()
    if args.output and args.output.exists():
        raise ValueError("Output already exists; choose a fresh artifact path.")
    with tempfile.TemporaryDirectory(prefix="rp-documentary-master-smoke-") as directory:
        client = Path(directory) / "Smoke.lean"
        client.write_text(CLIENT, encoding="utf-8", newline="\n")
        result = subprocess.run(["lake", "env", "lean", "--run", str(client)], cwd=ROOT,
                                capture_output=True, timeout=120, check=False)
    if result.returncode or result.stderr:
        raise ValueError("Lean master smoke failed: " +
                         (result.stdout + result.stderr).decode("utf-8", "replace"))
    audit, marker, remainder = result.stdout.partition(b"DOCUMENTARY_MASTER_DOCUMENT_BEGIN\n")
    required = {b"'DocumentaryMasterSmoke.verify' does not depend on any axioms",
                b"'DocumentaryMasterSmoke.run' does not depend on any axioms",
                b"'main' does not depend on any axioms"}
    if not marker or set(audit.splitlines()) != required:
        raise ValueError("Missing clean runtime audit or unexpected output.")
    document, end, suffix = remainder.partition(b"DOCUMENTARY_MASTER_DOCUMENT_END\n")
    if not end or suffix or document != EXPECTED:
        raise ValueError("Actual master documentary output differs from the constructed fixture.")
    if args.output:
        with args.output.open("xb") as stream:
            stream.write(HEADER + document)
    print("DOCUMENTARY_MASTER_SMOKE_OK: 17 checks; independent goals; origins; actual widths; "
          "produced successor; exact output; clean runtime audit")
    sys.stdout.flush()
    sys.stdout.buffer.write(document)


if __name__ == "__main__":
    try:
        main()
    except (OSError, ValueError, subprocess.TimeoutExpired) as error:
        print("DOCUMENTARY_MASTER_SMOKE_ERROR: " + str(error), file=sys.stderr)
        sys.exit(1)
