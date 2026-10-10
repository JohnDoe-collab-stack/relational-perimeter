#!/usr/bin/env python3
"""Non-confirmatory execution of the constructed documentary semantic fixture.

The temporary Lean client evaluates the real producer and independent goal
checker. Its output bytes are copied unchanged, apart from an explanatory header.
No local model, master-engine bridge or checkpoint run is claimed here.
"""
import argparse
from pathlib import Path
import subprocess
import sys
import tempfile

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parent.parent
CLIENT = r"""
import Tests.LocalAlignment.DocumentaryCases
namespace DocumentarySmoke
open ConstitutiveSearch.Agent.Local.Documentary
open ConstitutiveSearch.Agent.Local.Documentary.Cases

def verify : List (Bool × Bool) → IO Unit
  | [] => pure ()
  | check :: rest =>
      if check.1 == check.2 then verify rest
      else throw (IO.userError "independent goal verdict changed")

def run : IO Unit := do
  let checks := [
    (goalSucceeded [factDemand] initial.items, false),
    (goalSucceeded [factDemand] (execute initial privateOrigin).1.items, false),
    (goalSucceeded [factDemand] alternativeResult.1.items, true),
    (goalSucceeded [pinnedDemand] alternativeResult.1.items, false),
    (goalSucceeded [factDemand] (execute initial updatedOrigin).1.items, false)]
  verify checks
  let stdout ← IO.getStdout
  stdout.write ⟨(utf8 "DOCUMENTARY_SMOKE_DOCUMENT_BEGIN\n").toArray⟩
  stdout.write ⟨actualDocument.toArray⟩
  stdout.write ⟨(utf8 "DOCUMENTARY_SMOKE_DOCUMENT_END\n").toArray⟩
end DocumentarySmoke
def main : IO Unit := DocumentarySmoke.run
/- AXIOM_AUDIT_BEGIN -/
#print axioms DocumentarySmoke.verify
#print axioms DocumentarySmoke.run
#print axioms main
/- AXIOM_AUDIT_END -/
"""
EXPECTED = (
    b"> La mesure certifiee est 42.\n\n"
    b"Source 1, version 1, extrait 0, occurrence recue 1.\n"
    b"Fait 7 = 42.\n"
)
HEADER = (
    "# Premier élément documentaire constitué\n\n"
    "Cas construit de développement, sans inférence du modèle. "
    "Le contenu ci-dessous provient de l'opération Lean autorisée après refus "
    "d'une autre occurrence et effacement du contexte de proposition.\n\n"
).encode("utf-8")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, help="Create a new Markdown fixture artifact; never overwrite.")
    args = parser.parse_args()
    if args.output and args.output.exists():
        raise ValueError("Output already exists; choose a fresh artifact path.")
    with tempfile.TemporaryDirectory(prefix="rp-documentary-smoke-") as directory:
        client = Path(directory) / "Smoke.lean"
        client.write_text(CLIENT, encoding="utf-8", newline="\n")
        result = subprocess.run(["lake", "env", "lean", "--run", str(client)], cwd=ROOT,
                                capture_output=True, timeout=120, check=False)
    if result.returncode or result.stderr:
        raise ValueError("Lean smoke failed: " + (result.stdout + result.stderr).decode("utf-8", "replace"))
    audit, marker, remainder = result.stdout.partition(b"DOCUMENTARY_SMOKE_DOCUMENT_BEGIN\n")
    required = {b"'DocumentarySmoke.verify' does not depend on any axioms",
                b"'DocumentarySmoke.run' does not depend on any axioms",
                b"'main' does not depend on any axioms"}
    if not marker or set(audit.splitlines()) != required:
        raise ValueError("Missing clean runtime audit or unexpected output.")
    document, end, suffix = remainder.partition(b"DOCUMENTARY_SMOKE_DOCUMENT_END\n")
    if not end or suffix or document != EXPECTED:
        raise ValueError("Actual documentary output differs from the frozen constructed fixture.")
    if args.output:
        with args.output.open("xb") as stream:
            stream.write(HEADER + document)
    print("DOCUMENTARY_SMOKE_OK: 5 independent goal verdicts; exact actual output; clean runtime audit")
    sys.stdout.flush()
    sys.stdout.buffer.write(document)


if __name__ == "__main__":
    try:
        main()
    except (OSError, ValueError, subprocess.TimeoutExpired) as error:
        print("DOCUMENTARY_SMOKE_ERROR: " + str(error), file=sys.stderr)
        sys.exit(1)
