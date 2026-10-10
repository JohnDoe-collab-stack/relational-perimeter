#!/usr/bin/env python3
"""Development execution of finite documentary composition.

Check received fact/origin goals independently, actual events and reference
transport. A literal-input oracle covers permission subsets and finite request
lists. Render the actual produced dossier. No model inference is performed.
"""
import argparse
import itertools
from pathlib import Path
import subprocess
import sys
import tempfile

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parent.parent
CLIENT = r"""
import Tests.LocalAlignment.DocumentaryDossierCases
set_option genInjectivity false
set_option maxRecDepth 8192
set_option maxHeartbeats 20000000
namespace DocumentaryDossierSmoke
open ConstitutiveSearch.Agent.Local.Documentary
open ConstitutiveSearch.Agent.Local.Documentary.Cases
open ConstitutiveSearch.Agent.Local.Documentary.MasterCases
open ConstitutiveSearch.Agent.Local.Documentary.Dossier
open ConstitutiveSearch.Agent.Local.Documentary.DossierCases
open ConstitutiveSearch.EndogenousDecomposition

def verify : List Bool → IO Unit
  | [] => pure ()
  | verdict :: rest =>
      if verdict then verify rest
      else throw (IO.userError "Dossier composition or oracle verdict changed")

def matrix (allowed : List Nat) (tasks : List (Obligation context))
    (positions : List (Option Nat)) (complete : Bool) (count : Nat) : Bool :=
  let contract : Contract := ⟨allowed⟩
  let state : State sources contract := ⟨VariableMaster.Example.origin, empty sources contract⟩
  let result := Dossier.execute state tasks
  (result.2.events.map (fun event => event.map Citation.position) == positions) &&
  (goalSucceeded (demands tasks) result.1.memory.items == complete) &&
  (result.1.memory.items.length == count) &&
  (result.1.cursor.depth == state.cursor.depth + tasks.length)

def run : IO Unit := do
  verify [
    goalSucceeded (demands tasks) produced.1.memory.items,
    produced.1.memory.items.length == 2,
    produced.1.cursor.depth == start.cursor.depth + 2,
    produced.2.events.map (fun event => event.map Citation.position) == [some 1, some 2],
    produced.1.memory.items.map (fun item => item.source.version) == [2, 1],
    !goalSucceeded (demands [first, pinned, revision]) withRefusal.1.memory.items,
    withRefusal.2.events.map (fun event => event.map Citation.position) == [some 1, none, some 2],
    goalSucceeded [factDemand, revisedDemand] withRefusal.1.memory.items,
    withRefusal.1.memory.items.length == 2,
    withRefusal.1.cursor.depth == start.cursor.depth + 3,
    !goalSucceeded (demands [unavailable, revision]) withUnavailable.1.memory.items,
    withUnavailable.2.events.map (fun event => event.map Citation.position) == [none, some 2],
    repeated.1.memory.items.length == 2,
    goalSucceeded (demands [first, first]) repeated.1.memory.items,
    noTasks.1.memory.items.length == 0,
    noTasks.1.cursor.depth == start.cursor.depth,
    goalSucceeded [factDemand, revisedDemand] erased.1.memory.items,
    resumed.1.cursor.depth == firstPart.1.cursor.depth + 1,
    goalSucceeded [factDemand, revisedDemand] resumed.1.memory.items,
    goalSucceeded (demands tasks) existing.1.memory.items,
    keptReference.position == 1]
__MATRIX__
  let stdout ← IO.getStdout
  stdout.write ⟨(utf8 "DOCUMENTARY_DOSSIER_DOCUMENT_BEGIN\n").toArray⟩
  stdout.write ⟨ConstitutiveSearch.Agent.Local.Documentary.DossierCases.actualDocument.toArray⟩
  stdout.write ⟨(utf8 "DOCUMENTARY_DOSSIER_DOCUMENT_END\n").toArray⟩
end DocumentaryDossierSmoke
def main : IO Unit := DocumentaryDossierSmoke.run
/- AXIOM_AUDIT_BEGIN -/
#print axioms DocumentaryDossierSmoke.verify
#print axioms DocumentaryDossierSmoke.matrix
#print axioms DocumentaryDossierSmoke.run
#print axioms main
/- AXIOM_AUDIT_END -/
"""
EXPECTED = (
    b"> La mesure certifiee est 42.\n\n"
    b"Source 1, version 1, extrait 0, occurrence recue 1.\n"
    b"Fait 7 = 42.\n"
    b"> La mesure revisee est 43.\n\n"
    b"Source 1, version 2, extrait 0, occurrence recue 2.\n"
    b"Fait 7 = 43.\n"
)
HEADER = (
    "# Dossier sourcé produit par la composition du maître\n\n"
    "Cas construit de développement, sans inférence du modèle. "
    "Chaque demande consomme le successeur et la mémoire produits par la demande précédente. "
    "Le corps ci-dessous est copié depuis les éléments réellement constitués.\n\n"
).encode("utf-8")


def oracle_matrix():
    # These received literals are independent of the Lean producer and checker.
    values = [42, 42, 43]
    jobs = [(42, None, 0, 1), (43, None, 1, 2),
            (42, 0, 0, 1), (44, None, 1, 2)]
    names = ["first", "revision", "pinned", "unavailable"]
    checks = []
    for mask in range(8):
        allowed = [i for i in range(3) if mask & (1 << i)]
        for length in range(4):
            for indices in itertools.product(range(4), repeat=length):
                positions, items = [], []
                for index in indices:
                    value, pin, left, right = jobs[index]
                    eligible = lambda origin: (origin in allowed and values[origin] == value
                                               and (pin is None or pin == origin))
                    position = right if eligible(right) else left if eligible(left) else None
                    positions.append(position)
                    if position is not None:
                        items.append((position, values[position]))
                complete = all(any(fact == jobs[index][0] and
                                   (jobs[index][1] is None or origin == jobs[index][1])
                                   for origin, fact in items) for index in indices)
                task_literal = "[" + ", ".join(names[i] for i in indices) + "]"
                position_literal = "[" + ", ".join("none" if i is None else "some " + str(i)
                                                  for i in positions) + "]"
                check = (f"matrix {allowed} {task_literal} {position_literal} "
                         f"{str(complete).lower()} {len(items)}")
                checks.append(check)
    return checks


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, help="Create a new Markdown artifact; never overwrite.")
    args = parser.parse_args()
    if args.output and args.output.exists():
        raise ValueError("Output already exists; choose a fresh artifact path.")
    checks = oracle_matrix()
    groups = []
    for offset in range(0, len(checks), 40):
        groups.append("  verify [\n    " + ",\n    ".join("(" + check + ")"
                      for check in checks[offset:offset + 40]) + "]")
    client_source = CLIENT.replace("__MATRIX__", "\n".join(groups))
    with tempfile.TemporaryDirectory(prefix="rp-documentary-dossier-smoke-") as directory:
        client = Path(directory) / "Smoke.lean"
        client.write_text(client_source, encoding="utf-8", newline="\n")
        result = subprocess.run(["lake", "env", "lean", "--run", str(client)], cwd=ROOT,
                                capture_output=True, timeout=120, check=False)
    if result.returncode or result.stderr:
        raise ValueError("Lean dossier smoke failed: " +
                         (result.stdout + result.stderr).decode("utf-8", "replace"))
    audit, marker, remainder = result.stdout.partition(b"DOCUMENTARY_DOSSIER_DOCUMENT_BEGIN\n")
    required = {b"'DocumentaryDossierSmoke.verify' does not depend on any axioms",
                b"'DocumentaryDossierSmoke.matrix' does not depend on any axioms",
                b"'DocumentaryDossierSmoke.run' does not depend on any axioms",
                b"'main' does not depend on any axioms"}
    if not marker or set(audit.splitlines()) != required:
        raise ValueError("Missing clean runtime audit or unexpected output.")
    document, end, suffix = remainder.partition(b"DOCUMENTARY_DOSSIER_DOCUMENT_END\n")
    if not end or suffix or document != EXPECTED:
        raise ValueError("Actual produced dossier differs from the constructed fixture.")
    if args.output:
        with args.output.open("xb") as stream:
            stream.write(HEADER + document)
    print(f"DOCUMENTARY_DOSSIER_SMOKE_OK: 21 fixture checks; {len(checks)} literal-oracle cases; "
          "four clean runtime audits; actual events, continuation, old references and exact dossier")
    sys.stdout.flush()
    sys.stdout.buffer.write(document)


if __name__ == "__main__":
    try:
        main()
    except (OSError, ValueError, subprocess.TimeoutExpired) as error:
        print("DOCUMENTARY_DOSSIER_SMOKE_ERROR: " + str(error), file=sys.stderr)
        sys.exit(1)
