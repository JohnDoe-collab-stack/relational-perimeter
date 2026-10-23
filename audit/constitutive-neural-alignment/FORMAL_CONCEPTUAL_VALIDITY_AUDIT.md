# Independent formal and conceptual validity audit

Report failures plainly. Do not repair the target repository during the audit.
Do not infer success from names, comments, tests that merely mention a theorem,
or the existence of a certificate field. A negative or inconclusive verdict is
an acceptable outcome.

## 1. Exact material

- Repository: `https://github.com/JohnDoe-collab-stack/relational-perimeter.git`
- Branch: `codex/constitutive-neural-alignment-implementation`
- Scientific evidence revision:
  `1cb2d9119458ef57bb30dc8b6ec66d259aa427a4`
- Registry-link revision:
  `88b6928e2535911e0c2c88d9ca77df256e2e0e1c`
- Evidence parent: `19e3c2fea9a15461e354f3e35e65683aa4572711`
- Remote `main` expected at preparation time:
  `822fa2a0e0bcb2eba667ca4bcbfab5989f623c42`
- Expected merge-base with `origin/main`:
  `1e5aeda745559d62a3819bb3213da7fce3c31ad1`
- Toolchain: the unchanged `lean-toolchain` in the source archive, currently
  Lean `v4.33.1`.

The supplied offline archive is authoritative if remote access is unavailable.
Before doing any substantive work, record the SHA-256 of that archive, verify
the revisions above inside it, and hash every tracked file. Repeat the file hash
comparison at the end. Mutations and probes must run only in disposable copies.

## 2. Immutable targets and scope

Read these files completely before testing the implementation:

- `docs/work/CIBLE_ALIGNEMENT_CONSTITUTIF_INCREMENTAL.fr.md`
- `docs/work/CONSTITUTIVE_NEURAL_ALIGNMENT_TARGETS.fr.md`
- `docs/work/RAPPORT_VERIFICATION_ALIGNEMENT_CONSTITUTIF_fafd739.fr.md`
- `docs/alignement-constitutif-neuronal-incremental.fr.md`
- `docs/incremental-constitutive-neural-alignment.en.md`
- `docs/work/L11_PREVALIDATION_CANDIDAT_ALIGNEMENT_CONSTITUTIF.fr.md`
- `docs/work/NEURAL_ALIGNMENT_IMPLEMENTATION_MATRIX.md`
- `docs/scientific-claims.json`
- `docs/reports/revue-interne-alignement-constitutif-neuronal-1cb2d91.md`

Treat C1–C18, G1–G10 and RC1–RC6 exactly as written. Do not substitute a
weaker target, and do not promote an implementation-plan obligation into a
result. The canonical French and English claims are relative to a received
meta-contract and their declared finite interfaces. They do not claim to
discover human values, justify the norm, align every AI system, or prove a
resource advantage.

## 3. Required repository checks

Run from clean checkouts of the exact revisions and report commands, exit
codes, warnings and selected-file counts:

```text
lake clean
lake build +RelationalPerimeter
lake build
python scripts/check-scientific-docs.py --self-test
python scripts/check-scientific-docs.py --static
python scripts/check-scientific-docs.py --lean
pwsh -NoProfile -File scripts/verify.ps1
bash scripts/verify.sh
git diff --check
lake update
```

Confirm that `lake update` leaves `lake-manifest.json` byte-identical. Confirm
that both portals select the same Lean files. Check production-module
reachability, all import-boundary and stratification inventories, all compiled
code checks, all negative fixtures and all scientific-document checks.

Scan every Lean source for forbidden constructs, including `axiom`, `sorry`,
`noncomputable`, `Classical`, `propext`, `Quot.sound` and `native_decide`.
Verify exactly one final `AXIOM_AUDIT` block per Lean file. Inspect every
constant, not only registered public declarations, and distinguish handwritten
from compiler-generated constants. No handwritten result may depend on an
axiom.

## 4. Formal chain to audit

Audit the complete producer-to-consumer chain, not isolated theorem names:

```text
received meta-contract and current contract
  -> serialized artifact/update and exact decoding
  -> native neural execution
  -> non-identity transformation and proposal
  -> one produced action occurrence
  -> one effect consuming that action
  -> event, memory and successor consuming that effect
  -> autonomous local obligations and transition decision
  -> affected-cone calculation from decoded graph and delta
  -> licensed transport plus recomputation
  -> assembled target certificate
  -> independent complete recheck
  -> dependent checked trace and closed runtime installation
  -> covered future continuation or refusal before effect
```

For each arrow identify the exact declaration, the produced value or witness,
the consumer, whether the dependency is definitional or propositional, and an
adversarial probe showing that a foreign or reconstructed substitute is
rejected for a substantive reason.

## 5. Mandatory questions

Answer every question `VERIFIED`, `QUALIFIED` or `FALSE`, with file,
declaration, probe and log references.

1. Are primitive relational roles and their witnesses consumed in the actual
   construction, rather than stored next to an otherwise relation-free result?
2. Is the artifact/update received as serialized data without a target
   certificate, and is the installed material exactly what was decoded?
3. Are stable identities distinct from `Fin` positions across insertion,
   removal, renaming and reindexing?
4. Are transformation, proposal, action, effect and successor produced by one
   executed chain? Can a constant post-hoc transformation, foreign action,
   rebuilt effect or equal-valued foreign occurrence replace any of them?
5. Are the required source system, new requirement, context and incorporated
   authorization all consumed by the learned reconfiguration?
6. Are operational obligations defined independently of checker success and
   then decided by executable local analyses?
7. Is the complete reference checker independent of the incremental verdict,
   incremental fragments and target certificate?
8. Does the incremental target certificate actually consume licensed
   transported source fragments and recomputed affected fragments, rather than
   a regenerated complete target snapshot?
9. Is acceptance equivalence with the complete recheck proved on the same
   domain and property, and do successful paths produce the same successor?
10. Can successive accepted transitions start only from the exact state and
    contract produced by the preceding transition?
11. Does the closed runtime install only accepted updates, with rejected
    updates unable to yield an installable successor or effect?
12. On the learned instance, do aligned and bypass updates have the same
    admitted intention and the same current table, while the same API accepts
    and installs the aligned update and refuses the bypass specifically for the
    missing constitutive authorization dependency?
13. Does the nonempty future continuation use the exact produced states and
    exact future contract, with aligned satisfaction and pure counterfactual
    bypass violation?
14. Does forgetting begin with two operational states that still carry
    distinct origins, execute an actual reduction, preserve every covered
    future and make origin reconstruction impossible? Keep preservation and
    irrecoverability separate.
15. Are grouping, forgetting, equality of values, equality of source states,
    admission and normative satisfaction kept distinct in the types?
16. Are C1–C17, G1–G10 and RC1–RC6 all closed jointly on the claimed learned
    lineage, rather than sampled from unrelated public examples?
17. Do the canonical French and English texts state exactly the formal scope,
    hypotheses, producers and exclusions, with no stronger causal,
    generality, cost or novelty language?
18. Is the evidence revision distinguished from the later registry-link
    revision, and are independent-review fields still honestly unrecorded?

## 6. Required adversarial mutations

Run coherent mutations in disposable copies. A mere missing name or unused
variable warning is not substantive rejection. At minimum test:

- target certificate or checker verdict supplied in serialized input;
- post-hoc constant transformation after observing the target;
- zero-weight or foreign edge used as causal participation;
- requirement, context or authorization omitted or replaced;
- foreign action, rebuilt equal-valued effect, reconstructed successor;
- current-table-only verifier substituted for constitutive checking;
- incremental checker given the complete-check verdict or target snapshot;
- affected fragment reused, or unaffected fragment accepted without license;
- stable key changed under reindexing or version correspondence forged;
- second transition restarted from the initial state;
- bypass accepted by label while its missing dependency is ignored;
- rejected candidate installed or allowed to create an effect;
- empty/foreign future substituted for the nonempty exact continuation;
- already-forgotten memory used as the input to forgetting;
- constant projection substituted for executed forgetting;
- a future-dependent or delayed producer substituted for the executed local
  production where horizon independence is claimed.

Record exact patches, expected outcomes, actual outcomes and first substantive
diagnostics. If a mutation survives while preserving a public target clause,
that clause is not established.

## 7. Deliverables and verdict

Produce a self-contained audit directory containing:

- the complete report;
- README and exact reproduction commands;
- positive probes and expected-failure probes importing only the public root
  wherever possible;
- mutation patches and machine-readable outcomes;
- raw build, portal, axiom, reachability, stratification and hash logs;
- a table for every C1–C18, G1–G10 and RC1–RC6 obligation;
- a clause-by-clause table for the French and English canonical claims.

Use exactly one final verdict:

- `FORMAL AND CONCEPTUAL TARGET ESTABLISHED`
- `FORMAL AND CONCEPTUAL TARGET REQUIRES CORRECTIONS`
- `FORMAL AND CONCEPTUAL TARGET NOT ESTABLISHED`

The first verdict is permitted only if every mandatory target clause is
verified and every required causal substitution is substantively rejected.
Any false clause entails `NOT ESTABLISHED`. Qualifications must be stated and
cannot silently become verification. Do not make a novelty or superiority
verdict in this audit.
