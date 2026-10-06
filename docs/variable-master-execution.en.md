# Variable decomposition in the master execution

The computation can now retain one or two branches depending on the generated
contexts it receives. A partition is not an input to this execution path.
This extends the master executor without replacing the audited width-one
result or the binary theorem about `carry`.

## Actual chain

`VariableMasterExecution` reuses the existing resource producers:

1. `masterHead` materializes the four existing master producers in order:
   discovery, application, decomposition and assembly. The resulting supports
   are shared by reads and by cursor continuation.
2. Opening reads the head's discovered variable and the received generated SAT
   contexts. Freshness is checked; an already decided variable does not create
   a spurious new formation.
3. Flip-relation search examines the opened frontier. Every absorption uses a
   total action and separate SAT-preservation evidence. Unresolved search
   retains the relevant branches.
4. The actual retained frontier feeds the next step. The next cursor comes
   from the same master support without executing its head again.

Typed references distinguish the cursor, received frontier, produced head,
opening and reduction. `History` indexes its tail by the cursor and frontier
actually produced. No future tail is passed to head construction.

`step` materializes its five producers in the same body, then reads their
shared outputs. `scripts/check-variable-master-codegen.py`, included in both
verifiers, checks the generated C applications of the master head, its
discovery, opening and normalization. It rejects support reconstruction through
the old helpers on this path. This checks these named applications, not total
cost or heap size.

`execute_erases` proves agreement with `MasterResources.execute` for every
step count. `execute_viable_iff` composes SAT-preserving transports throughout
the chain. The four foundational files are unchanged.

## Constructed variation

`VariableMasterInstance` fixes the same initial public master, formula
`x10 ∨ x1 ∨ x2`, selected variable `x10`, and SAT criterion. The parents have
equal depth; their histories fixed `x1` to true or false. Every one of the four
children has an accepted continuation.

- After `x1 = true`, the searched flip relation is reconstructed and retained
  width is one.
- After `x1 = false`, this finder finds neither direction between the children
  and retained width is two.

The widths are proved about `step`, hence about producer outputs, not a list
supplied as an expected answer. The variable is proved equal to that of the
executed role. No grouping mask or mode is supplied. The parents are legitimate
constituted inputs to the extension; they are not claimed to be two outputs of
the canonical run itself.

## Future distinctions under a fixed contract

`VariableMasterFutures` declares one contract: arbitrarily repeated reads of
`x10` after the actually produced action. It does not promise search restarts
or inspection of the original assignment.

The grouped pair has identical futures under this contract. In the unresolved
case, a read positively separates the pair. `every_exact_realization_distinguishes`
requires every exact realization to preserve that distinguishability without
prescribing a memory encoding. This does not characterize every distinction
of a runtime with restart, pulse, or other interaction.

`exact_future_fibres` characterizes equality of reduced states by equivalence
of all futures, for every source of this contract. `covers_read_values`
constructs a source for each of the two reduced values. The original grouped
sources remain provably distinct: reduction eliminates a distinction that
is unnecessary for this contract, without asserting equality of the sources.

## Scope

Finder failure does not prove that no other useful relation exists. The
preserved criterion is SAT, not identity of all assignments. The read contract
differs from the project's restart contracts. This normalizer traverses an
explicit frontier: no general non-extensive cost bound, unpredictability, or
efficient solution of arbitrary SAT is claimed.

The package already sent for audit remains unchanged. This extension requires
its own independent audit before being described as independently validated.

## Reproducible local verification

With Lake and Python 3 available (or `RELATIONAL_PERIMETER_PYTHON` set), run
`pwsh -File scripts/check-variable-master.ps1` from the directory.
The script fingerprints its inputs before clean builds, runs the Windows
verifier and compares the final fingerprints. Proofs, examples and compiled
code checks are verified together. Logs are created in a new sibling directory,
outside the sources, without overwriting earlier results. This protocol is
neither a benchmark nor an independent audit.
