# Erratum F5 for the historical v10 comparison

V10 is preserved exactly as executed at commit
`cb8d9e17b7b9db60c057d1617f1d56321e03ee3c`.  Its recorded rows and hashes
remain historical evidence and are not rewritten.

The v10 statement that its explicit reference combination did not call the
compared constitutive runtime was incorrect.  The two pre-effect decisions
were obtained transitively through `submitUpdate`.  Several other row fields
were printed as literal consequences of Lean proofs rather than recomputed IO
observations.  The run remains reproducible, but those two facts prevent it
from establishing the claimed comparator independence and observation
boundary.

The successor protocol v13 corrects both defects in new code: its reference
decision consumes only independently computed elementary observations, a
generated-code gate rejects every transitive path to compared checker
verdicts, and proof-only consequences are kept in a separate evidence ledger.
V13 has no confirmatory result while its protocol status remains a draft.
