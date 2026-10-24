# Causal complete-property scaling v12 — confirmatory analysis

## Frozen revision and execution

- Frozen source: `090820d4786d68787f730c5e77cc91220a8075de`.
- Frozen protocol: `9bdfa304f0f54a2cac6b0295937c171d11e6609d`.
- Recorded result: `dd220c4e65647c07ae058580ecbc9622d8f1812e`.
- Protocol identifier: `compiled-causal-complete-property-scaling-v12`.

The campaign executed the same compiled complete-property checker and its
independent complete recheck at sizes 0, 4, 8, 16 and 32. Trace lengths were
respectively 3, 6, 9, 12 and 15. All five preregistered repetitions at every
size were accepted, for 25 accepted repetitions in total. The negative control
was rejected. The validator passed its eleven mutation self-tests.

## Structural observations

The measured structures grow with the declared size. From size 0 to 32, the
number of neural nodes grows from 2 to 34, the profile width from 4 to 36, the
causal graph from 17 nodes and 21 edges to 49 nodes and 117 edges, and the
complete obligations from 35--37 to 163--177 over the corresponding traces.

The checker performs real fragment reuse. At the first local transition it
transports 2, 6, 10, 18 and 34 fragments at the five sizes while recomputing
two. Extended transitions expose the opposite regime: at size 32 the last
transition transports one fragment and recomputes 35. The published costs
therefore distinguish local and extended affected cones instead of reporting a
selection counter as a speedup.

## Preregistered practical criterion

The practical-gain criterion is false. Median cumulative incremental time
divided by median cumulative complete-recheck time is:

| size | trace length | accepted repetitions | incremental/full median ratio |
| ---: | -----------: | -------------------: | ----------------------------: |
| 0 | 3 | 5 | 3.865 |
| 4 | 6 | 5 | 11.649 |
| 8 | 9 | 5 | 31.859 |
| 16 | 12 | 5 | 121.814 |
| 32 | 15 | 5 | 760.445 |

At size 32, median cumulative time is 3,175,844,800 ns for the incremental
checker and 4,176,300 ns for the complete recheck. The campaign therefore
establishes no time or memory gain for this implementation. P8 is evaluated,
but the practical part of P8/S6 is unfavorable.

## Interpretation boundary

The campaign is an observational result, not a Lean theorem or an asymptotic
complexity bound. It does not negate the formal transport, recomputation,
acceptance-equivalence or causal-chain theorems. It shows that this current
incremental implementation does more measured work than the independent full
recheck on the frozen family, even though it genuinely transports fragments.

