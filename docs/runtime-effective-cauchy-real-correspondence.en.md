# Runtime–effective-Cauchy-real correspondence

## Status and scope

This is the canonical passage for the
`RUNTIME_EFFECTIVE_CAUCHY_REAL_CORRESPONDENCE` claim. It states a constructive
correspondence between runtime behaviors, effective dyadic presentations, and
effective Cauchy carriers. It is neither an independent audit, an
identification of rich histories, nor a construction of all classical real
numbers.

## Formal runtime–effective-real correspondence conclusion

`EffectiveDyadicPresentation` receives a computable function
`approximation : Nat -> SignedDyadicCode` and a positive coherence law for any
two precisions refining a common precision.
`presentationToRuntime P baseDepth presentation` constructs an
`ExecutedCauchyFamily P baseDepth` whose producer computes the approximation at
the requested precision and whose modulus is the identity, and then constructs
its authoritative `RuntimeReal`.

Conversely, `runtimeToPresentation real` obtains every approximation by
executing the canonical limit step from the runtime's initial state and reading
the response owned by that step. At every precision,
`RuntimeReal.ReadoutOrigin` retains the produced step, its equality with the
canonical step, and the exact equality between its stored readout and the
exposed readout.

The presentation round trip is exact at every precision by
`presentation_roundtrip_readout_exact`. The runtime round trip is a
`RuntimeReadoutEquivalent`. `runtimeReadoutCorrespondence` makes this numerical
equivalence interderivable with positive equivalence of the readout
presentations. None of these constructions implies equality of rich states,
journals, resources, programs, or occurrences.

## Actually retained limit futures

A `LimitQuery` separates comparison accuracy from response precisions chosen
beyond the threshold. `RuntimeReadoutEquivalent.toLimitFuture` executes the
corresponding limit-request lists through `run` and constructs a
`PairedLimitTrace` over the two traces actually retained. Every step keeps both
`ExecutedStep`s, equality of their starting depths, and the `Near` relation
between their readouts; terminal-depth equality is derived from those same
steps. `LimitFutureEquivalent.toReadouts` recovers the numerical law from a
singleton trace. Readout equivalence and finite limit-future equivalence are
therefore interderivable without identifying rich steps.

The common runtime supplies a complementary cross-environment connection.
`CommonRealRuntime.NumericalFutureEquivalent` pairs limit transitions actually
executed by `performReal` from arbitrary memories in two environments.
`numericalFutureCorrespondence` identifies it exactly with
`RuntimeReadoutEquivalent` only at numerical level. The environment — producer
and modulus — remains runtime data; this relation never becomes exact
`FutureEquivalent` between different programs.

## External effective carrier

`EffectiveCauchyReal.Carrier` contains an executable signed-dyadic sequence, an
explicit modulus, positive monotonicity of that modulus, and a Cauchy law.
`toPresentation` diagonalizes the sequence through its modulus;
`ofPresentation` constructs the canonical identity-modulus carrier. Both
directions and their round trips are related by
`EffectiveCauchyReal.Equivalent`, without quotients or classical choice.

`fromRuntime` reads a carrier from the runtime's downstream presentation.
`toRuntime` constructs a runtime from the received carrier.
`runtimeCarrierCorrespondence` makes runtime readout equivalence interderivable
with equivalence of the carriers read this way, and
`carrier_runtime_roundtrip_equivalent` proves the round trip of a received
carrier. A converse reconstruction of runtime history from numerical values
alone is neither defined nor claimed.

## Connection to the Gödel perimeter

For every `ExecutedGodelProduction`, `realizePresentation` and
`realizeCarrier` place these constructions on exactly
`godelPerimetralPresentation execution` at historical base `H1`. The package
jointly contains the Gödel raccord, positive runtime, numerical correspondence,
retained limit futures, and readout provenance. The equalities
`godelInitialIsRuntimeInitial`, `godelProducedRealIsRuntimeProduced`, and
`godelFirstStepIsRuntimeStep` prevent an independent second execution from
being juxtaposed with the Gödel package.

The Heyting-arithmetic instance concretely closes the Gödel parameters. The
numerical presentation or carrier remains a received input: Gödel truth and
non-provability reject total closure but compute no approximation.

## Non-conclusions

The correspondence covers exactly dyadic presentations and Cauchy reals
effectively presented by the received data. It does not cover all classical
reals. It does not prove transport of addition, multiplication, order, or
apartness, density, the Archimedean property, order completeness, `AC`, or
`CH`. Those properties require separate constructions and claims.
