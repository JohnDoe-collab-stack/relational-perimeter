# Runtime–effective-Cauchy-real correspondence

## Status and scope

This is the canonical passage for the
`RUNTIME_EFFECTIVE_CAUCHY_REAL_CORRESPONDENCE` claim. It states a constructive
structural correspondence between runtime behaviors, effective dyadic
presentations, and effective Cauchy carriers. The correspondence includes the
operations and relations actually constructed on the relational carrier, as
well as its Cauchy families and their limits. It is neither an independent
audit, an identification of rich histories, nor a construction of all
classical real numbers.

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

Above this numerical connection, `effectiveCorrespondence P baseDepth`
constructs the structural correspondence for the closed runtime carrier:
applications and round trips, constants, addition, negation, multiplication,
inversion under apartness from zero, constructive order, density and finite
bounds, source and native Cauchy families, limits, effective completeness, and
numerical uniqueness. Its six blocks are filled by repository producers and
theorems; their conclusion is not assumed by the constructor. Transports to
presentations and carriers remain downstream readouts and do not identify the
forgotten rich data.

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

## Effective structural correspondence

The closed carrier `RelationalRealAddition.Real P baseDepth` is constituted by
the five constructors `leaf`, `add`, `neg`, `mul`, and `certified`. Its objects
remain executable behaviors: their rich environments retain archives,
productions, actions, and occurrences, and their live environments then
project exactly the memory required by the fixed future contract.
`toPresentation` and `toCarrier` are downstream readouts; they form none of
these objects.

`effectiveCorrespondence P baseDepth` constructs, without a terminal
assumption, an `EffectiveCorrespondence` package with six blocks.
`ApplicationMaps` provides maps to and from presentations and carriers, their
round trips up to `Equivalent` and `NumericalFutureEquivalent`, and preservation
and reflection of numerical equivalence. These round trips are never
equalities of occurrences or rich families.

`OperationTransports` connects dyadic constants, zero, one, addition,
negation, and multiplication to the corresponding presentation and carrier
operations. Inversion remains partial: its formation requires a positive
`Apartness` witness from zero, kept separate from the action that produces the
inverse. Each relational operation is executed first from the current archives
of its arguments; its readout is transported only afterwards. No numerical
operation is imported back to manufacture the runtime retroactively.

`RelationTransports` preserves strict order and apartness and reflects them on
the images of the applications by executing fresh comparisons from the
received archives. Order is not made globally decidable. The laws in
`ConstructiveOrderedFieldLaws` and `ConstructiveOrderedFieldFutureLaws` include
the additive group, multiplicative laws, positivity of one, constructive order
laws, compatibility with addition and positive multiplication, and the two
inverse laws under their explicit domain. Their conclusions are readout and
future equivalences, never identities of occurrence trees.

`OrderAndFiniteWitnesses` also retains the producers of dyadic density and
natural bounds. They receive order witnesses and current archives, execute
their probes and actions, and then project the orders of the same produced
targets to presentations and carriers. These are constructed finite witnesses,
not an invocation of order completeness.

## Executed families, grouping, and native limits

`FamilyCorrespondence` distinguishes source `ExecutedCauchyFamily` objects,
numerical `EffectiveFamily` objects, carrier families, and
`NativeCauchyFamily` objects whose terms are themselves behaviors of the
closed carrier. Source transports retain the declared producer and modulus and
establish termwise equivalences; they do not recover forgotten histories or
Cauchy witnesses from their codes.

For a native family, every term's live kernel and its connection to the rich
step are supplied separately. At every request, limit production starts from
the current archive bank, executes the diagonal term selected by the modulus,
has grouping consume that same `Step`, installs the produced target, and
continues the journal. The next bank replaces only the entry actually visited.
The live projection retains the installed code; it does not execute the rich
production again.

`nativeCompleteness` constructs the authoritative candidate, its convergence,
the effective readout, correspondence with the produced limit of the realized
family, and reuse of the installed target. `nativeUnique` compares two received
candidates of the same family through a mediation that produces one term step
and shares it between the two convergence laws. Its conclusion is
`Equivalent` together with `NumericalFutureEquivalent`; it cannot identify the
candidates' constructors, archives, or occurrences.

`LimitCorrespondence` separately retains preservation of a limit to its
readout, reflection and realization, the route from a returned source family,
carrier limits, numerical uniqueness, and the rich trace whose projection
gives numerical futures. The proof consumes the received term and candidate
steps; neither a prefabricated target nor a naked code can replace them.

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

The correspondence covers the closed relational carrier constructed in the
repository and the effective dyadic presentations and effective Cauchy
carriers or families supplied by the received data. Within that scope it
establishes the structural transports, executed dyadic density, natural
bounds, and effective Cauchy completeness described above.

It does not cover all classical real numbers and does not prove least-upper-
bound completeness. It does not identify families, programs, archives,
journals, Cauchy witnesses, or occurrences that have the same readouts. Memory
minimality always remains relative to a fixed environment and future contract;
it is neither a physical-cost bound nor a universal certification of callback
captures. Finally, no conclusion about `AC`, `CH`, or originality follows from
this correspondence.
