# Conventional regular Cauchy reference and runtime realization

## Status and scope

This passage is the canonical text for the
`RUNTIME_CONVENTIONAL_REGULAR_CAUCHY_REFERENCE` claim. It fixes an autonomous
reference of regular dyadic Cauchy reals inside the repository and then proves
its relational correspondence with the already constituted numerical carrier
and runtime.

The reference includes every received function from natural precisions to
signed dyadic codes when equipped with positive regularity. It is therefore
not restricted to closed repository programs. It is not, however,
definitionally identified with `Mathlib.Real`, Dedekind cuts, or another
external construction not formalized here.

The order of primitives remains constitutive. Runtime relations, executions,
actions, memories, and limits are produced before their readouts. Names and
extensive classes defined in this passage are downstream comparisons; they
reconstruct no forgotten occurrence, history, archive, bank, journal, or
resource.

## Formal conclusion about regular names

A `RegularDyadicName` contains an approximation
`Nat -> SignedDyadicCode` and a positive regularity law. At every requested
precision, two sufficiently fine replies from the same name are related by
`Near`. `NameEquivalent` relates two names when one shared reply threshold
provides this proximity at every requested precision.

Reflexivity, symmetry, and transitivity of `NameEquivalent` are positively
constructed. Dyadic constants preserve the exact value of the received code.
Negation reads the requested precision, addition reads one extra bit, and
multiplication probes each factor at precision zero before refining the other
according to the obtained amplitude. These operations and their laws use no
carrier or runtime.

`NameOrder` and `NameApartness` carry positive oriented margins. Order
transport explicitly aligns seven directed bounds: three fine links on each
side and the central link. Inversion receives a positive apartness-from-zero
witness. Dyadic density and natural bounds produce their codes and integers
from the finite replies actually read.

The `regularOrderedCompletion` packet closes constructive ordered-field laws,
density, and bounds on regular names. It concretely realizes the
`PresentedDyadicOrderedFieldCompletion` contract without a terminal runtime or
extensive-class hypothesis.

## Produced completion

A `RegularPresentedFamily` receives its names, a monotone outer modulus, and
its Cauchy law. Its limit is not supplied as a candidate:
`regularLimitResult family` produces `diagonalName family`, which reads the
term selected by the modulus at the requested precision. The same produced
name then supplies convergence and positive uniqueness.

`regularPresentedCompletion.complete` reuses exactly this producer.
`conventionalCompletionObject` is therefore a concrete realization of the
presented-dyadic-completion contract whose carrier is exactly
`RegularDyadicName`, whose equivalence is exactly `NameEquivalent`, and whose
own modulus is the identity.

An `ExternalPresentedFamily` adds an explicit member name to each extensive
term. `referenceFamily` copies these names, the modulus, and the same Cauchy
law. `externalComplete` invokes regular completion once and uses the same
produced name for the result class, its convergence, and its uniqueness. It
does not complete a bare `Nat -> Value` function lacking member names and a
modulus.

## Extensive classes without a selected representative

An `ExtensiveCauchyReal.Value` is a `Contains` relation on names, saturated by
`NameEquivalent` and coherent: two member names are positively equivalent.
Its inhabitance is hidden under `Nonempty`. No field selects a representative
in `Type`.

`classOf name` constructs the exact class of a name. `ExternalEquivalent`
positively transports membership in both directions; it does not identify the
`Contains` predicates by equality. `classOf` preserves and reflects
`NameEquivalent`, and every value is propositionally equivalent to a class
constructed in this way.

`ConventionalRegularCauchyReference` has exactly
`Carrier := RegularDyadicName` and `Equivalent := NameEquivalent`.
`ReferenceRealizes name value` is exactly `value.Contains name`.
`referenceCoverage` constructively covers every name, whereas
`valueReferenceCoverage` covers every value only under `Nonempty`. The latter
direction cannot be eliminated into a function selecting a name.

`ClassDescent` supplies the relational universal property of this quotient
specification: every name map respecting `NameEquivalent` descends to a total,
stable graph that is single-valued up to target equivalence. Exactness on
`classOf` and uniqueness are proved without a representative function.

Extensive operations are constructed directly from member names and their
membership witnesses. Complete positive laws remain on names. On a bare
`Value`, equivalence, order, apartness, inversion, density, bounds, and
algebraic laws are explicit propositional readouts. No `Nonempty` is
eliminated to manufacture positive data in `Type`.

## Universal property of completion

The universal quotient property above is distinct from the universal
completion property. A `RelationalCompletionMorphism Target` stores only a
`CompletionMorphism conventionalCompletionObject Target`. Its graph on
classes is definitionally the relational descent of this pullback map.

For every other `Target : PresentedDyadicCompletionObject`, target
completeness constructs `relationalCompletionComparison Target`. Uniqueness of
two such morphisms is derived from coherence of member names, preservation of
`NameEquivalent`, and the already proved uniqueness of completion morphisms.
Dyadic constants and produced limits are transported by this same graph; no
independent graph is assumed.

`quotientRecognition` and `completionRecognition` respectively assemble the
quotient specification and the ordered Archimedean relational completion.
Completion recognition consumes `regularPresentedCompletion`,
`regularOrderedCompletion`, the setoid readout, and the constructed morphisms.
It does not receive its conclusion as a field of an external interface.

## Carrier-to-class correspondence

For every perimetral presentation `P` and depth `baseDepth`,
`regularCharacterization P baseDepth` instantiates the preceding gate's
relative characterization with `regularOrderedCompletion`. It constructs the
maps

```text
carrierToReferenceName : EffectiveCauchyReal.Carrier -> RegularDyadicName
referenceNameToCarrier : RegularDyadicName -> EffectiveCauchyReal.Carrier
```

and their returns up to positive equivalence. These maps and their laws for
constants, operations, order, apartness, inversion, density, bounds, and
limits are derived results of presented completion and uniqueness.

`Realizes carrier value` is exactly
`ClassDescent referenceNameToCarrier value carrier`. Every realization proof
therefore carries its member name, its class membership, and its agreement
with the carrier. `carrierCoverage` associates every carrier with the class of
the name obtained by the forward map and consumes the proved return.
`relationalCoverage` covers every value in the other direction only under
`Nonempty`.

Correctness shows that equivalent carriers realize `ExternalEquivalent`
values. Faithfulness shows that realizations of externally equivalent values
have equivalent carriers. Transports and their reflections reuse the same
relative characterization: no second operation or relation is reconstructed.

For families and limits, `carrierExternalFamily` retains the terms, modulus,
and names produced by `carrierCoverage`. Two already produced completion
packets are compared through convergence of the external candidate and carrier
uniqueness. The reverse route uses the explicit diagonal transport of the
relative characterization; these two families and their moduli are not
silently identified.

## Runtime realization

`RuntimeRealizes runtime value` is exactly
`Realizes (toCarrier runtime) value`. Thus `runtimeCoverage` gives every
runtime a downstream value that it realizes. `valueRuntimeCoverage` starts
from relational coverage of a value, constructs `ofCarrier` only inside
`Nonempty`, and transports agreement through `carrier_roundtrip`. No
`Value -> Real P baseDepth` function is obtained.

For every explicitly received regular name,
`runtimeOfReferenceName P baseDepth name` instead applies
`referenceNameToCarrier` and then `ofCarrier`. This construction is executable
because the name, rather than a bare class, is a declared input.
`runtimeOfReferenceNameRealizes` proves that this runtime realizes
`classOf name`. This backward map is a downstream comparison route; it does
not become the origin of native runtime producers and recovers no erased
history.

Runtime transports for operations, order, apartness, inversion, density, and
bounds pass through the already established readout theorems and then through
carrier correspondence. Density and bound transports consume the received
rich packets and retain their exact codes or integers. Limit transport
consumes `carrierProduced.native.limit` and the `limitExact` equality of the
same packet; it manufactures no second runtime limit.

## Exact verdict and non-conclusions

`recognizesConventionalCauchyReference P baseDepth` gathers the four
constructed packets: `QuotientRecognition`, `CompletionRecognition`,
`CarrierValueCorrespondence`, and `RuntimeValueCorrespondence`. It establishes
correspondence with every element of the regular Cauchy reference fixed in
this passage, including every received regular name, rather than only the
previously closed effective terms.

The constructive direction concerns explicitly received names and carriers.
The direction starting from a bare extensive class remains relational and
propositionally truncated. Round trips identify neither functions,
occurrences, rich families, programs, memories, nor proofs.

This result proves no identity with `Mathlib.Real`, Dedekind cuts, or any other
model not formalized in the repository. It proves neither least-upper-bound
completeness, globally decidable order, representative choice, nor enumeration
of all reals by a finite program. No conclusion about `AC`, `CH`, physical
cost, or originality follows from this claim.
