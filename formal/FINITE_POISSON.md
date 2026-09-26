# Finite Poisson API

This is the finite-volume probability infrastructure for issue #41. It does
not define a BDG action, identify an action expectation with `continuumMean`,
or assert sample-wise convergence. Existing deterministic definitions and
theorem contracts are unchanged. Tracker and main proof-status updates remain
separate from this implementation PR.

## Construction and conventions

- `FiniteConfiguration.ofTuple` forgets the enumeration of a finite tuple,
  retaining multiplicities in a `Multiset`. Its permutation invariance is
  proved. The measurable space on multisets is the final sigma algebra of all
  these finite-tuple presentations.
- `FinitePoisson.law μ` is an actual measure: the countable sum of the
  finite product intensity measures, pushed to multisets and multiplied by
  their exponential/factorial Janossy coefficients. Its mass-one theorem uses
  the pinned mathlib `poissonPMF`, not an assumed point-process theorem.
- All probability results require `IsFiniteMeasure μ`. The construction does
  not divide by the region's volume. Empty and null-volume regions therefore
  require no exceptional choice of a sampled location.
- Counts include multiplicities. `pointSum` removes exactly one selected
  occurrence; `pairSum` sums ordered pairs of distinct occurrences and removes
  both. The second factorial moment excludes the diagonal. Atomic intensity
  measures remain legitimate inputs, but need not produce simple samples.
- `ae_nodup` proves almost-sure simplicity from atomlessness and a measurable
  diagonal. `FiniteSprinkling` discharges these hypotheses for its restricted
  product Lebesgue intensity; it also proves almost-sure support in the region.
  Each configuration is finite by its type, not merely almost surely finite.

## Measurability and integration

`JointMeasurable F` states joint measurability in parameters and tuple
coordinates on **every** finite stratum. This is an explicit measurable-test
hypothesis, not an integration identity or a presumed product/quotient
interchange. Counts for measurably parameterised subsets satisfy it; in
particular the two endpoints of an interval may vary.

The main generic contracts are:

```lean
FiniteConfiguration.measurable_count
FiniteConfiguration.measurable_pointSum
FiniteConfiguration.measurable_pairSum
FinitePoisson.count_probability
FinitePoisson.map_count
FinitePoisson.joint_count_probability
FinitePoisson.lintegral_pointSum
FinitePoisson.lintegral_pairSum
```

The two reduced Campbell–Mecke identities allow the test function to depend
on the **whole remaining configuration**. An unmarked factorial-moment formula
alone would not suffice for the later interval-layer expectation. The proofs
split finite product measures at the selected coordinate, then cancel the
factorial and interchange nonnegative sums and integrals by Tonelli.

The count law is derived separately: product measures give the void
probability, reduced Mecke gives the count recursion, and induction recovers
the Poisson PMF. For two disjoint measurable pieces the joint mass function is
the product of the respective Poisson mass functions, including zero rates.

`lintegral_card` and `lintegral_pairCard` prove the first two factorial moments.
`integrable_pointSum` and `integrable_pairSum` use them to prove absolute
integrability for bounded signed residual observables. `integral_pairSum`
provides signed integration as a difference of positive- and negative-part
Mecke integrals, with an explicit bound hypothesis. The nonnegative Mecke
identities themselves require no boundedness or integrability assumption.

## Spacetime interface

`FiniteSprinkling` has only four geometric/density inputs: a region, its
measurability, finite volume, and a positive real density. Its intensity is
density times restricted spacetime product Lebesgue measure. Its probability
measure and its laws are derived, not structure fields.

`causalIntervalInterior x y` is the existing **closed causal interval with its
two endpoints removed**. This is an order-theoretic interior, not a silent
replacement by the chronological interval. Null-related intermediate points
are retained. Reinserting either marked endpoint leaves `intervalCount`
unchanged, including when the configuration has multiplicities.

`intervalCount_probability` gives the exact Poisson law. `intensity_apply`
and `intensity_toReal` identify its rate with density times the volume of the
interval's intersection with the sprinkled region. No causal-convexity premise
is needed here, and unrestricted interval volume is not substituted by fiat.

`intervalPairSum` sums any function of the interior count over ordered
strictly causal pairs. It is measurable for natural, real, and extended
nonnegative weights. `lintegral_intervalLayer` combines reduced two-point Mecke
and the subset count law into the exact bilocal Poisson-PMF formula for any
layer. `integrable_intervalPairSum` handles bounded signed weights.

The later action/expectation work must still supply the actual BDG coefficients
and normalization, the appropriate causal-convexity and interval-volume
identifications, and the bridge to the unchanged `continuumMean`.

## Validation

The library root imports `SpacetimeSprinkling`, which imports all seven new
probability/configuration modules. `PoissonRegression.lean` is independently
discovered by `check.sh`, including its isolated public-declaration audit.
Regressions cover empty regions and subsets, disjoint pieces, enumeration
invariance, multiplicities, absence of self-pairs, factorial moments, negative
signed sums, interval endpoints and null-related intermediate points, joint
measurability, and exact layer averaging.

With the pinned Lean toolchain and existing dependency cache installed:

```sh
cd formal
lake exe cache get Mathlib.Probability.Distributions.Poisson \
  Mathlib.MeasureTheory.Integral.Pi Mathlib.Data.List.FinRange
./check.sh
```

The checks recompile every local source with warnings as errors and run both
isolated and aggregate transitive axiom audits. Only the usual Lean foundations
are permitted; no custom probability axiom is allowed.
