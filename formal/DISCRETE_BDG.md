# Discrete four-dimensional BDG action

This is the finite-action API for issue #42, built on the constructed
[finite Poisson infrastructure](FINITE_POISSON.md). It defines a random
finite-order observable and proves its measurability and absolute
integrability. It does **not** identify its expectation with `continuumMean`;
that bridge remains issue #43. No deterministic definition or theorem
hypothesis is changed. Tracker and main proof-status updates remain separate
until merge.

## Finite order and counting conventions

`CausalPoint c` is a new finite type of locations in the support of a
configuration. Its `PartialOrder` instance is the existing Minkowski causal
relation, not the coordinatewise order on `Spacetime`. Reflexivity,
transitivity, and antisymmetry are proved. On a simple configuration,
`CausalPoint.card_eq` identifies its cardinality with `c.card`.

`CausalPoint.mem_interval_iff` identifies the existing endpoint-excluded
`causalIntervalInterior` with the strict interval of this partial order.
Null-related intermediate points remain included. `configurationInterval`
is its intersection with the finite support; `intervalCount_eq_card` proves
that the existing measurable count is its cardinality when `c.Nodup`.

`intervalLayer k c` counts strictly causal ordered pairs with exactly `k`
interior points. Thus layer zero counts links, and an interval in layer `k`
has `k + 2` elements including its endpoints. `causalLayerPairs` is the
corresponding finite set of pairs, and `intervalLayer_eq_card` proves equality
with its cardinality on simple configurations.

As in the Poisson infrastructure, the observable is defined on all multisets.
Counts retain multiplicities away from the simple configurations, but there
are no strictly causal self-pairs even at coincident locations. The proved
`FiniteSprinkling.ae_nodup` and `ae_supported` laws justify the almost-sure
identification with a genuine finite causal set in the region, recorded in
`FiniteSprinkling.ae_discreteBDGAction_eq_finite_order`. Finite-tuple permutation
invariance is also proved; no enumeration is physical input.

## Coefficients and normalization

The definition uses only point cardinality and four natural layer counts:

```lean
def discreteBDGAction (ρ : ℝ) (c : Multiset Spacetime) : ℝ :=
  bdgNormalization ρ * ((c.card : ℝ) - intervalLayer 0 c +
    9 * intervalLayer 1 c - 16 * intervalLayer 2 c + 8 * intervalLayer 3 c)
```

`bdgNormalization ρ` is `4 / (Real.sqrt 6 * Real.sqrt ρ)`. The action is
normalized as the physical action multiplied by Planck length squared and
divided by reduced Planck's constant, with density the inverse fourth power
of the discreteness length. Positive density comes from `FiniteSprinkling`.
The definition is total at other real densities, but no physical claim is
made there.

`bdgLayerWeight` has kernel-side weights `1, -9, 16, -8` at counts zero
through three, and zero above three. The action subtracts this weighted pair
sum. `bdgLayerWeight_polynomial` verifies that the exponential generating
polynomial, with factorial denominators, is exactly the existing
`bdgPolynomial`; `bdgLayerWeight_kernel` verifies the finite Poisson-weighted
sum against `bdgKernel`. In particular the quadratic layer coefficient is
`16`, not `8`, and the cubic layer coefficient is `-8`, not `-4/3`.

`bdgNormalization_mul_density` proves that multiplying this normalization
by one factor of density gives `(4 / Real.sqrt 6) * Real.sqrt ρ`, the
existing deterministic prefactor. These are algebraic compatibility checks,
not an expectation theorem.

## Finite rearrangements and integrability

- `intervalCount_erase_left` and `intervalCount_erase_right` prove that
  removing either endpoint leaves its interval count unchanged, including
  on configurations with multiplicities.
- `intervalPairSum_eq_sum` rewrites the reduced pair sum as the full finite
  double sum with zero diagonal, counting interiors in the original sample.
- `intervalPairSum_bdgLayerWeight` regroups that sum into the four layers.
- `discreteBDGAction_eq_pairSum` and `discreteBDGAction_eq_point_pair` expose
  the point and reduced-pair terms required by Campbell–Mecke.
- `discreteBDGAction_eq_sum` gives the unreduced double-sum version, while
  `discreteBDGAction_eq_finite_order` identifies the actual support and pair
  cardinalities on simple samples.

`measurable_intervalLayer` and `measurable_discreteBDGAction` use joint
measurability on every finite tuple stratum. `integrable_intervalLayer` and
`integrable_discreteBDGAction` derive absolute integrability from the Poisson
first and second factorial moments and the uniform absolute weight bound
`16`. `abs_discreteBDGAction_le` supplies an explicit cardinality-quadratic
bound. No integrability or expectation identity is assumed, and there is no
uniform upper bound on the random number of points. Finite volume suffices;
bounded measurable regions are included, but causal convexity is not needed
at this stage.

## Regressions and validation

`DiscreteBDGRegression.lean` independently checks:

- the empty sample, singleton, and a three-point spacelike antichain;
- all four layers of a five-point chain, and the zero weight of the additional
  layer in a six-point chain;
- a null-sided diamond with four links and a two-interior-point pair, whose
  action is negative;
- inverse-square-root density scaling, coincident locations without
  self-pairs, almost-sure simplicity, and null-volume regions;
- the induced non-coordinatewise partial order, order-interval semantics,
  natural finite-pair cardinalities, and permutation invariance;
- the independently restated reduced-pair action formula, measurability,
  and integrability.

The library root imports both new modules. The regression source is discovered
independently by the existing validation command:

```sh
cd formal
./check.sh
```

This checks every local Lean source with warnings as errors, isolated
public-declaration axiom audits, and the aggregate library audit. Only the
standard Lean foundations are permitted. The final expectation identity,
transfer of deterministic limits to expectations, variance, and sample-wise
convergence remain outside this implementation.
