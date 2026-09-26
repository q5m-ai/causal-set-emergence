# Poisson expectation bridge API

This implementation for issue #43 connects the actual finite Poisson law and
original discrete four-dimensional BDG action to the pre-existing
`continuumMean`. It transfers the existing deterministic limits without
changing their definitions or hypotheses. Tracker #1 and the main proof-status
documentation are deliberately unchanged: their updates are deferred until
these declarations merge.

## Exact expectation, before any limit

`expectedBDGAction` is defined by integration of `discreteBDGAction` against
`FinitePoisson.law` with intensity equal to density times restricted product
Lebesgue measure. It is not defined using `continuumMean`. At positive density
on a measurable finite-volume region, this is exactly the already constructed
`FiniteSprinkling.probability`, with proved total mass one and almost-sure
support and simplicity.

The main identity also exposes that probability measure directly:

```lean
theorem FiniteSprinkling.expectation_eq_continuumMean (S : FiniteSprinkling)
    (hconv : CausallyConvex S.region) :
    (∫ c, discreteBDGAction S.density c ∂S.probability) =
      continuumMean S.density S.region
```

`CausallyConvex M` means that every closed causal interval between two points
of `M` is contained in `M`. It does not assume a volume, integral, or expectation
identity. The underlying sprinkling supplies measurability, finite volume,
and positive density. Boundedness is sufficient, but the expectation identity
itself only needs finite volume.

`BoundedCausalRegion` records measurability, boundedness, and this geometric
causal-convexity condition. Its `sprinkling` constructor discharges finite
volume at every positive density. The corresponding
`BoundedCausalRegion.expectedBDGAction_eq` has no probabilistic or integrability
premise. Absolute integrability of the discrete action follows from the
existing first and second factorial moments. `integrableOn_bilocal_bdg`
independently proves absolute integrability of the actual causal-pair kernel
on every bounded region by compact domination.

## Proof decomposition

- `PoissonExpectation.lean` converts the proved nonnegative interval-layer
  Campbell–Mecke identity into a real expectation. Layer probabilities are
  jointly measurable and bounded by one; real-integral interchanges and finite
  signed sums have explicit absolute-integrability proofs.
- `integral_intervalLayer` uses the exact Poisson PMF at the rate of the
  endpoint-excluded interval **intersected with the sprinkled region**. It
  needs no causal convexity. The point term uses the first factorial moment.
- `poissonBDGMean_eq_sum` retains all kernel-side weights `1, -9, 16, -8`.
  The PMF supplies the factorial denominators and exponential, giving precisely
  the existing `bdgKernel`. The action retains the opposite pair signs
  `N - N₀ + 9 N₁ - 16 N₂ + 8 N₃` and its original density normalization.
- `TimelikeInterval.lean` derives arbitrary future-timelike interval volume
  from the existing zeroth interval moment and the checked volume-preserving
  rest-frame map. Both real and extended-real volume statements are available;
  finiteness is derived, not hidden by conversion to real numbers.
- `ExpectationGeometry.lean` proves that removing the two marked endpoints
  does not change volume. Causal convexity then removes the region restriction
  from the interval rate. A translated null cone has zero product Lebesgue
  volume, so the timelike calculation applies almost everywhere in each
  future-point integral. Null-related intermediate points are **not** deleted
  from finite order intervals, and the closed causal relation is unchanged.
- `ExpectationBridge.lean` combines those results, retains both density
  factors from two-point Mecke, and uses the original normalization algebra.
  The exact finite-density identity is established before any limit is taken.
  Empty and nonempty zero-volume regions have zero expected action without
  choosing a uniform point in a null region.

## Checked region classes and limit transfer

`GraphCapData.boundedCausalRegion` uses the existing measurability, boundedness,
and complete-slice causal-convexity results; no profile regularity beyond the
existing geometric data is needed for the exact expectation identity.
`boundedCausalRegion_nullCap` similarly uses the existing null-cap geometry.
The ellipsoids instantiate the original graph-cap data under the original axis
hypotheses.

`ExpectedLimits.lean` rewrites the expected action to `continuumMean` at every
positive density, then applies the corresponding existing deterministic
limit. Its public contracts include:

```lean
AdmissibleGraphCap.expectedBDGAction_limit
AdmissibleGraphCap.expectedBDGAction_limit_eq_angle
ellipsoid_expectedBDGAction_limit
nullCap_expectedBDGAction_limit
```

The general graph-cap target is the existing canonical reciprocal-gradient
boundary integral, equivalently its angle integral. Positive-height critical
points remain permitted. The ellipsoid limit retains unequal axes and the
original explicit value. The null-cap limit has exactly the original
`0 < a < T` hypotheses and the existing algebraic `nullJointArea` target; it
does not supply a new induced-null-joint interpretation.

These are limits **of expectations** only. No variance, concentration,
convergence in probability, almost-sure convergence, or sample-wise action
limit is asserted.

## Regression and validation

`ExpectationRegression.lean` independently expands the probability law,
normalized signed discrete action, continuum integral, and canonical surface
measure. It exercises finite-volume input, absolute integrability, every layer
coefficient, a negative kernel value, arbitrary timelike interval volume,
endpoint removal, null cones, diagonal exclusion, empty and singleton regions,
the concrete unequal-axis `48π` limit, the null-cap `3π` limit, and an admissible
quartic retaining an interior critical point.

The library root imports all four new modules. The existing checker discovers
the independent regression as well as every local Lean source, treats warnings
as errors, and runs isolated and aggregate transitive axiom audits. No new
axiom, `sorry`, `admit`, or premise equivalent to the bridge is introduced.

```sh
cd formal
./check.sh
```

The only permitted axiom dependencies remain Lean's standard `propext`,
`Classical.choice`, and `Quot.sound`. No new dependency or toolchain version is
required. Repository Python, symbolic, numerical, Markdown, and source-diff
checks remain applicable; GitHub CI does not replace the local Lean audit.
