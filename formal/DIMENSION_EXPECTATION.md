# Dimension-indexed discrete action and exact Poisson expectation (#77)

This is the **finite-density bridge** for the isolated, unsmeared, minimal-layer
BDG action in every integer physical dimension at least two. It does not prove
a global higher-dimensional boundary limit. The generic probability law and
Mecke identities, the [published kernel coefficients](../notes/dimension-kernels.md),
and [actual Minkowski interval geometry](DIMENSION_INTERVALS.md) are reused.
The original 4D and conformal APIs are unchanged.

## Independent definitions and supported dimensions

`DimensionSpacetime n` has one time and `n` Euclidean spatial coordinates.
Physical dimension is `d = n + 1`; the Minkowski expectation theorem requires
`0 < n`, hence `d >= 2`. This is a quantified theorem, not extrapolation from
low-dimensional tests. Some finite combinatorial identities also make sense
outside this physical range; they do not assert a dimension-one physical model.

`MeasuredOrder` packages only a partial order and measurability of its relation.
It has no measure, interval-volume law, expectation, jet, cancellation or limit
field. `dimensionMeasuredOrder` instantiates it with the closed causal order,
not the coordinatewise product order and not chronology.

The following is literal code notation for the independent discrete definition:

```text
m = dimensionFactorCount d = d / 2 + 1       -- natural-number division
C(d,k) = k! * (dimensionPolynomial d).coeff k
N_k(c) = number of ordered distinct related pairs with k exclusive interior points
A_disc(O,d,rho,c) = rho^(2/d - 1) *
  [dimensionPointCoefficient(d) * N(c)
   - dimensionPairCoefficient(d) * sum_{k=0..m} C(d,k) * N_k(c)]
```

`dimensionLayerWeight` uses the polynomial recurrence already derived from the
published Euler operator in #71, not a new normalization chosen from a desired
expectation. `dimensionPolynomialStage_natDegree_le` proves finite support;
`dimensionLayerWeight_zero` proves that higher layers vanish.
`dimensionLayerWeight_kernel` proves the exponential generating identity with
the **factorial denominators in the Poisson probabilities**, not in the layer
counts. For example, the 4D layer coefficient at index two is `16`, while the
polynomial coefficient is `8`. The 3D weights are `1, -27/8, 9/4`, not the 4D
weights.

`discreteDimensionAction` uses only cardinality and these finite layers.
`MeasuredOrder.Point` equips the finite support with the supplied partial order;
`Point.mem_interval_iff` identifies the endpoint-excluded interval with its
strict order interval. `layer_eq_card` and
`discreteDimensionAction_eq_finite_order` identify the multiset observable with
the actual support cardinalities on simple configurations. Removing or
reinserting endpoints does not change their exclusive count, even with
multiplicities. Null-related interior points are retained. Relabelling a tuple
does not change the observable.

## Probability and integrability before averaging

`DimensionSprinkling` assumes only a measurable finite-volume region and a
positive density. Its intensity is density times restricted canonical volume;
its probability is exactly `FinitePoisson.law intensity`, not a supplied field
or an integral-defined surrogate.

Joint count measurability follows from `FiniteConfiguration.jointMeasurable_count`
and joint measurability of the order interval. Measurable reduced pair sums give
measurable layers, and finite sums give a measurable action. The first Poisson
factorial moment integrates cardinality. The second factorial moment integrates
every layer, whose indicator is bounded by one on ordered distinct occurrences.
Consequently every finite signed layer combination is **absolutely integrable**,
without bounding the random configuration's cardinality.

`ae_supported`, `ae_nodup`, and `ae_action_eq_finite_order` derive support,
simplicity and the genuine finite-order action interpretation for the constructed
law. A zero-volume region has an empty sample almost surely, even if the region
is nonempty.

## First bridge: arbitrary finite measured orders

`MeasuredOrderPoisson.lean` has no Minkowski or dimension dependency. Its
`integral_layer` derives each layer expectation by reduced two-point Mecke and
the existing Poisson subset-count law. The interval rate is the **actual
intensity measure of the exclusive interval**. The two selected endpoints do
not enter that count. Atomic measures are allowed here; the distinct-location
pair mask is retained.

`DimensionMeasureExpectation.lean` combines those derived layer expectations
with the finite generating identity. `integrable_dimensionKernel` and its
section version bound the signed kernel by the finite sum of absolute layer
weights, since every Poisson probability is at most one. They allow a different
finite endpoint measure. `integrable_dimensionPairMean` and its section version
also cover the masked kernel and its outer integral. Thus the signed integral
identities do not rely on totalization of a nonintegrable function.

For a finite atomless reference measure, density scaling and removal of the
null endpoint diagonal give:

```lean
theorem dimensionFiniteMeasureAction_expectation
    {α : Type*} [MeasurableSpace α] (O : MeasuredOrder α) (d : ℕ)
    (μ : Measure α) [IsFiniteMeasure μ] [NoAtoms μ]
    {ρ : ℝ} (hρ : 0 < ρ) :
    (∫ c, discreteDimensionAction O d ρ c
      ∂FinitePoisson.law (ENNReal.ofReal ρ • μ)) =
      dimensionFiniteMeasureAction O d μ ρ
```

The deterministic right side is separately defined using `μ (O.interval x y)`.
Two-point Mecke contributes two density factors. Factoring one density into
the discrete normalization leaves the same point and pair density powers as
`dimensionWeightedAction`. No flat volume formula is used at this stage.

In particular, `DimensionSprinkling.expectation_eq_restricted` specializes this
identity to a measurable finite-volume region **without causal convexity**.
Its kernel argument uses `dimensionRestrictedIntervalVolume`, the exclusive
interval intersected with that region. Non-convex regions cannot silently
substitute their full ambient interval volume.

## Second bridge: Minkowski geometry

`DimensionSprinkling.restricted_rate` invokes #91's
`dimensionRestrictedIntervalVolume_eq_properTime` only for region endpoints in
an ambient-causally-convex region. It covers null and diagonal pairs as well as
timelike ones. The intensity and both integrations use canonical product
Lebesgue volume. The independently defined bilocal functional is specialized
at constant first-endpoint weight one; all future partners in the region remain.

The convenient bounded-region contract is:

```lean
theorem DimensionBoundedCausalRegion.expectedAction_eq {n : ℕ} (hn : 0 < n)
    {M : Set (DimensionSpacetime n)} (hM : DimensionBoundedCausalRegion M)
    {ρ : ℝ} (hρ : 0 < ρ) :
    dimensionExpectedAction n ρ M =
      dimensionWeightedAction n (dimensionPointCoefficient (n + 1))
        (dimensionPairCoefficient (n + 1)) (dimensionIntervalCoefficient (n + 1))
        ρ M (fun _ => 1)
```

The underlying sprinkling theorem needs only finite volume, measurability and
ambient causal convexity. The bounded wrapper supplies finiteness from geometry.
This is an expectation theorem, not a sample-wise statement or a global limit.

## Calibrations and compatibility

- **2D:** `discreteDimensionAction_two` is exactly
  `2*N - 4*N_0 + 8*N_1 - 4*N_2`, with no density power left. It is dimensionless;
  no Planck length is defined using division by `d-2`.
- **4D discrete:** `discreteDimensionAction_four` identifies the whole action
  with unchanged `discreteBDGAction` after mapping every point with
  `dimensionSpacetimeCoordinates 3`. It holds for every multiset, not just
  almost surely or for timelike configurations.
- **4D probability and expectation:** `PoissonTransport.lean` transports the
  existing Janossy law stratum by stratum under a measure-preserving measurable
  equivalence. `DimensionSprinkling.four_probability` applies this to #91's
  coordinate map. `dimensionExpectedAction_four` therefore recovers unchanged
  `expectedBDGAction` on every measurable finite-volume region, even a
  non-convex one. This is not proved indirectly by assuming both continuum
  bridges or a Poisson-law coupling.
- **#93:** the reusable measured-order helper is separate from flat volume
  geometry and has no dependency on conformal asymptotics. The existing
  `FiniteMeasureBDG`, `ConformalAction`, their definitions and proofs remain
  untouched; no second probability law is introduced.

## Verification boundary

**Written argument:** the decomposition above and the conventional contract F
in the kernel note explain the route. **Machine verification:** the seven new
modules are imported by `BoundaryDraft`; `DimensionExpectationRegression.lean`
independently expands the finite-measure and physical contracts and tests
measurability, integrability, support, simplicity, zero volume, both parities'
weights, factorial denominators, a finite 2D chain, repeated endpoints,
null-related intermediate points, non-convex restricted volume, and 4D
observable/law/expectation transport. The PR records observed validation on
its candidate head. **Independent human mathematical review:** outstanding.

Run the full `formal/check.sh` source/transitive-axiom and aggregate audit,
`check_symbolic.py`, the Python unittest suite, and the Markdown checks. The
incremental checker is edit-loop feedback only. No custom axiom or admission
is permitted. No rate, variance, concentration, density-dependent geometry,
shrinking-cutoff uniformity, induced joint-area transport, global
higher-dimensional boundary limit, or individual-sprinkling convergence follows
from this package. It does not close research epic #24.
