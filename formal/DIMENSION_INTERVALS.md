# Dimension-indexed causal intervals and finite-density transport (#91)

This is the finite-geometry bridge from the published coefficients to **actual
interval volume**, in every integer physical dimension at least two. It reuses
`DimensionSpacetime`, the Euclidean sphere normalization, and the independently
defined `dimensionIntervalCoefficient`. It does not reconstruct kernel moments,
change the existing four-dimensional action, or extend a boundary limit.

## Scope and theorem contracts

`DimensionSpatial n` is `EuclideanSpace ℝ (Fin n)` and
`DimensionSpacetime n` is its product with real time. Here `n` is **spatial**
dimension; physical dimension is `n + 1`. Volume is canonical product Lebesgue
measure. Volume-law and null-cone theorems require `0 < n`, so physical dimension
one is not claimed. This is a quantified theorem, not extrapolation from the
2D–4D calibrations. Several algebraic/order lemmas also work at `n = 0`.

The principal measure-level result is:

```lean
theorem volume_dimensionCausalInterval (hn : 0 < n)
    (x y : DimensionSpacetime n) (hxy : y ∈ dimensionCausalFuture x) :
    volume (dimensionCausalInterval x y) = ENNReal.ofReal
      (dimensionIntervalCoefficient (n + 1) *
        dimensionIntervalSq x y ^ (((n + 1 : ℕ) : ℝ) / 2))
```

This includes null and coincident endpoints. A non-future-related pair instead
has an empty interval; the displayed formula is **not** asserted for arbitrary
unordered endpoints. `volume_dimensionCausalInterval_lt_top` proves finiteness
before any conversion to real volume.

The independent region hypothesis is `DimensionCausallyConvex M`: every
**ambient closed causal interval** between two points of `M` lies in `M`.
It contains no integral, volume, normalization, or limit premise.

```lean
theorem dimensionRestrictedIntervalVolume_eq_properTime (hn : 0 < n)
    {M : Set (DimensionSpacetime n)} (hM : DimensionCausallyConvex M)
    {x y : DimensionSpacetime n} (hx : x ∈ M) (hy : y ∈ M)
    (hxy : y ∈ dimensionCausalFuture x) :
    dimensionRestrictedIntervalVolume M x y = ENNReal.ofReal
      (dimensionIntervalCoefficient (n + 1) *
        dimensionIntervalSq x y ^ (((n + 1 : ℕ) : ℝ) / 2))
```

For a non-convex region, `dimensionRestrictedIntervalVolume` remains the volume
of the **exclusive interval intersected with that region**. It is never defined
by the proper-time formula. A regression uses a two-point region with timelike
endpoints: its restricted volume is zero but its ambient interval volume is two.
Existing `DimensionGraphCapData` supplies non-vacuous causally convex examples.

## Written proof and implementation map

### 1. Order, measurability, endpoints and nullity

`BoundaryDraft/DimensionCausalInterval.lean` defines the closed interval as the
intersection of two closed cones, and the exclusive interval by removing only
the two endpoints. `dimensionCausalOrder` proves reflexivity, transitivity and
antisymmetry. **Chronology is not the discrete order.** The regression retains
an intermediate point on a null segment even though it is not chronological.

Continuity of the Euclidean norm proves joint measurability of the causal
relation and closed interval. Removing the endpoint equality sets gives joint
measurability of the exclusive interval. Section measurability then proves
joint measurability of restricted interval volume for measurable regions.
Singletons have zero product volume, and Fubini proves endpoint-diagonal nullity.

At a fixed time a null cone has a spatial sphere as its fibre. The existing
positive-dimensional Euclidean sphere-nullity theorem and product Fubini give
`volume_dimensionNullCone` and `volume_dimensionNullPairs`. This includes the
two spatial directions in physical dimension two. For a null endpoint pair,
the triangle inequality and the two causal inequalities must be saturated;
every intermediate point therefore lies on the first endpoint's null cone.
This proves zero volume directly, including restricted intervals in arbitrary
regions. No singular Lorentz transformation or continuity-in-boost argument is
used. `ae_dimensionCausalFuture_chronological` is an **integration** consequence,
not a change to the order definition.

### 2. The actual rest-frame volume

`BoundaryDraft/DimensionIntervalVolume.lean` bounds every interval by a compact
time-interval/Euclidean-ball product, establishing finite measure and the
integrability needed for Fubini. Between the origin and `(H, 0)`, the spatial
slice is the closed ball of radius `min t (H - t)`. The existing
`integral_dimensionSpatial_radial` computes its volume. Splitting the time
integral at `H / 2` and reflecting its second half evaluates the polynomial
primitive. `dimensionRadialFactor_eq_sphere` and
`dimensionIntervalCoefficient_eq_sphere` identify the result with the published
Gamma coefficient, in every positive spatial dimension. Zero duration is
included; the proof does not infer finiteness from a totalized real integral.

### 3. Lorentz transport, with its Jacobian and time orientation proved

`BoundaryDraft/DimensionLorentz.lean` defines the actual Minkowski bilinear
form from the time product minus the Euclidean spatial inner product. It proves
nondegeneracy and uses the matrix of that form in a finite basis: preservation
of the form forces the square of the linear determinant to be one. The Haar
change-of-variables theorem therefore proves preservation of canonical product
volume. Spatial orientation reversal is allowed.

`DimensionPoincareEquiv` assumes only a linear equivalence, translation,
preservation of that bilinear form, and positive time component of the image
of the unit time axis. The Cauchy–Schwarz inequality proves future-cone
preservation; its inverse's time orientation is derived. Squared proper time,
closed intervals, arbitrary-set volumes and signed set integrals transport.
No measure-preservation field or desired action identity is assumed.

For a future timelike displacement of proper duration `H`,
`exists_dimensionRestFrame` constructs a map. It uses the identity on the time
axis and otherwise the explicit rank-one Lorentz reflection with normal equal
to the displacement minus `(H, 0)`. Its non-null denominator, involution,
metric preservation, axis image and future orientation are proved. Translation
then transports the computed rest-frame volume to arbitrary timelike endpoints.
The real half-dimensional power is retained in odd dimensions. Null endpoints
use the separate zero-volume proof above.

### 4. Exact deterministic transport

`BoundaryDraft/DimensionActionTransport.lean` substitutes in **both endpoints**
of the existing `dimensionWeightedAction`. The transported first-endpoint
weight is composed with the inverse map. Partners still range over the whole
region intersected with the closed causal future, not over the source support.

`DimensionPoincareEquiv.weightedAction_image` proves affine Lorentz covariance.
`dimensionWeightedAction_dilate` proves positive-dilation scaling at positive
density: the region scales by `s`, density becomes `ρ * s ^ (n + 1)`, and the
action factor is `s ^ (n - 1)`. Both endpoint Jacobians are proved, as are the
proper-time and real-power identities. The dilation statement assumes a
measurable region; bounded regions with continuous weights have the compact
absolute domination already proved by `integrableOn_dimensionWeighted_bilocal`.
There is no unproved finite-density transport premise left in these APIs.

The ambient proper-time kernel remains an independently defined deterministic
observable on other regions. Its identification with a restricted-volume
Poisson kernel requires causal convexity and the **separate probability bridge**;
this file does not assert that identification for non-convex regions.

### 5. Dimensions two, three and four; coordinate normalization

`BoundaryDraft/DimensionIntervalCompatibility.lean` gives the exact 2D, 3D and
4D laws using the existing coefficients `1 / 2`, `Real.pi / 12`, and
`Real.pi / 24`. These are specializations, not the proof's dimension range.

`dimensionSpacetimeCoordinates` maps time and Euclidean spatial coordinates to
the original time-first `Fin (n + 1) → ℝ` coordinates. Its measure preservation
is proved from `PiLp.volume_preserving_equiv` and the product-coordinate
bijection, with no extra normalization factor. In 4D it identifies the original
squared proper time, closed causal order, closed and exclusive intervals, and
actual interval measures. `dimensionWeightedAction_four_eq_continuumMean`
identifies the complete unweighted finite-density observable with the unchanged
`continuumMean`, not merely with its reduced plane kernel. No old 4D theorem or
action definition is edited. The published coefficient here is the proper-time
coefficient; the normalized-null-coordinate convention discussed in
[the kernel note](../notes/dimension-kernels.md#1-sources-conventions-and-normalization-table)
is not silently substituted for it.

## Verification and remaining boundaries

- **Written argument:** the proof decomposition above and the Lean module
  explanations specify the conventional finite-geometry route.
- **Machine verification:** the five modules are imported by `BoundaryDraft`.
  `DimensionIntervalRegression.lean` and `DimensionTransportRegression.lean`
  independently exercise the general contracts, measurability, non-convexity,
  null/diagonal endpoints, non-rest translation, parity, nonunit and reciprocal
  dilation, signed weights and unchanged 4D measure/action conversion. Require
  the full `formal/check.sh` source/transitive-axiom audit on the candidate head;
  the PR records the observed result. Incremental checks alone do not qualify.
- **Diagnostics:** `test_rest_interval_volume_by_ball_slices` independently
  integrates Euclidean ball slices in both parities, including zero duration.
  Python/symbolic/numerical agreement is diagnostic, not a universal proof.
- **Independent human mathematical review:** outstanding. Machine checking is
  not an assertion of independent review or physical applicability.

The dimension-indexed finite Poisson/discrete-action expectation instantiation
in #77, geometric higher-dimensional long-null jets, and global
higher-dimensional two-face limits remain separate. The subsequent
[#92 geometry package](../notes/dimension-two-face-geometry.md) supplies written
intrinsic joint-area/transport proofs and a named 3D pilot; a corresponding
dimension-indexed Lean geometry port remains outstanding.
No probability axiom, expectation identity, jet, asymptotic cancellation or
limit has been added to geometric admissibility. No rates, density-dependent
geometry, shrinking-cutoff uniformity or sample-wise convergence are inferred.
This finite-geometry package does not close the research epic #24.

Reproduce from the repository root:

```sh
.venv/bin/python check_symbolic.py
.venv/bin/python -m unittest -v
.venv/bin/python reproduce.py
python3 check_markdown.py
python3 -m unittest -v test_check_markdown
cd formal
./check.sh
```
