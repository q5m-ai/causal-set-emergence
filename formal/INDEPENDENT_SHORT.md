# Actual independent-envelope short limit (#107)

## Scope

`BoundaryDraft.IndependentShortLimit` proves the actual class-E short-action
limit, not just the response of a polynomial model. The hypotheses are exactly
`AdmissibleIndependentTwoFace h f`. No overlap, remainder, density, divergence
or limit premise is added to that geometric contract. The action, kernel,
restricted Poisson law, intrinsic area and positive-angle target are unchanged.

The public handoff to #109 is:

```lean
theorem AdmissibleIndependentTwoFace.exists_shortContinuumMean_limit
    {h f : Spatial → ℝ} (hf : AdmissibleIndependentTwoFace h f) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
      Tendsto (fun ρ => shortContinuumMean ρ δ (twoFaceRegion h f)) atTop
        (𝓝 (twoFaceBoundaryIntegral h f))
```

The cutoff is fixed before density tends to infinity. A single sufficiently
small positive bound works for **every** smaller fixed positive cutoff,
including that bound. The cutoff equality still belongs to the long domain.
This result neither needs nor proves #108's long-density theorem. There is no
full-action or expected-action limit here, no shrinking-cutoff uniformity,
quantitative rate, or individual-sprinkling claim. #109 and integration PR #104
retain final assembly and parent acceptance. Human mathematical review remains
outstanding unless separately recorded.

## Proof construction

### Raw germs before differentiation

`IndependentShortGerm.lean` derives a `RawFaceNeighborhood` from compactness,
raw C³ germs and the independent envelope bounds. This is an intermediate
geometric neighborhood proved to exist, **not an admissibility field**.
Both raw differentials are strictly bounded there. Neither the thickness
slope nor the sum of the two envelope constants must be below one.

`partner_positive` uses the raw past bound on a small translated segment:
a positive raw causal gap forces the partner's height to be positive.
`raw_envelope_positivePart` then identifies the raw and envelope positive
parts for sources in the closed positive region. Exterior envelope gaps
vanish by the separate global face bounds. Only after these facts does
`translatedOverlap_eq_shortGap` rewrite the actual overlap in raw coordinates.
Null displacements and the vertex are included. Irrelevant exterior raw data
need not be continuous.

`translatedOverlap_eq_fixed_sub_gap_add_collar` establishes absolute
integrability before the signed split. `volume_region_eq_height` identifies
the constant term with the original spacetime point volume; the time-linear
moving slice is explicit in `translatedOverlap_eq_absolute_bulk`.

### Common moving collar and complete two-jet

`IndependentShortCollar.lean` uses the slope-independent finite height atlas,
its fixed compact supports, and its original C² weighted Jacobians. The pure
moving-root and jet helpers now require only `RegularHeightPair`. No C³
Jacobian is assumed.

The raw future has no global Lipschitz bound. Consequently the original
argument estimating it at an arbitrary negative moving root cannot be copied.
Instead, an intermediate-value argument produces a root on the actual
nonnegative-height fibre. The local bound puts this root inside the common
IFT uniqueness neighborhood, identifying it with the smooth root. Signed
Fubini is justified on each fixed compact rectangle before chart summation.
Only the regular collar is transported; interior critical points remain in
the fixed-domain bulk integral, outside the coarea argument.

`IndependentShortJet.lean` proves `exists_absoluteOverlap_twoJet` with the
actual volume, linear slice, future Hessian and full canonical surface square.
It then constructs `exists_absoluteOverlap_remainder`: one measurable
representative with C² regularity and bounds on its value, first derivative
and second derivative. These are the actual `ShortNullRemainder.CubicBounds`
consumed by the normalized nearly-null cancellation theorem. A value-only
cubic estimate is not substituted for derivative control.

### Actual density and intrinsic coefficient

`IndependentShortAngular.lean` derives full-sphere coefficients from the
complete jet. The slope-free polynomial calculations in `TwoFaceAngularJet`
now operate on `RegularHeightPair`; explicit wrappers preserve the original
admissible-class signatures. The constant and time-linear terms are retained,
as are both signed quadratic modes.

`TwoFaceCoefficient` now derives the same spatial/intrinsic target identity
under independent face bounds, again retaining original wrappers. Spatial
divergence is the existing proved regular-height theorem. Its future-Hessian
contribution supplies the boundary flux; it is not discarded. No source
weights or artificial partition-derivative terms are introduced. The geometric
reciprocal-gradient integral may be used algebraically without asserting that
a same-height planar region is causally convex or has a particular action.

`IndependentShortLimit.lean` establishes the four moving-endpoint radial
identities for the actual cutoff fibre, including empty support. It proves
`AbsoluteShortModel.actual_density_decomposition` after absolute integrability
of the actual overlap and remainder product integrands, before signed Fubini.
The class-E producer is `exists_shortOverlapDensity_decomposition`: one
measurable remainder and its primitive bounds produce the exact decomposition
of the existing `shortOverlapDensity` at every smaller fixed positive cutoff.
The final theorem discharges **all** inputs to
`AbsoluteShortModel.action_limit_of_remainder`, including the original point
volume and density powers, and identifies the result with the independent
intrinsic target. No invalid planar comparison or long-limit premise is used.

## Acceptance and regressions

| #107 obligation | Producer / evidence |
| --- | --- |
| Local raw/envelope equality before differentiation | `partner_positive`, `raw_envelope_positivePart`, `translatedOverlap_eq_shortGap` |
| Actual C³ extension and complete absolute two-jet | `exists_collarCorrection_twoJet_independent`, `exists_absoluteOverlap_twoJet` |
| Full-sphere coefficients and actual density decomposition | `exists_absoluteAngularExpansion`, `exists_shortOverlapDensity_decomposition` |
| Measurable primitive remainder and derivative bounds | `exists_absoluteOverlap_remainder`, `ShortNullRemainder.CubicBounds` |
| Original point term, density powers and fixed-cutoff limit | `volume_region_eq_height`, `exists_shortContinuumMean_limit` |
| Divergence and unchanged intrinsic coefficient | `spatial_divergence`, `absoluteShortCoefficient_identification` |
| Old/new geometries and critical points | `IndependentShortRegression.lean`, existing independent-face and absolute-short Python regressions |

`IndependentShortRegression.lean` independently expands the original
point/pair normalization and target, all four density coefficients, and all
primitive bounds. It applies the **new absolute theorem** to the steep capsule
while retaining its positive-height critical point and exclusion from the old
cap class, the nonplanar variable-angle symmetric unequal-axis member, every
old member, the original planar unequal-axis value, and empty geometry with
arbitrary exterior raw future data. Existing symbolic/numerical capsule,
variable-angle, moving-endpoint and Hessian regressions remain complementary
diagnostics; fitted high-density values are not used as proofs.

## Validation

Local validation passed: focused Lean compilation and independent regression
contracts; the incremental changed-source check; the full two-worker build,
all-source warnings-as-errors/transitive-axiom audit and aggregate audit;
all symbolic checks; all 179 Python tests; Markdown lint and its 20 tests.
The measured full audit took 1:56:24. No Lean input changed after that gate;
subsequent documentation-only edits received the lightweight Markdown checks.
This is a machine-check receipt, not independent human mathematical review.

```sh
(cd formal && ./check.sh --incremental --base origin/main)
(cd formal && ./check.sh)
.venv/bin/python check_symbolic.py
.venv/bin/python -m unittest -v
python3 check_markdown.py
python3 -m unittest -v test_check_markdown
```
