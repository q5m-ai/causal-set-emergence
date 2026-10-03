# Smooth 3D pilot: intrinsic area and integration interfaces

This is the completion layer of [the shared #115 geometry API](PILOT3_GEOMETRY.md).
It preserves `Pilot3RegularHeight`, `SmoothPilot3`, the actual action and Poisson
law, and the independently fixed `pilot3BoundaryIntegral`. No area formula,
coarea identity, jet, divergence identity or limit is an admissibility field.
The new declarations below have Lean proofs; the final integrated audit receipt
is recorded on PR #120. Independent human mathematical review is separate.

## Proof architecture and normalization

1. `Pilot3Curve` proves exact tangent-line normalization and local distortion
   estimates for the actual scalar graph in the Euclidean spatial plane:
   `pilot3Coordinates (pilot3Curve g u) = (g u, u)`.
2. `Pilot3CurveArea` derives local finiteness, absolute continuity and the
   shrinking-ball density of the canonical Hausdorff pullback. Lebesgue
   differentiation and Radon–Nikodym uniqueness identify its **variable speed**.
   `Pilot3CurveAreaLocal` localizes through smooth cutoffs and a countable cover.
3. `Pilot3HeightCharts` constructs smooth height charts on actual open
   neighborhoods, retaining an orthogonal base coordinate. Each inverse has a
   global smooth representative on a smaller target ball. No openness of the
   set of infinite-order `ContDiffAt` points is assumed.
4. `Pilot3ChartTransport` differentiates the actual inverse. Its absolute
   determinant is tangent speed divided by gradient norm. `Pilot3SliceCharts`
   identifies the fixed canonical level measures with these same speeds.
5. `Pilot3JointCharts` identifies the **original** joint measure on every Borel
   chart subset with the actual lifted-curve Lorentzian Gram speed.
   `Pilot3JointAtlas` proves finite gluing and atlas independence as equalities
   of measures, including positive-measure overlaps.
6. `Pilot3Atlas`, `Pilot3AtlasRepresentation` and `Pilot3AtlasRegularity` construct
   the finite collar, smooth subordinate partition, fixed compact rectangles,
   common integrable bounds, and bounds at every fixed finite derivative order.
7. `Pilot3Coarea` proves signed spatial coarea after absolute integrability.
   `Pilot3Endpoints` removes only the two proved null regular levels.
   `Pilot3Ramp` and `Pilot3Divergence` derive outward-flux integration by parts
   using whole-space FTC/Fubini and the canonical collar density.

Spatial Hausdorff **one**-measure has normalization **one**. No sphere-area,
angular-average, action or 4D two-area coefficient enters this coarea law.
The joint density is Lorentzian Gram speed, not Euclidean spacetime speed.
Only the selected collar is noncritical; all positive-height critical points
remain in the original region. Canonical negative levels are empty, so the
boundary-density limit is **right-sided**, not a two-sided continuity claim.

## Exact area and gluing signatures

All names are in namespace `BoundaryDraft`. Implicit `h f` have type
`Pilot3Space → ℝ`; `hf` always means the unchanged `SmoothPilot3 h f`.

```lean
pilot3_hausdorff_restrict_curve_image_of_contDiffOn {g : ℝ → ℝ}
    (hg : Continuous g) (U : Set ℝ) (hU : IsOpen U)
    (hgU : ContDiffOn ℝ 1 g U) (s : Set ℝ)
    (hs : MeasurableSet s) (hsU : s ⊆ U) :
  (μH[1] : Measure Pilot3Space).restrict (pilot3Curve g '' s) =
    Measure.map (pilot3Curve g) ((volume.restrict s).withDensity
      (fun u => ENNReal.ofReal (pilot3CurveJacobian g u)))

Pilot3SliceChart.jointArea_chart (c : Pilot3SliceChart h)
    (hf : SmoothPilot3 h f) (s : Set ℝ) (hs : MeasurableSet s)
    (hsD : s ⊆ c.sliceDomain 0) :
  (pilot3JointArea h f).restrict (c.jointChart f '' s) =
    Measure.map (c.jointChart f) ((volume.restrict s).withDensity
      (fun u => ENNReal.ofReal (c.jointDensity f u)))

Pilot3RegularHeight.exists_collarAtlas (hh : Pilot3RegularHeight h) :
  Nonempty (Pilot3CollarAtlas h)

Pilot3CollarAtlas.sum_localJointMeasure (A : Pilot3CollarAtlas h)
    (hf : SmoothPilot3 h f) :
  (∑ i, A.localJointMeasure f i) = pilot3JointArea h f

Pilot3CollarAtlas.jointAtlas_independent (A : Pilot3CollarAtlas h)
    (hf : SmoothPilot3 h f) (B : Pilot3CollarAtlas h) :
  (∑ i, A.localJointMeasure f i) = ∑ j, B.localJointMeasure f j
```

`jointDensity f u` is defined as
`pilot3GramDensity (deriv (c.jointChart f) u)`, not a supplied density.
`jointDensity_eq` derives its spatial-area-factor formula and
`jointDensity_pos` proves strict positivity on the chart domain.
`jointArea_overlap` gives equality of the two restricted pushforwards on
**every Borel overlap**. `integral_jointArea_eq_sum` transports every integrable
observable through the finite atlas. No multiplicity-one assumption is used.

## Exact integration signatures for #79

```lean
pilot3LevelMeasure (h : Pilot3Space → ℝ) (t : ℝ) : Measure Pilot3Space
pilot3HeightDensity (h : Pilot3Space → ℝ) (t : ℝ) : ℝ
pilot3WeightedHeightDensity (h w : Pilot3Space → ℝ) (t : ℝ) : ℝ

Pilot3CollarAtlas.integral_openCollar_weighted (A : Pilot3CollarAtlas h)
    (hh : Pilot3RegularHeight h) (w : Pilot3Space → ℝ)
    (hw : ContinuousOn w (pilot3ClosedPositive h))
    (g : ℝ → ℝ) (hg : ContinuousOn g (Icc 0 A.width)) :
  (∫ x in {x | 0 < h x ∧ h x < A.width}, g (h x) * w x) =
    ∫ t in (0 : ℝ)..A.width, g t * pilot3WeightedHeightDensity h w t

Pilot3RegularHeight.tendsto_weightedHeightDensity_zero
    (hh : Pilot3RegularHeight h) (w : Pilot3Space → ℝ)
    (hw : ContinuousOn w (pilot3ClosedPositive h)) :
  Tendsto (pilot3WeightedHeightDensity h w) (𝓝[≥] 0)
    (𝓝 (∫ x, w x / ‖pilot3Gradient h x‖ ∂pilot3SurfaceMeasure h))

Pilot3RegularHeight.spatial_divergence (hh : Pilot3RegularHeight h)
    (hV : ∀ x ∈ pilot3ClosedPositive h, ContDiffAt ℝ 1 V x) :
  (∫ x in {x | 0 < h x}, pilot3Divergence V x) =
    -(∫ x, inner (𝕜 := ℝ) (V x) (pilot3Gradient h x) /
      ‖pilot3Gradient h x‖ ∂pilot3SurfaceMeasure h)

SmoothPilot3.spatial_divergence (hf : SmoothPilot3 h f) :
  (∫ x in {x | 0 < h x}, pilot3Laplacian f x) =
    -(∫ x, inner (𝕜 := ℝ) (pilot3Gradient f x) (pilot3Gradient h x) /
      ‖pilot3Gradient h x‖ ∂pilot3SurfaceMeasure h)
```

Here `V : Pilot3Space → Pilot3Space`. The minus sign is the outward normal,
which opposes increasing height. `integrableOn_openCollar_weighted`,
`intervalIntegrable_weightedHeightDensity`, `integrableOn_divergence` and
`integrable_surface_flux` supply the associated absolute integrability.
`integral_closedCollar_weighted` gives the closed-endpoint version.
`exists_collar_coarea` constructs one width for all continuous signed spatial
and height observables. Exterior weight/field values need not be measurable.

```lean
Pilot3CollarAtlas.exists_uniform_weighted_derivative_bound
    (A : Pilot3CollarAtlas h) (w : Pilot3Space → ℝ)
    (hw : ∀ x ∈ pilot3ClosedPositive h, ContDiffAt ℝ ∞ w x) (n : ℕ) :
  ∃ B : ℝ, 0 < B ∧ ∀ i,
    ∀ p ∈ Icc 0 A.width ×ˢ (A.charts i).closedDisk,
      ‖iteratedFDeriv ℝ n
        (fun q : ℝ × ℝ => A.weightedLocalTerm w i q.1 q.2) p‖ ≤ B
```

The same rectangles work for every finite order, with a separate bound for
each order. This does not assert a uniform bound over all orders or prove an
overlap Taylor jet. #78's actual long density/signed null-coordinate transport
and averaged jet, and #79's short response/remainder and coefficient
identification, remain separate analytic producer work.

## Concrete controls and dimensional boundaries

- `Pilot3Disconnected` proves admissibility of two separated unit disks with
  the curved sine future, both whole joint circles, both retained critical
  centers, nonempty regions, and actual signed collar integration. Its raw
  maximum is smooth near the entire closed positive region; no exterior
  smoothness or bilocal-action additivity is claimed.
- `Pilot3Annulus` proves the quartic annular height with combined slope witnesses
  `3 / 16` and `1 / 8`, both boundary circles, a retained positive-height critical
  circle, genuine curved-future behavior, planar recovery, signed collar coarea
  and spatial divergence. These are proofs, not merely executable fixtures.
- `DimensionTwoEndpoints` derives finiteness of every compact regular zero set
  in `DimensionSpatial 1`, identifies canonical Hausdorff zero-measure with
  counting measure on finite endpoint sets, and proves the integral sums all
  endpoints with arbitrary signed weights. The regression includes four
  endpoints. It does not introduce a full 2D two-face/action-limit contract.
- `DimensionFourGeometry` reuses `dimensionSpacetimeCoordinates 3` for **every
  original `AdmissibleTwoFace` C³ member**. It proves the region constructor,
  normals/metric and canonical measure/target transport, retains the original
  spatial two-area normalization, and identifies the actual action and
  expectation. Its limit theorem only re-expresses the already proved 4D limit.
  No old contract is strengthened, and no unified all-dimensional geometry
  class or higher-dimensional analytic port is claimed.

Five standalone pilot regressions check these contracts, including the original
overlap/contact controls. Follow [the required full local audit](README.md#reproduce)
after the final Lean input change. Module builds and incremental audits are
edit-loop evidence, not substitutes for that integrated gate or for independent
human mathematical review.
