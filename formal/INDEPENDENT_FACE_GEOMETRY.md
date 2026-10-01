# Independent-envelope geometry and regular heights (#106)

## Scope and verification boundary

`BoundaryDraft.IndependentFace` is the public import for the geometric part of
class E in [the independent-face note](../notes/independent-face-extension.md).
The new Lean declarations prove region/stratum geometry, independent spacelike
face bounds, the positive joint angle, intrinsic area and chart compatibility,
and the existing **finite-density** Poisson equality. They also expose the
regular-height atlas and spatial-divergence prerequisites without a cap-slope
restriction.

This completes the geometry package for #106, **not** the direct-origin limit
in #97. The actual overlap Taylor theorem belongs to #107, fixed-cutoff long
cancellation to #108, and coefficient identification/asymptotic assembly to
#109. Draft PR #104 is not an import or dependency. Its analytic backend is not
silently assumed here. Independent human mathematical scrutiny remains
outstanding under #94/#86; kernel checking verifies the encoded statements,
not physical applicability or novelty.

The older note's written proofs and historical status are unchanged. In
particular, its all-transport exclusion and explicit capsule integral
calculation are not promoted to new Lean theorems by this package.

## Exact admissibility and old inclusion

```lean
AdmissibleIndependentTwoFace (h f : Spatial → ℝ) : Prop
AdmissibleTwoFace.toIndependentTwoFace
```

The new contract extends `RegularHeight h` and records only:

- bounded positivity of `h`;
- the original `GraphCapRegularity h`: C³ raw height germs at the closed
  positive region, zero height on its frontier, and a nonzero actual
  differential at zero-height points there;
- C³ raw future germs at the same closed positive region;
- existence of global lower and upper `StrictGraphLipschitz` envelopes,
  with difference `max 0 h` everywhere and upper envelope equal to `f` on
  `graphClosedPositive h`.

The lower envelope's equality with `f-h` on the closure is **derived**. So is
coincidence of the envelopes outside positivity. There is no combined budget
below one, smoothness requirement on a clipped envelope, or analytic
conclusion in an admissibility field. Positive-height critical points and
irrelevant exterior raw values are unrestricted. The empty region is admitted,
including arbitrary raw future data outside its empty closure.

`AdmissibleTwoFace` and `AdmissibleGraphCap` are unchanged. Every original
member embeds without new hypotheses: the witnesses are its original future
and that future minus the positive height. This does not create a reverse
conversion or let a steep height use the planar-cap action theorem.

## Public class-E interfaces

Unless otherwise indicated, the following methods take
`hf : AdmissibleIndependentTwoFace h f`.

| Interface | Result and additional hypotheses |
| --- | --- |
| `lowerEnvelope`, `upperEnvelope` | Chosen global causal envelopes; no differentiability is asserted for them |
| `strictGraphLipschitz_lower`, `strictGraphLipschitz_upper` | Independent strict bounds |
| `envelope_gap`, `upper_eq`, `lower_eq` | Exact positive-height difference everywhere; raw-germ agreement on `graphClosedPositive h` |
| `envelopes_eq_of_nonpos` | Coincidence wherever raw height is nonpositive |
| `exists_thickness_bound` | A nonnegative thickness Lipschitz constant below two, not below one |
| `region_eq_twoGraphRegion` | Exact equality of the original raw-germ region and envelope region |
| `isOpen_region`, `measurableSet_region`, `isCompact_closure_region`, `isBounded_region` | Open, measurable, bounded region with compact closure |
| `mem_closure_region` | Exactly the closed fibres over `graphClosedPositive h` |
| `causallyConvex_region`, `boundedCausalRegion` | Containment of every **closed ambient causal interval**, including vertices and null relations |
| `isCompact_past`, `isCompact_future`, `isCompact_joint`, `frontier_region` | Compact original strata; the two closed faces exhaust the frontier |
| `past_inter_future` | Exact face intersection; this set identity needs no admissibility hypothesis |
| `exists_face_slope_bound`, `face_slopes_lt_one` | Both raw gradients are bounded by the maximum of independent strict envelope constants |
| `normals_future_unit`, `normals_independent` | Actual future unit timelike normals; a vanishing linear combination at a joint point has both coefficients zero |
| `cosh_gt_one`, `angle_identities`, `areaDensity_pos`, `joint_tangent_geometry` | Positive angle and induced spacelike tangent metric at every `x ∈ graphJoint h` |
| `continuousOn_weight`, `continuousOn_areaDensity` | Continuity on the compact spatial joint |
| `finite_projectedArea`, `finite_jointArea`, `integrable_weight` | Finite original area measures and absolutely integrable original angle weight |
| `expectedBDGAction_eq` | For `0 < ρ`, the unchanged expected discrete action equals `continuumMean`; **no limit** |
| `toRegularHeightPair`, `spatial_divergence` | The actual raw future Laplacian integral equals minus its normalized Hausdorff boundary flux |

`RegularHeight.gradient_bound_of_envelope` is the reusable derivative-bound
lemma. It requires a raw C³ germ on the closure, a nonnegative global Lipschitz
constant for an envelope, and agreement on the closure. It differentiates
only inside the open positive region and then uses continuity of the raw
differential to reach the joint.

## Area, normalization and raw-germ charts

All original definitions are retained: `twoFaceRegion`, the three face/joint
sets, `twoFaceNormal`, `twoFaceWeight`, `twoFaceProjectedArea`,
`twoFaceJointArea`, `twoFaceBoundaryIntegral`, `continuumMean`, and
`expectedBDGAction`. The area still uses the Lorentzian Gram factor, **not**
Euclidean spacetime graph area, and the spatial Hausdorff normalization in
`graphSurfaceMeasure` is still `ENNReal.ofReal (Real.pi / 4)`.

For `c : SliceHeightChart h` the new methods are:

- `hasFDerivAt_jointChart_independent` and
  `jointFrame_eq_fderiv_independent`: the declared frame is the actual
  derivative of the raw future chart, at `u ∈ c.sliceDomain 0`;
- `jointDensity_eq_independent`: the actual Lorentzian Gram density equals the
  original area factor times the spatial chart Jacobian on that domain;
- `jointArea_chart_independent`: equality of measures on every measurable
  `s ⊆ c.sliceDomain 0`;
- `jointArea_overlap_independent`: equality on the full overlap of two such
  measurable chart subsets, with neither disjointness nor discarded seams.

These all accept class E, not `AdmissibleTwoFace`. Global raw-future continuity
would be an invalid added assumption. `jointArea_eq_map_upper` instead compares
the raw lift almost everywhere with the continuous upper-envelope lift on
the joint. Derivatives still come from the raw C³ germ, never from the clipped
envelope at the joint.

## Slope-independent regular-height API

`RegularHeight h` extends the unchanged `GraphCapRegularity h` with bounded
positivity only. It does **not** assume Lipschitz control. Positive-part
continuity is proved using smoothness near the closure and vanishing off it.

The `RegularHeight` namespace now supplies:

- positive-part continuity/compact support, open/measurable positivity,
  `frontier_eq`, compact closure/joint, and nonnegative height on the closure;
- `exists_noncritical_band`, `exists_regular_neighborhood`, the actual
  gradient and spatial unit-normal identities;
- finite normalized joint/regular-level measures and integrable
  reciprocal-gradient weights;
- `exists_contDiff_level_chart`, `exists_regularHeightChart`,
  `exists_coordinateHeightChart`, `exists_sliceHeightChart`,
  `exists_jointChart`, and `exists_controlledCollarAtlas`;
- regular-level volume nullity and the open/closed collar endpoint transports;
- `tendsto_graphWeightedHeightDensity_zero` for a spatial observable continuous
  on the closed positive region.

The finite-sum transport methods in `GraphAtlasRepresentation` and the
spatially weighted coarea methods in `GraphWeightedCoarea` now accept
`RegularHeight h`. Signed observables retain their continuity/integrability
hypotheses. These identities are **proved results**, not structure fields.
The existing `RegularHeightChart` and `ControlledCollarAtlas` definitions and
all canonical measures are unchanged.

`RegularHeightPair h f` adds only a C³ observable near the closure. Its
`integrable_graphSurface_flux`, `graph_ramp_balance` and `spatial_divergence`
prove the same flux identities without either face's slope bound. The
original `AdmissibleTwoFace` theorem signatures are retained as wrappers.
Original cap methods likewise retain compatibility wrappers; a one-way
coercion from `AdmissibleGraphCap h` to `RegularHeight h` supports existing
callers of the generalized atlas methods. No cap action reduction, cap angle
identity, or cap limit is generalized to slope-less geometry.

## Instances and regressions

`ellipsoid_regularHeight` and `graphJoint_ellipsoid_regular` need only positive
height scale and positive axes. `symmetricEllipsoid_independent` admits height `ellipsoidProfile a b` and
future `ellipsoidProfile (a / 2) b` under `0 < a` and `∀ i, a < b i`. Its causal
envelopes are plus/minus the positive half-height. `symmetricEllipsoid_cosh`
computes the actual opposite-normal angle from the half-height gradient.

`steepCapsule_admissible` specializes this to the required height scale
`3/4` and unit axes. `steepCapsule_height`, `steepCapsule_future`,
`steepCapsule_upper_envelope` and `steepCapsule_slope` check the specified
norm-squared profile, half-height future, clipped half-height envelope and
thickness slope `3/2` on the unit sphere. `steepCapsule_not_old_cap` and
`steepCapsule_not_old_twoFace` prove failure of the original coordinate
contracts; `steepCapsule_positive_critical` retains the interior maximum.

`IndependentFaceRegression.lean` independently restates the region, null
interval, finite-density bridge, normalization, actual-frame, chart-overlap,
signed coarea and divergence contracts. It instantiates the steep capsule's
atlas and proves its width stops below the retained critical height. It also
checks the empty case, a genuinely nonplanar symmetric unequal-axis member
with distinct positive angles, original planar inclusion, a nonconstant angle
weight on the original unequal-axis joint, and the original planar
measure/target recovery with its `48 * Real.pi` value.

Run the incremental developer check against an ancestor base, then the full
local `formal/check.sh` warning/transitive-axiom gate before handoff. Python
symbolic/numerical checks remain complementary regressions, not substitutes
for these Lean proofs. No sample-wise convergence, rates, shrinking cutoffs,
extra strata, null/mixed joints, curvature, or dimensional enlargement is
implied.
