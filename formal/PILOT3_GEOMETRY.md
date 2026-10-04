# Smooth 3D pilot: shared formal geometry for #115

## Scope and verification boundary

This package implements the shared smooth 3D geometry in #115 through one
production `SmoothPilot3` interface for #78/#79. It proves the whole finite
region and strata, intrinsic canonical joint area and Borel-overlap compatibility,
finite-atlas gluing, signed collar coarea and spatial divergence, actual causal
overlap and compact perturbation tubes, and #77's unchanged expectation
specialization. The [integration completion layer](PILOT3_INTEGRATION.md)
records exact area/collar/divergence signatures and proof architecture.
This supplies geometry, **not** the remaining #78/#79 analytic estimates or
#80's full-action assembly; the pilot's two action-limit goals remain open.

The class is exactly the smooth global two-graph class in
[the written #92 contract](../notes/dimension-two-face-geometry.md), with the
strict **combined** positive-part-height/future slope budget. It is not class E.
Physical dimension three means `DimensionSpacetime 2`, with the existing
canonical product Lebesgue measure. All original 4D declarations, hypotheses,
actions, laws, measures, and limits are unchanged.

The distinction between a smooth germ and a pointwise infinite-order
`ContDiffAt` matters in pinned mathlib: the latter permits neighborhoods that
vary with finite derivative order. `smooth_near` and `smooth_future` therefore
require an **open neighborhood on which `ContDiffOn` has smooth order**.
They do not merely require `ContDiffAt` at the base point, do not require
analytic germs, and do not require the clipped height to be smooth at the joint.

## Modules and exact consumer signatures

All declarations below are in namespace `BoundaryDraft`. The library root
imports every new module. Standalone regression sources independently import
the producer modules rather than relying on the library root.

| Module | Responsibility |
| --- | --- |
| `Pilot3Contract` | `Pilot3Space`, `Pilot3Spacetime`, slope-independent `Pilot3RegularHeight`, exact `SmoothPilot3`, actual region/strata, independent candidate area/angle/target, two open goal propositions |
| `Pilot3RegularHeight` | Open positive set, compact closed positive set and joint, noncritical band, smooth regular neighborhoods, constructed local height charts, finite one-dimensional Hausdorff measure |
| `Pilot3Geometry` | Whole region, closed ambient interval containment, full compact strata, vertical Fubini/volume, #77 constructor and exact expectation specialization |
| `Pilot3Overlap` | Independently defined signed first-endpoint covariogram, absolute integrability, causal vertical intersection and positive-part identity, raw short gap, exact bulk/moving-collar split and source-weight linearity |
| `Pilot3Tubes` | Actual null/proper-time coordinates, both-endpoint margins, finite-difference controls including contacts, compact old-active perturbation tubes, finite length support, common raw smooth translation neighborhood and finite-order derivative bounds |
| `Pilot3Metric` | Actual gradients, future unit normals, strictly positive angle, induced positive tangent metric, one-dimensional Gram density and scalar reparameterization factor |
| `Pilot3Surface` | Exact line normalization, finite candidate projected/spacetime measures, weight integrability, actual chart derivative and pointwise Gram factor, exact planar recovery |
| `Pilot3Examples` | Concrete unit ball/sine and planar pilots, nonempty curved future, retained critical point, whole circular joint and empty member |
| `Pilot3Components` | Whole-region/closed-positive maximum identities, both joints of separated components, exclusion of irrelevant exterior raw zeros |
| `Pilot3Curve`, `Pilot3CurveArea`, `Pilot3CurveAreaLocal` | Canonical variable-speed Hausdorff curve area, local restriction, signed integration and integrability equivalence |
| `Pilot3Levels`, `Pilot3HeightCharts`, `Pilot3ChartTransport`, `Pilot3SliceCharts` | Compact canonical levels, constructed smooth coordinate charts, actual determinant/tangent-speed identity and level-measure transport |
| `Pilot3JointCharts`, `Pilot3JointAtlas` | Actual Lorentzian lifted-curve density, all Borel chart restrictions/overlaps, finite gluing and atlas independence of the fixed measure |
| `Pilot3Atlas`, `Pilot3AtlasRepresentation`, `Pilot3AtlasRegularity` | Constructed finite smooth collar/partition, fixed compact rectangles, shared signed integrands and finite-order derivative bounds |
| `Pilot3Coarea`, `Pilot3Endpoints`, `Pilot3Ramp`, `Pilot3Divergence` | Normalized signed spatial coarea, proved null-endpoint removal, right-sided canonical density limit and outward-flux divergence |
| `Pilot3Disconnected`, `Pilot3Annulus` | Admissible disconnected/annular curved and planar controls, whole joint components, retained critical points and actual integration |
| `DimensionTwoEndpoints`, `DimensionFourGeometry` | Regular 2D endpoint finiteness/counting and exact coordinate/measure/action compatibility for every unchanged 4D C³ member |

The complete defining fields live in `Pilot3Contract.lean`; none is a jet,
measure choice, integral, coarea, cancellation, expectation identity or limit
premise. `Pilot3RegularHeight` has no slope hypothesis. `SmoothPilot3` adds
only the smooth future germ and the specified combined budget.

The following is the **compiled** common finite-density interface, with
`h f : Pilot3Space → ℝ` and `hf : SmoothPilot3 h f`:

```lean
pilot3Region (h f : Pilot3Space → ℝ) : Set (DimensionSpacetime 2)
pilot3Action (ρ : ℝ) (h f : Pilot3Space → ℝ) : ℝ
pilot3BoundaryIntegral (h f : Pilot3Space → ℝ) : ℝ
Pilot3DeterministicGoal : Prop
Pilot3ExpectedGoal : Prop

SmoothPilot3.boundedCausalRegion (hf : SmoothPilot3 h f) :
  DimensionBoundedCausalRegion (pilot3Region h f)

SmoothPilot3.expectedAction_eq (hf : SmoothPilot3 h f) {ρ : ℝ}
    (hρ : 0 < ρ) :
  dimensionExpectedAction 2 ρ (pilot3Region h f) = pilot3Action ρ h f

SmoothPilot3.integrable_bilocal (hf : SmoothPilot3 h f) (ρ : ℝ) :
  IntegrableOn (fun p : Pilot3Spacetime × Pilot3Spacetime =>
    dimensionBilocalKernel 2 (dimensionIntervalCoefficient 3) ρ p.1 p.2)
    {p | p.1 ∈ pilot3Region h f ∧ p.2 ∈ pilot3Region h f ∧
      p.2 ∈ dimensionCausalFuture p.1}
```

`pilot3Action` is precisely `dimensionWeightedAction 2` with the existing
physical-dimension-three point, pair and interval constants and source weight
one. `dimensionExpectedAction` still integrates `discreteDimensionAction`
against `FinitePoisson.law` of restricted volume times positive density.
`expectedAction_eq` is **derived** by `DimensionBoundedCausalRegion.expectedAction_eq`,
not encoded in admissibility or the definition of expectation.
`pilot3ExpectedGoal_iff` transfers the two **open propositions** by that
positive-density identity; it proves neither limit.

`Pilot3LongContractRegression.lean` independently expands the actual action,
probability law, causal domain, physical powers, region, closure and band for
#78. It now also expands the signed overlap and checks its absolute
integrability, fixed-cutoff tubes, length support and all-direction contact
control. It does not construct the long density, signed null-coordinate
transport or a jet. The same full partner set remains in the actual action;
source-weight linearity and component identities do not assert componentwise
additivity of a bilocal action.

`Pilot3ShortContractRegression.lean` independently expands the target from
one-dimensional Hausdorff measure and actual gradients, checks positivity,
finiteness, integrability, spacetime pushforward, planar recovery and the
actual tangent Gram factor for #79. It checks the open goals and conditional
expectation transfer, and now the exact raw overlap/moving-collar identities
and smooth compact translation-tube interface. It also checks intrinsic
Borel chart measures/overlaps, signed spatial coarea with both integrability
claims, right-sided density regularity, and spatial divergence with its outward
sign. It does not assert the short asymptotic estimate or a target/coefficient
identity.
`Pilot3OverlapRegression.lean` additionally checks null/zero displacements,
signed weights, exact contact, empty geometry, and a retained critical source
whose old gap is zero and new gap is negative while tube containment still holds.
The conventional consumer packages, [PR #119 for #78](https://github.com/q5m-ai/causal-set-emergence/pull/119)
and [PR #116 for #79](https://github.com/q5m-ai/causal-set-emergence/pull/116),
use the following agreed convention. Their merged notes are integrated from
`main`; they remain written arguments, not imported Lean proofs, and this port
does not assert their analytic conclusions.

```text
z = y - x = (tau, b), r = |b|, v = tau + r, sigma = tau^2 - r^2
long: future causal and v >= delta; short: future causal and v < delta
fixed delta > 0, independent of density; equality belongs to long
point term: short, exactly once
circle area: total mass 2*pi, not a probability measure
3D polar/null Jacobian: (1 - sigma/v^2)/4
signed outer pair factor: -dimensionPairCoefficient 3 * rho^(1 + 2/3)
```

The selected short route is direct-origin absolute overlap. The actual causal
positive-part overlap and compact perturbation tubes are now proved below.
Controlled signed collar/coarea integration and outward divergence flux are
proved in the [integration layer](PILOT3_INTEGRATION.md). An exact moving-collar
set integral alone is still not a coarea formula, and raw-germ or chart-integrand
derivative bounds are not an overlap jet.

### Actual overlap and compact-tube signatures

The observable is defined from the original region indicator before the formula
is proved. The weight acts only on the source, may have either sign, and need
only be continuous on the closed positive region. Its exterior values need not
be measurable. Absolute integrability is established before signed Fubini.
With the same `h`, `f` and `hf` as above:

```lean
pilot3WeightedOverlap (h f w : Pilot3Space → ℝ) (z : Pilot3Spacetime) : ℝ
pilot3OverlapGap (h f : Pilot3Space → ℝ) (z : Pilot3Spacetime)
    (x : Pilot3Space) : ℝ
pilot3ShortGap (f : Pilot3Space → ℝ) (z : Pilot3Spacetime)
    (x : Pilot3Space) : ℝ

SmoothPilot3.weightedOverlap_eq_gap (hf : SmoothPilot3 h f)
    (w : Pilot3Space → ℝ) (hw : ContinuousOn w (pilot3ClosedPositive h))
    (z : Pilot3Spacetime) (hz : ‖z.2‖ ≤ z.1) :
  pilot3WeightedOverlap h f w z =
    ∫ x, w x * max 0 (pilot3OverlapGap h f z x)

SmoothPilot3.integrable_weighted_overlapGap (hf : SmoothPilot3 h f)
    (w : Pilot3Space → ℝ) (hw : ContinuousOn w (pilot3ClosedPositive h))
    (z : Pilot3Spacetime) (hz : ‖z.2‖ ≤ z.1) :
  Integrable (fun x => w x * max 0 (pilot3OverlapGap h f z x))

SmoothPilot3.weightedOverlap_eq_bulk_add_collar (hf : SmoothPilot3 h f)
    (w : Pilot3Space → ℝ) (hw : ContinuousOn w (pilot3ClosedPositive h))
    (z : Pilot3Spacetime) (hz : ‖z.2‖ ≤ z.1) :
  pilot3WeightedOverlap h f w z = pilot3WeightedOverlap h f w 0 -
    (∫ x in {x | 0 < h x}, w x * pilot3ShortGap f z x) +
    ∫ x in {x | 0 < h x ∧ h x < pilot3ShortGap f z x},
      w x * (pilot3ShortGap f z x - h x)
```

These are the actual L3 and T5 identities in the merged long/short notes.
`weightedOverlap_eq_shortGap` gives the raw positive-part formula on the whole
positive source set. `weightedOverlap_zero` gives the original weighted point
volume. `Pilot3SlopeControl.mem_overlap_fibre` is pointwise, not just almost
everywhere, and `overlap_fibre_empty_of_nonpos_gap` keeps the original open time
endpoints at contact. `positive_endpoints` rules out spurious exterior partners.
No null displacement, component, or exceptional direction is discarded.

`Pilot3SlopeControl` only repackages the existing two Lipschitz constants and
strict combined budget; `SmoothPilot3.exists_slopeControl` derives a witness.
It is not an added admissibility condition. Its `gap_height_margins`,
`nullGap_decrease`, `rayGap_sigma_bounds` and
`rayGap_nonpos_of_cutoff_nonpos` prove the elementary L7 controls. In particular,
nonpositive null cutoff gap makes the whole right fibre nonpositive.

The compact height tube is the closed positive region intersected with the
positive-part-height superlevel set. `isCompact_heightTube` proves compactness;
`pilot3HeightTube_positive` proves strictly positive raw height when the margin
is positive. The following common interval depends on the fixed cutoff and
geometry, never on density:

```lean
SmoothPilot3.exists_long_perturbationTube (hf : SmoothPilot3 h f)
    (δ : ℝ) (hδ : 0 < δ) :
  ∃ κ η ε : ℝ, Pilot3SlopeControl h f κ η ∧
    ε = pilot3PerturbationWidth κ (1 - κ - η) δ ∧
    0 < ε ∧ ε < δ ^ 2 ∧
    ∀ (x θ : Pilot3Space) (v σ : ℝ), ‖θ‖ = 1 → δ ≤ v →
      σ ∈ Icc 0 ε → 0 ≤ pilot3RayGap h f x θ 0 v →
      x ∈ pilot3HeightTube h ((1 - κ - η) * δ / 2) ∧
      x + (v / 2) • θ ∈ pilot3HeightTube h ((1 - κ - η) * δ / 2) ∧
      x + ((v - σ / v) / 2) • θ ∈ pilot3HeightTube h ((1 - κ - η) * δ / 4)

SmoothPilot3.future_derivative_bounds (hf : SmoothPilot3 h f)
    (a : ℝ) (n : ℕ) :
  ∃ B : ℝ, 0 ≤ B ∧ ∀ x ∈ pilot3HeightTube h a,
    ‖iteratedFDeriv ℝ n f x‖ ≤ B
```

`pilot3PerturbationWidth` is the minimum of `δ^2/2` and
`(1-κ-η)*δ^2/(2*(1+κ))`. The endpoint theorem assumes activity only at
**old** proper-time square zero; the perturbed gap may already be negative.
It therefore covers exact contacts and positive-height critical points.
`exists_long_length_bound` supplies a finite upper length for every active
ray, uniformly in source, direction and nonnegative proper-time square.
These are controls for a future long producer, not that producer's density,
averaged jet, signed transport or cancellation theorem.

For the short consumer, `pilot3TranslationTube h ε` is the closed metric
thickening of the entire closed positive region. Its compactness and full
small-segment containment do not require that region to be convex or connected:

```lean
SmoothPilot3.exists_smooth_translationTube (hf : SmoothPilot3 h f) :
  ∃ ε : ℝ, ∃ U : Set Pilot3Space, 0 < ε ∧ IsOpen U ∧
    pilot3TranslationTube h ε ⊆ U ∧
    ContDiffOn ℝ ∞ h U ∧ ContDiffOn ℝ ∞ f U

SmoothPilot3.exists_translationTube_derivative_bounds (hf : SmoothPilot3 h f) :
  ∃ ε : ℝ, 0 < ε ∧
    (∀ x ∈ pilot3TranslationTube h ε,
      ContDiffAt ℝ ∞ h x ∧ ContDiffAt ℝ ∞ f x) ∧
    ∀ n : ℕ, ∃ Bh Bf : ℝ, 0 ≤ Bh ∧ 0 ≤ Bf ∧
      ∀ x ∈ pilot3TranslationTube h ε,
        ‖iteratedFDeriv ℝ n h x‖ ≤ Bh ∧ ‖iteratedFDeriv ℝ n f x‖ ≤ Bf
```

The first theorem retains an actual common open smooth neighborhood. The
second uses one tube for all finite orders, with a separate bound for each
order; neither says the clipped height is smooth. The separately constructed
`Pilot3CollarAtlas`, canonical level transport and coarea theorems are recorded
in [the integration interface](PILOT3_INTEGRATION.md); they are not inferred
merely from these tube bounds.

## What the geometric proofs actually give

- `isOpen_region`, `isBounded_region` and `measurableSet_region` use the
  continuous causal envelopes, never global continuity of raw height.
- `causallyConvex_region` retains each **closed ambient** interval, including
  endpoints and null points; it does not assume intrinsic causality or select
  one spatial component.
- `mem_closure_region`, `frontier_region`, `past_inter_future` and the three
  compactness theorems give every closed face/joint stratum over the closure
  of the positive set. No exterior zero sheet is added.
- `Pilot3RegularHeight.exists_noncritical_band` separates the compact critical
  set's positive heights from zero. Critical points are not removed from the
  region. `exists_regular_neighborhood` provides a common smooth ambient
  neighborhood, and `exists_level_chart` constructs a partial homeomorphism
  with the actual tangent inclusion as central inverse derivative.
- `normals_future_unit`, `cosh_gt_one`, `angle_identities`, `tangentMetric_pos`
  and `normals_orthogonal` derive the strict branch from actual differential
  bounds and transversality. Lean's total square root/division is not used as
  evidence of positivity. `exists_angle_margin` is for each fixed region,
  not uniform in a degenerating family.
- `pilot3_line_normalization` proves the one-measure convention on every
  linear image of a real set, without a measurability or finiteness premise.
  The coefficient is one, not the 4D spatial two-area coefficient pi/4.
- `hausdorff_finiteAt_joint` uses the implicit function theorem's local
  Lipschitz parameterization and one-dimensional tangent kernel. Compactness
  then gives finite spatial Hausdorff measure, before any target evaluation.
  The Lorentzian area factor is at most one, so the candidate induced measure
  is finite; continuity on the compact joint proves absolute weight integrability.
- `chart_gramDensity` identifies the actual derivative of a differentiable
  level curve after the future lift. `pilot3GramDensity_smul` supplies the
  absolute one-dimensional Jacobian, including orientation reversal. These
  are pointwise facts. `Pilot3SliceChart.jointArea_chart` in
  `Pilot3JointCharts.lean` uses the independent variable-speed curve area theorem
  to obtain equality of the actual measures on Borel chart subsets and overlaps;
  `Pilot3CollarAtlas.sum_localJointMeasure` then proves finite gluing.
- `integral_region` and `volume_region` give product-volume vertical Fubini
  with the original open time endpoints and no omitted positive components.
  They are not spatial coarea.

The target is specified independently as the angle-weighted measure obtained
from canonical spatial one-measure and the Lorentzian tangential Gram factor,
then pushed to the actual spacetime joint. `boundaryIntegral_eq_joint` proves
that projection/pushforward agreement. The new curve/chart/atlas theorems
identify this **same fixed measure** intrinsically; they neither replace it
with an arbitrary supplied measure nor redefine it from an action coefficient.

## Coverage ledger and remaining scope

| #115 item | Delivered here | Verification boundary |
| --- | --- | --- |
| Exact 3D class, region, independent target and goals | Original definitions preserved; no analytic admissibility fields; intrinsic target now identified by chart measures | The two pilot action-limit propositions remain open |
| Region and all strata | Open/measurable/bounded, finite volume, complete closed ambient interval containment, closure/frontier, compact faces/joint and exact intersection | No extra bundled manifold-with-boundary object is claimed or required by the supplied direct-origin interfaces |
| Normals, angle, Gram density and canonical measure | Strict future unit normals/angle, positive induced metric, line normalization one, finite area/integrable weight; variable-density Hausdorff area, every Borel chart overlap, finite gluing and atlas independence | The measure remains fixed independently of the action |
| #77 constructor | Existing action/law and derived finite-density expectation identity | Not a definition of expectation or a sample-wise result |
| Actual overlap and perturbation tubes | Signed actual covariogram, exact causal gap and bulk/moving-collar identities; old-active compact tubes, finite length support, contacts/critical points, common raw smooth neighborhood and derivative bounds | Long density/signed null-coordinate transport and averaged jet belong to #78; short response/remainder and coefficient identification belong to #79 |
| Regular-height/collar/integration | Constructed finite smooth collar and partition, fixed compact rectangles, canonical regular-level transport, signed coarea with integrability, null endpoints, right-sided density regularity, finite-order chart bounds and spatial divergence | Only the selected collar is noncritical; no overlap jet or 4D analytic coefficient is ported |
| Examples and consumer contracts | Ball/sine, planar, empty, whole-circle and contact controls; disconnected/annular admissibility, all joint components, retained critical centers/circle and actual integration; standalone #78/#79 regressions | No bilocal-action additivity or arbitrary-max smoothness claim |
| Physical dimension two | Compact regular zero-set finiteness, canonical zero-dimensional counting measure, all-endpoint integrals, four-endpoint signed regression | No full 2D two-face/action-limit contract or general-dimensional class is introduced |
| Physical dimension four | Exact region/normal/metric/measure/target/action/expectation coordinate compatibility for every unchanged old C³ member; old limit re-expressed in dimension-indexed coordinates | No old hypothesis is strengthened and no new 4D analytic result is inferred |
| Other dimensions | No geometry or analytic port claimed | The separately named written candidate remains a follow-up, not an all-dimensional Lean theorem |

No long/short asymptotic overlap jet, parity cancellation, asymptotic action theorem,
curved metric, null/mixed geometry, rates or sample-wise convergence are added.
The written #92 proofs remain written proofs at their original scope; Python
regressions are not universal proofs. Independent human mathematical review
of this encoding and its applicability remains outstanding.

## Reproduction

Follow [the pinned Lean setup](README.md#reproduce). The local full gate must
run after the final Lean source/build/checker/dependency change; the incremental
check is only edit-loop feedback.

```sh
cd formal
./check.sh --incremental --base origin/main
./check.sh
cd ..
.venv/bin/python check_symbolic.py
.venv/bin/python -m unittest -v
.venv/bin/python reproduce.py
python3 check_markdown.py
python3 -m unittest -v test_check_markdown
```

Validation results are recorded in the PR after observation. All five
standalone pilot regressions are discovered by `check.sh`, with warnings as errors
and the transitive-axiom rule, even though they are not library-root imports.
No independent human review is implied by a successful integrated Lean audit.
