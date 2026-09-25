# Lean verification: checked components and explicit targets

**Status: the deterministic ellipsoid and null-plane-cap continuum limits and
the concrete ellipsoid's Lorentzian angle/surface-integral interpretation are
proved in Lean. The exact finite-density reduction is also proved for the
general admissible graph-cap class. General positive-angle geometry, finite
Hausdorff joint integrals, and the vanishing non-collar remainder are checked.
Euclidean planar Hausdorff normalization and exact tangent-image area are
proved on every set. The variable-Jacobian scalar-graph area formula is proved,
including its open-domain and signed-integral forms. Canonical height levels
have finite measure and integrable weights in a noncritical band. A finite
controlled collar atlas, ambient and canonical slice transport, smooth overlap
weights, and uniformly dominated finite-sum representations are now proved.
The canonical density is continuous and measurable on a nonnegative collar,
uniformly bounded there, and tends from the right to the existing boundary
integral. Canonical Hausdorff and parametric ellipsoid measures agree, with
subtype transport, integrability, and recovery of the original boundary value.
Global collar coarea is derived from the atlas, including null endpoints,
absolute integrability, and the signed kernel specialization. The general
deterministic limit, arbitrary null boundaries, induced null-joint geometry,
and the Poisson-expectation bridge remain open.**

Lean **4.19.0** and mathlib **v4.19.0** are pinned. `lake-manifest.json` pins the
resolved dependency commits; mathlib is
`c44e0c8ee63ca166450922a373c7409c5d26b00b`.

This is the checked layer for Program 1 of **Causal Set Emergence**. The Lake
package identifier remains `causal_set_gravity` because this program studies the
BDG gravitational action; renaming the research umbrella does not change its
mathematical scope. This directory contains the proved components and explicit
open targets.

## What actually compiles and is proved

`./check.sh` builds the library, discovers **every local Lean source** (excluding
`.lake/` and `.tools/`), and checks each with warnings treated as errors. Each
source is also rechecked in an isolated current module so all of its public
declarations receive a transitive axiom audit even when that source is not
imported by the library root. Finally, the aggregate audit inventories the
library's public theorems and public definitions. The library root imports
all kernel, general graph-cap, ellipsoid, causal-interval, null-coordinate,
Gaussian, and limit modules. `GraphCapRegression.lean` independently restates
the general finite-density equality, checks complete slices with null points
and the vertex, and verifies ellipsoid compatibility and a nonquadratic
admissible profile with a positive-height critical point. It also checks that the uniform
noncritical band stops below that critical height. `GraphCollarRegression.lean`
independently checks the band contract, compact joint, local regular
neighborhoods, exclusion of unrelated exterior zeros, and original unequal-axis
ellipsoid hypotheses. `GraphBoundaryRegression.lean` independently checks
strict slopes/normals/angles, implicit charts, finite surface measure and
integrable weights, the exact action split and vanishing remainder, and
compatibility with the original unequal-axis gradient and parametric integral.
Its original parametric checks are retained; the new
`EllipsoidHausdorffRegression.lean` independently checks the measure-level
Hausdorff/parametric identification, arbitrary joint observables and
ambient/subtype transport, canonical integrability, and both canonical `48π`
integrals with the original unequal-axis endpoints and hypotheses.
`HausdorffGraphRegression.lean` checks Euclidean rather than supremum norms,
actual graph derivatives, zero-error comparisons without a finiteness premise,
a nonlinear paraboloid's local bounds, the planar disk upper bound, and null
remainders. `HausdorffPlaneRegression.lean` checks both planar inequalities,
equality of measures on arbitrary sets, the closed unit disk, the genuinely
Euclidean norm, and the infinite-measure case. `HausdorffDensityRegression.lean`
checks the graph pullback, tangent-map injectivity, and the almost-everywhere
closed-ball density uniqueness theorem. `HausdorffAreaRegression.lean` now
independently checks arbitrary-set tangent area, the tilted Euclidean slope,
infinite area, nonlinear graph area, derived local finiteness/absolute
continuity, every-point density, open-domain localization, and signed
integration/integrability. `GraphDensityRegression.lean` checks canonical level
normalization, compactness, an integrable level band, the zero-height boundary
value, and extension of a joint neighborhood to a thin collar. It also checks
collar measurability, a uniform bound, the right-hand boundary limit, and a
measurable cutoff usable by a signed-kernel consumer. The unequal-axis limit
is `48π`, while two-sided continuity is explicitly disproved for that example.
The quartic regression checks these regularity facts on a controlled collar
strictly below its retained positive-height critical point.
`GraphAtlasRegression.lean` checks chart construction,
canonical slice transport, the common dominator, and an overlapping refinement
of a whole finite atlas. Both duplicate chart entries have positive weights on
an open overlap; a concrete ellipsoid specialization proves that the overlap
has positive ambient volume. The density and ambient formulas are exercised
on that refinement without disjointness or seam assumptions, together with
continuity of its chart integrals and continuity and boundedness of the
canonical density; global coarea is also checked on it.
`GraphCoareaRegression.lean` independently restates coarea, spatial and height
absolute integrability, joint measurability, endpoint nullity, original ellipsoid
hypotheses, and a negative collar weight with a discontinuous ambient extension.
The quartic coarea regression retains its critical point and proves that the
selected width stops strictly below it. No regression asserts the still-open
general limit.
`EllipsoidRegression.lean` checks the original ellipsoid contract and
its endpoint examples. `EllipsoidJointRegression.lean` separately checks
regularity, the strict positive angle branch, connectedness, nonconstant weights,
the north-pole area Jacobian, absolute integrability, and the `48π` joint integral.
`NullCapRegression.lean` independently restates the
unchanged null target, specializes the actual four-dimensional interval moment
at `n = 0,1`, checks both weight endpoints, and instantiates the exact reduction
and limit at `T = 2`, `a = 1`.

| File | Checked result | What it does **not** establish |
|---|---|---|
| `BoundaryDraft/Algebra.lean` | BDG coefficient factorization | The exponential-series interchange with an integral |
| same | Interval coefficient cancellation for every natural `n` | The Lorentzian interval moment formula itself |
| same | Plane-cap coefficient recurrence | The beta integral or differentiated series |
| same | Null joint area decomposition | That the two geometric patches have those areas |
| same | Uncut area specialization | The causal-diamond action limit |
| same | Squared angle-weight algebra | The geometric angle relation or positive square-root step |
| `BoundaryDraft/AnalyticCore.lean` | Signed rescaling limit | Integrability of the particular BDG kernel |
| same | Unit-mass specialization | Normalization of the particular BDG kernel |
| `BoundaryDraft/KernelScaling.lean` | Auxiliary-integral scaling; fourth-power and positive-density kernel scaling | Mass one or tail estimates |
| `BoundaryDraft/KernelDerivatives.lean` | Differentiation under the auxiliary integral through order three | The BDG future-cone/action-density identity |
| same | Kernel differentiability and continuity; boundary values | Estimates at infinity |
| same | Exact finite-interval mass and signed first moment | Half-line mass or absolute first-moment integrability by itself |
| `BoundaryDraft/GaussianCancellation.lean` | Exact substitution and absolute Gaussian cancellation estimate | The sharper asymptotic expansion |
| `BoundaryDraft/KernelEstimates.lean` | Explicit absolute `O(u⁻³)` kernel bound; `KernelTailGoal`; vanishing-moment boundary estimate | Graph-cap geometry or its non-collar reduction |
| `BoundaryDraft/KernelHalfLine.lean` | Large-argument limits; absolute integrability and first moment; mass one; `KernelMassGoal`; signed first moment zero | The four-dimensional action reduction |
| same | Concrete positive-half-line signed-rescaling limit | Coarea or either main boundary-limit theorem |
| `BoundaryDraft/GraphGeometry.lean` | Separate reduction/collar APIs, positive-part continuity, open/measurable/bounded cap, compact positive-part support, complete future slices and causal convexity | Regular-collar construction, coarea or a boundary limit |
| `BoundaryDraft/GraphCollar.lean` | Compact/measurable Euclidean joint, uniform noncritical boundary band, ambient C³ regular neighborhoods | Integration charts, normalized surface measure, coarea or a boundary limit |
| `BoundaryDraft/GraphAngle.lean` | Actual Euclidean gradient, uniform strict slope bound, inward/outward unit normals, positive rapidity, face geometry and `coth` identity | Coarea or a deterministic limit |
| `BoundaryDraft/GraphJacobian.lean` | Volume-frame determinant equals the positive Gram area Jacobian divided by the actual gradient norm | A transformation law for Hausdorff measure |
| `BoundaryDraft/HausdorffGraph.lean` | C¹ graph/tangent-image Hausdorff bounds for every subset of a small ball, with sharp relative factors; continuous graphs are measurable embeddings and tangent graph maps are injective | The variable-Jacobian area formula |
| `BoundaryDraft/PlanarIsodiametric.lean` | Sharp Euclidean planar isodiametric inequality on every set, proved by two perpendicular Steiner symmetrizations | A graph-area or coarea formula |
| `BoundaryDraft/HausdorffPlane.lean` | Both inequalities and equality of normalized planar Hausdorff and Lebesgue measures on every set; Lebesgue-null sets are Hausdorff-null | Hausdorff/parametric-area identification on graphs or coarea |
| `BoundaryDraft/HausdorffDensity.lean` | Normalized ambient Hausdorff graph pullback; identification of an absolutely continuous locally finite measure from its almost-everywhere shrinking-ball density | Computation of a particular density by itself |
| `BoundaryDraft/HausdorffLinear.lean` | Exact arbitrary-set area of injective planar linear images and the scalar-graph tangent factor | Nonlinear graph area by itself |
| `BoundaryDraft/HausdorffArea.lean` | Derived local finiteness, absolute continuity, every-point closed-ball ratios, variable-Jacobian scalar-graph area, signed integration and integrability | Collar coarea or ellipsoid parametric measure compatibility |
| `BoundaryDraft/HausdorffAreaLocal.lean` | Localization to an open C¹ domain of a continuous scalar graph, via cutoff extensions and countable gluing | General level-chart integration or height-density continuity |
| `BoundaryDraft/GraphDensity.lean` | Canonical level measures and height density; finite measure and integrability in a noncritical band; exact zero-height boundary value; negative-height vanishing and the two-sided-continuity obstruction; joint neighborhoods contain a thin collar | Coarea or a continuity theorem |
| `BoundaryDraft/GraphChart.lean`, `GraphCoordinateChart.lean` | Neighborhood-level C³ height charts; orthogonal coordinate complements and C¹ inverse extensions | A global flow or global chart |
| `BoundaryDraft/GraphChartTransport.lean`, `GraphSliceTransport.lean` | Actual inverse-frame Jacobian, ambient change of variables, canonical normalized level-measure transport, signed integration and integrability | Global coarea or a limit |
| `BoundaryDraft/GraphAtlas.lean`, `GraphAtlasRepresentation.lean` | Finite atlas of a whole closed collar, smooth subordinate overlap weights, common finite-sum representations on fixed domains, joint local continuity and one uniform integrable dominator | Height Fubini, continuity of the canonical density, or the general limit |
| `BoundaryDraft/GraphDensityRegularity.lean` | Dominated convergence on fixed disks; continuity and measurability of the canonical density on a closed nonnegative collar; a uniform finite bound; the right-hand boundary limit | Global coarea, two-sided continuity, C¹ regularity, a rate, or the general action limit |
| `BoundaryDraft/GraphEndpoints.lean` | Regular levels are volume-null; open/closed collar integral and integrability transport to original spatial coordinates | Nullity of unrelated exterior zeros or coarea by itself |
| `BoundaryDraft/GraphCoarea.lean` | Global collar coarea from the common atlas, justified height Fubini and finite sums, absolute integrability, signed kernel specialization and exact action split | A collar through critical points or the general limit |
| `BoundaryDraft/GraphSurface.lean` | Height-flattening local charts; canonical Hausdorff target with explicit coefficient; finite joint measure; absolute integrability and equality of reciprocal-gradient and angle integrals | Hausdorff/parametric-area identification, coarea, height-density continuity or the general limit |
| `BoundaryDraft/GraphTail.lean` | Absolute scaled tail, exact action collar/remainder split, vanishing spatial remainder allowing critical points | The collar limit |
| `BoundaryDraft/EllipsoidGeometry.lean` | Positive ellipsoid, measurability, boundedness, compact positive-part support, strict Euclidean Lipschitz estimate; instantiation of the general geometry | Sublevel volumes or coarea |
| `BoundaryDraft/GraphExamples.lean` | Full ellipsoid admissibility under the original hypotheses; quartic damped-ellipsoid admissibility and exact reduction | A new limit or joint integral |
| `BoundaryDraft/ConeIntegral.lean` | Exact radial action-density identity by a zero-endpoint primitive; finite-fibre FTC | A boundary limit |
| `BoundaryDraft/SpacetimeIntegration.lean` | Product-measure coordinate decomposition, Fubini, spatial polar integration, and translation of actual BDG integrals | The Poisson-expectation bridge |
| same | `graphCap_graphReduction` and `AdmissibleGraphCap.graphReduction` prove the unchanged `GraphReductionGoal h`; `ellipsoid_graphReduction` remains its original concrete specialization | A boundary limit by itself |
| `BoundaryDraft/EllipsoidIntegration.lean` | Axis determinant, Euclidean superlevel volumes, and exact signed height-integration formula with absolute integrability | General coarea or Lorentzian joint geometry |
| `BoundaryDraft/EllipsoidLimit.lean` | Bounded continuous global weight, exact fixed-half-line rescaling, and `ellipsoidLimitGoal : EllipsoidLimitGoal` | A convergence rate, arbitrary graph caps, or the Poisson bridge |
| `BoundaryDraft/EllipsoidJoint.lean` | Smooth profile, actual Euclidean gradient, nonzero joint differential, inward/outward unit normals, strict `0 < k < 1` | Arbitrary graph profiles |
| `BoundaryDraft/EllipsoidAngle.lean` | Explicit positive rapidity, cosh/sinh/tanh/coth identities, spacelike face tangents and joint orthogonality | Null-angle limits or general joints |
| `BoundaryDraft/EllipsoidSurface.lean` | Global sphere parameterization, cross-product/Gram Jacobian, parametric induced surface measure, integrability and exact variable-angle integral, connected nonconstant-angle joint | General coarea or a Hausdorff-measure identification for arbitrary surfaces |
| `BoundaryDraft/SphereSurface.lean` | Normalized Euclidean Hausdorff sphere area equals the existing polar sphere measure, from hemisphere graph area, radial-sector volume and a finite cover | An arbitrary-surface or coarea theorem |
| `BoundaryDraft/EllipsoidHausdorff.lean` | Canonical and original parametric ellipsoid measures agree under positive-axis hypotheses; subtype/ambient integral and integrability transport; canonical angle and reciprocal-gradient values and concrete limit interpretation | Collar coarea, height-density continuity or the general graph-cap limit |
| `BoundaryDraft/NullGeometry.lean` | Open/measurable/bounded concrete cap, causal transitivity, causal convexity, and complete future slices | Arbitrary null boundaries |
| `BoundaryDraft/CausalInterval.lean` | Four-dimensional polar/null Jacobians and exact standard causal-interval kernel identity by finite primitives | A probability bridge or power-series assumption |
| `BoundaryDraft/IntervalMoments.lean` | Actual four-dimensional causal-interval moment formula for every natural `n` | A separate series interchange (not used by the kernel proof) |
| `BoundaryDraft/LorentzReflection.lean`, `TimelikeInterval.lean` | Audited determinant-one-in-absolute-value rest-frame transport and exact identity for arbitrary timelike endpoints | General curved spacetime |
| `BoundaryDraft/NullBoundary.lean` | The null cone has product Lebesgue measure zero; strict and closed future-tip slices have equal integrals | Boundary distributions or non-Lebesgue measures |
| `BoundaryDraft/NullCoordinates.lean`, `NullCapReduction.lean` | Null-coordinate Jacobian, transverse polar coarea, two dominated Fubini swaps, exact support and logarithmic `nullCapWeight` | A formula assumed from numerical quadrature |
| `BoundaryDraft/NullGaussian.lean` | Unit mass, absolute integrability, exact density rescaling, and half-line Gaussian concentration | A convergence rate |
| `BoundaryDraft/NullCapLimit.lean` | Exact bilocal cancellation, bounded continuous weight extension, absolute integrability, and `nullCapLimitGoal : NullCapLimitGoal` | Poisson variance/convergence, arbitrary null boundaries, or angle interpretation |

The analytic theorem genuinely permits a **signed** kernel. In ordinary
notation it proves

```math
 \int G(u)B(\varepsilon u)\,d\mu(u)
 \longrightarrow B(0)\int G\,d\mu
 \quad(\varepsilon\to0),
```

assuming `G` is integrable and `B` is globally bounded and continuous. There is
no assumption that `G ≥ 0`. The measure `μ` may be Lebesgue measure restricted
to the positive half-line. A bounded continuous extension of the collar
profile fits this theorem; for general graph caps the exact geometric reduction,
scalar-graph area formula, non-collar remainder, one-sided density regularity,
and collar coarea are checked, but the collar action limit still needs a proof.
The theorem `planeKernel_rescaling_limit` now instantiates this lemma with the concrete
BDG kernel and Lebesgue measure restricted to `Ioi 0`, using the proved
absolute integrability and mass one, not additional kernel hypotheses.
`EllipsoidLimit` now applies it to the actual globally extended ellipsoid
weight; no collar/remainder split or global C¹ hypothesis is needed.

`Audit.lean` discovers the public declarations in the imported `BoundaryDraft`
namespace rather than maintaining a theorem allowlist. In addition, the
per-source audit in `check.sh` covers public declarations in unimported files
and other namespaces. Both reject any transitive axiom dependency beyond Lean's
standard `propext`, `Classical.choice`, and `Quot.sound`. Compiler-generated
implementation artifacts are not audit roots; private helper dependencies are
still audited transitively. The checked results contain no `sorry`, `admit`, or
custom axioms. This does not mean that the full research argument has been
checked: the missing theorems are not silently assumed.

## Concrete kernel: what the new proofs establish

`planeKernel_density_scaling` proves equation (14) directly from the defining
integral, for **every** positive density and every real height:

```math
 G_\rho(H)=sG_1(sH),\qquad s=\sqrt{\sqrt\rho}=\varepsilon^{-1}.
```

The radial change of variables is proved first, including oriented integrals
for negative heights. The nonzero linear-chain-rule step is valid even for
Lean's total derivative; it does not hide a differentiability assumption.
The separate `KernelDerivatives` module then proves actual `HasDerivAt`
statements, not just equalities involving a possibly undefined derivative.

For $`z=(\pi/24)\rho H^4(1-v^2)^2`$, the fixed-interval representation is

```math
 F_\rho^{(j)}(H)=4\pi H^{3-j}\int_0^1 v^2 R_j(z)e^{-z}\,dv,
 \quad j=0,1,2,3,
```

where

```math
 R_0=1,\quad R_1=3-4z,\quad R_2=6-36z+16z^2,\quad
 R_3=6-204z+288z^2-64z^3.
```

Joint continuity on a compact parameter rectangle supplies an integrable
uniform bound for each differentiation. This proves
$`F_\rho'(0)=F_\rho''(0)=G_\rho(0)=0`$ and
$`F_\rho'''(0)=8\pi`$, with no positivity assumption on the kernel.
Writing $`c_\rho=\sqrt\rho/(2\pi\sqrt6)`$, the fundamental theorem of
calculus then proves

```math
 \int_0^H G_\rho(u)\,du=c_\rho F_\rho'(H),\qquad
 \int_0^H uG_\rho(u)\,du=c_\rho\bigl(HF_\rho'(H)-F_\rho(H)\bigr).
```

These identities hold for finite $`H`$; they alone do not justify passing to
infinity. That passage is now proved separately as follows, completing the
one-dimensional analytic milestone in
[issue #4](https://github.com/q5m-ai/causal-set-emergence/issues/4).
The exact reduction from `continuumMean` is also now proved for ellipsoids in
[issue #6](https://github.com/q5m-ai/causal-set-emergence/issues/6), as described below.
Neither result completes the boundary-limit program in
[issue #1](https://github.com/q5m-ai/causal-set-emergence/issues/1).

## Half-line estimates and normalization

The proof avoids differentiating the remainder of an asymptotic expansion.
Set $`a=(\pi/24)u^4`$ and substitute $`t=1-v^2`$ in the already-checked
fixed-interval formulas. The substitution is differentiated in the smooth
polynomial direction, so no derivative of a square root at zero is needed.
The two relevant polynomials are instances of

```math
 P_{b,d}(a,t)=b-(2b+3d)at^2+2da^2t^4.
```

For $`a>0`$ and $`b,d\ge0`$, `gaussianCancellation_bound` proves

```math
 \left|\int_0^1\sqrt{1-t}\,P_{b,d}(a,t)e^{-at^2}\,dt\right|
 \le \frac{5b+11d}{2a}.
```

Its proof uses an exact primitive for the constant-weight integral,
$`(bt-dat^3)e^{-at^2}`$, the bound $`|\sqrt{1-t}-1|\le t`$, and an
explicit primitive for the resulting nonnegative absolute envelope. Thus the
estimate controls absolute values rather than merely signed cancellation.
Taking $`(b,d)=(6,8)`$ and $`(2,0)`$, respectively, gives for every $`u>0`$

```math
 |F''(u)|\le\frac{2832}{u^3},\qquad
 |uF'(u)-F(u)|\le\frac{240}{u},\qquad
 |G(u)|\le\frac{1416}{\pi\sqrt6\,u^3}.
```

These loose constants suffice: continuity handles $`[0,1]`$, and comparison
with $`u^{-3}`$ and $`u^{-2}`$ proves integrability of $`G`$ and $`u|G|`$.
The theorem `kernelTailGoal` uses $`C=1416/(\pi\sqrt6)`$ and $`R=1`$.

For normalization, `planeAuxiliary_div_eq_integral` proves

```math
 \frac{F(u)}u=2\pi\int_0^\infty
   \sqrt{1-s/u^2}\,e^{-(\pi/24)s^2}\,ds.
```

Here Lean's real square root is zero for negative inputs; the integrand
vanishes above $`u^2`$. It is dominated by an integrable Gaussian. Dominated
convergence and the half-Gaussian integral yield $`F(u)/u\to2\pi\sqrt6`$.
The second bound above then proves $`F'(u)\to2\pi\sqrt6`$ and
$`uF'(u)-F(u)\to0`$. Only after proving absolute integrability do we pass the
finite-interval identities to infinity, obtaining mass one and signed first
moment zero. `kernelMassGoal` proves the **unchanged** target, including its
absolute first-moment clause.

No additional hypotheses on the concrete kernel are introduced. The sharper
coefficient $`G(u)\sim-2\sqrt6/(\pi u^3)`$, and the derivative remainders
through order three in the draft, are **not** claimed as Lean results.

## Exact general graph-cap action reduction

The focused API in `GraphGeometry.lean` has three predicates:

- `GraphCapData h`: bounded `Ω = {x | 0 < h x}` and global Euclidean
  `κ`-Lipschitz control of `max 0 ∘ h` for some `0 ≤ κ < 1`.
- `GraphCapRegularity h`: C³ locally at every point of the closed positive
  region in Euclidean coordinates; `h = 0` on its boundary; and a nonzero
  actual Fréchet differential at zero-height points in that closure.
- `AdmissibleGraphCap h`: both. No differential condition is imposed at
  positive height. Exterior zeros unrelated to the cap are immaterial.
  `AdmissibleGraphCap.frontier_eq` identifies the boundary with the zero
  level **in the closure of Ω**. Positivity on Ω holds by its definition.

These are geometric/regularity assumptions, not premises encoding a reduction,
limit, coarea identity, or joint integral. The C³-at-closure formulation specifies
an ambient local extension, as needed for a future regular collar, not smoothness
of the positive-part extension across the joint. The exact reduction needs only
`GraphCapData`; it does not use any collar fields or require raw-profile
continuity outside Ω.

```lean
theorem graphCap_graphReduction (h : Spatial → ℝ) (hh : GraphCapData h) :
    GraphReductionGoal h

theorem AdmissibleGraphCap.graphReduction {h : Spatial → ℝ}
    (hh : AdmissibleGraphCap h) : GraphReductionGoal h
```

Euclidean positive-part control proves continuity in the original coordinate
topology. Hence Ω, the positive-part epigraph, and the cap are open and
measurable. Bounded Ω gives compact positive-part support; continuity on its
closure bounds height and gives a compact spacetime box. The epigraph is a
future set by the squared causal inequality, and `graphCap_complete_future`
retains the entire truncated cone, **including the vertex and null points**.
`graphCap_causallyConvex` follows from this exact set equality.

`SpacetimeIntegration` reuses the existing coordinate/Euclidean measure
transformations and concrete cone identity. It proves absolute integrability
of the actual kernel on causal pairs in a compact product box, of each
future-point kernel, and of every continuous function of height on Ω.
`integral_graphCap_depth_of_integrable` supplies profile-independent vertical
Fubini with the Lebesgue-null endpoint replacements and `t ↦ -t` substitution;
`integral_graphCap_depth` supplies its compact domination. Translation then
identifies the actual inner integral with `coneIntegral`, and the existing
finite-fibre FTC yields the unchanged `planeKernel`. Thus, at every `ρ > 0`,

```text
continuumMean ρ (graphCapRegion h) = ∫ x in {x | 0 < h x}, planeKernel ρ (h x).
```

This reduction is deterministic and finite-density only. The separate general
angle, canonical boundary-integral identities, and collar coarea are checked,
but the collar limit, arbitrary null boundaries, and the Poisson-expectation
bridge are not proved here.

### Compact joint and noncritical band (#19 prerequisite layer)

`GraphCollar.lean` defines `graphJoint h` as the zero level in the Euclidean
closed positive region. It proves equality with the Euclidean frontier and
compactness/measurability, transferring compactness through the coordinate
homeomorphism without identifying the Euclidean norm with the coordinate sup
norm. Local C³ regularity makes the actual differential continuous on that
compact region. Its critical set is compact and has strictly positive height;
the extreme value theorem therefore gives `δ > 0` such that `dh ≠ 0` wherever
`h ≤ δ` in the closed positive region. The empty critical set is allowed.
Ambient open C³ neighborhoods with nonvanishing differential are also proved.

### General angle, surface area, level density, and remainder (#19)

`GraphAngle.lean` defines `graphGradient` by Riesz duality from the actual
Fréchet differential. On the open positive region, the positive-part Lipschitz
bound controls the raw profile's differential. Continuity of that differential
extends the same strict bound to the closure; this does not differentiate the
nonsmooth positive part at the joint. Boundary regularity then gives
`0 < graphSlope h x < 1`. The inward/outward normals have norm one and
height derivatives equal to the positive/negative slope. The existing generic
hyperbolic identities give strict positive rapidity and `coth θ = 1/‖∇h‖`.
The face directions are orthogonal to the tangent kernel and their normalized
Minkowski inner product is `−cosh θ`. No angle relation is a premise.
`GraphJacobian.lean` also derives the local coarea factor: for a height frame
with `dh z = 1` and `dh v = dh w = 0`, the absolute three-dimensional determinant
is the positive square root of the tangential Gram determinant divided by
`‖∇h‖`. This is checked linear algebra, not yet a surface-measure transformation.

`GraphSurface.lean` constructs height-flattening partial homeomorphisms with
two-dimensional tangent coordinates using the implicit function theorem. The
central level parametrization is strictly differentiable at its base point,
with derivative tangent inclusion; therefore it is Lipschitz on a neighborhood.
Hausdorff measure of its image is bounded by a finite Lipschitz factor times
the finite measure of a ball in that two-dimensional kernel. Compactness of
the joint then proves finite two-dimensional Hausdorff measure globally.

`graphSurfaceMeasure h` is `(π/4) • μH[2]` restricted to `graphJoint h` in
Euclidean space. This explicitly states the intended area convention: pinned
mathlib uses unnormalized squared diameters. **Scalar-graph parametric area is
now identified with this normalized Hausdorff convention. Agreement with the
existing polar-sphere-based ellipsoid measure is also proved in
`EllipsoidHausdorff.lean`.** Finiteness of this declared measure, continuity and
absolute integrability of the reciprocal-gradient weight, integrability of
the angle weight, and equality of their integrals are proved independently.
`graphBoundaryIntegral` is the reciprocal-gradient integral, and
`GraphCapLimitGoal h` states convergence of the unchanged `continuumMean` to
that integral. The latter is an **open general proposition definition, not a
general theorem**; `ellipsoid_canonical_limit` supplies its concrete ellipsoid
instance by reusing the existing deterministic limit.

`HausdorffGraph.lean` now proves the local tangent-to-graph comparison from
C¹ regularity, without assuming a surface transformation. For a scalar graph
`F(x) = (g(x), x)` and its actual Euclidean derivative `A = DF(a)`, every
`0 < ε < 1` admits a ball about `a` such that, for **every** subset `s` of it,

```text
(1 − ε)² μH[2](A '' s) ≤ μH[2](F '' s) ≤ (1 + ε)² μH[2](A '' s).
```

Strict differentiability supplies the uniform linear approximation, and the
graph derivative does not contract vectors. The correspondence of the two
images and its inverse therefore have the required Lipschitz bounds. The
Hausdorff image estimates and cancellation are checked even for infinite
measures. Domain and codomain are `EuclideanSpace`, so this is not a
supremum-norm substitute for the needed estimate. The passage from these local
bounds to the scalar-graph variable-Jacobian area formula is now checked in
`HausdorffLinear`, `HausdorffArea`, and `HausdorffAreaLocal`, as described below.

`HausdorffPlane.lean` separately proves the **covering half** of normalization:
`(π/4) μH[2](s) ≤ volume(s)` for every subset of the Euclidean plane.
Besicovitch supplies full disk coverings with arbitrarily small radii and
summed area at most `volume(s) + ε`; the Hausdorff covering limit and the
checked disk-area formula yield the bound. This handles the null remainder
explicitly: a Lebesgue-null planar set has zero Hausdorff measure.

`PlanarIsodiametric.lean` now proves the sharp reverse ingredient
`volume(s) ≤ (π/4) ediameter(s)²` for every planar set. For a compact convex
set, two perpendicular Steiner symmetrizations preserve area by Fubini and do
not increase Euclidean diameter. The centrally symmetric result lies in a disk
of half the diameter. Bounded arbitrary sets pass to their closed convex hull,
which has the same diameter; unbounded sets have infinite extended diameter.
`volume_le_normalized_hausdorff_plane` applies `Measure.le_hausdorffMeasure` to
scaled volume, and `normalized_hausdorff_plane_eq_volume` identifies the
measures. `normalized_hausdorff_plane_eq_volume_apply` holds on every set,
without measurability or finiteness hypotheses. No normalization or
isodiametric premise is assumed. This normalization is reused, not reproved, in
the graph-area argument.

`HausdorffLinear.lean` identifies the range of each injective map from the
Euclidean plane with an orthonormal two-dimensional coordinate space.
Isometry invariance transports Hausdorff measure to that plane; the existing
normalization and Haar determinant law then give exact image area on every
set. The determinant squared is the tangential Gram determinant. For
`surfaceGraphDerivative L`, the factor is `sqrt (1 + ‖L‖²)`. No ambient volume
restricted to a two-plane is used.

`HausdorffArea.lean` combines this calculation with the local distortion
bounds. Local domination proves local finiteness and absolute continuity;
shrinking closed-ball ratios converge at every point to the actual graph
Jacobian. Only then does the density uniqueness theorem identify the pullback
with `volume.withDensity (ENNReal.ofReal ∘ surfaceGraphJacobian g)`.
Pushforward, signed integral, and absolute-integrability identities follow.
`HausdorffAreaLocal.lean` constructs global C¹ cutoff representatives of local
germs and glues the measure identities over a countable cover. Consequently a
continuous scalar graph needs C¹ regularity only on the open domain of
integration, not outside it. `SphereSurface` and `EllipsoidHausdorff` reuse this
formula to identify the existing ellipsoid polar parameterization below.
`GraphCoarea` below now derives integration of a regular height collar.

`GraphDensity.lean` defines `graphLevel h s` inside `graphClosedPositive h`,
`graphLevelMeasure h s` by normalized Hausdorff restriction, and
`graphHeightDensity h s` by integrating the reciprocal actual gradient norm.
The implicit-function argument proves finite surface measure on every regular
level. Compactness and continuity give absolute integrability; the existing
noncritical band supplies these facts on every level of one band. At zero,
the measure equals `graphSurfaceMeasure h` and the density equals
`graphBoundaryIntegral h`, hence the variable-angle boundary integral. Every
open neighborhood of the compact joint contains a sufficiently thin closed
positive collar. Negative-height levels have zero measure and zero density,
so two-sided continuity would force the boundary integral to be zero. These
three density lemmas are selectively reused from draft PR #29 by #34.
`GraphDensityRegularity` supplies the uniform collar bound and one-sided
continuity from the atlas below. The density's role in global coarea is proved
separately in `GraphCoarea`.

### Controlled collar atlas and common transport API (#31)

`GraphChart.lean` upgrades the existing implicit chart to C³ on open source
and target neighborhoods using `PartialHomeomorph.contDiffAt_symm`.
`GraphCoordinateChart.lean` chooses a nonzero coordinate of the actual
differential and retains the other two orthogonal coordinates. This makes each
inverse slice a scalar graph after an ambient isometry, rather than assuming
an area law for the implicit theorem's unspecified complement. A C¹ cutoff
extension supplies globally continuous scalar representatives without imposing
regularity outside the chart.

`GraphChartTransport.lean` differentiates the inverse identities throughout
the target, proves its determinant nonzero, and invokes
`graph_coarea_frame_jacobian` for the ambient transformation.
`GraphSliceTransport.lean` reuses the checked scalar-graph area theorem and
isometry invariance to transport exactly `graphLevelMeasure`, with the same
Jacobian. Nonnegative chart heights belong to `graphClosedPositive`; at zero
this is proved by approaching from positive chart heights. No exterior-zero,
normalization, or surface-transport premise is added.

`AdmissibleGraphCap.exists_controlledCollarAtlas` constructs a
`ControlledCollarAtlas h`. Compactness selects finitely many joint-centered
patches; the thin-collar theorem extends their cover to a whole closed collar,
strictly inside the noncritical band. A smooth partition of unity is subordinate
to these patches and sums to one on the entire collar, including both endpoints.
There is no disjointness, multiplicity bound, or discarded-seam assumption.
Every chart uses a fixed planar disk, with a compact height/disk rectangle
strictly inside its controlled target.

The downstream API in `GraphAtlasRepresentation.lean` is:

- `A.integral_closedCollar_eq_sum`: an absolutely integrable ambient collar
  contribution is a finite sum of weighted chart integrals;
- `A.graphHeightDensity_eq_sum`: the canonical level density is the sum of
  integrals of those same weighted Jacobians over fixed planar disks;
- `A.continuousOn_localTerm` and `A.integrableOn_localTerm`: joint continuity
  on the compact parameter rectangles and absolute integrability; and
- `A.exists_uniform_integrable_dominator`: one positive constant, independent
  of height and chart index, dominates every local term and is integrable on
  every fixed finite-measure disk.

These are proved from unchanged `AdmissibleGraphCap` hypotheses. The atlas
records only geometric charts and partition data, not assumed transformation
laws. This representation API stops before height Fubini for #33 and limit
assembly for #32; the downstream regularity argument for #34 is now checked
as described next. It does not modify the separate ellipsoid
measure-compatibility theorem completed in #30, and positive-height critical
points beyond the selected collar remain permitted.

### One-sided canonical density regularity (#34)

`GraphDensityRegularity.lean` applies dominated convergence to each
`A.localTerm` on its fixed planar disk. `A.continuousOn_localTerm` gives
pointwise continuity in height, including both endpoints, and
`A.exists_uniform_integrable_dominator` supplies the height-independent
integrable bound. `A.graphHeightDensity_eq_sum` then transfers continuity of
the finite sum to the **existing canonical density**. The proved smooth
partition weights account for all overlaps; no disjointness, multiplicity,
or discarded-seam premise is introduced.

`A.continuousOn_graphHeightDensity` holds on `Icc 0 A.width`. It yields Borel
measurability on the interval subtype, almost-everywhere strong measurability
for restricted Lebesgue measure, a measurable zero cutoff, and a uniform
positive finite bound by compactness. Atlas construction removes the atlas
premise in `AdmissibleGraphCap.exists_regular_heightDensity_band`.
The boundary consequences are:

```lean
theorem AdmissibleGraphCap.continuousWithinAt_graphHeightDensity_zero
    {h : Spatial → ℝ} (hh : AdmissibleGraphCap h) :
    ContinuousWithinAt (graphHeightDensity h) (Set.Ici 0) 0

theorem AdmissibleGraphCap.tendsto_graphHeightDensity_zero
    {h : Spatial → ℝ} (hh : AdmissibleGraphCap h) :
    Tendsto (graphHeightDensity h) (𝓝[≥] 0) (𝓝 (graphBoundaryIntegral h))
```

The last step reuses `graphHeightDensity_zero`; it does not introduce a new
boundary value or any field in `AdmissibleGraphCap`. The unequal-axis example
has right limit `48π` and is not two-sided continuous at zero. The quartic
example retains its positive-height critical point outside the controlled
collar, and the overlapping-atlas regression exercises the same convergence
argument after duplicating every chart with half weights. No global density
regularity, C¹ theorem, coarea, action limit, or rate is asserted.

### Global collar coarea (#33)

`GraphCoarea.lean` integrates the common atlas representation in height.
Continuity of the test weight is required only on the selected closed height
interval; no sign condition or global continuation is needed. Compactness of
each fixed height/disk rectangle proves joint measurability and absolute
integrability before Fubini. The resulting height functions are integrable
before the finite sum is interchanged with the height integral. The sum is
identified with the existing `graphHeightDensity`, using canonical slice
transport rather than a coarea-defined replacement density.

`GraphEndpoints.lean` selectively reuses only the endpoint/null-level lemmas
from draft PR #29. Finite two-dimensional Hausdorff measure makes regular
levels null for three-dimensional volume. This removes both endpoints inside
the closed positive region; the raw zero set outside that closure is never
assumed null. The measure-preserving Euclidean/spatial identification returns
the result to the original product Lebesgue measure. Atomlessness removes the
one-dimensional interval endpoints.

`AdmissibleGraphCap.exists_collar_coarea` constructs a positive noncritical
width, common to all continuous-on-the-collar test weights. It supplies both
spatial `IntegrableOn` and height `IntervalIntegrable` proofs, and the identity:

```lean
(∫ x : Spatial in {x | 0 < h x ∧ h x < δ}, f (h x)) =
  ∫ t in (0 : ℝ)..δ, f t * graphHeightDensity h t
```

For any constructed atlas `A`, `A.integral_openCollar_profile` supplies the
same identity at `A.width`. `exists_planeKernel_collar_coarea` supplies one
width for every positive density, retaining the signed kernel.
`A.continuumMean_eq_height_collar_add_remainder` rewrites the exact action
split with this height integral; the remainder may still contain critical
points. No coarea field, equivalent premise, or stronger graph-cap hypothesis
is introduced. Density regularity (#34) is separately checked; final limit
assembly (#32) remains an open obligation.

`GraphTail.lean` proves the scaled bound with the concrete constant
`C = 1416/(π sqrt 6)` and width `ε = (sqrt (sqrt ρ))⁻¹`. On `h ≥ δ > 0`, the
norm of the remainder integral is bounded by `C ε² δ⁻³ volume(Ω)` and hence tends
to zero. Absolute integrability and measurability are proved without continuity
of the raw profile outside its positive set. The exact four-dimensional action
is split into `0 < h < δ` and `h ≥ δ`; the endpoint remains in the remainder,
so no level-set-nullity premise is used. No differential or coarea assumption
is used for this entire tail argument, even at the quartic critical height.

Issue #19's prerequisite layer is complete in PR #21. Milestone 5 remains
incomplete: collar coarea (#33) and one-sided density regularity (#34) now
have checked declarations; collar limit assembly (#32) remains open. The
independent ellipsoid measure task split into #30 has checked declarations in
`EllipsoidHausdorff`. No structure
field or hypothesis assumes the remaining results. None of the original action
or concrete limit definitions changes.

### Ellipsoid compatibility and a nonquadratic example

`ellipsoid_admissible` uses the already-proved smoothness and nonzero joint
differential from `EllipsoidJoint`. It adds no axis hypotheses. The original
concrete reduction remains available with its unchanged statement:

```lean
theorem ellipsoid_graphReduction (a : ℝ) (b : Fin 3 → ℝ)
    (ha : 0 < a) (hb : ∀ i, 2 * a < b i) :
    GraphReductionGoal (ellipsoidProfile a b)
```

It proves equality at **every positive density**, not just asymptotically.
`continuumMean`, `graphCapRegion`, `ellipsoidProfile`, `bdgKernel`, `planeKernel`,
and the target proposition are unchanged. No future-slice, density-identity,
or reduction premise is introduced.

1. **Geometry.** Positivity is equivalent to `∑ (x i / b i)^2 < 1`.
   Continuity gives measurability; the positive set is contained in `Icc (-b) b`,
   and the positive part has compact support. For a smallest axis `m`, its
   global Euclidean Lipschitz constant is `κ = 2*a/m < 1`, including pairs
   outside the ellipsoid. The raw quadratic is not asserted to be Lipschitz.
   `spatialDistance_sq` identifies this Euclidean metric with the spatial
   quadratic form in `causalFuture`, rather than the coordinate supremum norm.
   The positive-part epigraph is a future set; `ellipsoid_complete_future`
   proves the exact cap/causal intersection, with null points and vertex
   retained, and `ellipsoid_causallyConvex` proves causal convexity.
2. **Analytic cancellation.** `coneRadialSlice_eq_radial` justifies `r = H*v`.
   With `k = (π/24)*ρ*H⁴`, `w = 1-v²`, `z = k*w²`, and
   `R₃ = 6-204z+288z²-64z³`, the primitive

   ```text
   M(v) = 2*v³*w*(-8*z²*(w+1) + 2*z*(15*w+14) - 15*w - 12)*exp(-z)
   ```

   vanishes at both endpoints and has derivative
   `v²*(w²*(R₃'-R₃)(z) + 48*P(z))*exp(-z)`.
   Compact-rectangle dominated differentiation and the FTC therefore give
   `Fρ''''(H) = -8πρ * coneRadialSlice ρ H`. Integrating from zero, retaining
   the checked `Fρ'''(0) = 8π`, proves the exact radial density identity.
   This replaces the previously unformalized exponential-series/beta exchange
   with a finite exact argument; algebraic recurrences alone are not used as
   an analytic justification.
3. **Measures and Fubini.** A measure-preserving equivalence splits `Fin 4 → ℝ`
   into time and three spatial coordinates. Another identifies spatial product
   Lebesgue measure with Euclidean volume. Polar integration uses the checked
   three-ball volume `4π/3`, giving the angular factor `4π`. Continuous
   integrands on explicit compact boxes supply absolute integrability before
   either Fubini interchange. Endpoint replacements use the atomlessness of
   Lebesgue measure. Thus `coneIntegral_eq_radial` identifies the actual
   four-dimensional cone integral, and `planeAuxiliaryThird_eq_coneIntegral`
   proves `Fρ'''(H)/(8π) = 1 - ρ*Qρ(H)` for every finite `H ≥ 0`.
4. **Original action.** Translation invariance and the complete-future theorem
   identify the inner integral in `continuumMean`. The exact spatial/vertical
   decomposition is now the general `integral_graphCap_depth`; the old
   `integral_ellipsoid_depth` keeps its weaker positive-axis hypotheses via the
   shared integrable-fibre lemma. Finally the FTC and `Fρ''(0) = 0` give the
   existing `planeKernel ρ (h x)` along each fibre.

No strengthened geometric hypotheses were needed. This exact reduction is
reused, rather than assumed or redefined, in the ellipsoid-limit proof below.
The distinct concrete null-cap reduction is proved separately rather than
forced through the graph-cap infrastructure.

`GraphExamples` also admits `dampedEllipsoidProfile a b = e - e²`, where
`e = ellipsoidProfile a b`, under the original axes and `a ≤ 1/2`. It has the
same positive region, remains strictly Lipschitz after positive-part extension,
and has the original differential at height zero. The regression with
`a = 1/4`, `bᵢ = 1` proves admissibility, exact reduction, value `3/16` and
zero differential at the origin, and inequality with **every** quadratic
`ellipsoidProfile a b`. Thus interior critical points are genuinely admitted,
and the general result is exercised on a non-ellipsoidal graph profile.

## Explicit ellipsoid integration and continuum limit

`EllipsoidIntegration.lean` proves, for positive axes and `a > 0`,

```math
 |\{x:s<h(x)\}|=\frac{4\pi}{3}\Bigl(\prod_i b_i\Bigr)
   \sqrt{1-s/a}^{\,3},\qquad 0\le s\le a.
```

At and above `s = a` the strict superlevel set is empty. The coordinate map
`x_i ↦ x_i/b_i` has diagonal determinant `∏ b_i⁻¹`; mathlib's Lebesgue
transformation law supplies the axis factor, and a measure-preserving
identification with Euclidean space supplies the three-ball volume. Neither
volume identity is an assumption. Spheres have zero spatial measure, so open
and closed radial domains give the same integrals, including radius zero.

For **every globally continuous real integrand** `f`, including `planeKernel ρ`,
`integral_ellipsoid_profile` proves the exact signed formula

```math
 \int_{h>0}f(h(x))\,dx
 =C\int_0^a\sqrt{1-s/a}\,f(s)\,ds,
 \qquad C=\frac{2\pi\prod_i b_i}{a}.
```

Continuous integrands on the explicit compact spatial box are absolutely
integrable. The weighted finite-interval integrand is continuous, including
both endpoints. After diagonal and radial integration, the substitution is
proved in the **polynomial direction** `t = 1-r²`, followed by `s = a*t`.
There is no differentiation of the square root at the interior critical
height `s = a`, nor an assumption that this weight is globally C¹.

`EllipsoidLimit.lean` uses the global extension

```math
 B(s)=C\sqrt{\bigl(1-\max(0,s)/a\bigr)_+}.
```

It is continuous, satisfies `|B(s)| ≤ |C|`, is constant for `s ≤ 0`, and
vanishes for `s ≥ a`. The exact height formula and checked
`ellipsoid_graphReduction` therefore give, at every positive density,

```math
 \mathrm{continuumMean}_\rho(M_h)
 =\int_0^\infty G(u)B(\varepsilon u)\,du,
 \qquad \varepsilon=\bigl(\sqrt{\sqrt\rho}\bigr)^{-1}.
```

The half-line extension adds only zeros. The original weighted half-line
integral is absolutely integrable by compactness and its zero tail; the
rescaled integral is dominated by the checked integrable function `|C| |G|`.
`planeKernel_density_scaling` and positive linear substitution justify the
fixed-domain identity. Continuity of square root at zero and the reciprocal
limit prove `ε → 0` as `ρ → ∞`; positive density holds eventually. Finally
`planeKernel_rescaling_limit` gives `B(0) = C`, proving
`ellipsoidLimitGoal : EllipsoidLimitGoal` under the original hypotheses.
This retains the **entire signed kernel**, including its negative tail, and
controls the whole ellipsoid, not just a collar. No rate is asserted.

## Concrete ellipsoid joint geometry and variable-angle integral

This is a separate interpretation of the existing `ellipsoidLimitGoal`, not a
new proof or modification of that deterministic target. `EllipsoidJoint` works
in `EuclideanSpace ℝ (Fin 3)` and differentiates the **existing**
`ellipsoidProfile` after the coordinate identification. It proves smoothness,

```text
∇h(x)ᵢ = −2 a xᵢ / bᵢ²,
J = {x | ∑ (xᵢ/bᵢ)² = 1} = {x | h(x) = 0}.
```

The gradient and actual Fréchet differential are nonzero everywhere on `J`.
The inward normal is `n = ∇h / ‖∇h‖`, and the outward normal is `−n`; both have
norm one. Their directional derivatives are respectively `k` and `−k`, where
`k = ‖∇h‖`. The original hypotheses `a > 0` and `bᵢ > 2a` prove `0 < k < 1`.

`EllipsoidAngle` uses the explicit rapidity

```text
θ = log ((1+k) / sqrt(1-k²)) > 0.
```

It proves `cosh θ = 1/sqrt(1-k²)` and `sinh θ = k/sqrt(1-k²)` separately,
then `tanh θ = k` and `coth θ = 1/k`. The face-tangent vectors `(0,n)` and
`(−k,n)` are orthogonal to every joint tangent in `ker dh`; their Minkowski
squares are `−1` and `−(1−k²)` in signature `(+---)`. The normalized vectors
are unit spacelike with inner product `−cosh θ`. No geometric relation is a
premise, and the old squared algebra lemma is not used to select a sign.

`EllipsoidSurface` uses the **entire unit sphere** as parameter space. The
map `Φ(u)ᵢ = bᵢ uᵢ` is a checked homeomorphism onto `J`, with inverse
`uᵢ = xᵢ/bᵢ`; its ambient derivative is the diagonal linear map. For every
oriented unit-area tangent frame `v × w = u`, the cofactor identity proves

```text
DΦ(v) × DΦ(w) = (∏ bᵢ) (uᵢ/bᵢ),
Jac₂ Φ(u) = (∏ bᵢ) ‖(uᵢ/bᵢ)‖ > 0.
```

The Jacobian is also proved equal to the positive square root of the induced
metric's Gram determinant. The explicit **parametric induced surface measure**
`ellipsoidSurfaceMeasure` transports `Jac₂ Φ · volume.toSphere` through this
global homeomorphism. Here `volume.toSphere` is mathlib's Euclidean polar surface
measure, defined from radial sectors with checked polar disintegration; its
mass `4π` follows from the three-ball volume, not an assumed ellipsoid-area
formula. This representation does not assert a separate equivalence with
Hausdorff measure on arbitrary surfaces.

Continuity proves Jacobian measurability, and the homeomorphism supplies the
exact measure transport. There are **no discarded poles, seams, or null-boundary
replacements**: the parameterization is global and includes every joint point.
Pointwise positive-branch cancellation gives

```text
Jac₂ Φ(u) coth θ(Φ(u)) = (∏ bᵢ) / (2a).
```

Finite spherical area proves absolute integrability before evaluation. Thus
`integral_ellipsoid_coth` gives `∫_J coth θ dA = 2π (∏ bᵢ)/a`.
`ellipsoid_limit_eq_joint_integral` rewrites the already-proved deterministic
limit using this identity. Connectedness follows from the sphere homeomorphism.
At axis endpoint `j`, the weight is `bⱼ/(2a)`, so distinct axes give distinct
weights on that connected surface. The original `(1/4, ![1,2,3])` regression
retains the deterministic `48π` limit and separately checks the same joint
integral, slopes `1/2` and `1/6`, and weights `2` and `6`.

### Canonical/parametric ellipsoid compatibility (#30)

`SphereSurface` applies the checked scalar-graph area formula to an upper
hemisphere. The radial filling has volume Jacobian `r² / sqrt(1 - ‖y‖²)`;
ordinary three-dimensional change of variables and Tonelli identify graph
area with three times radial-sector volume. A finite isometric hemisphere
cover proves equality with mathlib's existing `volume.toSphere` on the entire
sphere. This is a measure identity, not just a total-area calculation.

`EllipsoidHausdorff` writes the upper ellipsoid as a scalar graph over the
axis-scaled disk. Its local density agrees with the original
`ellipsoidSurfaceJacobian` by the already checked tangent-frame theorem.
Negation treats the lower hemisphere. The equator has zero canonical area by
planar normalization, and its linear image is proved null by a Lipschitz
Hausdorff estimate. These local identities give the following global theorem
under merely positive axes:

```lean
theorem normalizedHausdorffTwo_restrict_ellipsoidJoint
    (b : Fin 3 → ℝ) (hb : ∀ i, 0 < b i) :
    normalizedHausdorffTwo.restrict (ellipsoidJoint b) =
      Measure.map (Subtype.val : ellipsoidJoint b → JointSpace)
        (ellipsoidSurfaceMeasure b hb)
```

`normalizedHausdorffTwo_comap_ellipsoidJoint` expresses the same identity on
the joint subtype. Nonnegative and signed integrals, and absolute
integrability, transport for arbitrary observables, including functions
defined only on the subtype. `graphSurfaceMeasure_ellipsoid` connects the
unchanged general graph-cap measure to this identity. Under the original
`a > 0`, `bᵢ > 2a` hypotheses, `integral_ellipsoid_canonical_coth` and
`graphBoundaryIntegral_ellipsoid` recover `2π (∏ bᵢ) / a` by reusing the
parametric evaluation. `ellipsoid_canonical_limit` rewrites the original
concrete limit with that canonical boundary value. The independent regression
checks both canonical `48π` integrals and the unchanged nonconstant endpoints.
These measure-compatibility theorems do not themselves prove collar coarea,
height-density continuity, or a general deterministic limit.

## Exact null-cap reduction and Gaussian limit

The null proof starts from the unchanged `nullCapRegion`, `continuumMean`,
`bdgKernel`, and `NullCapLimitGoal`. For `0 < a < T`, `NullGeometry` proves the
strict cap open, bounded, causally convex, and gives its exact complete future
slice. `NullBoundary` proves the omitted future null cone has four-dimensional
product Lebesgue measure zero. Thus `nullCap_future_kernel_identity` can use the
closed causal interval without silently changing the integral.

`CausalInterval` derives the standard interval integral in spatial polar and
radial null coordinates. The null matrix has checked determinant one, and two
explicit finite primitives prove, for every `ρ,T > 0`,

```math
 \rho\int_{I(x,q)}K\!\left(\frac\pi{24}\rho\tau_{xy}^4\right)dy
 =1-\exp\!\left(-\frac\pi{24}\rho\tau_{xq}^4\right).
```

No exponential-series/integral interchange is used. `IntervalMoments`
independently proves the actual four-dimensional moment formula for every
natural `n`; the focused regression checks `n=0` and `n=1`.
`LorentzReflection` and `TimelikeInterval` transport the standard identity to
arbitrary future-timelike endpoints using an explicit involutive Lorentz
reflection whose determinant and time orientation are proved.

For the cap itself, `NullCoordinates` proves the four-coordinate Jacobian and
two-dimensional transverse polar formula. `NullCapReduction` identifies the
remaining rectangle `0<u<T/√2`, `0<v<a/√2`; all integrands are dominated on
explicit compact boxes before each Fubini swap. Evaluating the two fibres,
including `σ=0` separately, yields in the actual spacetime measure

```math
 \int_{M_{T,a}} f(\tau_{x0}^2)\,dx
 =\int_0^{aT} f(\sigma)W_{T,a}(\sigma)\,d\sigma,
```

with zero support above `aT` and

```math
 W_{T,a}(\sigma)=\frac\pi4\left[
 a(2T-a)-2(1-a/T)\sigma-\frac{\sigma^2}{T^2}
 -2\sigma\log\frac{aT}{\sigma}\right]
```

for `0 < σ < aT`, while `W(0)=πa(2T-a)/4`. Measurability, endpoint continuity,
finite support, and absolute integrability are checked. The global analytic
extension clamps `σ` to `[0,aT]`; it is continuous, bounded, equals the geometric
weight for every `σ≥0`, is constant to the left, and vanishes to the right.

The interval identity cancels the signed bilocal term exactly, before any
limit, to

```math
 \mathrm{continuumMean}_\rho(M_{T,a})
 =\frac4{\sqrt6}\sqrt\rho\int_0^\infty
 e^{-(\pi/24)\rho\sigma^2}W_{T,a}(\sigma)\,d\sigma.
```

`NullGaussian` proves absolute integrability, mass four after the displayed
prefactor, the `ρ^{-1/2}` change of scale, finite-support domination, and
concentration at zero. Consequently `nullCapLimitGoal : NullCapLimitGoal`
proves the unchanged target with limit `4W(0)=πa(2T-a)`. This is deterministic:
it does not establish the Poisson-expectation bridge, variance, convergence in
probability, a general graph-cap limit, arbitrary null boundaries, or the
Lorentzian angle/joint interpretation. No quantitative rate is claimed.

## The actual main targets, not weakened substitutes

`BoundaryDraft/Specification.lean` defines:

- Four spacetime coordinates with **product Lebesgue measure**.
- The causal relation using the Minkowski quadratic form, explicitly, rather
  than confusing the coordinate function space's norm with a Lorentzian norm.
- The actual bilocal deterministic continuum mean action, `continuumMean`.
- The null-plane-truncated region and ellipsoidal graph-cap family.
- The concrete auxiliary integral and its second derivative defining the
  signed kernel.

For example, the first full target is expressed as:

```lean
def NullCapLimitGoal : Prop :=
  ∀ T a : ℝ, 0 < a → a < T →
    Tendsto (fun ρ => continuumMean ρ (nullCapRegion T a))
      atTop (𝓝 (nullJointArea T a))
```

The variable-angle family's full target is:

```lean
def EllipsoidLimitGoal : Prop :=
  ∀ (a : ℝ) (b : Fin 3 → ℝ), 0 < a → (∀ i, 2 * a < b i) →
    Tendsto (fun ρ => continuumMean ρ (graphCapRegion (ellipsoidProfile a b)))
      atTop (𝓝 (2 * Real.pi * (∏ i : Fin 3, b i) / a))
```

These `Goal` declarations are **definitions of propositions, not themselves
proofs**. The unchanged goals now have proof terms `ellipsoidLimitGoal` and
`nullCapLimitGoal`. `GraphReductionGoal h` now has a proof for every member
of `GraphCapData h` (hence every `AdmissibleGraphCap h`), not for unrestricted
profiles. `ellipsoid_graphReduction` remains the concrete specialization. The original
`KernelMassGoal` and `KernelTailGoal` also have proof terms, `kernelMassGoal` and
`kernelTailGoal`. All are audited transitively with the rest of the library.

The continuum action is not defined to be its conjectured answer. Both limit
proofs start from the actual four-dimensional integral, not a reformulated
target or an assumed geometric reduction.

## Remaining proof graph

1. **Probability bridge, separate milestone.** Define Poisson sprinkling,
   interval counts, and the discrete BDG action; derive `continuumMean` as its
   expectation. Neither deterministic limit by itself proves that bridge,
   variance bounds, or convergence in probability.
2. **Concrete deterministic limits: completed.** The full ellipsoid and
   null-plane-cap reductions and limits are proved under their original
   hypotheses. The null proof includes causal convexity, complete interval
   slices, boundary null sets, coordinate Jacobians, exact weight, domination,
   and Gaussian concentration.
3. **Concrete kernel estimates: completed.** `KernelMassGoal`,
   `KernelTailGoal`, the required limits, and the signed graph-cap rescaling
   theorem are proved. The sharper differentiable asymptotic expansion remains
   draft-level and is not needed by either checked limit.
4. **General graph caps: exact reduction completed; limit open.** The admissible
   API, complete slices, causal convexity, compact domination, and exact
   four-dimensional action reduction are checked, with ellipsoid and quartic
   instances. Compact joints, the noncritical band, local height charts, and
   the vanishing non-collar remainder are now checked. Planar normalization,
   tangent area, the scalar-graph area formula, and ellipsoid measure
   compatibility are also proved. A finite controlled collar atlas now supplies
   both local measure transports, smooth overlap weights, and uniformly
   dominated finite-sum representations. One-sided canonical density continuity,
   collar measurability, and a uniform bound are now proved from that API.
   Global collar coarea, including endpoint replacements and the signed kernel
   specialization, is also derived from those representations. The collar
   limit is still needed.
5. **Concrete ellipsoid interpretation completed; general pointwise geometry checked.**
   The positive-angle identity now holds for every admissible graph cap.
   Its two finite canonical boundary integrals are equal. Identification with
   the existing ellipsoid parametric measure and the concrete ellipsoid limit
   is now checked; identification with a general deterministic limit remains
   open. Arbitrary null boundaries and induced null-joint area also remain
   open. The checked
   equality to `nullJointArea` still uses its existing explicit algebraic
   definition, not a theorem about induced null-joint geometry.
6. **Beyond the present scope.** Curved spacetime, other dimensions,
   tangential/degenerate joints, and quantitative convergence rates remain
   outside the checked claims.

The two concrete deterministic milestones and the ellipsoid geometric
interpretation, plus the general graph-cap exact reduction, are complete and
audited, including canonical/parametric ellipsoid measure compatibility.
General graph-cap collar coarea and one-sided height-density continuity are
also checked. The collar limit, arbitrary null boundaries, induced null-joint
geometry, and the probability bridge remain separate tasks.

## Reproduce

With Lean/elan installed and the pinned toolchain selected by `lean-toolchain`:

```sh
cd formal
# The committed manifest pins dependencies. Avoid fetching all of mathlib's
# cache; the modules below are sufficient for the checked layer.
MATHLIB_NO_CACHE_ON_UPDATE=1 lake update
lake exe cache get \
  Mathlib.MeasureTheory.Integral.DominatedConvergence \
  Mathlib.MeasureTheory.Measure.Lebesgue.Basic \
  Mathlib.Analysis.Calculus.Deriv.Basic \
  Mathlib.Analysis.Calculus.Deriv.Comp \
  Mathlib.Analysis.Calculus.Deriv.Mul \
  Mathlib.Analysis.Calculus.Deriv.Pow \
  Mathlib.Analysis.Calculus.ParametricIntervalIntegral \
  Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic \
  Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus \
  Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts \
  Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral \
  Mathlib.Analysis.SpecialFunctions.ImproperIntegrals \
  Mathlib.Analysis.SpecialFunctions.Log.NegMulLog \
  Mathlib.Analysis.SpecialFunctions.Exp \
  Mathlib.Analysis.SpecialFunctions.ExpDeriv \
  Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic \
  Mathlib.Analysis.InnerProductSpace.PiL2 \
  Mathlib.Analysis.Calculus.Gradient.Basic \
  Mathlib.Analysis.Calculus.ContDiff.Operations \
  Mathlib.Analysis.Calculus.ContDiff.RCLike \
  Mathlib.Analysis.Calculus.Implicit \
  Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff \
  Mathlib.Analysis.Calculus.BumpFunction.InnerProduct \
  Mathlib.MeasureTheory.Function.Jacobian \
  Mathlib.Geometry.Manifold.PartitionOfUnity \
  Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace \
  Mathlib.LinearAlgebra.Dual.Lemmas \
  Mathlib.MeasureTheory.Measure.Hausdorff \
  Mathlib.Analysis.SpecialFunctions.Log.Basic \
  Mathlib.Analysis.NormedSpace.Connected \
  Mathlib.LinearAlgebra.CrossProduct \
  Mathlib.LinearAlgebra.Matrix.FiniteDimensional \
  Mathlib.LinearAlgebra.Matrix.SchurComplement \
  Mathlib.Data.Fintype.Lattice \
  Mathlib.MeasureTheory.Integral.Prod \
  Mathlib.MeasureTheory.Constructions.HaarToSphere \
  Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls \
  Mathlib.Tactic.Ring Mathlib.Tactic.FieldSimp \
  Mathlib.Tactic.Linarith Mathlib.Tactic.NormNum Mathlib.Tactic.Positivity
./check.sh
```

The current workspace also has an ignored, task-local Lean distribution under
`.tools/`; `check.sh` detects it. No global toolchain configuration was changed.
Dependencies and build products under `.lake/`, and the local distribution,
are excluded from Git. Only the formal sources, configuration, and lockfile
are committed. The enclosing repository is private; no paper or result has
been publicly released.
