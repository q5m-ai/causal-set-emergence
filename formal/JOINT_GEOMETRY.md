# Induced spacelike joint area and angle (#51)

**Status: machine-checked geometry for the original `AdmissibleTwoFace`
coordinate subclass and its affine Lorentz/positive-dilation images.** This is
not a two-curved-face action-limit theorem. The region/stratum goal,
localization, overlap regularity, wedge analysis, rates and individual-sample
convergence remain separate obligations. No action or probability definition,
admissibility hypothesis, or existing boundary target changes.

The public modules are `JointMetric`, `TwoFaceAngle`, `TwoFaceSurface`,
`TwoFaceCharts`, and `JointTransport`. The unchanged `TwoFaceAreaGoal` and
`TwoFacePlanarTargetGoal` now have proof terms `twoFaceAreaGoal` and
`twoFacePlanarTargetGoal`.

## Scope and signature

Start with the [two-graph contract](../notes/two-face-contract.md): thickness
`h`, future height `f`, spatial joint `graphJoint h`, and spacetime lift
`twoFaceLift f`. The original positive-part Lipschitz bound is retained;
raw `h` need not be globally Lipschitz or globally smooth. Positive-height
critical points are not excluded. The joint may be empty or disconnected.

The Lean signature is `(+---)`. Its induced **positive** joint metric is
minus the restricted Minkowski form. Both normals are future-directed: the
past face's inward normal and the future face's outward normal. Spatial
orientation reversal is allowed by `PoincareEquiv`.

The global slope-budget presentation is not itself Lorentz invariant. We do
not pretend every transported region satisfies that same coordinate budget.
Instead, `JointTransport` treats the actual transformed embedding of the
original reference joint. This supplies affine covariance without enlarging
`AdmissibleTwoFace` or starting an unrestricted Lorentzian-manifold library.

## 1. Normals, positive angle and compact margins

Write `q = grad f`, `p = grad(f-h)`. Differentiating the thickness bound only
inside its positive set, then extending the differential bound continuously
to its closure, gives the original thickness constant. Differentiating the
global future Lipschitz bound gives the future constant. The triangle
inequality and strict combined budget bound both face slopes strictly below
one, uniformly on the closed positive region.

`jointUnitNormal_future_unit` normalizes the graph normal and proves its
positive time component and Minkowski square one. `joint_tangent_geometry`
uses the actual differential: a spatial vector in the kernel of `dh` lifts
to a common face tangent orthogonal to both normals. Cauchy–Schwarz and the
strict future slope make minus its Minkowski square strictly positive for
every nonzero spatial vector.

Strictness of the normal product is derived, not selected after squaring.
For distinct slopes the key algebra is

```math
(1-p\cdot q)^2-(1-|p|^2)(1-|q|^2)
=|p-q|^2(1-|q|^2)+((p-q)\cdot q)^2>0.
```

The numerator and both normalization factors are positive. Nonvanishing of
`dh` on the joint gives distinct slopes, hence `C > 1`. The positive branch
is constructed explicitly:

```math
\theta=\log(C+\sqrt{C^2-1})>0,\qquad
\cosh\theta=C,\quad \sinh\theta=\sqrt{C^2-1},\quad
\frac{C}{\sqrt{C^2-1}}=\coth\theta.
```

`AdmissibleTwoFace.angle_identities` proves each identity separately. No
unsigned angle equation is used to infer a sign. `continuousOn_cosh`,
`continuousOn_weight`, and `continuousOn_areaDensity` follow from the C³
germs and strict denominator bounds. `exists_joint_margins` applies the
extreme-value theorem on the compact joint to obtain one positive lower
margin for `C-1` and the area density. It treats the empty joint separately.
These margins belong to each fixed geometry; no uniform near-tangent or
near-null family bound is claimed.

## 2. The induced metric determines area

Let `n` be the spatial unit normal to the regular joint and `b` the tangential
part of `q`. For arbitrary spatial joint tangents `v,w`, `jointGraph_gram`
computes the determinant of the Lorentzian tangent Gram matrix:

```math
\det(-g|_{v,w})=(1-|b|^2)
\bigl(|v|^2|w|^2-(v\cdot w)^2\bigr),\qquad
b=q-(q\cdot n)n.
```

The proof first expresses the determinant using the spatial cross product.
The cross product of two tangents is parallel to their unit normal; taking
its norm and inner product with `q` gives the displayed factorization.
`joint_tangential_norm_le` and strict spacelikeness prove `1-|b|² > 0`.
Taking positive square roots proves `AdmissibleTwoFace.gramDensity`:

```math
\sqrt{\det(-g|_{v,w})}
=\sqrt{1-|b|^2}\,\mathrm{Jac}_2(v,w).
```

Consequently the unchanged coordinate definition `twoFaceProjectedArea`
weights the unchanged normalized Euclidean `graphSurfaceMeasure h` by
`twoFaceAreaDensity h f`; `twoFaceJointArea` maps it to the actual spacetime
joint. The spatial measure is only a **reference** measure. It is not used
unweighted, and ambient four-dimensional Euclidean Hausdorff area is not
substituted for the induced Lorentzian area.

### Charts and overlaps

`AdmissibleGraphCap.exists_jointChart` constructs regular scalar-graph charts
covering every joint point, using the existing implicit-chart infrastructure.
`hasFDerivAt_jointChart` and `jointFrame_eq_fderiv` identify their actual
derivatives; `jointSlice_tangent` derives their membership in the kernel of
`dh`. Their Gram densities are strictly positive on their open domains.

`SliceHeightChart.jointArea_chart` reuses the checked Euclidean scalar-graph
area theorem and proves an **equality of measures on every measurable chart
subset** with density `jointGramDensity` of the actual derivative.
`jointArea_overlap` equates the two chart measures on their entire overlap.
There are no seam, disjointness, or null-overlap premises. Thus choosing a
different covering by these constructed charts does not change the measure.
`jointGramDensity_change_frame` independently proves the absolute-determinant
law under a tangent-coordinate change, including orientation reversal.

This is a chart construction on the stated regular coordinate subclass,
not a claim that arbitrary immersed surfaces or arbitrary manifold atlases
have been formalized.

## 3. Finiteness before evaluation

Orthogonal projection bounds `b` by `q`. The Lorentzian density lies between
zero and one (strictly above zero on the joint). Therefore
`twoFaceProjectedArea_le` dominates it by the existing finite spatial joint
measure. `finite_projectedArea` and `finite_jointArea` follow without an
assumption on the target integral.

Continuity of the angle weight on the compact joint, finite area, and support
on that joint prove `integrable_weight` and `integrable_spacetimeWeight`.
`integral_spacetimeWeight` identifies the integral on the actual spacetime
joint with the unchanged `twoFaceBoundaryIntegral`. Neither finiteness nor
absolute integrability is inferred from Lean's totalized integral or from a
known numerical value.

## 4. Covariance from the actual derivative

A `JointTangentFrame` contains only two regular spatial tangents. Its existence
is constructed from the charts, not assumed in admissibility. For an embedding
`psi`, `jointFrameDensity` computes

```math
\frac{\sqrt{\det\bigl(-g(D\psi(v_i),D\psi(v_j))\bigr)}}
     {\mathrm{Jac}_2(v_1,v_2)}.
```

`jointInducedArea` integrates this derivative-based density against the
reference spatial surface measure and maps it through `psi`. It is **not**
defined by transporting an already-known answer. `frameDensity_lift` proves
that every regular reference frame gives exactly `twoFaceAreaDensity` for
the original lift. The same frame independence holds after Lorentz transport
or dilation by the following identities.

For an affine Lorentz equivalence, the chain rule removes the translation
and the linear part preserves every Gram entry. Thus `frameDensity_comp`
and `inducedArea_comp` prove preservation of the independently computed
measure. `twoFace_chart` retains its local Gram-density characterization.
`future_unit_normal` proves future orientation and unit length of transported
normals; `twoFace_weight` preserves their invariant angle quotient.
`twoFace_boundaryIntegral` and `twoFace_integrable_weight` give equality of
angle-weighted integrals and absolute integrability, with the observable
pulled back through the **affine inverse**, including the translation.
`twoFace_integral` transports arbitrary signed observables as well.

For a positive dilation, each tangent is multiplied by the scale. The Gram
determinant has degree four and its positive square root degree two.
`jointInducedArea_smul` derives the second-power area factor;
`dilated_chart` verifies the corresponding local chart rule. Unit normals
remain normal to the dilated tangent planes, so the angle weight is unchanged.
`boundaryIntegral_dilate` and `integrable_weight_dilate` prove the integral
scaling and its absolute integrability. These results concern geometry,
independently of the already proved action/density scaling in #50.

## 5. Exact planar compatibility and negative controls

For **every** old admissible height, setting `f = 0` makes the density one and
the angle weight the reciprocal of the actual gradient norm. Therefore
`twoFaceProjectedArea_planar` is equality of measures, and
`twoFaceBoundaryIntegral_planar` recovers exactly `graphBoundaryIntegral`.
No sphere-only calibration or stronger height hypothesis is used.

`JointSurfaceRegression.lean` independently checks the actual derivative
chart rule, overlap measures, signs, frame changes, integrability and margins.
It retains the original unequal-axis `48 * Real.pi` integral, recovers it on
a translated nontrivial boost, and checks dilation and reciprocal dilation
values `192 * Real.pi` and `12 * Real.pi`. Explicit inverse coordinates and
two joint points with different time coordinates prevent a planar-time-only
or translation-free test. The existing curved-sine family also satisfies the
new finiteness and integrability theorems.

The Euclidean negative control uses two actual spatial joint tangents at the
unequal ellipsoid's north pole. After the boost their Lorentzian Gram density
is one, whereas their four-coordinate Euclidean Gram density is `sqrt(17/8)`,
strictly larger. Thus Euclidean spacetime area has the wrong local metric
factor. The independent `test_joint_geometry.py` additionally integrates the
whole boosted unequal-axis joint: Lorentzian weighted area reproduces `48*pi`,
while the Euclidean replacement gives approximately `181.78994` instead of
`150.79645` (about 20.55% too large). Quadrature refinement and a separate
precision check are included; these numerical diagnostics are not substitutes
for the Lean theorems. The curved-sine diagnostic checks the two normals and
the decreasing Lorentzian versus increasing Euclidean graph-area factors.

## Verification and remaining boundary

Run `formal/check.sh`: library build, every local source with warnings as
errors, isolated transitive axiom audits, and the aggregate public-library
audit. Only `propext`, `Classical.choice`, and `Quot.sound` are permitted.
Run the repository Python/symbolic/numerical checks and Markdown validation.
The independent Lean regression is discovered even outside the library root.

There is no localization, coarea, action identity, finiteness assumption, or
boundary-integral value in the geometric structures. This completes the
geometric target on the stated subclass, not the two-face asymptotic contract
or tracker #24. It does not reprove the separate Poisson-expectation bridge,
claim sample-wise convergence, or constitute independent mathematical review.
