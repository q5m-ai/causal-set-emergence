# Controlled conformal 4D action: finite-density API

Issue [#93](https://github.com/q5m-ai/causal-set-emergence/issues/93) supplies a
**finite-density expectation identity**, not a curved continuum limit. The
original flat definitions, `AdmissibleTwoFace`, and all flat theorems remain
unchanged. The common unweighted observable for #73/#74/#75/#76 is
`BoundaryDraft.conformalAction` in `BoundaryDraft/ConformalAction.lean`.

## Fixed geometric input

Keep the existing coordinate space `Spacetime = Fin 4 → ℝ`, signature `(+---)`,
future orientation, and closed `causalFuture` relation. Fix one original
`AdmissibleTwoFace h f` and its `twoFaceRegion h f`. Original two-face geometry
already proves openness, measurability, boundedness, compact closure, and
ambient causal convexity. None of its hypotheses is strengthened.

`ControlledConformalFactor Omega M` has only these geometric fields:

```lean
measurable : Measurable Omega
control : ∃ U : Set Spacetime,
  IsOpen U ∧ closure M ⊆ U ∧ ContDiffOn ℝ ⊤ Omega U ∧
  ∃ m L : ℝ, 0 < m ∧ ∀ p ∈ U, m ≤ Omega p ∧ Omega p ≤ L
```

Thus the factor is smooth of all orders, positive and uniformly controlled on
one open neighborhood of the **whole closure**. All geometry, neighborhoods and
bounds are fixed as density varies. Global measurability is just an ambient
extension convention: smoothness and positivity outside `U` are not required.
An extension by one off `U` is Borel measurable. The checked
`conformalVolume_restrict_congr`, `conformalAction_congr`, and
`conformalProbability_congr` show independence from values outside `M`.
No jet, cancellation, expectation identity or desired limit is a field.

The coordinate definitions and determinant calculation are:

```text
g_p(v,w) = Omega(p)^2 * minkowskiInner(v,w)
det(g_p) = -Omega(p)^8
sqrt(abs(det(g_p))) = Omega(p)^4
mu_g = volume.withDensity (fun p => ENNReal.ofReal (Omega(p)^4))
```

`conformalMetric_eq_scaled` identifies the metric with Minkowski's form under
positive invertible tangent scaling. `conformalMetric_causal_iff` checks the
same future quadratic cone, including its null boundary. The order and
exclusive intervals deliberately reuse `causalFuture` and
`causalIntervalInterior x y = causalInterval x y \ {x,y}`. On the controlled
region this is also the causal-curve order: positive conformal rescaling
preserves every future causal tangent; conversely the straight segment between
Minkowski-related region endpoints lies in their causal interval and hence in
`M` by causal convexity. This last curve interpretation is a written geometric
argument, not a new Lean Lorentzian-manifold/path formalism.

`conformalVolume_absolutelyContinuous` and `conformalVolume_noAtoms` prove
atomlessness. `ControlledConformalFactor.volume_bound` bounds region volume by
`ENNReal.ofReal (L^4) * volume M`. Boundedness then proves finite mass, including
empty and nonempty zero-volume regions. The exact expectation itself needs
only a finite atomless restricted measure; smoothness is the agreed controlled
geometric class, not a hidden analytic input to probability theory.

## Canonical observable and probability space

These are definitions before any averaging or limiting argument:

```lean
conformalIntervalVolume (Omega : Spacetime → ℝ)
  (M : Set Spacetime) (x y : Spacetime) : ℝ
conformalAction (Omega : Spacetime → ℝ) (rho : ℝ) (M : Set Spacetime) : ℝ
conformalIntensity (Omega : Spacetime → ℝ) (rho : ℝ)
  (M : Set Spacetime) : Measure Spacetime
conformalProbability (Omega : Spacetime → ℝ) (rho : ℝ)
  (M : Set Spacetime) : Measure (Multiset Spacetime)
conformalExpectedAction (Omega : Spacetime → ℝ) (rho : ℝ)
  (M : Set Spacetime) : ℝ
```

The following code notation spells out `conformalAction_eq_integral`, not a
conjectured continuum target:

```text
V_M(x,y) = mu_g(M intersect (causalInterval(x,y) minus {x,y}))
K(z) = (1 - 9*z + 8*z^2 - (4/3)*z^3) * exp(-z)
A_g(rho,M) = (4/sqrt(6))*sqrt(rho) *
  [mu_g(M) - rho * integral_{x in M} integral_{y in M intersect Jplus(x)}
     K(rho * V_M(x,y)) dmu_g(y) dmu_g(x)]
intensity = ENNReal.ofReal rho • mu_g.restrict M
probability = FinitePoisson.law intensity
expected = integral discreteBDGAction(rho,c) dprobability(c)
```

The real-valued interval volume is finite, nonnegative and bounded by region
volume, so conversion from extended reals does not hide infinite mass.
`measurable_intervalVolume` proves joint endpoint measurability;
`measurable_kernel` also includes the density variable. `integrable_kernel`,
`integrable_kernel_section`, `integrable_causalKernel`, and
`integrable_outer_kernel` discharge signed product, every-section and outer
integrability at every positive density. The proof bounds Poisson probabilities
by one and keeps the complete signed finite layer sum.

`conformalVolume_restrict_interval` and `intervalVolume_ambient` derive
ambient equality **only for endpoints in a causally convex region**, including
finiteness. Endpoint removal is volume-null. No curved interval is replaced by
`(pi/24) * intervalSq^2`; no chronological-only order is substituted.

The genuine discrete observable is exactly the existing `discreteBDGAction`:

```text
4/(sqrt(6)*sqrt(rho)) * [N - N_0 + 9*N_1 - 16*N_2 + 8*N_3]
```

Layers count **ordered** distinct causal pairs with the indicated number of
exclusive-interval points. Null-related intermediate points remain in the
finite order. `ae_supported`, `ae_nodup`, and `ae_finite_order` prove that under
the actual constructed probability law this is the finite-set action, not a
continuum-defined substitute. `count_probability` gives every subset's Poisson
count at its curved restricted rate. Factorial moments prove absolute
integrability without a bounded-cardinality premise. Zero-volume regions have
empty samples almost surely and zero expected action.

## Exact theorem and proof decomposition

```lean
theorem ControlledConformalFactor.expectedAction_eq
    {Omega : Spacetime → ℝ} {M : Set Spacetime}
    (hOmega : ControlledConformalFactor Omega M)
    (hm : MeasurableSet M) (hb : Bornology.IsBounded M)
    {rho : ℝ} (hrho : 0 < rho) :
    conformalExpectedAction Omega rho M = conformalAction Omega rho M

theorem AdmissibleTwoFace.conformal_expectedAction_eq
    {h f : Spatial → ℝ} (hf : AdmissibleTwoFace h f)
    {Omega : Spacetime → ℝ}
    (hOmega : ControlledConformalFactor Omega (twoFaceRegion h f))
    {rho : ℝ} (hrho : 0 < rho) :
    conformalExpectedAction Omega rho (twoFaceRegion h f) =
      conformalAction Omega rho (twoFaceRegion h f)
```

`FiniteMeasureBDG.lean` first specializes the **existing** generic
`FinitePoisson` count/Mecke and `PoissonIntegration` factorial-moment proofs to
an arbitrary finite intensity on the existing 4D order. Its `integral_layer`
uses the actual interval rate. `kernel_eq_sum` supplies factorial denominators
and all four signed weights. `integral_action` combines the real point and
pair expectations. `finiteMeasureAction_expectation` then specializes intensity
to density times a finite atomless measure. Only the selected diagonal is
removed almost everywhere. Two-point Mecke gives **density squared**; factoring
one density into the original physical normalization leaves the inner density
in `A_g`. No limit or flat volume formula is used in this proof.

This is a new finite-measure specialization, not an invasive rewrite of the
old flat API. For #77 it is still **4D-order-specific**, not a dimension-indexed
measured-order abstraction. The probability law and generic factorial/Mecke
proofs are reused, not rederived or changed. No competing generic helper is
extracted in this pass.

## Flat calibration and genuinely curved example

Checked calibration declarations:

```lean
conformalExpectedAction_one
conformalAction_one
conformalExpectedAction_const
conformalAction_const
```

For the original bounded causally convex flat regions they give:

```text
A_1(rho,M) = continuumMean(rho,M)
A_c(rho,M) = c^2 * continuumMean(rho*c^4,M)       (c > 0)
E_c(rho,M) = c^2 * expectedBDGAction(rho*c^4,M)
```

Both the measure/law and the discrete normalization are identified. Constant
factors are calibration, **not** the curved test.

`ConformalExamples.lean` uses `quadraticConformalFactor p = 1 + (p 0)^2`.
It proves all-order smoothness, strict positivity and control on every bounded
region: on a fixed slab `abs(t) < T`, take lower bound `1` and upper bound
`1 + T^2`. The concrete region uses the original ellipsoid height `1/4`, axes
`(4,4,4)`, and planar future face. The two interior points at times `-1/8` and
`-1/16` with zero spatial coordinates have different conformal factors. Its
original admissibility, conformal control, nonconstancy **inside the region**,
and exact expectation are checked in Lean.

Nonzero spacetime curvature is established independently as follows. Fix
signature `(+---)` and the explicit convention:

```text
R^a_{bcd} = partial_c Gamma^a_{db} - partial_d Gamma^a_{cb}
           + Gamma^a_{ce} Gamma^e_{db} - Gamma^a_{de} Gamma^e_{cb}
Ric_{bd} = R^a_{bad};  scalar R = g^{bd} Ric_{bd}
```

For a time-only factor set `H = Omega'/Omega`. Directly from the metric,
`Gamma^0_00 = H`, `Gamma^0_ij = H*delta_ij`, and
`Gamma^i_0j = Gamma^i_j0 = H*delta^i_j`. Contracting the displayed convention
gives `Ric_00 = -3*H'`, `Ric_ij = (H' + 2*H^2)*delta_ij`, and
`R = -6*Omega''/Omega^3`. For `Omega = 1+t^2` this is
`R = -12/(1+t^2)^3`, nonzero everywhere. Reversing the curvature-tensor
convention reverses this sign; no bulk coefficient is quoted from it.

`conformal_geometry.py` independently constructs the metric, differentiates
its entries, builds all Christoffels and Ricci entries, and contracts the
scalar; it does not insert the conformal-curvature shortcut. Exact SymPy tests
verify the above result and flat/constant controls. An independent exact
vertical-interval integral of `Omega(t)^4` over its spatial-ball sections is
strictly different from the flat proper-time formula for the interior endpoint
pair. This is symbolic verification and a written curvature calculation,
**not a Lean curvature theorem or a proof of bulk localization**.

## Downstream boundary and validation

#73 must identify its analytic notation with this unweighted action, same
region, measure and isolated exclusive interval; it owns local expansions,
curvature-sign conversion when comparing literature, nonlocal/nearly-null
control, and the go/narrow/stop decomposition. #74/#75 still need the compatible
curved joint/face and bulk geometry, induced measures and normals, analytic
remainders and signed cancellations, and target coefficients. #76 may use the
proved exact expectation only after an independent deterministic limit is
established on the same domain. No curved induced-joint target or
Einstein--Hilbert coefficient is defined or assumed here. Before downstream
work starts, compare #73's feasibility output and decomposition with this API;
this package does not certify that compatibility check in advance.

The integrated [#73 feasibility report](../notes/curved-bulk-pilot.md#pinned-93-api-identification-source-level-not-an-integrated-audit)
now explicitly identifies its observable with the API at `373caca`, with the
same region class, measure, exclusive intervals and normalization. Its fixed
pair-domain split (C19) is compatible with the signed integrability proved
here, but remains a written analytic identity rather than a new Lean result.
The decision is **narrow**: #74 still needs signed short-remainder and
boundary-truncated long-amplitude estimates; #75 must retain that same
unproved analytic work. #73 and the general contract use the opposite Riemann
sign from this note's example, so `R_93 = -R_73 = -R_90`; the finite-density API
contains no scalar curvature or bulk target and is unaffected. This source
comparison supplies no missing localization theorem or human review.

This does not close #24, prove a general curved/global theorem, or assert
singular-angle uniformity, shrinking-cutoff interchange, a rate, variance,
concentration or individual-sprinkling convergence.

Validation commands:

```sh
cd formal && ./check.sh
# From repository root, with requirements.txt installed:
python3 check_symbolic.py
python3 -m unittest -v
python3 check_markdown.py
python3 -m unittest -v test_check_markdown
```

`ConformalRegression.lean` independently expands both definitions and exercises
the law, all signed layers, both density factors, integrability, endpoint/null
conventions, ambient compatibility, flat and non-unit/reciprocal scaling,
extension independence and zero-volume cases. The full integrated checker
includes isolated source and aggregate transitive axiom audits; only
`propext`, `Classical.choice`, and `Quot.sound` are permitted. Compilation and
symbolic checks are not independent human review; no such review is claimed
by this implementation note. The PR records observed validation at its head.
