# Issue #24: from checked graph caps to two curved faces

**Status:** proposed research decomposition, not a proof of localization or of
Conjecture 1′. The calculations below are written arguments and a symbolic
cross-check, not new Lean theorems. A failed localization lemma or a necessary
correction term is a useful outcome, not a reason to hide an assumption.

## 1. Stocktake at the completed base case

The reference is merged `main` at `59b38e0`, after PRs #47 and #48.
[Tracker #1](https://github.com/q5m-ai/causal-set-emergence/issues/1) and its
probability milestone #40 are closed. The [acceptance audit](../formal/ACCEPTANCE.md)
records 88 checked Lean sources and 727 audited public library theorems. Those
are the recorded full-audit results, not a new Lean run for this planning note.

| Available result | Reusable source | Remaining boundary |
| --- | --- | --- |
| Actual finite Poisson law, reduced Mecke identities, discrete action and exact expectation | `FinitePoisson`, `PoissonIntegration`, `DiscreteBDG`, `ExpectationBridge` | No sample-wise convergence; no new curved-spacetime probability interface |
| Expected boundary limit for every admissible graph cap | `GraphLimit`, `ExpectedLimits` | Future face is planar |
| Concrete unequal-axis ellipsoid and null-plane-truncated diamond | `EllipsoidLimit`, `NullCapLimit`, `ExpectedLimits` | The null target is algebraic, not a general induced-null-area theorem |
| Signed kernel scaling, normalization, cancellation and absolute tails | `KernelScaling`, `KernelHalfLine`, `KernelCollar` | These are not estimates for an arbitrary two-face bilocal integral |
| Euclidean area, controlled collars, overlapping charts, coarea and right-continuous level density | `HausdorffAreaLocal`, `GraphAtlasRepresentation`, `GraphCoarea`, `GraphDensityRegularity` | A spacetime joint not lying in a constant-time plane needs its induced metric area |
| Explicit Lorentz rest-frame transport for timelike intervals | `LorentzReflection`, `TimelikeInterval` | No general action/joint Poincaré-covariance API yet |

In particular, **do not reopen the four-dimensional Poisson bridge**. For a new
bounded measurable causally convex Minkowski region,
`BoundedCausalRegion.expectedBDGAction_eq` already supplies it. The new work is
geometry and deterministic asymptotics, followed by an expectation transfer.
Neither the probabilistic theorem nor the existing limits establish variance,
concentration, a rate, or the unrestricted conjecture.

## 2. The next theorem should change one major assumption

Stay in four-dimensional Minkowski space, at fixed geometry, with the current
unsmeared normalized action. Replace the planar future face by a second curved
spacelike face. Initially exclude null/timelike faces, tangential joints,
noncompact regions, holes with extra boundary strata, and varying geometry as
density increases. This is an intermediate theorem, not a redefinition of #24.

A candidate geometric contract is a bounded open causally convex region whose
boundary consists of two compact sufficiently smooth spacelike faces, meeting
transversely along their common compact spacelike two-dimensional boundary.
Specify what “consists of” and “smooth up to the joint” mean; forbid unrecorded
lateral walls. Begin with C³ as in the base case, but investigate whether the
estimates actually follow from it. Any stronger regularity must be explicit.
Global hyperbolicity is not a substitute for proving ambient causal convexity.

Use both **future-directed** unit timelike normals, not both outward normals.
In signature `(-+++)`, let their inner product determine the invariant angle:

```math
C(p)=-g(n_-(p),n_+(p))>1,\qquad
w(p)=\frac{C(p)}{\sqrt{C(p)^2-1}}=\coth\theta(p).
```

The area is induced by the positive definite restriction of the Lorentzian
metric to the joint. It is not ambient Euclidean Hausdorff area in four
coordinates. In the existing planar case this must recover exactly
`graphSurfaceMeasure`, `graphBoundaryIntegral`, and the positive angle branch.
Compactness and transversality should yield finite area and an integrable
weight, rather than assuming the target integral is well behaved.

Keep the numerical action and proposed geometric target independently defined.
The eventual Lean contract must not have fields asserting localization,
overlap regularity, wedge asymptotics, cancellation, or the desired limit.
A separate conditional analytic lemma may take such hypotheses; applying it
to the geometric class is a distinct obligation.

## 3. An exact route worth trying: translated overlap

The [weighted integral method, source §2.6](https://arxiv.org/html/2501.00139v2#S2.SS6)
already makes this change of variables. It is prior work, not a novelty claim.
We propose formalizing it for the existing signed kernel and using it to study
uniform estimates, not merely to calculate another symmetric example.

Write `K = bdgKernel`, set the interval coefficient to its existing value, and
define the overlap independently of the action:

```math
c=\frac{\pi}{24},\qquad
Q(z)=(z^0)^2-|\mathbf z|^2,\qquad
V_M(z)=\int_{\mathbb R^4}\mathbf 1_M(x)\mathbf 1_M(x+z)\,dx.
```

The determinant-one substitution from a pair of endpoints to an endpoint and
a displacement gives the candidate exact reduction:

```math
\mathcal A_\rho(M)=\frac4{\sqrt6}\sqrt\rho
\left[|M|-\rho\int_{J^+(0)}
 K\bigl(c\rho Q(z)^2\bigr)V_M(z)\,dz\right].
```

This is an identity for `continuumMean` on bounded measurable regions; causal
convexity is additionally required to interpret it as the existing isolated
Poisson mean. Compact domination must precede signed Fubini. Prove overlap
measurability, support bounds, and absolute integrability, including empty and
zero-volume regions. Do not replace restricted interval volume in a
non-causally-convex sprinkling by the full Minkowski interval volume.

There is also a useful coordinate test case. Suppose two globally strictly
Lipschitz graph functions enclose a bounded region and a displacement is
future causal. The lower epigraph is a future set and the upper hypograph a
past set. Vertical integration then gives

```math
M=\{(t,x):f_-(x) < t < f_+(x)\},\qquad
V_M((s,a))=\int_{\mathbb R^3}
 \bigl[f_+(x+a)-s-f_-(x)\bigr]_+\,dx.
```

This graph formula is only a sufficient coordinate model. Do not silently
strengthen the original graph-cap assumptions to require a globally smooth,
globally Lipschitz **raw** height profile. Its checked control is on the
positive part; smooth face germs and globally causal envelopes may need
separate APIs. Interior critical points and irrelevant exterior zeros remain
allowed in the existing theorem.

## 4. A concrete cancellation to extract first

Small interval volume does **not** imply small endpoint separation. Write a
future displacement in radial null coordinates:

```math
u=t-r,\qquad v=t+r,\qquad 0\le u\le v,\qquad
Q=uv,\qquad dz=\frac{(v-u)^2}{8}\,du\,dv\,d\omega.
```

Here the sphere measure has total mass `4π`. The diagonal scale is
`ρ^(-1/4)`, whereas at fixed positive `v` the near-null transverse width in
`u` is of order `ρ^(-1/2)/v`. An isotropic short-distance cutoff misses this
second regime.

For the actual polynomial, elementary Gaussian moments give

```math
K(x)=\left(1-9x+8x^2-\frac43x^3\right)e^{-x},\qquad
\int_0^\infty z^j K(z^2)\,dz
=-\frac{j(j-1)(j-2)}{12}\,
\Gamma\!\left(\frac{j+1}{2}\right),\qquad j\ge0.
```

Thus the moments of orders zero, one, and two vanish, while the moment of
order three is `-1/2`. To verify the formula, substitute `x = z²`, evaluate
the four Gamma integrals, and use the Gamma recurrence. Absolute convergence
holds for every displayed moment. The SymPy 1.14.0 check in
[`check_symbolic.py`](../check_symbolic.py) recovers the factor and all four
values. This is **not** `planeKernel`: that reduced kernel
has mass one. Nor do these three zero moments prove geometric localization.

### A bounded analytic lemma, separate from the geometric conjecture

Fix a macroscopic separation cutoff `δ > 0`. Set `σ = uv`, the squared proper
time, and integrate all the other displacement coordinates first. The
long-displacement overlap density is

```math
B_\delta(\sigma)=\int_{S^2}
\int_{\max(\delta,\sqrt\sigma)}^\infty
\frac{(v-\sigma/v)^2}{8v}\,
V_M\!\left(\frac{v+\sigma/v}{2},
           \frac{v-\sigma/v}{2}\omega\right)
\,dv\,d\omega,\qquad \sigma\ge0.
```

Boundedness of the region bounds the effective `v` range. The part of the
bilocal integral with `v ≥ δ` is exactly the integral of this density against
`K(c ρ σ²)`. A promising **sufficient**, not yet geometrically proved, condition
is a second-order expansion with a little-o remainder:

```math
B_\delta(\sigma)=b_0+b_1\sigma+b_2\sigma^2+o(\sigma^2)
\quad(\sigma\downarrow0).
```

For a measurable bounded compactly supported density satisfying that condition,
the three moment cancellations imply

```math
\rho^{3/2}\int_0^\infty
 B_\delta(\sigma)K(c\rho\sigma^2)\,d\sigma\longrightarrow0.
```

**Written proof of the conditional implication.** Subtract the quadratic
polynomial over the whole half-line, using its three exact zero integrals.
Divide the remainder by `σ²`; the quotient tends to zero at the origin and
is globally bounded, using compact support and boundedness away from zero.
Substitute `z = sqrt(c ρ) σ`. The remaining prefactor is the constant
`c^(-3/2)`, and a constant times `z² |K(z²)|` dominates. Dominated convergence
proves the limit. With remainder bounded by `C σ^(2+α)` near zero, for some
`α > 0`, the same substitution gives order `ρ^(-α/2)`, with exponentially
small polynomial tails. Constants may depend on the **fixed** cutoff.

The normalization matters: the bilocal term carries `ρ^(3/2)`, not just the
square-root prefactor. An unscaled error tending to zero need not suffice.
Taking absolute values **before** the polynomial cancellations generally loses
the result. This lemma concerns only the long-displacement bilocal piece, not
the point term or the short-displacement bulk cancellation.

### The genuine research question

Does the geometrically defined, already averaged `B_δ` have the required
expansion for the candidate two-face class? Translated boundary intersections
can develop tangencies even when the original joint is regular. It is not
valid to declare their overlap globally C³. Averaging over directions and
lengths may repair singularities, or a different cancellation theorem may be
needed. Prove this, stratify the exceptional configurations with estimates,
or exhibit an obstruction. Do not insert this expansion into admissibility.

An order `σ² log σ` term or another insufficiently controlled remainder would
be diagnostically important. It would first refute this sufficient route,
not automatically the conjecture. A rigorous counterexample to the conjecture
must concern the complete normalized action of an admissible region.

## 5. First work packages

These are intended as small issue contracts, with acceptance tests rather than
optimistic assertions that each already has a proof. Geometry interfaces should
be agreed before downstream implementation. Independent analytic work can run
in parallel.

| ID | Deliverable and definition of done | Dependencies | What we learn |
| --- | --- | --- | --- |
| [A / #49](https://github.com/q5m-ai/causal-set-emergence/issues/49) | Precise two-face theorem contract, source/obstruction register, and nonvacuity examples. Compile open goals as propositions, with no admissions. Account explicitly for graph-cap compatibility and genuinely curved future faces. | Existing checked program | Which version we are actually trying to prove |
| [B / #50](https://github.com/q5m-ai/causal-set-emergence/issues/50) | Affine Lorentz covariance of the unchanged deterministic action and finite-density dilation law; transfer through the existing expectation bridge. Prove causal and Lebesgue transport, not just interval invariance. | Existing interval/measure API | Which coordinate choices are harmless |
| [C / #51](https://github.com/q5m-ai/causal-set-emergence/issues/51) | Induced spacelike joint measure, positive invariant angle, finiteness/integrability, chart compatibility and Lorentz transport. Recover the original canonical planar target exactly. | A; B supplies ambient transport | Whether the proposed answer is geometrically the right quantity |
| [D / #52](https://github.com/q5m-ai/causal-set-emergence/issues/52) | Exact translated-overlap reduction, compact domination, signed Fubini, support/measurability, null-coordinate disintegration and the graph overlap formula on its stated subclass. | Existing action; A for subclass compatibility | A representation retaining all nearly-null pairs |
| [E / #53](https://github.com/q5m-ai/causal-set-emergence/issues/53) | Three concrete signed Gaussian moments and the conditional long-null cancellation lemma above, with integrability and scaled remainder estimates. Distinguish it from geometric applicability. | Existing polynomial; independent of A–D | Exactly what regularity would be sufficient |
| [F / #54](https://github.com/q5m-ai/causal-set-emergence/issues/54) | Deterministic diagnostics for genuinely two-curved-face families, with independent geometry and numerical error controls, keeping geometry fixed during each density limit. | A and D for meaningful tests | Where the proposed regularity/locality could fail |

B's dilation regression should use the exact dimensional identity, for `s > 0`:

```math
\mathcal A_\rho(sM)=s^2\mathcal A_{\rho s^4}(M).
```

Suggested diagnostic families for F:

- A boosted existing ellipsoid, as a covariance calibration only. It is not a
  new two-curved-face result.
- Bend both faces using the same small nonlinear time shift supported away
  from the joint. Keep the entire joint neighborhood unchanged. With strict
  Lipschitz margin retained, this tests whether remote face shape can affect
  the leading answer; recompute the actual region volume and pair integral.
- Allow the shift to vary along the joint, producing a nonplanar joint. Compute
  the induced Lorentzian area independently; Euclidean area is a negative
  control, not the reference answer.
- Near-tangent examples with positive angle fixed during each density run.
  Deteriorating constants must not be mistaken for a counterexample.

Direct high-density Monte Carlo is a poor primary diagnostic: the signed
bulk/pair cancellation and random fluctuations can swamp an order-one target.
Use reduced deterministic integration, precision/refinement checks, and the
existing exact examples as calibration. Numerical agreement is not acceptance
of a missing remainder estimate.

## 6. Research gates after the first batch

Do not launch “prove general localization” as one implementation issue. Resolve
these in order, splitting a gate again when its analytic route becomes clear.

### G1 — geometric long-null cancellation

Apply E to D's **actual** overlap density, or replace E by an explicitly proved
weaker averaged criterion. Identify the treatment of translated tangencies and
any exceptional directions. The result must work for every region in A, or
state the smaller covered class honestly. Failure should produce a precise
obstruction and a revised strategy, not an analytic hypothesis disguised as
geometry. This is the first high-risk gate.

### G2 — regulated tangent-wedge coefficient

Compute the coefficient for two transverse spacelike tangent hyperplanes with
a tangential test weight. An infinite wedge does not have a finite action;
state a localization/regulator and account for its artificial boundaries and
cross terms. Derive the invariant `coth θ` coefficient, retaining all signs.
Recover the planar graph result, and require uniform estimates when the angle
stays in a fixed compact subset of the positive branch. This calculation and
G1 can be investigated in parallel once their interfaces are fixed.

The [regulated wedge proof](regulated-tangent-wedge.md) implements this local
calculation with compact first-endpoint weights and a bounded tent regulator.
It records the exact artificial-complement subtraction, retained cross-region
pairs, checked finite-density reduction and limit, and conventional
invariant-area/uniformity arguments. It does not replace G1 or the stability
and globalization obligations below.

### G3 — stability and short-displacement cancellation

Compare genuinely curved faces with their tangent wedges **after accounting
for the signed cancellations**. Control interior, single-face and joint
pieces separately; do not assume single-face or curvature contributions vanish
because the conjectured answer lacks them. Establish a uniform normalized
error, not pointwise Taylor convergence. If an extra term survives, identify
it and test the candidate theorem against it. This is the second high-risk
gate; a small shape displacement alone is not an adequate error estimate.

The [short-displacement argument](curved-face-stability.md) supplies a
conventional proof at a fixed sufficiently small cutoff for the unchanged
two-graph class, awaiting independent review. It derives the local overlap
extension from C³ face germs, quantifies the signed normalized remainder and
compares with regulated tangent-wedge observables. A spatial source partition
has a nonzero cutoff-derivative term in general; the argument retains it until
the complete partition cancels it. Only the exact finite-density partitions
are newly machine checked, not this full analytic proof. No long-null or
complete two-face limit is inferred.

### G4 — globalization, then expectation

Use a finite controlled joint atlas and overlap-aware weights. A bilocal
action is not additive across artificial chart regions: partition the actual
integral with an exact identity and retain cross-chart pairs or prove their
cancellation. Explain any cutoff-derivative terms. Use one consistent collar
and cutoff hierarchy for local and remainder estimates. A safe possible order
is density first at fixed macroscopic cutoff, then cutoff removal; estimates
must justify that order. Do not assume constants uniform as `δ` tends to zero.

Assemble the deterministic theorem only after G1–G3. Then apply the already
proved four-dimensional expectation bridge. Keep the original graph-cap,
unequal-axis, quartic/interior-critical-point and null-cap regressions unchanged.
Require the full Lean source/axiom audit, a conventional proof explanation,
and independent mathematical review; green Markdown CI is not a Lean audit.

## 7. What should wait, and what need not

The [general roadmap](conjecture-roadmap.md) still governs #24. The flat
two-face theorem would be a major partial resolution, **not closure**.

- **Other dimensions:** first separate dimension-dependent signed moments,
  action normalization and area dimension from dimension-independent geometry.
  Do not port four-dimensional coefficients unchanged. The generic finite
  Poisson construction is reusable; the action and interval-volume bridge need
  dimension-specific extensions.
- **Curved spacetime:** translated overlap is not a global curved-space method.
  It may teach which estimates a covariant replacement needs, but interval
  volumes, volume densities, the bulk curvature coefficient, and nonlocal
  remainder bounds require a new argument. Recovering the Einstein–Hilbert
  term is mandatory for #24's general target.
- **Null/mixed joints:** pursue a separate contract and geometry theorem. The
  concrete null-cap result is a regression, not permission to interchange the
  density limit with a singular angle limit. Its induced-area interpretation
  is a useful independent task, but not a blocker of the spacelike program.
- **Variance and individual sprinklings:** optional separate strengthening,
  not a hidden requirement for this mean-action theorem.
- **Literature and expert scrutiny:** start now, not after formalization.
  Sections 2.4–2.7 and 7 of the source distinguish regimes, the existing
  weighted method, smearing and known angle examples. The repository's
  [reference inventory](references.md) is a starting point, not a completed
  novelty search. Conjecture 2 remains in #26.

**Recommended first mathematical step:** E's signed-moment and conditional
cancellation lemma, alongside A's statement work and D's exact reduction.
That gives a useful, falsifiable analytical interface before a large new
geometry library is built. The key lesson to test is whether locality emerges
from signed cancellation of nonlocal pairs, rather than from their absence.
