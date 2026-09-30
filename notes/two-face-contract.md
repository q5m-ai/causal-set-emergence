# Four-dimensional two-spacelike-face contract (#49)

**Status: the original restricted contract now has deterministic and
expectation-limit proofs; it is not an unrestricted localization theorem.**
This began as work package A of the [flat-localization plan](flat-localization-plan.md).
The definitions and nonvacuity regressions compile in
[`TwoFaceContract.lean`](../formal/BoundaryDraft/TwoFaceContract.lean) and
[`TwoFaceExamples.lean`](../formal/BoundaryDraft/TwoFaceExamples.lean).
Defining a proposition does not prove it. The separate
[region geometry and API integration](../formal/TWO_FACE_GEOMETRY.md) now
proves `TwoFaceRegionGoal` and exact finite-density overlap/expectation
identities. The independent [joint-geometry proof](../formal/JOINT_GEOMETRY.md)
now establishes the area and planar-target goals. The subsequent
[two-face assembly](two-face-limit.md) supplies unconditional Lean proofs of
both original asymptotic goals without changing the contract. This does not
close #24 or assert sample-wise convergence.

## 1. Fixed geometry, action, and deliberately restricted class

The first contract covers **global two-graph regions with a slope budget**, not
all embedded two-face regions, and not even all pairs of strictly spacelike
global graphs. This smaller geometric class is chosen to include the entire
original `AdmissibleGraphCap` API without changing it. Its restrictions are
coordinate-dependent; covariance belongs to #50, not a claimed property of
this particular presentation of admissibility.

Choose two functions `h, f : Spatial → ℝ` independently, once and for all. Write

```math
\Omega=\{x:h(x)>0\},\qquad
M_{h,f}=\{(t,x):f(x)-h(x) < t < f(x)\}.
```

The main geometric case has nonempty `Ω`. The Lean class also retains empty
caps, as the old API does; the concrete nonempty examples below prevent a
vacuous contract. Connectedness is not required: the two **labeled faces** and
the joint may have several components, all of which are included in the sets
and measure. No component or additional boundary stratum is discarded.

Require precisely:

1. `AdmissibleGraphCap h`, unchanged. Thus `Ω` is bounded; the positive part
   `h₊ = max 0 h` is globally strictly Euclidean Lipschitz; the raw height has
   an ambient C³ germ at every point of `closure Ω`; it vanishes on the
   frontier; and its actual differential is nonzero at zero-height points
   in that closure. No derivative condition is imposed at positive height.
2. `f` has an ambient C³ germ at every point of `closure Ω`, including the
   joint. There is no smoothness requirement on the envelopes across the joint.
3. There exist fixed nonnegative constants `κ, λ` with the following bounds:

   ```math
   \kappa+\lambda<1,\qquad
   |h_+(x)-h_+(y)|\le\kappa|x-y|,\qquad
   |f(x)-f(y)|\le\lambda|x-y|.
   ```

All spatial norms in these assumptions are **Euclidean**, not the coordinate
function space's supremum norm. The budget is a sufficient geometric
restriction, not an overlap-density or asymptotic assumption. It excludes, for
example, some pairs of steep oppositely sloped spacelike faces whose thickness
has Lipschitz constant greater than one. Such pairs require a later, larger
interface. The subsequent two-face limit proof establishes that the original
C³ regularity suffices for these fixed-geometry deterministic and expectation
goals; it does not prove every stronger weighted or uniform-family estimate.

Keep the present four-dimensional, **unsmeared** normalized discrete action
`discreteBDGAction`, the constructed finite Poisson law, and `continuumMean`
unchanged. On a finite sample the normalization is `4 / (sqrt 6 * sqrt ρ)`
times `N - L₀ + 9L₁ - 16L₂ + 8L₃`, where `Lₖ = intervalLayer k` counts
strictly related ordered pairs with exactly `k` interior elements (`L₀` counts
links). This is the existing action multiplied by `l_p² / ℏ`, with `ρ = l⁻⁴`;
see the [discrete-action contract](../formal/DISCRETE_BDG.md).
Density is positive and tends to infinity while `h`, `f`, all slope margins,
and the entire region remain fixed. The intended theorem is

```math
\lim_{\rho\to\infty}\mathrm{continuumMean}(\rho,M_{h,f})
=\lim_{\rho\to\infty}\mathbb E[\mathrm{discreteBDGAction}(\rho)]
=\int_J\coth\theta\,dA_L.
```

The expectation is for sprinkling into this same region. Ambient causal
convexity makes the isolated and embedded interval volumes agree. No
assumption of intrinsic global hyperbolicity replaces that containment
condition. There is no second smearing scale, density-dependent geometry,
rate, variance bound, convergence in probability, or sample-wise convergence
in this contract. Flat curvature means no bulk Einstein–Hilbert term is
being omitted from a curved-spacetime claim.

## 2. Face germs, envelopes, and exact strata

The smooth face germs are `f₋ = f - h` and `f₊ = f`. The globally causal
envelopes are instead `ℓ = f - h₊` and `u = f`.
`twoFaceRegion_eq_envelopes` proves that these enclose **exactly the same**
region. Exterior zeros or negative values of the raw height do not create
walls, faces, or joints. In particular, `h` need not be globally Lipschitz;
the old quadratic ellipsoids would fail that stronger condition.

Let `S` be the zero level in `closure Ω`, equivalently its frontier. The
intended complete boundary decomposition is

```math
\begin{aligned}
\Sigma_-&=\{(f(x)-h(x),x):x\in\overline\Omega\},\\
\Sigma_+&=\{(f(x),x):x\in\overline\Omega\},\\
J&=\{(f(x),x):x\in S\},\\
\partial M&=\Sigma_-\cup\Sigma_+,\qquad
\Sigma_-\cap\Sigma_+=J.
\end{aligned}
```

These are compact C³ faces with boundary, with disjoint relative interiors.
There are **no lateral timelike walls, null faces, tips, extra corners, or
unrecorded seams**. The nonzero differential of `h` on `S` gives transversality
of the two face conormals. The slope budget controls both smooth face slopes
on the closed positive region, by differentiating inside `Ω` and extending
the bound continuously to its closure, not by differentiating `h₊` at the
joint. Strict spacelikeness of either face makes the joint spacelike.
Positive-height critical points of `h`, and critical points of either face,
are allowed: they are not degeneracies of the joint.

The topological/compact stratum consequences and ambient causal convexity
are proved by `twoFaceRegionGoal` in `TwoFaceGeometry.lean`, with the unchanged
contract. The separate [work package C proof](../formal/JOINT_GEOMETRY.md)
derives the face slope bounds, actual normals, positive joint metric and angle,
and finite intrinsic joint measure. None is a field in `AdmissibleTwoFace`.

### Exact constructor obligations for the existing probability bridge

`BoundedCausalRegion (twoFaceRegion h f)` requires exactly:

- `MeasurableSet (twoFaceRegion h f)`;
- `Bornology.IsBounded (twoFaceRegion h f)`;
- `CausallyConvex (twoFaceRegion h f)`, namely containment of **every closed
  ambient causal interval** with endpoints in the region, including null
  segments and vertices.

`AdmissibleTwoFace.boundedCausalRegion` now supplies this constructor:

1. Continuous envelopes make the strict inequalities open, hence measurable.
2. A continuous filling of the existing compact `closure Ω` times the closed
   unit interval has image exactly `closure M`. Density of the open product
   and closedness of the compact image prove both inclusions, giving actual
   boundedness rather than a new structure field.
3. The lower envelope has Lipschitz constant at most `κ + λ < 1`, so its
   strict epigraph is a future set. The upper envelope has constant
   `λ < 1`, so its strict hypograph is a past set. Their intersection is
   ambient-causally-convex. This does not use an assumed expectation identity.
4. Removing `M` from its derived closure leaves precisely the two endpoint
   graphs. Their intersection is height zero in `closure Ω`. Continuous graph
   embeddings give compactness; no exterior zero or extra stratum is added.

`TwoFaceOverlap.lean` specializes #52 using these same envelopes and the actual
region. The existing `BoundedCausalRegion.expectedBDGAction_eq` gives the exact
expectation identity at every positive density, with the full signed overlap
representation and fixed-positive-cutoff density identities. The original
conditional `twoFace_expectedLimit_of_region_and_limit` remains available;
`twoFace_expectedLimit_of_limit` discharges only its geometry premise. The
**deterministic two-face limit is now proved separately in `TwoFaceLimit`**.
Neither transfer theorem reconstructs the probability law. See the [proof and regression guide](../formal/TWO_FACE_GEOMETRY.md).

## 3. Positive angle and independent Lorentzian area

Use the existing Lean signature `(+---)`, with both **future-directed** unit
timelike normals. On the past face this is the inward normal; on the future
face it is the outward normal. If `v₋ = ∇(f-h)` and `v₊ = ∇f`, then

```math
n_\pm=\frac{(1,v_\pm)}{\sqrt{1-|v_\pm|^2}},\qquad
C=g(n_-,n_+)
=\frac{1-v_-\cdot v_+}{\sqrt{1-|v_-|^2}\sqrt{1-|v_+|^2}},\qquad
\theta=\cosh^{-1}C>0,\quad w=\frac{C}{\sqrt{C^2-1}}.
```

With the paper's opposite signature `(-+++)`, replace `g(n₋,n₊)` by its
negative. Transversality makes the future unit normals distinct, so `C > 1`;
the positive branch gives `w = coth θ`. Both-outward normals would give the
wrong sign. Compactness gives a strictly positive angle minimum for each
fixed nonempty joint, not uniformly over all admissible geometries.

The independent geometric meaning of `dA_L` is the Riemannian area of the
positive metric **minus the restricted Lorentzian metric** on `TJ` in our
signature. For any regular joint chart `ψ`, its density is

```math
dA_L=\sqrt{\det\bigl(-g(\partial_i\psi,\partial_j\psi)\bigr)_{i,j=1}^2}
\,du^1du^2.
```

This is **not** ambient Euclidean Hausdorff area in four coordinates. To give
the Lean target a concrete meaning now, rather than an arbitrary measure
parameter, use the spatial projection `S`, its already normalized
`graphSurfaceMeasure h`, and the following coordinate candidate. Put

```math
\nu=\frac{\nabla h}{|\nabla h|},\qquad
b=\nabla f-(\nabla f\cdot\nu)\nu,\qquad
j_L=\sqrt{1-|b|^2},\qquad
dA_L=j_L\,dA_S.
```

Indeed, lifting a Euclidean orthonormal tangent frame of `S` by `x ↦ (f(x),x)`
gives Gram matrix `I - b bᵀ`. The Euclidean spacetime graph factor would instead
be `sqrt(1 + |b|²)`; even using unweighted spatial area would generally be
wrong. `twoFaceProjectedArea` is `graphSurfaceMeasure h` with this density,
and `twoFaceJointArea` is its pushforward to spacetime. The target
`twoFaceBoundaryIntegral` integrates the independently defined angle weight
against the projected measure. No action, overlap, or desired limit occurs
in its definition.

**Now proved separately by C / #51:** normal/angle identities and strictness;
identification with the intrinsic Gram-density rule in constructed covering
charts and their overlaps; finite area and absolute integrability; affine
Lorentz and positive-dilation transport using #50; and exact planar
compatibility. See the [proof and scope](../formal/JOINT_GEOMETRY.md).
`TwoFaceAreaGoal` has a proof term; it is not an exhaustive formalization of C.
Nondegeneracy and integrability are derived theorems, not consequences of
Lean's total square roots, division or integrals.

## 4. Nonvacuity and unchanged base cases

**Every original planar cap.** Set `f = 0`, take its existing positive-part
constant `κ`, and use `λ = 0`. `AdmissibleGraphCap.twoFace_planar` proves
admissibility with no extra premise; `twoFaceRegion_planar` proves exact set
equality with `graphCapRegion h`. Independent regressions reapply the already
proved deterministic and expected limits with the original
`graphBoundaryIntegral h`. Geometrically `j_L = 1`, and the angle weight is
`1 / |∇h|`, so the new target must recover `graphSurfaceMeasure` and
`graphBoundaryIntegral` exactly. `TwoFacePlanarTargetGoal` records
that exact identification; C now proves it without changing either target.

The old unequal-axis ellipsoids keep their original hypotheses. The damped
quartic is instantiated in the new regression, and its existing checked
positive-height critical point remains untouched. No global noncriticality
or global raw-height Lipschitz condition is added.

**Genuinely curved future face.** For any original admissible `h` and any of
its positive-part constants `κ`, take

```math
c=\frac{1-\kappa}{2}>0,\qquad f(x)=c\sin x_1.
```

The sine is globally 1-Lipschitz, so `λ = c` meets the budget; it is smooth
independently of `h`. `AdmissibleGraphCap.exists_twoFace_sine` proves this
construction. For the specific height `ellipsoidProfile (1/4) (fun _ => 4)`,
the spatial points `(0,0,0)`, `(π/2,0,0)`, `(π,0,0)` all lie strictly inside
`Ω`. Their future heights are `0, c, 0`; the middle point is the spatial
midpoint, so the future face is not affine even **on the face domain**.
`twoFace_curved_nonvacuity` checks the positive heights and violated midpoint
identity. Thus this is not merely a Lorentz boost of a planar future face.
The past graph is also curved (its quadratic height contribution is independent
of the sine). Changing `h` while fixing the sine independently changes the
past face. Its asymptotic limit was not supplied by the initial contract;
`TwoFaceAssemblyRegression.lean` now instantiates the unconditional
deterministic and expectation theorems while retaining this nonaffinity witness.

## 5. Source review and attribution

Reviewed for this contract: Dowker–Liu–Lloyd-Jones,
[arXiv:2501.00139v2](https://arxiv.org/html/2501.00139v2), **§§2.4–2.7 and all
of §7**, and the repository [reference inventory](references.md). The local
HTML snapshot matches the inventory's SHA-256. Article text is not committed.
This is a targeted reading, **not an exhaustive novelty search or independent
verification of the paper's calculations**.

| Source passage | What it establishes or proposes | Consequence for this contract |
| --- | --- | --- |
| §2.4 | Distinguishes isolated from embedded interval counts in non-causally-convex regions | Explicit ambient containment is essential for the existing bridge |
| §2.5, (10)–(12) | Replaces the unweighted joint conjecture by Conjecture 1′ with the angle weight; timelike boundaries have a different divergent scaling | Use (11); do not mix in Conjecture 2 or claim the unrestricted conjecture |
| §2.6, (14) | Translated overlap / “volume of realisation” method, attributed there to earlier work [25]; also treats bilocal cross contributions | Overlap is prior work, not a new method here; #52 must keep the actual signed action and cross pairs |
| §2.7, (15)–(22) | Introduces smearing to control fluctuations and distinguishes its scales/limits; discusses conjectural finite-density corrections | The present statement stays unsmeared and expectation-only; no simulated fluctuation claim is imported |
| §7.1, (55) | The two-dimensional lozenge gives `2n + 1/(2n)`, not the old unweighted joint count | The angle is essential, not a convention that can be suppressed |
| §7.2, (56)–(60) | Uses spacelike tangents in signature `(-+++)`; local joint attribution begins with a stated half-lozenge assumption | Match the positive angle using normals; do not treat local attribution as a proved general localization theorem |
| §7.3, (61)–(67) | Spacelike-triangle calculation supports the same angle coefficient | Known flat-sided evidence, not two curved smooth faces in four dimensions |
| §7.4, (68)–(73) | States the variable-angle higher-dimensional conjecture; checks constant-angle cones through dimension 11 with the paper's integration-domain approximation | These cones are prior evidence, not a proof for the present smooth two-graph class; cone tips also fall outside our no-extra-strata geometry |

The inventory separately records Dowker's 2020 boundary paper (including its
warning about interchanging a pointwise limit with the outer integral), the
known arbitrary-dimensional causal-diamond results attributed to Buck et al.,
and the related curved-small-diamond work of Machet–Wang. The latter two
remain **not fully reviewed here**; this task has not re-reviewed the entire
2020 paper. The source's earlier weighted-method reference [25], its angle
reference [30], subsequent publications, and potentially overlapping work
outside this inventory need further literature review. No claim of novelty,
priority for two-curved-face results, or exhaustive absence of counterexamples
follows from this reading. Repository planar, ellipsoid, quartic and concrete
null-cap results retain their own machine-checked scope and attribution.

## 6. Original obstruction register and remaining research decisions

The register below preserves the initial #49 research status, not the current
proof inventory. Its fixed-cutoff G1 obligations were subsequently proved in
#61; the unweighted short analysis and end-to-end assembly now discharge the
original limit goals. The full weighted G3 estimate is a distinct conventional
argument. Uniform angle/cutoff limits and enlargement of the coordinate class
remain outside these results. None of these analytic conclusions is an
admissibility field.

| Obstruction | Concrete question / required test | Status and possible stronger hypothesis |
| --- | --- | --- |
| Translated-boundary tangencies | Can translates of the two smooth faces create overlap singularities whose averaged near-null density has a `σ² log σ` term rather than the sufficient quadratic little-o expansion? Does angular/length averaging repair them? | Open G1. C³ of the original faces does not prove overlap C³. Bounds on translated contact order, stronger smoothness or convexity are **provisional**, not present assumptions |
| Macroscopic nearly-null pairs | After the full `ρ^(3/2)` bilocal prefactor, do the three signed transverse moments actually cancel the geometric long-displacement contribution for each fixed cutoff? | Open G1. Small interval volume is not small coordinate separation. Do not drop the signed tail or assume a localization estimate |
| Degenerate angles / nearly null faces | Do estimates deteriorate as the positive angle tends to zero or a slope tends to one? Can density and angle limits be interchanged? | Not asserted. Each geometry has fixed strict margins; uniform families, quantitative lower-angle bounds and null limits require separate hypotheses/theorems |
| Artificial partition or regulator boundaries | Does a wedge/chart split preserve all cross-chart causal pairs and cancel cutoff terms? Can an artificial wall produce an apparent leading boundary term? | Open G2/G4. A bilocal action is not additive over cells; use an exact partition identity, not a discarded seam or finite action for an infinite wedge |
| Curved-face stability | Does normalized signed cancellation eliminate single-face and curvature terms, rather than merely making a pointwise Taylor error small? | Open G3. Higher derivative bounds alone are not an action error estimate |
| Scope of the coordinate budget | Can the contract be enlarged to arbitrary two-face regions or graphs without `κ + λ < 1` while preserving the old API? | Deferred. The current restriction is explicit and geometric; any enlargement needs its own nonvacuity and constructor checks |

An obstruction to a sufficient overlap expansion is not automatically a
counterexample to Conjecture 1′. A counterexample must concern the **complete
normalized action** of an admissible fixed region. Conversely, unsuccessful
estimates are not permission to insert localization, overlap regularity,
wedge asymptotics, the limit, or the expectation identity into the geometry.

## 7. Verification boundary and handoff

`TwoFaceRegionGoal` is proved by `twoFaceRegionGoal`, with reusable per-region
geometry and exact overlap/expectation specializations. `TwoFaceAreaGoal` and
`TwoFacePlanarTargetGoal` have independent proofs in `TwoFaceSurface`, with
intrinsic chart and transport results in `TwoFaceCharts` and `JointTransport`.
`TwoFaceLimitGoal` and `TwoFaceExpectedLimitGoal` now have unconditional proof
terms `twoFaceLimitGoal` and `twoFaceExpectedLimitGoal` in `TwoFaceLimit.lean`,
without admissions, custom axioms, or assumed short-limit premises. Planar
inclusion, exact envelope/set identities, the sine construction and concrete
nonplanarity remain checked. The original action, region, target, goal
definitions and all old hypotheses are unchanged.

The #51 geometry remains a separate proof layer. #60 connects #52's merged
overlap API through the proved region constructor and causal envelopes, not
globally Lipschitz raw heights. #61 derives the actual long-density regularity
and cancellation. The subsequent unweighted short proof constructs the actual
overlap extension, controls its remainder, and identifies the original
boundary coefficient before assembly. Geometry stays fixed throughout; the
sine family is now also a nonplanar limit regression. This does not retroactively
turn the original contract or earlier finite-density identities into proofs
of their later analytic obligations.

Validation commands: `formal/check.sh` (library build, every source with
warnings as errors, isolated transitive axiom audits, aggregate audit), the
repository Python/symbolic/numerical checks, `python3 check_markdown.py`, and
`python3 -m unittest -v test_check_markdown`. GitHub browser rendering must be
checked separately from Markdown parsing. None of these mechanical checks
constitutes independent mathematical review of the proposed contract.
