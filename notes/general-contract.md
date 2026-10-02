# General Conjecture 1′: contract and scope gate (#90)

**Decision: GO on the explicit interfaces below; NARROW the next proof tasks,
not the general target; STOP any general-theorem or novelty claim.** This is a
written research contract, not a new limit proof. It absorbs the scope questions
of superseded #82. [Issue #24](https://github.com/q5m-ai/causal-set-emergence/issues/24)
keeps its completion criterion: a non-vacuous general theorem with curvature
bulk, variable-angle joint and identified Poisson expectation, or a rigorous
full-action counterexample and corrected general theorem. Closing this contract
gate is not completion of that criterion. Timelike Conjecture 2 stays in
[#26](https://github.com/q5m-ai/causal-set-emergence/issues/26).

Source baseline: [`73ddd09`](https://github.com/q5m-ai/causal-set-emergence/tree/73ddd09b4a631dc2d4818d9bd2da7ef69a2ca1b1).
Read together with the [passage-level literature audit](general-contract-literature.md).
The latter corrects two over-broad literature summaries: the inspected 2015
paper explicitly evaluates diamond asymptotics in dimensions 2–16, and the
2020 curved-diamond calculations are curvature expansions, not the required
fixed-geometry error theorem.

## 1. Coverage matrix: target is not the union of today's pilots

Here **checked** means the stated repository Lean result, not independent
review. **Published evidence** is distinguished in the literature audit.

| Axis | Intended general coverage / decision | Checked baseline | Unresolved coverage and owner |
| --- | --- | --- | --- |
| Dimension | Every integer dimension at least two; include 2D counting measure on joints. Dimension one has no codimension-two joint and is not this conjecture | Global deterministic/expected limits in 4D; `dimensionWeighted_wedge_limit` in every integer dimension at least two | 3D global pilot first; 2D and remaining odd/even global limits remain with #81, not inferred from #88 |
| Observable | Unsmeared **minimal-layer** BDG action, normalized by the Planck power as in §2; density alone varies | `discreteBDGAction`, independently constructed finite Poisson law and `ExpectationBridge` in 4D | Dimension-indexed observable/bridge #77; curved measured-order instance #93. Smearing and random convergence are different problems |
| Interval regime | Isolated order/interval count; embedded regime agrees only after ambient containment is proved | `BoundedCausalRegion` requires containment of every closed ambient interval, including null segments | Intrinsically defined regions are meaningful, but an embedding's restricted order need not equal intrinsic order. Non-convex embeddings need a separate contract, not the flat volume formula |
| Causality | Time orientation, intrinsic global hyperbolicity and, when embedded, explicit ambient causal convexity | Actual two-graph containment in `TwoFaceGeometry`; null-cap containment in `NullGeometry` | No replacement of ambient containment by the words “globally hyperbolic”; general ambient/atlas formulation #81 |
| Metric / bulk | General smooth Lorentzian metric; independently defined scalar curvature and volume | Flat action/transport only; zero bulk in existing global limits | Nonconstant-conformal 4D feasibility #73, exact foundation #93, components #74/#75, assembly #76; general metrics remain #81 |
| Compactness | First precise core: compact closure, hence finite volume. Finite-volume noncompact geometries remain a separate target question | Bounded caps, compact faces and joints | Noncompact exhaustion requires full signed-action tail control, not just finite volume; register N below |
| Boundary regularity | Smooth core in §3 in every dimension; finite-regularity refinements stated separately | Original **C³** global two-graph class, unchanged | No automatic C³ sufficiency in higher dimensions. #78 tests fractional/higher jets; smoothness alone is not their proof |
| Slope / presentation | No global graph coordinate or combined slope budget in the general core | `AdmissibleTwoFace`: height-positive-part and future-envelope constants whose **sum is less than one** | Independent-face enlargement #85; general atlas/globalization remains #81/#86. §5 gives an example outside even transported old presentations |
| Joint / angle | Intrinsic positive metric on a spacelike joint; both future timelike normals on spacelike faces; positive transverse angle | `TwoFaceAngle`, `TwoFaceSurface`, `TwoFaceCharts`, `JointTransport` | General-dimensional/curved independent area and angle; no arbitrary measure supplied as “the target” |
| Integrability / margins | Compact smooth spacelike core derives finite area, positive minimum angle and absolute integrability; singular branches must state their own integrability | These consequences are derived for the original class, not fields in admissibility | No density-dependent margins; small-angle uniformity, null transition and finite-integral degeneracies are separate gates |
| Strata | All past/future intersections, all components, null/spacelike types, same-side seams, tips and higher corners must be inventoried | Original class has exactly two labeled faces and their joint; concrete null cap has a separate algebraic target | Smooth spacelike core excludes extra strata explicitly; null/mixed pilot §6 has one specified tip. Arbitrary extra strata remain on #24 |
| Topology / caustics | No simply-connected assumption. General target cannot silently forbid conjugate points or topology | Multiple components allowed; positive-height critical points allowed | Smooth joint torus is an inclusion test. Topology change, null cut loci, generator caustics and nonsmooth creases need explicit treatment, not deletion as measure-zero sets |
| Limit / review | Fixed region, metric, margins and regulators before density tends to infinity; expectation only | `twoFaceLimitGoal`, `twoFaceExpectedLimitGoal`; fixed-cutoff long cancellation | No rate, shrinking-cutoff uniformity, variance or sample-wise result. Early independent review #94 and final human review #86 remain separate |

Authorities for the checked column:
[`TwoFaceContract`](../formal/BoundaryDraft/TwoFaceContract.lean),
[`TwoFaceLimit`](../formal/BoundaryDraft/TwoFaceLimit.lean),
[`ExpectationBridge`](../formal/BoundaryDraft/ExpectationBridge.lean),
[`NullCapLimit`](../formal/BoundaryDraft/NullCapLimit.lean),
[`ExpectedLimits`](../formal/BoundaryDraft/ExpectedLimits.lean), and the
[dimension ledger §§6–8](dimension-kernels.md#6-non-vacuous-global-contracts-explicitly-still-open).
In particular, #88 proves an actual **full-partner, fixed-regulator local
observable**, not a general-dimensional global limit or expectation theorem.
#89 proves exactly the original restricted contract, not every pair of
individually spacelike faces. Its fixed-cutoff assembly has no missing
shrinking-cutoff step.

## 2. Independent action, order and geometric target

Fix dimension $`d\ge2`$. Let $`\mu_g`$ be Lorentzian volume and let the selected
causal order be specified before any counts. For a finite order $`C`$, write
$`L_k(C)`$ for the number of **ordered**, distinct related endpoint pairs with
exactly $`k`$ strictly intermediate elements. No diagonal, unordered-pair factor
or endpoint count belongs in $`k`$.

Use exactly the published constants and finite recurrence in
[dimension-kernels §§1–2](dimension-kernels.md#1-sources-conventions-and-normalization-table):
$`m=\lfloor d/2\rfloor+1`$, $`a_d=-\alpha_d>0`$,
$`C_{k+1}^{(d)}=k![z^k]P_d(z)`$, $`K_d(z)=P_d(z)e^{-z}`$.
Then define, independently of a continuum limit,

```math
A^{\mathrm{disc}}_{\rho,d}(C)=\rho^{-(d-2)/d}
 \left[a_d\,\#C-\beta_d\sum_{k=0}^{m}C_{k+1}^{(d)}L_k(C)\right].
```

For $`d>2`$ this is $`l_p^{d-2}S^{(d)}/\hbar`$, with
$`\rho=l^{-d}`$. For $`d=2`$ it is $`S^{(2)}/\hbar`$: no definition involving
$`1/(d-2)`$ is used. The 4D bracket is
$`(4/\sqrt6)(N-L_0+9L_1-16L_2+8L_3)`$; the 2D bracket is
$`2(N-2L_0+4L_1-2L_2)`$.

Construct the Poisson law of intensity $`\rho\mu_g|_M`$ separately. In the
isolated **ambient-order restriction** regime define

```math
\begin{aligned}
V_M(x,y)&=\mu_g\bigl(M\cap(I(x,y)\setminus\{x,y\})\bigr),\\
\mathcal A_{\rho,d}(M,g)&=\rho^{2/d}\left[a_d\mu_g(M)-\beta_d\rho
 \int_M\!\int_{M\cap J^+(x)}K_d(\rho V_M(x,y))\,d\mu_g(y)d\mu_g(x)\right].
\end{aligned}
```

Here $`I(x,y)`$ is the **closed** interval of that order. Null endpoints and
the diagonal have zero volume under the geometric instances; prove this when
instantiating, rather than redefining counts. For an intrinsic region, first
replace the order and intervals by the intrinsic ones. Global hyperbolicity of
the intrinsic metric does not identify these two constructions. In the
embedded regime the count can include sprinkled elements outside $`M`$;
its parameter is the ambient interval volume. Causal convexity equates it
with $`V_M`$. Without containment the parameters, and generally the actions,
differ (DLL §2.4). In curvature, **never** substitute the flat proper-time
volume law for $`V_M`$.

Finite-density expectation equality is an output: Mecke plus interval Poisson
counts, atomlessness and absolute integrability. On a finite-volume region
$`L_k\le N^2`$ and finite Poisson second moments control the finite signed sum.
The existing generic probability APIs can supply this argument; their curved
and dimension-indexed geometric instances still have owners #93 and #77.

### Curvature sign, not just metric signature

Use signature $`(+,-,\ldots,-)`$ and the curvature convention

```math
\begin{aligned}
R^a{}_{bcd}&=\partial_d\Gamma^a_{cb}-\partial_c\Gamma^a_{db}
 +\Gamma^a_{de}\Gamma^e_{cb}-\Gamma^a_{ce}\Gamma^e_{db},\\
R_{bd}&=R^a{}_{bad},\qquad R=g^{bd}R_{bd}.
\end{aligned}
```

This is the sign choice for which in 4D, with $`g=\Omega^2\eta`$,
$`R=6\Omega^{-3}\Box_\eta\Omega`$. Thus $`\Omega=1+bt^2`$ gives
$`R=12b/(1+bt^2)^3`$, agreeing at the origin with Dowker (2020), (2.8),
after signature conversion. A consumer using the opposite Riemann convention
must convert the scalar sign, not copy $`R/2`$ solely from a signature label.
#73 owns its production curvature convention and must record that conversion;
#93 does not need curvature to prove its finite-density identity.

Define $`dA_g`$ on each spacelike joint by the Riemannian metric $`-g|_{TJ}`$,
not by ambient Euclidean Hausdorff measure. For the spacelike/spacelike part,
use future-directed unit timelike normals $`n_-,n_+`$ (past inward, future
outward), $`C=g(n_-,n_+)>1`$, and define

```math
\mathcal T_{\mathrm{SS}}(M,g)=\frac12\int_M R\,d\mu_g
 +\int_J\frac{C}{\sqrt{C^2-1}}\,dA_g
 =\frac12\int_M R\,d\mu_g+\int_J\coth\theta\,dA_g.
```

No action, overlap jet, cancellation, limit or expectation identity enters
these geometric definitions. Analytic lemmas may assume jets; geometric
admissibility may not.

## 3. A precise non-vacuous general core candidate

**Candidate G-SS, unproved.** For each integer $`d\ge2`$, let the ambient
spacetime be a smooth, time-oriented globally hyperbolic Lorentzian manifold.
Let $`M`$ be a nonempty precompact open ambient-causally-convex region. Require:

1. The entire frontier is the union of compact embedded smooth spacelike
   hypersurfaces-with-boundary $`\Sigma_-`$ and $`\Sigma_+`$, each possibly
   disconnected, with disjoint relative interiors and common boundary exactly
   the compact smooth embedded codimension-two submanifold $`J`$.
2. Each labeled face is achronal, respectively past and future for the region.
   At $`J`$ its two conormals are linearly independent. Empty $`J`$ is allowed
   for compact-Cauchy-surface slabs; no topology or connectedness is imposed
   beyond the ambient spacetime assumptions.
3. There are **no other boundary strata** in this core. Geometry is fixed.
   Smoothness is a sufficient candidate regularity, not a claim of minimality
   or a proof of the required overlap regularity.

Prove that the expectation of the independently defined discrete action tends
to $`\mathcal T_{\mathrm{SS}}`$, by proving the deterministic limit and the exact
finite-density identity separately. This quantifies over arbitrary metrics,
dimensions, topology and face atlases in the stated class, not over graphs in
a privileged coordinate system or only small normal neighborhoods. It contains
both bulk and varying-angle terms. It does **not** assert a result yet.

The joint tangent metric is positive because it lies in a spacelike face.
Distinct future unit normals give $`C>1`$. Compactness and smoothness then give
finite area, a strictly positive minimum angle for each fixed nonempty joint,
and absolute integrability of both terms. These are geometric consequences,
not assumptions that a totalized Lean integral has its intended value.
No quantitative margin uniform over the whole class is claimed. Conjugate
points of interior null geodesics are not excluded by G-SS; this is precisely
one of the general-curved risks that a proof must handle.

**Nonvacuity in every target dimension.** In spatial dimension $`d-1`$,
$`h(x)=a(1-|x|^2)`$, $`f(x)=\epsilon\sin x_1`$ with
$`a,\epsilon>0`$, $`2a+\epsilon\lt 1`$ give smooth flat members with regular
sphere joint (two points in 2D); see the explicit dimension-ledger construction.
The origin's height critical point is permitted. This is not an all-dimensional
Lean instance or limit theorem.

**Nonvacuity with both terms present.** Take the existing unequal-axis cap
$`h(x)=\frac14(1-x_1^2-x_2^2/4-x_3^2/9)`$, $`f=0`$, and
$`\Omega=1+bt^2`$, $`b>0`$, on Minkowski space. The causal cones, convexity
and joint angles are unchanged by the conformal factor. On the compact region
$`-h\lt t\lt 0`$, the scalar curvature above is positive, so the bulk integral is
strictly positive. At the joint $`t=0`$ the conformal factor is one: the old
weights 2 and 6 at axis endpoints and the joint integral $`48\pi`$ remain.
The geometry therefore has nonzero bulk **and** variable angle. This is a
conventional witness, not a new curved Lean limit. General metrics need not
be conformally flat; this example does not redefine G-SS.

**Exclusions and retained branches.** Smoothness avoids choosing an unjustified
finite regularity in higher dimensions. Compact closure avoids an unproved
tail/exhaustion interchange. Transversality excludes the nonintegrable
zero-angle singularity from this first core. Null faces cannot have unit
timelike normals; they need §4, not a formal evaluation of this formula at
infinity. Tips, same-side creases and extra corners invalidate item 1, and their
zero ambient volume does not imply zero action contribution. All these branches
stay visible in §7 and on #24; proving G-SS alone would not settle the intended
null/mixed or more singular coverage.

### Lean contract examples and the encoding boundary

The following are literal examples of **existing** interfaces, excerpted from
`TwoFaceContractRegression.lean` and `TwoFaceLimit.lean`; their proofs belong to
the baseline, not this contract package:

```lean
example : TwoFaceExpectedLimitGoal =
    (∀ h f, AdmissibleTwoFace h f →
      Tendsto (fun ρ => ∫ c, discreteBDGAction ρ c
        ∂FinitePoisson.law (ENNReal.ofReal ρ • volume.restrict (twoFaceRegion h f))) atTop
          (𝓝 (twoFaceBoundaryIntegral h f))) := rfl

example : TwoFaceLimitGoal := twoFaceLimitGoal
example : TwoFaceExpectedLimitGoal := twoFaceExpectedLimitGoal
```

For the general port, the required **Lean declaration design** is below.
Names prefixed `General` are proposed API slots, **not declarations currently
implemented or typechecked**. Their meanings are exactly G-SS and §2, not
arbitrary oracle functions. This records the input/output contract before
proof work without inventing a Lorentzian-manifold implementation in #90:

```lean
-- Proposed schema, not a theorem or a compilable library excerpt.
-- GeneralSpacelikeRegion encodes only G-SS's metric, sets and geometry.
-- The action, Poisson law, curvature, joint metric and normals are constructed
-- independently as in §2; none is an admissibility conclusion.
def GeneralDeterministicGoal : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (G : GeneralSpacelikeRegion d),
    Tendsto (fun ρ => generalContinuumAction ρ G) atTop
      (𝓝 (generalBulkIntegral G + generalJointIntegral G))

def GeneralExpectedGoal : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (G : GeneralSpacelikeRegion d),
    Tendsto (fun ρ => ∫ c, generalDiscreteBDGAction d ρ c
      ∂generalPoissonLaw ρ G) atTop
      (𝓝 (generalBulkIntegral G + generalJointIntegral G))
```

An implementation must construct the volume/order/intervals and geometric
objects, prove nonempty instances including the curved witness, and discharge
measurability/integrability. Accepting arbitrary functions named “action” and
“target”, or putting either goal in `GeneralSpacelikeRegion`, would not encode
this contract. #91/#92 and #93 own the first concrete ports; #81 owns the
missing manifold-level generalization. No Lean source is changed here and no
new Lean verification or integrated audit is claimed.

## 4. Null/mixed taxonomy and two different singular limits

All cases below refer to **past–future** joints with positive induced screen
metric. A meeting of two patches of the *same* past or future face is a crease,
not automatically one of these joints.

| Joint | Intrinsic data and normalization | Candidate coefficient / status |
| --- | --- | --- |
| Spacelike/spacelike (SS) | Two future unit timelike normals; $`C>1`$, positive rapidity, induced joint area | $`C/\sqrt{C^2-1}`$; checked only in the original 4D class |
| Spacelike/null (SN) | Future unit timelike normal $`n`$ and future null normal ray $`[k]`$; positive $`g(n,k)`$; actual generator/affine-scale data if derivatives along the null face are used | Candidate unit weight for a regular transverse joint. Direct fixed-null proof needed; no finite canonical rapidity from the ray alone |
| Null/null (NN) | Two distinct future null rays $`[k],[\ell]`$ with $`g(k,\ell)>0`$, screen metric and generator data | Candidate unit weight; diamonds calibrate it. Coincident rays are a degenerate case, not a regular NN joint |

Here “candidate unit weight” means the proposed extension

```math
\mathcal T_{\mathrm{reg}}=\frac12\int_M R\,d\mu_g
 +\int_{J_{\mathrm{SS}}}\coth\theta\,dA_g
 +\int_{J_{\mathrm{SN}}}dA_g+\int_{J_{\mathrm{NN}}}dA_g.
```

It does not silently assign zero to tips or other strata. A general stratified
theorem with this target is unresolved; §6 proposes only one explicit pilot.
If another stratum contributes, the target must be corrected with evidence.

**Why normal scales matter.** Under independent positive rescalings,

```math
\begin{aligned}
k\mapsto\alpha k &: \quad \log g(n,k)\mapsto\log g(n,k)+\log\alpha,\\
(k,\ell)\mapsto(\alpha k,\beta\ell)&:
 \quad\log g(k,\ell)\mapsto\log g(k,\ell)+\log\alpha+\log\beta.
\end{aligned}
```

Thus a logarithmic null angle requires marked normals and a reference scale
(if its argument has units). On SN one can fix $`g(n,k)=1`$ at the joint,
then extend $`k`$ affinely along each generator. On NN the convention
$`g(k,\ell)=2`$ still leaves reciprocal rescalings; an auxiliary timelike
field or separate affine markings fixes those. These choices are gauges to
record and test, not extra physical inputs to the unchanged discrete action.
If $`\nabla_k k=\kappa k`$, then rescaling gives
$`\kappa'=\alpha\kappa+k(\alpha)`$ and screen expansion scales by
$`\Theta'=\alpha\Theta`$. Any proposed expression involving these must
have its gauge dependence accounted for. Unit joint weight and induced area
are scale invariant; invariance alone does **not** prove they are the full
answer. Sorkin's marked-null angle convention is not permission to replace
the BDG weight by a continuum gravitational-action logarithmic corner term.

**Small positive angle is not a null face.** With finite timelike normals,
$`\theta\downarrow0`$ means coincident normals and
$`\coth\theta\sim1/\theta`$. Keeping one face timelike and sending the other
toward a distinct null ray instead drives $`\theta\to\infty`$ and
$`\coth\theta\to1`$. For a planar face and slope $`s\in(0,1)`$, the weight
is $`1/s`$: $`s\downarrow0`$ and $`s\uparrow1`$ are opposite endpoints.
If both faces approach the *same* null direction their relative rapidity can
have different limits depending on the path; regular joint transversality
may fail. Neither this elementary coefficient limit nor a pointwise metric
limit permits interchange with density, cutoff removal or the joint integral.

**Inventory, not a general null theorem.** The checked cap is precisely
`nullCapRegion T a` with $`0\lt a\lt T`$, the open diamond from $`(-T,0)`$ to zero
cut by $`t-x_1>-a`$. Its deterministic and expected limits equal the algebraic
`nullJointArea T a` $`=\pi a(2T-a)`$. `NullGeometry` checks containment;
`NullCapLimit` does not give general induced-null-joint geometry or arbitrary
stratified null coverage. The endpoints $`a=0,T`$ are not in that theorem.
Flat diamonds have the known target $`S_{d-2}(T/2)^{d-2}`$ (2 in 2D,
$`\pi T^2`$ in 4D); see the literature audit for the explicit dimensional
range actually established in the inspected source. The dimensional kernel
ledger's finite-density diamond series is not an all-dimension asymptotic
proof. Neither calibration is obtained by an automatic spacelike/null limit.

## 5. Inclusion, exclusion and a genuinely steep test

- **Included old examples:** every old planar cap, unequal-axis ellipsoids,
  the damped quartic with its interior critical point, and the genuinely
  nonaffine sine future face. See `TwoFaceExamples.lean` and its regression.
  No requirement of a nonzero height gradient in the whole interior is added.
- **Included topology test:** the thin solid-torus height
  $`h=a[\delta^2-(\sqrt{x_1^2+x_2^2}-R_0)^2-x_3^2]`$ with
  $`R_0>\delta>0`$, $`2a\delta\lt 1`$, and $`f=0`$. Its positive part is
  globally $`2a\delta`$-Lipschitz, and near its closed positive set the axis
  singularity is absent. Its joint is a regular torus with gradient norm
  $`2a\delta`$. This conventional inclusion test shows why “sphere” or
  “simply connected” must not enter the contract. The numerical/symbolic
  regression checks the parameterization, not a Lean topology theorem.
- **Curved bulk and variable angle:** the conformal ellipsoid in §3.
- **Not G-SS:** the checked null cap, diamonds and §6's mixed regions have
  null faces/tips. Exclusion from this core is not exclusion from #24.

For #85 fix $`s=3/4`$ and consider the rotationally symmetric region

```math
M_s=\{(t,x):|x|\lt 1,\quad
 -\tfrac{s}{2}(1-|x|^2)\lt t\lt\tfrac{s}{2}(1-|x|^2)\}.
```

Both raw face germs are smooth and have slope at most $`s\lt 1`$ on the closed
ball; their causal envelopes are respectively minus/plus
$`s(1-|x|^2)_+/2`$, each globally $`s`$-Lipschitz. The region is their strict
epigraph/hypograph intersection, hence ambient-causally-convex and bounded.
There are exactly the two faces and the regular sphere joint. The thickness
positive part has optimal Lipschitz constant $`2s=3/2`$, so even the same-height
planar reference cap fails the old hypothesis. The old combined budget would
require at least $`3s=9/4`$.

This is not merely a poor choice of one Lorentz frame. For any common boost
with speed $`0\le v\lt 1`$, rotational symmetry lets us choose the antipodal
joint points along its axis. The transformed future slope maximum is at least
$`u=(s+v)/(1+sv)`$, and at one of those points the slope difference is
$`\Delta=2s(1-v^2)/(1-s^2v^2)`$. Any old combined constants must bound
$`u+\Delta`$. Direct algebra gives

```math
u+\Delta-1=
 \frac{(1-v)[3s-1+(3s-s^2)v]}{1-s^2v^2}>0
 \qquad(s=3/4,\ 0\le v\lt 1).
```

Rotations, translations and positive dilations do not evade this necessary
bound. Thus the example lies outside the old class and its known transported
presentations. This is a conventional geometric argument, with symbolic
regressions, **not** a newly proved BDG limit. #85 must audit the surviving
jets and replace the invalid planar comparison, rather than rename the class.

**#85 handoff:** [the independent-face audit](independent-face-extension.md)
now states the larger class and proves its region/stratum/area geometry in
writing. It exhibits a closed-interval containment failure and an actual
short-null overlap discrepancy for the same-height reference cap, derives the
actual local two-jet and replacement long-ray bounds, and records the bounded
[direct-origin replacement #97](https://github.com/q5m-ai/causal-set-emergence/issues/97).
This is the obstruction branch of #85, **not
new global limit coverage**. No original Lean contract or theorem is changed;
independent human review remains outstanding.

## 6. Selected first flat 4D mixed pilot for #83 / #84

**GO, directly at fixed null geometry.** Put the future tip at zero. Choose a
smooth globally Euclidean-Lipschitz $`H:\mathbb R^3\to\mathbb R`$ with constant
$`\lambda\lt 1`$ and $`H(0)>0`$, all fixed. Define

```math
M_H=\{(t,x):-H(x)\lt t\lt -|x|\},\qquad
D_H=\{x:|x|\lt H(x)\}.
```

The lower face is spacelike; the upper face is the past null cone of zero,
smooth except at its single specified tip. Along each $`\omega\in S^2`$,
$`r-H(r\omega)`$ starts negative, grows with derivative at least
$`1-\lambda`$, and tends to infinity. Hence it has a unique positive root
$`r_H(\omega)`$, smooth by the implicit function theorem, with fixed bounds

```math
\frac{H(0)}{1+\lambda}\le r_H(\omega)
 \le\frac{H(0)}{1-\lambda}.
```

Thus the domain is bounded, the mixed joint is the smooth spacelike surface
$`\psi(\omega)=(-r_H(\omega),r_H(\omega)\omega)`$, and the complete frontier
has lower face, null face, this joint and the cone tip (no lateral wall or
unrecorded seam). The null metric calculation cancels both radial derivative
terms, giving the independently defined target

```math
-g(d\psi,d\psi)=r_H^2\,d\omega^2,\qquad
\mathcal J_H=\int_{S^2}r_H(\omega)^2\,d\omega.
```

The lower epigraph is a future set, and the cone interior is a past set.
Their intersection is open and ambient-causally-convex. For each source in it,
**every** future partner up to the tip stays above the lower face, so the
full-partner interval reduction is a promising route; proving and instantiating
its exact integration identity is work for #83, not an assumed limit here.

An explicit member is $`H(x)=T+\epsilon\sin x_1`$ with
$`T>\epsilon>0`$, $`\epsilon\lt 1`$. Its lower face is genuinely nonplanar on the
region, its radial joint varies, and it is not the already-checked all-null
plane cut (causal face type is invariant under Lorentz transformations).
“New member” here means outside that repository calibration, not a novelty
claim against the literature. The constant $`H=T`$ member provides a round
mixed calibration with candidate area $`4\pi T^2`$.

Use future null normal $`k=(1,-\omega)`$ on the upper face and future unit
normal $`n=(1,-\nabla H)/\sqrt{1-|\nabla H|^2}`$ on the lower face.
Then $`g(n,k)=(1-\nabla H\cdot\omega)/\sqrt{1-|\nabla H|^2}>0`$;
§4's joint normalization is available. The target does not depend on that
scale. #83 must compute the actual signed coefficient at fixed geometry,
control the tip and all nearly-null partners, and state precisely which
remainders remain for #84. #84 must prove global summability, tip behavior,
independent area identification and the actual 4D Poisson transfer. A local
unit coefficient alone is insufficient. No smoothing family or density/null
limit interchange is authorized. This pilot does not cover NN joints,
curved-null geometry or other dimensions.

**#83/#84 handoff:** the [fixed-null estimates](null-mixed-estimates.md) and
[written expected-action assembly](null-mixed-assembly.md) now cover exactly
this selected flat 4D class. The latter proves the geometric bridge hypotheses,
complete strata, global deterministic induced-area limit and exact Poisson
transfer without dropping any partners or cutoff complements. These are written
proofs with executable regressions, not new Lean-checked mixed-region results;
independent human review and the broader branches in the matrix remain open.

## 7. Obstruction register and falsifiable tests

The tests in `test_general_contract.py` check algebra and explicit examples;
they do not decide the conjecture. Each STOP below is a stop on a **route or
claim**, not a full-action counterexample.

| ID | Inclusion/exclusion test and exact missing result | Decision / retained owner |
| --- | --- | --- |
| S: independent slopes | §5's smooth capsule has spacelike faces in every presentation but violates the old budget in every common Lorentz frame; its same-height planar cap is not spacelike | GO #85 on independent causal envelopes; STOP reuse of the old planar comparison without replacement |
| A: angle degeneration | Plane/slope weight has different limits at slope zero and slope one. A vanishing angle may make the joint integral infinite even with finite area | Fixed positive-margin G-SS only for now; integrable degeneracies and uniform families remain #24/#81 |
| C: extra corners | Replace a smooth future graph locally by the minimum of two distinct spacelike planes; the one-sided derivatives disagree at their ridge | Not G-SS. Inventory same-side crease, its intersection with J and triple corners; derive the full normalized contribution before claiming zero. #86 retains this branch |
| T: topology | Solid-torus height has regular joint; compact spatial-cylinder slabs can have empty J. Conversely disconnected temporally separated diamonds have ambient cross-pairs absent from a componentwise intrinsic order | Include regular topology; retain all cross-pairs for the selected order. Topology-changing trousers are not smooth globally hyperbolic core regions; their published divergences do not refute G-SS |
| F: focusing / conjugate points | Inward null generators from a round sphere have transverse Jacobian proportional to the square of remaining affine radius, vanishing at the tip | Tip explicitly present in §6; no generic no-caustics theorem. For interior conjugate points or null cut loci, local RNC expansions cannot cover all partners; #73/#81 must control or identify their contribution |
| N: noncompactness | A constant-height Minkowski slab has infinite volume; finite Poisson construction is not applicable. Even finite volume alone supplies no normalized signed-action tail bound | STOP unqualified noncompact extension. Missing result: exhaustion-independent full-action tails and target integrability. Retain under #24/#81, not a renamed compact theorem |
| D: dimensional jet | Actual long amplitude must have the critical little-o remainder of real order d/2; odd half-orders and critical logs can survive normalization | #78 begins with 3D and bounded 5D/6D transfer tests; no jet field in geometry. #79 keeps odd positive first moments and even divergent second moments |
| P: partitions | First-endpoint partition sums to one, but each cell still pairs with the complete region | #74/#75/#79/#84 must preserve cross-chart partners and cancel artificial cutoff/weight-derivative terms in the full sum |
| B: curvature / nonlocality | Local interval Taylor remainder at short coordinate distance does not control macroscopic nearly-null pairs with small interval volume | #73 needs a falsifiable normalized signed estimate, not just the R/2 coefficient; #76 cannot assemble an obstruction report as a theorem |
| L: attribution | Chevalier 2023 primary text not retrieved; 2015 source gives explicit finite dimensional range, not the all-dimension proof previously attributed to it | STOP novelty certification. See literature audit; #81/#86 must resolve proof provenance or supply the missing general result |

No new catch-all issue is opened: these named gaps already have coverage
owners. A subsequent bounded follow-up must specify the missing estimate,
geometric construction or provenance result and its actual dependencies.
The core excludes no dimension at least two merely because its pilot is hard.

## 8. Exact downstream handoff contracts

All outputs use §2's normalization, fixed geometry and isolated interval
regime. “GO” means a well-defined task, not that its conjectured output is true.

| Owner | Input | Required output / gate |
| --- | --- | --- |
| #73 | Original `AdmissibleTwoFace`; smooth positive nonconstant conformal factor bounded above/below near closure; #93's actual restricted-volume observable | Curvature convention and source conversion; compatible local/nonlocal split; one proved normalized controlling estimate or precise obstruction; GO/NARROW/STOP for #74/#75 |
| #74 | #73's viable class/split and #93's proved finite-density API | Bulk component tending to the independently defined half-curvature integral, with signed local **and** long-partner remainders and every cutoff derivative accounted for |
| #75 | Same class/action/split as #74; independent curved area and angle | Joint component tending to that geometric integral plus any explicitly retained compensating partition terms; prove weighted estimates if used, not a citation to an unencoded estimate |
| #76 | Compatible proved #74/#75 outputs and #93 bridge | Full deterministic bulk-plus-variable-angle limit, then expected limit on exactly that controlled class; no general-metric promotion |
| #77 | Published dimension coefficients, generic finite Poisson machinery, #91 physical interval geometry | Actual finite-order observable and exact positive-density restricted-volume expectation; identify flat `dimensionWeightedAction` only after containment and interval-volume proofs; 2D/4D calibrations |
| #78 | #92's fixed 3D region/area contract and actual overlap; checked analytic cancellation lemma from #88 | Actual fixed-cutoff long disintegration and sufficient geometric jet, or an identified surviving term; explicit 5D/6D transfer/regularity ledger |
| #79 | Same #92 class/decomposition as #78 and #88's full-partner local observable | Complete short limit with cutoff-independent geometric coefficient, retaining parity terms; if planar comparison is used, also prove the global planar base limit |
| #80 | #77/#78/#79 proved outputs on their identical supported class | Global deterministic limit and then expectation transfer; record precise dimension/regularity range, not all-dimension inference |
| #81 | Actual outcomes of #76/#80, this full matrix, #91/#92 geometry and remaining branches | Keep all unsupported dimensions, general metrics, atlas/globalization, finite-regularity and noncompact questions visible; open bounded proof tasks only after identifying their missing results |
| #83 | Exactly §6's smooth Lipschitz H, fixed null cone, independent area and normal conventions; unchanged 4D action | Direct fixed-null signed coefficient/estimates, exact all-partner reduction if used, explicit tip and nonlocal remainder interface; at least the sine member, not only round calibration |
| #84 | §6 geometry and proved #83 outputs | Measurability/boundedness/containment, full strata, missing global/tip control, deterministic area limit, then old 4D bridge with real hypotheses discharged; no dependency on #81 |
| #85 | Independent strict causal-envelope/face bounds, C³ germs near compact regular joint, §5 witness | Geometry/area construction and audit of each old proof step; replacement route and full enlarged limit if possible, otherwise rigorous route obstruction and bounded replacement task |
| #86 | Actual contracts/proofs, all unresolved rows, early #94 findings | Final integrated coverage and independent human review against #24's unchanged criterion; no automatic epic closure from successful pilots |

#91 owns dimension-indexed interval volume and Lorentz/measure transport;
#92 owns independent dimensional two-face geometry/nonvacuity/area, beginning
in 3D. #93 alone owns the initial curved finite-density production API and any
shared probability extraction; this document does not compete with it. The
agreed #73/#93 pilot is compatible with §2, but is a proper subset of G-SS.
No downstream consumer may add an expectation identity, cancellation estimate
or desired jet to geometric admissibility to satisfy this handoff.

## 9. Validation and review status

- **Written here:** candidate definitions, conventional example arguments,
  normal-rescaling derivations, source audit and bounded decisions.
- **Machine checked previously:** only the exact Lean declarations cited in
  the baseline. No `.lean` file or old hypothesis is modified here; the general
  Lean schema is explicitly unimplemented. Any subsequent Lean implementation
  must run the full integrated `formal/check.sh` source/transitive-axiom audit
  on its exact head, not merely the incremental developer mode.
- **Executable diagnostics here:** `python -m unittest -v test_general_contract`
  checks the steep boost obstruction, curvature sign, null rescalings, distinct
  singular limits, mixed screen metric, and topology/stratum negative controls.
  Symbolic identities and finite samples are not new geometric limit proofs.
- **Repository checks:** `check_symbolic.py`, full Python tests, `reproduce.py`,
  `python3 check_markdown.py`, and `python3 -m unittest -v test_check_markdown`.
  GitHub browser rendering is a separate check, not certified by Markdown lint.
- **Independent human review:** not supplied by this implementation. #94 and
  #86 remain required. Neither source reading nor automated PR feedback is a
  substitute for mathematical/physical peer review.
