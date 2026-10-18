# Causal Set Emergence

Research into how continuum spacetime geometry, gravitational action, and
possibly dynamical laws can emerge from discrete causal order.

This repository now has two deliberately separated layers:

1. **A rigorous continuum-limit proof program** whose checked base cases concern
   the four-dimensional Benincasa–Dowker–Glaser (BDG) causal-set action and
   whose strategic target is the general boundary and joint conjecture.
2. **An exploratory emergence program** collecting conceptual notes,
   visualizations, and research questions about causal growth, quantum
   histories, and automaton-like dynamics.

The first layer contains mathematical claims with explicit verification status.
The second is a research agenda, not an assertion that an automaton model or a
complete causal-set dynamics has been found.

> **Research status:** the repository is public; independent human mathematical
> acceptance and manuscript publication are not established by that visibility.
> Formal verification checks the encoded statements, not novelty or unencoded
> physical applicability. No new launch or submission is recorded here.

## Human-facing research review package

Start with the [one-page account](research/README.md), then the
[compact manuscript](research/manuscript.md), [WORKS / FAILS / UNKNOWN matrix](research/coverage.md),
[expert reading packets](research/review.md), and [reproducible artifact](research/artifact.md).
The [static review page](site/research.html) works without JavaScript and prints
as a reading copy. Mathematical sources are pinned to integration commit
`9e0068f91c219fe61984d20fdb3f6939eab907c4`, not the moving `main` branch.

Priority scrutiny: the **written curved-4D complete-action obstruction** and
**corrected universal flat dimension theorem**, with the positive curved
subclasses kept distinct from a universal corrected theorem. The package is
prepared, not launched or submitted; no independent human acceptance or full
Lean certification is claimed. Unmerged #180 stays separate. The bounded
[experimental assessment returns B](research/experiments.md): a model-to-observable
calculation is missing, not a new publication prerequisite or #24 closure condition.
Earlier dated source/issue receipts below retain their historical scope.

## Why “emergence”?

A causal set begins with very little: discrete elements, causal order, and local
finiteness. A successful theory must explain how familiar continuum structures
appear at larger scales—including manifold structure, topology, Lorentzian
metric, dimension, locality, and the geometric field described as gravity in
general relativity.

The current proofs study one controlled part of that bridge. Given causal sets
obtained from increasingly dense Poisson sprinklings into specified continuum
regions, does the discrete BDG action recover the expected continuum geometric
term? This is a necessary consistency test, but it runs from a known continuum
target toward its discrete approximation. It does **not** yet derive spacetime
or gravity from unconstrained microscopic dynamics.

The longer-term question is complementary: can covariant causal growth or
rewriting rules make manifold-like causal sets and their effective physics
emerge without assuming a background lattice, global clock, or preferred
frame?

## Program 1 — BDG continuum limits

[The analytic proof draft](notes/first-attempt.md) studies the flat-space
specialization of [Conjecture 1′, equation (11)](https://arxiv.org/html/2501.00139v2#S2.E11)
in Dowker–Liu–Lloyd-Jones:

```math
 \lim_{\rho\to\infty}\mathcal A_\rho(M)
 =\int_J\coth\theta\,dA,
 \qquad
 \mathcal A_\rho=\frac{l_p^2}{\hbar}\,\mathbb E S^{(4)}_\rho.
```

In **3+1-dimensional Minkowski space**, the draft gives arguments for these
restricted classes, pending independent mathematical review:

1. **One-null-tip regions**, including a causal diamond with `T>0` cut by
   the null plane `t-z=-a`, retaining `t-z>-a`, with `0<a<T`. The limiting
   normalized mean action is `π a (2T-a)`, equal to the joint area.
2. **Spacelike graph caps with a planar future boundary**, under the stated
   regularity, strict-spacelikeness, and transversality assumptions. The limit
   is `∫∂Ω 1/|∇h| dA = ∫J coth(θ) dA`.
3. **A connected variable-angle family:** unequal-axis ellipsoidal graph caps,
   with explicit limit `2π b₁b₂b₃/a`.

The argument performs the complete future-point integral before taking the
limit. This avoids an unjustified coordinate-local approximation for nearly
null pairs, which can have small interval volume despite large coordinate
separation. The graph-cap argument then uses a signed approximate identity and
the coarea formula.

### Machine-checked boundary

[The Lean layer](formal/README.md) uses pinned Lean 4.19.0 and mathlib. It now
proves the concrete kernel normalization and tails, exact four-dimensional
admissible graph-cap and concrete null-cap action reductions, explicit ellipsoid
height-integration formulae, and the **general deterministic graph-cap boundary
limit**, alongside the original concrete limits:

```lean
theorem AdmissibleGraphCap.graphCapLimit {h : Spatial → ℝ}
    (hh : AdmissibleGraphCap h) : GraphCapLimitGoal h
```

```text
ellipsoidLimitGoal : EllipsoidLimitGoal
nullCapLimitGoal   : NullCapLimitGoal
```

The original restricted **two-face deterministic and expected-action goals**
now also have unconditional Lean proofs, without changing `AdmissibleTwoFace`,
the action, the region, or the induced-area target:

```lean
theorem twoFaceLimitGoal : TwoFaceLimitGoal
theorem twoFaceExpectedLimitGoal : TwoFaceExpectedLimitGoal
```

These cover genuinely curved future faces in the stated four-dimensional
two-graph class, not the unrestricted conjecture or individual sprinklings.

The separate [controlled conformal pilot](formal/CONFORMAL_ACTION.md) now
constructs the curved finite-volume Poisson law and proves its exact
finite-density expectation equals the independently defined restricted-volume
BDG integral. It retains the original two-face coordinate regions and flat API.
A nonconstant admissible conformal factor has independently calculated nonzero
scalar curvature; no curved continuum limit or bulk/joint coefficient is
claimed by this finite-density result.

All public theorems and definitions pass a transitive axiom audit permitting
only Lean’s standard foundations. The general graph-cap and original ellipsoid
proofs retain the whole signed kernel, including its negative tail; the null
proof derives the exact causal-interval cancellation and normalized Gaussian
concentration.

The [dimension-indexed prerequisite layer](notes/dimension-kernels.md) now also
proves the actual signed integrals, parity-dependent tails and moments, unit
reduced-kernel mass, and a fixed-regulator weighted flat local coefficient in
every integer dimension at least two. The bilocal theorem retains all future
partners and assumes neither mass nor convergence. The separate
[finite-geometry bridge](formal/DIMENSION_INTERVALS.md) now proves actual
causal-interval volumes, Lorentz and positive-dilation action transport, and
unchanged 4D coordinate/measure compatibility in the same dimension range.
The separate [dimension-indexed Poisson bridge](formal/DIMENSION_EXPECTATION.md)
now constructs the genuine finite-order action and proves its exact expectation
using actual restricted interval volume, then specializes to that flat action
under ambient causal convexity. It calibrates the dimensionless 2D action and
transports the unchanged 4D action and probability law through the proved
coordinate map. No global two-face limit or sample-wise convergence follows
from that finite-density bridge alone; independent human mathematical review
remains outstanding.
The [dimension-indexed two-face geometry package](notes/dimension-two-face-geometry.md)
now supplies a written region/stratum and intrinsic-area proof, with chart
compatibility, finite target, Lorentz/dilation transport, exact 4D identification,
and the named smooth 3D pilot. That delivery is conventional geometry plus
regressions, not a new Lean geometry theorem. The later formal packages below
now prove the pilot's deterministic/expected goals; broader dimensional goals
remain open.
The follow-on [smooth 3D formal geometry](formal/PILOT3_GEOMETRY.md)
now proves that exact pilot's whole region/strata, intrinsic canonical joint
area with Borel-overlap compatibility and finite-atlas gluing, signed collar
coarea, right-sided density regularity and spatial divergence. It retains the
actual signed causal overlap, compact perturbation tubes and existing Poisson
specialization, and includes admissible disconnected/annular controls, regular
2D endpoint counting, and exact compatibility for every original 4D C³ member.
The [compiled integration interfaces](formal/PILOT3_INTEGRATION.md) do not
supply the separate long/short analytic estimates or a new pilot action limit.

The [3D direct-origin short package](notes/dimension-three-short.md) derives
that same pilot's actual fixed-cutoff short limit conventionally, retaining
the point cancellation, fractional radial responses, future Hessian and
partition derivatives. Its derivative-controlled remainder and independent
target identification have executable regressions, **not new Lean proofs**.
The shared geometry port, long estimate and global assembly remain separate;
this short result does not close the pilot's full-action or expected goals.
The [dimensional long-null analysis](notes/dimension-long-null.md) now derives
actual signed disintegration and fixed-cutoff long cancellation in writing for
every `SmoothPilot3`, including translated contacts and exceptional directions.
Its bounded 5D/6D transfer uses a separately named C⁴ class and a proved regular
small fixed cutoff. That written delivery is not a Lean specialization or a
full pilot limit. The subsequent [actual 3D long formalization](formal/PILOT3_LONG_NULL.md)
constructs the canonical density and full signed disintegration, derives its
contact-uniform averaged jet, and proves normalized long cancellation for
every `SmoothPilot3` at every fixed positive cutoff. It keeps exact/approaching
contacts, completely closing fibres, all components and positive-height critical
points. The [actual 3D short formalization](formal/PILOT3_SHORT.md) separately
proves the direct-origin short response, derivative-controlled remainder and
intrinsic coefficient, at every sufficiently small fixed positive cutoff.

The [5D/6D short-response decision](notes/dimension-five-six-short.md) derives
actual dimension-specific bases, signed fractional/logarithmic responses,
moving-endpoint remainder bounds and the independent intrinsic coefficient
in writing. Its named C⁴ classes match the small-fixed-cutoff C4LongPilot56
long result. It freezes bounded deterministic/expected assembly contracts
and formal prerequisites, with **no new Lean theorem or general 5D/6D coverage**.
The old C³ and broader #81/#24 obligations remain open.

The [all-dimensional Minkowski proof](notes/all-dimensional-flat-limit.md)
now derives actual short and long producers and global deterministic/expected
limits for every integer dimension at least two in the Minkowski-embedded
smooth G-SS core. Graph coordinates are derived, not assumed; no combined
slope budget is imposed. Its finite-regularity bound grows with dimension.
This is a **written theorem, not a new Lean result or independent review**.
General flat-manifold coverage remains under #149; general-metric nonlocality
remains under #151/#81.
The [shared normalization and producer interface](notes/dimension-producer-interface.md)
records both endpoint partitions, point-once allocation and signed cutoff
conversion for #150/#151; it is not a general-metric theorem.

The [first-cut cubic-torus continuation](notes/first-cut-flat-torus.md) proves
in writing the complete deterministic and expected zero limits for every
dimension at least two in the fixed band `L/2 < T < L/sqrt(2)`. It derives the
at-most-two lift geometry, both projected overlaps and the complete matched
long primitive. The actual odd-dimensional fractional overlap term is retained;
its signed normalized response decays. The proof consumes the existing short
theorem and separately discharges the generic dimension-indexed expectation
hypotheses. This is **not arbitrary-flat coverage, a new Lean result or
independent human review**; #149/#81/#24 remain open.

The [general finite-lift reduction](notes/finite-lift-flat-reduction.md) derives
faithful individual developed diamonds and exact physical interval-union/chart
formulas for every flat G-SS region in every dimension at least two. It does
not assume a globally injective developing map. Its critical-order comparison
retains arbitrary multiplicity and self-overlap. It then derives the
sum-volume primitive through cubic order and proves the complete deterministic
and separate expected limits for **all flat G-SS geometries in 2D, 3D and 4D**.
These are written results, not new Lean proofs or independent review.

The subsequent [flat holonomy continuation](notes/flat-holonomy-obstruction.md)
derives a fully matched quartic logarithm for an admissible compact flat
reflection quotient. With the complete physical interval union and short
point cancellation restored, its action has a nonzero limit in **dimension
six** and diverges positively in **every dimension at least seven**, despite
an independently zero target. The actual measured-order bridge transfers
this complete-action obstruction to expectation separately. This is a
**written negative resolution**, not a new Lean theorem or human-reviewed
result. The subsequent [Klein-bottle contact](notes/flat-klein-bottle-obstruction.md)
derives a fully matched fractional term at dimension five's critical order:
a complete nonzero limit in **dimension five** and positive divergence in
**every dimension at least six**. Thus the written dimension coverage is
exhaustive: general positive coverage in 2D–4D, and existence of admissible
counterexamples in every dimension at least five. The
[corrected FLAT theorem and proof audit](notes/corrected-flat-theorem.md)
state the sharp quantifiers and assess #149's original complete-action
negative-resolution route. Classifying every individual higher-dimensional
response is open research, not an additional condition of that route.
**Flat 4D G-SS coverage is general in writing**; the earliest general curved-4D
obstacle is the actual long-interval response through cut/conjugate contacts,
owned by #151/#81. No original scope or observable is changed; independent
human review and any justified formalization remain outstanding.

The subsequent [smooth 3D assembly and coverage audit](formal/PILOT3_LIMIT.md)
combines both actual producers at one common fixed positive cutoff, then uses
the separately proved finite-density expectation identity. `Pilot3Limit.lean`
proves the unchanged `Pilot3DeterministicGoal` and `Pilot3ExpectedGoal` for
exactly `SmoothPilot3`. Standalone regressions retain genuinely curved future
faces, interior critical points, whole disconnected/annular regions and the
unchanged 4D calibration. This is a smooth combined-budget **flat 3D** result,
not the all-dimensional C³ candidate, an independent-envelope dimensional
extension, or a curved/null/mixed theorem. #81/#24 coverage and independent
human review remain open; no rate or sample-wise convergence is implied.

The **concrete ellipsoid geometric interpretation** is also checked separately:
its joint is a smooth regular level with nonzero Euclidean gradient, its angle
lies on the strict positive branch with `coth θ = 1 / ‖∇h‖`, and its variable-angle
surface integral equals `2π (∏ bᵢ) / a`. The surface measure uses a global
sphere-to-ellipsoid parameterization with a checked tangential Jacobian. Unequal
axes give distinct weights on one connected joint; `(a,b) = (1/4, ![1,2,3])`
has weights `2` and `6` at two axis endpoints and integral `48π`.
`SphereSurface.lean` and `EllipsoidHausdorff.lean` now identify this measure
with canonical normalized Euclidean Hausdorff area, including explicit
ambient/subtype transport and absolute integrability. The same `48π` value
is checked independently in both the canonical angle and reciprocal-gradient
integrals, without changing the original ellipsoid hypotheses.

The **general graph-cap exact reduction** is now checked at every positive
density: `AdmissibleGraphCap.graphReduction` proves the unchanged
`GraphReductionGoal h` from `continuumMean`. Bounded positivity and strict
Euclidean Lipschitz control of `max 0 ∘ h` suffice for complete future slices,
causal convexity, compact domination, and vertical Fubini. The API separately
records C³ regularity near the closed positive region and a nonzero differential
only on its zero-level boundary; positive-height critical points remain allowed.
The original ellipsoids instantiate it without stronger hypotheses. A quartic
height profile also instantiates it and has a checked interior critical point.
`GraphCollar.lean` additionally proves that the Euclidean joint is compact and
measurable, and that some uniform positive-height band has no critical points.
Each point of this band has an ambient C³ regular neighborhood and a local
height-flattening chart. `GraphAngle.lean` derives the normals, strict slope
bound, and positive-branch angle identity for every admissible cap.
`GraphSurface.lean` defines a Euclidean Hausdorff surface target, proves its
finiteness and both boundary weights' absolute integrability, and equates their
integrals. `HausdorffGraph.lean` proves the local two-sided Euclidean
Hausdorff comparison of a C¹ graph with its tangent image.
`PlanarIsodiametric.lean` proves the sharp Euclidean planar isodiametric
inequality by two perpendicular Steiner symmetrizations. Together with the
existing disk-covering direction, `HausdorffPlane.lean` proves normalized planar
Hausdorff measure equals Lebesgue measure on every set, including sets of
infinite measure. `HausdorffDensity.lean` supplies closed-ball density uniqueness.
`HausdorffLinear.lean` proves exact tangent-image area on arbitrary sets, using
intrinsic orthonormal range coordinates and the Euclidean Haar determinant.
`HausdorffArea.lean` proves the variable-Jacobian scalar-graph area formula by
local distortion, local finiteness, absolute continuity, and shrinking-ball
ratios. `HausdorffAreaLocal.lean` localizes it to open C¹ domains of continuous
graphs and derives the signed integral identity. `GraphDensity.lean` defines
canonical level measures and height density, proves finiteness and absolute
integrability on a noncritical band, and identifies the zero-height value with
the boundary integral. `GraphAtlas.lean` constructs a finite controlled atlas
of a whole smaller closed collar with smooth subordinate partition weights.
`GraphChartTransport.lean` and `GraphSliceTransport.lean` prove ambient and
canonical level-measure transport with the same checked Jacobian.
`GraphAtlasRepresentation.lean` supplies both finite-sum representations on
fixed chart domains, joint continuity of the local data, and a uniform
integrable dominator. `GraphDensityRegularity.lean` uses dominated convergence
and the overlap-aware sum to prove continuity, measurability, and a uniform
bound for the canonical density on a nonnegative collar, including its
right-hand boundary value. Negative heights have zero canonical density;
two-sided continuity is not claimed. `GraphCoarea.lean` derives **global collar
coarea** with explicit absolute integrability and the signed `planeKernel`
specialization. `GraphEndpoints.lean` derives both endpoint replacements
without excluding unrelated exterior zeros. `KernelCollar.lean` reuses the
one-sided signed-rescaling work from draft PR #29. `GraphLimit.lean` combines
that analytic collar limit with coarea and density regularity on the **same
constructed collar**, and the vanishing spatial remainder from `GraphTail.lean`.
It proves the unchanged `GraphCapLimitGoal h` and identifies the limit with both
canonical boundary integrals. Coarea is used only in the noncritical collar;
no global density regularity is assumed. Independent regressions recover the
original unequal-axis ellipsoid value and retain the quartic's interior critical
point in the tail domain. No admissibility hypothesis is added.

The **separate Poisson-expectation bridge is now proved**, through merged
PRs #44, #46, and #47. The finite sprinkling probability law and the normalized
discrete BDG action are constructed independently of `continuumMean`.
`FiniteSprinkling.expectation_eq_continuumMean` identifies their exact
finite-density expectation with that unchanged deterministic integral for
measurable finite-volume causally convex regions at positive density.
`ExpectedLimits.lean` then transfers the ellipsoid, admissible graph-cap,
and null-cap limits under their original hypotheses. See the
[probability API](formal/FINITE_POISSON.md), [discrete action](formal/DISCRETE_BDG.md),
and [expectation bridge](formal/EXPECTATION_BRIDGE.md).

The null result starts from the unchanged four-dimensional `continuumMean` and
proves the exact logarithmic weight, support, endpoint, absolute integrability,
and density limit under exactly `0 < a < T`. Its expected-action version has the
same hypotheses and algebraic `nullJointArea` target. Arbitrary null boundaries
and a general induced-null-joint area interpretation remain open.

The [ambient covariance and scaling API](formal/ACTION_TRANSPORT.md) also
proves affine time-oriented Lorentz invariance of the unchanged finite-density
action, allowing translations and spatial orientation reversal. Independent
positive dilation gives the second-power action factor and fourth-power density
transformation. Both identities transfer through the existing expectation
bridge. A translated boost of the original unequal-axis ellipsoid and explicit
inverse/dilation checks serve as calibrations, not new curved-face limits.
The [spacelike joint geometry layer](formal/JOINT_GEOMETRY.md) now proves the
induced Lorentzian area and positive two-normal angle for the stated two-graph
subclass, including compact-joint finiteness, absolute integrability, chart
overlap compatibility, affine Lorentz transport, and area dilation scaling.
It recovers the unchanged planar measure and boundary integral exactly.
A boosted unequal-axis joint retains `48π`, while its ambient Euclidean
spacetime area is an explicit negative control. This is geometry, not a new
two-curved-face action-limit theorem.

These results complete the mathematical implementation of the restricted
four-dimensional program, **not** the unrestricted conjecture, a convergence
rate, variance or concentration bounds, convergence in probability, or
almost-sure convergence of individual sprinklings. The
[acceptance and gap-history audit](formal/ACCEPTANCE.md) records the checked
contracts and scope for [tracker #1](https://github.com/q5m-ai/causal-set-emergence/issues/1).

### Strategic direction beyond the checked base cases

Closing issue #1 is the minimum milestone for Program 1, not its final research
target. The follow-on program aims to prove a precise general form of Conjecture
1′, or to replace it with a corrected theorem if its unrestricted formulation
is false. The first qualitative step is to remove the planar-future-boundary
restriction and prove covariant joint localization for two general smooth
spacelike boundary faces in four-dimensional Minkowski space. The later stages
address arbitrary dimension, curved spacetime, and null or mixed joints.

This direction prioritizes a general mechanism over accumulating more explicit
profiles. Restricted families remain valuable as checked base cases and
regressions, but they do not close the general-theorem target. The theorem's
admissible regions, regularity, boundary strata, action regime, angle
conventions, and mode of random convergence must be stated precisely before a
proof can be claimed.

See the [general-conjecture roadmap](notes/conjecture-roadmap.md), the
[general contract and scope gate](notes/general-contract.md), and
[tracking issue #24](https://github.com/q5m-ai/causal-set-emergence/issues/24).
The scope gate separates the general curved/dimensional target from the proved
restricted cases, specifies null/mixed and steep-face pilots, and records
[source-review limitations](notes/general-contract-literature.md). It is a
research contract, not another limit theorem.
The [first two-face contract](notes/two-face-contract.md) now specifies a
restricted global two-graph class, an independent Lorentzian-area target,
nonplanar examples, and explicit geometric/asymptotic goals. The separate
[two-face geometry integration](formal/TWO_FACE_GEOMETRY.md) proves the
region/stratum contract and connects every admissible region to the exact signed
overlap and Poisson-expectation APIs. The [joint-geometry proof](formal/JOINT_GEOMETRY.md)
proves the area and planar-target goals, including intrinsic chart meaning and
transport. The separate [long-null theorem](formal/LONG_NULL_GAP.md) proves
actual-overlap regularity and signed long-pair cancellation at every fixed
positive cutoff. None of these geometric or finite-density identities alone
establishes the full two-face limit.

The [regulated tangent-wedge calculation](notes/regulated-tangent-wedge.md)
now derives the local positive-angle coefficient using a compact first-endpoint
weight and an independently specified bounded regulator. Lean checks its exact
signed action reduction, regulated limit, and scalar error estimate. The proof
notes separately explain invariant area, uniformity away from zero angle, and
exact artificial-complement subtraction with cross-patch partners retained.
This local result does not prove curved-face stability or the two-face limit.

The separate [short-displacement stability argument](notes/curved-face-stability.md)
gives a conventional proof for the unchanged two-face class at a fixed small
coordinate-displacement cutoff. It derives a local C³ overlap extension,
retains the signed logarithmic cancellations and quantifies the normalized
curved-versus-wedge error. Spatial source weights have a generally nonzero
cutoff-derivative term; it cancels only in the complete partition. This argument
awaits independent mathematical review; its full weighted error estimate is
not asserted as a Lean theorem. Lean checks the exact short/long and
source-partition identities separately.

The [two-face assembly](notes/two-face-limit.md) now also has an **end-to-end
Lean proof of both original limit goals**. Its checked route subtracts the
planar cap with the same height rather than formalizing every weighted-wedge
estimate. It derives the actual local C³ overlap difference and its two-jet,
controls the nearly-null remainder, evaluates the signed logarithmic response,
and proves the spatial divergence identity and independent target
identification. One common fixed positive cutoff combines this short limit
with the checked long-null theorem; the separately proved Poisson bridge then
transfers the result to expectations. The original class and all goal
definitions are unchanged. No shrinking-cutoff uniformity, convergence rate,
unrestricted-conjecture result, or sample-wise convergence is claimed.

### Fixed-null mixed estimates and written expected-action assembly

The [fixed-null mixed pilot](notes/null-mixed-estimates.md) derives the signed
unit joint coefficient directly for a smooth spacelike lower face beneath a
null cone. Its conventional proof gives an explicit weighted near-cone bound,
uniform tip control, and the generator-derivative term needed for source
partitions. Discarding the complement of a shrinking joint collar is a proved
localization-route obstruction, not a counterexample to the full action.
The [nonplanar sine diagnostics](results/null-mixed.md) retain all future
partners. The [written assembly for #84](notes/null-mixed-assembly.md) now
proves the complete region/stratum geometry and global induced-area limit,
then uses an exact positive-density Poisson identity to obtain the expected-action
limit. Independent finite-order and positive-layer quadrature regressions
check the normalization without defining expectation from the reduced action.
This is a written proof, not a new Lean-checked mixed-region theorem or an
independently reviewed result. The later [dimensional cone-ending proof](notes/null-cone-dimensions.md)
extends its stated flat cone class to every integer dimension at least two;
it does not prove arbitrary null/mixed geometry.

The [complete conformally curved single-cone theorem](notes/conformal-cone-limit.md)
now proves the **whole #169 4D class**: every smooth globally strict-Lipschitz
floor of #84 and every fixed smooth positive spacetime-dependent conformal
factor on its causal enclosure. An actual future-endpoint cone-ball reduction
resolves the characteristic contacts without spacelike generator arguments.
Matched short/null remainders derive the physical point cancellation and the
independent curvature-plus-induced-SN-area target, with all generator, floor,
tip, cutoff and ordered-partition terms restored. The original-law expectation
is transferred separately afterward. This is a **written proof and finite
diagnostics, not a new Lean theorem or independent human acceptance**.
The [regular curved two-tip theorem](notes/conformal-two-tip-limit.md) (#178)
adds the complete union/lens response for its **whole regular 4D conformal
class**, with arbitrary non-axial floor and spacetime factor. Its floor/phase
inverse retains translated closing tangencies; the matched short proof derives
SN flux and retains nonzero weighted crease/generator endpoints. Actual
weighted interval/pair valuation and CC cap hypotheses give full assembly,
then separate original-law expectation. This is written, not Lean-checked or
independently accepted.
The subsequent [general past-front theorem NF-d](notes/regular-null-front-limit.md)
extends the mechanism to **every dimension at least two**, with a smooth
strictly spacelike floor and explicit regular null-contact geometry in
conformally Minkowski spacetime. It includes arbitrary finite tip multiplicity
and dependent cone intersections, with full pair/layer inclusion–exclusion,
complete deterministic assembly and separate original-law expectation.
The [all-null product obstruction NP](notes/null-product-focusing-obstruction.md)
derives a complete positive divergent action in 7D, including the actual null
endpoint masks, focal matching, independent short target and point cancellation.
Both are written research, not new Lean results or independent acceptance.
The [joint tangency theorem TC-d](notes/null-tangency-matching.md) subsequently
resolves arbitrary two-sheet floor/crease tangencies by closing-first signed
phase matching, including infinitely flat gaps and positive-area coincidences.
It completes deterministic assembly and expectation, deriving a twice-screen
union-coincidence term rather than assuming all extra strata vanish.
[The original #156 crosswalk](notes/null-mixed-required-coverage.md#8-original-contract-reconciliation-after-the-general-front-attempt)
still recommends **STILL BLOCKED**: general moving-null singular contacts and
the corrected intrinsic theorem remain unproved. Read the
[proof spine](notes/null-proof-spine.md) and
[source audit](notes/null-closure-audit.md).
A proved obstruction to local-finite-jet repairs is not a universal replacement.
The [Cartesian continuation NX](notes/null-cartesian-pushforward.md) derives
the compact smooth-sheet long pushforward, its geometric nonlocal term and
signed remainder, retaining finite higher-sheet masks. The subsequent
[complete gluing argument NG](notes/null-complete-gluing.md) audits those inputs
and writes the full point/pair decomposition before estimating. A two-normal
signed identity and joint diagonal/end resolution complete finite conformal
null polyhedra and the **whole** round bicone, not merely NX13's collar; the
latter has an independently derived nonlocal correction in odd dimensions.
[DL](notes/null-two-dimensional-gluing.md) computes the real two-dimensional
logarithms, adjoining cross partners and conformal vertex matching.
[FL](notes/null-floor-level-matching.md) handles all finite smooth-sheet
strict-floor contacts jointly, deriving their one/two/zero screen traces.
The [singular-end reconstruction SE/IF](notes/null-singular-end-audit.md)
author-checks those estimates, resolves arbitrary opposite-front exits in the
flat common-tip class by complete signed fibre integration, and derives a
fixed-width intrinsic focal threshold including its physical closing boundary.
It also computes the actual seven-halves transition coefficient, retaining both
matched tails above threshold. [The curved common-tip response CS](notes/curved-common-tip-response.md)
now resolves that **same** cusp at density `A(t)=1+t*t`: complete signed
partner integration gives curvature plus conformal outer-screen area, with
no additional shared-generator or end charge. Its nonexponential profile,
whole matching tail and uniform tube estimate extend to arbitrary smooth
positive spacetime density in the three-dimensional common-tip class.
[The intrinsic-union continuation IU](notes/intrinsic-union-continuation.md)
then resolves the actual spherical interval jointly through focal and closing
transitions, proving its complete growth plus finite term with uniform o(1)
error. A separate derivative-free logarithmic-ramp identity applies to general
physical unions without requiring a classical expansion. Its general geometric
critical trace remains unproved: the exact next specialist question is stated,
not assumed as parent admissibility. These are restricted written results,
not a corrected general theorem or independent acceptance.
[The geometric critical-trace attempt GT](notes/geometric-critical-trace.md)
states the exact normalized full-tail obligation and pursues three distinct
routes. Count-free clock control gives an actual coarea density and its first
coefficient; a density-jet replacement is proved negligible at complete critical
order. The remaining signed scale increment still lacks its geometric trace:
these gains do not prove the corrected general theorem. Nonlocal-correction
attempts retain the spherical and CS adversaries without assuming their structure.
[The integrated independent investigation IN](notes/independent-null-investigation.md)
provides an inverse-free complete pairing for arbitrary closed-Y null suspensions.
[The matching continuation SM](notes/null-suspension-matching.md) now recovers its
point, bulk and screen from four signed moments, with a uniform local-reference
error and exact auxiliary-cutoff recombination. It completes the local-width
suspension theorem, all widths in d=2,3, and, by a different signed integration,
derives a finite extra charge in a flat all-null 5D quotient without
conjugate points; higher
dimensions have complete-action growth. The arbitrary-Y complementary response
and the corrected general theorem remain unproved. GT's scale increment is one
possible route, not a necessary acceptance condition. Finite diagnostics do
not certify these geometric remainders or supply independent acceptance.
#156/#81/#24, #177 and #94/#86 remain open; #185 stays deferred. No scope change
is enacted.
No sample-wise or spacelike-to-null singular-limit conclusion is implied.

### Independent-face enlargement

The [independent-face enlargement audit](notes/independent-face-extension.md)
derives a larger fixed 4D class in writing, with independent strict causal
bounds and the same intrinsic area/angle target. A steep capsule lies outside
even transported old presentations. Its same-height planar reference is not
causally convex and has the wrong causal overlap formula. This is a rigorous
obstruction to that comparison route, **not** a counterexample to the full
conjecture or a new enlarged-class limit. The audit records surviving local
jets, replacement long-ray margins and the bounded
[direct-origin proof task #97](https://github.com/q5m-ai/causal-set-emergence/issues/97).
The [partial direct-origin analytic backend](notes/direct-origin-short.md) now
checks the absolute short basis responses and a conditional remainder transfer
in Lean. That backend alone is not a geometric limit theorem; #97 stays open.

The separate [Lean geometry package for #106](formal/INDEPENDENT_FACE_GEOMETRY.md)
now encodes that independent-envelope class and proves its region, strata,
positive-angle/induced-area geometry and finite-density Poisson equality.
It includes every old member and the genuinely steep symmetric capsule,
retains interior critical points, and exposes slope-independent height-atlas
and divergence prerequisites. The separate [actual class-E short proof](formal/INDEPENDENT_SHORT.md)
now derives the raw/envelope agreement, absolute overlap two-jet, measurable
derivative-controlled remainder and actual density decomposition. It proves
the short-action limit to the unchanged intrinsic target at every sufficiently
small fixed positive cutoff, including the steep and variable-angle members.
The [class-E long proof](formal/INDEPENDENT_LONG_NULL.md) supplies actual signed
long cancellation at every fixed positive cutoff. The subsequent
[#109 assembly and complete #97 acceptance map](formal/INDEPENDENT_LIMIT.md)
combine these producers at one common fixed positive cutoff and then apply
the separately proved Poisson bridge. They give unconditional deterministic
and expected-action limits for exactly class E, without changing the old
contract or using the inadmissible planar reference. The steep capsule,
variable-angle members and interior critical points are retained. This is
still a restricted flat 4D global two-graph theorem, not a general curved,
null/mixed, other-dimensional or sample-wise result; independent human review
remains outstanding under #94/#86. PR #104 owns final integration to `main`.

### Controlled curved proofs and their verification boundary

The [fixed-geometry conformal pilot](notes/curved-bulk-pilot.md) derives an
exact curved interval-volume formula and the candidate bulk response of a
second-jet model, with explicit curvature conventions and endpoint derivative
terms. It proves a conventional signed estimate for smooth interior long-null
sectors and an obstruction to dropping macroscopic nearly-null partners by
absolute bounds. The actual boundary-truncated unweighted remainder remains
open. This is analytic feasibility work for #73, with symbolic/numerical
regressions, **not** a Lean-verified curved limit or an expected-action theorem;
#93 owns the canonical curved finite-density API.

The subsequent [sharp-cutoff contact analysis](notes/curved-remainders.md)
for #74 gives the actual phase-straightened amplitudes and moving-contact
terms. On that fixed curved pilot, even the normalized **signed** long fibre
has no density-uniform integrable first-endpoint dominator. This obstructs
one order of averaging, not the complete action limit. Contacts must instead
be averaged, or explicitly subtracted and restored, before signed domination.
That partial, non-Lean delivery does not close #74 or supply its corrected
long and actual short contracts or supported bulk theorem.

The [contact-averaged long proof](notes/curved-contact-long.md) now derives
actual fixed-cutoff signed long cancellation for the original two-face class
with exactly that polynomial density, including smooth endpoint weights.
It integrates source time before seeking dominated jet control and retains
both moving-boundary contributions. This is a conventional written proof with
independent executable regressions, not a new Lean theorem or independent
human review. The raw-first-endpoint obstruction remains valid; that long-only
result does not supply the short or bulk theorem.

The [interior short/bulk proof](notes/curved-interior-short.md) now derives the
actual signed short remainder uniformly on compact interior source supports,
retaining the entire second jet, both endpoint measures and all moving-diagonal
terms. Combined with the already proved averaged long result, it gives the
supported half-curvature response with an independently calculated scalar and
the original normalization. Nonconstant endpoint fields retain their
wave-operator terms. These are written theorems with separate executable regressions,
**not new Lean proofs** or independent human review. That interior-only
package left the actual boundary-collar short term explicit.

The [boundary-collar handoff](notes/curved-boundary-collar.md) now restores the
whole bulk integral and proves the actual signed single-face estimate, using
only the original C³ face regularity. Its exact full/face/corner identity
retains both measures, all partners and the nonzero single-face joint flux;
no collar is dropped by small volume. It discharges #74's bulk/non-joint
producer obligations and handed #75 a precisely normalized actual corner
functional, leaving its weighted tangent comparison and joint limit open at
that stage. Finite partitions, cutoff compatibility and both spacetime boundary
fluxes are explicit. These are written results with separate regressions,
not new Lean proofs or independent human mathematical review.

The subsequent [curved joint-corner proof](notes/curved-joint-corner.md) supplies
that weighted comparison for the same fixed polynomial density and original
C³ two-face class. It retains the actual curved phase, both measures, moving
corner boundaries and the compensating single-face joint flux. Independent
normal/Gram geometry identifies the limit with induced curved joint area times
the positive-angle weight, including unequal-axis nonzero-curvature and
varying-angle examples. Signed errors are summable at one common fixed cutoff;
no same-chart partner restriction or shrinking-cutoff argument is used.
This is a **written theorem**, with separate symbolic/numerical checks, not a
new Lean result or independent human review. That producer leaves the complete
assembly and expectation transfer to the following package, rather than
asserting them as part of its joint-only theorem.

The [controlled curved assembly](notes/curved-assembly.md) now combines these
actual bulk/collar, joint and contact-averaged long producers at one common
fixed cutoff. It proves in writing that the complete canonical action tends
to the whole half-curvature integral plus the variable-angle induced joint
integral, for exactly the original C³ two-face class and `Omega(t)^4=1+t^2`.
It then discharges that fourth-root factor's geometric hypotheses and applies
#93's **curved** positive-density expectation identity; the flat bridge is not
reused as a curved theorem. An unequal-axis member has nonconstant positive
scalar curvature, strictly positive bulk and angle weights 2 and 6 on one
joint. All cross-chart partners, single-face fluxes and the collar complement
are retained. This is a **conventional written deterministic/expected theorem**
with separate executable regressions, not a new Lean asymptotic theorem or
independent human review. The coverage comparison leaves #81/#24/#86 open for
general metrics, dimensions and strata; no rate, shrinking-cutoff uniformity
or individual-sprinkling convergence is implied.

The [#133 general-metric/atlas feasibility gate](notes/general-metric-atlas-gate.md)
compares that completed pilot with explicit nonpolynomial, compact-quotient and
non-conformally-flat focusing tests. It supplies written bounded interfaces,
a thin flat-torus slab calculation and a precise focusing-route obstruction,
with separate regressions and follow-up contracts. It supplies **no new Lean
verification or general-metric/atlas coverage theorem**; #81/#24 remain open.

The subsequent [#138 thin flat-torus formal port](formal/THIN_TORUS_LIMIT.md)
proves the actual quotient-slab deterministic zero limit and, separately, its
original-Poisson-law expected limit for every fixed positive height below half
the period. Checked interval lifts and geometric volume, full-partner pair
integration, the derived logarithmic phase and exact point cancellation retain
seams and both endpoint measures. The acceptance map records the integrated
validation boundary and strictly nonzero finite-density regressions. This
bounded flat-quotient result does not extend to curved atlases or sample-wise
convergence and does not complete #81/#24 or independent human review.

The [#139 sphere-circle focusing producer](notes/sphere-circle-focusing.md)
now derives the actual endpoint-averaged antipodal-neighborhood density in
writing. An exact circle/time reduction retains transverse separations and
closing time contacts; a summable primitive jet proves signed cut-neighborhood
cancellation without a smooth phase inverse through the focusing transition.
The exact short/off-cut complement remains explicit and requires a matched
producer. This is not a complete-action limit or counterexample, a new Lean
result, or independent human review; #81/#24 remain open.

The [#152 sphere-circle complement proof](notes/sphere-circle-complements.md)
derives the actual 4D short response and signed off-cut long cancellation for
that same fixed slab. It retains long-circle nearly-null partners, both endpoint
measures, the moving time contacts and every F20 boundary. An actual analytic
phase inverse and summable density remainders produce the physical-point
cancellation and independently normalized curvature coefficient, with one fixed
compatible cutoff. Together with #139's accepted cut primitive and the excess
tail, these are written sector outputs for #153's complete assembly and separate
expectation transfer—not a new Lean theorem, independent human acceptance, or
general coverage under #81/#24.

The subsequent [#153 complete sphere-circle assembly](notes/sphere-circle-assembly.md)
proves the written full deterministic limit for that fixed 4D geometry and
then transfers it through #137's checked selected-order, original-Poisson-law
bridge. All four F20 pair sectors, both endpoint measures and every boundary
are restored, with the physical point exactly once. The result equals the
independently contracted `320*pi` curvature bulk; the joint is empty. This
completes this focusing example, not general metric/dimension coverage, a
compiled asymptotic proof or independent human review. #81/#24/#86/#94 and
sample-wise convergence remain separate.

The [partial #151 globalization work](notes/full-partner-globalization.md)
proves the written manifold measurability/locality and exact full-partner atlas
identities, plus weighted long cancellation for thin flat-torus slabs in every
dimension. It retains the accepted 4D focusing estimate and its full complement.
The [7D continuation](notes/seven-dimensional-focusing-obstruction.md) derives a
**written complete-action obstruction** to the all-dimensional finite G-SS
target: a matched caustic term survives actual short point cancellation.
Its sign has an exact rational certificate. General caustic classification,
independent human review and corrected umbrella assembly remain outstanding;
PR #159 stays draft, with no new Lean result or issue closure.

The [#136 nonpolynomial short/assembly proof](notes/nonpolynomial-short-limit.md)
consumes that gate's actual long estimate for `Omega(t)=1/(1-t)`. It derives
the signed full/face/corner estimates for smooth original two-face regions
inside `abs(t)<1/2`, retaining both endpoint measures, moving diagonal strips,
both spacetime-face fluxes and the compensating joint flux. It then proves
the complete deterministic bulk-plus-joint limit and applies #93's genuine
expectation equality. This is **written analysis with executable regressions**,
not a compiled curved limit or independent human review. The general-metric,
other-dimension/stratum and sample-wise gaps under #81/#24 remain open.

The [#150 general-metric short derivation](notes/general-metric-short.md) and
[actual signed-remainder proof](notes/general-metric-short-remainders.md) now
supply the written short producers on the general smooth G-SS core, in every
physical dimension. Actual null-tube rescaling derives the interval phase and
full-cone remainder; exact moving-source flattenings prove the entire face and
joint comparisons, including every diagonal contact, both face fluxes and joint
compensation. The fixed temporal cutoff and its signed local conversion remain
compatible with #149/#151. This is **written analysis with regressions**, not a
compiled proof or independent human review. The general nonlocal long producer
and full-action/expectation assembly remain with #151/#81; #24 stays open.

The [general curved-4D continuation](notes/curved4-physical-response.md) derives
the actual physical clock pushforward without a geodesic branch list and
bounds its small-volume long sublevels. It audits consumption of S30 and
explores signed dilation estimates weaker than a cubic jet. The
[focal-geometry follow-up](notes/curved4-focal-research.md) derives the first
whole-primitive coefficient from general geometry and realizes a quartic
focus in an explicit curved G-SS metric, where absolute cubic domination
fails. A separately [regenerated certificate](notes/curved4-focal-certificate.md)
proves the fully matched model coefficient positive. The
[physical classification](notes/curved4-focal-globalization.md) and
[complete-action argument](notes/curved4-complete-action-obstruction.md) then
supply uniform two-subtracted matching, the closing/overlap layers and the
whole regular complement. The resulting **written curved-4D obstruction**
has negative rho-to-power-3/14 action growth against the independent zero
target, with the same cutoff and physical point restored once. Expectation
is transferred separately; no sample-wise result follows. This is not a
Lean proof or independent mathematical acceptance, which remains #94/#86.
The original G-SS scope and broader #151/#81/#24 ownership are unchanged.

The [corrected curved-4D theorem](notes/curved4-corrected-convergence.md)
proves a **written positive limit for every smooth positive time/circle
conformal factor on the focusing sphere-circle slab**. It derives the actual
weighted interval and both-measure pushforward, straightens closing fibres,
and proves a summable critical remainder before restoring the entire action
and separately transferring expectation. This is an infinite-dimensional,
non-conformally-flat class that retains antipodal focusing, not an assumption
that the long response vanishes. Its geometric summability threshold explains
why the quartic obstruction escapes. General metrics, other strata/dimensions
and sample-wise limits remain #151/#81/#24; independent acceptance and formal
verification remain #94/#86. No predecessor proof or audit receipt is changed.

The [#151 acceptance crosswalk and corrected-coverage ledger](notes/issue-151-resolution.md)
assesses the original **negative-resolution alternative**, rather than claiming
that the restricted positive family proves a universal theorem. It links every
acceptance clause to its actual source, records the #165 proof audit, and keeps
the unresolved corrected general-curved theorem explicitly with **#81** (not
only a closed child), required null/mixed work with #154–#156, the selected
formal torus task with #138, and final scrutiny/formalization with #94/#86.
Earlier delivery-time issue-status statements above are historical; #81/#24
remain open and their stronger completion criteria are unchanged.

The [sphere-dependent extension under #81](notes/sphere-dependent-conformal-limit.md)
removes #165's angular restriction in writing: every smooth positive factor on
the same focusing slab has the complete canonical action limit and a separate
actual-measure Poisson transfer. Its signed sphere-point map retains both
orientations; the rescaled angular motion yields the integrable critical
remainder instead of assuming weighted cancellation from causal invariance.
The [geometric sufficient-condition continuation](notes/geometric-long-cancellation.md)
derives cancellation from resolved **physical interval point maps**, endpoint
abundance and moving-contact control. It also proves the faithful conformal-
diamond-cover case with general spacelike faces, ordered partitions and a
nonempty variable-angle joint example with independently calculated bulk and
joint. The [non-conformal stability theorem PW-4](notes/nonconformal-plane-wave-limit.md)
then derives the complete limit for smooth symmetric positive-definite
transverse-matrix plane-wave profiles with fixed global positive lower and finite
upper bounds, and ambient-contained G-SS regions. Exact quadratic path minimization supplies
the whole physical interval; the divided-volume formula is uniform through
both tips and the parallel-null collar. Actual spacelike face/cutoff contacts,
nonempty variable-angle joints, both measures and the separate original-law
expectation are retained. Stability is within that metric class, **not** under
arbitrary perturbations; it does not claim uniform RPL point-map bounds where
only the exact phase argument is proved.

These are written results, not universal coverage, new Lean proofs or
independent acceptance. The consolidated [scope, proof dependencies and
adversarial estimate audit](notes/nonconformal-plane-wave-limit.md) separate
proved results from the remaining intrinsic whole-interval containment and
simultaneous singular-contact blocker. Curved 3D, broader corrected
metric/dimension coverage and the separately owned null/mixed branch
remain unresolved; the subsequent complete curved 2D result is recorded below. #164's proof and certificate are unchanged; final human
scrutiny remains #94/#86, and #81/#24 stay open.

The [curved-3D response](notes/curved-three-d-response.md) derives the actual
physical-union primitive and its first subtraction for the original smooth
core. Its **restricted** FCDC-3 theorem proves the complete deterministic and
separate original-law expectation limit under a faithful whole-interval
conformal-cover condition, with independent curvature and variable-angle curve
joint. The [focal continuation](notes/curved-three-d-focusing.md) additionally
proves the complete zero limit for one genuinely curved compact 3D slab with
quartic conjugacy, two-route cuts and physical endpoint overlaps. It uses the
3D kernel, not the 4D obstruction's coefficient. The original arbitrary-metric
3D critical remainder remains **UNKNOWN under #177/#81**. These are written
arguments and diagnostics, not new Lean proofs or independent acceptance;
#94/#86 retain scrutiny. The independent #175 curved-2D worker is not a premise.
The [signed-matching continuation](notes/curved-three-d-matching.md) derives a
weaker averaged criterion and smooth one-screen angular control without a
finite analytic contact classification. Uniform physical-union matching when
the quartic coefficient vanishes remains unproved; this adds no complete-class
coverage or counterexample and retains the original #177/#81 quantifiers.
The subsequent [cluster audit](notes/curved-three-d-clusters.md) establishes a
uniform 9/5 physical-volume bound for the phase-bad sector, including flat and
losing near-minimizers, and a joint weighted contact estimate. The remaining
blocker is aggregate signed matching of the phase-good active Morse clusters,
with both tips, physical overlaps, all masks and both subtractions restored.
Its compatible accumulating-well diagnostic is not a spacetime counterexample.
The [whole-union continuation](notes/curved-three-d-union.md) now derives
count-free tip-overlap control, a resolved physical Morse model and a global
cut threshold from the actual null Hamiltonian. It produces an aggregate
opening coefficient and a summable cut-graph budget, but not the critical
extra half-order with changing competitors and simultaneous moving masks.
The original complete deterministic/expected conclusion remains **UNKNOWN**;
coalescing-well and singular-curvature controls diagnose failed inferences,
not admitted complete-action counterexamples.
The [critical continuation](notes/curved-three-d-critical.md) states the exact
weighted ramp/signed obligation and both subtraction tails, derives a
two-sided ordinary-cut budget, and constructs fixed admitted metrics realizing
the circular arrival envelope and singular cut curvature at a point source.
Their complete all-source actions are not computed. The remaining gap is a
uniform weighted aggregate opening/contact numerator estimate, not the
existence of a cut budget; every original acceptance item remains mapped
without narrowing #177 or claiming its deterministic/expected conclusion.
The [final phase freeze and specialist handoff](notes/curved-three-d-phase-freeze.md)
records two unsuccessful final approaches and one exact unproved lemma for
signed increments of the complete unit-weight physical ramp. This avoids
requiring arbitrary-weight expansions or a classical second coefficient;
it does not prove the missing limit. The research phase is complete, **not
#177**. Specialist review is recommended before further autonomous work.

The [intrinsic Hadamard optical theorem HO-4](notes/hadamard-optical-limit.md)
adds written 4D coverage for every ambient-contained G-SS region in an
ultrastatic spacetime whose spatial geometry is complete, simply connected
and nonpositively curved. Whole-interval comparison and a resolved two-cone
rescaling control both tips, the near-null regime and moving face/cutoff
contacts; the critical signed remainder is derived, not assumed from unique
geodesics. The complete canonical action and separate original-law expectation
reach the independent curvature-plus-joint target. Genuinely variable-curvature,
non-conformally-flat members with nonempty variable-angle joints are included.
The [source-backed WORKS / FAILS / UNKNOWN ledger](notes/intrinsic-coverage-ledger.md)
preserves all integrated successes and complete counterexamples, and keeps
broader curved 3D, metric/dimension and null/mixed obligations with #81 and
#156. This is not a new Lean proof, universal replacement conjecture or
human acceptance; #94/#86 and #81/#24 remain open.

The [complete curved 2D theorem C2](notes/curved-two-d-limit.md), addressing
#175's original quantifiers, adds written coverage for **every smooth 2D
G-SS member**. Global null coordinates are derived on the causal cover;
physical route unions retain both endpoint overlaps, both measures and all
moving face/cutoff contacts. A geometrically derived quadratic primitive
remainder gives the genuine 2D signed long response. At one fixed cutoff,
S30 restores the whole curvature-plus-counting-joint action with the point
once, then the original-law expectation transfers separately. Compact-Cauchy
slabs and all joint endpoints are included; no conformal-chart, small-width
or unique-interval assumption is added. The argument and finite diagnostics
are not new Lean verification or independent expert acceptance. #175 remains
open pending separate acceptance; #81/#24 and #94/#86 remain open.

## Program 2 — dynamics and automaton-like growth

The exploratory question is whether causal-set dynamics can be represented as
an asynchronous, label-independent growth or graph-rewriting system:

```text
discrete event + causal dependencies + covariant update law
                         ↓
       histories with emergent geometry and physics
```

The Game of Life is a useful intuition for emergence from simple rules, but not
a direct model. Ordinary cellular automata assume a spatial lattice, global
clock, simultaneous updates, and fixed local neighborhood. Those assumptions
would build in structures that causal set theory is meant to explain.

A viable causal analogue would need to preserve partial order and local
finiteness, avoid physical dependence on birth labels, support Lorentzian
rather than lattice locality, and ultimately admit quantum amplitudes or a
quantum measure over histories. One possible bridge to Program 1 is to ask
whether the BDG action can weight legal histories through an amplitude such as
`exp(iS)`.

This direction currently consists of questions and comparisons—not a proposed
fundamental rule. See:

- [Emergence and dynamics: current learnings and roadmap](notes/emergence-roadmap.md)
- [Viewing notes from the Fay Dowker / Curt Jaimungal conversation](notes/fay-dowker-interview-notes.md)
- [Discussion #12: order-invariant automata](https://github.com/q5m-ai/causal-set-emergence/discussions/12)

## Interactive explainer

[`site/index.html`](site/index.html) is a build-free visual introduction
to:

- discrete events and causal partial order;
- manifold, topology, and metric as emergent continuum concepts;
- causal diamonds, links, light cones, and Lorentzian nonlocality;
- a toy observer represented as a causal process across alternative histories;
- canonical, path-integral, and stochastic quantization;
- the continuum-limit calculation studied in this repository.

Open it directly, or serve only the site directory:

```sh
python3 -m http.server 8000 --directory site
```

Then visit <http://localhost:8000/>.

## Evidence and claim discipline

| Label | Meaning here |
|---|---|
| **Exploratory** | A question, analogy, or proposed direction; not a result |
| **Drafted** | A written analytic argument awaiting independent review |
| **Numerically checked** | Reproducible finite-density or symbolic evidence |
| **Machine checked** | The stated Lean declaration compiles and passes the axiom audit |
| **Established** | Reserved for independently reviewed or published work |

Distinct proof programs should remain independently auditable. A deeper result
may supersede an earlier argument without erasing its provenance. Numerical
agreement and visualization never substitute for proof, and machine checking
never substitutes for validating that the formal statement matches the intended
physics.

## Repository map

- `notes/first-attempt.md` — analytic boundary-limit proof draft and scope.
- `notes/conjecture-roadmap.md` — staged route from issue #1 to the general theorem.
- [Dimension-indexed kernel prerequisites](notes/dimension-kernels.md) — action
  normalizations, checked signed integrals, parity-dependent tails/moments and
  a checked regulated weighted local coefficient; not a higher-dimensional
  two-face limit.
- [Dimension-indexed two-face geometry](notes/dimension-two-face-geometry.md) —
  written finite geometry and intrinsic targets, the `SmoothPilot3` contract,
  all-component examples and dimension/regularity obligations; no new limit.
- `notes/general-contract.md` — general coverage matrix, independent candidate
  theorem, null/mixed taxonomy, obstruction tests and downstream contracts.
- `notes/general-contract-literature.md` — checked source passages, normalization
  differences, dimensional/curvature qualifications and unresolved attribution.
- `notes/null-mixed-estimates.md`, `null_mixed.py` — fixed-null weighted estimates,
  tip/complement accounting and nonplanar diagnostics for the selected mixed class.
- `notes/null-mixed-assembly.md`, `mixed_poisson.py` — written global deterministic
  and expected-action proof for that class; independent finite-order/layer checks.
- `notes/curved-assembly.md`, `curved_assembly.py` — written controlled conformal
  4D bulk-and-joint deterministic/expected theorem and separate finite
  certificates; not a new Lean continuum-limit theorem or general curved result.
- `notes/null-complete-gluing.md`, `notes/null-two-dimensional-gluing.md`,
  `notes/null-floor-level-matching.md` — complete signed gluing at their stated
  scopes; `null_complete_gluing.py` and its tests are finite diagnostics only.
- `notes/null-singular-end-audit.md` — author reconstruction, complete flat
  common-tip singular-end theorem and intrinsic focal closing threshold;
  `null_singular_ends.py` and its tests are finite diagnostics, not certificates.
- `notes/curved-common-tip-response.md` — complete SE6 curved cusp and 3D
  conformal common-tip theorem, signed profile mass/tail and critical remainder;
  `curved_cusp_response.py` and its tests are finite diagnostics only.
- `notes/intrinsic-union-continuation.md` — two intrinsic-union methods, complete
  spherical growth/finite remainder and the exact general filtered-trace gap;
  `intrinsic_union_response.py` and its tests are finite diagnostics only.
- `notes/geometric-critical-trace.md` — exact trace obligation, whole-clock coarea,
  critical density-jet stability and three routes with the general gap retained;
  `geometric_trace_diagnostics.py` and its tests are finite diagnostics only.
- `notes/independent-null-investigation.md` — complete cap transport and
  inverse-free suspension pairing, including the lost homogeneous-data warning;
  `null_suspension.py` and its tests are finite diagnostics only.
- `notes/null-suspension-matching.md` — arbitrary-Y origin matching, complete
  local-width theorem and a flat 5D nonlocal charge with physical-union assembly;
  `null_suspension_matching.py` and its tests are finite diagnostics only.
- `notes/references.md` — sources, attribution, and novelty boundaries.
- `notes/emergence-roadmap.md` — synthesis of conceptual learnings and next questions.
- `notes/fay-dowker-interview-notes.md` — provisional viewing notes and study prompts.
- `formal/` — Lean proofs, admissible graph-cap API, explicit targets, audit,
  and reproduction guide.
- `calculations.py`, `check_symbolic.py` — deterministic numerical and symbolic checks.
- `RESULTS.md` — reproducible finite-density tables.
- [Two-face diagnostics](notes/two-face-diagnostics.md) — controlled deterministic
  experiments, cancellation/refinement checks, and limitations; not a new theorem.
- `site/` — standalone interactive explainer.

## Writing mathematics on GitHub

Follow [the math authoring guide](notes/github-math.md) for Markdown files,
issues, PRs, and comments. Use fenced `math` displays and dollar/backtick inline
math; GitHub does not render all LaTeX delimiters or macros. Run
`python3 check_markdown.py` before publishing and check the browser preview,
not just the Markdown API. Repository agent instructions are in
[`AGENTS.md`](AGENTS.md).

## Reproduce the computational checks

Requires Python 3.11+ and the pinned packages in `requirements.txt`:

```sh
uv venv .venv
uv pip install --python .venv/bin/python -r requirements.txt
.venv/bin/python check_symbolic.py
.venv/bin/python check_markdown.py
.venv/bin/python -m unittest -v
.venv/bin/python reproduce.py
```

Without `uv`, create a standard virtual environment and install from
`requirements.txt`. Lean reproduction instructions and the exact checked
boundary live in [`formal/README.md`](formal/README.md).

Downloaded source articles, local environments, and build products are ignored.
No third-party article text is committed.
