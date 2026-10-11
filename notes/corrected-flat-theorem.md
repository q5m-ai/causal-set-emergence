# The corrected FLAT theorem: sharp universal dimension range

**Status.** Conventional written mathematics, with executable diagnostics;
not a new Lean theorem or independent human review. This note states the
quantifiers proved by PR #163, records the proof audit, and assesses #149
against its original acceptance text. It does not merge the PR, close an
issue, alter G-SS, or declare the parent conjecture proved.

## 1. Unchanged class, action and probability law

For each integer dimension d at least two, let the flat class consist of
**every** member of [G-SS](general-contract.md#3-a-precise-non-vacuous-general-core-candidate)
whose globally hyperbolic ambient Q has flat Lorentzian metric. Thus M is
precompact and ambient-causally-convex, with the prescribed smooth spacelike
past/future faces and transverse joint J. All the original component,
achronality and stratum conditions remain. Empty joint is allowed. No
orientability, topology, lattice, ultrastatic, global graph, development
injectivity, width or combined-slope condition is added.

The selected order is the ambient causal order restricted to M, and the
interval is the **exclusive physical interval**, not a developed copy counted
with multiplicity. In the canonical normalization of
[the dimension interface](dimension-producer-interface.md),

```math
\begin{aligned}
V_g(x,y)&=\mu_g\{z\in M:x\preceq z\preceq y,\ z\notin\{x,y\}\},\\
\mathcal A_{\rho,d}
 &=a_d\rho^{2/d}\mu_g(M)
 -\beta_d\rho^{1+2/d}\int_{x\prec y}
          K_d(\rho V_g(x,y))\,d\mu_g(x)\,d\mu_g(y),\\
\mathcal T_d(M,g)&=\int_J\coth\theta\,dA_g.
\end{aligned}\tag{CFT1}
```

The point coefficient is the positive `a_d` of the shared interface (minus
the d'Alembertian coefficient `alpha_d`); an earlier CFT1 printed `alpha_d`
instead. This notation correction does not change the canonical action used
in the proofs. The flat bulk curvature term is zero. The target is independently defined
by induced metric and future normals, including counting measure at **every**
2D joint endpoint. Both endpoint measures, all causal partners and every
ordered pair of partition labels are retained. The physical point term occurs
once, in strict short; equality belongs to long. A sufficiently small positive
temporal cutoff is fixed before taking the density limit. No cutoff shrinks
with density.

The probability law remains the finite Poisson law of intensity rho times
restricted geometric volume. The independent finite-density bridge, discharged
in [FL18](finite-lift-flat-reduction.md#9-actual-expectation-hypotheses-and-coverage-ledger),
is valid for **every dimension and every geometry in this flat class**, without
assuming any asymptotic conclusion:

```math
\begin{aligned}
\mathbb E_{\mathrm{Poisson}(\rho\mu_g|_M)}
       A^{\mathrm{disc}}_{\rho,d}
 &=\mathcal A_{\rho,d}(M,g),\qquad \rho>0.
\end{aligned}\tag{CFT2}
```

This applies the existing compiled generic
`dimensionFiniteMeasureAction_expectation` after a **written manifold
hypothesis discharge**. It is not a newly compiled quotient/manifold instance.

## 2. Quantified theorem and proof

**Theorem FLAT.**

1. For **each** d in {2,3,4} and **every** flat G-SS member, both its complete
   deterministic action and its original-law expected discrete action tend
   to the independent joint target in CFT1. Smoothness as required by G-SS
   supplies the sufficient finite C8 budget described below. The geometry
   and cutoff are fixed; no family-uniform or complete-action rate is claimed.
2. For **each** integer d at least five there exists a **fixed analytic** flat
   G-SS member with empty joint for which the same deterministic and expected
   actions do not tend to that target. The family is precisely K1: ambient
   `R × X_d`, with `X_d` the Klein-bottle quotient in
   [the obstruction proof](flat-klein-bottle-obstruction.md#1-geometry-and-complete-lift-lists)
   times the specified transverse flat torus, and slab width `21/20`.
   Its independent target is zero. K7–K10 prove, with a constant D_d
   strictly positive for each fixed d,

   ```math
   \begin{aligned}
   \lim_{\rho\to\infty}\mathcal A_{\rho,5}&=D_5>0,\\
   \lim_{\rho\to\infty}
      \rho^{-(1-5/d)}\mathcal A_{\rho,d}&=D_d>0,
      \qquad d\ge6.
   \end{aligned}\tag{CFT3}
   ```

   CFT2 separately gives the identical expected-action conclusions. The
   auxiliary variables in the positive fractional moment for D_d are only
   an integration device; they do not change the physical Poisson law.
3. In every dimension the exact finite-lift/physical-union reduction, the
   overlap comparison, and CFT2 continue to cover **all** flat G-SS members.
   They do not assert that every higher-dimensional region fails. The
   all-dimensional Minkowski, thin-torus and first-cut positive theorems
   remain valid under their existing hypotheses.

Consequently, if U_d denotes “every flat G-SS member in dimension d has the
canonical deterministic **and** expected joint limit”, the precise sharp
universal dimension statement is

```math
\begin{aligned}
U_d\quad\Longleftrightarrow\quad d\in\{2,3,4\},
\qquad d\in\mathbb Z,\ d\ge2.
\end{aligned}\tag{CFT4}
```

The negative quantifier is “for every higher dimension, **there exists** a
counterexample”, not “every higher-dimensional region is a counterexample”.
CFT4 is maximal in its universal dimension range with the original class,
action and target unchanged. It is not a necessary-and-sufficient geometric
classification of individual higher-dimensional members.

**Proof of the positive clause.** FL1–FL4 derive finitely many genuine
connecting lifts and faithful individual diamonds; the physical interval is
their union, with intermediate-chart unions retaining large-diamond
self-overlap. In the small-volume long domain the null routes separate.
FL5–FL9 bound the error between the physical-volume primitive and the
sum-volume primitive by O(w^(q+2)), with q=d/2. This is a shell/coarea bound
for the *difference of primitives*, not permission to add nonlinear kernels.

The derived phase/face ranks and moving-mask argument in FL10–FL12 give
an actual integer cubic polynomial plus o(w^3) for the sum-volume primitive,
including arbitrary simultaneous contacts. For d=4 its remainder is exactly
of the required little-o critical order; for d=2,3 it is above that order.
The signed moments in G7 remove the relevant lower integer powers. In d=2
the cubic term itself need not have zero moment, but its normalized response
tends to zero. G6's Stieltjes bound handles the remainder without differentiating
an uncontrolled error. The physical-union correction also tends to zero
in every dimension. Therefore the complete long action tends to zero in
2D–4D, with no lost sign sector or reference strip.

At the **same fixed cutoff**, the flat specialization of S30 supplies the
short limit, including physical point cancellation, moving faces, the true
joint, components and all partition terms. Only its flat specialization is
consumed; no unfinished long theorem from #151 is an input. Its local flat
calculation is also the short producer underlying #157, with the exact
G10–G11 atlas and cutoff accounting. Adding short and long proves clause 1
for the deterministic action; applying CFT2 afterwards proves expectation.

This argument is not limited to constant test fields. FL12 allows signed
smooth source/target weights. Combining its vanishing long term with S30
retains the flat bulk term `integral chi*Box(phi)`, the future face flux
`integral (phi*n_+(chi)-chi*n_+(phi))`, and the joint term
`integral chi*phi*coth(theta)`. Source, Hessian and partition derivatives
are not declared zero. The unit-field physical statement in CFT1 follows
only after that accounting; no separate weighted stochastic theorem is
asserted here.

**Proof of the negative clause.** K1 verifies the original geometric
hypotheses in each dimension, including global hyperbolicity and ambient
containment. K2–K4 derive the complete lift list, the fold and its density,
both inverse branches, both physical contact centers, and both endpoint
times. K6–K8 match all fifteen nonempty sign sectors, retain the regular
complement and closing fibres, and prove the positive fractional coefficient
by an auxiliary moment identity, not a sign fit. K9 is the signed response
of that matched primitive. FL9 restores the physical interval union, and
S30 restores the whole short action at the same cutoff, giving K10/CFT3.
The separate CFT2 transfer completes clause 2. This is a counterexample to
the original universal assertion, not to any of the preserved positive
subclass theorems. Clauses 1 and 2 prove CFT4.

The reflection-quotient logarithm H1–H15 remains a distinct, independently
matched mechanism: a nonzero complete limit in 6D and positive divergence
above it. It is not needed to fill a remaining dimension-five gap. Its audit
is retained rather than deleting the earlier theorem when K10 becomes enough
for the negative quantifier.

## 3. Proof audit and finite derivative ledger

This is an author's source audit and explicit proof strengthening, **not an
independent referee report**. The hard dependencies are as follows.

| Step | Reason the implication is valid | Shortcut not used |
| --- | --- | --- |
| Finite connecting lifts | Compact causal enclosure plus temporal control bounds complete auxiliary Riemannian length; lifted metric balls are compact and the deck action is proper | A finite spatial lattice list or proper holonomy image |
| Faithful developed diamonds | The cover is globally hyperbolic; causal-geodesic existence and geodesic initial-value uniqueness give development injectivity on each causal future; compactness fills the developed diamond by an open/closed argument | Global development injectivity, exponential surjectivity or Lorentz completeness |
| Actual volume | FL3–FL4 use physical indicator unions and all intermediate charts; thin long diamonds become individually injective only near the null limit | Applying the nonlinear kernel to an inclusion–exclusion sum of kernel values |
| Overlap error | Endpoint cone boxes give the product-volume bound; monotone target flow and pair coordinates give shell thickness times width in FL9 | Truncating inclusion–exclusion at pair intersections or discarding face masks |
| Available ranks | Three distinct future null representatives are independent; endpoint blocks prove the needed phase/face triples; the short cutoff/joint limit has an explicit rank argument | Fourfold independence, independent coordinates for every branch, or arbitrary genericity |
| One-positive sectors | Derived pairwise ranks on the phase fibre give continuous coarea fluxes; the moving-mask lemma gives their right derivative | Assuming a C2 fibre density through all contacts |
| Two-positive sectors | Individually regular remaining masks give a bounded one-sided directional derivative after rescaling | Assuming that derivative is linear in the phase direction |
| Three-or-more-positive sectors | Three actual phase coordinates scale; positive-measure zero sets have vanishing tangential gradient almost everywhere; remaining boundary normals give almost-everywhere indicator limits | Analytic face masks, finite contact order or a rate for the little-o remainder |
| Quartic logarithm | Even-amplitude divided remainders control the product pushforward; inactive-coordinate antiderivatives include every strip; the fourth-moment identity fixes the full sign | Treating the all-positive corner as the complete coefficient |
| Fractional fold | The held linear coordinate turns the product into a negative square; its actual discriminant and both branches give an inverse-square-root density; K6 matches every sector | Replacing the fold by an unrestricted product or fitting its singular exponent |
| Moving fold and complement | Nonzero discriminant derivatives permit repeated inactive-coordinate integration; the L1 translation and half-Hölder bounds give K8's remainder; closing fibres stay in F_d | Dropping a moving endpoint or differentiating the primitive remainder without a bound |
| Signed normalization | G7, H13 and K9 retain the actual Mellin roots, their logarithmic derivative, and the negative pair prefactor | Bounding the entire kernel absolutely before polynomial subtraction |
| Full action and expectation | Exact fixed-cutoff assembly precedes limits; the original-law bridge is separately discharged | Counting the point twice, changing the observable, or inferring sample-wise convergence |

For clarity, the standard geometric inputs to the faithful-diamond argument
are the existence of a smooth Cauchy temporal function, Hopf–Rinow for the
complete auxiliary Riemannian metric and its lift, causal limit-curve
compactness, globally hyperbolic causal-geodesic existence (Avez–Seifert),
and uniqueness of the geodesic initial-value problem. The proof checks their
hypotheses on the actual cover before using them. No Python diagnostic
certifies these standard theorems or that hypothesis check.

The regularity demand is finite and geometry-dependent, not a new C3 theorem:

- **General positive 2D–4D statement:** C8 is a sufficient nonoptimal local
  budget for metric/face/temporal/endpoint-field data on the compact tubes.
  The FL transport step needs only finitely many coarea derivatives through
  its one-sided second derivative. The short mixed expansion has order
  `floor(d/2)+4`, at most six here, with two additional derivatives covering
  its coordinate, face and joint operations. Smooth G-SS supplies these
  bounds; compact spacelikeness/transversality gives positive inverse margins.
- **Explicit negative families:** the data are analytic and the localized
  amplitudes smooth on fixed compact supports. A deliberately conservative
  sufficient derivative ceiling for the displayed calculations is
  `floor(d/2)+32`. In H6 four double even divided-remainder steps cost at most
  sixteen transverse derivatives; controlling five pushforward derivatives
  and the six further inactive-amplitude derivatives costs at most eleven
  more. K6 needs at most four antiderivative transfers to make a remaining
  singular integral C3; derivatives of its nonvanishing discriminant
  denominators and amplitude fit within the same ceiling. The short producer's
  `floor(d/2)+4` mixed derivatives and two coordinate derivatives do also.
  Thus every fixed dimension uses a specified finite number of bounded
  derivatives, not an assumption of an unproved all-order expansion.
- **Previously merged positive subclasses:** #157's sharper
  `max(3, ceil(d/2)+1)` budget and #132's bounded C4 5D/6D results remain
  unchanged. The conservative budgets above neither weaken nor re-prove them.

These are sufficient derivative counts used by the proofs, not a relaxation
of the original smooth class or a claim of optimality. No bound is uniform
over degenerating angles, changing topologies, shrinking injectivity radii,
or a density-dependent geometry.

The added diagnostics in `test_flat_proof_stabilization.py` address specific
proof risks, not a new collection of limit examples: a boost/Milne coordinate
calculation checks faithful interval volume with its nonconstant measure;
its quotient checks physical union rather than multiplicity; coincident
regular masks check a nonlinear directional derivative; and an infinite-order
smooth mask gives an explicit o(w^3) remainder with **no positive power gain**.
This last control prevents replacing the proved little-o by an unjustified
complete-action rate. Existing tests retain the full sign-sector coefficients,
physical-union negative controls and signed fractional/log responses.

## 4. Assessment against #149's original acceptance

The [exact source snapshot](evidence/issue-149-acceptance.json) preserves #149's
title, body and open state before this assessment. In particular its delivery
alternative says, verbatim:

> Deliver a conventional quantified theorem with an exact dimension/geometry coverage map, or a complete-action obstruction and corrected statement. If only a restricted theorem is obtainable, retain and file the precise residual core blockers under #81; a list of successful dimensions does not complete this contract.

Its completion discipline also says:

> A failed estimate or isolated surviving sector is not a counterexample. A negative resolution requires an admissible fixed region and its **complete normalized action**, followed by the precise corrected statement and residual owners.

**Assessment: the written mathematical delivery satisfies that negative
route**, subject to scrutiny of the conventional proofs. CFT4 is a theorem
about the **whole original flat class**, not a list of successful examples.
K10 supplies fixed admissible complete-action obstructions in every excluded
dimension. A classification of the limit of each individual higher-dimensional
region is not stated as an additional condition of this alternative.

| Original requirement | Delivery evidence | What is not inferred |
| --- | --- | --- |
| Actual densities, contacts and summable remainders | FL1–FL12; K2–K9 and H2–H14 for the complete negative families; the finite derivative ledger above | An all-dimensional universal positive producer |
| Signed moments and physical normalization | Existing dimension kernels and G7; all-sector H10–H13 and K6–K9 | A fitted coefficient or 4D coefficients copied into other dimensions |
| Independent target and full action at one cutoff | FL13–FL14/S30 in 2D–4D; independently zero targets and H15/K10 in the obstructions | An isolated-sector obstruction, discarded point term or rate |
| Odd/even cases, components and nonzero field controls | General signed cubic argument, all-dimensional kernel identities, exact ordered partitions and S30's retained field/face terms | A new global graph or combined-slope restriction |
| Separate actual-law expectation | FL18/CFT2 and the individual obstruction transfers | Variance or convergence of individual sprinklings |
| Corrected quantified statement and coverage | CFT3–CFT4, with all-dimensional reduction and preserved positive subclasses | Failure of every higher-dimensional geometry |
| Residual owners and verification distinctions | Sections 5–6 below | Completion of #81/#24, independent review, or a compiled general manifold theorem |

Earlier delivery receipts called individual higher-dimensional classification
an open residual under #149/#81. It is indeed open mathematics, but treating
it as a **mandatory further #149 acceptance test** would add a condition not
present in the quoted contract. This assessment corrects that interpretation;
it does not rewrite the earlier receipts or change the issue body.

Accordingly the next mandatory gate for this delivered flat theorem is
**independent mathematical scrutiny and the separately authorized integration
process**, not another example-specific proof or an exhaustive classification
of all higher-dimensional contacts. A universal replacement target in higher
dimensions remains valuable research under the general #81/#151 nonlocal
program; it is not claimed here. #149 remains open until its authorized
administrative decision. No original scope, title, body or checkbox is edited.

## 5. Physical 4D conclusion and the first curved-4D obstacle

For **every flat 3+1-dimensional G-SS region**, not just an embedded Minkowski
or torus example, the written theorem gives the canonical joint limit for
the complete deterministic action and the original-law mean. It removes the
flat-topology/holonomy/global-graph gap in this spacelike two-face core.
It does not prove emergence of the metric, gravitational dynamics, a
sample-wise continuum limit, or any null/mixed or curved extension.

For a general curved **4D** G-SS member the finite-density accounting and
Poisson foundation already exist, and S30 supplies the written local short
bulk/face/joint producer. Let T_g denote its independent unit-field target.
For a common fixed cutoff the exact G1/G4 identity gives

```math
\begin{aligned}
T_g&=\frac12\int_M R_g\,d\mu_g+\int_J\coth\theta\,dA_g,\\
\mathcal A_{\rho,4}-T_g
 &=L_g^\delta(\rho)+(S_g^\delta(\rho)-T_g),\\
S_g^\delta(\rho)-T_g&\longrightarrow0.
\end{aligned}\tag{CFT5}
```

Thus, consuming that short result, the remaining full-target question is
exactly whether the **whole physical long response** tends to zero. In flat
space the cover/development argument gives faithful quadratic diamonds and
a finite separated null-route arrangement. **That is the first unavailable
replacement in curved 4D:** absence of conjugate points and the faithful
quadratic-volume representation no longer follow. Even on the universal
cover a cut/conjugate locus can carry multiple or continuously many null
geodesics; a uniform phase inverse or finite nondegenerate branch list cannot
be assumed. The compact-length argument can still bound the number of
relevant deck classes in a curved ambient. What is missing is a faithful
quadratic diamond or controlled null-ray system **within each class**, not
just a list of those classes. The failure is before a Taylor or signed-kernel
argument, not merely a missing partition-of-unity summation.

Here is a precise sufficient producer and its weaker exact response test,
using only #151's existing G5–G7 interface. Let N_g(w) be the **physical** long
pair primitive at `0 < V_g <= c_4*w^2`; the omitted null pairs have zero
pair measure. For arbitrary
constants b_1,b_2,b_3 put

```math
\begin{aligned}
E_g(w)&=\frac{N_g(w)-b_1w-b_2w^2-b_3w^3}{w^3},\\
L_g^\delta(\rho)
 &=2\beta_4c_4^{-3/2}\int_0^\infty
 z^4K'_4(z^2)E_g((c_4\rho)^{-1/2}z)\,dz.
\end{aligned}\tag{CFT6}
```

The identity is Stieltjes integration by parts followed by the three exact
integer moment cancellations; it does **not** assert the existence of a
jet. Finite pair measure and exponential decay control infinity. At zero,
N_g(w) tends to zero, so the Stieltjes boundary term vanishes; the displayed
integral is integrable there even before assuming a bounded E_g. A
geometry-derived bounded E_g tending to zero
would suffice by dominated convergence. More generally #151 can prove the
vanishing of the displayed signed integral directly, or compute a surviving
fully matched response. A pointwise cubic jet is sufficient, not logically
necessary. Any retained fractional/log contact and its face/cutoff/regular
partners must be assembled before declaring an obstruction.

The [sphere–circle assembly](sphere-circle-assembly.md) proves this for its
selected 4D focusing geometry, not for arbitrary curved G-SS members. The
[7D focusing obstruction](seven-dimensional-focusing-obstruction.md) does not
settle the 4D question either. No universal curved-4D theorem or counterexample
is supplied here. This is the existing **#151** geometric long-producer task,
with **#81** owning the complete curved-4D/general coverage decision. No new
shared definition, duplicate child, or example-specific side task is created.

The [curved-4D continuation](curved4-physical-response.md) derives a branch-free
physical clock pushforward and a general small-sublevel bound, audits the S30
hypothesis discharge, and supplies a weaker signed dilation-increment test.
Its critical geometric estimate is still blocked; it proves neither a general
curved-4D limit nor a complete-action obstruction.

## 6. Evidence pins, residual owners and verification boundary

The source audit starts at PR #163 head
`b55a46cd8015bb1777b2d4f8de3d3689be9fd65c`, based on current integration head
`81d99e4bb247b308b33d1917922f43a6fb69c8c0`. The strengthening in this note and
its companion edits is later work, not retroactive evidence about that head.
Useful unchanged source pins are:

- [Flat reduction and counterexamples before stabilization](https://github.com/q5m-ai/causal-set-emergence/tree/b55a46cd8015bb1777b2d4f8de3d3689be9fd65c/notes).
- [Consumed short producer S30](https://github.com/q5m-ai/causal-set-emergence/blob/0208f7caa8cafad594842dd7eab551586c598ce5/notes/general-metric-short-remainders.md#8-quantified-short-theorem-partition-cancellation-and-the-151-boundary).
- [Complete selected 4D sphere–circle assembly](https://github.com/q5m-ai/causal-set-emergence/blob/f001e5747cdd0b70b4f08658e1655fa6f438a7d3/notes/sphere-circle-assembly.md).
- [Compiled generic dimension expectation source](https://github.com/q5m-ai/causal-set-emergence/blob/f572b16ad530c5fcd5da1e728979a52070d158fc/formal/BoundaryDraft/DimensionMeasureExpectation.lean).

**#149:** this sharp flat theorem and its negative-route delivery.
**#151/#81:** the actual general curved-4D long response, broader nonlocal
classification and the parent corrected general statement. **#81/#24:**
retain their original curved and null/mixed coverage and verification gates;
flat written coverage alone does not complete those parents. Timelike
Conjecture 2 remains outside this task. **#86/#94:** independent human
scrutiny, source/novelty review, justified formalization and final artifact
verification. The bounded thin-4D formal port remains separate.

The audit strengthens the causal-development and arbitrary-mask explanations,
makes the folded-remainder transfer explicit, and repairs the stale introductory
claim that dimension five was unresolved. It does not change the equations
or coefficients of FL1–FL18, H1–H15 or K1–K10. It finds no reason to withdraw
those written conclusions; that is an author's assessment, not proof-checker
or independent reviewer approval.

Executable checks validate finite algebra, selected integrals and negative
controls, not these universal geometric arguments. No Lean/checker/dependency/
build input changes here, no fresh Lean audit is claimed, and the existing
compiled bridge does not certify the manifold asymptotics. Review of the
starting head is not review of the final stabilization head. PR receipts
record actual local/CI/browser validation separately. Nothing in this note
authorizes merge, deployment, agent launch or automatic issue closure.

Refs #149, #81, #24, #151, #86, #94.
