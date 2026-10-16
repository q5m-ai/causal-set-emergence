# When the mean causal-set action recovers geometry — and when it does not

**Compact research manuscript for scrutiny, not a submission or accepted paper.**
All mathematical sources in this manuscript are pinned to integration commit
[`9e0068f91c219fe61984d20fdb3f6939eab907c4`](https://github.com/q5m-ai/causal-set-emergence/tree/9e0068f91c219fe61984d20fdb3f6939eab907c4)
(hereafter **S**). This manuscript summarizes existing arguments; it supplies
no new proof or formal certification. Principal claims below have **written-proof**
status. See the [review packets](review.md) for the proof dependencies, not issue history.

## Abstract

The mean of the unsmeared minimal-layer Benincasa–Dowker–Glaser action is
compared with half the integrated scalar curvature plus an angle-weighted
past–future joint term. The source reports a smooth curved four-dimensional
complete-action obstruction, a sharp universal flat dimension theorem, and
positive curved subclasses including geometries with focusing. The decisive
object is the actual small-volume distribution of all causal endpoint pairs,
not a local curvature expansion alone. We state the exact quantifiers, explain
the signed cancellation and matched focusing mechanism, and isolate the
geometric estimates needing independent scrutiny. These are fixed-background
mean-action statements, not emergence of dynamics, sample-wise convergence,
novelty certification, or empirical evidence for causal-set physics.

## 1. Observable and geometric contract

**G-SS** means: a fixed smooth time-oriented globally hyperbolic Lorentzian
ambient manifold of integer dimension at least two; a nonempty precompact
open ambient-causally-convex region M; its entire frontier consists of two
compact embedded smooth spacelike hypersurfaces-with-boundary, each possibly
disconnected and achronal, respectively past and future. Their relative
interiors are disjoint and their common boundary is exactly a compact smooth
codimension-two joint J, with independent conormals. Empty J is allowed.
There are no other boundary strata. No global graph, orientability,
simple-connectedness, field equation, energy condition or absence of caustics
is imposed. These are the source's geometric hypotheses, not analytic limit
assumptions ([contract §§2–3][contract]).

The signature is positive-time. Scalar curvature uses the contract's Riemann
sign, calibrated in four dimensions by the conformal formula below. Both
normals at a spacelike joint are future unit timelike normals. Its area is
induced by minus the restricted metric; in dimension two each joint point
has mass one. Put $`C=g(n_-,n_+)>1`$ and $`\theta=\mathrm{arcosh}(C)`$.
For the actual exclusive physical interval and geometric volume measure,

```math
\begin{aligned}
V_g(x,y)&=\mu_g(\{z\in M:x\preceq z\preceq y,\ z\notin\{x,y\}\}),\\
\mathcal A_{\rho,d}&=a_d\rho^{2/d}\mu_g(M)
 -\beta_d\rho^{1+2/d}\int_{x\prec y}K_d(\rho V_g(x,y))\,d\mu_g(x)d\mu_g(y),\\
\mathcal T_g&=\frac12\int_M R_g\,d\mu_g+\int_J\frac{C}{\sqrt{C^2-1}}\,dA_g,\\
g=\Omega^2\eta\quad(d=4)&:\qquad R_g=6\Omega^{-3}\Box_\eta\Omega.
\end{aligned}
```

The order is the ambient order restricted to M. Containment is proved before
identifying isolated and ambient intervals. A physical union is counted once,
not once per geodesic. Ordered pairs have no factor one-half.

For exact all-dimensional normalization ([kernel source §§1–2][kernels]), set
$`m=\lfloor d/2\rfloor+1`$ and define

```math
\begin{aligned}
c_d&=\frac{2\pi^{(d-1)/2}}{2^{d-1}d(d-1)\Gamma((d-1)/2)},&
g_d&=\frac{c_d^{2/d}}{\Gamma(1+2/d)},\\
a_{2n}&=4g_{2n},&\frac{\beta_{2n}}{a_{2n}}&=\frac{\Gamma(n+2)\Gamma(n)}{\Gamma(2n)},\\
a_{2n+1}&=2g_{2n+1},&\frac{\beta_{2n+1}}{a_{2n+1}}&=\frac{2n+2}{2^{2n}},\qquad n\ge1,\\
P_{d,0}(z)&=1,&P_{d,i}(z)&=P_{d,i-1}(z)+\frac{d}{2i}z(P'_{d,i-1}(z)-P_{d,i-1}(z)),\\
K_d(z)&=P_{d,m}(z)e^{-z},&C_{k+1}^{(d)}&=k![z^k]P_{d,m}(z),\quad 0\le k\le m.
\end{aligned}
```

The recurrence runs from i=1 to m. With N the event count and L_k the number
of distinct ordered related pairs with exactly k intervening events, the
observable and its **separately proved finite-density bridge** are

```math
\begin{aligned}
A^{\mathrm{disc}}_{\rho,d}
 &=\rho^{-(d-2)/d}\left[a_dN-\beta_d\sum_{k=0}^{m}C_{k+1}^{(d)}L_k\right],\\
\mathbb E_{\mathrm{Poisson}(\rho\mu_g|_M)} A^{\mathrm{disc}}_{\rho,d}
 &=\mathcal A_{\rho,d}\qquad(\rho>0).
\end{aligned}
```

This is $`l_p^{d-2}S^{(d)}/\hbar`$ for d>2 and directly
$`S^{(2)}/\hbar`$ in 2D. The generic bridge has compiled foundations;
new manifold hypothesis discharges and asymptotics below are written.
A limit of expectations is not a random limit under a single fixed law.

## 2. Principal statements

### Theorem CO: a complete-action curved-4D obstruction

Take the fixed analytic metric and slab

```math
\begin{aligned}
Q&=\mathbb R_t\times(\mathbb R/20\mathbb Z)_r
 \times(\mathbb R/\pi\mathbb Z)_x\times(\mathbb R/20\mathbb Z)_z,\\
g&=dt^2-dr^2-dx^2-dz^2+\tfrac14\sin^2(2x)(dt-dr)^2,\\
M&=(-7/8,7/8)\times\mathbb T^3,&\mu_g(M)&=700\pi,\\
R_g&=0,&J&=\varnothing,\qquad\mathcal T_g=0,\\
\mathcal A_{\rho,4}&=-D\rho^{3/14}+O(\rho^{1/6}),&D&>0.
\end{aligned}
```

All G-SS hypotheses hold; the metric is curved despite zero scalar curvature.
Both endpoint coordinate densities are one. The same asymptotic holds for
the original-law expected discrete action by the finite-density identity.
The positive constant D is **defined by the physical source integral in CO1**,
not fitted from numerical action values. Its factor I obeys the model enclosure
$`1/4<I<3/2`$; the arithmetic certificate alone does not establish D's physical
meaning. Sources: [CR4–CR9][focal], [CG1–CG9][global],
[CC1–CC13][certificate], [CO1–CO16][obstruction].

### Theorem FLAT: sharp universal dimension range, not universal failure

For every d in {2,3,4} and **every flat G-SS member**, the complete deterministic
and original-law expected actions tend to the independently defined joint
integral. There is no extra quotient, topology, width or global-graph condition.
Smoothness supplies the sufficient finite regularity in the source; this is
not an all-C3 statement ([CFT1–CFT4][flat]).

For every integer d≥5 there exists the following fixed analytic counterexample.
Put p=d−3. Let X_d be Euclidean space with coordinates (x,y,b), b in R^p,
quotiented by (x,y,b)↦(x+1,−y,b), (x,y,b)↦(x,y+2,b), and translations by
10 in each b coordinate. Set M_d=(−21/40,21/40)×X_d with the ultrastatic flat
metric. Its joint and curvature target are zero. [K1–K10][klein] state

```math
\begin{aligned}
\lim_{\rho\to\infty}\mathcal A_{\rho,5}&=D_5>0,\\
\lim_{\rho\to\infty}\rho^{-(1-5/d)}\mathcal A_{\rho,d}&=D_d>0
 \qquad(d\ge6).
\end{aligned}
```

The same conclusions hold for expectations. Thus “every flat G-SS member has
the canonical limit” holds **exactly** in dimensions 2–4. This existential
negative clause does not contradict all-dimensional positive Minkowski and
specified torus subclasses. It is a corrected universal **flat** theorem,
not the broader corrected curved theorem sought by #81/#24.

### Theorem SW: a geometrically specified curved positive family

For **every fixed smooth positive** function Omega on
R×S²₁×(R/20Z), without symmetry or smallness restrictions, set

```math
\begin{aligned}
M&=(-2,2)\times S^2_1\times(\mathbb R/20\mathbb Z),&
g&=\Omega(t,p,z)^2(dt^2-h_{S^2}-dz^2),\\
\mathcal T_g&=\int_{-2}^{2}\int_0^{20}\int_{S^2}
 [\Omega^2+3\Omega(\Omega_{tt}-\Omega_{zz}-\Delta_{S^2}\Omega)]\,dA\,dz\,dt,\\
\lim_{\rho\to\infty}\mathcal A_{\rho,4}
 &=\lim_{\rho\to\infty}\mathbb E A^{\mathrm{disc}}_{\rho,4}=\mathcal T_g.
\end{aligned}
```

Here $`\Delta_{S^2}p_i=-2p_i`$. The joint is empty and antipodal focusing
is retained. Omega=1 gives 320π. This [SW1–SW14 theorem][sw] extends the
sphere-independent [RC1–RC17 theorem][rc]; neither assumes long cancellation
as admissibility. Constants depend on the fixed metric; no degenerating-factor
uniformity is asserted. RPL/FCDC and HO provide other sufficient geometric
classes, not a necessary-and-sufficient curved classification.

### Theorem C2: the whole smooth curved two-dimensional spacelike core

For **every 2D G-SS member**, with no additional topology or chart restriction,
the deterministic and separately transferred original-law expected limits equal
$`\mathcal T_g`$, with every joint endpoint counted once. The actual kernel is
$`K_2(z)=(1-2z+z^2/2)e^{-z}`$, with a₂=2 and β₂=4.
[C2.1–C2.18][c2] include physical route unions and both overlap corners.
This written theorem was integrated through #176. It does not imply curved
3D or any new compiled curved limit. The regular conformal two-tip theorem
integrated through #179 has its distinct CT1 hypotheses and null strata;
see [coverage](coverage.md), not G-SS by substitution.

## 3. Readable proof spine and vulnerable inferences

**1. Identify the action before taking a limit.** Mecke's pair formula and
Poisson interval probabilities produce the signed kernel exactly. The point
term and both endpoint measures remain. Curvature and joint targets are
calculated independently. This prevents proving a statement about a renamed
observable or defining the target by its limit.

**2. Split once at a fixed positive temporal gap.** The written local producer
[S30][short] supplies the short bulk, face compensation and joint contribution.
It retains source derivatives, all ordered chart pairs, and the point once.
The remaining complete long response is not small merely because its intervals
are thin. The universal identity “target convergence iff this actual long
response vanishes” is useful accounting, **not a geometric corrected theorem**.

**3. Understand the cancellations.** In 4D the physical kernel and its Mellin
transform are

```math
\begin{aligned}
K_4(s)&=(1-9s+8s^2-\tfrac43s^3)e^{-s},\\
\widehat K_4(z)&=\Gamma(z)\prod_{j=1}^3(1-2z/j),\\
\int_0^\infty u^jK_4(u^2)\,du&=0\quad(j=0,1,2).
\end{aligned}
```

An actual cubic small-volume primitive with a summable little-o remainder
therefore gives zero long response. Taking absolute values before subtracting
the canceled terms destroys this mechanism. Other dimensions require their
own moments and critical order.

**4. Prove, rather than assume, the geometric primitive.** FLAT develops
individual lifted diamonds faithfully, enumerates finitely many relevant lifts,
and controls the physical-union correction. Its moving-mask/coarea argument
works even at dependent or infinite-order contacts in 2D–4D. For SW, the
signed sphere-point map retains both orientations, both endpoint densities
and the interior conformal density. Straighten closing fibres first. The
actual endpoint abundance makes the cubic remainder bounded by an integrable
$`a^{-1/4}`$, where a is angular deficit from the antipode.

**5. In CO the matched fractional term survives.** Classification of *all*
minimizers gives the quartic contact and ordinary seams. In minimum coordinates,
volume scales as $`k^{7/2}`$ and pair measure carries
$`2k^{7/2}\,dk\,dr\,dE`$. Matching both wells, both interval tips, moving
opening and physical overlaps produces a Mellin pole at 9/7. CO13 is the
crucial model-to-physical transfer, with an O(sqrt(k)) gain after actual
closing-fibre integration. CO15 accounts for the regular complement, including
the small-u chart. Ordinary poles are canceled; the 9/7 multiplier is
$`\Gamma(9/7)22/343>0`$. The negative pair prefactor then yields CO1.
No other part of the assembled action has a compensating pole of that order.

**6. Restore everything, then transfer the mean.** Combine at the same cutoff,
retain the full physical union and every complementary sector, and use S30.
Only afterwards invoke the already identified Poisson mean. No variance or
individual-sprinkling conclusion follows.

**Weakest / highest-priority review steps:** CO's global minimizing-path
classification; uniform endpoint/opening/closing matching in CO5–CO13; Mellin
continuation and completeness of CO14–CO16; the analytic error bounds behind
the model certificate; FLAT's faithful development and arbitrary-mask
transport; SW's signed moving sphere map and domination; and the consumed
S30 theorem. Finite diagnostics can catch errors but do not prove these
uniform statements. No blocking defect is asserted here, and no independent
acceptance is inferred from the absence of one.

## 4. Relationship to the published conjecture

Dowker, Liu and Lloyd-Jones, *Timelike boundary and corner terms in the causal
set action*, [CQG DOI 10.1088/1361-6382/ae0be5](https://doi.org/10.1088/1361-6382/ae0be5),
[arXiv:2501.00139v2 §§2.4–2.7, equation (11), §7][dll], propose the mean
bulk-plus-angle-weighted-joint limit. Multiplying their (11) by the Planck
power gives our target. Their sign convention must be converted, not guessed
from the signature. Their joint is a **past–future intersection**, not any
same-side seam. Their isolated/embedded regimes agree here only through
proved interval containment; smearing changes the observable.

G-SS is a precise repository **subcase**, not a quotation of a fully enumerated
published admissibility predicate. If the published universal claim includes
these compact-Cauchy slabs, CO is a counterexample to that claim in physical
4D, not just a failed proof route. The paper's globally hyperbolic formulation
and curved empty-joint precedent support this reading; intended-scope scrutiny
is explicitly requested. The flat theorem corrects the universal dimension
range for G-SS only. None of this resolves all published null/mixed regimes,
timelike Conjecture 2, or the broader corrected curved theorem.

The action coefficients, Poisson averaging, overlap method and conjecture are
prior work. The [passage audit][literature] records actual diamond calculations
in dimensions 2–16 in the inspected 2015 source, whereas DLL describes an
all-dimensional result; the repository now has its own written ND diamond
argument but that does not settle historical priority. Chevalier's primary
text has not been obtained. No first-proof or novelty claim is made.

## 5. Limits of this release

See [the current matrix](coverage.md). #24/#81/#94/#86 remain open; their
remaining acceptance obligations are not conditions for making these bounded
mathematical claims available for scrutiny. Unmerged #180 is not an input.
The [experimental report](experiments.md) is independent: an obstruction in a
background action limit is neither a propagation calculation nor falsification
of causal-set physics. No manuscript submission, outreach or launch is performed.

[contract]: https://github.com/q5m-ai/causal-set-emergence/blob/9e0068f91c219fe61984d20fdb3f6939eab907c4/notes/general-contract.md
[kernels]: https://github.com/q5m-ai/causal-set-emergence/blob/9e0068f91c219fe61984d20fdb3f6939eab907c4/notes/dimension-kernels.md
[focal]: https://github.com/q5m-ai/causal-set-emergence/blob/9e0068f91c219fe61984d20fdb3f6939eab907c4/notes/curved4-focal-research.md
[global]: https://github.com/q5m-ai/causal-set-emergence/blob/9e0068f91c219fe61984d20fdb3f6939eab907c4/notes/curved4-focal-globalization.md
[certificate]: https://github.com/q5m-ai/causal-set-emergence/blob/9e0068f91c219fe61984d20fdb3f6939eab907c4/notes/curved4-focal-certificate.md
[obstruction]: https://github.com/q5m-ai/causal-set-emergence/blob/9e0068f91c219fe61984d20fdb3f6939eab907c4/notes/curved4-complete-action-obstruction.md
[flat]: https://github.com/q5m-ai/causal-set-emergence/blob/9e0068f91c219fe61984d20fdb3f6939eab907c4/notes/corrected-flat-theorem.md
[klein]: https://github.com/q5m-ai/causal-set-emergence/blob/9e0068f91c219fe61984d20fdb3f6939eab907c4/notes/flat-klein-bottle-obstruction.md
[sw]: https://github.com/q5m-ai/causal-set-emergence/blob/9e0068f91c219fe61984d20fdb3f6939eab907c4/notes/sphere-dependent-conformal-limit.md
[rc]: https://github.com/q5m-ai/causal-set-emergence/blob/9e0068f91c219fe61984d20fdb3f6939eab907c4/notes/curved4-corrected-convergence.md
[c2]: https://github.com/q5m-ai/causal-set-emergence/blob/9e0068f91c219fe61984d20fdb3f6939eab907c4/notes/curved-two-d-limit.md
[short]: https://github.com/q5m-ai/causal-set-emergence/blob/9e0068f91c219fe61984d20fdb3f6939eab907c4/notes/general-metric-short-remainders.md
[literature]: https://github.com/q5m-ai/causal-set-emergence/blob/9e0068f91c219fe61984d20fdb3f6939eab907c4/notes/general-contract-literature.md
[dll]: https://arxiv.org/html/2501.00139v2#S2.E11
