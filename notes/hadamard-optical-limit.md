# Intrinsic Hadamard optical geometry in four dimensions (#172)

**Written theorem HO-4, not a Lean proof or independent human acceptance.**
The proposed first milestone of #172 is proved below for its stated class.
The reason is not merely uniqueness of a geodesic. Comparison first traps
**every** interval point; a null rescaling then has a nonfocusing quadratic
reference metric. Smooth dependence of the **whole two-cone domain**, including
its apices and transverse intersection, removes the apparent tip logarithm.
The resulting phase estimate is an output of geometry. The ambient metric
itself need not have a quadratic path action, constant curvature or a conformal
Minkowski chart.

This is one sufficient corrected theorem, **not** a universal replacement for
Conjecture 1′. The [coverage ledger](intrinsic-coverage-ledger.md) keeps proved
corrections, proposed conjectures and unknown coverage separate. #81/#24 and
human expert acceptance #94/#86 remain open. No null-boundary assertion is made.

## 1. Exact statement, dependencies and fixed conventions

Let (Sigma,h) be a complete simply connected smooth Riemannian three-manifold
with sectional curvature at most zero. In the ambient spacetime set

```math
\begin{aligned}
 Q&=\mathbb R\times\Sigma,& g&=dt^2-h,&d\mu_g&=dt\,d\mathrm{vol}_h,\\
 M&\text{ is any fixed smooth ambient-contained G-SS region in }Q,\\
 \mathcal T_g&=\frac12\int_M R_g\,d\mu_g
                  +\int_J\coth\theta\,dA_g.
\end{aligned}\tag{HO1}
```

G-SS means exactly the [original contract, §§2–3](general-contract.md): compact
closure, the actual two smooth achronal spacelike faces, their transverse
common joint and no extra strata. There is no global graph hypothesis on M.
The ambient restrictions here specify a **subclass**, not a change to G-SS.
No uniform curvature bound on all of Sigma is required. Bounds on the compact
causal enclosure and its slightly larger tubes suffice. All data are fixed
before density varies.

**Theorem HO-4.** Every such M has the complete canonical deterministic limit
T_g, and separately the same expected discrete-action limit under the original
Poisson law of intensity rho times restricted geometric volume. Nonempty,
variable-angle joints are included. For every sufficiently small **fixed**
positive temporal-gap cutoff, the complete long response tends to zero.
No rate for the full action, shrinking-cutoff limit or sample-wise claim follows.

Substantive dependencies, read at integration source
`0358c32f7ca19a4491b7e904ee5eaf44003619d3`:

| Input | What is consumed, not inferred |
| --- | --- |
| [G-SS](general-contract.md), [literature crosswalk](general-contract-literature.md), live #172/#81/#24 and [integrated stocktake](https://github.com/q5m-ai/causal-set-emergence/issues/81#issuecomment-6159774542) | Independent action/target and the exact scope; published Conjecture 1′ is not literally G-SS; no novelty or expert-acceptance claim |
| [General short geometry G1–G16](general-metric-short.md) and [S1–S30](general-metric-short-remainders.md) | Entire strict-short theorem, including its null-edge interval proof, both measures, moving face/corner roots, temporal-shell conversion, compensating fluxes and ordered partition cancellation |
| [PW2–PW7](nonconformal-plane-wave-limit.md) | Exact quadratic reference cones, including the parallel generator; used only for the **limit of the rescaled metric**, not as an exact formula for the original metric |
| [GC6 and its contact proof](geometric-long-cancellation.md#true-contacts-joints-and-the-fixed-temporal-shell) | Intrinsic spacelike-face/cutoff rank argument, discharged again in §6; no extension to #169's characteristic null contacts |
| [Dimension kernel §§1–4](dimension-kernels.md), [shared interface](dimension-producer-interface.md) | Actual 4D constants and three signed moments; point only in short, equality in long, both endpoint measures and all ordered labels |
| [MeasuredOrderBDG4](../formal/BoundaryDraft/MeasuredOrderBDG4.lean), [#137 proof boundary](../formal/COMPACT_MEASURED_ORDER.md) | Existing generic finite-density bridge; §8 supplies the written geometric instance, not a new compiled manifold theorem |
| [CP2/CP4/CP6](curved4-physical-response.md), [CO1–CO16](curved4-complete-action-obstruction.md) and its CR/CG/CC dependencies | Physical clock accounting and the unchanged #164 obstruction/certificate boundary; no obstruction proof is re-run, edited or used to infer positive coverage |

The standard Riemannian inputs used below are Cartan–Hadamard, the squared-
distance Hessian comparison, first/second variation, and smooth dependence of
geodesic/Jacobi ODEs. Their specific consequences are derived below; the words
“no cut locus” do not supply the high derivatives. Hopf–Rinow makes bounded
closed spatial tubes compact. Causal speed is at most one in h, so t is Cauchy,
ambient causal diamonds are compact, and Q is globally hyperbolic. None of this
alone proves the separately required containment of intervals in M.

## 2. Start with the actual optical ellipsoid and clock

Translate the source time to zero. For spatial endpoints p,q let L=d_h(p,q),
tau=L+e. Ultrastatic causality is exactly temporal gap at least spatial distance:
integrating the speed bound proves necessity; traversing a minimizing geodesic
at speed at most one proves sufficiency. Thus, for endpoints in M,

```math
\begin{aligned}
 I[(0,p),(L+e,q)]
 &=\{(t,z):d_h(p,z)\le t\le L+e-d_h(z,q)\},\\
 V(p,q,e)&=\int_\Sigma
       [L+e-d_h(p,z)-d_h(z,q)]_+\,d\mathrm{vol}_h(z).
\end{aligned}\tag{HO2}
```

This counts physical points once. Ambient containment identifies it with the
restricted exclusive volume, since endpoints have zero volume. In long, small
excess pairs with tau at least delta and e at most delta/2 have L at least
delta/2. The compact endpoint set bounds L above. The spatial diagonal with
long positive tau belongs instead to the positive-volume complement.

Extend the unique minimizing segment to a complete unit-speed geodesic gamma,
with gamma(0)=p and gamma(L)=q. Every z has a unique nearest point gamma(s) on
this **line**, not necessarily on the segment. Squared distance to z is proper
and strictly convex along the line: its second derivative is at least two.
This proves existence and uniqueness of the foot. The implicit function theorem
applied to its first derivative proves smooth dependence on z and the geodesic
parameters, including on the line, since squared distance is smooth on a
Hadamard manifold. The foot variation is orthogonal. Set r=d_h(z,gamma(s)).
Comparison for either right triangle gives

```math
\begin{aligned}
 d_h(p,z)^2&\ge s^2+r^2,&
 d_h(q,z)^2&\ge(L-s)^2+r^2,\\
 -e/2&\le s\le L+e/2,&
 r^2&\le
 \frac{e(2L+e)(s+e/2)(L+e/2-s)}{(L+e)^2},\\
 0&\le t-s\le e.
\end{aligned}\tag{HO3}
```

For the middle line insert the first line into HO2 and solve the Euclidean
prolate-ellipse inequality. It holds also outside the segment. For the last
line use d_h(p,z) at least |s| and d_h(q,z) at least |L-s|.
This is containment of the **whole physical interval**, not a lower-volume
comparison or a bound for one Jacobi field. It also traps every causal path
joining the endpoints, since each point of such a path is in that interval.

In particular r is O(sqrt(e)) uniformly, while s within O(e) of either end
has r=O(e). The two end caps extend beyond s=0,L; deleting them would change
the integral. In the central portion HO3 gives the familiar sharper width
O(sqrt(e*s*(L-s)/L)). No derivative is taken in these singular slice variables.

## 3. Rescale the metric, not an interior distance expansion

Parallel transport a local orthonormal screen frame along gamma and use
spatial Fermi coordinates z=exp_gamma(s)(Y). They are valid on a common tube
for a compact family of (p,q) with L bounded below. One can also see injectivity
from the unique foot: a perpendicular geodesic realizes its minimizing foot
by convexity, and the Hadamard exponential is injective. The inverse is smooth
by the preceding foot argument. Finite direction-frame patches suffice.

Along the axis the metric is Euclidean to first order. The Jacobi/second-
variation calculation in Fermi coordinates gives
h_ss=1+A_s(Y,Y)+O(|Y|^3), h_sA=O(|Y|^2), and h_AB=delta_AB+O(|Y|^2), where
A is the negative of the sectional-curvature operator in planes containing
gamma-prime. Thus A is positive semidefinite. Equivalently its sign is fixed
by the spatial index form integral of |Y-prime| squared plus A(Y,Y). This
avoids confusing the Riemannian comparison sign with G-SS's scalar convention.
The remainder and any fixed finite set of derivatives are smooth and bounded
on the compact family, by Taylor's integral formula.

Put e=eta squared, allowing either sign of eta for smooth extension. The map
and **actual** pulled-back volume are

```math
\begin{aligned}
 t&=s+\eta^2 v,& z&=\exp_{\gamma(s)}(\eta Z),\\
 g_\eta&=\eta^{-2}\Phi_\eta^*g
       =2\,ds\,dv-|dZ|^2-A_s(Z,Z)\,ds^2+O(\eta),\\
 \Phi_\eta^*d\mu_g
   &=\eta^4\sqrt{\det h(s,\eta Z)}\,ds\,dv\,d^2Z,\\
 P&=(0,0,0),&Q_L&=(L,1,0).
\end{aligned}\tag{HO4}
```

The O(eta) here is a **smooth tensor family with all needed derivatives**,
not merely componentwise convergence. For example (1-h_ss)/eta squared and
h_sA/eta divide smoothly by the stated axis vanishing; the remaining time
term is eta squared dv squared. No inverse s, L-s or eta remains. Passive
endpoint/frame derivatives have the same property. The determinant identity
is triangular and exact; the interior volume form is not replaced by its
axis value.

By HO3 every rescaled interval is in one fixed compact box, with
s between -eta squared/2 and L+eta squared/2, v in [0,1], and bounded Z.
Choose a larger open box with positive clearance. Both physical tips are the
fixed distinct points P,Q_L; L stays in a compact positive interval. The
limiting metric, denoted g_0, is Lorentzian. The function U=s+v is temporal
there, since g_0 inverse applied to dU twice is 2+A_s(Z,Z), at least two.
It remains uniformly temporal on the larger box for all small |eta|. This
controls every rescaled causal tangent and gives bounded U-parametrized ODEs.

## 4. Why the entire rescaled domain, including both tips, is smooth

This is the decisive step. A smooth limiting metric by itself is insufficient
if its cones are cut, conjugate, tangent to one another, or if actual intervals
can escape the common box. HO3 and the following construction discharge those
risks, uniformly over the compact endpoint family.

### 4.1 The reference cones have no hidden singular direction

Solve B''=A B with B(0)=I and B'(0)=0. For every fixed vector b,
(|B b| squared)'' is nonnegative and its first derivative at zero is zero;
thus |B b| is at least |b| on either side of zero. B is invertible. The
Wronskian identity makes B transpose B-prime symmetric. Consequently

```math
\begin{aligned}
 Z&=B(s)X,&
 v&=\widetilde v+\tfrac12X^TB(s)^TB'(s)X,\\
 g_0&=2\,ds\,d\widetilde v-dX^TG(s)dX,&G(s)&=B(s)^TB(s),\\
 \mathcal B(a,b)&=\int_a^bG(r)^{-1}\,dr,&
 \mathcal Q(a,b)&=2(b-a)\Delta\widetilde v
       -\Delta X^T\left(\frac{\mathcal B(a,b)}{b-a}\right)^{-1}\Delta X.
\end{aligned}\tag{HO5}
```

All coefficients and inverse margins are bounded on the needed finite s
interval. Extend G positively with bounded eigenvalues outside a larger
interval if using PW's global formulas; future reference paths have
nondecreasing s, so this changes no relevant interval. PW2–PW7 now describe
**the entire reference interval**, not just its central ray. For positive s
gap, the causal cost is strictly positive quadratic energy and its endpoint
inverse is nonsingular. At zero s gap the only causal direction is the vertical
one; on a nontrivial vertical null segment, the differential of Q in the s
gap is 2 times the positive v gap. Thus that direction also has a regular
null cone, not a missing collar. The averaged-matrix formulas remove the
apparent division by b-a. Equivalently, the transverse index form
integral of |Y-prime| squared plus A(Y,Y) is positive for every nonzero
zero-endpoint variation. There are no reference conjugate or cut points.

The two reference cone sheets meet transversely. Proportional null conormals
at an intersection would give matching generator tangents, hence one unbroken
null geodesic from P to Q_L by ODE uniqueness. HO5 says these endpoints are
strictly timelike (Q=2L). This is impossible. Compactness gives a positive
transversality margin on their intersection. Near either apex the other
cone inequality is strictly inactive, with a uniform margin after fixing
small apex neighborhoods. The intersection can contain the extrema s=0,L;
these are **regular cone-intersection points**, not discarded spatial tips.

### 4.2 A compact two-cone domain lemma, with proof

For this family the volume of the actual rescaled interval, against any
smooth compactly controlled density, is smooth in eta and the endpoint
parameters. Here are the domain details needed for that conclusion.

1. Enlarge the box first to contain both complete reference cones truncated
   just beyond the U levels of the opposite tip. These truncated cones are
   compact: future reference paths have s and v nondecreasing, and their
   nonnegative screen energy bounds |Z| squared by twice the product of their
   s and v gaps; reverse the argument for the past cone. This enlargement
   leaves room for ordinary ODE continuation. On it U is uniformly temporal.
   Normalize null initial vectors by dU=1 and parametrize their geodesics by U.
   Smooth dependence gives the perturbed solutions through these same finite
   U ranges in a still larger box. The ODE and its derivatives are bounded
   on the resulting compact direction and time ranges. Near an apex,
   position divided by U-distance from that apex extends smoothly; its angular
   differential is the ordinary nondegenerate unit-sphere differential.
2. Away from the apices the reference null-cone maps are embeddings and
   immersions by HO5. On compact pieces their inverses have a positive local
   margin. Immersion persists under sufficiently small smooth perturbation.
   Injectivity persists too: separated reference parameter points stay
   separated by compactness, while nearby points are handled by the uniform
   local inverse. Include a slightly larger reference cone neighborhood to
   avoid artificial endpoint edges in this argument.
3. These sheets exhaust the **actual** boundary. In the original ultrastatic
   geometry each cone boundary is generated by its minimizing spatial
   geodesic. A retained boundary segment and its continuation to the other
   endpoint lie wholly in HO3's box. Any sequence of purported extra boundary
   generators has a convergent initial direction and a convergent
   U-parametrized ODE solution there. Its limit is a reference generator.
   Step 2's inverse excludes an extra branch. This is where whole containment
   is essential; an unrelated extension of the metric outside the box would
   not justify this conclusion. Conversely the nearby sheets have the correct
   future/past side by their time orientation and local cone orientation.
   Continuous dependence of the causal boundary (or the same compact
   generator argument) identifies the intervening intersection with the
   actual interval. No choice of a selected ray replaces a physical minimum.
4. The two sheet functions have independent differentials at their common
   boundary. Their reference margin persists for small eta, including the
   vertical directions. The implicit function theorem uses these **two**
   functions as coordinates near the seam. Single-sheet neighborhoods use
   just its one defining function. There is no imposed boundary at s=0,L.
5. A finite smooth partition on the larger box divides the domain into
   interior pieces, single-sheet pieces, double-sheet corners and two apex
   pieces. The first three are smooth fixed-box/half-box/orthant integrals
   after the preceding coordinate changes, with the full moving Jacobians.
   At an apex use U-radius r, null angular direction, and the enclosed
   three-dimensional slice ball. For small r the slice cone is star-shaped
   in local spatial coordinates, its radius divided by r is smooth and
   positive, and the other cone is inactive. Scale the slice ball radially;
   its measure contains r cubed. Integrating r on a fixed small interval
   gives a common integrable derivative dominator, including r=0. Smooth
   cutoffs handle overlap with the other charts; no tip cap is omitted.
6. Every map, inverse and density above has bounded derivatives of any fixed
   finite order on its compact parameter domain. Differentiate **these
   resolved integrals**, not an indicator or an interior distance Hessian.
   Finite summation proves the assertion, jointly in endpoint parameters.

This proof uses ordinary ODE and inverse-function estimates with strictly
positive compact margins, not an assumed volume jet or an analytic metric.
It provides a finite resolved-domain integration, which is sufficient here;
no assertion about a single global RPL point map is needed.

The full integral is invariant under eta to -eta, Z to -Z, because HO4
maps the reflected points to the same physical points. Thus it is smooth
even in eta. Taylor to arbitrary even order, with its integral remainder,
makes it smooth in e=eta squared on the closed half-line. For example eight
eta derivatives and the corresponding passive derivatives suffice for the
four e derivatives used below. The exact optical volume therefore obeys

```math
\begin{aligned}
 V(p,q,e)&=e^2H(p,q,e),&0\lt c\le H\le C,\\
 |\partial_e^j\partial_\lambda^\alpha H|&\le C_{j,\alpha}
       \quad(0\le j\le4),\\
 H(p,q,0)&=\pi\int_0^L
       \frac{ds}{\sqrt{\det(D_+(s)+D_-(s))}}>0.
\end{aligned}\tag{HO6}
```

Here lambda denotes any of the finitely many passive endpoint/frame
coordinates, and D-plus/minus are the endpoint energy Hessians of g_0 in
Fermi screen coordinates. The last line follows by integrating the reference
clock width [1-Z transpose (D-plus+D-minus) Z/2] positive part. The index form
makes its matrix positive. Near either end its inverse determinant square
root is O(s) or O(L-s), respectively. Alternatively PW5 computes the same
whole positive volume after HO5. Continuity, compactness and a fixed small
interior reference subdiamond give a positive uniform lower bound. In flat
space it is pi L squared/6, agreeing with the **whole** flat diamond volume.
This identifies a coefficient after proving all tip bounds, not in place of them.

## 5. The former logarithmic route and the uniform near-null output

The earlier [optical-index attempt](geometric-long-cancellation.md#4-genuinely-different-routes-tried-and-the-sharper-remaining-blocker)
expanded at fixed longitudinal s. Its transverse parameter was sqrt(e/s),
so the critical absolute derivative bound involved the integral of ds/s.
That estimate was already bad for a flat diamond. HO3 proves that the omitted
tip domains have size e in every physical direction, hence volume O(e to the
fourth power): they are precisely at the threatened order, not disposable.

HO4 instead fixes both **spacetime** tips before differentiating. The limiting
cones are transverse even at their longitudinal extrema, and §4 integrates
all their moving charts together. This derives HO6 with no logarithm at that
order. It is not a cancellation guessed from the flat calibration. Nonpositive
curvature supplies both the global containment comparison and the positive
reference index form. Unique geodesics alone supplies neither argument.

Put w=sqrt(V), with **no c4 rescaling**. HO6 gives the actual smooth inverse
of w=e sqrt(H), with derivative at zero sqrt(H(p,q,0)) bounded positively.
All needed passive/mixed inverse derivatives are bounded. For ordinary
coordinate inverse theorems one may extend H to negative e to the required
finite differentiability order by its one-sided Taylor data; no physical
negative-excess interval is asserted. The null relation
is the smooth hypersurface tau=d_h(p,q) on the fixed long collar. Its time
derivative is one. Every sufficiently small volume long pair lies in this
collar: on the compact complement with e bounded positively, HO2 is continuous
and strictly positive. This also treats the spatial diagonal, large excess,
and every above-phase-cap complement, not just the nearly-null central sector.

## 6. Moving endpoint masks, cutoff contacts and the critical remainder

The actual pair form is dt_p dt_q dvol_h(p) dvol_h(q). In endpoint charts
retain both spatial Jacobians and every smooth source/target field. No
translation invariance or density at the source is substituted for HO2.
The only sharp masks are those of the actual endpoints in M and tau at least
delta. We now justify differentiating their integrals in w.

A fixed-long null source cannot lie on the future face or on J; the timelike
future-face conormal forces a future causal curve immediately outside the
closure. Likewise a target cannot lie on the past face or on J. A compact
limit of causal curves would give the same contradiction for a sequence
approaching such a forbidden contact. Thus those forbidden contacts have
positive clearance on the compact long-null set. This removes **no short
joint collar**.

The possible source-past and target-future contacts are independent on the
null relation: move the target along its nonzero null generator to change
its future-face function while fixing the source, then vary the source to
change its past-face function. A timelike conormal cannot annihilate that
generator. Compact local inverses give uniform contact coordinates.

The shell tau=delta adds a third constraint. Choose delta sufficiently small
once. With zero or one true face active, local null coordinates give its
independence from the shell. If both are active, speed control makes endpoints
O(delta) apart; compact disjoint face interiors away from J exclude them
there. Near J, with source x, separation r and null direction k, the leading
three differentials are

```math
\begin{aligned}
 \alpha_-\,dx,\qquad
 \alpha_+\,dx+\alpha_+(k)\,dr,\qquad dt(k)\,dr.
\end{aligned}\tag{HO7}
```

The joint conormals are independent and dt(k)>0, so the rank is three.
The smooth O(r) errors preserve it at every sufficiently small fixed delta,
uniformly by compactness. If J is empty, there are no such two-face shell
contacts at small delta. This is a proof of the needed simultaneous rank,
not a generic transversality assumption on the faces.

Use w and the active contact functions as coordinates. Finite smooth pair
partitions supported within these charts turn all masks into fixed orthants.
The full pulled-back density is smooth, including both endpoint volume forms,
fields, every contact Jacobian and shell movement. Compact Taylor remainder
after integration therefore produces the **actual** long density and primitive

```math
\begin{aligned}
 b(w)&=b_0+b_1w+b_2w^2+O(w^3),\\
 N(w)&=b_0w+\tfrac12b_1w^2+\tfrac13b_2w^3+O(w^4).
\end{aligned}\tag{HO8}
```

Signed endpoint weights are allowed. The coefficients are derivatives of these
actual integrals, not hypotheses in admissibility. Uniform bounded third
derivatives of b follow from §4 and the smooth endpoint/contact inverse;
the finite sum is summable without deleting any joint or shell neighborhood.
A phase cutoff equal to one near zero makes the cap smooth. The uncut
above-cap part remains a finite-measure positive-volume complement.

For the unchanged kernel the genuine signed response is

```math
\begin{aligned}
 K_4(z)&=(1-9z+8z^2-\tfrac43z^3)e^{-z},&
 \int_0^\infty z^jK_4(z^2)\,dz&=0\quad(j=0,1,2),\\
 \rho^{3/2}P^{\ge\delta}_{\chi,\phi}(\rho)&=O(\rho^{-1/2}).
\end{aligned}\tag{HO9}
```

Subtract the degree-two polynomial on the entire positive w half-line;
its polynomial tails beyond the fixed cap are exponentially small. The
remaining scaled integral is bounded by a constant times rho to power -1/2
multiplied by the finite integral of z cubed |K4(z squared)|. Positive-volume
complements are bounded by a polynomial in rho times exp(-c rho). This proves
HO9 for the **whole** fixed-cutoff long domain. Absolute estimation before
these signed subtractions would not prove it. The displayed subtractions
are proof identities, not new terms in the physical action.

## 7. Restore the complete action and independent target

Choose one positive delta below both §6's threshold and all S30 thresholds
for this metric, region and finite field family. Compact auxiliary tubes,
smooth unit fields, the actual two faces and transverse joint verify S30's
hypotheses. Use the immutable canonical normalization

```math
\begin{aligned}
 a_4&=\beta_4=4/\sqrt6,\\
 \mathcal A_{\rho,4}
 &=a_4\sqrt\rho\,\mu_g(M)
     -\beta_4\rho^{3/2}(P^{\lt\delta}+P^{\ge\delta})\\
 &=S^\delta+L^\delta\longrightarrow\mathcal T_g.
\end{aligned}\tag{HO10}
```

S30 puts the physical point **once** in S-delta and retains its compensating
face/joint flux before identifying T_g. HO9 controls L-delta; equality belongs
to long. If endpoint partitions are used, restore every ordered (i,j) term,
including unequal labels. Their double sum is one at finite density; their
derivatives sum to zero only after summation. For general smooth fields S30
retains integral chi Box(phi), the future antisymmetric field flux and the
weighted joint; none was set to zero chartwise. No artificial cutoff or
partition boundary is a new physical face. The target is always the
independently defined scalar curvature and induced normal/Gram area in HO1.

## 8. Transfer the original-law expectation only now

The smooth manifold is standard Borel and dt dvol_h restricted to M is finite
and atomless. The order tau at least d_h is closed and is the actual ambient
causal order. Its exclusive triple-interval indicator is Borel. HO2 is its
actual volume by containment, not a separate optical model. Null-pair sets
are product-null by time-fibre Fubini; this removes no null collar. Layer
counts are bounded by squared cardinality, integrable under the original
finite Poisson law. Applying the existing measured-order Mecke/count theorem
therefore gives, for each positive density,

```math
\begin{aligned}
 \mathbb E L_k&=\rho^2\int_{x\prec y}
    e^{-\rho V(x,y)}\frac{(\rho V(x,y))^k}{k!}\,d\mu_g(x)d\mu_g(y),\\
 \mathbb E A^{\mathrm{disc}}_{\rho,4}
   &=\mathcal A_{\rho,4}\longrightarrow\mathcal T_g.
\end{aligned}\tag{HO11}
```

This is a written specialization of the checked generic bridge, not a new
compiled limit or an independently defined law. No stochastic-limit exchange,
variance bound or sample-wise result is used.

## 9. Variable curvature, changing causal cones and a true nonempty joint

An explicit non-conformally-flat family, beyond the delivered constant-
curvature/conformal and exact quadratic-wave classes, is

```math
\begin{aligned}
 h_\kappa&=dx^2+a(x)^2dy^2+dz^2,& a(x)&=1+\kappa x^2,\quad\kappa>0,\\
 K_{xy}&=-2\kappa/a(x),& K_{xz}&=K_{yz}=0,\\
 R_g&=-4\kappa/a(x),&
 W_{abcd}W^{abcd}&=\tfrac43K_{xy}^2>0.
\end{aligned}\tag{HO12}
```

The surface curvature is -a''/a. The product curvature operator has eigenvalues
K_xy,0,0, so every sectional curvature is nonpositive. The metric dominates
the Euclidean metric, hence is complete on R3; R3 is simply connected.
Curvature varies with x. The scalar sign follows the G-SS convention: an
ultrastatic unit sphere product has scalar +2, so here scalar is 2K_xy.
The positive Weyl contraction rules out conformal flatness and conformality
to the quadratic plane-wave classes (whose scalar Weyl contractions vanish).
The focusing sphere-circle family has different topology and positive optical
sphere curvature, and is not an application of this comparison argument.

Let s>0, epsilon>0, s+epsilon<1, fixed independently of kappa and density.
With r squared=x squared+y squared+z squared, take

```math
\begin{aligned}
 f&=\varepsilon z,& b&=s(1-r^2),\\
 M&=\{r\lt1,\ f-b/2\lt t\lt f+b/2\},&
 J&=\{r=1,\ t=\varepsilon z\}.
\end{aligned}\tag{HO13}
```

The global envelopes f plus/minus s(1-r squared) positive part/2 have
Euclidean Lipschitz constants at most epsilon+s, hence the same strict bound
relative to d_h. Their epigraph/hypograph intersection proves **ambient closed
interval containment**, not just local spacelikeness. The raw faces are smooth
and spacelike, are achronal, meet only at J, and have independent conormals
since db is nonzero there. No lateral wall or null tip exists. Thus these
are actual nonempty-joint G-SS members for every kappa>0.

Compute the target without an action fit. On the unit sphere put
A=1-epsilon squared and d=x squared+y squared/a squared+z squared. Direct
normal contraction and the induced tangential Gram determinant give

```math
\begin{aligned}
 \coth\theta&=\frac{A+s^2d}{2s\sqrt{Ad+\varepsilon^2z^2}},&
 dA_g&=a\sqrt{Ad+\varepsilon^2z^2}\,dS,\\
 \mu_g(M)&=\frac{8\pi s}{15}(1+\kappa/7),&
 \frac12\int_M R_g\,d\mu_g&=-\frac{16\pi\kappa s}{15},\\
 \mathcal J_g&=\frac\pi s\int_{-1}^1
 \left[Aa(x)+\frac{s^2}2\left(a(x)(1+x^2)
                         +\frac{1-x^2}{a(x)}\right)\right]dx,\\
 \mathcal T_g&=\mathcal J_g-16\pi\kappa s/15.
\end{aligned}\tag{HO14}
```

The volume integral uses the actual time thickness s(1-r squared) and
spatial density a. For bulk the a cancels the denominator in R/2. For area
restrict diag(1,a squared,A) to the Euclidean sphere tangent plane; its
cofactor determinant is a squared times (Ad+epsilon squared z squared).
The two face slopes are epsilon dz plus/minus s(x dx+y dy+z dz), giving
the displayed normal weight. Integrate y squared and z squared azimuthally
at fixed x to get J_g. Angle and area vary; freezing a at an endpoint or
using Euclidean joint area changes the target. The flat kappa-zero limit
recovers 2 pi (A+s squared)/s, but the theorem covers the **whole variable-
curvature family**, and arbitrary Hadamard h, not only this calibration.

## 10. Decisive-estimate scrutiny and honest stopping boundary

| Tempting shortcut | What actually supplies the missing implication |
| --- | --- |
| Unique geodesics imply convergence | HO3 traps all points; HO4–HO6 prove a uniform whole-domain phase; HO7–HO9 separately resolve the endpoint masks |
| The central quadratic lens is the whole interval | The two e-sized caps and the vertical reference generators are included in §4's cone charts; no s=0,L artificial wall is imposed |
| Nonpositive curvature makes the original path action quadratic | False. Only the rescaled **limit** is quadratic; the smooth perturbed two-cone integral with its actual density supplies the remainder |
| Smooth metrics automatically give smooth volumes | False at cut/conjugate/tangent contacts. §4 proves compact containment, reference cone embeddings, apex regularity and intersection transversality before differentiating |
| A logarithm in an absolute majorant is an action counterexample | False. The old estimate did not match the caps. HO6 resolves it in this class; CO requires its separate full matching in a different geometry |
| A smooth phase straightens every boundary | Only the strict-spacelike rank argument proves this here. #169's characteristic contacts violate that argument and remain separate |
| A local/long theorem alone computes the target | S30 at the same fixed cutoff restores short/point/compensating flux, and HO14 computes a target independently |

The first milestone is therefore a complete **written sufficient theorem**,
not merely a publishable central-lens note. The exact remaining implication
for broader coverage is not hidden: absent Hadamard comparison, HO3 need not
hold; absent a positive reference index form, §4's embedded-cone/transverse-
seam argument can fail. None of that implies action failure outside HO-4.
The known sphere success is a reminder that this condition is not necessary.
General curved 2D/3D, broader metric/dimension coverage and unresolved
cut/focusing/true-joint combinations remain #81; null/mixed remains #156/#169.
No unproved jet, cancellation or limit is made an admissibility condition.

`hadamard_optical.py` and its tests are finite diagnostics: actual variable-
curvature geodesic/clock quadrature including both caps, independent reference
phase, noncommuting Jacobi checks, containment algebra, real volume forms,
nonempty-joint target and ordered partition/cutoff accounting. They do not
certify HO-4 or evaluate a general complete action asymptotic. No Lean input
or #164 audited proof/certificate is changed. Validation, exact-head CI,
browser equation inspection and the one bounded feedback pass are recorded
on the scoped PR. Independent mathematical/physical acceptance and any
justified formalization remain #94/#86.

[Shared-definition coordination](https://github.com/q5m-ai/causal-set-emergence/issues/169#issuecomment-6170709226)
was posted before edits. #169 is neither duplicated nor made a dependency.
No agent launch, merge, deployment, issue closure, parent-scope change or
reopening of #151 accompanies this theorem.

Refs #172, #81, #24, #90, #150, #151, #164, #169, #94, #86.
