# Beyond the single cone: a two-tip mixed feasibility package (#134)

**NARROW to one fixed flat 4D two-tip region with a nonplanar floor; GO on
its full-partner lens analysis; STOP any claim that its global limit is proved.**
This is a written geometry/finite-density reduction and proof-task selection,
with symbolic/numerical regressions. It is **not Lean-checked**, an independent
human review, a new taxonomy, or completion of #81/#86/#24. Refs #134.

Integration baseline: `origin/issue-81-general-coverage` already existed and
was pinned at `d41a062aba04552f1db42e9f3d59cb242ec6ed09`. The parent contract
is [#90 §4](general-contract.md#4-nullmixed-taxonomy-and-two-different-singular-limits);
#82 remains superseded. Historical status in those notes is not rewritten.

## 1. Proof inspection and branch selection

The actual [single-cone proof](null-mixed-assembly.md) first proves closed
ambient interval containment in (MA5). It then uses the **stronger** (MA6):
for *each source*, its whole future in the region is, up to null-volume
endpoints, the complete interval from that source to the **same tip**.
Only this permits `causalInterval_kernel_identity` in
[`TimelikeInterval.lean`](../formal/BoundaryDraft/TimelikeInterval.lean) to give
(MA8), cancel the point term, and produce the positive Gaussian in (MA9).
The theorem requires positive density and a timelike pair of endpoints; it
integrates the entire `causalInterval`, not an arbitrary subset or union.
Causal convexity alone does not give (MA6).

The new region below preserves containment but violates (MA6) on an open set
of sources. Each separate cone cap is already a member of #83/#84. Their
**union is not**: it has two distinct future tips and a same-side crease.
Neither Lorentz transport nor a different smooth lower graph turns those two
tips into the single tip required by (MA6). The intersection lens is not a
source-to-tip interval either. Section 4 isolates exactly the missing term.

Why this branch, rather than another calibration:

- A diamond or the checked null-plane-cut diamond is known calibration, not
  the next branch. Adding only a different spacelike floor under one cone
  repeats #84, including its already written nonplanar examples.
- Two overlapping cones with a **flat** common floor are a useful easier
  calibration: reversing time leaves a planar future boundary. For a causal
  displacement, the past-set property makes the overlap depend only on the
  displacement's time component and the spatial union/lens slice volume.
  A planar-cone integration route is then available. We do not advertise that
  simplification as an irreducible new null estimate.
- A fixed **nonplanar** floor removes this particular simplification, while
  the known single-cap terms and exact inclusion–exclusion leave just one
  geometrically specified lens response. Its floor has nonzero second
  fundamental form on an open subset, so no Lorentz change makes it a plane.
  This is substantially narrower than
  arbitrary NN joints, null caustics, curved metrics or arbitrary dimensions.

“New” means outside the written single-cone theorem and listed repository
calibrations, **not priority in the literature**. See §7.

| Actual null/mixed coverage at the pinned base | Regime / verification boundary |
| --- | --- |
| `nullCapRegion T a`, the diamond from $`(-T,0)`$ to zero cut by a null plane, with strict $`0\lt a\lt T`$ | Flat 4D isolated=ambient by checked containment; checked deterministic and expected limit to the algebraic `nullJointArea T a`, equal to $`\pi a(2T-a)`$. Not a general induced-null-joint or crease theorem. See `NullGeometry`, `NullCapLimit`, `ExpectedLimits`. |
| Flat causal diamonds | Known past–future NN calibration, not the new branch; explicit 4D target $`\pi T^2`$ for proper height T. Published dimensional scope/provenance qualified in §7, not inferred from a finite-density series. |
| #83/#84 smooth strict-Lipschitz floor under one flat 4D cone | Written full deterministic induced SN-area theorem and genuine expected limit, one tip, no same-side crease; isolated=ambient by written containment. Weighted generator terms and normalized tip bound proved in writing, not a new Lean instance. |
| Selected two-tip U and intersection lens L | Written finite-density geometry, expectation and exact nonlocal interface only; no global limit. Both tips, same-side crease and triple corner accounted for below. |
| General contract's other null/mixed strata and regimes | Past–future NN versus same-side NN, additional tips/corners, focusing/cut loci, curved/other-dimensional and non-convex restricted intervals remain distinct unresolved branches in §6 under #81/#86. |

## 2. Geometry, order, generators and an independent target

Use Minkowski signature $(+---)$ and Lebesgue four-volume. All lengths below
are in one fixed coordinate unit. Freeze $`a=1/2`$ and $`b=1/10`$, and write
$`x=(z,w)`$ with $`w\in\mathbb R^2`$. Define

```math
\begin{aligned}
c_\pm&=(\pm a,0,0),& v_\pm&=(0,c_\pm),& r_\pm(x)&=|x-c_\pm|,\\
H(x)&=1+b\sin z,&
M_\pm&=\{(t,x):-H(x)\lt t\lt-r_\pm(x)\},\\
U&=M_+\cup M_-,& L&=M_+\cap M_-,&
E_\pm&=M_\pm\setminus M_\mp.
\end{aligned}
\tag{TT1}
```

The selected branch is **U with these fixed parameters**; L is its analytic
reduction, not an independently chosen substitute observable. No limit in b
or a is used. Geometry has no action, jet, cancellation or limit as a field.
The globally smooth H satisfies $`9/10\le H\le11/10`$ and is b-Lipschitz.
Each cap is a translated #84 member, with $`H(c_\pm)>0`$.

**Order and interval regime.** Define $`p\preceq q`$ by
$`q_t-p_t\ge|q_x-p_x|`$, including null pairs, and use isolated restricted
interval counts. The lower epigraph F is a future set because a causal
increment increases $`t+H(x)`$ by at least $`(1-b)\Delta t`$. Each
$`P_\pm=I^-(v_\pm)`$ is a past set, as are its union and intersection.
For $`p\preceq y\preceq q`$ with endpoints in any of M+, M-, U or L,
the first endpoint puts y in F and the second puts it in the relevant past
set. Thus the **entire closed ambient interval** is contained. In particular,
the intrinsic causal order agrees too: its causal straight segment lies in
that interval. This proof, not intrinsic global hyperbolicity alone, equates
the isolated rate with the ambient interval volume. It also implies global
hyperbolicity here: strong causality is inherited and each causal diamond
between interior endpoints is the ambient compact diamond.

All four regions are nonempty open Borel sets. They lie in
$`-11/10\lt t\lt0`$, $`|x|\lt a+11/10`$, so have finite volume and compact
closure. L contains $`(-3/4,0)`$. The min/max graph descriptions and strict
Lipschitz inequalities show that closure is obtained by non-strict
inequalities. At a zero-height endpoint approach from the interior spatial
domain, then between the time endpoints. There is no lateral wall.

### Complete stratum inventory

For U the smooth lower face is $`t=-H(x)`$ over
$`\min(r_+,r_-)\lt H`$. Its future null sheets are $`t=-r_\pm`$ with
$`r_\pm\lt H`$ and $`\pm z>0`$, excluding their tips. Their SN joints
$`J^U_\pm`$ have $`r_\pm=H`$, $`\pm z>0`$. The remaining strata are:

- **Two actual tips** v+ and v-. Their neighborhoods are estimated in §5.
- **Same-future-side null crease C:** $`z=0`$,
  $`t=-s(w)`$, $`s(w)=\sqrt{a^2+|w|^2}`$, $`|w|\lt\sqrt{1-a^2}`$.
  This is a smooth spacelike disk, not a past–future NN joint. Its center
  $`(-a,0)`$ is a regular point of the disk, not a third tip.
- **Triple corner Gamma:** $`z=0`$, $`t=-1`$,
  $`|w|=\sqrt{1-a^2}`$. It is the boundary of C and both SN pieces, a
  spacelike circle of length $`2\pi\sqrt{1-a^2}`$.

L has the complementary null sheets and SN pieces $`J^L_\pm`$ with
$`\pm z\lt0`$, the same C and Gamma, and **no tips**: neither v+ nor v-
is in its closure. In both regions all lower-face points away from the SN
pieces and Gamma are smooth. There are no other corners, components of the
frontier, generator caustics or transition strata. All boundary graphs have
zero four-volume; this is used for finite-density endpoint conventions,
**not** to discard density-normalized neighborhoods of C or Gamma.

To check regularity without a picture, write $`x=c_i+r\omega`$,
$`\mu=\omega_1`$. The equation $`r=1+b\sin(c_{i,1}+r\mu)`$ has a unique
smooth root $`R_i(\mu)\in[9/10,11/10]`$, since the derivative of its left
side minus right side is at least $`1-b`$. At that root the axial coordinate
$`c_{i,1}+R_i(\mu)\mu`$ has derivative
$`R_i/(1-b\mu\cos(c_{i,1}+R_i\mu))>0`$. Thus the cuts are exactly
$`\mu=-a`$ for the plus cap and $`\mu=a`$ for the minus cap; at either
cut R=1. These transverse cuts prove regularity at Gamma as well.

### Affine markings, screen metrics and target

On sheet i use the future affine null vector
$`k_i=(1,-\omega)`$ along $`(-r,c_i+r\omega)`$; the future affine parameter
is -r. On the floor use
$`n=(1,-b\cos z,0,0)/\sqrt{1-b^2\cos^2z}`$. At the SN pieces,
$`g(n,k_i)=(1-b\mu\cos z)/\sqrt{1-b^2\cos^2z}>0`$.
On C the two marked rays satisfy $`g(k_+,k_-)=2a^2/s^2>0`$; their
same-side meeting is not silently assigned the regular past–future NN weight.

Cone-screen area at radius r is $`r^2d\omega`$. At a joint parametrized by
$`(-R_i,c_i+R_i\omega)`$, radial derivative terms cancel in the Lorentzian
Gram matrix, giving $`R_i^2d\omega^2`$. On C the positive induced metric is
$`I-ww^\mathsf T/s^2`$, determinant $`a^2/s^2`$, hence
$`dA_C=(a/s)\,d^2w`$ and $`|C|_g=2\pi a(1-a)`$.
None of these measures is defined through an action limit.

Define the **candidate regular-joint targets**, with zero curvature bulk,

```math
\begin{aligned}
S_i&=2\pi\int_{-1}^{1}R_i(\mu)^2\,d\mu,\\
J_U&=2\pi\left[\int_{-a}^{1}R_+(\mu)^2\,d\mu
                 +\int_{-1}^{a}R_-(\mu)^2\,d\mu\right],\\
J_L&=2\pi\left[\int_{-1}^{-a}R_+(\mu)^2\,d\mu
                 +\int_a^1R_-(\mu)^2\,d\mu\right],&
J_U+J_L&=S_++S_-.
\end{aligned}
\tag{TT2}
```

These integrals are the induced areas of the SN pieces, with unit candidate
weight. Gamma has zero measure for these **geometric area integrals**. This
does not say its normalized action contribution vanishes. **Whether J_U is
the full action target is unresolved.** In particular no zero coefficient for
C or Gamma is an assumption. A surviving term would require a corrected target
on this stratified branch, not deletion of the example.

Affine rescaling $`k_i\mapsto\alpha_i(\omega)k_i`$ corresponds to
$`r=\alpha_i A`$: $`r^2=\alpha_i^2 A^2`$, including any generator endpoint
on C rather than the floor. Joint and crease area are unchanged. The logs
of the SN/NN scalar products would acquire respectively one/two additive
log-scales. We introduce **no logarithmic corner action** or preferred scale.
Generators of U run from a floor or crease endpoint to a tip; those of L run
from the floor to C. All such endpoints must be retained in an integration
by parts. These markings are independent of the discrete observable.

## 3. Unchanged action and genuine finite-density expectation

For any of the four regions V, use the actual finite Poisson law of intensity
$`\rho\,dp|_V`$: Poisson cardinality with mean $`\rho|V|`$, followed by
independent positions distributed as normalized restricted volume. Count
ordered distinct causal pairs with k **other** points in the closed interval.
Set $`\sigma(p,q)=(q_t-p_t)^2-|q_x-p_x|^2`$ and

```math
\begin{aligned}
c&=\pi/24,& C_4&=4/\sqrt6,&
K(z)&=(1-9z+8z^2-4z^3/3)e^{-z},\\
A^{\mathrm{disc}}_\rho(C)
 &=\frac{C_4}{\sqrt\rho}(N-L_0+9L_1-16L_2+8L_3),\\
\mathcal A_\rho(V)[\phi]
 &=C_4\sqrt\rho\left[\int_V\phi(p)\,dp
 -\rho\int_V\phi(p)\int_{V\cap J^+(p)}K(c\rho\sigma(p,q)^2)\,dq\,dp\right].
\end{aligned}
\tag{TT3}
```

Weights are bounded measurable **first-endpoint** weights. Unweighted means
phi=1. The observable is unsmeared, with no subtraction or extra boundary term.
All finite-density integrals are absolutely integrable by compact domination;
this is not a uniform-in-density bound.

Section 2 proves precisely `BoundedCausalRegion`'s three fields: measurable,
bounded, closed-interval causally convex. Endpoint removal is volume-null,
so the actual restricted interval rate is $`c\rho\sigma^2`$ for timelike
pairs. Null-related pairs and the diagonal are product-volume-null by Fubini,
but remain in the discrete order. Campbell–Mecke gives, separately for each k,

```math
\begin{aligned}
\mathbb E[L_k]&=\rho^2\int_V\int_{V\cap J^+(p)}
 e^{-c\rho\sigma^2}\frac{(c\rho\sigma^2)^k}{k!}\,dq\,dp,\\
\mathbb E[A^{\mathrm{disc}}_\rho]&=\mathcal A_\rho(V)[1].
\end{aligned}
\tag{TT4}
```

The discrete bound $`|A^{\mathrm{disc}}_\rho|\le
C_4\rho^{-1/2}[N+16N(N-1)]`$ and finite Poisson factorial moments justify
integrability. This is a **written specialization with hypotheses proved**,
not an expectation defined to equal a numerical integral and not an exchange
with a sample-wise limit. The existing checked counterparts are
`FiniteSprinkling.interval_rate` in
[`ExpectationGeometry.lean`](../formal/BoundaryDraft/ExpectationGeometry.lean)
and `BoundedCausalRegion.expectedBDGAction_eq` in
[`ExpectationBridge.lean`](../formal/BoundaryDraft/ExpectationBridge.lean).
There is no new compiled U or L instance and no new expected **limit** here.

## 4. Exact full-partner reduction, including the irreducible lens

For a source in E_i, its future partners in U are exactly those of M_i,
up to the cone boundary. A causal successor in the other past cone would put
the source there too, a contradiction. For a source p in L put
$`D_i(p)=I(p,v_i)`$. The future fibres in U and L are respectively their
**union and intersection**, up to null endpoints. Define

```math
\begin{aligned}
e_i(p)&=e^{-c\rho\sigma(p,v_i)^2},&
Q_\rho(p)&=\rho\int_{D_+(p)\cap D_-(p)}K(c\rho\sigma(p,q)^2)\,dq,\\
1-\rho\int_{U\cap J^+(p)}K(c\rho\sigma^2)\,dq
 &=e_+(p)+e_-(p)-1+Q_\rho(p)\qquad(p\in L),\\
\mathcal A_\rho(U)[\phi]
 &=\mathcal A_\rho(M_+)[\phi]+\mathcal A_\rho(M_-)[\phi]
       -\mathcal A_\rho(L)[\phi],\\
\mathcal A_\rho(L)[\phi]
 &=C_4\sqrt\rho\int_L\phi(p)(1-Q_\rho(p))\,dp.
\end{aligned}
\tag{TT5}
```

**Proof of the valuation identity, not assumed bilocal additivity.** Points
in E+ and E- cannot be causally related in either direction: the later point's
past cone would contain the earlier point. Every other causal pair is in one
or both caps, with the doubly counted pairs precisely those of L. Apply this
indicator identity to the signed pair integral and ordinary inclusion–exclusion
to the point integral. Closed containment also ensures that for endpoints in
a cap or L, *all intermediate points of any configuration in U* stay there.
Thus the same identity holds for discrete actions of restrictions of **one**
finite configuration in U. It is not an assertion about independently drawn
configurations or about arbitrary component/chart partitions.

All pairs from L to either E_i are retained in the M_i terms. The subtraction
contains every L-to-L pair once, not a locally regulated crease coefficient.
The #84 Gaussian reductions apply only to the two cap terms. They do not
replace $`1-Q_\rho`$ by a Gaussian or imply positivity of the lens action.

### A strict witness to the failure of the single-tip step

Take $`p=(-u,0)`$ with $`a\lt u\lt1`$. Both tips are in its chronological
future. Points $`q=(-\epsilon,c_-)`$ with
$`0\lt\epsilon\lt\min(u-a,a)`$, and an open neighborhood of them, are
future partners in U but not in $`D_+(p)`$. The analogous plus-tip neighborhood
is in $`D_+(p)`$ but outside the intersection lens. Direct spatial integration
(the formula below at zero density) gives

```math
\begin{aligned}
|D_+(p)\cap D_-(p)|&=\frac\pi{24u}(u-a)^4(u+2a),\\
|D_+(p)|-|D_+(p)\cap D_-(p)|
 &=\frac{\pi a(u-a)^2(u^2+2au-a^2)}{12u}>0.
\end{aligned}
\tag{TT6}
```

On a fixed compact partner domain K converges uniformly to 1 as density goes
to zero. More explicitly, if $`c\rho(u^2-a^2)^2\le1/16`$, its polynomial
is at least $`1-9/16-4/(3\cdot16^3)>0`$ throughout both intervals.
Thus the omitted integral is genuinely nonzero at these positive densities.
This refutes the **exact single-tip replacement**, not the conjectured
high-density target. Neither low-density positivity nor a failed absolute
estimate is evidence of a high-density complete-action counterexample.

### Actual nonlocal coordinates for the follow-up

No unknown interval-volume law remains in this flat branch. The remaining
integral is nevertheless over all lens partners, including macroscopic
nearly-null separations. Use axial symmetry to put
$`p=(-u,z,R,0)`$ and $`q=(-v,\zeta,r\cos\theta,r\sin\theta)`$. Then

```math
\begin{aligned}
a&\lt u\lt1+b,& |z|&\lt u-a,&
0&\lt R\lt\sqrt{u^2-(|z|+a)^2},&u&\lt H(z),\\
a&\lt v\lt u,& |\zeta|&\lt v-a,&
0&\lt r\lt\sqrt{v^2-(|\zeta|+a)^2},&0&\le\theta\lt2\pi,\\
\Delta&=(u-v)^2-(\zeta-z)^2-R^2-r^2+2Rr\cos\theta,\\
Q_\rho(p)&=\rho\int_a^u\int_{-(v-a)}^{v-a}
 \int_0^{\sqrt{v^2-(|\zeta|+a)^2}}\int_0^{2\pi}
 \mathbf1_{\Delta\ge0}K(c\rho\Delta^2)\,r\,d\theta\,dr\,d\zeta\,dv,\\
\mathcal A_\rho(L)&=C_4\sqrt\rho\int
 \mathbf1_{u\lt H(z)}(1-Q_\rho(p))\,2\pi R\,dR\,dz\,du.
\end{aligned}
\tag{TT7}
```

The last integral uses the first line's u,z,R bounds. The source azimuth is
integrated to $`2\pi`$; partner azimuth is not deleted. No floor indicator
is missing for q: future-set monotonicity from p proves it automatically.
This is a fixed, finite-dimensional **actual** interface, not a desired jet.
It makes clear why the flat-floor calibration does not settle the selected
branch: the remaining source cutoff $`u\lt1+b\sin z`$ is nonconstant.

For central sources only, theta integrates out. With $`y=r^2`$, the simpler
threefold diagnostic integral for $`Q_\rho/\rho`$ is

```math
\begin{aligned}
2\pi\int_a^u\int_0^{\min(v-a,u-v)}\int_0^{Y(v,\zeta)}
 K\!\left(c\rho[(u-v)^2-\zeta^2-y]^2\right)\,dy\,d\zeta\,dv,\\
Y(v,\zeta)=\min\{v^2-(\zeta+a)^2,(u-v)^2-\zeta^2\}.
\end{aligned}
\tag{TT8}
```

Split v at $`v_0=(u^2+a^2)/(2u)`$ and $`v_1=(u+a)/2`$, and the middle
zeta fibre at $`(2uv-u^2-a^2)/(2a)`$. All moving boundaries then have explicit
polynomial formulas. This derives (TT6) and enables independent positive-layer
quadrature; a central source alone is **not** the full source integral (TT7).

## 5. Tips, artificial partitions and the normalized stopping point

**A genuine tip estimate.** In the tip neighborhood
$`B_{i,\delta}=\{-\delta\lt t\lt-r_i,\ r_i\lt\delta\}`$ take
$`0\lt\delta<a`$. It lies above the floor since H is at least 9/10, and
$`r_j\ge2a-r_i>\delta>-t`$, so it is entirely in E_i. Its full-partner
response is exactly the single-cap Gaussian. The coarea Jacobian bound
$`r_i^2/(2\sqrt{r_i^2+s})\le r_i/2`$ and Gaussian mass four give
$`|\mathcal A_\rho(U)[\phi\mathbf1_{B_{i,\delta}}]|
\le4\pi\|\phi\|_\infty\delta^2`$ at **every positive density**.
These neighborhoods contain actual spacetime neighborhoods of the tips in U.
No analogous normalized C/Gamma estimate has been proved here.

**Source and partner partitions.** For any finite bounded source partition
$`\sum_j\phi_j=1`$, (TT3) sums exactly to the full action, with all partners
still in V. For a measurable partner cutoff $`0\le\chi\le1`$, write

```math
\begin{aligned}
S_\rho^V[\phi;\chi]&=C_4\sqrt\rho\left[\int_V\phi
 -\rho\int_V\int_{V\cap J^+(p)}\phi(p)\chi(p,q)K(c\rho\sigma^2)\,dq\,dp\right],\\
N_\rho^V[\phi;\chi]&=-C_4\rho^{3/2}\int_V\int_{V\cap J^+(p)}
 \phi(p)(1-\chi(p,q))K(c\rho\sigma^2)\,dq\,dp,\\
S_\rho^V+N_\rho^V&=\mathcal A_\rho(V)[\phi].
\end{aligned}
\tag{TT9}
```

No separate vanishing of N is asserted. A further finite partner partition
keeps **every ordered pair of charts**, not just matching chart indices.
Only E+-to-E- pairs vanish, by the particular geometric proof in §4.

For a smooth source weight on a neighborhood of the closure, the known cap
limits retain the generator terms of #83 (NM8), now translated:

```math
\begin{aligned}
\lim_{\rho\to\infty}\mathcal A_\rho(M_i)[\phi]
 =\int_{S^2}R_i^2\phi(-R_i,c_i+R_i\omega)\,d\omega
 -\int_{S^2}\int_0^{R_i}r^2
   (-\partial_t+\omega\cdot\nabla_x)\phi(-r,c_i+r\omega)\,dr\,d\omega.
\end{aligned}
\tag{TT10}
```

Their derivatives cancel only in a complete source partition. A radial split
also carries both signed artificial endpoints. Restricting to exposed angular
sectors changes generator endpoints to C; those endpoint terms cannot be
thrown away. The lens term in (TT5) remains until its actual response is
proved; (TT10) is not a local-to-global argument for it.

Let $`e_i^\rho=\mathcal A_\rho(M_i)-S_i`$ and define the actual residuals
$`R_V^\rho=\mathcal A_\rho(V)-J_V`$ for V=U,L. Independently of any limit,

```math
\begin{aligned}
R_U^\rho&=e_+^\rho+e_-^\rho-R_L^\rho,&
 e_+^\rho&\longrightarrow0,& e_-^\rho&\longrightarrow0.
\end{aligned}
\tag{TT11}
```

Hence the selected **deterministic target for U is equivalent to the target
for L**, not proved by the two cap theorems. If the full lens has an additional
finite term, the union has its negative relative to these targets. This is a
falsifiable full-action test, not a fitted local coefficient.

**Normalized boundary rule for a future proof.** It may either evaluate the
complete (TT7), requiring no deletion of boundary neighborhoods, or introduce
fixed cutoffs and retain their complements and (TT9) throughout. If it wants
to discard a shrinking C/Gamma neighborhood, it must first prove a bound on
its *all-partner normalized response*, for example a vanishing iterated
limsup as density tends to infinity and then the fixed neighborhood width
tends to zero. If that bound fails, keep and identify the response instead.
Zero four-volume of C/Gamma is not such a bound. No shrinking-cutoff uniformity
or absolute-value estimate of the raw kernel is imposed as a necessary theorem.

**Limit order:** only density tends to infinity in the proposed theorem.
The floor, tip separation and all charts remain fixed. The optional tip
removal uses the bound above after density (or its justified uniform bound).
There is no interchange with b tending to zero, merging tips, a face becoming
null, or a small positive spacelike angle. Here faces are null from the start.
Coinciding null rays at a=0 and the SS zero-rapidity singularity are distinct
geometric degenerations, neither analyzed by this package.

## 6. Bounded follow-up contracts and genuine dependencies

These are proposed task contracts, **not newly proved limit declarations or
new GitHub issue numbers**. #81 owns scheduling; #86 owns unresolved coverage
and review. No serialization through #82 or repeat of #90 is required.

| Contract | Actual input and dependency | Required output / stop rule |
| --- | --- | --- |
| TT-A: lens analytic producer (next proof task) | Exactly (TT1), (TT3), (TT7); the signed 4D kernel. #83/#84 needed only for equivalence with U, not as a substitute lens estimate | Prove the complete normalized L limit equals the independent J_L, or derive a nonzero surviving/divergent **complete-action** term. Include moving floor/crease/Gamma contacts and all long partners; prove any claimed jets from geometry. A fixed-cutoff short/long route is optional, with (TT9) and all boundary terms retained. A failed sufficient estimate returns NARROW/STOP, not a counterexample. |
| TT-B: two-tip global and expected assembly | TT-A's actual deterministic result, #84's two cap limits, (TT2)/(TT5), and §3's genuine finite-density Poisson equality | Prove the deterministic U target (or a source-backed corrected target) by (TT11), then the expected limit. Inventory every stratum and exact quantifiers. No sample-wise convergence or rate. Cannot complete before TT-A. |
| TT-F: formal port, if checked coverage is requested | Stable written geometry, finite-density identities and actual TT-A/TT-B proof; existing interval and probability APIs | Encode U/L, screen measures, all containment and analytic producers, then instantiate the expectation bridge. Geometry/finite-density port can start before TT-A, but no limit can. Coordinate ownership before touching shared Lean/probability/checker files; after the last Lean-affecting change run the full integrated local audit. |
| TT-P: provenance and independent review | §7's passage receipts and unresolved primary text, plus the selected proof when available | Obtain Chevalier text or document continuing access limits, expert-assisted comparison with multi-tip/crease work, and attributable human mathematical/physical review. No priority claim pending this work. Analytic work need not wait for a missing all-diamond citation. |

The minimal dependency chain is TT-A → TT-B; TT-F's limit port depends on the
actual analytic proof, not issue closure. TT-P is independent provenance/review
work, not an artificial analytic prerequisite. **This reconnaissance can finish
while TT-A and TT-B remain open.** No global two-tip/null theorem is completed
by publishing this selection.

Unsupported branches still retained under #81/#86: arbitrary past–future NN
joints; more tips and same-side creases; general extra corners; null focusing
and cut loci; curved null faces and general atlases; other dimensions;
noncompact tails; degenerate rays/angles and density-dependent geometry.
For curved extensions, separately missing are actual metric interval volume
and order/containment, induced curved screen geometry, signed nonlocal
estimates, and formal instances. The controlled polynomial conformal
spacelike assembly is not a null theorem. For dimensional extensions the
checked dimension-indexed finite-density bridge does not supply a new
multi-tip kernel response, critical-order remainder or joint-measure port.
Intrinsic-only/non-convex regions must keep their genuinely restricted rates;
none inherits this flat ambient formula automatically.

## 7. Reviewed literature and unresolved provenance

Bounded reading on **2026-10-05**, separate from independent peer review. The
following pinned primary passages were actually retrieved and re-read for
this selection; their downloaded HTML SHA-256 values match the receipts in
[the #90 literature audit](general-contract-literature.md#4-reproducible-reading-evidence).
That older audit's wider search is inherited evidence, not a fresh exhaustive
search here. No article body is committed.

| Source / reviewed passages | Relevance and limits |
| --- | --- |
| [DLL 2501.00139v2](https://arxiv.org/html/2501.00139v2), §§2.3–2.6, (7)–(14), Appendix B (85)–(88), bibliography [25] | Actual mean, isolated/embedded distinction and bilocal cross terms; Appendix B explicitly forbids summing disjoint region actions without cross terms. Our special valuation has its own geometric proof. Conjecture (11), not a proved multi-tip theorem. Their “any dimension” diamond attribution does not resolve the primary-source discrepancy below. |
| [Dowker 2007.13206v2](https://arxiv.org/html/2007.13206v2), §2.1, §4 (4.4)–(4.14), §5 | Complete source-to-tip integration and the flat Gaussian are prior work. Curved terms are retained only to first order; omitted terms explicitly require bounds. Not a fixed-curvature null/mixed theorem or an estimate for our intersecting future intervals. |
| [BDJS 1502.05388v2](https://arxiv.org/html/1502.05388v2), §4 (64)–(76) | 4D diamond is established calibration. The inspected general-d evaluation explicitly says dimensions 2–16; no newly inspected all-integer proof here. |
| [Machet–Wang 2007.13192v2](https://arxiv.org/html/2007.13192v2), §3 (46)–(48), §3.2 opening, §4 | Confirms the 2–16 attribution; curved small diamonds are first-order curvature calculations (explicit 3,4,5 cases). Null-plane-truncated diamond already proposed as future work. Neither that idea nor diamond calibration is a novelty claim here. |
| Chevalier, *The Discrete Causal Action and Holes in Spacetime* (2023) | **Primary text not obtained/reviewed.** DLL [25] still supplies only author/title/year; its attribution of the overlap method was read. No inference that the thesis lacks a multi-tip/crease result. Access and exact coverage remain unresolved under #86. |
| Sorkin 1908.10022v1 and later work listed by #90 | **Not re-read in this package.** Inherited passage audit only. Our affine-rescaling algebra is independent; continuum logarithmic corner conventions are not imported into BDG. |

No retrieved passage proves the selected nonplanar two-tip global theorem;
this bounded statement about the inspected passages is **not evidence of
novelty**. No new broad search or expert-assisted review was completed. The
all-dimension diamond provenance and Chevalier access questions remain open.

## 8. Executable evidence, acceptance map and validation boundary

[`two_tip_null.py`](../two_tip_null.py) supplies independent geometric radii,
SN areas, lens volume, and positive Poisson-layer integrals for **central
sources only** using (TT8). It is not a full-action or high-density solver.
[`test_two_tip_null.py`](../test_two_tip_null.py) checks the moving-domain
volume symbolically; screen/normal algebra; geometric witnesses; actual finite
configuration inclusion–exclusion; and negative controls for lost chart
partners, omitted overlap and wrong layer factorials. Moderate-density
quadrature refinement checks the signed response against separately integrated
layers. These are regressions, not certified integration errors or proofs of
quantified asymptotics. Flat-floor calibration is explicitly not the selected
new branch.

| #134 acceptance | Delivered evidence / remaining distinction |
| --- | --- |
| Actual inventory, known cases, unresolved provenance | §1 proof audit and §7 primary-passage ledger; #90 taxonomy reused, not redone; #82 not reopened |
| Bounded new geometry and independent data | §2 fixed nonplanar two-tip U, complete strata, order, markings, screen/area and candidate target; no presumed zero crease coefficient |
| Actual finite-density/nonlocal interface | (TT5)–(TT9), strict missing-domain witness (TT6), all source/partner pairs and cutoff terms; normalized tip bound, no deletion of C/Gamma |
| Interval/expectation instances and wider gaps | §2 containment, §3 written specialization of actual APIs; no new compiled instances; §6 separates curved/dimensional geometry, analytics and ports |
| Go/narrow/stop and bounded dependencies | §6 TT-A → TT-B and independent TT-P; optional TT-F requires shared ownership and full audit; selected global theorem still open |

Run from the repository root with the unchanged `requirements.txt`:

```sh
.venv/bin/python -m unittest -v test_two_tip_null
.venv/bin/python two_tip_null.py
.venv/bin/python check_symbolic.py
.venv/bin/python -m unittest -v
.venv/bin/python reproduce.py
python3 check_markdown.py
python3 -m unittest -v test_check_markdown
```

**Local receipt (2026-10-05):** 9 focused tests passed; the full Python suite
passed **285 tests** (460.477 seconds); `check_symbolic.py`, `reproduce.py` and
`two_tip_null.py` passed; Markdown lint checked 58 documents with zero problems,
and its 20 regression tests passed. An earlier full-suite command hit a
240-second harness timeout; the complete 900-second-budget rerun above passed.
This is lightweight Python/documentation validation, not a Lean audit.

**Exact scope:** written geometry/finite-density proofs and conditional
follow-up contracts; Python/SymPy numerical/algebraic regressions. No Lean
source, checker, dependency or build configuration changes, so no new Lean
audit is run or claimed. Existing theorem signatures were read, not rechecked.
GitHub rendering and CI are separate validation checks. Independent human
mathematical/physical review is **outstanding** under #94/#86. No merge,
deployment, agent launch, epic closure or sample-wise claim is part of this
package.
