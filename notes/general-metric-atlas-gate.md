# General-metric and atlas feasibility gate (#133)

**GO on a bounded nonpolynomial long producer and a thin quotient-slab
reduction; NARROW the next short/globalization packages; STOP promotion to a
general-metric theorem.** This is written analysis with executable regressions,
not new Lean verification or independent human mathematical review.

Pinned integration input:
`d41a062aba04552f1db42e9f3d59cb242ec6ed09` on
`origin/issue-81-general-coverage`, including merged #76 / PR #135.
The task branch is `issue-133-general-metric-gate`; its PR targets that
integration branch, **not main**, with `Refs #133`. Integration there does not
automatically close #133. Nothing here closes #81/#86/#24.

## 1. Actual source boundary, not issue-state inference

| Inspected input at the pin | What its producers actually supply | What cannot be reused without proof |
| --- | --- | --- |
| [#76 assembly](curved-assembly.md), CA6–CA9 | Written complete deterministic/expected theorem on original C³ combined-budget two-graphs, exactly `q(t)=1+t^2`; a common fixed cutoff; whole bulk, compensating joint flux and every ordered partition pair | Arbitrary positive conformal factors, a different metric/order, or manifold atlases |
| [#74 full/face/corner handoff](curved-boundary-collar.md), H3–H18; [interior producer](curved-interior-short.md), S8–S14 | Actual interval identity, derivative-controlled signed remainders, moving diagonal, whole collar bulk and single-face flux | A coordinate Taylor remainder alone, boundary cones replaced by full cones, or the assertion that any smooth metric has these symbol bounds |
| [#75 corner producer](curved-joint-corner.md), J7–J19 | Derived ratio-phase inverse and moving height roots; signed actual-minus-tangent estimate; induced area/positive-normal angle; restores the generally nonzero face flux | Conformal angle invariance as a proof of a joint action limit; deletion of chart derivatives or auxiliary partners |
| [#117 long producer](curved-contact-long.md), A3–A14 | Time/contact-averaged quadratic right jet, both moving-boundary terms and integrable remaining-parameter domination | Raw first-spacetime-endpoint domination: [the rejected route](curved-remainders.md) remains obstructed |
| [#93 API](../formal/CONFORMAL_ACTION.md); `ConformalAction.lean`, `ConformalGeometry.lean`, `FiniteMeasureBDG.lean` | Compiled positive-density equality for controlled conformal volume on the existing 4D Minkowski coordinate **order**, not a flat interval-volume substitution | `FiniteMeasureBDG` is finite-**measure**, not arbitrary-**order**: its type is `Measure Spacetime` and it uses `causalFuture`/`causalIntervalInterior` |
| [#97 class E](../formal/INDEPENDENT_LIMIT.md); `IndependentFaceLimit.lean` | Compiled `twoFaceLimit`, `expectedBDGAction_limit`: flat 4D global two-graphs with independent strict envelopes and actual short/long producers | Curvature or topology beyond a global graph presentation; its atlas is a joint/height atlas within that presentation |
| [#80](../formal/PILOT3_LIMIT.md); `Pilot3Limit.lean` | Compiled `SmoothPilot3.action_limit` and `.expectedAction_limit`: flat **3D**, smooth combined-budget geometry | A 4D curved estimate, arbitrary dimension, or a global manifold atlas theorem |
| [#90 §§1–3, 7](general-contract.md) | Independent smooth precompact G-SS candidate, allowing compact-Cauchy slabs with empty joint and interior conjugate points | A proved general theorem, or intrinsic global hyperbolicity in place of ambient interval containment |

The compiled declarations above are existing source results with their recorded
upstream audits. This pass inspects, but does **not** recompile or independently
audit them. In particular #76's application of #93 is a written instantiation;
it is not a compiled curved limit. Historical status passages are not rewritten.

### Coordination and ownership

Preflight read #131/#132/#134 and posted the
[#133 boundary](https://github.com/q5m-ai/causal-set-emergence/issues/133#issuecomment-5995175610)
to each: [#131](https://github.com/q5m-ai/causal-set-emergence/issues/131#issuecomment-5995175945),
[#132](https://github.com/q5m-ai/causal-set-emergence/issues/132#issuecomment-5995176453),
[#134](https://github.com/q5m-ai/causal-set-emergence/issues/134#issuecomment-5995176820).
There were no competing comments or open implementation PRs at preflight.
This is notification and an ownership boundary, not claimed peer approval.
No shared definitions are modified. #131 keeps 2D, #132 keeps 5D/6D, #134 keeps
null/mixed **boundary** strata. Interior null focusing below is not a null
boundary. One future measured-order port owns any shared extraction; consumers
must coordinate before editing those definitions, not fork the observable.

## 2. Frozen observable, geometric core and sufficient analytic interface

All tests are smooth, nonempty, fixed, precompact 4D G-SS regions. Future means
increasing time. Use the unchanged minimal-layer coefficients, signature
(+---) and **#90's curvature sign**, opposite the example calculator in #93.
For the specified ambient order, count ordered distinct related pairs and
remove only their two endpoints from the closed interval:

```math
\begin{aligned}
V_M(x,y)&=\mu_g\bigl(M\cap(I[x,y]\setminus\{x,y\})\bigr),\qquad
K(z)=(1-9z+8z^2-\tfrac43z^3)e^{-z},\\
A_g(\rho,M)&=\frac4{\sqrt6}\sqrt\rho\left[\mu_g(M)-\rho
 \int_M\int_{M\cap J^+(x)}K(\rho V_M(x,y))\,d\mu_g(y)d\mu_g(x)\right],\\
\mathcal T_g&=\frac12\int_M R_g\,d\mu_g+
 \int_J\frac{g(n_-,n_+)}{\sqrt{g(n_-,n_+)^2-1}}\,dA_g.
\end{aligned}
```

This is notation for #90's observable, not a new production API. Define the
bulk by Levi-Civita contraction, joint measure by minus the induced metric,
and the angle by the two future unit normals, **before** any limit. Empty
joint means zero joint integral, not a zero-angle limit. All constants, collar
widths and positive margins are fixed before density varies.

For branch C below these are exactly #93's `conformalAction`, volume and law.
For A/F the identical finite-order formula uses the explicitly specified
manifold order; that **instance is not implemented** by #93's coordinate API.
The reusable compiled `FinitePoisson.law`, count law, two-point Mecke and
`PoissonIntegration` factorial moments are generic in the measurable space.
On the manifolds below, finite volume and atomlessness hold; the distance
relation is closed, its joint interval indicator is Borel, and integration of
that indicator gives measurable bounded interval volume. The finite signed
layer sum is integrable because each layer count is at most the square of
cardinality. Mecke therefore gives, **in writing**, the usual exact expectation
identity with density squared in the pair term and
`4/(sqrt(6)*sqrt(rho)) * [N-N0+9*N1-16*N2+8*N3]` in the discrete action.
Null relations remain in the order. This argument specifies a legitimate
future instance; it does not pretend `discreteBDGAction` already accepts an
arbitrary manifold/order or redefine expectation to be the continuum formula.

**Finite-partition lemma (written).** For bounded smooth source/target weights
summing to one, the complete ordered double sum of their pair integrals equals
the original pair integral at every positive density. The point term has weight
`sum_i,j chi_i(x)*phi_j(x)=1`, not one point allocation per chart. Proof: expand
the finite sums under absolutely finite integrals. This uses no local chart
containing both endpoints. It is false with only matching chart indices.

**Signed-phase lemma (written sufficient interface).** At a fixed long cutoff,
suppose an *actual* endpoint-weighted pair integral, after all necessary contact
averaging, has near-zero phase density B with phase `V=c*w^2`, `c=pi/24`, and

```math
\begin{aligned}
B(w)&=b_0+b_1w+b_2w^2+w^2e(w),\\
e(w)&\longrightarrow0,\qquad |e(w)|\le C,\qquad 0\lt w\le e_0,\\
\int_0^\infty z^jK(z^2)\,dz&=0\quad(j=0,1,2).
\end{aligned}
```

Assume the complementary pair domain has interval volume bounded positively
away from zero and finite weighted mass. Then its exponentially small kernel
tail and the displayed jet imply `rho^(3/2)*P_long -> 0`. Subtract the polynomial
using the three whole-half-line moments, rescale `z=sqrt(c*rho)*w`, and dominate
the remainder by a constant times `z^2*abs(K(z^2))`. Truncated-polynomial tails
are exponentially small too. An integrable parameter majorant before the final
averaging gives the same result. These are **analytic lemma hypotheses**, never
admissibility fields. A metric expansion does not supply B; §3 derives it for
C, §4 bypasses it by an exact reduction, and §5 identifies its failure at a
particular unaveraged focusing fibre.

## 3. C — nonpolynomial conformal branch

### Geometry, targets and genuine exclusion

In ambient `t<1` take the conformal Minkowski patch and the original smooth
ellipsoid member

```math
\begin{aligned}
g&=(1-t)^{-2}(dt^2-|dz|^2),&q(t)&=(1-t)^{-4},&R_g&=12,\\
h(z)&=\tfrac14(1-z_1^2-z_2^2/4-z_3^2/9),&f&=\tfrac18,\\
M&=\{(t,z):h(z)>0,\ f-h(z)\lt t\lt f\},&
d\mu_g&=q(t)\,dt\,dz.
\end{aligned}
```

The ambient patch is globally hyperbolic: its cones are Minkowski's and closed
intervals lie in compact finite-time diamonds below `t=1`. The old combined
budget is 1/2, its joint is regular, and all germs are smooth. The time closure
of M is `[-1/8,1/8]`; every closed ambient interval between its endpoints is
contained in M by the original envelope argument. Thus intrinsic and restricted
orders agree here **by containment**, not by global hyperbolicity alone.
The two compact spacelike faces and their ellipsoidal joint exhaust the frontier.

On `abs(t)<1/2`, Omega lies between 2/3 and 2 and is smooth. Extend it measurably
by one outside that slab to instantiate #93; extension independence and
containment make this the same action and intervals on M. The curvature
calculation is independent: `6*Omega''/Omega^3=12` in #90's convention, also
checked by direct connection contraction. The targets are

```math
\begin{aligned}
\mathcal B_C&=48\pi\int_{-1/8}^{1/8}
 \frac{(1/2+4t)^{3/2}}{(1-t)^4}\,dt>0,\\
\mathcal I_C&=48\pi(1-1/8)^{-2}=\frac{3072\pi}{49}.
\end{aligned}
```

The spatial slice volume is `8*pi*(1/2+4*t)^(3/2)`; the bulk is six times metric
volume. Joint weights at the first and third axis tips are still 2 and 6, and
the induced area scales by Omega squared. These are geometric definitions,
not fitted action coefficients. This is not a coordinate version of #76:
that metric has scalar `3*(1-t^2/2)/(1+t^2)^(5/2)`, nonconstant on every open
set; this metric has nonzero constant scalar. Isometries or the existing
constant scalings cannot remove that invariant distinction. It remains
conformally flat by design; §5 separately tests genuine nonconformal curvature.
No novelty claim about de Sitter physics or the literature is intended.

### Exact full-ray phase, beyond polynomial density

Here is a bounded sufficient result for **any fixed smooth positive time-only
q** on a neighborhood of the relevant compact time range, retaining the
original graph geometry and C² endpoint weights. Let D be the unit Minkowski
diamond with endpoints `(-1/2,0)` and `(1/2,0)`, of volume c. For timelike
separation put `T=(u+v)/2`, `r=(v-u)/2`. A rest-frame boost and scaling give

```math
\begin{aligned}
H_q(t,u,v)&=\frac1c\int_D q(t+T/2+T a+r b_1)\,da\,db,\\
V_M(x,x+(T,rn))&=c(uv)^2 H_q(t,u,v),\\
H_q(t,0,v)&=6\int_0^1 s(1-s)q(t+vs/2)\,ds.
\end{aligned}
```

The scaling determinant is `(uv)^2`; rotational invariance removes n only
because q is time-only. D is fixed, so differentiation under this compact
integral proves smoothness through `u=0`, positive upper/lower bounds and all
needed derivative bounds. For the last identity, slicing D by `a+b_1` gives
normalized density `6*s*(1-s)` on `[0,1]`. For `q=1+t^2` it recovers A3
exactly, including `3*v^2/40` on the null ray. In general the phase coefficient
samples the **whole null segment**, not q or a finite curvature jet at x.

### Written long-sector theorem and contact proof

Fix `delta>0`, long `v>=delta`, and a finite family of C² endpoint fields.
Compact geometry bounds v above by D0 and puts all old-active endpoints in
positive-height tubes, exactly as A6–A7. Define `F=u*v*sqrt(H_q)`.
At `u=0`, `F_u=v*sqrt(H_q)>0`; compactness therefore supplies a common small
right collar with a smooth inverse `u=U(t,v,w)`, positive derivative and
`U=O_delta(w)`. The complement `u>=u0` has
`V>=c*delta^2*u0^2*min(q)>0`, hence an exponentially small normalized tail.
A global polynomial formula or global phase inverse is unnecessary.

On the collar the **actual** amplitude and time boundary are

```math
\begin{aligned}
a(t,v,w;z,n)&=\chi(t,z)\phi(y)q(t)q(t+(U+v)/2)
 \frac{(v-U)^2}{8F_u(t,U,v)},\\
G(t,v,w)&=f(z+(v-U)n/2)-t-(v+U)/2,\\
\tau_0(v)&=f(z+vn/2)-v/2,\qquad
J(w,v)=\int_{\ell(z)}^{\tau(v,w)}a(t,v,w)\,dt.
\end{aligned}
```

Here `ell=f-h` at active source points and `G(tau(v,w),v,w)=0`.
At zero phase `G_t=-1` and `tau_0'<=-(1-eta)/2`. Compact implicit-function
bounds preserve both margins. The strict upper envelope gives
`G(t,v,w)<=G(t,v,0)-(1-eta)*U/2`, so nonpositive old gaps never open to the
right, and `tau<=tau_0`. The lower envelope retains every target without a
same-chart test. This proves that the inverse root describes the whole actual
time interval, not just a patch of it.

For each active source/direction let R0 be the old v root, `tau_0(R0)=ell`,
and `d=-tau_0'(R0)>0`. The right coefficients of the time/v-averaged fibre are

```math
\begin{aligned}
F_0&=\int_\delta^{R_0}J(0,v)\,dv,\qquad
F_1=\int_\delta^{R_0}J_w(0,v)\,dv,\\
F_2&=\frac12\int_\delta^{R_0}J_{ww}(0,v)\,dv
 +\frac{a(\ell,R_0,0)\tau_w(R_0,0)^2}{2d}.
\end{aligned}
```

Use full Leibniz derivatives in J, including derivatives of both weights,
phase inverse, Jacobian, target density and moving time boundary. The final
term is the v-contact triangle; it does not vanish for unit weights. Proof:
on the lost layer put `v=R0-w*s`; then `J/w` tends to
`a(ell,R0,0)*(d*s+tau_w)`. Integrating the negative oriented triangle gives
exactly the last term. Its width is `O_delta(w)` and its height is
`O_delta(w)`, uniformly even for approaching cutoff contacts. For each fixed
active parameter the layer eventually misses delta. At exact/nonpositive
cutoff contact the whole right fibre and coefficients are zero.

Consequently the fibre remainder is `w^2*E(w;z,n)`, pointwise `E->0`, dominated
by a constant on a compact spatial/direction set. Measurability follows from
measurable difference quotients; bounded coefficients are integrable. Dominated
convergence produces §2's actual averaged B jet. That lemma proves the written
extension `L_chi,phi -> 0` for these time-only q, including branch C. This does
not recover the false raw-time dominator, assert uniform little-o over cutoff
contacts, or allow spatially dependent conformal factors without new analysis.

### What survives and exactly what remains

- **Survives with proof above:** causal order/containment, #93 finite-density
  identity, full-ray phase regularity, long contact averaging and finite
  endpoint partitions, at each fixed positive cutoff.
- **Survives as identities, not yet a new short theorem:** H3's full/face/corner
  restoration, both endpoint measures, the induced normal/area formulas and
  spatial flux accounting for time-only q. The short scaled phase is smooth
  with positive ratio derivative at zero scale; this supplies inverse charts,
  not by itself the normalized actual-minus-jet estimates.
- **Missing matched producer:** derive S8–S14 for the actual integral with this
  H_q, evaluate all second-order interval/density terms, derive H8–H12 and
  J10–J17 on the entire boundary collar, including moving diagonal strips and
  compensating face flux. Identify the response as the independent R/2 and
  joint target above, then match the fixed cutoff and assemble. The old exact
  polynomial, diagonal formulas S6/H9, and interpolation truncation cannot be
  copied verbatim. No curvature expansion alone establishes these remainders.

**Decision C: GO long; NARROW full-limit work to that explicit matched-short
contract.** No complete deterministic or expected limit for C is claimed here.

## 4. A — an atlas test with an exact full-partner solution

Let `X=R^3/(L*Z)^3`, `g=dt^2-h_flat`, and
`M=(-T/2,T/2) x X`, with fixed `0<T<L/2` (e.g. L=1, T=2/5).
The ambient ultrastatic product is globally hyperbolic: its spatial factor is
complete, and time slices are compact Cauchy surfaces. More explicitly its
closed order is `s-t>=d_X(p,q)`, where d_X is the minimum Euclidean distance
over lattice lifts. Closed intervals are compact. A causal curve's time is
monotone, so **every ambient interval** between endpoints of M stays in M.
Volume is `dt*dvol_X`, its total is `L^3*T`, both compact smooth faces are
spacelike, and J is empty. Independently R=0, so both target integrals are zero.

This is genuinely outside every existing global two-graph presentation, not
new curvature. A compact boundaryless spacelike face cannot be immersed as
such a hypersurface in Minkowski coordinates: spatial projection has invertible
differential, so its compact image would also be a nonempty open subset of
R³. Equivalently M retracts to T³, whereas a two-graph region retracts to an
open subset of R³, whose ordinary third homology is zero. Passing to its
infinite cover changes the region, volume and order; it is not action transport.
The solid-torus **height** example in #90 does not solve this test.

### Unique lift is proved for intervals, not assumed for chart labels

Any causal curve in this slab has spatial length at most its time separation,
which is less than T. Thus between fixed endpoints there is at most one causal
target lift: two such lifts would differ by a lattice vector of length at
least L, but their distances from the source lift sum to less than `2*T<L`.
Every lifted path and intermediate interval point is in that same Minkowski
diamond. Conversely that diamond projects into the interval. Projection on
it is injective: two same-time points differ by less than L. Therefore, with
`tau=s-t` and `r=d_X(p,q)<=tau`, the **actual restricted** interval volume is
`c*(tau^2-r^2)^2`. Causal target displacements fill the Euclidean ball of radius
tau with ordinary multiplicity one, even across any coordinate seam.

Finite-density Fubini now gives the complete pair integral, per spatial volume,
without throwing away any chart pair:

```math
\begin{aligned}
\frac{P_A(\rho)}{L^3}
 &=4\pi\int_0^T(T-\tau)\int_0^\tau r^2
     K\bigl(c\rho(\tau^2-r^2)^2\bigr)\,dr\,d\tau
 =\int_0^{T^2}K(c\rho w^2)B_T(w)\,dw,\\
B_T(w)&=2\pi\int_{\sqrt w}^T(T-\tau)\sqrt{\tau^2-w}\,d\tau.
\end{aligned}
```

This is a full-volume equality, not additivity of isolated chart actions.
In particular source labels near opposite sides of a coordinate seam retain
their actual short causal pairs. The point term is exactly `L^3*T`.

### Written deterministic and expected thin-slab theorem

Elementary integration, for `0<w<T^2`, gives

```math
\begin{aligned}
B_T(w)&=\pi T\left[T\sqrt{T^2-w}
 -w\log\frac{T+\sqrt{T^2-w}}{\sqrt w}\right]
 -\frac{2\pi}{3}(T^2-w)^{3/2},\\
B_T(w)&=\frac{\pi T^3}{3}+\frac{\pi T}{2}w\log w
 +\pi T\bigl(\tfrac12-\log(2T)\bigr)w
 -\frac{\pi}{8T}w^2+O_T(w^3).
\end{aligned}
```

The error follows by Taylor expansion of the smooth square root and
`log(T+sqrt(T^2-w))` on a fixed neighborhood of zero; extend B by zero
past `T^2`. The logarithm is **retained**, not put into a quadratic Peano jet.
Besides the three zero moments, direct gamma differentiation gives

```math
\begin{aligned}
\int_0^\infty z\log z\,K(z^2)\,dz&=\frac1{12},\\
\int_0^\infty w\log w\,K(c\rho w^2)\,dw&=\frac1{12c\rho},\\
\frac{\pi T}{2}\frac1{12c\rho}&=\frac T\rho.
\end{aligned}
```

Thus the log term cancels the physical point volume with its exact sign and
normalization. The `O(w^3)` remainder integrated with the absolute kernel is
`O(rho^-2)`, so after the pair normalization it tends to zero. The complement
of a fixed small phase interval, including the subtracted polynomial/log tails,
is exponentially small. This proves **in writing**, for every fixed thin slab,

```math
\begin{aligned}
A_g(\rho,M)&\longrightarrow0=\mathcal T_g,\qquad
\mathbb E_{\Pi_{\rho,g,M}}[A^{\mathrm{disc}}_\rho]&\longrightarrow0.
\end{aligned}
```

The second statement uses the separately justified measured-order Mecke
argument of §2 **after** the deterministic proof. It is not an application of
the hard-coded flat-coordinate expectation theorem to a quotient. Neither
statement is compiled Lean. The finite-density action is generally nonzero;
a zero target and empty joint do not make the theorem vacuous.

**Audit A:** local flat short geometry survives on lifted intervals; arbitrary
endpoint partitions require the full double sum, but this proof uses none.
The exact reduction handles the entire nearly-null sector, face contacts and
both time faces together, bypassing a new weighted short/long producer. There
are no conjugate points; no cut locus is reached by an actual causal pair
because T is less than the injectivity radius. This justified restriction is
on the **test**, not a new assumption in G-SS.

**Decision A: GO to the bounded formal port of this full-partner reduction.**
Missing checked interfaces are the compact quotient measured order, injective
interval lifting, quotient integration and the displayed primitive/log response.
For thicker slabs the unique-lift proof fails at nearest-lattice ties; interval
volume is the volume of a **union** of projected diamonds, not the sum of lift
volumes. No thick-torus or general atlas result follows. §5 tests cut/focusing
instead of quietly excluding it from the general target.

## 5. F — non-conformally-flat curvature with interior focusing

Take the ultrastatic product

```math
\begin{aligned}
X&=S^2_a\times S^1_L,\qquad
h=a^2(d\vartheta^2+\sin^2\vartheta\,d\varphi^2)+dz^2,\\
g&=dt^2-h,\qquad M=(-T/2,T/2)\times X,\qquad
(a,L,T)=(1,20,4).
\end{aligned}
```

Here L is circle circumference. The same completeness and monotone-time
argument as A proves ambient global hyperbolicity **and** interval containment.
All faces are compact smooth spacelike slices, with empty J and no other
boundary strata; the polar coordinate singularities are atlas artifacts.
The scalar and squared Weyl tensor, by direct product curvature contraction
with #90's sign, are

```math
\begin{aligned}
R_g&=\frac2{a^2},\qquad
C_{abcd}C^{abcd}=\frac4{3a^4}>0,\qquad
\mathcal B_F=\frac1{a^2}(4\pi a^2LT)=4\pi LT=320\pi,\qquad
\mathcal I_F&=0.
\end{aligned}
```

Nonzero Weyl curvature is invariant under coordinates and obstructs even
**local** conformal flatness. Compact boundaryless faces also give A's global
presentation obstruction. Thus this is neither #76 in different coordinates
nor a flat transport. Its bulk target is nonzero and defined without the action.

### Actual order and all-partner interface

For p,q in X, the spatial distance is the square root of the sum of squared
sphere distance and squared shortest circle distance. The causal relation is
`tau>=d_h(p,q)`. With all balls understood in the **whole** compact X,

```math
\begin{aligned}
V(\tau;p,q)&=\int_0^\tau
 \mathrm{Vol}_h\bigl(B_h(p,s)\cap B_h(q,\tau-s)\bigr)\,ds\\
 &=\int_X\bigl(\tau-d_h(p,z)-d_h(z,q)\bigr)_+\,d\mathrm{vol}_h(z),\\
P_F(\rho)&=\int_0^T(T-\tau)\int_{X\times X}
 \mathbf1_{\{d_h(p,q)\le\tau\}}K(\rho V(\tau;p,q))
 \,d\mathrm{vol}_h(p)d\mathrm{vol}_h(q)\,d\tau.
\end{aligned}
```

These exact identities follow from spatial-speed control, minimizing spatial
geodesics and time Fubini. Endpoint removal is null. They include pairs with no
common chart and are valid at cut loci; one must not replace the intersection
of metric balls by one normal-coordinate diamond there. They are also the
starting full-partner interface for a future deterministic theorem.

At short separations below a fixed normal radius, the usual smooth metric
and volume expansions and finite atlas exist, with compact bounds. They do
**not** supply #74's full signed primitive remainder, and Ricci-direction
terms cannot be discarded in favor of scalar curvature alone. Away from the
cut locus, null geodesic tubes have nonzero transverse Jacobian on compact
subsets; this supplies local smooth coordinates, not a globally averaged
quadratic phase jet or the required moving-face/contact estimates.

### Precise failure of the pilot's regular phase at focusing

For endpoints at north/south poles on S², at the same circle coordinate,
let `D=pi*a` and `tau=D+epsilon`. They fit strictly inside the selected slab
for sufficiently small positive epsilon. Along a sphere great circle the
transverse exponential Jacobian contains `sin(r/a)/(r/a)` and vanishes at
`r=pi*a`; the other transverse circle direction has unit factor. All meridians
reach the antipode at the first conjugate/cut time. No boundary tip is involved.

Write r for distance from the north pole and z for the shortest circle
coordinate from the endpoints. Since `tau<T<L/2`, the active circle coordinates
have no wrap ambiguity. The exact second formula for V becomes

```math
\begin{aligned}
V(D+\varepsilon;N,S)=2\pi a\int_0^D\sin(r/a)
 \int_{-L/2}^{L/2}\left[D+\varepsilon-\sqrt{r^2+z^2}
 -\sqrt{(D-r)^2+z^2}\right]_+\,dz\,dr.
\end{aligned}
```

For interior r set `A(r)=D/(2*r*(D-r))`. Substituting `z=sqrt(epsilon)*zeta`
shows that the bracket divided by epsilon tends to
`(1-A(r)*zeta^2)_+`. Domination here can be proved, not guessed: convexity gives
`distance_N+distance_S>=sqrt(D^2+4*z^2)`, so the active rescaled support obeys
`abs(zeta)<=sqrt(2*D+epsilon)/2`; the rescaled bracket lies between zero and
one. The endpoints r=0,D are null sets for this integral. Bounded convergence
on a fixed compact r/zeta domain therefore proves

```math
\begin{aligned}
V(D+\varepsilon;N,S)&=D_a\varepsilon^{3/2}+o(\varepsilon^{3/2}),\\
D_a&=\frac{8\pi a}{3}\int_0^D\sin(r/a)
 \sqrt{\frac{2r(D-r)}D}\,dr>0.
\end{aligned}
```

This is a **written interval-volume asymptotic**, not a complete-action
asymptotic. It obstructs a finite smooth positive coefficient in a uniform
`V=epsilon^2*H` representation through these pairs: `V/epsilon^2` diverges.
The exact phase `sqrt(V/c)` behaves as `epsilon^(3/4)`; its inverse is of order
`w^(4/3)` and cannot have the pilot's C² inverse with nonzero first derivative.
It is a real focusing obstruction, not a coordinate artifact or a failed
numerical fit.

Antipodal endpoint pairs themselves have zero product measure. That fact does
**not** control their neighborhoods after normalization by `rho^(3/2)`.
Conversely, failure of this unaveraged fibre estimate is **not a counterexample**
to the complete action: averaging transverse endpoint separations may restore
a sufficient jet, or nonanalytic terms may combine with other sectors.

**Decision F: STOP the smooth single-geodesic-phase transplant; NARROW to an
actual cut-neighborhood pair-density producer.** The exact missing result is
the pushforward of the last full P integral, with a fixed time cutoff and a
finite smooth partition of the *pair domain*, near the sphere antipodal cut
set. Include the transition from unique to multiple minimizers, transverse
endpoint separation, time contacts, both measures and all cross-chart pairs.
Derive its actual small-volume density and signed moments, either yielding a
summable quadratic jet after averaging or identifying surviving fractional/log
terms. Restore the complementary pair domain exactly. Only after compatible
short producers and a complete signed assembly could this prove or refute the
bulk target. No formal global-limit port is justified yet for F.

## 6. Decisions, native follow-ups and acceptance mapping

The following signatures are **proof contracts, not compiled declarations**.
Their admissibility inputs contain only the metrics, regions and fixed smooth
geometric data above. No expected limit, density jet or cancellation is a field.

```text
C-short (written producer first):
  in: branch C metric; original smooth two-face region; actual H_q; C5 fields
  out: actual full/face/corner signed short estimates with all fluxes;
       independent bulk/joint identification; one fixed short cutoff
  then: consume section 3 long theorem and #93 equality; full expected limit

Measured-order port (one shared owner):
  in: finite atomless Borel geometric volume, measurable closed causal relation,
      its actual exclusive interval indicator on a standard Borel manifold
  out: canonical order-parameterized layer/action compatibility and count/Mecke
       expectation using existing FinitePoisson/PoissonIntegration;
       recover existing 4D/dimensional APIs without changing their observables

A-port (bounded checked target, not arbitrary atlas):
  in: cubic flat torus, fixed 0<T<L/2, actual quotient order and induced volume
  out: interval lifting + full pair reduction + exact log/point cancellation;
       deterministic zero target, then genuine expected zero limit

F-cut (written feasibility producer, not a promised limit):
  in: exactly (a,L,T)=(1,20,4), actual metric-ball intervals and full P_F
  out: cut-neighborhood endpoint-averaged density/normalization, all transition
       and complement terms; go/narrow/stop for later short/global assembly
```

Created bounded native **#81 children**, with verified GitHub dependency edges:

| Contract | Issue | Native blocked-by prerequisites |
| --- | --- | --- |
| C-short | [#136](https://github.com/q5m-ai/causal-set-emergence/issues/136) | #133 and #76: phase/long gate and actual #74/#75 assembly interfaces |
| Measured-order port | [#137](https://github.com/q5m-ai/causal-set-emergence/issues/137) | #133 and #93: selected geometric instances and compatible finite-measure extraction |
| A-port | [#138](https://github.com/q5m-ai/causal-set-emergence/issues/138) | #133 and #137: written reduction and the missing checked manifold-order foundation |
| F-cut | [#139](https://github.com/q5m-ai/causal-set-emergence/issues/139) | #133: explicit full-partner geometry/obstruction, not an unproved general assembly |

These are actual native relationships, not merely body references. The dimension and null-boundary siblings are
coordination partners, not artificial blockers. No dependency on a desired
future full limit is used to prove its own producers.

| #133 acceptance | Evidence here | Boundary |
| --- | --- | --- |
| Completed pilot vs smooth precompact core | §§1–2, actual source/declaration audit and independent targets | Written #76 is not a compiled curved theorem |
| Explicit tests outside existing coverage | C: constant nonzero scalar vs pilot; A: compact closed faces/topology; F: nonzero Weyl invariant | A local conformal chart or toroidal joint alone is not new coverage |
| Long/short/contact and full-partner audit | C exact rest-diamond phase/contact proof; A complete pair reduction; F metric-ball identity and conjugate-volume obstruction | Failing a raw estimate does not refute the action |
| Separate geometry, probability, estimates and assembly | §2 API/instance distinction; C open short package; A written assembly; F open averaged producer | No new Lean theorem, human review, or probability-limit interchange |
| Bounded dependencies and justified decisions | Signatures above and native follow-up receipt | General atlas/metric coverage, #81/#86/#24 remain open |

There is no demonstrated need to enlarge the core with noncompact tails or
uniformly degenerating angles. Those stay separate, as do spatially dependent
conformal densities, thicker quotient slabs, general null boundaries, arbitrary
dimensions, additional strata and minimal finite regularity. No full-action rate,
shrinking-cutoff uniformity or individual-sprinkling convergence is requested or
claimed. These tests do not exhaust G-SS and cannot narrow its general target.

## 7. Verification boundaries and reproduction

- **Written results:** C's time-only long theorem; finite-partition and signed
  phase interfaces; A's exact thin-slab deterministic/expected theorem; F's
  interval-volume focusing obstruction. Each has the bounded hypotheses above
  and still requires independent mathematical review.
- **Symbolic/numerical evidence:** `general_metric_gate.py` and
  `test_general_metric_gate.py` check direct product curvature/Weyl, independent
  de Sitter curvature/targets, polynomial recovery and nonpolynomial interval
  quadrature, the whole null-ray phase, torus seam pairs, the full pair reduction,
  nonzero off-diagonal partition terms, exact log/point normalization, and
  actual antipodal-volume quadrature with refinement/scaling controls.
  These are finite regressions, not proof assistants or convergence proofs.
- **Lean:** no sources, checker, dependencies or build inputs change. The PR
  records exact unchanged-input comparison against the pin; no fresh full Lean
  audit is necessary or claimed. Future formal work must coordinate ownership,
  use the pinned ancestor for incremental development, and run the full local
  integrated gate after its last Lean-affecting change.
- **Rendering/review:** Markdown lint and browser mathematics are distinct
  checks. The PR records the browser check and one bounded feedback snapshot.
  Automated review is not independent human mathematical review (#94/#86).

```sh
.venv/bin/python -m unittest -v test_general_metric_gate
.venv/bin/python check_symbolic.py
.venv/bin/python -m unittest -v
.venv/bin/python reproduce.py
python3 check_markdown.py
python3 -m unittest -v test_check_markdown
```
