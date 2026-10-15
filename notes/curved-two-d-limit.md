# Complete curved 2D spacelike response and assembly (#175)

**Status: conventional written theorem, not a new Lean proof or independent
human acceptance.** The theorem below has the **whole** smooth 2D G-SS
quantifiers of [#175](https://github.com/q5m-ai/causal-set-emergence/issues/175),
not an extra conformal-chart, topology, width, or global-graph hypothesis.
It consumes the written [S1–S30 short producer](general-metric-short-remainders.md),
including its low-dimensional diagonal and face compensation. The new work is
the global physical interval, the critical long primitive, and their complete
consumer. The expectation statement is subsequent and separate.

Base: `d2cbbc12dbfee6376140a2137013f3d409adfdbf`, fetched from
`origin/issue-81-general-coverage`. Read with [the independent contract](general-contract.md),
[G1–G7](full-partner-globalization.md), and [the dimension constants](dimension-kernels.md).
[DLL v2, §§2.4–2.5 and (11)](https://arxiv.org/html/2501.00139v2#S2.E11)
uses the original minimal-layer expectation and past–future joint; G-SS is
its specified spacelike subcase, not a quotation of a published complete
admissibility predicate. No novelty or all-strata assertion is made.

## 1. Quantified statement and genuine two-dimensional normalization

**Theorem C2.** Let Q be any fixed smooth time-oriented globally hyperbolic
Lorentzian two-manifold. Let M be any nonempty precompact open
ambient-causally-convex G-SS member: precisely the two compact smooth achronal
spacelike faces, their transverse common boundary J, all components, and no
other boundary strata, as in general-contract §§2–3. Then the complete
canonical deterministic action has the limit

```math
\begin{aligned}
K(z)&=(1-2z+z^2/2)e^{-z},\
\mathcal A_{\rho,2}(M)
 &=2\rho\mu_g(M)-4\rho^2\int_{x\preceq y\,;\ x,y\in M}
 K(\rho V_M(x,y))\,d\mu_g(x)d\mu_g(y),\
\lim_{\rho\to\infty}\mathcal A_{\rho,2}(M)
 &=\frac12\int_M R_g\,d\mu_g
   +\sum_{j\in J}\frac{g(n_-,n_+)(j)}
      {\sqrt{g(n_-,n_+)(j)^2-1}}.
\end{aligned}\tag{C2.1}
```

The normals are both future unit timelike normals, and R has #90's sign.
The zero-dimensional measure assigns mass **one to each joint point**;
compactness of the smooth zero-manifold J makes this a finite sum. Empty J
is allowed. The volume is the actual exclusive ambient interval restricted
to M. No phase expansion or desired limit is in the hypotheses.

For any fixed smooth real endpoint fields chi, phi near the compact region,
the corresponding point-weighted bilocal action also satisfies

```math
\begin{aligned}
\lim_{\rho\to\infty} A_{\chi,\phi}(\rho)
 &=\int_M\chi(\Box_g\phi+R_g\phi/2)\,d\mu_g\
 &\quad+\int_{\Sigma_+}
       (\phi n_+(\chi)-\chi n_+(\phi))\,d\Sigma_g
       +\sum_{j\in J}\chi(j)\phi(j)\coth\theta(j).
\end{aligned}\tag{C2.2}
```

This weighted deterministic statement is useful for atlas restoration; no
weighted stochastic observable is silently substituted for the physical one.
Section 8 separately proves that the expectation of the original discrete
2D action, under the original finite Poisson law, has C2.1's limit.

Here the flat normalization constant is c_2=1/2, the point coefficient is 2,
and the pair coefficient is 4. Direct integration of this K, not a 4D moment
identity, gives

```math
\begin{aligned}
\int_0^\infty z^{a-1}K(z)\,dz
 &=\Gamma(a)(1-a)(1-a/2),\
\int_0^\infty K(z)\,dz&=\int_0^\infty zK(z)\,dz=0,\
\int_0^\infty K(z)\log z\,dz&=-\tfrac12,\
\int_0^\infty zK(z)\log z\,dz&=\tfrac12.
\end{aligned}\tag{C2.3}
```

The first formula holds for a>0. Polynomial expansion proves absolute
integrability; differentiating in a near 1 and 2 is dominated by an integrable
power times (1+|log z|). Thus the two logarithmic responses are genuine signed
integrals, not regularized divergent moments. They are the point and critical
short mechanisms; the long argument below must rule out a critical logarithm,
not simply erase it by an ordinary moment zero.

## 2. Global null coordinates are a conclusion, on the cover

We use the smooth Cauchy temporal splitting theorem, as in
[G3's compact causal-control proof](full-partner-globalization.md#2-general-geometric-foundation-without-an-analytic-estimate).
A connected Q is diffeomorphic to R times a connected Cauchy one-manifold C.
The latter is a line or a circle. Thus its universal cover has Cauchy surface
R. This rules out a spatial-reflection holonomy here by geometry, not by an
extra orientability hypothesis. Only finitely many ambient components meet
the compact closure of M; apply the construction to each.

The lifted temporal function is Cauchy. Indeed an inextendible lifted causal
curve with finite temporal endpoint would project to an extendible curve in
Q (the original temporal function is Cauchy), and the local covering property
would extend the lift. Infinite winding at a finite temporal endpoint cannot
evade this: on a compact causal enclosure, G3 bounds auxiliary length by
temporal gap. A convergent projected endpoint therefore has a lift limit.
This also proves the usual lifted global hyperbolicity via the Cauchy
splitting/compact-diamond characterization.

Orient C's line coordinate s. On a circle choose its lift with period L>0.
Each of the two inextendible null curves through p meets C once, transversely.
Let u(p) be the s-label of its left-moving curve and v(p) the negative s-label
of its right-moving curve. At C they are (s,-s). Smooth dependence and
uniqueness for the null ODE show that u,v are smooth, their differentials are
independent, and both increase on future timelike vectors. This construction
uses entire null curves, not local coordinate patches patched by assumption.

Here is also an injectivity and order proof. In the temporal splitting
(t,s), the two null speeds are smooth functions a_-(t,s)<a_+(t,s). Each null
solution exists for every finite t, by the Cauchy property. Same-family
solutions never cross. Opposite-family solutions can cross only from negative
to positive relative spatial separation, since their relative derivative at
a crossing is strictly positive. They therefore intersect at most once.
This makes (u,v) injective. At any time later than p, the spatial interval
between its two null solutions is precisely its causal future slice: the
speed inequality is necessary, and interpolating the two speeds gives all
intermediate endpoints by continuous dependence. Earlier than p the two
label inequalities are incompatible. Consequently

```math
\begin{aligned}
\widetilde Q&\simeq U\subset\mathbb R^2,\
p\preceq q&\quad\Longleftrightarrow\quad
                  u(p)\le u(q),\quad v(p)\le v(q),\
g&=2w(u,v)\,du\,dv,\qquad d\mu_g=w(u,v)\,du\,dv,\quad w>0,\
T(u,v)&=(u+L,v-L)\quad\text{in the circle case}.
\end{aligned}\tag{C2.4}
```

The image U is open, but more is needed. For comparable p,q, the image of
the compact lifted causal diamond equals U intersected with their coordinate
rectangle. It is closed in that rectangle by compactness, and relatively open
because U is open. The rectangle is connected and the intersection nonempty;
hence the **whole rectangle** belongs to U. This proves causal convexity of
the coordinate image, including both null edges and tips. It is not an appeal
to conformal flatness alone. The deck formula follows from the Cauchy labels;
w is invariant under T. In the line case there is no deck group.

Compact causal control also supplies all constants used below. Lift endpoints
in finitely many relatively compact evenly covered endpoint charts. G3's
complete auxiliary metric length bound places every connecting lift and its
whole interval in a compact lifted ball. Alternatively, in C2.4 the possible
endpoint shifts satisfy the explicit finite bounds in C2.5 below. All relevant
rectangles have compact union in U. On a slightly larger compact neighborhood,
w has a positive lower bound and bounded derivatives of every required finite
order. The same is true of the endpoint fields and the chosen temporal
function. No bound uniform over different metrics/topologies is asserted.

## 3. Physical intervals, all routes, and the complete pair measure

Fix endpoint representatives x=(u,v) and y=(U,V) in those charts. In the circle
case the complete lift list and physical interval are

```math
\begin{aligned}
\mathcal I(x,y)
 &=\{n\in\mathbb Z:u\le U+nL,\quad v\le V-nL\},\
-\frac{U-u}{L}&\le n\le\frac{V-v}{L},\
D_n(x,y)&=[u,U+nL]\times[v,V-nL],\
I_Q(x,y)&=\pi\left(\bigcup_{n\in\mathcal I(x,y)}D_n(x,y)\right),\
V_Q(x,y)&=\int_F
 \mathbf1_{\bigcup_{n,k}T^kD_n(x,y)}\,w(a,b)\,da\,db.
\end{aligned}\tag{C2.5}
```

F is one measurable deck fundamental domain. Only finitely many translated
rectangles meet any chosen compact fundamental piece. One may take 0<=u<L;
the rectangles' bounded v-ranges then make the relevant part compact. The
line case has just its one rectangle. Every causal path lifts with one of
these endpoint labels. Conversely every point in one of these rectangles
lies on a lifted causal path. This proves the set identity, including paths
which change null direction. The **union indicator** handles both intersections
between routes and self-overlap of a large rectangle. One must not sum kernel
values over n, or apply the kernel to a lift-multiplicity volume.

For x,y in M, ambient causal convexity puts every such path and every interval
point in M. It also proves equality of intrinsic and restricted ambient order.
Endpoints have zero geometric volume, so V_M=V_Q there. For limiting pairs in
the closure of the actual causal pair domain, all their lifted intervals lie
in the closure of M, by compactness/continuity; its smooth faces have zero
volume. Formula C2.5 also proves continuity of V_Q on local endpoint charts:
rectangle endpoints vary continuously, degenerate rectangles have zero area,
and the finite union indicators converge almost everywhere off rectangle
edges. This continuity is used only on the compact relevant pair enclosure.

Choose **one** smooth Cauchy temporal function tau, and strict short/equality
long at a fixed positive delta. In any two endpoint charts the actual long
primitive is exactly

```math
\begin{aligned}
N^\delta_{\chi,\phi}(s)
 &=\int \mathbf1_M(x)\mathbf1_M(y)
  \mathbf1_{\{x\preceq y,\ \tau(y)-\tau(x)\ge\delta,\ V_Q(x,y)\le s\}}\
 &\hspace{17mm}\cdot\chi(x)\phi(y)w(x)w(y)\,du\,dv\,dU\,dV.
\end{aligned}\tag{C2.6}
```

Sum this with the complete ordered endpoint partition. It is a coordinate
spelling of G5, not a new measure. This note uses **physical volume s**, whereas
G5 uses w_G=V/c_2=2V: N_G(w_G)=N(w_G/2). Both endpoint densities and all moving
face masks are in C2.6.

### Which contacts actually remain at small volume?

For delta>0 the closure of the actual long pair domain is separated from
x on the future face and from y on the past face, including their joints.
To prove this, take a hypothetical sequence approaching such a pair. Causal
convexity places its curves in M; compact temporal-speed control gives a
limit causal curve in its closure with temporal duration at least delta.
Near a future face, a defining function with future timelike differential
is nonpositive on the region and increases strictly along that curve. Starting
on the face is impossible. The reversed argument holds at a past target.
At J the same defining function is still smooth and timelike. Thus the long
source has at most its **past** face mask, and the long target at most its
**future** face mask. This is a derived clearance statement, not deletion of
joint atoms: their entire short contribution remains in S30.

Each nonempty lift rectangle has volume at least a positive constant times
its two side lengths. Fixed temporal gap and compact coordinate control bound
the larger side away from zero. Three causal lifts would put a middle
rectangle's two side lengths at least L, forcing a fixed positive volume.
Two nonadjacent lifts do the same. Hence a sufficiently small physical-volume
collar has **one thin rectangle or two adjacent thin rectangles only**.
In the line case only the first alternative occurs. Higher winding and all
other pairs remain in the fixed-positive-volume complement, not a removed
subset of the action.

A two-route zero-volume contact has one null increment L and the other zero.
The positive null derivatives of tau on the compact enclosure bound its
temporal gap below by a positive constant. Choose delta smaller than half
this bound and smaller than the S30/locality bound. The temporal-cutoff mask
is then inactive near every two-route contact. This is compatible with any
fixed smooth Cauchy temporal function; it is not an assumed special global
conformal-time cutoff. With no two-route contacts this extra bound is absent.

## 4. Resolve the two-route physical union before estimating it

Near a two-route contact use z=(u,v) for the source and signed excesses p,q
so that the target representative is (u+L+p,v+q). The possible rectangles are

```math
\begin{aligned}
D_A&=[u,u+L+p]\times[v,v+q] &&(q\ge0),\
D_B&=[u,u+p]\times[v,v+L+q] &&(p\ge0),\
V_A&=\int_{D_A}w,\qquad V_B=\int_{D_B}w,\qquad
 V_{\mathrm{sum}}=\mathbf1_{\{q>0\}}V_A+\mathbf1_{\{p>0\}}V_B.
\end{aligned}\tag{C2.7}
```

Negative widths are used only as smooth signed extensions for differentiation,
not as physical rectangles. In the one-positive sectors the interval is its
one rectangle. In the positive-positive sector the rectangles are individually
injective, but have **two** physical overlaps, not one:

```math
\begin{aligned}
C_x&=[u,u+p]\times[v,v+q],\
C_y&=[u+L,u+L+p]\times[v,v+q],\
V_Q&=V_A+V_B-\int_{C_x}w-\int_{C_y}w,\qquad p,q\ge0,\
|V_Q-V_{\mathrm{sum}}|&\le Cpq,\qquad
 V_A=qH_A(z,p,q),\quad V_B=pH_B(z,p,q),\quad H_A,H_B\ge c>0.
\end{aligned}\tag{C2.8}
```

Indeed D_A meets only D_B and T D_B; their intersections are the displayed
source and target rectangles. All other translates are disjoint when |p|,|q|
are sufficiently small compared with L. The lower bounds and smoothness of
H follow by rescaling the thin coordinate to [0,1] and integrating the actual
positive w along the entire other side. Values at both endpoints remain.

Let N_sum be C2.6 with this sum phase, using **exactly the same** physical
endpoint domain, masks, weights and partitions. On the difference of its
sublevel set and the physical one, p,q are O(s), because V_Q is at least
each single-rectangle volume. C2.8 therefore confines that difference to
s<V_sum<=s+C s^2. In this corner the derivative of V_sum with respect to p
is bounded below, so for each q its p-width is O(s^2), while its q-width is
O(s). The passive source variables have bounded measure. Consequently

```math
\begin{aligned}
|N^\delta_{\chi,\phi}(s)-N^\delta_{\mathrm{sum},\chi,\phi}(s)|
 \le C_{\chi,\phi}s^3.
\end{aligned}\tag{C2.9}
```

This estimate is valid also for signed fields and arbitrary moving endpoint
masks, by bounding their absolute amplitudes. It compares **primitives**, not
kernels or their derivatives. It retains the physical-union correction and
will make its normalized response vanish by Stieltjes integration below.
There is no unproved differentiable remainder assertion here.

## 5. Derive the critical primitive from the moving masks

We give the contact argument explicitly, since smooth w alone is insufficient.
Use finitely many smooth compact pair cutoffs near the compact zero-volume
long locus. Their sum is one on a smaller collar. All artificial chart edges
are in those smooth cutoffs. The remaining positive-volume region is retained.

**Moving-mask lemma (first derivative).** Suppose a compactly supported smooth
amplitude a(r,z) is integrated over finitely many smooth inequalities
F_i(r,z)>=0. At r=0 suppose each active z-gradient is nonzero, and each pair
of simultaneously active z-gradients is independent. Then its integral B(r)
is C1 near zero, with the one-sided statement sufficient here, and

```math
\begin{aligned}
B'(0)&=\int_{F_i\ge0}\partial_r a(0,z)\,dz\
 &\quad+\sum_i\int_{F_i=0,\ F_j\ge0\ (j\ne i)}
        \frac{a(0,z)\,\partial_r F_i(0,z)}{|\nabla_zF_i(0,z)|}\,dA_i,\
B(r)&=B(0)+rB'(0)+r\epsilon(r),\qquad
 \epsilon(r)\longrightarrow0,\quad |\epsilon(r)|\le C.
\end{aligned}\tag{C2.10}
```

Proof: use finite implicit-function boxes at each face. A moving face changes
a strip of width O(|r|). Pairwise independence bounds an intersection of two
such strips by O(r^2), uniformly on compact supports. The first difference
quotient is therefore the sum of the interior derivative and the displayed
single-face fluxes. On each parametrized face, the other masks' boundaries
have measure zero by pairwise independence. Dominated convergence gives
continuity of each flux as r varies, even at a triple or higher contact.
Compact bounds on the same fluxes bound B'. The fundamental theorem of
calculus proves the last line. No independence of every mask simultaneously,
finite contact order, analytic boundary, or vanished closing fibre is assumed.

### One-positive sectors

A single thin route has excess r>=0, longitudinal length l bounded away from
zero, source coordinates z, and physical volume rH(z,l,r), H>0 smooth.
Use **physical volume** s as the thin coordinate by the implicit function
theorem. The change of variables preserves the full smooth amplitude,
including w(x)w(y), the phase Jacobian, endpoint fields and both face motions.
At s=0 its remaining variables are the two source coordinates and l.
Possible sharp masks are source past face, target future face, temporal
cutoff, and (near a two-route contact) the other route's negative excess.

Here are the required ranks on that zero-phase fibre:

- A spacelike face conormal is timelike and has nonzero pairing with either
  future null direction. Each face mask and the temporal mask is regular.
- Vary the target along the active null ray holding the source fixed. The
  source mask is fixed and the target-face and temporal masks have nonzero
  derivatives. Conversely vary the source along that ray holding the target
  fixed. The target mask is fixed and the temporal derivative is nonzero.
  These variations prove independence of source/target, source/cutoff and
  target/cutoff pairs, using regularity of the remaining mask.
- The inactive route boundary fixes l=L. Each endpoint face is independent
  of it since its source-coordinate differential at fixed l is timelike.
  The temporal cutoff never meets it, by the small fixed delta choice in §3.

Compactness gives positive rank margins in a finite cover. At small positive
s they persist. Thus C2.10 applies to the **actual** pushed integral, including
simultaneous contacts, nonzero field derivatives and every closing fibre.
Writing B for its density gives

```math
\begin{aligned}
N_{\mathrm{one}}(s)
 &=b_0s+\tfrac12b_1s^2+R_{\mathrm{one}}(s),\
|R_{\mathrm{one}}(s)|&\le s^2\eta(s),\qquad
 \eta(s)\longrightarrow0,\qquad 0\le\eta(s)\le C.
\end{aligned}\tag{C2.11}
```

For instance take eta(s) to be half the supremum of |B'(r)-B'(0)| for
0<=r<=s. The constants b_0,b_1 are obtained from the domain integral and
**all** fluxes in C2.10, not selected to match a target.

### Two-positive sectors

Here p,q>=0 and V_sum=pH_B+qH_A. Put p=sa, q=sb. The rescaled domain is a
bounded perturbation of the triangle A(z)b+B(z)a<=1, where A=H_A(z,0,0)>0
and B=H_B(z,0,0)>0. Its Jacobian is s^2. Each face mask now depends on z and
s(a,b); at s=0 it is a regular source-coordinate hypersurface (the target is
a fixed coordinate translate of z). Its O(s)-moving strip has O(s) z-measure.
This remains true when the two face boundaries coincide: a union bound on
the strips suffices. The temporal mask is inactive. Smooth amplitudes and
uniformly bounded rescaled triangles give

```math
\begin{aligned}
N_{\mathrm{two}}(s)
 &=s^2\int \frac{W(z,0,0)
       \mathbf1_M(x(z))\mathbf1_M(y(z))}{2A(z)B(z)}\,dz+O(s^3).
\end{aligned}\tag{C2.12}
```

Boundary values of the displayed indicators do not affect this integral.
W includes both geometric endpoint densities and the original smooth pair
cutoff. In particular a closing source-time interval is integrated, not
replaced by its length at a frozen endpoint. At an exact slab-width contact
its zero leading coefficient is allowed and the moving strip remains in
the O(s^3) estimate. This is why no generic four-mask rank hypothesis is needed.

Together C2.9–C2.12 prove, for each fixed smooth weighted ordered chart pair
and hence their finite sum, the **geometrically produced** estimate

```math
\begin{aligned}
N^\delta_{\chi,\phi}(s)&=c_1s+c_2s^2+s^2E(s),\
E(s)&\longrightarrow0\quad(s\downarrow0),\qquad |E(s)|\le C.
\end{aligned}\tag{C2.13}
```

The bound here initially holds in one fixed volume collar. Continue N
constantly beyond its bounded support; then E is bounded on the whole positive
half-line as well. Outside the collar, continuity of the actual physical
volume on the compact pair closure gives a positive volume lower bound.
Its normalized response is bounded by a fixed polynomial in rho times an
exponential. This accounts for higher winding, timelike interiors, atlas
complements and the transition out of the thin-volume charts. No selected
sector is being identified with the complete long action.

## 6. Signed long response, with its complement and union correction

The pushforward measure has no atom at zero: null intervals and null-related
endpoint pairs have zero geometric volume, as follows either from C2.4 or
achronal-boundary Fubini. Signed Fubini gives the exact Stieltjes formula,
with N continued constantly, not reset to zero at its support endpoint:

```math
\begin{aligned}
P^{\ge\delta}_{\chi,\phi}(\rho)
 &=\int_0^\infty K(\rho s)\,dN^\delta_{\chi,\phi}(s)
 =-\rho\int_0^\infty N^\delta_{\chi,\phi}(s)K'(\rho s)\,ds,\
L^\delta_{\chi,\phi}(\rho)
 &=-4\rho^2P^{\ge\delta}_{\chi,\phi}(\rho)
 =4\int_0^\infty z^2K'(z)E(z/\rho)\,dz
 \longrightarrow0.
\end{aligned}\tag{C2.14}
```

Integration by parts and C2.3 annihilate both polynomial primitive terms:
int z K'=-int K=0 and int z^2 K'=-2 int zK=0. The remaining integrand is
bounded by C z^2|K'(z)|, integrable, and tends to zero. This proves the
critical signed response without differentiating the o(s^2) remainder.
The O(s^3) physical-union correction has zero response by the same argument.
The fixed-positive-volume complement and polynomial tails are exponentially
small. This is precisely G5–G7 in dimension two after w_G=2s, including the
minus sign of the pair action. It is not an absolute bound on the original
nearly-null kernel.

## 7. Independent target, common-cutoff assembly, and point exactly once

Independently of any action, Christoffel contraction for C2.4 in #90's
curvature convention gives

```math
\begin{aligned}
\Gamma^u_{uu}&=\partial_u\log w,\qquad
\Gamma^v_{vv}=\partial_v\log w,\qquad
R_g=\frac2w\partial_u\partial_v\log w,\
\frac12R_g\,d\mu_g&=\partial_u\partial_v\log w\,du\,dv.
\end{aligned}\tag{C2.15}
```

In local coordinates t=(u+v)/2, x=(u-v)/2 the metric is
Omega^2(dt^2-dx^2), Omega^2=2w. If the two actual face slopes at a joint are
p and q, direct normalization of their timelike normals gives

```math
\begin{aligned}
n_-&=\frac{(1,p)}{\Omega\sqrt{1-p^2}},\qquad
n_+=\frac{(1,q)}{\Omega\sqrt{1-q^2}},\
C&=\frac{1-pq}{\sqrt{(1-p^2)(1-q^2)}},\qquad
\coth\theta=\frac{1-pq}{|p-q|},\qquad dA_g(j)=1.
\end{aligned}\tag{C2.16}
```

The counting measure has no conformal length factor. Transversality bounds
the denominator away from zero on the finite J. These are independent
curvature/normal definitions, not coefficients defined by a limiting integral.

Choose delta once below **all** S30 locality, face/joint-root, temporal-shell
and §3 two-route bounds. For every endpoint partition pair the finite-density
identity is exactly G1. S30 is applicable to every such smooth field pair
on the actual metric and region; its entire S14 moving-diagonal term in 2D,
both oriented bulk face fluxes, S25 face compensation and S29 counted corner
term are retained. It gives the right side of C2.2 for strict short. Add
C2.14 at this same delta to prove C2.2 for the complete action.

For clarity, the short logarithmic cancellation is indispensable here. In a
local full cone the two radial directions each contribute the lower-end
logarithm; in physical-volume coordinates their combined point-density term
is minus log(s) times the actual diagonal measure chi*phi*dmu_g. By C2.3 its
pair integral is (1/(2 rho)) times that measure, so the negative pair prefactor
cancels **2 rho** times that measure. The critical s log(s) response is
1/(2 rho^2), not a vanishing ordinary moment; S19/S25/S29 derive its metric,
field, face and counted-joint coefficient. The moving-diagonal order-s term
S14 has its own ordinary zero moment and is not absent. We consume those
actual producers; neither log coefficient nor compensating face flux is
added to admissibility or inferred from a numerical fit.

For independently chosen source/target partitions chi_i,phi_j summing to one,

```math
\begin{aligned}
\sum_{i,j}\chi_i(x)\phi_j(y)&=1,\
\sum_{i,j}\int_M\chi_i\phi_j\,d\mu_g&=\mu_g(M),\
\mathcal A_{\rho,2}&=\sum_{i,j}
       \left(S^\delta_{\chi_i,\phi_j}+L^\delta_{\chi_i,\phi_j}\right).
\end{aligned}\tag{C2.17}
```

Every off-diagonal label remains. Summing derivatives of the partitions
cancels artificial atlas fluxes, not true face or joint terms. For the
physical unit fields the Box and field-normal terms vanish only **after**
this sum, yielding C2.1. A different cutoff is related by the exact opposite
signed G2 integral; at finite density it is restored even when nonzero.
Disconnected components do not introduce discarded cross-pairs: a causal
curve between two components of M would be contained in M and connect them,
contradicting their separation. This consequence of ambient containment,
not a general action valuation rule, covers all components and all their
counted endpoints. There is no remaining artificial boundary or point term.

## 8. Only now transfer the original Poisson expectation

The following discharges the actual geometric hypotheses of
[`dimensionFiniteMeasureAction_expectation`](../formal/BoundaryDraft/DimensionMeasureExpectation.lean),
not an assumed bridge field. Smooth manifolds are standard Borel. Global
hyperbolicity gives a closed ambient causal partial order (G3 supplies the
compact limit-curve proof). Restricted to M it is Borel and remains that
**same** order. The triple exclusive-interval indicator is Borel, so its
geometric volume is a measurable endpoint function. Finite chart covers and
smooth positive densities give finite atomless mu_g restricted to M. Section
3 proves interval containment and the actual volume identity, rather than
substituting intrinsic global hyperbolicity for containment.

Construct the original finite Poisson law with intensity rho*mu_g|M. For a
finite configuration let L_k count ordered distinct related pairs with k
strictly intermediate points. The action is 2(N-2L_0+4L_1-2L_2). The layer
weights (1,-2,1), including **k!**, are not the polynomial coefficients
(1,-2,1/2). Each layer is bounded by N^2, and finite Poisson second moments
justify integrability and finite signed summation. The ordinary one-/two-point
Mecke formulas and the actual exclusive-interval Poisson count give

```math
\begin{aligned}
\mathbb E L_k
 &=\rho^2\int_{x\preceq y\,;\ x,y\in M}
 e^{-\rho V_M(x,y)}\frac{(\rho V_M(x,y))^k}{k!}\,d\mu_g(x)d\mu_g(y),\
\mathbb E\,[2(N-2L_0+4L_1-2L_2)]&=\mathcal A_{\rho,2}(M),\
\lim_{\rho\to\infty}\mathbb E A^{\mathrm{disc}}_{\rho,2}
 &=\frac12\int_MR_g\,d\mu_g+\sum_{j\in J}\coth\theta(j).
\end{aligned}\tag{C2.18}
```

The last line follows **after** C2.1. This is a written manifold instantiation
of the previously compiled generic bridge, not a new compiled manifold
instance or a sample-wise, variance, probability or almost-sure conclusion.

## 9. Adversarial diagnostics, original acceptance, and limits

`curved_two_d.py` and `test_curved_two_d.py` supply finite diagnostics, not
certification of the universal C2.13 remainder. They exercise weighted
rectangles against a separate physical time-slice integral; periodic physical
unions against independently intersected circle slices; both overlap corners;
more-than-two lift and self-overlap complements; genuinely variable curved
density; nonempty unequal-angle counted endpoints; nonzero endpoint fields;
compact-Cauchy empty-joint slabs including the two-route/closing-width contact;
and finite-density full ordered partition and cutoff restoration.

| Original #175 obligation | Written output |
| --- | --- |
| Actual entire 2D class, atlas/topology/containment | C2.4 derived from global null ODEs and Cauchy geometry; C2.5 finite complete route list and physical union; §3 containment and endpoint clearance |
| Both measures, moving masks, cut contacts, closing fibres, complements | C2.6–C2.12; pairwise-rank moving-mask lemma, including coincident closing masks in the two-positive sector; positive-volume complement retained |
| Critical estimate from geometry, genuine 2D signs/logarithms | C2.3, derived C2.13, Stieltjes C2.14; no desired jet in the class |
| Whole action with one compatible fixed cutoff and point once | C2.17 and actual S14/S19/S25/S29/S30 consumption, §7; opposite G2 conversion retained |
| Independent curvature and every counting atom | C2.15–C2.16; all components, both normals, no higher-dimensional tip deletion |
| Original-law expectation only afterward | C2.18 with actual Borel order/intervals, finite atomless measure, containment, integrability and factorials discharged |
| Proof level and remaining ownership | Written proof plus finite diagnostics; no new Lean asymptotics, formal audit or attributable human review |

No original flat result, complete obstruction, model certificate, or historical
issue/PR receipt is rewritten. C2 adds the entire **smooth curved 2D G-SS**
row, not regular SN/NN or arbitrary tips, seams and other strata. Curved 3D,
broader corrected 4D/higher-dimensional coverage remain **#81**; all remaining
null/mixed coverage remains **#156**. Intended-statement/provenance scrutiny,
independent mathematical/physical acceptance and justified formalization stay
**#94/#86**. Those obligations are not certified by automated tests or this
author's argument. No finite-regularity relaxation, uniform degenerating-family
bound, shrinking cutoff, noncompact tail, stochastic strengthening, merge,
deployment or automatic issue closure is part of this delivery.

Refs #175, #81, #24, #90, #150, #77, #94, #86.
