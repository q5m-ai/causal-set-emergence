# Intrinsic physical unions: two methods and the remaining inference (#156)

**Written analysis, not independent acceptance or new Lean coverage.** Start:
`5ca76f65608177edbcc8a755c8e7e48af9341556`; existing #184 branch and target
`issue-81-general-coverage`. The [original-item crosswalk §8](null-mixed-required-coverage.md#8-original-contract-reconciliation-after-the-general-front-attempt)
remains authoritative. Nothing here changes the action, closed order, law,
physical cutoff, original acceptance or theorem ownership.

**Decisive result and limitation.** Resolving the *actual* spherical union
radially, without differentiating through its seven-halves angular transition,
gives its complete growth **plus finite term with an o(1) error**, uniformly
through the physical closing threshold. This strengthens IF5, but is used as
an adversarial test, not a universal normal form. A different, derivative-free
logarithmic-ramp identity then removes every kernel-null power without assuming
that the geometric primitive has a classical expansion. It applies to general
physical unions, but the required geometric critical trace is still missing.
Thus the original-contract recommendation remains **STILL BLOCKED**.

## 1. Audit CS before consumption; no new cusp calculation

The [CS proof](curved-common-tip-response.md) is used only at its actual
conformal common-tip scope. Its critical points reconstruct as follows.

- The homothety times boost has bounded entries. The pulled density therefore
  has common positive and derivative bounds. Reflection of the rest diamond
  removes odd transverse square roots; a bounded number of physical derivatives
  controls each required phase derivative. This does not assert an intrinsic
  map or an inverse of the limiting singular map.
- In CS4 split l at 1/4. The upper piece has the regular edge poles; the lower
  piece retains both its l and xi subtractions. The double remainder is bounded
  by a polynomial in the Mellin parameter times the integrable powers below.
  The angularly averaged linear l jet is independent of xi. The cubic jet has
  degree at most one in xi, including products of lower jets. Consequently
  neither collision produces a double pole. Away from xi=0 no xi derivatives
  are needed, including at xi=1.

```math
\begin{aligned}
|R(l,\xi,w)|&\le C(1+|w|)^N
                l^{6-3\mathrm{Re}(w)}\xi^{3-3\mathrm{Re}(w)/2},\\
2&\lt\mathrm{Re}(w)\lt7/3,\\
\mathrm{Res}_{w=1}Z_E(w)&=8,
 &\widehat K_3(1)&=-1/8,\\
\mathrm B(-1/2-3u/2,3/2)&=-\pi(u-2/3)+O((u-2/3)^2),\\
\int^{\mathrm{cont}}F(x)x^{-3u/2}\,dx
 &=-\frac{2f_0}{3(u-2/3)}+O(1).
\end{aligned}\tag{IU1}
```

The rightward contour shift subtracts residues, giving the actual positive
point coefficient. At the mass pole the last two lines multiply to
`2*pi*f_0/3`, not zero. The constant subtraction at small lambda gives the same
`beta/u` after splitting its integral at one. CS8a retains the nonzero upper
tail; it is not an exponential replacement. Gamma decay controls the contour
shift uniformly in the bounded density family.

Finally `kappa[E]=s*kappa[A](q)` must be used **before** estimating CS9.
The remaining bound is `C*epsilon^(-1)*(1+s/epsilon)^(-3/2)`. After
`s=epsilon*z`, the entire upper tail has mass at most
`2*C*(1+L)^(-1/2)`; the lower end is bounded. Together with the actual
past-set membership limit this justifies the two-sector dominated convergence.
No blocking discrepancy is found within CS's stated scope. This is an author
reconstruction, not #94/#86 acceptance. The resolved cusp is not redone.

## 2. General geometry: the union and the closing cap come first

The physical clock construction [CP3–CP6](curved4-physical-response.md#2-physical-intervals-without-selecting-geodesics)
uses global hyperbolicity, a compact causal enclosure and ambient containment,
not spacelike-face smoothness, until its later contact arguments. Those first
steps therefore apply to the present causally convex null/mixed regions.
Choose a smooth timelike Cauchy flow `q(t,z)`, with actual density j. Its
first arrival from p is a_p(z), its last departure to q is b_q(z). On each
**physical** flow line the interval is one intersection of two closed rays:

```math
\begin{aligned}
V(p,q)&=\int_Y\mathbf1_{a_p(z)\lt b_q(z)}
            \int_{a_p(z)}^{b_q(z)}j(t,z)\,dt\,d\sigma(z),\\
N^{\delta,V}_{\chi,\phi}(v)
 &=\int_M\chi(p)\,d\mu(p)
   \int_{\ell\lt m_+}\int_\ell^{\max(\ell,T_{p,z}(v))}
           \phi(q(t,z))j(t,z)\,dt\,d\sigma(z),\\
\ell&=\max(a_p(z),m_-(z),t(p)+\delta).
\end{aligned}\tag{IU2}
```

Here M cuts each flow line in `(m_minus,m_plus)`, or an empty interval;
T is the inverse of the **whole** volume, clipped at m_plus. Empty causal
sections contribute zero. Strict increase after arrival follows by inserting
a positive-volume timelike diamond. Continuity follows by dominated convergence
of the actual cone indicators; their boundaries are achronal and volume-null.
Neither assertion supplies differentiability of the inverse.

Thus IU2 retains continuously many routes, both endpoint measures, the real
closing cap, every macroscopic partner and all partition labels. It is not
an integral of a kernel over individual geodesic diamonds. A signed target
field remains inside its clock integral. The same formula without the temporal
mask defines the complete pair primitive. Strict short and its exact complement
use one compatible **fixed positive** delta; the point belongs only to short.
The phase variable v is not a replacement physical cutoff.

This is an existing geometric foundation, not the missing continuation theorem.
The question is what its *actual clipped inverse average* does at critical
order. The next calculation tests that question where a globally smooth
amplitude is known to be false.

## 3. First method: a joint resolution of the actual spherical interval

Use exactly NP1's region and both endpoint weights, O5's whole sphere union,
and IF1's secondary transition. No slab overlap is substituted. Write
`a=pi-theta`, `e=U-theta`, and introduce the auxiliary projective coordinates

```math
\begin{aligned}
r&=a+e,& y&=e/(a+e),&
 a&=r(1-y),& U&=\pi+r(2y-1),\\
x&=\pi+a(t-1),& t&=1-\cos\varphi,\\
B_a(\eta)&=\sqrt{\cos^2\eta+\sin^2(a/2)\sin^2\eta},&
Y_a(\eta)&=2\arcsin(\cos(a/2)\sin\eta),\\
M_a(t,\eta)&=
 \frac{2[B_a(\eta)-\sin^2(a(1-t)/2)/B_a(\eta)]}
 {\sqrt{\mathrm{sinc}(at/2)\mathrm{sinc}(a(2-t)/2)}}.
\end{aligned}\tag{IU3}
```

Here `sinc(x)=sin(x)/x`, with value one at zero. The variables x and Y
are O5's sum and difference of the **two physical
sphere distances**, not two competing route volumes. Let eta range from
`-pi/2` to `pi/2`. O5's complete two-orientation measure becomes exactly
`M_a d eta d phi`. Indeed substitute
`sin(Y/2)=cos(a/2)*sin(eta)` in its y-distance edge and use
`cos(theta)-cos(x)=2*sin(at/2)*sin(a(2-t)/2)` in its x edge. The two square-root
Jacobians cancel as shown in IU3. At a=0 its limit is `2*cos(eta)`; that
meridian side is included, not discarded.

Integrate O5's U derivative **before** taking the limit. Define a smooth
function near U=x=pi by

```math
\begin{aligned}
\Psi(U,x,Y)&=\frac{\pi^2}{32}\int_0^1
 z^2(2x+(U-x)z)^2
 \frac{[(x+(U-x)z)^2-Y^2]^2}{[x+(U-x)z]^4}\,dz,\\
q_y(t)&=y-(1-y)t,\\
\frac{W(\pi+r(2y-1),\pi-r(1-y))}{r^3}
 &=\int_0^\pi\int_{-\pi/2}^{\pi/2}
       [q_y(1-\cos\varphi)]_+^3
       M_{r(1-y)}(1-\cos\varphi,\eta)
       \Psi(U,x,Y_{r(1-y)}(\eta))\,d\eta\,d\varphi.
\end{aligned}\tag{IU4}
```

Only where q is positive is Psi needed. Its argument `U-x=r*q` there is the
actual positive time gap. Formula IU4 is exact, including both sphere sheets,
the entire secondary transition at `y=2/3`, and the meridian end y=1.
There is no differentiation across that transition.

### A radial error bound from this physical map

For small positive r, the following bounds hold uniformly in y:

```math
\begin{aligned}
W&=r^3y^{7/2}h(r,y),\\
0\lt c&\le h(r,y)\le C,&
|h(r,y)-h_0(y)|&\le Cr,\\
\|h(r,\cdot)-h_0\|_{C^4([0,y_0])}&\le Cr
                                  &&(0\lt y_0\text{ sufficiently small}),\\
y^{7/2}h_0(y)&=\Phi(y)
 =D(1-y)^3F\left(\frac{2y-1}{1-y}\right),&\Phi(1)&=D.
\end{aligned}\tag{IU5}
```

Here D and F are the actual O6 constants/profile. To prove the bounds, not
assume a regular normal form, observe directly that
`abs(Y_a-2*eta)<=a`, `abs(B_a-cos(eta))<=C*a`, and
`sin(a*(1-t)/2)^2/B_a<=C*a`. The denominator in M has a fixed positive margin.
Consequently `M_a=2*cos(eta)+O(a)` uniformly, including the polar endpoints.
Psi differs by O(r) from `(pi*pi-4*eta*eta)^2/24`. The integral of
`q_+^3 d phi` is comparable to `y^(7/2)` on the entire unit interval.
These facts prove the first two lines and identify the tangent profile.
At y=0 the normalized expression is interpreted by its regular-edge limit.

For the derivative statement, restrict to a small fixed neighborhood of y=0
and set `t=y*z/(1-y)`, with `0<=z<=1`. Extract `y^(7/2)` explicitly; the
remaining fixed weight is `z^(-1/2)*(1-z)^3`. The sinc denominators are away
from zero. Here a is comparable to r. The functions B and Y extend on a
common small complex y disk with their positive-real branches; their only
possible square-root zeros in a are imaginary, outside that sector. Bounds
`B-cos(eta)=O(r)` and `Y-2*eta=O(r)` hold there as well, including the endpoints.
For example `dY/da=-sin(a/2)*sin(eta)/B` is bounded in that sector; integrating
along its radial segment proves the latter bound. Cauchy estimates on a
smaller disk give the four derivative bounds under the integrable fixed
weight. This argument uses the exact trigonometric geometry, not analyticity
of an arbitrary metric.

No fourth angular derivative is claimed near y=2/3. In fact IF1's nonzero
seven-halves term is still present in h_0 and in the actual W. It does not
obstruct IU5's **radial** estimate. The profile has the actual opening formula
`h_0=D*c_star*(1-y)^(-1/2)*H(y/(2*(1-y)))` near zero, so it is smooth there.
It is positive and continuous through the remaining compact y interval,
including y=1. Decrease the fixed radial neighborhood to obtain the lower
bound in IU5.

## 4. Simultaneous focal and closing transitions: the complete remainder

Let T range in any fixed compact subinterval of `(0,L/2)`. Extend the actual
IF2 weight G_T(U) by zero for U at least T. Its geometric representation
`G_T(U)=(T-U)_+^(9/2)*L_T(U)` makes this extension C4 near U=pi, with uniform
bounds on that compact T interval. This is where **both endpoint masks**
enter. In particular it keeps the physical closing cap even when it passes
through the focal and secondary transitions.

Choose a fixed smooth radial partition chi(r), one near zero, supported
inside IU5's neighborhood. The cut part of the **actual volume Mellin integral**
is

```math
\begin{aligned}
Z_{c,T}(w)&=C_Y\int_0^\infty\int_0^1
 \chi(r)r^{2-3w}y^{-7w/2}A_T(r,y,w)\,dy\,dr,\\
A_T(r,y,w)&=(1-y)\mathrm{sinc}(r(1-y))
 G_T(\pi+r(2y-1))h(r,y)^{-w},\\
A_T(0,y,w)&=(1-y)G_T(\pi)h_0(y)^{-w},
 &C_Y&=2\pi V_Y.
\end{aligned}\tag{IU6}
```

It initially converges absolutely for `0<Re(w)<2/7`. Subtract A_T(0,y,w)
in r. By IU5, the difference is O(r) with polynomial vertical growth; the
same is true of its first four y derivatives near zero. For G_T this uses
only its four bounded derivatives: the k-th y derivative carries r to power
k, and the zeroth difference is O(r). **No fifth derivative of the closing
weight is required.**

On a fixed y collar at zero subtract degree three in y from both terms.
The angular remainder is integrable for `Re(w)<10/7`; the radial difference
is integrable for `Re(w)<4/3`. Away from that collar y is bounded below,
so no angular derivative is taken at the seven-halves transition. The radial
leading term has a single pole at w=1; the edge subtractions have the four
simple poles `2j/7`, j=1,...,4. There are no collisions between these pole
sets and hence no double pole in this strip. All constants and vertical
polynomial bounds are uniform in T, including T=pi.

This proves meromorphic continuation to `Re(w)<4/3` with precisely those
possible poles; it is **derived from IU4**, not stipulated in admissibility.
The actual K7 has a zero at all four edge poles. A contour at, for example,
`Re(w)=13/10` lies strictly above the action-critical value `9/7`. Its
Gamma decay and these bounds give a remainder whose multiplication by
`rho^(9/7)` tends uniformly to zero.

### Independent coefficient, both tails and the fourth subtraction

At w=1 the radial residue is -1/3. Change y to
`S=(2*y-1)/(1-y)` in the remaining continued integral. The initial convergent
integrals agree, so their continuations agree. The result is

```math
\begin{aligned}
\mathrm{Res}_{w=1}Z_{c,T}(w)&=-C_T,&
C_T&=\frac{2\pi V_YG_T(\pi)}{3D}I,\\
I&=\frac{\log(5/2)}3+\frac{35\pi}{128}
 \left[\int_0^1\frac{H(x)^{-1}-1-r_1x-r_2x^2}{x^{7/2}}\,dx
       -\frac25-\frac23r_1-2r_2\right],\\
r_1&=-1/18,&r_2&=-59/7128.
\end{aligned}\tag{IU7}
```

This is O12's *ordinary convergent subtracted integral*. Its opening/matching
terms and **entire meridian tail** `log(5/2)/3` are indispensable. The unchanged
rational O13 certificate proves I is positive. Its value is not fit to the
action. The fourth regular pole, at 8/7, is retained and annihilated by the
fourth genuine kernel zero. Attempting to integrate its ordinary inverse
coefficient absolutely to a=0 was the failed route; IU6 instead defines its
unique continued geometric coefficient by the explicit radial subtraction.
No infinite coefficient is multiplied by zero.

At T=pi, G_T(pi)=0. For each r the support has `y<1/2`; the post-secondary
side is absent **by the physical cap**. Above threshold it reappears and
remains in IU6. This handles simultaneous closing without replacing the
weight by a positive constant or exchanging a fixed-width limit with density.

### Full deterministic restoration and separate expectation

The nonorigin, nonfocal small-volume complement has the actual regular
interval inverse. Its four Taylor coefficients are annihilated; the C4
closing weight gives a primitive with one more derivative, sufficient for
the same contour/critical remainder. Fixed-positive-volume complements are
exponentially small, uniformly on the compact width interval. Artificial
partition boundaries are retained in these exact complements.

At the origin, NP4–NP6 give the independently derived point and curvature/NN
screen coefficients. Their estimates are uniform here: the interval inverse
is independent of T, while the endpoint coefficients and the fixed-cutoff
short weight have uniform derivatives for T bounded away from zero. The
point coefficient is `-1024*mu(M_T)/5`; the moment is `-5/128` and `a_7=8*beta_7`.
Thus it cancels the physical point exactly. NP6 supplies the independent
finite target `V_Y*(T*T/2+2)`. The long origin has only kernel-null powers.
All source/target labels must be summed; no weighted-cell focusing theorem
is inferred from symmetry.

We have consequently proved the stronger, complete statement

```math
\begin{aligned}
\mathcal A_{\rho,7}(M_T)
 &=\gamma(T)\rho^{2/7}+V_Y(T^2/2+2)+o(1),\\
\gamma(T)&=\frac{5\beta_7}{128}\frac{2\pi V_YG_T(\pi)}{3D}I,\\
\gamma(T)&=0\quad(T\le\pi),&\gamma(T)&\gt0\quad(T\gt\pi).
\end{aligned}\tag{IU8}
```

The error is uniform on the stated compact width intervals. Each application
still fixes its geometry and uses one positive physical temporal cutoff;
there is no density-dependent cutoff or deletion of either matching tail.
IU8 is an asymptotic of the **unchanged action**, not a modified observable.
The same formula holds for its expectation only afterward, by NP's actual
Borel order, whole-interval containment, atomless volume and ordered Mecke
identity. No sample-wise statement follows.

IU8 strengthens IF5's deliberately weaker above-threshold statement. It is
still **only this intrinsic product family**, not #156's corrected general
theorem. The next method is pursued because this success cannot be promoted
by declaring every focal union to have IU3's coordinates.

## 5. Why the first method does not yield the general producer

The unconditional clock formula IU2 provides continuity and monotonicity,
not a positive resolved factor with IU5's radial modulus and opening-edge
derivatives. Intrinsic smoothness does not bound inverse endpoint Jacobi
matrices near all conjugate minima. Actual focal orders differ: the preserved
4D [CO obstruction](curved4-complete-action-obstruction.md) has a different
surviving order, and NP/NA3 rule out an additive local-finite-jet repair.
Their complete obstructions, not the failure of this proof method, exclude
the false universal finite local target.

One attempted transfer would resolve a minimum at each active ray and sum
its continued coefficients. That is invalid **before** remainder estimation:
IU2 is a union on each physical flow line; an inverse of its volume is not
a sum of ray inverses. The [CL3 proper-piece analysis](curved-three-d-clusters.md#6-distinct-attempts-at-the-remaining-whole-cluster-matching)
already exhibits the issue at the two tips and at small action gaps. Its
central transport and its phase-bad bound do not supply this missing full
union estimate. The accumulating-well germ there is only an abstract control,
not a Lorentzian counterexample; it cannot justify a finite branch count.
No #177 conclusion or ownership is taken over here.

The precise lost step is the summable *radial difference bound for the whole
clipped union*, not a kernel coefficient. Demanding such a classical resolved
expansion in all geometries may itself be stronger than necessary. We therefore
change methods rather than assume finite type or keep differentiating a
nonsmooth selected branch.

## 6. Second method: a canonical derivative-free signed response identity

This construction is dimension independent and applies to the **actual**
finite signed pair measure, including arbitrary physical unions. It builds
on [G5–G7](full-partner-globalization.md) and the
[averaged-ramp idea of M3](curved-three-d-matching.md#1-the-observable-and-an-averaging-criterion-without-a-second-pointwise-jet),
but requires no fitted/subtracted
list of geometric Taylor coefficients.

Use volume phase v, `m=floor(d/2)+1`, and `alpha_j=2*j/d`. For a locally
bounded primitive N define the ordinary averaging operator H and filter F_d:

```math
\begin{aligned}
(HN)(v)&=\int_0^1N(vt)\,dt,&
\mathcal F_d&=H\prod_{j=1}^m[I-(1+\alpha_j)H],\\
\mathcal F_d[v^s]&=f_d(s)v^s,&
f_d(s)&=\frac{\prod_{j=1}^m(s-\alpha_j)}{(s+1)^{m+1}},\\
C_d&=\frac{(-1)^m}{\prod_{j=1}^m\alpha_j},&
J_{m+1}(z)&=(-z\partial_z)^{m+1}e^{-z}.
\end{aligned}\tag{IU9}
```

Write `c_l` for the coefficients of
`product_j(1-(1+alpha_j)*X)`. Repeated ordinary integration, then finite
signed Fubini, makes this a direct geometric ramp on the original pairs:

```math
\begin{aligned}
\Phi_d(r)&=\mathbf1_{0\le r\le1}
 \sum_{l=0}^m c_l\left[1-r\sum_{k=0}^l\frac{\log(1/r)^k}{k!}\right],\\
(\mathcal F_dN)(v)&=
 \int_{p\preceq q\in M}\chi(p)\phi(q)
               \Phi_d(V(p,q)/v)\,d\mu(p)\,d\mu(q),\\
P(\rho)&=C_d\int_0^\infty J_{m+1}(z)
                         (\mathcal F_dN)(z/\rho)\,dz.
\end{aligned}\tag{IU10}
```

At r=0 use the continuous limit of each bracket; at r=1 it is zero.
The filter is bounded and signed. All routes are already united in V before
it is evaluated. Either fixed temporal mask can be inserted in the pair
measure, with its exact complement; neither the phase threshold v nor the
substitution `v=z/rho` changes that physical mask. N is continued **constantly**
beyond its support, not by zero.

**Proof of the response identity without a classical expansion.** In
logarithmic distributional derivatives, `D_v=v*partial_v` satisfies
`(D_v+1)H=I`. The bounded-average definition gives
`(D_v+1)^(m+1) F_d N=product_j(D_v-alpha_j)N`. Transfer these derivatives
onto the exponential. The adjoint of `D_v+1` for ordinary dv is `-D_v`.
The kernel recurrence gives
`-K_d'=product_j(1+(D_z+1)/alpha_j)exp(-z)`, proving IU10.
One can first insert compact cutoffs and then remove them. Bounded N at
zero and its constant continuation at infinity, with the exponential and
its polynomial derivatives, make all boundary terms vanish. This also
justifies the calculation for finite signed measures rather than only smooth
primitives. No derivative of a moving front or union selector is taken.

### The physical point is matched, not suppressed

Let `mu_0=integral chi*phi dmu` be the actual diagonal point weight. There is
an exact algebraic point subtraction, with no assertion that geometry has
already produced this coefficient:

```math
\begin{aligned}
Q_{\mathrm{pt}}(v)&=
 \begin{cases}
 \displaystyle\frac{a_d\mu_0}{\beta_d\widehat K_d(1)}v,&d\text{ odd},\\
 \displaystyle\frac{a_d\mu_0}{\beta_d\widehat K_d'(1)}v\log v,&d\text{ even},
 \end{cases}\qquad Q_{\mathrm{pt}}(0)=0,\\
\int_0^\infty K_d(\rho v)\,dQ_{\mathrm{pt}}(v)
 &=\frac{a_d\mu_0}{\beta_d\rho},\\
\mathcal A_{\rho,d}[\chi,\phi]
 &=-\beta_d C_d\rho^{1+2/d}
   \int_0^\infty J_{m+1}(z)
       \mathcal F_d[N-Q_{\mathrm{pt}}](z/\rho)\,dz.
\end{aligned}\tag{IU11}
```

In even dimensions the genuine zero at one is simple, so the logarithmic
moment is its derivative; no density logarithm survives that point identity.
The subtraction is on the full half-line and has only polynomial/logarithmic
growth. It is therefore integrable against every displayed exponential
weight. IU11 retains the point exactly once and is not an assumed cancellation.

Every kernel-null pure power is now removed **by a fixed finite sequence of
ordinary geometric averages**, even when no such expansion of N exists.
Logarithmic powers are differentiated in s in IU9 and are not mistakenly
annihilated with their pure powers. This includes the even-dimensional
critical logarithm. The transform has not defined a correction as the action.
It has supplied an explicit geometric producer whose asymptotics remain to
be established.

### A genuinely weaker sufficient estimate, and the failed universal bound

Put `b=1+2/d`. If independently derived geometric terms have been removed
and the remaining filtered primitive B obeys `B(v)=o(v^b)` with a bounded
divided remainder near zero, IU11 and the integrable weight
`z^b*abs(J_{m+1}(z))` prove its complete normalized response vanishes.
This is an analytic implication, **not an admissibility condition or a
proof that arbitrary physical geometry satisfies it**. A weaker convergence
against that signed weight can also suffice; pointwise limits are not necessary.

For example, the abstract increasing primitive
`N(v)=v^(2/d)+v^(b-1/4)*sin(v^(-1/2))`, on a sufficiently small fixed
interval and continued constantly, has no classical critical remainder.
Its derivative's oscillatory part is smaller than the leading positive
derivative. One integration by parts gives
`H[v^(b-1/4)*sin(v^(-1/2))]=O(v^(b+1/4))`; further averages preserve that
bound. The leading power is killed exactly by F_d. Thus the filtered
criterion holds although the classical remainder divided by v^b is
unbounded. As with M3's control, this is **not a spacetime realization**.
It prevents insisting that all proofs must first derive a classical expansion.

Now attempt to discharge the bound from IU2 alone. The terminal short null
segment supplies a contained diamond of volume at least `c*h^(d/2)` for
clock advance h. Compact clock densities give the general long estimate
`abs(N(v))<=C*v^(2/d)`. Each bounded averaging in IU9 preserves, but does
not improve, this order. After critical normalization it gives O(rho),
not o(1). Where a first geometric coefficient has separately been proved,
its removal improves this to o(rho), still not the needed conclusion.
Closing caps only reduce this positive bound; taking absolute values loses
the very signed cancellation now exposed by the filter.

The **actual spherical adversary** rules out assuming an automatic further
cancellation. Its geometrically derived focal mode is `C_T*v`, and

```math
\begin{aligned}
f_7(1)&=-\frac{15}{76832}\ne0,\\
C_7\int_0^\infty zJ_5(z)\,dz\,f_7(1)&=-5/128,\\
-\beta_7\rho^{9/7}P_{C_Tv}(\rho)
 &=\frac{5\beta_7C_T}{128}\rho^{2/7}.
\end{aligned}\tag{IU12}
```

Both matched tails in IU7 are needed to obtain C_T in this calculation.
IU8 separately restores the complete finite remainder. Thus the direct
identity detects, rather than erases, the real nonlocal obstruction. Positive
clock-strip bounds and kernel zeros alone cannot establish the missing trace.
No universal zero response, local-jet correction or finite target is inferred.

## 7. Common tips intrinsically, and the replacement when there is no tip

For `M=I+(a) intersect P` with P an open past set containing a, transitivity
still gives the whole past-partner fibre `I(a,q)`, up to volume-null boundaries,
in **any** admitted ambient geometry. This is the part of CS that survives
without conformal coordinates. Point/label accounting and the separate
finite-density Mecke identity survive as well. Local normal geometry supplies
local coefficients under its genuine locality hypotheses.

It does **not** give a bounded reference diamond, the cubic angular identity
that excluded CS's double pole, or CS7's generator mass. In particular the
actual intrinsic null relation can terminate or branch at a cut, and there
is no globally faithful ray parametrization on which that mass calculation
was based. Here the valid complete intrinsic response is IU2/IU10/IU11 applied
to the actual fibre, not a substituted conformal profile. Its additional
geometric critical trace is not proved zero.

For a general future set F and past set P, the exact replacement is
`F intersect I-(q)`, not a sum of tip intervals. If, only when actually
available, `F=union_i I+(a_i)` is a **finite** representation, define
`D_i(q)=I+(a_i) intersect I-(q)` and the set of active i for which q is in
I+(a_i). For q in M this set is nonempty. Exact inclusion–exclusion gives

```math
\begin{aligned}
\int_{F\cap I^-(q)}K_d(\rho V(p,q))\,d\mu(p)
 &=\sum_{\varnothing\ne S\subset\mathrm{active}(q)}(-1)^{|S|+1}
   \int_{\bigcap_{i\in S}D_i(q)}K_d(\rho V(p,q))\,d\mu(p),\\
1&=\sum_{\varnothing\ne S\subset\mathrm{active}(q)}(-1)^{|S|+1}.
\end{aligned}\tag{IU13}
```

The second line is the point multiplicity. Every overlap integral uses the
same whole physical V(p,q). Intersections are generally not diamonds with
another point tip. Dropping them is an error already at finite density, not
an optional asymptotic simplification. General F need not have a finite-tip
representation at all; IU2 is still available. A countable exhaustion permits
finite-density dominated passage, not passage at critical normalization
without a new uniform bound. Independent ordered source/target partitions
always remain valid when **all** their products are summed, by G4; that
identity is not tip-action additivity.

## 8. Exact stopping point and original-contract comparison

Two distinct attempts have been carried out. The first derives an actual
physical radial continuation and a complete critical remainder on the adverse
sphere family, including its finite term above threshold. Its general transfer
fails precisely at a uniform whole-union radial difference estimate, not at
an unknown kernel constant. The second replaces that potentially excessive
classical-expansion demand by the explicit derivative-free geometric filter
IU10. Its universal clock-strip bound is too weak, and IU12 proves that an
unexplained universal cancellation would be false.

**Smallest exact missing inference:** obtain the critical signed trace and
an integrable remainder for the canonical log-ramp of the **actual clipped
clock union** in IU10/IU11, through accumulating/merging route openings and
boundary closing, with every surviving term evaluated from geometry rather
than named as an action residual. This can be attacked without asserting a
classical polyhomogeneous expansion. The preceding geometric and signed
identities do not supply that estimate, so they are not a corrected general
theorem. Nor is IU8's family-specific correction a universal one.

A **specialist mathematical result on that filtered physical-clock trace**
is now the focused next requirement. An explicit parent scope decision would
be necessary only to accept the proved subclasses/obstructions as the endpoint
instead of the original general theorem; no such decision is adopted or
implicitly requested as a condition of admissibility. The single §8 crosswalk
keeps the original negative-resolution clause and remains STILL BLOCKED.

No claim is transferred to #177. #94/#86 retain independent mathematical/
physical scrutiny, provenance and justified verification; #185's claim-to-Lean
mapping remains deferred. All older proofs, certificates and historical
receipts keep their scopes. Diagnostics below support finite arithmetic and
domain checks, not the written analytic remainders or human acceptance.
